#!/usr/bin/env python3
"""Rebuild only the modules that a change can affect.

    python3 scripts/rebuild-affected.py [--check N] [ARGUMENTS FOR `lake build`]
    python3 scripts/rebuild-affected.py --check-only N

`lake build` compiles a module again whenever the public `.olean` of a module it can see has changed,
whether or not it uses what changed. This script runs `lake build` with a wrapper in place of `lean`.
When Lake asks for a module, the wrapper compiles it only if the rule below says the change can
affect it. Otherwise it puts the module's previous output back, and Lake goes on as if the module
had been compiled. The outcome is meant to be what `lake build` would have produced, but it is NOT a
verified build: see "Limits", and `scripts/REBUILD-AFFECTED.md` for how the rule was checked.

How it runs. The outputs and traces now in `.lake/build` are first recorded in
`.lake/rebuild-affected/base` (hard links). Lake then runs twice. The first pass runs on that copy,
through a directory of links to the project, and changes nothing in `.lake/build`: every module Lake
asks for gets its previous output back, so no module sees a changed import, and the modules Lake asks
for are therefore the ones whose own inputs changed (source, options, toolchain, dependencies), or
that see other modules than before or the same ones in another order. The second pass is the build.

The rule. A module M is compiled if its own inputs changed, if it has no previous output, or if it
uses `import all` or `meta import` or is not a `module` (then it reads more of its imports than their
public part).

Otherwise the script collects the changes that concern M. These are the changes that the modules M
sees logged when they were compiled, since M was last compiled or checked. If M sees other modules
than before, they are also everything in the modules that came into its view, as added, and
everything in those that went out of it, as removed. That second case needs M's source to be known
to be what its previous output was built from (the script learns this from Lake at the start of
every run, and learns it again after anything but this script replaced an output), the modules that
came or went to be of this package, and the others to be loaded in the same order as before;
otherwise M is compiled.

M is compiled if one of these changes, in a module X,
  1. adds, removes or changes a constant whose name occurs in M's previous output. A constant also
     counts as changed if its type or definition mentions a changed constant (unfolding reaches it),
     if an attribute tied to it changed, if a lemma that Lean generates for it on demand
     (`foo.eq_1`, `foo.congr_simp`, ...) appeared or disappeared in X, or if it is an instance or a
     simp lemma that was removed or narrowed from global to scoped;
  2. changes the constructor of a structure that M's previous output projects from;
  3. changes the compiled code of a constant that occurs in M's previous output, if M has compiled
     code (the projections after a removed structure field are a case: only their index changes);
  4. is in a module of which M used a macro, notation or attribute (Lean records these uses for
     `lake shake`);
  5. adds an instance, a simp lemma or a `grind` pattern: it counts, as in 1, for a constant of X in
     its pattern (a term it applies to contains that constant), and falls under 7 if there is none;
  6. adds a declaration or an `export`, unprotects a name or drops a namespace, when the last
     component of that name is a word of M's source (it could now resolve differently); removes or
     changes a declaration, or drops a lemma of case 1 that Lean had generated for it, when every
     component of the declaration's name is a word of M's source (Lean may have tried it as a
     meaning of a name in M and rejected it, or M may have asked for the lemma in a `simp [foo]`
     that left no mention of `foo` in the proof; neither leaves a trace in the output); or moves
     the registration of a namespace in which M declares something;
  7. is anything else that is not tied to a declaration: an entry of an extension the script does
     not know, new syntax, a removed coercion or `rfl` simp lemma. Then every module that sees X is
     compiled.

Limits. Lean does not record what the elaboration of a module read, so the rule is built from what a
compiled module contains and from the cases above. A dependency that leaves no trace in the output
and that no case covers is missed, and the reused output is then stale without a warning.
`--check N` compiles N of the reused modules again after the build and compares the outputs.
Warnings of reused modules are not printed again. Do not publish a cache built with this script.

The script reads compiled modules directly, so it is tied to a Lean version: it refuses to run with a
toolchain that is not in `CHECKED_TOOLCHAINS`. Its state is in `.lake/rebuild-affected`; delete that
directory to make it forget what it recorded. The state holds the previous outputs of the modules a
run compiles, until the next run, so a run needs that much free disk space.
"""
import array, hashlib, json, mmap, os, random, re, shutil, struct, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

try:
    import fcntl
except ImportError:      # Windows, where `main` refuses to run
    fcntl = None

OUTPUT_EXTS = (".olean", ".olean.server", ".olean.private", ".ilean", ".ir", ".ir.sig")

# ---------------------------------------------------------------------------------------------------
# Reading `.olean` files (format version 4). A file is a memory image: an 88-byte header, the image
# size, a pointer to the root `ModuleData`, then the objects. Pointers are absolute addresses, and the
# `.server` and `.private` parts of a module may point into the parts before them.

OBJECTS = 104
T_ARRAY, T_SARRAY, T_STRING, T_MPZ, T_THUNK, T_TASK, T_REF = 246, 248, 249, 250, 251, 252, 253
U64 = struct.Struct("<Q")
# object header: reference count (4 bytes, 0 here), size (2), number of pointer fields (1), tag (1)
NAME_RE = re.compile(rb"\x00\x00\x00\x00\x20\x00\x02[\x01\x02]")   # `Name.str`, `Name.num`
PROJ_RE = re.compile(rb"\x00\x00\x00\x00\x28\x00\x03\x0b")         # `Expr.proj`
ANONYMOUS = 1723                                                    # hash of `Name.anonymous`


class Module:
    """The parts of one compiled module: `X.olean`, then `.server` and `.private` if they exist."""

    def __init__(self, olean, norm=None):
        """`norm`, if given, maps the bytes of a string to the bytes `digest` should use instead."""
        self.parts, self.roots, self.memo, self.norm = [], [], {}, norm
        for p in (olean, olean + ".server", olean + ".private"):
            if not os.path.exists(p): break
            with open(p, "rb") as f:
                size = os.fstat(f.fileno()).st_size
                buf = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) if size else b""
            if size < OBJECTS or buf[:5] != b"olean" or buf[5] != 4:
                raise ValueError(f"{p}: not a version-4 .olean file")
            base, = U64.unpack_from(buf, 80)
            self.parts.append((base, base + size, buf))
            self.roots.append(U64.unpack_from(buf, 96)[0])

    def at(self, ptr):
        for base, end, buf in self.parts:
            if base <= ptr < end: return buf, ptr - base
        raise ValueError(f"pointer {ptr:#x} outside the module")

    def obj(self, ptr):
        """(tag, pointer fields, scalar bytes) of the object at `ptr`."""
        buf, off = self.at(ptr)
        head, = U64.unpack_from(buf, off)
        size, nobj, tag = (head >> 32) & 0xffff, (head >> 48) & 0xff, head >> 56
        if tag <= 243:
            return tag, struct.unpack_from(f"<{nobj}Q", buf, off + 8), bytes(buf[off + 8 + 8 * nobj:off + size])
        n, = U64.unpack_from(buf, off + 8)
        if tag == T_ARRAY: return tag, struct.unpack_from(f"<{n}Q", buf, off + 24), b""
        if tag == T_STRING: return tag, (), bytes(buf[off + 32:off + 31 + n])
        if tag == T_SARRAY: return tag, (), bytes(buf[off + 24:off + 24 + n * nobj])
        if tag == T_MPZ:
            limbs, = struct.unpack_from("<i", buf, off + 12)
            return tag, (), bytes(buf[off + 12:off + 16]) + bytes(buf[off + 24:off + 24 + 8 * abs(limbs)])
        if tag in (T_THUNK, T_TASK, T_REF): return tag, (n,), b""
        raise ValueError(f"unsupported object tag {tag}")

    def fields(self, ptr): return self.obj(ptr)[1]

    def name(self, ptr):
        parts = []
        while not ptr & 1:
            tag, (prefix, last), _ = self.obj(ptr)
            parts.append(self.obj(last)[2].decode("utf-8", "replace") if tag == 1 else str(last >> 1))
            ptr = prefix
        return ".".join(reversed(parts))

    def name_hash(self, ptr):
        """Lean stores the hash of a `Name` in the object."""
        if ptr & 1: return ANONYMOUS
        buf, off = self.at(ptr)
        return U64.unpack_from(buf, off + 24)[0]

    def names(self):
        """Hashes of all `Name` objects in the module: every name its declarations mention, with all
        prefixes. A superset of the constants they refer to."""
        out = set()
        for _, _, buf in self.parts:
            for m in NAME_RE.finditer(buf, OBJECTS):
                if not m.start() & 7: out.add(U64.unpack_from(buf, m.start() + 24)[0])
        return out

    def proj_structs(self):
        """Name hashes of the structures that occur in `Expr.proj` nodes."""
        out = set()
        for _, _, buf in self.parts:
            for m in PROJ_RE.finditer(buf, OBJECTS):
                if m.start() & 7: continue
                try: out.add(self.name_hash(U64.unpack_from(buf, m.start() + 8)[0]))
                except ValueError: pass
        return out

    def digest(self, ptr):
        """Hash of the object graph under `ptr` that does not depend on addresses."""
        memo = self.memo
        if ptr & 1: return U64.pack(ptr)
        stack = [ptr]
        while stack:
            p = stack[-1]
            if p in memo: stack.pop(); continue
            tag, fields, scalars = self.obj(p)
            todo = [f for f in fields if not f & 1 and f not in memo]
            if todo: stack.extend(todo); continue
            if tag == T_STRING and self.norm: scalars = self.norm(scalars)
            h = hashlib.blake2b(bytes((tag, len(fields) & 0xff)), digest_size=16)
            for f in fields: h.update(U64.pack(f) if f & 1 else memo[f])
            h.update(scalars)
            memo[p] = h.digest(); stack.pop()
        return memo[ptr]

    def mentioned(self, ptr):
        """Hashes of the names used under `ptr` (not of their prefixes)."""
        out, seen, stack = set(), set(), [ptr]
        while stack:
            p = stack.pop()
            if p & 1 or p in seen: continue
            seen.add(p)
            tag, fields, scalars = self.obj(p)
            if tag in (1, 2) and len(fields) == 2 and len(scalars) == 8: out.add(U64.unpack(scalars)[0])
            else: stack.extend(fields)
        return out

    def data(self, part=0):
        """(imports, constNames, constants, extraConstNames, entries) of one part's `ModuleData`."""
        return tuple(self.fields(x) for x in self.fields(self.roots[part])[:5])

    def constants(self, part=0):
        """{name hash: (name pointer, constant pointer)}"""
        _, names, consts, _, _ = self.data(part)
        return {self.name_hash(n): (n, c) for n, c in zip(names, consts)}

    def entries(self, part=0):
        """{extension name: entry pointers}"""
        out = {}
        for pair in self.data(part)[4]:
            n, arr = self.fields(pair)
            out[self.name(n)] = self.fields(arr)
        return out

    def all_names(self):
        """{name hash: name} of every constant of the module, private ones included."""
        out = {}
        for part in {0, len(self.parts) - 1}:
            for h, (n, _) in self.constants(part).items(): out[h] = n
        return {h: self.name(n) for h, n in out.items()}

    def imports(self):
        """[(module, public, all)] from the module header."""
        out = []
        for i in self.data(0)[0]:
            _, (n,), flags = self.obj(i)       # `Import`: module, then the flags importAll, isExported, isMeta
            out.append((self.name(n), bool(flags[1]), bool(flags[0])))
        return out

    def extra_mod_uses(self):
        """Modules this one depends on for something other than a term (recorded by Lean for `shake`)."""
        if len(self.parts) < 3: return set()
        uses = self.entries(2).get("_private.Lean.ExtraModUses.0.Lean.extraModUses", ())
        return {self.name(self.fields(e)[0]) for e in uses}


class Nothing:
    """Stands for a module that is not there, when all of another one appears or disappears."""
    def constants(self, part=0): return {}
    def entries(self, part=0): return {}
    def all_names(self): return {}
    def data(self, part=0): return ((), (), (), (), ())
    def name(self, ptr): return ""


NOTHING = Nothing()
UNORDERED = {"Lean.Linter.lintLogExt", "Lean.Linter.codeQualityLogExt"}


def same_but_numbering(a, pa, b, pb, renaming):
    """Are two objects equal up to a consistent renaming of the compiler's local variables (`_uniq.N.M`)?"""
    stack, seen = [(pa, pb)], set()
    while stack:
        x, y = stack.pop()
        if x & 1 or y & 1:
            if x != y: return False
            continue
        if (x, y) in seen: continue
        seen.add((x, y))
        (tx, fx, sx), (ty, fy, sy) = a.obj(x), b.obj(y)
        if tx != ty or len(fx) != len(fy): return False
        if tx in (1, 2) and len(fx) == 2 and len(sx) == 8 and len(sy) == 8:          # a `Name`
            nx, ny = a.name(x), b.name(y)
            if nx == ny: continue
            if not (nx.startswith("_uniq.") and ny.startswith("_uniq.")): return False
            if renaming.setdefault(nx, ny) != ny or renaming.setdefault("<" + ny, nx) != nx: return False
        elif sx != sy: return False
        else: stack.extend(zip(fx, fy))
    return True


def same_module(a, b):
    """Do two compiled versions of a module hold the same data in every part? Two things are not
    held against them, because they vary between compilations of the same source: the order of
    stored linter messages (linters run concurrently) and the numbering of local variables in the
    compiler's intermediate code."""
    if len(a.roots) != len(b.roots): return False
    renaming = {}
    for root_a, root_b in zip(a.roots, b.roots):
        fa, fb = a.fields(root_a), b.fields(root_b)
        if a.obj(root_a)[2] != b.obj(root_b)[2] or len(fa) != len(fb): return False
        if any(a.digest(x) != b.digest(y) for i, (x, y) in enumerate(zip(fa, fb)) if i != 4): return False
        ea, eb = a.fields(fa[4]), b.fields(fb[4])               # field 4: the extension entries
        if len(ea) != len(eb): return False
        for x, y in zip(ea, eb):
            (name_a, list_a), (name_b, list_b) = a.fields(x), b.fields(y)
            ext, la, lb = a.name(name_a), a.fields(list_a), b.fields(list_b)
            da, db = [a.digest(e) for e in la], [b.digest(e) for e in lb]
            if a.digest(name_a) != b.digest(name_b) or len(da) != len(db): return False
            if da == db or (ext in UNORDERED and sorted(da) == sorted(db)): continue
            if not ext.startswith(CODE_PREFIXES): return False
            if not all(p == q or same_but_numbering(a, e, b, f, renaming) for p, q, e, f in zip(da, db, la, lb)): return False
    return True


# ---------------------------------------------------------------------------------------------------
# What changed in a module that was compiled.

# Extensions whose entries describe one declaration and are only consulted when that declaration is
# involved. A changed entry counts as a change to the declarations of the module that it mentions.
DECL_BOUND = {
    "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt",
    "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt",
    "_private.Lean.Compiler.MetaAttr.0.Lean.metaExt",
    "Lean.backwardDefeqAttr", "Lean.defeqAttr", "Lean.noncomputableExt", "Lean.protectedExt", "Lean.auxRecExt",
    "Lean.noConfusionExt", "Lean.Meta.completionBlackListExt",
    "Lean.projectionFnInfoExt", "Lean.classExtension", "Lean.Meta.Match.Extension.extension",
    "Lean.Meta.congrKindsExt", "reducibilityCore", "reducibilityExtra", "Lean.IR.declMapExt",
    "recExt", "Lean.Elab.Structural.eqnInfoExt", "Lean.Meta.structuralRecArgPosExt",
    "Lean.Compiler.inlineAttrs", "Lean.Compiler.specializeAttr", "Lean.Compiler.implementedByAttr",
    "Batteries.Tactic.Alias.aliasExt", "simpsAttr",
}
DECL_BOUND_PREFIXES = ("Lean.Compiler.LCNF.", "_private.Lean.Compiler.LCNF.")
# Of these, the ones that describe compiled code. A change there matters only to modules that have
# compiled code of their own.
CODE_PREFIXES = ("Lean.Compiler.", "_private.Lean.Compiler.LCNF.", "Lean.IR.")
CODE = "Lean.IR.declMapExt"
# One entry per module, about the module itself: its package, and whether importing it is deprecated.
# They say nothing new when a module comes into view or goes out of it.
PER_MODULE = {"_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt", "Lean.deprecatedModuleExt"}
NAMESPACES = "_private.Lean.Namespace.0.Lean.namespacesExt"
STRUCTURES = "_private.Lean.Structure.0.Lean.structureExt"
# Declarations Lean generates next to a user declaration; source text does not name them through `open`.
GENERATED = {"mk", "rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "ctorIdx", "toCtorIdx", "inj",
             "injEq", "sizeOf_spec", "below", "brecOn", "ibelow", "binductionOn", "elim", "ext", "ext_iff"}


def dependents(mod, changed):
    """{name hash: name} of the public constants of `mod` whose type, or whose value unless they are
    theorems, mentions a constant with a hash in `changed`. Lean may unfold them down to that constant,
    so they count as changed even when their own term is the same as before."""
    reaches = {}                 # object -> does a name in `changed` occur under it?
    def reach(ptr):
        stack = [ptr]
        while stack:
            p = stack[-1]
            if p & 1 or p in reaches: stack.pop(); continue
            tag, fields, scalars = mod.obj(p)
            if tag in (1, 2) and len(fields) == 2 and len(scalars) == 8:          # a `Name`
                reaches[p] = U64.unpack(scalars)[0] in changed; stack.pop(); continue
            todo = [f for f in fields if not f & 1 and f not in reaches]
            if todo: stack.extend(todo); continue
            reaches[p] = any(reaches[f] for f in fields if not f & 1); stack.pop()
        return not ptr & 1 and reaches[ptr]
    out = {}
    for h, (n, c) in mod.constants(0).items():
        # a theorem's proof is never unfolded, and an inductive type does not unfold to its constructors
        if reach(mod.fields(mod.fields(c)[0])[0] if mod.obj(c)[0] in (2, 5) else c): out[h] = mod.name(n)
    return out


def unscoped(mod, entry):
    """The entry inside a scoped-extension entry: `global e` (constructor 0) or `scoped namespace e` (1)."""
    tag, fields, _ = mod.obj(entry)
    return fields[-1] if tag in (0, 1) and len(fields) == tag + 1 and not fields[-1] & 1 else entry


def projection_functions(mod):
    """{(structure name hash, field index): pointer to the name of the projection function}, from the
    structure information this module declares (entries `[name, fieldNames, fieldInfo, ...]`, where
    a field's information starts with `[fieldName, projFn, ...]`)."""
    out = {}
    for e in mod.entries(0).get(STRUCTURES, ()):
        struct_name, order, infos = mod.fields(e)[:3]
        by_field = {mod.name_hash(f[0]): f[1] for f in (mod.fields(i) for i in mod.fields(infos))}
        for i, field in enumerate(mod.fields(order)):
            if mod.name_hash(field) in by_field: out[mod.name_hash(struct_name), i] = by_field[mod.name_hash(field)]
    return out


def key_anchors(mod, entry, res):
    """Names of the constants in the discrimination-tree keys of a simp lemma or instance. The entry
    can only apply to a term that contains all of them. Keys are `Key.const name arity` (constructor
    4) and `Key.proj structure index arity` (constructor 6), both without scalar data; a projection
    key stands for the projection function of that field."""
    out, seen, stack, fns = {}, set(), [entry], None
    while stack:
        p = stack.pop()
        if p & 1 or p in seen: continue
        seen.add(p)
        tag, fields, scalars = mod.obj(p)
        if tag == 4 and len(fields) == 2 and not scalars and fields[1] & 1 and not fields[0] & 1:
            out[mod.name_hash(fields[0])] = fields[0]
        elif tag == 6 and len(fields) == 3 and not scalars and fields[1] & fields[2] & 1 and not fields[0] & 1:
            fns = fns if fns is not None else projection_functions(mod)
            fn = fns.get((mod.name_hash(fields[0]), fields[1] >> 1))
            if fn: out[mod.name_hash(fn)] = fn
            res["proj"].add(mod.name_hash(fields[0]))
        else:
            stack.extend(fields)
    return out


def grind_anchors(mod, entry, res):
    """Constants a `grind` entry is indexed by. `Entry` is `ext | funCC | cases | ematch | inj`: the
    declaration of a `funCC` or `cases` entry, or the symbols of an E-matching theorem (field 4 of
    `EMatchTheorem` is `symbols : List HeadIndex`, and `HeadIndex.const` is constructor 2). The other
    kinds give none."""
    out = {}
    tag, fields, _ = mod.obj(unscoped(mod, entry))
    if tag in (1, 2) and fields and not fields[0] & 1:
        out[mod.name_hash(fields[0])] = fields[0]
    elif tag == 3:
        cell = mod.fields(fields[0])[4]
        while not cell & 1:
            head, cell = mod.fields(cell)
            t, f, sc = mod.obj(head) if not head & 1 else (None, (), b"")
            if t == 2 and len(f) == 1 and not sc: out[mod.name_hash(f[0])] = f[0]
    return out


# Extensions whose entries are looked up by the constants of a pattern. A changed entry cannot matter
# to a module that mentions none of those constants, even through definitions it could unfold.
ANCHORED = {"Lean.Meta.simpExtension": key_anchors, "Lean.Meta.instanceExtension": key_anchors,
            "Lean.Meta.Grind.grindExt": grind_anchors}
INSTANCES, SIMP, PARSER, ALIASES = "Lean.Meta.instanceExtension", "Lean.Meta.simpExtension", "Lean.Parser.parserExtension", "Lean.aliasExtension"


def user_of_removed(mod, ext, entry):
    """For an instance or simp lemma that is no longer there: the name whose users are the only modules
    that can notice, or None when a use may have left no trace.
    An instance that was used is in the term, except coercions, which are unfolded when inserted.
    A simp lemma that rewrote something is in the proof, unless it holds by `rfl` (then `dsimp` may
    have used it); a declaration that `simp` was told to unfold can only matter where it occurs."""
    tag, fields, scalars = mod.obj(unscoped(mod, entry))
    if ext == INSTANCES:        # `InstanceEntry`: keys, val, priority, globalName?, synthOrder
        keys = mod.fields(fields[0])
        head = mod.obj(keys[0]) if keys and not keys[0] & 1 else None
        if not head or head[0] != 4 or mod.name(head[1][0]).startswith("Coe"): return None
        tag, expr, _ = mod.obj(fields[1])
        return expr[0] if tag == 4 else None                   # `Expr.const`
    if tag in (1, 2): return fields[0]                          # `SimpEntry.toUnfold`, `.toUnfoldThms`
    tag, thm, flags = mod.obj(fields[0])                        # `SimpEntry.thm`: keys, levelParams, proof, priority, origin
    if len(thm) != 5 or len(flags) < 4 or flags[2] or flags[3]: return None      # flags: post, perm, rfl, backwardRfl
    tag, origin, _ = mod.obj(thm[4])
    return origin[0] if tag == 0 and origin and not origin[0] & 1 else None      # `Origin.decl`


# Lemmas Lean generates the first time something asks for them (equation lemmas, congruence lemmas for
# `simp`, match splitters, ...). They are stored in the module that asked first, so a module below
# only generates its own copy when no module it sees has one.
ON_DEMAND = re.compile(r"\.(eq_\d+|eq_def|eq_unfold|congr_simp|hcongr_\d+|congr_eq_\d+|splitter|hinj|else_eq|induct|"
                       r"induct_unfolding|fun_cases|fun_cases_unfolding|mutual_induct|partial_correctness|"
                       r"mutual_partial_correctness)$")


def mod_tag(mod, ptr): return None if ptr & 1 else mod.obj(ptr)[0]


def user_name(name):
    """Could source text refer to this name? Not if Lean generated it."""
    parts = name.split(".")
    return not any(p.startswith("_") for p in parts) and parts[-1] not in GENERATED and not parts[-1].isdigit()


def multiset(digests):
    out = {}
    for d in digests: out[d] = out.get(d, 0) + 1
    return out


def projection_shift(old, a, new, b):
    """Are both constants the same projection function `fun params self => self.i`, up to the index?
    That is how the projections after a removed structure field change. Their type is the same and
    Lean reduces them through the constructor, so terms that use them are not affected; compiled
    code, which stores the index, is."""
    (ta, fa, _), (tb, fb, _) = old.obj(a), new.obj(b)
    if ta != 1 or tb != 1: return False                 # 1: `ConstantInfo.defnInfo`
    (_, va, sa), (_, vb, sb) = old.obj(fa[0]), new.obj(fb[0])     # `DefinitionVal`: [toConstantVal, value, hints, all]
    if sa != sb or [old.digest(x) for x in va[:1] + va[2:]] != [new.digest(x) for x in vb[:1] + vb[2:]]: return False
    ea, eb = va[1], vb[1]
    while True:
        (xa, ga, _), (xb, gb, _) = old.obj(ea), new.obj(eb)
        if xa == xb == 6 and old.digest(ga[1]) == new.digest(gb[1]): ea, eb = ga[2], gb[2]     # `Expr.lam`
        else: return xa == xb == 11 and old.digest(ga[0]) == new.digest(gb[0]) and old.digest(ga[2]) == new.digest(gb[2])


def diff_module(old, new):
    """Compare the public parts of two versions of a module (None: no such module). Returns a dict with
    names   {name hash: name} constants that were added, removed or changed
    code    {name hash: name} constants of which only the compiled code changed
    proj    name hashes of structures whose constructor changed
    taint   why every module that can see this one must be compiled ("" if not)
    taken   name hashes of the namespaces it now registers
    freed   name hashes of the namespaces it no longer registers
    tokens  last components of names that source text could now resolve differently
    gone    names that source text may have meant: constants that were removed or changed, and
            constants that lost a lemma generated on demand"""
    res = {"names": {}, "code": {}, "proj": set(), "taken": set(), "freed": set(), "taint": "", "tokens": set(), "gone": set()}
    old, new = old or NOTHING, new or NOTHING
    co, cn = old.constants(0), new.constants(0)
    for h in co.keys() | cn.keys():
        a, b = co.get(h), cn.get(h)
        if a and b and old.digest(a[1]) == new.digest(b[1]): continue
        mod, (n, c) = (new, b) if b else (old, a)
        name = mod.name(n)
        if a and b and projection_shift(old, a[1], new, b[1]):
            res["code"][h] = name; continue
        res["names"][h] = name
        for m, x in ((old, a), (new, b)):
            if x and m.obj(x[1])[0] == 6:        # `ConstantInfo.ctorInfo`: field 1 of its value is `induct`
                res["proj"].add(m.name_hash(m.fields(m.fields(x[1])[0])[1]))
        if user_name(name):
            if a: res["gone"].add(name)
            else: res["tokens"].update(WORD.findall(name.rsplit(".", 1)[-1]))
        if not (a and b) and ON_DEMAND.search(name):
            # Whoever needs this lemma of the parent declaration mentions the parent, unless it asked
            # for the lemma and the proof does not name it: an unused `simp [foo]`, or one that only
            # unfolds `foo`. Then only its source shows it, and it stores its own copy once the lemma
            # is gone from here.
            parent = name.rsplit(".", 1)[0]
            res["names"].setdefault(mod.name_hash(mod.fields(n)[0]), parent)
            if a and user_name(parent): res["gone"].add(parent)
    # every constant of the module, private ones included, can be the subject of an extension entry
    every = {**old.all_names(), **new.all_names()}
    aux = {m.name_hash(n) for m in (old, new) for n in m.data(0)[3]}
    eo, en = old.entries(0), new.entries(0)
    for ext in eo.keys() | en.keys():
        if ext.endswith(".moduleSummary"): continue      # derived from the entries of the extension itself
        if ext in PER_MODULE and (old is NOTHING or new is NOTHING): continue
        do = {old.digest(e): e for e in eo.get(ext, ())}
        dn = {new.digest(e): e for e in en.get(ext, ())}
        mo, mn = multiset(old.digest(e) for e in eo.get(ext, ())), multiset(new.digest(e) for e in en.get(ext, ()))
        removed = [do[d] for d in mo if mo[d] > mn.get(d, 0)]
        added = [dn[d] for d in mn if mn[d] > mo.get(d, 0)]
        if ext == PARSER:        # a new syntax node kind alone changes no parse
            removed = [e for e in removed if mod_tag(old, unscoped(old, e)) != 1]
            added = [e for e in added if mod_tag(new, unscoped(new, e)) != 1]
        if ext == ALIASES:       # `export`: (alias, declaration). Source that says the alias resolves differently.
            for mod, changed in ((old, removed), (new, added)):
                for n in (mod.name(mod.fields(e)[0]) for e in changed):
                    if user_name(n): res["tokens"].update(WORD.findall(n.rsplit(".", 1)[-1]))
            continue
        if ext in (INSTANCES, SIMP):
            # An entry that is gone can only be noticed where it was used, when a use leaves a trace.
            # The same holds for one that went from global to scoped: it applies in fewer places.
            narrowed, open_cases = set(), []
            for e in removed:
                user = user_of_removed(old, ext, e)
                if user is None: open_cases.append(e); continue
                res["names"].setdefault(old.name_hash(user), old.name(user))
                if old.obj(e)[0] == 0: narrowed.add(old.digest(unscoped(old, e)))
            removed = open_cases
            added = [e for e in added if not (new.obj(e)[0] == 1 and new.digest(unscoped(new, e)) in narrowed)]
        if ext == NAMESPACES:
            # A module registers a namespace it declares in unless a module it sees already has.
            res["freed"].update(old.name_hash(e) for e in removed); res["taken"].update(new.name_hash(e) for e in added)
            for n in map(old.name, removed):
                if user_name(n): res["tokens"].update(WORD.findall(n.rsplit(".", 1)[-1]))
            continue
        code_only = ext.startswith(CODE_PREFIXES)
        for mod, changed in ((old, removed), (new, added)):
            for e in changed:
                if ext == STRUCTURES:
                    # field names, defaults and the like are only read to elaborate uses of the constructor
                    struct_name = mod.name_hash(mod.fields(e)[0])
                    subjects = {h for m, cs in ((old, co), (new, cn)) for h, (_, c) in cs.items()
                                if m.obj(c)[0] == 6 and m.name_hash(m.fields(m.fields(c)[0])[1]) == struct_name}
                elif ext in DECL_BOUND or ext.startswith(DECL_BOUND_PREFIXES):
                    subjects = mod.mentioned(e) & every.keys()
                elif ext in ANCHORED:
                    anchors = ANCHORED[ext](mod, e, res).keys() & every.keys()
                    if anchors & res["names"].keys(): continue      # a changed constant is in its pattern
                    subjects = set(sorted(anchors, key=lambda h: (len(every[h]), h))[-1:])
                else:
                    subjects = set()
                if code_only:      # auxiliary declarations of the code generator are not constants
                    for h in mod.mentioned(e) & aux: res["code"].setdefault(h, "")
                elif not subjects:
                    res["taint"] = res["taint"] or f"entries of {ext} changed"
                for h in subjects:
                    kind = "code" if code_only or (h in res["code"] and ext == "Lean.projectionFnInfoExt") else "names"
                    res[kind].setdefault(h, every[h])
                    if ext == "Lean.protectedExt" and user_name(every[h]): res["tokens"].update(WORD.findall(every[h].rsplit(".", 1)[-1]))
    for h in res["names"]: res["code"].pop(h, None)
    return res


def output_changes(old, new, same_sig, changed):
    """What to log after compiling a module: how its public output differs from the previous one
    (`old`, or None) and which of its constants mention a name in the collections `changed`."""
    diff = {"names": {}, "code": {}, "proj": set(), "taken": set(), "freed": set(), "taint": "", "tokens": set(), "gone": set()}
    if old is not None and (bytes(old.parts[0][2]) != bytes(new.parts[0][2]) or not same_sig):
        diff = diff_module(old, new)
        if not same_sig:         # written by `leanir`; not expected to change without the `.olean`
            for h, (n, _) in new.constants(0).items(): diff["code"].setdefault(h, new.name(n))
    known = set(diff["names"]).union(*changed)
    if known:
        for h, n in dependents(new, known).items(): diff["names"].setdefault(h, n)
    return diff


def as_line(module, diff):
    """A change in the form the rule reads: one line of the log, or a module entering or leaving view."""
    return {"m": module, "taint": diff["taint"], "tokens": sorted(diff["tokens"]), "gone": sorted(diff["gone"]),
            "last": sorted({word for name in diff["gone"] for word in WORD.findall(name.rsplit(".", 1)[-1])}),
            "shown": sorted(diff["names"].items(), key=lambda kv: kv[1])[:40],
            "names": sorted(diff["names"]), "proj": sorted(diff["proj"]), "code": sorted(diff["code"]),
            "taken": sorted(diff["taken"]), "freed": sorted(diff["freed"])}


def presence(module, mod, appeared):
    """The line for a module that a module can newly see (`appeared`) or can no longer see:
    everything in it counts as added, or as removed."""
    diff = diff_module(None, mod) if appeared else diff_module(mod, None)
    for h, (n, c) in mod.constants(0).items():
        if mod.obj(c)[0] == 6: diff["proj"].add(mod.name_hash(mod.fields(mod.fields(c)[0])[1]))
    diff["code"].update(diff["names"])
    if not appeared: diff["tokens"] = set()
    return as_line(module, diff)


# ---------------------------------------------------------------------------------------------------
# The rule.

def facts(module):
    """What the rule needs to know about a module's previous output."""
    last = len(module.parts) - 1
    declares = set()                # the namespaces of its declarations: every proper prefix of their names
    for part in {0, last}:
        for n in module.data(part)[1]:
            n = module.fields(n)[0]
            while not n & 1:
                declares.add(module.name_hash(n)); n = module.fields(n)[0]
    return {"names": module.names(), "proj": module.proj_structs(), "extra": module.extra_mod_uses(),
            "code": bool(module.entries(last).get(CODE)), "declares": declares,
            "registers": {module.name_hash(e) for e in module.entries(0).get(NAMESPACES, ())}}


def affected(get_facts, lines, source_tokens):
    """Why a module whose own inputs are unchanged must be compiled: (reason, detail), or None.
    get_facts       () -> `facts` of its previous output
    lines           the changes that concern it (see `as_line`): those logged, since its output was
                    produced or last checked, by modules it can see, and the modules that came into
                    or went out of its view
    source_tokens   () -> the words of its source"""
    if not lines: return None
    mine, tokens = get_facts(), None
    names = mine["names"]
    for line in lines:
        x = line["m"]
        if not names.isdisjoint(line["names"]):
            shown = next((n for h, n in line["shown"] if h in names), "")
            return "refers to a changed declaration", f"`{shown}` in {x}" if shown else x
        if not mine["proj"].isdisjoint(line["proj"]): return "projects from a structure whose constructor changed", x
        if mine["code"] and not names.isdisjoint(line["code"]): return "has compiled code that uses a changed declaration", x
        if not (mine["registers"].isdisjoint(line["taken"]) and mine["declares"].isdisjoint(line["freed"])):
            return "declares in a namespace whose registration moved", x
        if x in mine["extra"]: return "uses a macro, notation or attribute of a changed module", x
        if line["taint"]: return "can see a module with a change that is not tied to one declaration", f"{x}: {line['taint']}"
        if line["tokens"] or line["last"]:
            tokens = tokens if tokens is not None else source_tokens()
            clash = tokens & set(line["tokens"])
            if clash: return "source mentions a name that was added or dropped", f"`{sorted(clash)[0]}` in {x}"
            if not tokens.isdisjoint(line["last"]):
                for name in line["gone"]:
                    if tokens.issuperset(WORD.findall(name)):
                        return "source could mean a declaration that was removed or changed, or that lost a generated lemma", f"`{name}` in {x}"
    return None


# ---------------------------------------------------------------------------------------------------
# Source files.

def header(path):
    """(is it a `module`?, [(imported module, public, all, meta)]) from a source file."""
    is_module, imports, depth = False, [], 0
    public = meta = all_ = expect_name = False
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            code, i = [], 0
            while i < len(line):                         # drop `--` and (nested) `/- -/` comments
                if depth:
                    opens, closes = line.find("/-", i), line.find("-/", i)
                    if closes == -1 and opens == -1: break
                    if opens != -1 and (closes == -1 or opens < closes): depth, i = depth + 1, opens + 2
                    else: depth, i = depth - 1, closes + 2
                elif line.startswith("--", i): break
                elif line.startswith("/-", i): depth, i = 1, i + 2
                else: code.append(line[i]); i += 1
            for word in "".join(code).split():
                if expect_name and word == "all": all_ = True
                elif expect_name:
                    imports.append((word, public, all_, meta))
                    public = meta = all_ = expect_name = False
                elif word == "module": is_module = True
                elif word == "public": public = True
                elif word == "meta": meta = True
                elif word == "import": expect_name = True
                elif word not in ("prelude", "private"): return is_module, imports
    return is_module, imports


def reads_private_data(path):
    """Does the module import anything with `import all` or `meta import`, or is it not a `module`?
    Then it also depends on the private part or the compiled code of its imports."""
    is_module, imports = header(path)
    return not is_module or any(all_ or meta for _, _, all_, meta in imports)


def view(imports, module):
    """The modules `module` sees, in the order Lean loads them: its imports and what they re-export,
    each after the modules it re-exports. `imports(m)` gives [(module, public, all)] in header order.
    The order matters: of two instances that fit, Lean prefers the one loaded later."""
    out, seen = [], set()
    stack = [(None, iter([d for d, _, _ in imports(module)]))]
    while stack:
        m, deps = stack[-1]
        for d in deps:
            if d not in seen:
                seen.add(d)
                stack.append((d, iter([e for e, public, _ in imports(d) if public])))
                break
        else:
            stack.pop()
            if m is not None: out.append(m)
    return out


def reexports(imports):
    """A function from a module to a value that identifies the ordered tree of what it re-exports,
    which is what Lake hashes for each import of a module."""
    memo = {}
    def tree(m):
        if m not in memo:
            memo[m] = None
            memo[m] = hash(tuple((d, tree(d)) for d, public, _ in imports(m) if public))
        return memo[m]
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 100000))      # chains of re-exports can be long
    return tree


# An identifier as Lean reads it, without dots: it starts with a letter, `_` or a letter-like
# character (Greek but for λ, Π and Σ; ℕ, ℝ, 𝒜, ...) and goes on with these, digits, `'`, `!`, `?`
# and subscripts. So `↑foo`, `foo⁻¹` and `¬foo'` give `foo` and `foo'`.
LETTERS = "A-Za-z_\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1\u03a4-\u03a9\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
WORD = re.compile(f"[{LETTERS}][{LETTERS}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a]*")


def source_tokens(path):
    """The words of a source file: everything that can be a component of a name."""
    with open(path, encoding="utf-8", errors="replace") as f: return set(WORD.findall(f.read()))


def file_hash(path):
    with open(path, "rb") as f: return hashlib.sha256(f.read()).hexdigest()


def write_json(path, value):
    tmp = f"{path}.{os.getpid()}.tmp"
    with open(tmp, "w") as f: json.dump(value, f)
    os.replace(tmp, path)


def read_jsonl(path):
    """The records of a file with one JSON value per line, without a last line that was cut short."""
    out = []
    with open(path) as f:
        for line in f:
            try: out.append(json.loads(line))
            except ValueError: pass
    return out


# ---------------------------------------------------------------------------------------------------
# State kept in `.lake/rebuild-affected/`:
#   base/       laid out like `.lake/build`. For each module: the outputs it had when the last run
#               started (hard links), its Lake trace, and `X.mark`: the header of that output, how far
#               into the change log it is known to be consistent (`seen`) and, once Lake confirmed it,
#               the hash of its source and the `epoch` in which that was. `X.made` identifies the
#               last output this script compiled for the module
#   epoch       a counter that goes up when something happened that the log does not cover: an output
#               was replaced by Lake or by the cache, or the build settings changed. A source hash
#               from an earlier epoch proves nothing
#   project/    links to the project, with `base` as its build directory, for the first pass
#   log.lines   one line per compiled module that changed (see `as_line`): its name, then JSON
#   log.hashes  the 64-bit name hashes of those lines
#   log.shown   for each line, some of the changed names, to explain a decision, and the names of the
#               constants that were removed or changed
#   run.jsonl   what the last run did with each module Lake asked for

KINDS = ("names", "proj", "code", "taken", "freed")
FORMAT = 2          # of the files in the state directory; a run that finds another number starts over


class DamagedLog(Exception): pass


class Shown:
    """Names of a log line that are rarely needed (those it can show for a hit, and those of removed or
    changed constants), read from `log.shown` only when asked for."""
    def __init__(self, path, offset): self.path, self.offset = path, offset
    def __iter__(self):
        with open(self.path, "rb") as f:
            f.seek(self.offset)
            return iter(json.loads(f.readline()))


class State:
    def __init__(self, root):
        self.root = root
        self.base = os.path.join(root, "base")
        self.build = os.path.join(os.path.dirname(root), "build")
        self.lib = os.path.join(self.build, "lib", "lean")
        self.shadow = os.path.join(root, "project")

    def path(self, name): return os.path.join(self.root, name)

    def base_olean(self, module): return os.path.join(self.base, "lib", "lean", *module.split(".")) + ".olean"

    def lib_olean(self, module): return os.path.join(self.lib, *module.split(".")) + ".olean"

    def files(self, module):
        """(a module's file in the build directory, the same file in `base`) for all it outputs"""
        rel = os.path.join(*module.split("."))
        names = [os.path.join("lib", "lean", rel + ext) for ext in OUTPUT_EXTS] + [os.path.join("ir", rel + ".c")]
        return [(os.path.join(self.build, n), os.path.join(self.base, n)) for n in names]

    def mirror(self, module, source=None):
        """Make `base` hold what `source` (default: the build directory) holds for a module: outputs,
        saved hashes and trace. Outputs are hard links; the trace is a copy, because Lake may rewrite
        a trace in place."""
        swap = lambda path: path if source is None else os.path.join(source, os.path.relpath(path, self.build))
        for real, kept in self.files(module):
            os.makedirs(os.path.dirname(kept), exist_ok=True)
            relink(swap(real), kept); relink(swap(real) + ".hash", kept + ".hash")
        recopy(swap(self.lib_olean(module)[:-len(".olean")] + ".trace"), self.base_olean(module)[:-len(".olean")] + ".trace")

    def set_aside(self, module):
        """Keep a second copy of what `base` holds for a module that has no outputs in the build
        directory (its last compilation failed). Lake deletes the outputs in `base` if it asks for
        the module in the first pass, and there would be nothing to put back."""
        aside = self.path("aside")
        for _, kept in self.files(module):
            dst = os.path.join(aside, os.path.relpath(kept, self.base))
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            relink(kept, dst)
        trace = self.base_olean(module)[:-len(".olean")] + ".trace"
        recopy(trace, os.path.join(aside, os.path.relpath(trace, self.base)))

    def lock(self, exclusive):
        f = open(self.path("lock"), "a")
        if fcntl: fcntl.flock(f, fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH)
        return f

    def log_end(self):
        """The size of `log.lines`. If its last line was cut short (the disk was full), later lines
        would be lost in it, so such a log is neither read nor added to; `main` then starts over."""
        path = self.path("log.lines")
        size = os.path.getsize(path) if os.path.exists(path) else 0
        if size:
            with open(path, "rb") as f:
                f.seek(size - 1)
                if f.read(1) != b"\n": raise DamagedLog("the change log was cut short; delete .lake/rebuild-affected")
        return size

    def append(self, line):
        with self.lock(True):
            self.log_end()
            size = lambda name: os.path.getsize(self.path(name)) if os.path.exists(self.path(name)) else 0
            if size("log.hashes") % 8: os.truncate(self.path("log.hashes"), size("log.hashes") // 8 * 8)
            at = [size("log.hashes") // 8]
            with open(self.path("log.hashes"), "ab") as f:
                for kind in KINDS:
                    f.write(array.array("Q", line[kind]).tobytes()); at.append(at[-1] + len(line[kind]))
            shown = json.dumps(line["shown"]).encode() + b"\n"
            short = {"taint": line["taint"], "tokens": line["tokens"], "last": line["last"], "at": at, "shown": size("log.shown"),
                     "gone": size("log.shown") + len(shown), "imports": line.get("imports", True), "empty": line.get("empty", False)}
            with open(self.path("log.shown"), "ab") as f: f.write(shown + json.dumps(line["gone"]).encode() + b"\n")
            with open(self.path("log.lines"), "ab") as f: f.write((line["m"] + "\t" + json.dumps(short) + "\n").encode("utf-8"))

    def lines_since(self, seen, visible):
        """(the lines logged after position `seen` by modules in `visible`, the end of the log)"""
        with self.lock(False):
            now = self.log_end()
            if now <= seen: return [], now
            with open(self.path("log.lines"), "rb") as f:
                f.seek(seen); raw = f.read(now - seen).decode("utf-8").splitlines()
            lines = []
            for entry in raw:
                m, _, rest = entry.partition("\t")
                if m in visible:
                    line = dict(json.loads(rest), m=m)
                    if not line["empty"]: lines.append(line)       # an empty line is for `explain` only
            if lines:
                hashes = array.array("Q")
                with open(self.path("log.hashes"), "rb") as f:
                    f.seek(8 * lines[0]["at"][0]); hashes.frombytes(f.read(8 * (lines[-1]["at"][-1] - lines[0]["at"][0])))
                start = lines[0]["at"][0]
                for line in lines:
                    at = line.pop("at")
                    for i, kind in enumerate(KINDS): line[kind] = hashes[at[i] - start:at[i + 1] - start]
                    line["shown"], line["gone"] = Shown(self.path("log.shown"), line["shown"]), Shown(self.path("log.shown"), line["gone"])
        return lines, now

    def logged(self):
        """[(position of a log line, the module it is about, whether its imports changed)]"""
        if not os.path.exists(self.path("log.lines")): return []
        out, at = [], 0
        with open(self.path("log.lines"), "rb") as f:
            for entry in f:
                m, _, rest = entry.partition(b"\t")
                out.append((at, m.decode("utf-8"), json.loads(rest).get("imports", True))); at += len(entry)
        return out

    def epoch(self):
        try:
            with open(self.path("epoch")) as f: return json.load(f)
        except (OSError, ValueError): return 0

    def note(self, **kw):
        with open(self.path("run.jsonl"), "a") as f: f.write(json.dumps(kw) + "\n")

    def presence(self, module, appeared):
        """The `presence` line of a module that came into view (from its current output) or went out
        of view (from its previous output). Computed once and kept in a file."""
        olean = self.lib_olean(module) if appeared else self.base_olean(module)
        cache = os.path.join(self.root, "presence", module + (".appeared" if appeared else ".gone"))
        try:
            with open(cache) as f: line, ident = json.load(f)
            if ident == identity(olean): return line
        except (OSError, ValueError): pass
        line = presence(module, Module(olean), appeared)
        os.makedirs(os.path.dirname(cache), exist_ok=True)
        write_json(cache, [line, identity(olean)])
        return line


def identity(path):
    try: st = os.stat(path)
    except OSError: return None
    return [st.st_ino, st.st_mtime_ns, st.st_size]


def relink(src, dst):
    """Make `dst` the same file as `src` (a hard link), or remove it if there is no `src`."""
    try: os.unlink(dst)
    except OSError: pass
    if not os.path.exists(src): return
    try: os.link(src, dst)
    except OSError: shutil.copyfile(src, dst)


def recopy(src, dst):
    """Make `dst` a copy of `src`, or remove it if there is no `src`."""
    try: os.unlink(dst)
    except OSError: pass
    if os.path.exists(src): shutil.copyfile(src, dst)


def refresh_base(state):
    """Make `base/` mirror the outputs now in the build directory, and return ({module: mark}, number
    recorded, whether an output was replaced by something else than this script). A module whose
    outputs were replaced since the last run (by Lake, by this script or by the cache) is consistent
    with its imports as of now, so its mark points to the current end of the log. A module without
    outputs keeps its base."""
    repair(state)
    seen, marks, n, foreign = state.log_end(), {}, 0, False
    for d, _, files in os.walk(state.lib):
        rel = os.path.relpath(d, state.lib)
        for fn in files:
            if not fn.endswith(".trace"): continue
            name = os.path.normpath(os.path.join(rel, fn[:-6])).replace(os.sep, ".")
            stem, bstem = os.path.join(d, fn[:-6]), state.base_olean(name)[:-len(".olean")]
            ident = [identity(stem + ".olean"), identity(stem + ".trace")]
            if ident[0] is None: continue
            try:
                with open(bstem + ".mark") as f: mark = json.load(f)
                if mark["id"] == ident:
                    marks[name] = mark; continue
            except (OSError, ValueError, KeyError): mark = {}
            state.mirror(name)
            marks[name] = {"id": ident, "seen": seen, "imports": Module(stem + ".olean").imports()}
            if mark.get("id", [None])[0] == ident[0]:
                # the same output file with a new trace: this script put it back, so its source is the same
                marks[name].update({key: mark[key] for key in ("src", "epoch") if key in mark})
            else:
                try:
                    with open(bstem + ".made") as f: foreign = foreign or json.load(f) != ident[0]
                except (OSError, ValueError): foreign = True
            write_json(bstem + ".mark", marks[name])
            n += 1
    base_lib = os.path.join(state.base, "lib", "lean")
    shutil.rmtree(state.path("aside"), ignore_errors=True)
    for d, _, files in os.walk(base_lib):            # modules that have no outputs right now
        for fn in files:
            name = os.path.normpath(os.path.join(os.path.relpath(d, base_lib), fn[:-5])).replace(os.sep, ".")
            if fn.endswith(".mark") and name not in marks:
                with open(os.path.join(d, fn)) as f: marks[name] = json.load(f)
                state.set_aside(name)
    return marks, n, foreign


def repair(state):
    """Undo what the first pass did to `base` for the modules Lake asked for there (it deleted their
    outputs and wrote new traces). Also run at the start, in case the last run was interrupted.
    Returns what Lake asked for."""
    if not os.path.exists(state.path("probe.jsonl")): return []
    asked = read_jsonl(state.path("probe.jsonl"))
    for r in asked:
        state.mirror(r["m"], None if os.path.exists(state.lib_olean(r["m"])) else state.path("aside"))
    os.unlink(state.path("probe.jsonl"))
    return asked


# ---------------------------------------------------------------------------------------------------
# The `lean` wrapper.

class Job:
    """One call of `lean` by Lake: `lean ARGS FILE -o OLEAN -i ILEAN [-c C] --setup SETUP --json`."""

    def __init__(self, state, mode, argv):
        self.state, self.mode, self.argv = state, mode, argv
        i = argv.index("-o")
        self.src, self.olean = argv[i - 1], argv[i + 1]
        with open(argv[argv.index("--setup") + 1]) as f: self.setup = json.load(f)
        self.name = self.setup["name"]
        self.inside = os.path.abspath(self.olean) == state.lib_olean(self.name)
        self.stem = state.base_olean(self.name)[:-len(".olean")]
        self.wants_c = "-c" in argv
        self.changed = []

    def mark(self):
        """The mark of the previous output, if there is one that is still the recorded file."""
        try:
            with open(self.stem + ".mark") as f: mark = json.load(f)
        except (OSError, ValueError): return None
        return mark if self.inside and mark["id"][0] == identity(self.stem + ".olean") else None

    def decide(self):
        """(None, log position) to reuse the previous output, else (reason, detail) to compile."""
        st, mark, own = self.state, self.mark(), self.name in self.mode["own"]
        if mark is None: return ("its own inputs changed" if own else "has no previous output"), ""
        visible = set(self.setup.get("importArts", {}))
        lines, now = st.lines_since(mark["seen"], visible)
        # Also needed when the module is compiled whatever the lines say: a definition that it leaves
        # as it was counts as changed, for the modules below, if it mentions a changed constant.
        self.changed = [line["names"] for line in lines]
        if own: return "its own inputs changed", ""
        if self.wants_c != os.path.exists(st.files(self.name)[-1][1]): return "has no previous output", ""
        if reads_private_data(self.src): return "uses `import all` or `meta import`, or is not a `module`", ""
        if self.name in self.mode["sees"]:        # it sees other modules than when it was last compiled
            try:
                with open(self.stem + ".vis") as f: vis = json.load(f)
            except (OSError, ValueError): return "sees other modules than before", ""
            ours = sorted(m for m in visible if os.path.exists(st.lib_olean(m)))
            if vis["run"] != self.mode["run"] or vis["sees"] != ours: return "sees other modules than before", ""
            lines = lines + [st.presence(m, True) for m in vis["gained"]] + [st.presence(m, False) for m in vis["lost"]]
        why = affected(lambda: facts(Module(self.stem + ".olean")), lines, lambda: source_tokens(self.src))
        return why or (None, now)

    def reuse(self, now):
        for real, kept in self.state.files(self.name): relink(kept, real)
        write_json(self.stem + ".mark", dict(self.mark(), seen=now))

    def record_changes(self):
        """After a successful compile: log what changed. Returns whether the public `.olean` did."""
        if not self.inside: return False
        def same(ext):
            a, b = self.stem + ext, self.olean[:-len(".olean")] + ext
            if not (os.path.exists(a) and os.path.exists(b)): return os.path.exists(a) == os.path.exists(b)
            with open(a, "rb") as f, open(b, "rb") as g: return f.read() == g.read()
        old, new = Module(self.stem + ".olean") if self.mark() else None, Module(self.olean)
        diff = output_changes(old, new, same(".ir.sig"), self.changed)
        if old is None and os.path.exists(self.stem + ".mark"):
            diff["taint"] = "its previous output is no longer there to compare with"
        # A change of its imports is logged too, in a line that is otherwise empty if nothing else
        # changed: what a module below saw before is worked out from the headers of the outputs that
        # are there now (see `explain`), which is wrong once one of them has changed. Such a line
        # changes nothing for the rule: what the module brings into view or takes out of it is
        # accounted for where a module below is found to see other modules than before.
        imports = old is None or old.imports() != new.imports()
        if imports or any(diff.values()):
            self.state.append(dict(as_line(self.name, diff), imports=imports, empty=not any(diff.values())))
        return old is not None and not same(".olean")

    def stamp(self):
        """Note which output this script produced, to tell it later from one that Lake or the cache put there."""
        if self.inside:
            os.makedirs(os.path.dirname(self.stem), exist_ok=True)
            write_json(self.stem + ".made", identity(self.olean))


def output_paths(argv):
    """The files a call of `lean` by Lake writes."""
    olean = argv[argv.index("-o") + 1]
    paths = [olean[:-len(".olean")] + ext for ext in OUTPUT_EXTS if ext != ".ilean"]
    return paths + [argv[argv.index(flag) + 1] for flag in ("-i", "-c") if flag in argv]


def probe(state, argv):
    """First pass, on `base`. Every module Lake asks for gets its previous output back: from the build
    directory, or from the copy set aside if it has none there, or empty files if it never had one
    (Lake only hashes them)."""
    with open(argv[argv.index("--setup") + 1]) as f: name = json.load(f)["name"]
    i = argv.index("-o")
    with state.lock(True), open(state.path("probe.jsonl"), "a") as f:
        f.write(json.dumps({"m": name, "src": argv[i - 1]}) + "\n")
    asked_for = {os.path.realpath(path) for path in output_paths(argv)}
    if os.path.realpath(state.base_olean(name)) not in asked_for:
        sys.stderr.write(f"rebuild-affected: {name} is not a module of this package and is not built; "
                         "build the dependencies first (`lake exe cache get`)\n")
        return 1
    for real, kept in state.files(name):
        if os.path.realpath(kept) not in asked_for: continue          # e.g. no `.c` wanted
        os.makedirs(os.path.dirname(kept), exist_ok=True)
        aside = os.path.join(state.path("aside"), os.path.relpath(kept, state.base))
        relink(real if os.path.exists(real) else aside, kept)
        if not os.path.exists(kept): open(kept, "wb").close()
    return 0


UNKNOWN = {"names": {}, "code": {}, "proj": set(), "taken": set(), "freed": set(), "tokens": set(), "gone": set()}


def wrapper(real, root, argv):
    if "-o" not in argv or "--setup" not in argv: os.execv(real, [real] + argv)
    state, t = State(root), time.time()
    with open(state.path("mode")) as f: mode = json.load(f)
    if mode["probe"]: return probe(state, argv)
    mode["own"], mode["sees"] = set(mode["own"]), set(mode["sees"])
    # A problem with reading the previous output must never lead to reusing it, and a module whose
    # change cannot be worked out counts as changed in a way that concerns every module that sees it.
    job, name = None, os.path.relpath(argv[argv.index("-o") + 1], state.lib)[:-len(".olean")].replace(os.sep, ".")
    try:
        job = Job(state, mode, argv)
        why, detail = job.decide()
    except Exception as e:
        job, why, detail = None, "could not be checked", f"{type(e).__name__}: {e}"
    if why is None:
        job.reuse(detail)
        state.note(m=job.name, reuse=True, argv=argv, path=os.environ.get("LEAN_PATH", ""), s=round(time.time() - t, 3))
        return 0
    # Lake has already deleted the old outputs. Make sure of it: they may be the same files as the
    # copies in `base` (hard links), which must survive the compilation to be compared with its result.
    for path in output_paths(argv):
        try: os.unlink(path)
        except OSError: pass
    rc = subprocess.call([real] + argv)
    changed = False
    if rc == 0:
        try:
            if job is None: raise RuntimeError(detail)
            changed = job.record_changes()
            job.stamp()
        except Exception as e:
            state.append(as_line(name, dict(UNKNOWN, taint=f"its change could not be worked out ({type(e).__name__}: {e})")))
            changed = True
    state.note(m=name, reuse=False, why=why, detail=detail, rc=rc, changed=changed, s=round(time.time() - t, 3))
    return rc


# ---------------------------------------------------------------------------------------------------
# The driver.

REPLAYED = re.compile(r"^\S+ \[\d+/\d+\] Replayed (\S+)$", re.M)
# The toolchains for which the layouts read above were compared with the Lean source: `ModuleData`,
# `ConstantInfo`, `Import`, the entries of the simp, instance and `grind` extensions, and the keys of
# discrimination trees. A Lean release can change any of them without changing the version of the
# `.olean` format, and the rule would then go wrong silently, so compare them again before adding one.
CHECKED_TOOLCHAINS = ("leanprover/lean4:v4.37.0-rc1",)


def prepare(project):
    """Create the state directory, a copy of the toolchain directory whose `lean` is this script, and
    a directory of links to the project whose build directory is `base`."""
    state = State(os.path.join(project, ".lake", "rebuild-affected"))
    os.makedirs(state.base, exist_ok=True)
    sysroot = subprocess.run(["lean", "--print-prefix"], check=True, capture_output=True, text=True, cwd=project).stdout.strip()
    real = os.path.join(sysroot, "bin", "lean")
    toolchain = state.path("sysroot")
    shutil.rmtree(toolchain, ignore_errors=True)
    os.makedirs(os.path.join(toolchain, "bin"))
    for sub in ("", "bin"):
        for entry in os.listdir(os.path.join(sysroot, sub)):
            if (sub, entry) not in (("", "bin"), ("bin", "lean")):
                os.symlink(os.path.join(sysroot, sub, entry), os.path.join(toolchain, sub, entry))
    with open(os.path.join(toolchain, "bin", "lean"), "w") as f:
        f.write(f'#!/bin/sh\nexec "{sys.executable}" "{os.path.abspath(__file__)}" --as-lean "{real}" "{state.root}" "$@"\n')
    os.chmod(os.path.join(toolchain, "bin", "lean"), 0o755)
    shutil.rmtree(state.shadow, ignore_errors=True)
    os.makedirs(os.path.join(state.shadow, ".lake"))
    for sub in ("", ".lake"):
        for entry in os.listdir(os.path.join(project, sub)):
            if (sub, entry) not in (("", ".lake"), (".lake", "build"), (".lake", "rebuild-affected")):
                os.symlink(os.path.join(project, sub, entry), os.path.join(state.shadow, sub, entry))
    os.symlink(state.base, os.path.join(state.shadow, ".lake", "build"))
    # Without the artifact cache, every module Lake finds out of date goes through the wrapper.
    return state, dict(os.environ, LAKE_OVERRIDE_LEAN="true", LEAN_SYSROOT=toolchain, LAKE_ARTIFACT_CACHE="false"), real


def probe_pass(state, env, lake_args):
    """Run the first pass. Returns what the wrapper was asked for, and the modules Lake found up to date."""
    write_json(state.path("mode"), {"probe": True})
    p = subprocess.run(["lake", "build", "-v"] + lake_args, env=env, cwd=state.shadow, capture_output=True,
                       encoding="utf-8", errors="replace")
    asked = repair(state)
    if p.returncode != 0:
        lines = [l for l in p.stdout.splitlines() if "Replayed" not in l and not l.startswith(("trace:", "warning:", "info:"))]
        print("\n".join(lines[-60:])); sys.stderr.write(p.stderr[-3000:])
        sys.exit("rebuild-affected: Lake failed before any module was compiled (see above)")
    return asked, set(REPLAYED.findall(p.stdout))


def source_roots(project):
    """Directories that can hold the source of a module, from `lakefile.toml`. Without them (a
    `lakefile.lean`) no source is found, and every module that sees other modules is compiled."""
    try:
        with open(os.path.join(project, "lakefile.toml"), "rb") as f: text = f.read()
    except OSError: return []
    try:
        import tomllib
        conf = tomllib.loads(text.decode("utf-8"))
        top, libs = conf.get("srcDir", "."), [lib["srcDir"] for lib in conf.get("lean_lib", []) if "srcDir" in lib]
    except ImportError:          # Python before 3.11: read the `srcDir` lines, the first section being the package
        package, *sections = re.split(r"(?m)^\[", text.decode("utf-8"))
        find = lambda part: re.findall(r"""(?m)^\s*srcDir\s*=\s*["']([^"']*)["']""", part)
        top, libs = (find(package) or ["."])[0], [d for part in sections for d in find(part)]
    except ValueError: return []
    top = os.path.join(project, top)
    return list(dict.fromkeys([top] + [os.path.join(top, d) for d in libs]))


def explain(state, project, marks, asked, replayed, epoch, run):
    """Sort the modules of the first pass into those to compile for their own sake and those that only
    see other modules than before. The second kind needs a source that is known to be what the
    previous output was built from, and known since nothing happened that the log does not cover
    (`epoch`); what such a module gained and lost is written to `X.vis`.
    Also records the source of every module Lake found up to date, for later runs."""
    roots = source_roots(project)
    def source(m):
        for root in roots:
            p = os.path.join(root, *m.split(".")) + ".lean"
            if os.path.exists(p): return p
    own, maybe, sees_other = [], [], []
    for r in asked:
        mark = marks.get(r["m"])
        same = mark and "imports" in mark and mark.get("epoch") == epoch and mark.get("src") == file_hash(r["src"])
        (maybe if same else own).append(r["m"])
    if maybe:
        # Modules of other packages are followed no further: they do not change between runs.
        # (`Init` is imported implicitly: it is in the header of an output but not in the source.)
        memo = {}, {}
        def before(m):
            if m not in memo[0]: memo[0][m] = [i for i in marks[m]["imports"] if i[0] != "Init"] if "imports" in marks.get(m, ()) else []
            return memo[0][m]
        def after(m):
            if m not in memo[1]: memo[1][m] = [i[:3] for i in header(source(m))[1] if i[0] != "Init"] if source(m) else []
            return memo[1][m]
        inside = lambda m: m in marks or source(m)
        tree_before, tree_after = reexports(before), reexports(after)
        last, moved = {}, {}          # module -> where its last log line is, and the last that changed its imports
        for at, x, imports in state.logged():
            last[x] = at
            if imports: moved[x] = at
        for m in maybe:
            old, new = view(before, m), view(after, m)
            old_set, new_set = set(old), set(new)
            seen = marks[m]["seen"]
            if any(moved.get(x, -1) >= seen for x in old):
                # A module it sees was compiled with other imports in an earlier run that did not get
                # as far as this one. Then `old` is not what its previous output saw.
                own.append(m); continue
            if old == new:
                # Lean loads the same modules in the same order. Lake asked because the trees of
                # re-exports differ, or because a module it sees changed in an earlier run that did
                # not get as far as this one. Either way it is an ordinary module for the second pass.
                if ([(d, tree_before(d)) for d, _, _ in before(m)] == [(d, tree_after(d)) for d, _, _ in after(m)]
                        and not any(last.get(x, -1) >= seen for x in old)):
                    own.append(m)
                continue
            # It is left to the rule only if modules of this package came or went and the others are
            # loaded in the same order as before. Otherwise Lake wanted it for a reason we cannot name.
            if (not all(inside(x) for x in old_set ^ new_set)
                    or [x for x in old if x in new_set] != [x for x in new if x in old_set]):
                own.append(m); continue
            write_json(state.base_olean(m)[:-len(".olean")] + ".vis",
                       {"run": run, "sees": sorted(x for x in new if inside(x)), "gained": sorted(new_set - old_set),
                        "lost": sorted(old_set - new_set)})
            sees_other.append(m)
    for m in replayed:
        mark = marks.get(m)
        if mark and not ("src" in mark and mark.get("epoch") == epoch) and source(m):
            write_json(state.base_olean(m)[:-len(".olean")] + ".mark", dict(mark, src=file_hash(source(m)), epoch=epoch))
    return own, sees_other


def last_run(state):
    return read_jsonl(state.path("run.jsonl")) if os.path.exists(state.path("run.jsonl")) else []


def summarize(state, seconds):
    runs = last_run(state)
    compiled = [r for r in runs if not r["reuse"]]
    print(f"rebuild-affected: compiled {len(compiled)} modules, {sum(r['changed'] for r in compiled)} of them with a changed "
          f"public output; reused the previous output of {len(runs) - len(compiled)}; {seconds:.0f} s")
    reasons = {}
    for r in compiled: reasons.setdefault(r["why"], []).append(r)
    for why, rs in sorted(reasons.items(), key=lambda kv: -len(kv[1])):
        example = next((f", e.g. {r['m']}: {r['detail']}" for r in rs if r["detail"]), "")
        print(f"  {len(rs):6d}  {why}{example}")


def check_one(state, real, project, r):
    """Compile a reused module again, into a scratch directory. Returns what differs, or None."""
    argv = [a for a in r["argv"] if a != "--json"]
    i = argv.index("-o")
    src, olean = argv[i - 1], argv[i + 1]
    out = os.path.join(state.path("check"), os.path.relpath(olean, state.build))
    os.makedirs(os.path.dirname(out), exist_ok=True)
    argv[i + 1] = out
    kept = {}
    for flag, ext in (("-i", ".ilean"), ("-c", ".c")):
        if flag in argv:
            j = argv.index(flag) + 1
            kept[out[:-len(".olean")] + ext], argv[j] = argv[j], out[:-len(".olean")] + ext
    p = subprocess.run([real] + argv, capture_output=True, encoding="utf-8", errors="replace", cwd=project,
                       env=dict(os.environ, LEAN_PATH=r["path"]))
    if p.returncode != 0: return "it no longer compiles\n" + (p.stdout + p.stderr)[-3000:]
    # A previous output may come from the cache, which was built in another directory, and linter
    # messages stored in the `.olean` hold the absolute path of the source file.
    rel = os.path.relpath(src, project).encode()
    norm = lambda s: rel if s.endswith(rel) and s[:1] == b"/" else s
    same = same_module(Module(olean, norm), Module(out, norm))
    for new, old in kept.items():
        with open(new, "rb") as f, open(old, "rb") as g: same = same and f.read() == g.read()
    return None if same else "compiling it again gives another output"


def check(state, real, n, project):
    """Compile `n` of the modules the last run reused again and compare. Returns how many differ."""
    reused = [r for r in last_run(state) if r["reuse"]]
    sample = random.sample(reused, min(n, len(reused)))
    with ThreadPoolExecutor(max(1, (os.cpu_count() or 2) // 2)) as pool:
        results = list(pool.map(lambda r: check_one(state, real, project, r), sample))
    shutil.rmtree(state.path("check"), ignore_errors=True)
    for r, what in zip(sample, results):
        if what: print(f"  DIFFERENT {r['m']}: {what}")
    bad = sum(1 for what in results if what)
    print(f"rebuild-affected: compiled {len(sample)} of {len(reused)} reused modules again; {bad} differ")
    return bad


def main(argv):
    if argv[:1] == ["--as-lean"]: return wrapper(argv[1], argv[2], argv[3:])
    n_check, build = 0, True
    if argv[:1] in (["--check"], ["--check-only"]): n_check, build, argv = int(argv[1]), argv[0] == "--check", argv[2:]
    project = os.getcwd()
    if os.name == "nt": sys.exit("rebuild-affected: not supported on Windows (the stand-in for `lean` is a shell script)")
    if not any(os.path.exists(os.path.join(project, f)) for f in ("lakefile.toml", "lakefile.lean")):
        sys.exit("rebuild-affected: run this from the directory that holds the lakefile")
    try:
        with open(os.path.join(project, "lean-toolchain")) as f: toolchain = f.read().strip()
    except OSError: toolchain = "no `lean-toolchain` file"
    if toolchain not in CHECKED_TOOLCHAINS:
        sys.exit(f"rebuild-affected: this script reads compiled modules of {' or '.join(CHECKED_TOOLCHAINS)} and has not been "
                 f"checked with another toolchain (here: {toolchain}). See CHECKED_TOOLCHAINS in the script.")
    state, env, real = prepare(project)
    if not build: return 1 if check(state, real, n_check, project) else 0
    # Three cases in which what earlier runs recorded is dropped. That is safe: whatever Lake then
    # asks for in the first pass is compiled, and the rule applies from there on.
    forget, used = None, os.path.isdir(os.path.join(state.base, "lib"))
    try: state.log_end()
    except DamagedLog: forget = "the change log of an earlier run was cut short"
    if not forget and used and not os.path.isdir(state.lib):
        forget = "the build directory was removed"      # `lake clean`: the outputs are not wanted back
    try:
        with open(state.path("format")) as f: same_format = json.load(f) == FORMAT
    except (OSError, ValueError): same_format = not used
    if not forget and not same_format: forget = "another version of this script wrote its state"
    if forget:
        print(f"rebuild-affected: {forget}; starting over without what earlier runs recorded", flush=True)
        shutil.rmtree(state.root)
        state, env, real = prepare(project)
    write_json(state.path("format"), FORMAT)
    t = time.time()
    marks, n, foreign = refresh_base(state)
    print(f"rebuild-affected: recorded the current outputs of {n} modules ({time.time() - t:.0f} s)", flush=True)
    # Two things can change what a module depends on without a line in the log: an output replaced by
    # Lake or by the cache, and the build settings. After either, a module counts as unchanged only
    # once Lake has found it up to date again.
    settings = {f: file_hash(os.path.join(project, f)) for f in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
                if os.path.exists(os.path.join(project, f))}
    try:
        with open(state.path("settings")) as f: settings_same = json.load(f) == settings
    except (OSError, ValueError): settings_same = False
    epoch = state.epoch()
    if foreign or not settings_same:
        if epoch: print("rebuild-affected: outputs were replaced by something else than this script since its last run, or the build "
                        "settings changed; the modules that are out of date for it are compiled", flush=True)
        epoch += 1
        write_json(state.path("epoch"), epoch); write_json(state.path("settings"), settings)
    t = time.time()
    asked, replayed = probe_pass(state, env, argv)
    own, sees_other = explain(state, project, marks, asked, replayed, epoch, run=t)
    print(f"rebuild-affected: {len(own)} modules have changed inputs of their own, {len(sees_other)} see other modules "
          f"than before ({time.time() - t:.0f} s)", flush=True)
    write_json(state.path("mode"), {"probe": False, "own": own, "sees": sees_other, "run": t})
    if os.path.exists(state.path("run.jsonl")): os.unlink(state.path("run.jsonl"))
    rc = subprocess.call(["lake", "build"] + argv, env=env, cwd=project)
    summarize(state, time.time() - t)
    if n_check and rc == 0 and check(state, real, n_check, project): rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
