"""Replay the rule of `rebuild-affected.py` over one merged batch, with the outputs CI published.

usage: batch_replay.py META HIST REPO BATCH [ancestors|global] [direct] [probe]

META and HIST are the directories of fetch_meta.py and batch_extract.py; REPO is a clone that has
the commits; BATCH is 1 for b2, ..., 19 for b20.

For every module that Lake compiled again in the batch (its input hash differs between the two
trees), in an order in which imports come first, the rule decides from the old outputs whether the
script would compile it. If so, its new output is the one CI published, and what changed in it is
logged for the modules below, with the script's own code. If not, the module is reused, and it is a
MISS when the output CI published for the new tree differs from the old one. Outputs are compared in
seven parts, with absolute source paths cut to `src/...`; parts that differ only in the order of
stored linter messages or in the numbering of the compiler's local variables count as equal.

Which modules Lake asks for in the script's first pass is modelled from the sources: edited and new
modules, and modules for which the ordered tree of re-exports behind an import changed.

Options, for experiments: `ancestors` and `global` show a module more changes than the script does
(those of everything it imports directly or not, or of everything before it in the order); `direct`
does not follow definitions that mention a changed constant; `probe` compiles every module whose
import structure changed.

Writes HIST/replay-b<N>-*.json (the counts), .compiled.tsv (each compiled module with the reason)
and .lines.jsonl (what was logged)."""
import array, collections, importlib.util, json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
def load(name, file):
    spec = importlib.util.spec_from_file_location(name, next(p for p in (os.path.join(HERE, file), os.path.join(HERE, "..", file)) if os.path.exists(p)))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
ra, bx = load("ra", "rebuild-affected.py"), load("bx", "batch_extract.py")

meta, out, repo, k = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
order = next((o for o in ("global", "ancestors") if o in sys.argv[5:]), "visible")
precise = "probe" not in sys.argv[5:]       # `probe`: compile every module that sees other modules than before
deep = "direct" not in sys.argv[5:]
old_sha, new_sha = bx.COMMITS[k - 1], bx.COMMITS[k]
A, B = bx.manifest(meta, old_sha), bx.manifest(meta, new_sha)
T0 = time.time()

# ---- sources
def tree(sha):
    d = os.path.join(out, "src", sha)
    if not os.path.isdir(d):
        os.makedirs(d + ".tmp", exist_ok=True)
        git = subprocess.Popen(["git", "-C", repo, "archive", sha, "src"], stdout=subprocess.PIPE)
        subprocess.run(["tar", "-x", "-C", d + ".tmp"], stdin=git.stdout, check=True)
        if git.wait(): raise RuntimeError(f"git archive {sha} failed")
        os.rename(d + ".tmp", d)
    return os.path.join(d, "src")

def headers(src, known):
    """{module: [(imported module, public, meta, all)]} for the project modules in `known`."""
    res = {}
    for m in known:
        p = os.path.join(src, *m.split(".")) + ".lean"
        res[m] = [(d, public, meta, all_) for d, public, all_, meta in ra.header(p)[1]] if os.path.exists(p) else []
    return res

src_old, src_new = tree(old_sha), tree(new_sha)
H, H_old = headers(src_new, B), headers(src_old, A)
mods = list(B)
mods_all = list(B) + [m for m in A if m not in B]
outside = sorted({d for h in (H, H_old) for es in h.values() for d, *_ in es} - set(mods_all))   # modules of other packages
mods_all += outside
idx = {m: i for i, m in enumerate(mods_all)}
for h in (H, H_old):
    for m in outside: h[m] = []
OUTSIDE = sum(1 << idx[m] for m in outside)

def closures(H):
    """anc: all transitive imports; pub: what a module re-exports; vis: what it can see."""
    anc, pub, vis, state = {}, {}, {}, {}
    for root in H:
        if root in state: continue
        stack = [(root, iter(H[root]))]; state[root] = 1
        while stack:
            m, it = stack[-1]
            for d, *_ in it:
                if d not in state:
                    state[d] = 1; stack.append((d, iter(H[d]))); break
            else:
                a = p = v = 0
                for d, public, _, all_ in H[m]:
                    bit = 1 << idx[d]
                    a |= bit | anc[d]
                    v |= bit | pub[d] | (vis[d] if all_ else 0)
                    if public: p |= bit | pub[d]
                anc[m], pub[m], vis[m] = a, p, v
                stack.pop()
    return anc, pub, vis

anc, pub, vis = closures(H)
_, pub_old, vis_old = closures(H_old)
topo = sorted(mods, key=lambda m: anc[m].bit_count())
print(f"batch b{k + 1} {old_sha} -> {new_sha}: {len(B)} modules, graph {time.time() - T0:.0f}s", flush=True)

diff = subprocess.run(["git", "-C", repo, "diff", "--name-only", "-z", old_sha, new_sha, "--", "src"], capture_output=True, check=True).stdout.decode().split("\0")
S = {f[4:-5].replace("/", ".") for f in diff if f.startswith("src/") and f.endswith(".lean")}
R = [m for m in topo if m not in A or A[m][0] != B[m][0]]

# In the probe pass every output is put back, so Lake still asks for a module with unchanged source
# only when the list of modules behind one of its imports changed (Lake hashes that list).
def brings(H):
    """For each module, a hash of the ordered list of what importing it brings along, as Lake hashes it."""
    memo = {}
    def go(m):
        if m not in memo:
            memo[m] = 0
            memo[m] = hash(tuple((d, go(d)) for d, public, _, _ in H.get(m, ()) if public))
        return memo[m]
    return go
seq_old, seq_new = brings(H_old), brings(H)
SEES_OTHER = {m for m in R if m in A and m not in S and any(d not in H_old or seq_old(d) != seq_new(d) for d, *_ in H[m])}
# Of these, the script leaves to the rule only those for which modules of this package came or went
# and the others are loaded in the same order as before.
def lean_order(H):
    cache = {}
    def imports(m):
        if m not in cache: cache[m] = [(d, public, all_) for d, public, _, all_ in H.get(m, ())]
        return cache[m]
    return lambda m: ra.view(imports, m)
order_old, order_new = lean_order(H_old), lean_order(H)
out_set = set(outside)
SEES_OUTSIDE, SAME_VIEW, why_seen = set(), set(), collections.Counter()
for m in SEES_OTHER:
    old, new = order_old(m), order_new(m)
    old_set, new_set = set(old), set(new)
    if old == new: SAME_VIEW.add(m); why_seen["same modules in the same order"] += 1
    elif (old_set ^ new_set) & out_set: SEES_OUTSIDE.add(m); why_seen["modules of other packages came or went"] += 1
    elif [x for x in old if x in new_set] != [x for x in new if x in old_set]: SEES_OUTSIDE.add(m); why_seen["another order"] += 1
    else: why_seen["modules of this package came or went, same order"] += 1
SEES_OTHER -= SAME_VIEW          # Lake's hash changed, but what Lean loads did not
print(f"  import structure changed for {len(SEES_OTHER) + len(SAME_VIEW)}: {dict(why_seen)}, {time.time() - T0:.0f}s", flush=True)

if "vissize" in sys.argv[5:]:
    sizes = sorted(vis[m].bit_count() for m in mods)
    inside = sorted((vis[m] & ~OUTSIDE).bit_count() for m in mods)
    q = lambda v, p: v[min(len(v) - 1, len(v) * p // 100)]
    print("visible modules per module: all", [q(sizes, p) for p in (50, 90, 99, 100)], "inside the package", [q(inside, p) for p in (50, 90, 99, 100)])
    sys.exit(0)
if "graphonly" in sys.argv[5:]:
    dep = [m for m in R if m in A and m not in S]
    changed_vis = [m for m in dep if m in vis_old and vis_old[m] != vis[m]]
    lost = sum(1 for m in changed_vis if vis_old[m] & ~vis[m]); gained = sum(1 for m in changed_vis if vis[m] & ~vis_old[m])
    print(json.dumps({"batch": f"b{k + 1}", "recompiled": len(R), "edited_or_new": len(R) - len(dep), "lake_sees_other": len(SEES_OTHER),
                      "visible_set_changed": len(changed_vis), "lost_some": lost, "gained_some": gained}))
    sys.exit(0)

# ---- records
class Stored(ra.Module):
    """A module version as kept by batch_extract: the public .olean and the hashes of all constants."""
    def __init__(self, ltar):
        self.rp = bx.rec_path(out, ltar)
        super().__init__(self.rp + ".olean")
        self.parts, self.roots = self.parts[:1], self.roots[:1]
    def all_names(self):
        public = {h: self.name(n) for h, (n, _) in self.constants(0).items()}
        with open(self.rp + ".all", "rb") as f: a = array.array("Q"); a.frombytes(f.read())
        return {h: public.get(h, "<private>") for h in a}

def record(ltar, module=None, input_hash=None):
    rp = bx.rec_path(out, ltar)
    if not os.path.exists(rp + ".json"):
        err = bx.work((out, ltar, module, input_hash))
        if err: raise RuntimeError(err)
    with open(rp + ".json") as f: return json.load(f)

def declares_of(ltar):
    """Prefix hashes of the names of the module's public constants (private ones are not kept)."""
    mod, out = Stored(ltar), set()
    for n in mod.data(0)[1]:
        n = mod.fields(n)[0]
        while not n & 1:
            out.add(mod.name_hash(n)); n = mod.fields(n)[0]
    return out

def names_of(ltar):
    with open(bx.rec_path(out, ltar) + ".names", "rb") as f: a = array.array("Q"); a.frombytes(f.read())
    return set(a)

# ---- the change log
lines = []                                    # as `as_line`, plus "i": the index of the module

_presence = {}
def presence_of(x, appeared):
    """Everything in module `x` appearing (its new version) or disappearing (its old version)."""
    if (x, appeared) not in _presence:
        man = B if appeared else A
        record(man[x][1], x, man[x][0])
        _presence[x, appeared] = ra.presence(x, Stored(man[x][1]), appeared)
    return _presence[x, appeared]

def same_but_for_order(m):
    """Fetch both bundles again and compare them with `same_module`."""
    import shutil
    pair = []
    for side, man in (("old", A), ("new", B)):
        dest = os.path.join(bx.TMP, f"cmp-{os.getpid()}-{side}"); shutil.rmtree(dest, ignore_errors=True)
        pair.append((ra.Module(bx.fetch(man[m][1], man[m][0], dest), bx.norm), dest))
    same = ra.same_module(pair[0][0], pair[1][0])
    for _, dest in pair: shutil.rmtree(dest, ignore_errors=True)
    return same

def tokens(m): return ra.source_tokens(os.path.join(src_new, *m.split(".")) + ".lean")

stats, misses, compiled = collections.Counter(), [], []
for n, m in enumerate(R):
    new = record(B[m][1])
    old = record(A[m][1]) if m in A else None
    truly = old is None or old["fp"] != new["fp"]
    scope = {"visible": vis[m], "ancestors": anc[m], "global": -1}[order]
    mine = [line for line in lines if scope >> line["i"] & 1]
    concern = mine
    if old is None: why = ("new module", "")
    elif m in S: why = ("source changed", "")
    elif m in SEES_OTHER and (not precise or m in SEES_OUTSIDE): why = ("sees a different set of modules", "")
    elif ra.reads_private_data(os.path.join(src_new, *m.split(".")) + ".lean"): why = ("uses `import all` or `meta import`, or is not a `module`", "")
    else:
        facts = lambda: {"names": names_of(A[m][1]), "proj": set(old["proj"]), "extra": set(old["extra"]), "code": old["code"],
                         "declares": declares_of(A[m][1]),
                         "registers": {Stored(A[m][1]).name_hash(e) for e in Stored(A[m][1]).entries(0).get(ra.NAMESPACES, ())}}
        if m in SEES_OTHER:          # it sees other modules than before: what it gained appears, what it lost disappears
            stats["sees other modules"] += 1
            for bits, appeared in ((vis[m] & ~vis_old[m], True), (vis_old[m] & ~vis[m], False)):
                while bits:
                    low = bits & -bits; bits ^= low
                    concern = concern + [presence_of(mods_all[low.bit_length() - 1], appeared)]
        why = ra.affected(facts, concern, lambda: tokens(m))
        if why and m in SEES_OTHER: stats["sees other modules, compiled"] += 1
    if why is None:
        stats["reused"] += 1
        if truly:
            cols = [c for c, x, y in zip(("olean", "ilean", "ir", "ir.sig", "c", "server", "private"), old["fp"], new["fp"]) if x != y]
            if set(cols) <= {"server", "private"} and same_but_for_order(m):
                stats["reused: stored linter messages in another order"] += 1
            else:
                misses.append((m, cols)); stats["MISS"] += 1
        continue
    stats["compiled"] += 1; stats["compiled: " + why[0]] += 1
    stats["compiled, output really changed"] += truly
    compiled.append((m, why[0], why[1], truly))
    d = ra.output_changes(Stored(A[m][1]) if old else None, Stored(B[m][1]), old is None or old["fp"][3] == new["fp"][3],
                          [line["names"] for line in mine] if deep else [])
    if any(d.values()):          # the script also logs a change of imports alone, which the rule does not read
        lines.append(dict(ra.as_line(m, d), i=idx[m]))
        stats["logged a change"] += 1; stats["logged a taint"] += bool(d["taint"])
    if n % 5000 == 0: print(f"  {n}/{len(R)} {time.time() - T0:.0f}s {dict(stats)}", flush=True)

dep = [m for m in R if m in A and m not in S]
res = {"batch": f"b{k + 1}", "old": old_sha, "new": new_sha, "order": order, "deep": deep, "modules": len(B), "recompiled_by_lake": len(R),
       "edited_or_new": len(R) - len(dep), "stats": dict(stats), "misses": misses, "seconds": round(time.time() - T0)}
tag = f"b{k + 1}-{order}-{'deep' if deep else 'direct'}{'' if precise else '-probe'}"
with open(os.path.join(out, f"replay-{tag}.json"), "w") as f: json.dump(res, f)
with open(os.path.join(out, f"replay-{tag}.compiled.tsv"), "w") as f:
    for row in compiled: f.write("\t".join(map(str, row)) + "\n")
with open(os.path.join(out, f"replay-{tag}.lines.jsonl"), "w") as f:
    for line in lines: f.write(json.dumps({k2: v for k2, v in line.items() if k2 not in ("names", "proj", "code")} | {"n": len(line["names"])}) + "\n")
print(json.dumps({k2: v for k2, v in res.items() if k2 != "misses"}))
for m, cols in misses[:40]: print("MISS", m, cols)
