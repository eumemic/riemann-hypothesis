"""Compare two outputs of `lean-queries.sh decls`: the tree before and the tree after.

Declarations that Lean generates (auxiliary proofs, matchers, simp lemmas, equation lemmas and the
like) are not compared: which module holds them, and their numbering, depends on what a file can
see. For every other declaration the type must be the same, and for definitions the value too.
Proofs are not compared.

usage: same.py BEFORE AFTER [--modules-out FILE]      exit status 1 if something differs
  --modules-out FILE   write the modules that hold a differing declaration to FILE, one per line"""
import collections, re, sys

AUX = re.compile(r"(^|\.)(_proof_\d+(_\d+)?|_simp_\d+(_\d+)?|match_\d+(_\d+)?(\.[\w.]+)?|eq_\d+|eq_def|eq_unfold|congr_simp"
                 r"|hcongr_\d+|_sunfold|_unary|_mutual|_unsafe_rec|injEq|sizeOf_spec|_nativeDecide_\w+|_aux_\w+)$")


def load(path):
    d = {}
    for l in open(path, encoding="utf-8"):
        l = l.rstrip("\n")
        if not l: continue
        m, n, k, t, v = l.split("\t")
        d[(m, n)] = (k, t, v)
    return d


if __name__ == "__main__":
    a, b = load(sys.argv[1]), load(sys.argv[2])
    plain = lambda d: {k: v for k, v in d.items() if not AUX.search(k[1])}
    pa, pb = plain(a), plain(b)
    gone = sorted(k for k in pa if k not in pb); new = sorted(k for k in pb if k not in pa)
    typ = sorted(k for k in pa if k in pb and pa[k][1] != pb[k][1])
    val = sorted(k for k in pa if k in pb and pa[k][0] != "thm" and pa[k][1] == pb[k][1] and pa[k][2] != pb[k][2])
    proofs = sum(1 for k in pa if k in pb and pa[k][0] == "thm" and pa[k][2] != pb[k][2])
    print(f"declarations written in the sources: {len(pa)} before, {len(pb)} after "
          f"(generated ones, not compared: {len(a) - len(pa)} before, {len(b) - len(pb)} after)")
    print(f"only before: {len(gone)}, only after: {len(new)}, other type: {len(typ)}, definitions with another value: {len(val)}")
    print(f"theorems with another proof term (not a difference that counts): {proofs}")
    for name, ks in (("only before", gone), ("only after", new), ("other type", typ), ("other value", val)):
        for k in ks[:40]: print(f"   {name}: {k[0]}  {k[1]}")
    by = collections.Counter(k[0] for k in typ + val + gone + new)
    if "--modules-out" in sys.argv:
        with open(sys.argv[sys.argv.index("--modules-out") + 1], "w") as f: f.write("".join(m + "\n" for m in sorted(by)))
    if by: print("modules: " + ", ".join(f"{m} ({n})" for m, n in by.most_common()))
    sys.exit(1 if gone or new or typ or val else 0)
