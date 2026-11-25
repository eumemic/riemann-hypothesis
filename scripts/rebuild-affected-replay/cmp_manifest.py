"""Compare two tree manifests. usage: cmp_manifest.py A B"""
import sys
def load(p): return {l.split("\t")[0]: l.rstrip("\n").split("\t")[1:] for l in open(p, encoding="utf-8")}
a, b = load(sys.argv[1]), load(sys.argv[2])
cols = ["olean", "ilean", "ir", "ir.sig", "c", "server", "private"]
diff = {m: [c for c, x, y in zip(cols, a[m], b[m]) if x != y] for m in a.keys() & b.keys() if a[m] != b[m]}
print(f"A {len(a)} B {len(b)} common {len(a.keys() & b.keys())} only-A {len(a.keys() - b.keys())} only-B {len(b.keys() - a.keys())} differ {len(diff)}")
for m, cs in sorted(diff.items())[:int(sys.argv[3]) if len(sys.argv) > 3 else 60]: print("  DIFF", m, " ".join(cs))
