"""Which modules that MODULE sees hold a constant whose name ends with SUFFIX, before and after a batch?
usage: who_had.py META HIST BATCH MODULE SUFFIX"""
import array, importlib.util, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
def load(name, file):
    spec = importlib.util.spec_from_file_location(name, next(p for p in (os.path.join(HERE, file), os.path.join(HERE, "..", file)) if os.path.exists(p))); mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
ra, bx = load("ra", "rebuild-affected.py"), load("bx", "batch_extract.py")
meta, hist, k, m, suffix = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
A, B = bx.manifest(meta, bx.COMMITS[k - 1]), bx.manifest(meta, bx.COMMITS[k])
def imports_in(root):
    cache = {}
    def imports(x):
        if x not in cache:
            p = os.path.join(root, *x.split(".")) + ".lean"
            cache[x] = [(d, public, all_) for d, public, all_, meta_ in ra.header(p)[1]] if os.path.exists(p) else []
        return cache[x]
    return imports
compiled = {}
with open(os.path.join(hist, f"replay-b{k + 1}-visible-deep.compiled.tsv")) as f:
    for line in f:
        parts = line.rstrip("\n").split("\t"); compiled[parts[0]] = parts[1:]
target = None
for side, man, sha in (("old", A, bx.COMMITS[k - 1]), ("new", B, bx.COMMITS[k])):
    view = ra.view(imports_in(os.path.join(hist, "src", sha, "src")), m) + [m]
    for x in view:
        if x not in man: continue
        rp = bx.rec_path(hist, man[x][1])
        if not os.path.exists(rp + ".olean"): continue        # not recompiled in any batch we extracted: same on both sides
        mod = ra.Module(rp + ".olean"); mod.parts, mod.roots = mod.parts[:1], mod.roots[:1]
        for h, (n, c) in mod.constants(0).items():
            name = mod.name(n)
            if name.endswith(suffix):
                target = (h, mod.name_hash(mod.fields(n)[0]))
                print(f"{side}: {x} has {name}   [in batch: {'compiled: ' + compiled[x][0] if x in compiled else ('lake recompiled, rule reused' if (x not in A or A[x][0] != B.get(x, (None,))[0]) else 'not recompiled')}]")
if target:
    with open(bx.rec_path(hist, A[m][1]) + ".names", "rb") as f: a = array.array("Q"); a.frombytes(f.read())
    names = set(a)
    print(f"old output of {m} mentions the lemma: {target[0] in names}; mentions its parent: {target[1] in names}")
