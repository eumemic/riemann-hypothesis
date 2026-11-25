"""For the misses of a replay: constants that were removed or changed in a module the missed module
sees, and whose last name component is a word of its source.
usage: token_miss.py META HIST BATCH"""
import importlib.util, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
def load(name, file):
    spec = importlib.util.spec_from_file_location(name, next(p for p in (os.path.join(HERE, file), os.path.join(HERE, "..", file)) if os.path.exists(p))); mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
ra, bx = load("ra", "rebuild-affected.py"), load("bx", "batch_extract.py")
meta, hist, k = sys.argv[1], sys.argv[2], int(sys.argv[3])
A, B = bx.manifest(meta, bx.COMMITS[k - 1]), bx.manifest(meta, bx.COMMITS[k])
src = os.path.join(hist, "src", bx.COMMITS[k], "src")
cache = {}
def imports(x):
    if x not in cache:
        p = os.path.join(src, *x.split(".")) + ".lean"
        cache[x] = [(d, public, all_) for d, public, all_, meta_ in ra.header(p)[1]] if os.path.exists(p) else []
    return cache[x]
def stored(ltar):
    mod = ra.Module(bx.rec_path(hist, ltar) + ".olean"); mod.parts, mod.roots = mod.parts[:1], mod.roots[:1]; return mod
diffs = {}
def diff(x):
    """(removed, changed, added) user-named public constants of module x in this batch"""
    if x not in diffs:
        res = ([], [], [])
        if x in A and x in B and A[x][1] != B[x][1] and os.path.exists(bx.rec_path(hist, A[x][1]) + ".olean") and os.path.exists(bx.rec_path(hist, B[x][1]) + ".olean"):
            old, new = stored(A[x][1]), stored(B[x][1])
            co, cn = old.constants(0), new.constants(0)
            for h in co.keys() | cn.keys():
                name = (new.name(cn[h][0]) if h in cn else old.name(co[h][0]))
                if not ra.user_name(name): continue
                if h not in cn: res[0].append(name)
                elif h not in co: res[2].append(name)
                elif old.digest(co[h][1]) != new.digest(cn[h][1]): res[1].append(name)
        diffs[x] = res
    return diffs[x]
r = json.load(open(os.path.join(hist, f"replay-b{k + 1}-visible-deep.json")))
for m, cols in r["misses"]:
    words = ra.source_tokens(os.path.join(src, *m.split(".")) + ".lean")
    hits = {"removed": [], "changed": [], "removed, all components": [], "changed, all components": []}
    for x in ra.view(imports, m):
        removed, changed, added = diff(x)
        for kind, names in (("removed", removed), ("changed", changed)):
            for name in names:
                parts = name.split(".")
                if parts[-1] in words:
                    hits[kind].append(name)
                    if all(p in words for p in parts): hits[kind + ", all components"].append(name)
    print(f"b{k + 1} {m.rsplit('.', 1)[-1]} {cols}: " + "; ".join(f"{kind}: {len(v)} {v[:3]}" for kind, v in hits.items()))
