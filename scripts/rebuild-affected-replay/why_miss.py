"""For a module a replay reported as MISS: the changes that were logged by modules it can see.
usage: why_miss.py META HIST BATCH MODULE"""
import importlib.util, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
def load(name, file):
    spec = importlib.util.spec_from_file_location(name, next(p for p in (os.path.join(HERE, file), os.path.join(HERE, "..", file)) if os.path.exists(p))); mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
ra, bx = load("ra", "rebuild-affected.py"), load("bx", "batch_extract.py")
meta, hist, k, m = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
src = os.path.join(hist, "src", bx.COMMITS[k], "src")
old_src = os.path.join(hist, "src", bx.COMMITS[k - 1], "src")
def imports_in(root):
    cache = {}
    def imports(x):
        if x not in cache:
            p = os.path.join(root, *x.split(".")) + ".lean"
            cache[x] = [(d, public, all_) for d, public, all_, meta_ in ra.header(p)[1]] if os.path.exists(p) else []
        return cache[x]
    return imports
new_view, old_view = ra.view(imports_in(src), m), ra.view(imports_in(old_src), m)
print(f"{m}: sees {len(new_view)} modules ({len([x for x in new_view if os.path.exists(os.path.join(src, *x.split('.')) + '.lean')])} of this package); view changed: {new_view != old_view}; gained {sorted(set(new_view) - set(old_view))[:5]} lost {sorted(set(old_view) - set(new_view))[:5]}")
seen = set(new_view)
compiled = {}
with open(os.path.join(hist, f"replay-b{k + 1}-visible-deep.compiled.tsv")) as f:
    for line in f:
        parts = line.rstrip("\n").split("\t"); compiled[parts[0]] = parts[1:]
n_compiled = [x for x in new_view if x in compiled]
print(f"   of these, compiled in the batch: {len(n_compiled)}; with a really changed output: {sum(1 for x in n_compiled if compiled[x][-1] == 'True')}")
with open(os.path.join(hist, f"replay-b{k + 1}-visible-deep.lines.jsonl")) as f:
    for line in f:
        r = json.loads(line)
        if r["m"] in seen:
            shown = [n for h, n in r.get("shown", [])][:14]
            print(f"   LINE {r['m']}: {r['n']} names, taint={r['taint']!r}, tokens={r['tokens'][:8]}, taken={len(r.get('taken', []))}, freed={len(r.get('freed', []))}, code={len(r.get('code', [])) if isinstance(r.get('code'), list) else r.get('code')}\n        names: {shown}")
