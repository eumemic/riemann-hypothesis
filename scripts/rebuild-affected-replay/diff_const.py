"""For a module in a batch, list names mentioned by a changed private constant in only one version.
usage: diff_const.py CACHEMETA BATCH MODULE"""
import importlib.util, os, shutil, sys
HERE = os.path.dirname(os.path.abspath(__file__))
def load(name, file):
    spec = importlib.util.spec_from_file_location(name, next(p for p in (os.path.join(HERE, file), os.path.join(HERE, "..", file)) if os.path.exists(p))); mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
ra, bx = load("ra", "rebuild-affected.py"), load("bx", "batch_extract.py")
meta, k, m = sys.argv[1], int(sys.argv[2]), sys.argv[3]
A, B = bx.manifest(meta, bx.COMMITS[k - 1]), bx.manifest(meta, bx.COMMITS[k])
mods = []
for side, man in (("old", A), ("new", B)):
    dest = f"{bx.TMP}-dc-{os.getpid()}/{side}"; shutil.rmtree(dest, ignore_errors=True)
    mods.append(ra.Module(bx.fetch(man[m][1], man[m][0], dest), bx.norm))
old, new = mods
def names_under(mod, ptr):
    out, seen, stack = {}, set(), [ptr]
    while stack:
        p = stack.pop()
        if p & 1 or p in seen: continue
        seen.add(p)
        tag, fields, sc = mod.obj(p)
        if tag in (1, 2) and len(fields) == 2 and len(sc) == 8: out[mod.name_hash(p)] = mod.name(p)
        else: stack.extend(fields)
    return out
co, cn = old.constants(2), new.constants(2)
for h in co.keys() & cn.keys():
    if old.digest(co[h][1]) != new.digest(cn[h][1]):
        no, nn = names_under(old, co[h][1]), names_under(new, cn[h][1])
        print(new.name(cn[h][0])); print("   only old:", sorted(v for k2, v in no.items() if k2 not in nn)[:12]); print("   only new:", sorted(v for k2, v in nn.items() if k2 not in no)[:12])
print("old extra uses - new:", sorted(old.extra_mod_uses() - new.extra_mod_uses())[:8], "new - old:", sorted(new.extra_mod_uses() - old.extra_mod_uses())[:8])
