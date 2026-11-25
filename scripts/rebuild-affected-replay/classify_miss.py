"""Summarise how CI's outputs differ for the modules a replay reported as MISS.
usage: classify_miss.py CACHEMETA BATCH MODULE..."""
import importlib.util, os, shutil, sys
HERE = os.path.dirname(os.path.abspath(__file__))
def load(name, file):
    spec = importlib.util.spec_from_file_location(name, next(p for p in (os.path.join(HERE, file), os.path.join(HERE, "..", file)) if os.path.exists(p))); mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
ra, bx = load("ra", "rebuild-affected.py"), load("bx", "batch_extract.py")
meta, k = sys.argv[1], int(sys.argv[2])
A, B = bx.manifest(meta, bx.COMMITS[k - 1]), bx.manifest(meta, bx.COMMITS[k])
for m in sys.argv[3:]:
    mods = []
    for side, man in (("old", A), ("new", B)):
        dest = f"{bx.TMP}-miss-{os.getpid()}/{side}"; shutil.rmtree(dest, ignore_errors=True)
        mods.append(ra.Module(bx.fetch(man[m][1], man[m][0], dest), bx.norm))
    old, new = mods
    out = []
    for part in range(3):
        co, cn = old.constants(part), new.constants(part)
        added = [new.name(cn[h][0]) for h in cn.keys() - co.keys()]; removed = [old.name(co[h][0]) for h in co.keys() - cn.keys()]
        changed = [new.name(cn[h][0]) for h in co.keys() & cn.keys() if old.digest(co[h][1]) != new.digest(cn[h][1])]
        if added or removed or changed: out.append(f"p{part} consts +{added[:3]} -{removed[:3]} ~{changed[:3]} ({len(added)}/{len(removed)}/{len(changed)})")
        eo, en = old.entries(part), new.entries(part)
        for ext in sorted(eo.keys() | en.keys()):
            do = ra.multiset(old.digest(e) for e in eo.get(ext, ())); dn = ra.multiset(new.digest(e) for e in en.get(ext, ()))
            if do != dn: out.append(f"p{part} {ext.split('.')[-1]} -{sum((do[d] - dn.get(d, 0)) for d in do if do[d] > dn.get(d, 0))} +{sum((dn[d] - do.get(d, 0)) for d in dn if dn[d] > do.get(d, 0))}")
            elif [old.digest(e) for e in eo.get(ext, ())] != [new.digest(e) for e in en.get(ext, ())]: out.append(f"p{part} {ext.split('.')[-1]} order")
    print(m, "|", "; ".join(out)[:900], flush=True)
    shutil.rmtree(f"{bx.TMP}-miss-{os.getpid()}", ignore_errors=True)
