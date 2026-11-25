"""Do CI's two outputs of a module differ only in the counters of generated (hygienic) names?
usage: hyg_only.py META K MODULE...

Every constant that differs between the two versions is compared structurally, with a name allowed
to differ where both are of the form `…._hyg.N` and the same pairing is used throughout."""
import importlib.util, os, re, shutil, sys
HERE = os.path.dirname(os.path.abspath(__file__))
def load(name, file):
    spec = importlib.util.spec_from_file_location(name, next(p for p in (os.path.join(HERE, file), os.path.join(HERE, "..", file)) if os.path.exists(p))); mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
ra, bx = load("ra", "rebuild-affected.py"), load("bx", "batch_extract.py")
HYG = re.compile(r"^(.*\._hyg)\.\d+$")

def same_but_counters(a, pa, b, pb, renaming):
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
            mx, my = HYG.match(nx), HYG.match(ny)
            if not (mx and my and mx.group(1) == my.group(1)): return False
            if renaming.setdefault(nx, ny) != ny or renaming.setdefault("<" + ny, nx) != nx: return False
        elif sx != sy: return False
        else: stack.extend(zip(fx, fy))
    return True

meta, k = sys.argv[1], int(sys.argv[2])
A, B = bx.manifest(meta, bx.COMMITS[k - 1]), bx.manifest(meta, bx.COMMITS[k])
for m in sys.argv[3:]:
    mods = []
    for side, man in (("old", A), ("new", B)):
        dest = f"{bx.TMP}-hyg-{os.getpid()}/{side}"; shutil.rmtree(dest, ignore_errors=True)
        mods.append(ra.Module(bx.fetch(man[m][1], man[m][0], dest), bx.norm))
    old, new = mods
    verdict, n, renaming = "only counters", 0, {}
    for part in range(3):
        co, cn = old.constants(part), new.constants(part)
        if co.keys() != cn.keys(): verdict = "constants added or removed"; break
        for h in co:
            if old.digest(co[h][1]) != new.digest(cn[h][1]):
                n += 1
                if not same_but_counters(old, co[h][1], new, cn[h][1], renaming): verdict = f"{old.name(co[h][0])} differs otherwise"
        eo, en = old.entries(part), new.entries(part)
        for ext in eo.keys() | en.keys():
            if ext in ra.UNORDERED: continue
            xs, ys = eo.get(ext, ()), en.get(ext, ())
            if [old.digest(e) for e in xs] != [new.digest(e) for e in ys]:
                if len(xs) != len(ys) or not all(same_but_counters(old, x, new, y, renaming) for x, y in zip(xs, ys)): verdict = f"entries of {ext} differ otherwise"
    print(f"{m.rsplit('.', 1)[-1]}: {verdict} ({n} constants compared over the three parts, {len(renaming) // 2} names paired)", flush=True)
    shutil.rmtree(f"{bx.TMP}-hyg-{os.getpid()}", ignore_errors=True)
