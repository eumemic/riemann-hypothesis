"""Rebuild fan-out of a Lake project whose files are `module`s.

Lake (v4.37, Lake/Build/Module.lean, `ModuleImportInfo.addImport`) recompiles a module M when the
exported part changes in a module that M can see: a module M imports directly (`import` or
`public import`), or one that such a module reaches through `public import`s only. An `import all`
also makes M depend on the private part of what it names, a `meta import` on the compiled code.

usage: modgraph.py SRC_DIR [BUILD_LOG] [--tsv OUT]
  BUILD_LOG: output of `lake build`, for the compile seconds of each module."""
import os, re, sys, statistics

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sortimports import IMPORT, import_lines


def read(src):
    mods = {}
    for d, _, files in os.walk(src):
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                m = os.path.relpath(p, src)[:-5].replace(os.sep, ".")
                lines = open(p, encoding="utf-8").read().split("\n")
                idx = import_lines(lines)
                is_module = any(l.strip() == "module" or l.strip().startswith("module --") for l in lines[:(idx[0] if idx else 0)])
                imps = []
                for i in idx:
                    g = IMPORT.match(lines[i])
                    imps.append((g.group(4), bool(g.group(1)) or not is_module, bool(g.group(2)), bool(g.group(3))))
                mods[m] = (is_module, imps, len(lines) - 1)
    return mods

def analyse(mods):
    names = sorted(mods)
    idx = {m: i for i, m in enumerate(names)}
    direct = {m: [(d, pub) for d, pub, _, _ in mods[m][1] if d in mods] for m in names}
    # pubreach[m]: bitset of m and everything m reaches through public imports
    pubreach, allreach = {}, {}
    def reach(m, table, only_public):
        stack = [m]
        while stack:
            x = stack[-1]
            if x in table: stack.pop(); continue
            todo = [d for d, pub in direct[x] if (pub or not only_public) and d not in table]
            if todo: stack.extend(todo); continue
            r = 1 << idx[x]
            for d, pub in direct[x]:
                if pub or not only_public: r |= table[d]
            table[x] = r; stack.pop()
    for m in names: reach(m, pubreach, True); reach(m, allreach, False)
    sees = {}
    for m in names:
        s = 0
        for d, _ in direct[m]: s |= pubreach[d]
        sees[m] = s
    fan = {m: [] for m in names}          # who is recompiled when m's exported part changes
    for m in names:
        s = sees[m]
        while s:
            low = s & -s; fan[names[low.bit_length() - 1]].append(m); s ^= low
    trans = {m: bin(allreach[m]).count("1") - 1 for m in names}
    return names, direct, sees, fan, trans

def quantiles(vals):
    v = sorted(vals); n = len(v)
    q = lambda p: v[min(n - 1, n * p // 100)]
    return f"median {q(50)}, p75 {q(75)}, p90 {q(90)}, max {v[-1]}, mean {statistics.mean(v):.0f}"

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    tsv = sys.argv[sys.argv.index("--tsv") + 1] if "--tsv" in sys.argv else None
    if tsv: args.remove(tsv)
    mods = read(args[0])
    names, direct, sees, fan, trans = analyse(mods)
    n = len(names)
    nmod = sum(1 for m in names if mods[m][0])
    kinds = {"public": 0, "private": 0, "meta": 0, "all": 0}
    for m in names:
        for d, pub, meta, all_ in mods[m][1]:
            if d not in mods: continue
            kinds["public" if pub else "private"] += 1
            kinds["meta"] += meta; kinds["all"] += all_
    print(f"{n} files, {nmod} of them modules; imports of project files: {kinds['public']} public, "
          f"{kinds['private']} private, {kinds['meta']} meta, {kinds['all']} all")
    f = {m: len(fan[m]) for m in names}
    print(f"files recompiled when one file's exported part changes (not counting itself): {quantiles(f.values())} of {n}")
    print(f"   files whose change recompiles at least half of the project: {sum(1 for v in f.values() if v >= n / 2)}")
    print(f"   sum over all files: {sum(f.values()):,}")
    base = "Lib.Speed"
    if base in mods:
        pub = lambda m: [d for d, p in direct[m] if p]
        def reaches(m, step):
            seen, stack = set(), [m]
            while stack:
                for d in step(stack.pop()):
                    if d not in seen: seen.add(d); stack.append(d)
            return base in seen
        print("   files that do not reach Lib.Speed through public imports: "
              + (", ".join(m for m in names if m != base and not reaches(m, pub)) or "none"))
        print("   files that do not reach Lib.Speed at all: "
              + (", ".join(m for m in names if m != base and not reaches(m, lambda x: [d for d, _ in direct[x]])) or "none"))
    secs = {}
    if len(args) > 1:
        for line in open(args[1], encoding="utf-8", errors="replace"):
            g = re.match(r"^\S+ \[\d+/\d+\] Built (\S+) \(([\d.]+)(ms|s|m)\)", line)
            if g and g.group(1) in mods:
                secs[g.group(1)] = float(g.group(2)) * {"ms": 0.001, "s": 1, "m": 60}[g.group(3)]
        cost = {m: sum(secs.get(x, 0) for x in fan[m]) for m in names}
        c = sorted(cost.values())
        print(f"compile time of those files: median {c[n // 2] / 60:.0f} core-minutes, p75 {c[n * 3 // 4] / 60:.0f}, "
              f"p90 {c[n * 9 // 10] / 60:.0f}, max {c[-1] / 60:.0f}; whole project {sum(secs.values()) / 60:.0f}")
    if tsv:
        with open(tsv, "w") as out:
            out.write("module\trecompiled\tcore_seconds\n")
            for m in names:
                out.write(f"{m}\t{f[m]}\t{sum(secs.get(x, 0) for x in fan[m]):.0f}\n")
