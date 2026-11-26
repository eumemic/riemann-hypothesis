"""Give a file back the sight of the files that set attributes on declarations of other files.

`lake shake` decides from the constants a compiled file refers to. A file that changes the priority
of an instance of Mathlib, or makes a lemma of Mathlib an instance, is referred to by nothing, so
`lake shake` removes it from files whose statements were elaborated with that setting, and they
then elaborate with another instance.

  fixattrs.py add SRC BEFORE_SRC ATTRS_TSV MODULES ADDED
      For every module in MODULES (the modules in which same.py found a declaration that differs):
      add `import X -- shake: keep` for every attribute-setting file X that the module could see
      in BEFORE_SRC and cannot see now. Appends "module<TAB>X" lines to ADDED.
      ATTRS_TSV is the output of `lean-queries.sh attrs`. Exit status 3 if some module got nothing.
  fixattrs.py drop SRC MODULE X      remove that import of X from MODULE again
  fixattrs.py put SRC MODULE X       put it back"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sortimports import IMPORT, KEEP, import_lines, normalize
import modgraph


def visible(src):
    """module -> set of modules it can see: what it imports, and what those reach through public imports"""
    mods = modgraph.read(src)
    direct = {m: [(d, pub) for d, pub, _, _ in mods[m][1] if d in mods] for m in mods}
    reach = {}
    def pubreach(m):
        if m not in reach:
            reach[m] = {m}
            for d, p in direct[m]:
                if p: reach[m] |= pubreach(d)
        return reach[m]
    sys.setrecursionlimit(10000)
    return {m: set().union(*[pubreach(d) for d, _ in direct[m]]) if direct[m] else set() for m in mods}


def path(src, mod):
    return os.path.join(src, *mod.split(".")) + ".lean"


def put(src, mod, xs):
    lines = open(path(src, mod), encoding="utf-8").read().split("\n")
    last = import_lines(lines)[-1]
    lines[last + 1:last + 1] = ["import " + x + KEEP for x in xs]
    open(path(src, mod), "w", encoding="utf-8").write(normalize("\n".join(lines)))


def drop(src, mod, x):
    lines = open(path(src, mod), encoding="utf-8").read().split("\n")
    idx = [i for i in import_lines(lines) if IMPORT.match(lines[i]).group(4) == x]
    assert len(idx) == 1 and lines[idx[0]] == "import " + x + KEEP, f"{mod} has no marked private import of {x}"
    del lines[idx[0]]
    open(path(src, mod), "w", encoding="utf-8").write("\n".join(lines))


if __name__ == "__main__":
    what, src = sys.argv[1:3]
    if what == "drop": drop(src, sys.argv[3], sys.argv[4])
    elif what == "put": put(src, sys.argv[3], [sys.argv[4]])
    else:
        before, attrs, modules, added = sys.argv[3:7]
        setters = sorted({l.split("\t")[0] for l in open(attrs, encoding="utf-8") if l.strip()} - {"Lib.Speed"})
        old, new = visible(before), visible(src)
        stuck = 0
        for f in [l.strip() for l in open(modules) if l.strip()]:
            lost = [x for x in setters if x in old.get(f, ()) and x not in new.get(f, ()) and x != f]
            if not lost:
                print(f"{f}: saw none of {setters} before that it does not see now"); stuck += 1
                continue
            put(src, f, lost)
            with open(added, "a") as out: out.write("".join(f"{f}\t{x}\n" for x in lost))
            print(f"{f}: added " + ", ".join("import " + x for x in lost))
        sys.exit(3 if stuck else 0)
