"""Carry the `-- shake: keep` marks of an earlier result to a tree in which every import is public.

A marked import that the file has gets the mark (and becomes private if the earlier result has it
private). A marked import that the file does not have is added as the earlier result has it.
Lib/Speed.lean is left out: the pipeline marks its imports itself.

usage: seed.py SEED_SRC TARGET_SRC     prints the number of marks carried over"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sortimports import IMPORT, import_lines

seed, target = sys.argv[1:3]
n = files = 0
for d, _, fs in os.walk(seed):
    for f in fs:
        if not f.endswith(".lean"): continue
        p = os.path.join(d, f); rel = os.path.relpath(p, seed); q = os.path.join(target, rel)
        if not os.path.exists(q) or rel == os.path.join("Lib", "Speed.lean"): continue
        old = open(p, encoding="utf-8").read().split("\n")
        marked = {}
        for i in import_lines(old):
            if "shake: keep" in old[i]: marked[IMPORT.match(old[i]).group(4)] = old[i]
        marked = {m: l for m, l in marked.items() if os.path.exists(os.path.join(target, *m.split(".")) + ".lean")
                  or not m.startswith(("Lib.", "New."))}
        if not marked: continue
        lines = open(q, encoding="utf-8").read().split("\n")
        idx = import_lines(lines)
        have = {IMPORT.match(lines[i]).group(4): i for i in idx}
        add = []
        for m, l in marked.items():
            if m in have: lines[have[m]] = l
            else: add.append(l)
        lines[idx[-1] + 1:idx[-1] + 1] = add
        open(q, "w", encoding="utf-8").write("\n".join(lines)); n += len(marked); files += 1
print(f"marks carried over: {n} in {files} files")
