"""The sentences of the documentation that describe the import structure, brought in line with
private imports. Each replacement must find its old text exactly once, or already be made.

usage: docs.py REPO     prints what it changed"""
import os, sys

repo = sys.argv[1]
EDITS = [
    ("src/Lib/Base.lean",
     "The other files of `Lib` and `New`, except `Lib.Speed`, import this file, directly or not, and\n"
     "with it the speed settings of `Lib.Speed`.\n",
     "This file imports the speed settings of `Lib.Speed`. The other files of `Lib` and `New` import\n"
     "`Lib.Speed` too, through this file or without it.\n"),
    ("GUIDE.md",
     "`Lib/Speed`, imported through `Lib/Base`, holds the main settings",
     "`Lib/Speed`, which every file of `Lib` and `New` imports, directly or not, holds the main settings"),
    ("GUIDE.md",
     "- Local `seal`, `attribute` and `set_option` lines steer",
     "- A file imports another one with `public import` only if its statements or definitions use it. "
     "What only its proofs use is a plain `import`, so a change to a file recompiles fewer files. "
     "`lake shake --add-public-downstream Lib.Speed`, given the modules of `src`, proposes the import lines; "
     "its proposal for `Statements.lean` is not followed. An import with the comment `-- shake: keep` "
     "stays as it is: with what `lake shake` proposes for it, the file does not compile or one of its "
     "statements changes.\n"
     "- Local `seal`, `attribute` and `set_option` lines steer"),
]
for rel, old, new in EDITS:
    p = os.path.join(repo, rel)
    s = open(p, encoding="utf-8").read()
    if new in s:
        print(f"{rel}: already changed")
        continue
    assert s.count(old) == 1, f"{rel}: expected the old text once, found {s.count(old)} times: {old[:60]!r}"
    open(p, "w", encoding="utf-8").write(s.replace(old, new))
    print(f"{rel}: changed")
