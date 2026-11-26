"""Mark the import of Mathlib in Lib/Speed.lean and add the import of Aesop next to it.

usage: speed.py PATH_OF_Lib/Speed.lean"""
import sys

p = sys.argv[1]
s = open(p, encoding="utf-8").read()
assert s.count("public import Mathlib\n") == 1, "unexpected header of Lib.Speed"
s = s.replace("public import Mathlib\n", "public import Aesop -- shake: keep\npublic import Mathlib -- shake: keep\n")
open(p, "w", encoding="utf-8").write(s)
print("annotated", p)
