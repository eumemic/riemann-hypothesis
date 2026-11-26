"""Resolve a merge conflict between the result of a run and a newer commit, in a file where both
changed the import lines.

The result changes import lines only, so the file is the newer commit's file with a merged import
block: the result's lines, plus the imports the newer commit added, minus the imports it removed.
Run in a git checkout during a merge, for a file with conflicts.

usage: union.py FILE      exit status 1 if the conflict is not of this kind"""
import subprocess, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sortimports import IMPORT, import_lines, normalize


def stage(n, path):
    r = subprocess.run(["git", "show", f":{n}:{path}"], capture_output=True)
    return r.stdout.decode("utf-8") if r.returncode == 0 else None


def split(text):
    """(import lines by module name, the lines of the file without them, index of the first import line)"""
    lines = text.split("\n")
    idx = import_lines(lines)
    imps = {IMPORT.match(lines[i]).group(4): lines[i] for i in idx}
    keep = set(idx)
    return imps, [l for i, l in enumerate(lines) if i not in keep], idx[0]


def merge(base, ours, theirs):
    bi, bb, _ = split(base); oi, ob, opos = split(ours); ti, tb, tpos = split(theirs)
    if ob == bb: body, pos = tb, tpos               # the usual case: we changed import lines only
    elif tb == bb: body, pos = ob, opos
    else: return None
    out = dict(oi)
    for n, line in ti.items():
        if n in bi: continue
        if n not in out or (IMPORT.match(line).group(1) and not IMPORT.match(out[n]).group(1)):
            out[n] = line                           # added by the newer commit
    for n in bi:
        if n not in ti and n in out and "shake: keep" not in out[n]: del out[n]     # removed by it
    return normalize("\n".join(body[:pos] + list(out.values()) + body[pos:]))


if __name__ == "__main__":
    path = sys.argv[1]
    base, ours, theirs = stage(1, path), stage(2, path), stage(3, path)
    if base is None or ours is None or theirs is None:
        print(f"{path}: not changed on both sides"); sys.exit(1)
    new = merge(base, ours, theirs)
    if new is None:
        print(f"{path}: both sides changed more than import lines"); sys.exit(1)
    open(path, "w", encoding="utf-8").write(new)
    print(f"{path}: import block merged")
