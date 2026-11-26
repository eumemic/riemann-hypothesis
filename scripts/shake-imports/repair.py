"""Repair files that stop compiling after `lake shake --fix`.

For every module that failed in BUILD_LOG: make all of its imports `public`, and put back (as
`public import`) the imports it had in git revision ORIG that are missing now.
A file that fails again after that gets the name lookup: a `public import` of the project files
that open a namespace the errors call unknown, or of the one file that declares an unknown name.
What was done to each file is kept in REPO/.shake-repair.json (delete it to start over).

usage: repair.py REPO BUILD_LOG ORIG [--dry]
prints one line per failing file; exit status 3 if no file could be changed"""
import json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sortimports import IMPORT, import_lines, is_project, normalize

FROZEN = {"Statements"}          # a Comparator challenge file: never edited


def failing(log):
    cur, errs = None, {}
    for l in open(log, encoding="utf-8", errors="replace"):
        m = re.match(r"^(✖|✔|⚠|ℹ) \[\d+/\d+\] (Building|Built|Replayed) (\S+)", l)
        if m:
            cur = m.group(3) if m.group(1) == "✖" else None
            if cur: errs.setdefault(cur, [])
            continue
        if cur and l.startswith("error"): errs[cur].append(l.rstrip("\n"))
    return errs


def index(src):
    """namespace -> modules that open it with `namespace`, last name component -> modules declaring it"""
    ns, decl = {}, {}
    pat = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |unsafe |partial )*"
                     r"(?:def|theorem|lemma|abbrev|structure|class|inductive|instance|opaque|axiom)\s+([^\s:({\[]+)")
    for d, _, files in os.walk(src):
        for f in files:
            if not f.endswith(".lean"): continue
            p = os.path.join(d, f); mod = os.path.relpath(p, src)[:-5].replace(os.sep, ".")
            for l in open(p, encoding="utf-8"):
                m = re.match(r"^namespace\s+(\S+)", l)
                if m:
                    for part in m.group(1).split("."): ns.setdefault(part, set()).add(mod)
                    ns.setdefault(m.group(1), set()).add(mod)
                m = pat.match(l)
                if m: decl.setdefault(m.group(1).split(".")[-1], set()).add(mod)
    return ns, decl


def main():
    repo, log, orig = sys.argv[1:4]
    dry = "--dry" in sys.argv
    src = os.path.join(repo, "src")
    state_path = os.path.join(repo, ".shake-repair.json")
    state = json.load(open(state_path)) if os.path.exists(state_path) else {}
    errs = failing(log)
    ns = decl = None
    progress = 0
    for mod, es in sorted(errs.items()):
        rel = os.path.join("src", *mod.split(".")) + ".lean"
        path = os.path.join(repo, rel)
        if mod in FROZEN or not os.path.exists(path):
            print(f"{mod}: {len(es)} errors; NOT A FILE TO EDIT: " + " | ".join(e[:160] for e in es[:3])); continue
        lines = open(path, encoding="utf-8").read().split("\n")
        idx = import_lines(lines)
        have = {IMPORT.match(lines[i]).group(4) for i in idx}
        changed, add = [], []
        if "promoted" not in state.get(mod, []):
            for i in idx:                               # 1. private imports become public
                m = IMPORT.match(lines[i])
                if not m.group(1) and not m.group(2) and not m.group(3):
                    lines[i] = "public " + lines[i]; changed.append("public " + m.group(4))
            old = subprocess.run(["git", "-C", repo, "show", f"{orig}:{rel}"], capture_output=True, text=True).stdout.split("\n")
            for i in import_lines(old):                 # 2. imports the file had before
                name = IMPORT.match(old[i]).group(4)
                if name not in have and name not in add: add.append(name)
            state.setdefault(mod, []).append("promoted")
        if not changed and not add:                     # 3. what the errors call unknown
            if ns is None: ns, decl = index(src)
            wanted = set()
            for e in es:
                m = re.search(r"unknown namespace `([^`]+)`", e)
                if m: wanted |= ns.get(m.group(1), set())
                for pat in (r"Unknown (?:identifier|constant) `([^`]+)`", r"does not contain `([^`]+)`"):
                    m = re.search(pat, e)
                    if m and len(decl.get(m.group(1).split(".")[-1], ())) == 1: wanted |= decl[m.group(1).split(".")[-1]]
            add = [w for w in sorted(wanted) if w != mod and w not in have]
            state.setdefault(mod, []).append("names:" + ",".join(add))
        if add:
            last = idx[-1]
            lines[last + 1:last + 1] = ["public import " + a for a in add]
            changed += ["+public " + a for a in add]
        print(f"{mod}: {len(es)} errors; " + (", ".join(changed) if changed else "NOTHING TO CHANGE: " + " | ".join(e[:160] for e in es[:3])))
        if changed:
            progress += 1
            if not dry: open(path, "w", encoding="utf-8").write(normalize("\n".join(lines)))
    if not dry: json.dump(state, open(state_path, "w"), indent=1)
    print(f"{len(errs)} modules failed, {progress} changed")
    sys.exit(0 if progress or not errs else 3)


if __name__ == "__main__":
    main()
