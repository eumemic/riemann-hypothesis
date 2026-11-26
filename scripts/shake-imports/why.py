"""For every import marked `-- shake: keep` (outside Lib/Speed.lean) of a built tree: compile the
file with that import made private and print the errors, with the source lines they point at.

usage: why.py REPO [--jobs N] > report.txt"""
import concurrent.futures, json, os, shutil, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sortimports import IMPORT, imports, normalize
import refine


def errors(repo, mod):
    env, lean, args, src = refine.lean_command(repo, mod)
    lines = open(src, encoding="utf-8").read().split("\n")
    out = []
    for n, line in imports(lines).items():
        if "shake: keep" not in line: continue
        trial = refine.edit(lines, n, "import " + n if IMPORT.match(line).group(1) else None)
        text = normalize("\n".join(trial)); tl = text.split("\n")
        d = tempfile.mkdtemp(prefix="why-")
        try:
            tmp = os.path.join(d, os.path.basename(src))
            open(tmp, "w", encoding="utf-8").write(text)
            r = subprocess.run([lean] + [tmp if w == src else w for w in args], env=env, cwd=repo, capture_output=True, text=True)
        finally:
            shutil.rmtree(d, ignore_errors=True)
        errs = []
        for l in r.stdout.split("\n"):
            try: m = json.loads(l)
            except Exception: continue
            if m.get("severity") == "error":
                ln = m.get("pos", {}).get("line", 0)
                errs.append((ln, " ".join(m.get("data", "").split())[:260], tl[ln - 1].strip()[:160] if 0 < ln <= len(tl) else ""))
        out.append((n, bool(IMPORT.match(line).group(1)), errs))
    return mod, out


if __name__ == "__main__":
    repo = os.path.abspath(sys.argv[1]); srcdir = os.path.join(repo, "src")
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 6
    todo = []
    for d, _, fs in os.walk(srcdir):
        for f in fs:
            if not f.endswith(".lean"): continue
            p = os.path.join(d, f); mod = os.path.relpath(p, srcdir)[:-5].replace(os.sep, ".")
            if mod != refine.BASE and any("shake: keep" in l for l in imports(open(p, encoding="utf-8").read().split("\n")).values()):
                todo.append(mod)
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for mod, out in ex.map(lambda m: errors(repo, m), sorted(todo)):
            for n, pub, errs in out:
                print(f"== {mod}: {'public ' if pub else ''}import {n}  ({len(errs)} errors)")
                for ln, msg, srcline in errs[:4]:
                    print(f"   L{ln}: {msg}\n        | {srcline}")
            sys.stdout.flush()
