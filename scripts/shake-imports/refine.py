"""Decide, import by import, which of the changes `lake shake` proposes for a built tree can be
made, by compiling each file alone with the changed header.

  refine.py REPO SHAKE_LOG [--jobs N] [--skip MODULE ...]
      SHAKE_LOG is the output of `lake shake` without --fix. For every file in it: first all of its
      proposed changes together, and if the file does not compile with them, the proposed additions
      and then the other changes one at a time (make an import private, or drop it). A change is
      kept if the file compiles with it. An import that can neither be made private nor dropped
      gets the comment `-- shake: keep`, so that `lake shake` leaves it alone from now on; the
      errors that decided it are printed.

  refine.py REPO --unmark
      Remove the `-- shake: keep` comments outside Lib/Speed.lean, so that the next `lake shake`
      and `refine.py` decide them again.

A file is compiled as Lake compiled it in the last build (same arguments and --setup file, read from
its .trace), from a copy with the new header, writing no outputs. The tree must be built. The setup
file lists every module the file could see, so a header that removes imports, makes them private or
adds a module that was already reachable compiles against the same outputs."""
import concurrent.futures, json, os, re, shutil, subprocess, sys, tempfile, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sortimports import IMPORT, KEEP, import_lines, imports, is_project, normalize


BASE = "Lib.Speed"           # its marked imports (Mathlib, Aesop) are there on purpose


class Stale(Exception):
    pass


def proposals(log, src_prefix):
    cur, rem, add, files = None, {}, {}, []
    for l in open(log, encoding="utf-8", errors="replace"):
        l = l.rstrip("\n")
        m = re.match(r"^" + re.escape(src_prefix) + r"(.*)\.lean:$", l)
        if m: cur = m.group(1).replace("/", "."); files.append(cur); continue
        m = re.match(r"^  (remove|add) #\[(.*)\]$", l)
        if m and cur:
            items = [x.strip() for x in m.group(2).split(",") if x.strip()]
            (rem if m.group(1) == "remove" else add).setdefault(cur, []).extend(items)
    return files, rem, add


def lean_command(repo, mod):
    """environment, program, arguments (without the output arguments) and source path of the last build of `mod`"""
    rel = os.path.join(*mod.split("."))
    src = os.path.join(repo, "src", rel) + ".lean"
    trace = os.path.join(repo, ".lake/build/lib/lean", rel) + ".trace"
    if not os.path.exists(trace): raise Stale("no trace file")
    msgs = [e["message"] for e in json.load(open(trace)).get("log", []) if e.get("message", "").startswith(".> ")]
    if not msgs: raise Stale("no command in the trace file")
    words = msgs[0][3:].split()
    env, i = dict(os.environ), 0
    while "=" in words[i] and not words[i].startswith("/"):
        k, v = words[i].split("=", 1); env[k] = v; i += 1
    lean, args, skip = words[i], [], False
    for w in words[i + 1:]:
        if skip: skip = False; continue
        if w in ("-o", "-i", "-c", "-b"): skip = True; continue
        args.append(w)
    if src not in args or "--setup" not in args: raise Stale("was not compiled in this tree")
    setup = args[args.index("--setup") + 1]
    if not setup.startswith(repo + "/"): raise Stale("setup file outside this tree")
    for name, files in json.load(open(setup))["importArts"].items():
        if is_project(name) and (repo + "/.lake/build/") not in json.dumps(files):
            raise Stale(f"setup file takes {name} from another tree")
    return env, lean, args, src


def compiles(repo, src, text, env, lean, args):
    """whether `text` compiles in place of the file `src`, and its first error messages"""
    d = tempfile.mkdtemp(prefix="refine-")
    try:
        tmp = os.path.join(d, os.path.basename(src))
        with open(tmp, "w", encoding="utf-8") as f: f.write(text)
        try:
            r = subprocess.run([lean] + [tmp if w == src else w for w in args], env=env, cwd=repo,
                               capture_output=True, text=True, timeout=2400)
        except subprocess.TimeoutExpired:
            return False, ["timed out"]
        errs, tl = [], text.split("\n")
        for l in r.stdout.split("\n"):
            if '"severity":"error"' not in l: continue
            try: m = json.loads(l)
            except ValueError: errs.append(l[:200]); continue
            ln = m.get("pos", {}).get("line", 0)
            errs.append(f"L{ln}: " + " ".join(m.get("data", "").split())[:300] + "   | " + (tl[ln - 1].strip()[:140] if 0 < ln <= len(tl) else ""))
        if r.returncode != 0 and not errs: errs.append(f"exit status {r.returncode}: " + " ".join(r.stderr.split())[:200])
        return not errs, errs[:3]
    finally:
        shutil.rmtree(d, ignore_errors=True)


def edit(lines, name, new):
    """replace (or with new=None remove) the header import line of module `name`"""
    out, idx = [], set(import_lines(lines))
    for i, l in enumerate(lines):
        if i in idx and IMPORT.match(l).group(4) == name:
            if new is not None: out.append(new)
        else:
            out.append(l)
    return out


def insert(lines, extra):
    last = import_lines(lines)[-1]
    return lines[:last + 1] + extra + lines[last + 1:]


def kind(s):
    m = IMPORT.match(s)
    return m.group(4), bool(m.group(1))


def refine(repo, mod, rem, add):
    t0, log, why = time.time(), [], []
    try:
        env, lean, args, src = lean_command(repo, mod)
    except Stale as e:
        return mod, [f"? {e}"], why, time.time() - t0
    text = open(src, encoding="utf-8").read()
    lines = text.split("\n")
    run = lambda trial: compiles(repo, src, normalize("\n".join(trial)), env, lean, args)
    have = imports(lines)
    adds = {kind(a)[0]: a for a in add}
    new = [a for n, a in adds.items() if n not in have]
    steps = []                                           # (module, what, new line or None)
    for r in rem:
        n, pub = kind(r)
        if n not in have: log.append(f"? {n} is not imported"); continue
        if "shake: keep" in have[n]: continue
        if n in adds:
            apub = kind(adds[n])[1]
            if pub and not apub: steps.append((n, "private", "import " + n))
            elif apub and not pub: steps.append((n, "public", "public import " + n))
        else:
            steps.append((n, "dropped", None))
    together = insert(lines, new) if new else list(lines)
    for n, what, line in steps: together = edit(together, n, line)
    if len(steps) + bool(new) > 1 and run(together)[0]:
        lines = together
        log += [f"added {a}" for a in new] + [f"{what} {n}" for n, what, _ in steps]
    else:
        if new:
            trial = insert(lines, new)
            if run(trial)[0]: lines = trial; log += [f"added {a}" for a in new]
            else: log += [f"? could not add {a}" for a in new]
        for n, what, line in steps:
            good, errs = run(edit(lines, n, line))
            if good: lines = edit(lines, n, line); log.append(f"{what} {n}"); continue
            old = imports(lines)[n]
            if what == "public": log.append(f"? could not make {n} public"); continue
            if what == "dropped" and IMPORT.match(old).group(1):     # cannot go: maybe it can be private
                trial = edit(lines, n, "import " + n + KEEP)
                if run(trial)[0]:
                    lines = trial; log.append(f"KEEP as private {n}"); why.append((n, "dropped", errs)); continue
            lines = edit(lines, n, old + KEEP); log.append(f"KEEP {n}"); why.append((n, what, errs))
    new_text = normalize("\n".join(lines))
    if new_text != text: open(src, "w", encoding="utf-8").write(new_text)
    return mod, log, why, time.time() - t0


def unmark(repo):
    """remove the marks outside Lib/Speed.lean; returns (module, import) pairs"""
    srcdir, out = os.path.join(repo, "src"), []
    for d, _, fs in os.walk(srcdir):
        for f in fs:
            if not f.endswith(".lean"): continue
            p = os.path.join(d, f); mod = os.path.relpath(p, srcdir)[:-5].replace(os.sep, ".")
            if mod == BASE: continue
            lines = open(p, encoding="utf-8").read().split("\n")
            hit = False
            for i in import_lines(lines):
                if lines[i].endswith(KEEP):
                    lines[i] = lines[i][:-len(KEEP)]; out.append((mod, IMPORT.match(lines[i]).group(4))); hit = True
            if hit: open(p, "w", encoding="utf-8").write("\n".join(lines))
    return sorted(out)


if __name__ == "__main__":
    repo = os.path.abspath(sys.argv[1])
    srcdir = os.path.join(repo, "src")
    if "--unmark" in sys.argv:
        out = unmark(repo)
        print(f"marks removed: {len(out)} in {len({m for m, _ in out})} files")
        sys.exit(0)
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 12
    skip = set(sys.argv[sys.argv.index("--skip") + 1:]) if "--skip" in sys.argv else set()
    files, rem, add = proposals(sys.argv[2], srcdir + "/")
    todo = [f for f in files if f not in skip and (rem.get(f) or add.get(f))]
    print(f"{len(todo)} files, {sum(len(rem.get(f, [])) + len(add.get(f, [])) for f in todo)} proposed lines", flush=True)
    kept = made = odd = 0
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for mod, log, why, secs in ex.map(lambda f: refine(repo, f, rem.get(f, []), add.get(f, [])), todo):
            kept += sum(l.startswith("KEEP") for l in log); odd += sum(l.startswith("?") for l in log)
            made += sum(not l.startswith(("KEEP ", "?")) for l in log)
            print(f"{mod} ({secs:.0f}s): " + "; ".join(log), flush=True)
            for n, what, errs in why:
                for e in errs: print(f"    why {n} cannot be {what}: {e}", flush=True)
    print(f"changes made: {made}, imports marked `shake: keep`: {kept}, problems: {odd}")
