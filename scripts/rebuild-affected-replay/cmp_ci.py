"""Compare a built tree with the outputs CI published for a commit, for the modules of one batch
that Lake compiled again.

usage: cmp_ci.py CACHEMETA HIST BUILD_DIR BATCH [JOBS]

A module is first compared by fingerprints (as tree_manifest.py computes them). If those differ,
CI's bundle is fetched and the two are compared with `same_module`, which ignores the order of
stored linter messages and the numbering of the compiler's local variables."""
import hashlib, importlib.util, json, multiprocessing, os, shutil, sys
HERE = os.path.dirname(os.path.abspath(__file__))
def load(name, file):
    spec = importlib.util.spec_from_file_location(name, next(p for p in (os.path.join(HERE, file), os.path.join(HERE, "..", file)) if os.path.exists(p))); mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
ra, bx = load("ra", "rebuild-affected.py"), load("bx", "batch_extract.py")

def raw(p):
    try:
        with open(p, "rb") as f: return hashlib.blake2b(f.read(), digest_size=8).hexdigest()
    except OSError: return "-"

def one(args):
    hist, build, m, ih, ltar = args
    rel = os.path.join(*m.split("."))
    stem = os.path.join(build, "lib", "lean", rel)
    with open(bx.rec_path(hist, ltar) + ".json") as f: fp = json.load(f)["fp"]
    if not os.path.exists(stem + ".olean"): return m, "missing"
    mine = [raw(stem + e) for e in (".olean", ".ilean", ".ir", ".ir.sig")] + [raw(os.path.join(build, "ir", rel + ".c"))]
    mod = ra.Module(stem + ".olean", bx.norm)
    mine += [mod.digest(r)[:8].hex() for r in mod.roots[1:]] + ["-"] * (3 - len(mod.roots))
    if mine == fp: return m, None
    cols = [c for c, x, y in zip(("olean", "ilean", "ir", "ir.sig", "c", "server", "private"), mine, fp) if x != y]
    if set(cols) <= {"server", "private"}:
        dest = os.path.join(bx.TMP, f"cmpci-{os.getpid()}"); shutil.rmtree(dest, ignore_errors=True)
        try:
            same = ra.same_module(mod, ra.Module(bx.fetch(ltar, ih, dest), bx.norm))
        finally: shutil.rmtree(dest, ignore_errors=True)
        if same: return m, "order of linter messages or variable numbering only"
    return m, "DIFFERENT " + " ".join(cols)

if __name__ == "__main__":
    meta, hist, build, k = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    jobs = int(sys.argv[5]) if len(sys.argv) > 5 else os.cpu_count()
    A, B = bx.manifest(meta, bx.COMMITS[k - 1]), bx.manifest(meta, bx.COMMITS[k])
    todo = [(hist, build, m, ih, ltar) for m, (ih, ltar) in B.items() if m not in A or A[m][0] != ih]
    os.makedirs(bx.TMP, exist_ok=True)
    res = {}
    with multiprocessing.Pool(jobs) as pool:
        for m, what in pool.imap_unordered(one, todo, chunksize=32): res[m] = what
    kinds = {}
    for m, what in res.items(): kinds.setdefault(what or "identical", []).append(m)
    print(f"{len(todo)} modules that Lake compiled again in CI:")
    for what, ms in sorted(kinds.items(), key=lambda kv: -len(kv[1])):
        print(f"  {len(ms):6d}  {what}" + ("" if what in ("identical",) or not what.startswith(("DIFF", "missing")) else "  e.g. " + ", ".join(sorted(ms)[:5])))
