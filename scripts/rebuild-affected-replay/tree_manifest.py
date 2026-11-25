"""Fingerprint every module output in a Lake build directory.

usage: tree_manifest.py BUILD_DIR OUT_TSV [JOBS]

One line per module: name, then for .olean/.ilean/.ir/.ir.sig/.c a hash of the bytes, and for the
.server and .private parts a structural hash in which absolute source paths are cut to `src/...`
(linter messages stored there hold the path of the checkout that compiled the module)."""
import hashlib, importlib.util, multiprocessing, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("ra", next(p for p in (os.path.join(HERE, "rebuild-affected.py"), os.path.join(HERE, "..", "rebuild-affected.py")) if os.path.exists(p)))
ra = importlib.util.module_from_spec(spec); spec.loader.exec_module(ra)

def norm(s):
    i = s.rfind(b"/src/")
    return s[i + 1:] if s[:1] == b"/" and s.endswith(b".lean") and i >= 0 else s

def raw(p):
    try:
        with open(p, "rb") as f: return hashlib.blake2b(f.read(), digest_size=8).hexdigest()
    except OSError: return "-"

def one(args):
    build, rel = args
    stem = os.path.join(build, "lib", "lean", rel)
    out = [rel.replace(os.sep, "."), raw(stem + ".olean"), raw(stem + ".ilean"), raw(stem + ".ir"), raw(stem + ".ir.sig"),
           raw(os.path.join(build, "ir", rel + ".c"))]
    try:
        m = ra.Module(stem + ".olean", norm)
        out += [m.digest(r)[:8].hex() for r in m.roots[1:]] + ["-"] * (3 - len(m.roots))
    except Exception as e:
        out += [f"ERR:{type(e).__name__}", "-"]
    return "\t".join(out)

if __name__ == "__main__":
    build, outp = sys.argv[1], sys.argv[2]
    jobs = int(sys.argv[3]) if len(sys.argv) > 3 else os.cpu_count()
    lib = os.path.join(build, "lib", "lean")
    rels = [os.path.relpath(os.path.join(d, f), lib)[:-6] for d, _, fs in os.walk(lib) for f in fs if f.endswith(".olean")]
    with multiprocessing.Pool(jobs) as pool, open(outp, "w") as w:
        for line in pool.imap_unordered(one, [(build, r) for r in rels], chunksize=64): w.write(line + "\n")
    print(len(rels), "modules")
