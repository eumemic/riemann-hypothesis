"""Fetch the output bundles CI published for the modules it recompiled in some batches, and keep
what a replay of `rebuild-affected.py` needs from each bundle.

usage: batch_extract.py META OUT JOBS BATCH...        (BATCH: 1 for b2, ..., 19 for b20)

For each bundle <id> this writes under OUT/rec/<id[:2]>/:
  <id>.json    module, fingerprints of the 7 output parts, projections, extra module uses, imports
  <id>.names   u64 array: hashes of all names in the three .olean parts
  <id>.all     u64 array: hashes of the names of all its constants
  <id>.olean   the public .olean
"""
import array, gzip, hashlib, importlib.util, json, multiprocessing, os, shutil, subprocess, sys, time, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("ra", next(p for p in (os.path.join(HERE, "rebuild-affected.py"), os.path.join(HERE, "..", "rebuild-affected.py")) if os.path.exists(p)))
ra = importlib.util.module_from_spec(spec); spec.loader.exec_module(ra)

# main before batch b2, then after each of the batches b2 ... b20
COMMITS = ["a28ad7ec8b", "343b1de38b", "c9883164b0", "bb9476b875", "1cd97d8aa4", "1da818b50f", "307cef33f0", "9282d3a102",
           "67c00ce102", "4a5b4a2d2a", "c40250a501", "fcb6eac753", "27b5578748", "a18a350c3e", "246656fc62", "ef451fc356", "251c7b05dd", "8e5cefeeaf", "d91ae2678e", "91b2735308"]
BASE = "https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis/"
LEANTAR = os.path.join(subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True, check=True).stdout.strip(), "bin", "leantar")
TMP = "/dev/shm/bx" if os.path.isdir("/dev/shm") else "/tmp/bx"


def manifest(meta, sha):
    rev = json.load(open(f"{meta}/rev-{sha}.json"))
    out = {}
    with gzip.open(f"{meta}/mm-{rev['module_manifest_sha256'][:12]}.jsonl.gz", "rt", encoding="utf-8") as f:
        for line in f:
            row = json.loads(line)
            if isinstance(row, list): out[row[0]] = (row[1], row[2])
    return out


def norm(s):
    i = s.rfind(b"/src/")
    return s[i + 1:] if s[:1] == b"/" and s.endswith(b".lean") and i >= 0 else s


def raw(p):
    try:
        with open(p, "rb") as f: return hashlib.blake2b(f.read(), digest_size=8).hexdigest()
    except OSError: return "-"


def rec_path(out, ltar): return os.path.join(out, "rec", ltar[:2], ltar[:-5])


def fetch(ltar, input_hash, dest):
    """Download and unpack one bundle into `dest`; returns the path of its public .olean."""
    os.makedirs(os.path.join(dest, "lib")); os.makedirs(os.path.join(dest, "ir"))
    f = os.path.join(dest, ltar)
    for attempt in range(6):
        try:
            req = urllib.request.Request(BASE + ltar[:-5] + ".art", headers={"User-Agent": "curl/8"})
            with urllib.request.urlopen(req, timeout=120) as r, open(f, "wb") as w: shutil.copyfileobj(r, w)
            break
        except Exception:
            if attempt == 5: raise
            time.sleep(2 * (attempt + 1))
    subprocess.run([LEANTAR, "-C", os.path.join(dest, "lib"), "-C", os.path.join(dest, "ir"), "-x", "-f", "-j", "-"],
                   input=json.dumps([{"file": f, "hash": input_hash}]).encode(), check=True, capture_output=True)
    os.unlink(f)
    oleans = [x for x in os.listdir(os.path.join(dest, "lib")) if x.endswith(".olean")]
    return os.path.join(dest, "lib", oleans[0])


def work(args):
    out, ltar, mod, input_hash = args
    rp = rec_path(out, ltar)
    if os.path.exists(rp + ".json"): return None
    dest = os.path.join(TMP, ltar[:-5])
    shutil.rmtree(dest, ignore_errors=True)
    try:
        olean = fetch(ltar, input_hash, dest)
        stem = olean[:-6]
        m = ra.Module(olean, norm)
        fp = [raw(stem + e) for e in (".olean", ".ilean", ".ir", ".ir.sig")] + [raw(os.path.join(dest, "ir", os.path.basename(stem) + ".c"))]
        fp += [m.digest(r)[:8].hex() for r in m.roots[1:]] + ["-"] * (3 - len(m.roots))
        plain = ra.Module(olean)
        f = ra.facts(plain)
        os.makedirs(os.path.dirname(rp), exist_ok=True)
        with open(rp + ".names", "wb") as w: w.write(array.array("Q", sorted(f["names"])).tobytes())
        with open(rp + ".all", "wb") as w: w.write(array.array("Q", sorted(plain.all_names())).tobytes())
        shutil.copyfile(olean, rp + ".olean")
        rec = {"m": mod, "fp": fp, "proj": sorted(f["proj"]), "extra": sorted(f["extra"]), "code": f["code"],
               "sizes": [e - b for b, e, _ in plain.parts]}
        with open(rp + ".json.tmp", "w") as w: json.dump(rec, w)
        os.replace(rp + ".json.tmp", rp + ".json")
        return None
    except Exception as e:
        return f"{ltar} {mod}: {type(e).__name__}: {e}"
    finally:
        shutil.rmtree(dest, ignore_errors=True)


def needed(meta, batches):
    todo = {}
    for k in batches:
        a, b = manifest(meta, COMMITS[k - 1]), manifest(meta, COMMITS[k])
        for m, (ih, ltar) in b.items():
            if m not in a or a[m][0] != ih:
                todo[ltar] = (m, ih)
                if m in a: todo[a[m][1]] = (m, a[m][0])
        for m, (ih, ltar) in a.items():          # deleted modules: their declarations are needed
            if m not in b: todo[ltar] = (m, ih)
    return todo


if __name__ == "__main__":
    meta, out, jobs = sys.argv[1], sys.argv[2], int(sys.argv[3])
    todo = needed(meta, [int(x) for x in sys.argv[4:]])
    args = [(out, ltar, m, ih) for ltar, (m, ih) in todo.items() if not os.path.exists(rec_path(out, ltar) + ".json")]
    print(f"{len(todo)} bundles needed, {len(args)} to fetch", flush=True)
    os.makedirs(TMP, exist_ok=True)
    t, n, errs = time.time(), 0, 0
    with multiprocessing.Pool(jobs) as pool:
        for r in pool.imap_unordered(work, args, chunksize=8):
            n += 1
            if r: errs += 1; print("ERROR", r, flush=True)
            if n % 2000 == 0: print(f"{n}/{len(args)} {time.time() - t:.0f}s errors {errs}", flush=True)
    print(f"done {n} in {time.time() - t:.0f}s, errors {errs}", flush=True)
