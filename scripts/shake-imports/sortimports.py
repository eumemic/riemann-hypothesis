"""Order the import block of Lean files: `public import`s first, then the other imports, each group
sorted by module name. Files whose import block contains anything but import lines are left alone.

usage: sortimports.py FILE_OR_DIR...     prints the number of files changed"""
import os, re, sys

IMPORT = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?(\S+)(.*)$")
KEEP = " -- shake: keep"


def is_project(name):
    return name.startswith(("Lib.", "New.")) or name in ("Statements", "Main")


def import_lines(lines):
    """indices of the import lines in the header of a file (a line that starts with `import` further
    down, in a docstring for instance, is not one)"""
    out, depth = [], 0
    for i, line in enumerate(lines):
        s = line.strip()
        if depth:
            depth += line.count("/-") - line.count("-/")
        elif IMPORT.match(line):
            out.append(i)
        elif s == "" or s.startswith("--") or s == "module" or s.startswith("module --"):
            pass
        elif s.startswith("/-") and not s.startswith("/-!") and not out:      # a comment above the imports
            depth = line.count("/-") - line.count("-/")
        else:
            break
    return out


def imports(lines):
    """module name -> line, for the header of a file"""
    return {IMPORT.match(lines[i]).group(4): lines[i] for i in import_lines(lines)}


def normalize(text):
    lines = text.split("\n")
    idx = import_lines(lines)
    if not idx: return text
    a, b = idx[0], idx[-1] + 1
    block = lines[a:b]
    if any(not IMPORT.match(l) for l in block): return text          # blank lines or comments inside
    key = lambda l: IMPORT.match(l).group(4)
    pub = sorted((l for l in block if IMPORT.match(l).group(1)), key=key)
    prv = sorted((l for l in block if not IMPORT.match(l).group(1)), key=key)
    return "\n".join(lines[:a] + pub + prv + lines[b:])


def run(paths):
    n = 0
    for p in paths:
        files = [p] if os.path.isfile(p) else [os.path.join(d, f) for d, _, fs in os.walk(p) for f in fs if f.endswith(".lean")]
        for f in files:
            text = open(f, encoding="utf-8").read()
            new = normalize(text)
            if new != text:
                open(f, "w", encoding="utf-8").write(new); n += 1
    return n


if __name__ == "__main__":
    print(f"import blocks reordered: {run(sys.argv[1:])}")
