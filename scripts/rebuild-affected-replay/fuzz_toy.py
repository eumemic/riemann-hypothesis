"""Random sequences of edits and builds on a small project, comparing `rebuild-affected.py` with `lake build`.

usage: fuzz_toy.py SEED STEPS [SCRIPT]

Two copies of a fourteen-module project get the same edits. One is built with `lake build`, the other
with the script. After every build the exit codes must agree, the same modules must have outputs, and
those outputs must be the same. Between such builds the run also does things the script has to cope
with: builds of a single target, plain `lake build` in the script's copy, and edits that do not compile.

The project is made so that the dependencies the rule has cases for all occur: a definition reached
by unfolding, structure fields that are removed or swapped, instances that appear, disappear and
compete, a name that is declared in two namespaces, modules that come into view and go out of it, an
import that is not re-exported, a
namespace that two modules declare in, an equation lemma that the first module to ask generates, and
a name with two meanings of which Lean rejects one, and a `simp` call that asks for a generated lemma
and does not use it.
"""
import importlib.util, json, random, shutil, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = Path(sys.argv[3]).resolve() if len(sys.argv) > 3 else next(p for p in (HERE / "rebuild-affected.py", HERE.parent / "rebuild-affected.py") if p.exists())
spec = importlib.util.spec_from_file_location("ra", SCRIPT)
ra = importlib.util.module_from_spec(spec); spec.loader.exec_module(ra)

LAKEFILE = 'name = "toy"\nsrcDir = "src"\ndefaultTargets = ["Toy"]\n\n[[lean_lib]]\nname = "Toy"\nglobs = ["Toy.+"]\n'
DOMAINS = {
    "A_base": ["4", "2 + 2", "0 + 4", "5"], "A_unused": [True, False], "A_swap": [False, True], "A_inst": [False, True],
    "A_proof": [0, 1], "B_importF": [False, True], "B_importG": [True, False], "B_extra": [False, True],
    "B_ns": [False, True], "B_mismatch": [False, True], "B_err": [False, True], "C_unrel": ["7", "3 + 4", None],
    "C_err": [False, True], "C_privF": [False, True], "D_c": [0, 1], "E_c": [0, 1], "F_kind": ["fresh", "sub", "inst", "substr"], "J_simp": [True, False],
}
# Values with which some module does not compile. They are chosen less often and soon repaired.
BAD = {"A_base": "5", "B_importG": False, "B_mismatch": True, "B_err": True, "C_unrel": None, "C_err": True}


def sources(v):
    def mod(imports, body, private=()):
        head = "module\n\n" + "".join(f"public import Toy.{i}\n" for i in imports) + "".join(f"import Toy.{i}\n" for i in private) + ("\n" if imports else "")
        return head + "@[expose] public section\n\nnamespace Toy\n\n" + body + "\nend Toy\n"
    fields = ["  x : Nat\n", "  y : Nat\n"]
    if v["A_swap"]: fields.reverse()
    a = "structure Geo where\n" + "".join(fields) + ("  unused : Nat\n" if v["A_unused"] else "")
    a += f"\ndef base : Nat := {v['A_base']}\n\ndef helper (n : Nat) : Nat := n + base\n\n"
    a += "theorem helper_pos (n : Nat) : 0 < helper n := by\n  " + ("unfold helper base; omega" if v["A_proof"] == 0 else "unfold helper; unfold base; omega") + "\n"
    if v["A_inst"]: a += "\ninstance instA : Inhabited (Nat × Nat) := ⟨(0, 0)⟩\n"
    b = "def viaHelper : Nat := helper 1\n\n"
    if v["B_extra"]: b += "def extraB : Nat := 0\n\n"
    if v["B_ns"]: b += "def Extra.b : Nat := 0\n\n"
    b += "def geo0 : Geo := { x := 1, y := 2" + (", unused := 3" if v["A_unused"] != v["B_mismatch"] else "") + " }\n\ntheorem geo0_x : geo0.x = 1 := rfl\n"
    if v["B_err"]: b += "\ndef broken oops\n"
    c = "theorem viaHelper_eq : viaHelper = 5 := rfl\n\ndef Sub.c : Nat := 0\n"
    if v["C_unrel"]: c += f"\ndef unrelated : Nat := {v['C_unrel']}\n"
    if v["C_err"]: c += "\ndef broken oops\n"
    f = {"fresh": "def fresh : Nat := 3\n", "sub": "def Sub.unrelated : Nat := 3\n",
         "inst": "instance instF : Inhabited (Nat × Nat) := ⟨(1, 1)⟩\n", "substr": 'def Sub.unrelated : String := "s"\n'}[v["F_kind"]]
    g = "instance : Inhabited Geo := ⟨{ x := 0, y := 0" + (", unused := 0" if v["A_unused"] else "") + " }⟩\n"
    return {
        "A": mod([], a),
        "B": mod(["A"] + (["F"] if v["B_importF"] else []) + (["G"] if v["B_importG"] else []), b),
        "C": mod(["B"], c, ["F"] if v["C_privF"] else []),
        "D": mod(["C"], f"-- {v['D_c']}\ntheorem d_only : unrelated + 0 = 7 := by simp [unrelated]\n"),
        "E": mod(["B"], f"-- {v['E_c']}\ntheorem geo0_y : geo0.y = 2 := rfl\n\ntheorem geo_x (g : Geo) : g.x = g.x := rfl\n"),
        "F": mod([], f),
        "G": mod(["A"], g),
        "H": mod(["B"], "def pick : Geo := default\n"),
        "I": mod(["C"], "theorem i_only : (default : Nat × Nat) = (0, 0) := rfl\n"),
        "J": mod(["B"], "theorem j_only : helper 1 = 1 + base := " + ("by simp [helper]" if v["J_simp"] else "rfl") + "\n"),
        "K": mod(["J"], "theorem k_only : helper 2 = 2 + base := by simp [helper]\n"),
        "L": mod(["B"], "def Extra.l : Nat := 1\n"),
        "M": mod(["C"], "open Sub in\ntheorem m_only : Nat.succ unrelated = 8 := rfl\n"),
        "O": mod(["J"], "set_option linter.unusedSimpArgs false in\ntheorem o_only : (2 : Nat) + 0 = 2 := by simp [helper]\n"),
    }


def outputs(project):
    lib, res = project / ".lake/build/lib/lean/Toy", {}
    for olean in sorted(lib.glob("*.olean")):
        module = ra.Module(str(olean), lambda s: s.rsplit(b"/", 1)[-1])
        raw = [p.read_bytes() if p.exists() else b"" for p in
               (olean, olean.with_suffix(".ilean"), olean.with_suffix(".ir"), project / ".lake/build/ir/Toy" / (olean.stem + ".c"))]
        res[olean.stem] = (raw, [module.digest(root) for root in module.roots[1:]])
    return res


def main():
    seed, steps = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    top = Path(tempfile.mkdtemp(prefix=f"fuzz-{seed}-"))
    stock, ours = top / "stock", top / "ours"
    v = {k: d[0] for k, d in DOMAINS.items()}
    for project in (stock, ours):
        (project / "src/Toy").mkdir(parents=True)
        (project / "lakefile.toml").write_text(LAKEFILE)
        (project / "lean-toolchain").write_text(getattr(ra, "CHECKED_TOOLCHAINS", ["leanprover/lean4:v4.37.0-rc1"])[0] + "\n")
    written, history, counts = {}, [], {}

    def write():
        for name, text in sources(v).items():
            if written.get(name) != text:
                for project in (stock, ours): (project / "src/Toy" / f"{name}.lean").write_text(text)
                written[name] = text

    def run(cmd, cwd): return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)

    def fail(what, detail=""):
        print(f"\nMISMATCH at step {len(history)} (seed {seed}): {what}\n{detail}\nhistory:")
        for h in history[-12:]: print("  ", json.dumps(h))
        print("projects kept in", top)
        sys.exit(1)

    write()
    for project in (stock, ours): run(["lake", "build"], project)
    run([sys.executable, str(SCRIPT)], ours)
    for step in range(steps):
        edits = {}
        if rng.random() < 0.5:           # repair what does not compile
            for key, bad in BAD.items():
                if v[key] == bad: v[key] = edits[key] = DOMAINS[key][0]
        for key in rng.sample(sorted(DOMAINS), rng.choice([1, 1, 2, 3])):
            value = rng.choice([x for x in DOMAINS[key] if x != v[key]])
            if BAD.get(key, "") == value and rng.random() < 0.6: continue
            v[key] = edits[key] = value
        write()
        action = rng.choice(["tool"] * 7 + ["target"] * 2 + ["plain", "plain-target", "nothing"])
        target = [rng.choice(["Toy.B", "Toy.C", "Toy.J", "Toy.E"])] if "target" in action else []
        history.append({"step": step, "edits": edits, "action": action, "target": target})
        counts[action] = counts.get(action, 0) + 1
        if action == "nothing": continue
        if action.startswith("plain"):
            for project in (stock, ours): run(["lake", "build"] + target, project)
            continue
        a = run(["lake", "build"] + target, stock)
        b = run([sys.executable, str(SCRIPT)] + target, ours)
        history[-1]["rc"] = [a.returncode, b.returncode]
        if "Traceback" in b.stderr + b.stdout: fail("the script crashed", (b.stdout + b.stderr)[-3000:])
        if (a.returncode != 0) != (b.returncode != 0):
            fail(f"exit codes: lake {a.returncode}, script {b.returncode}", "--- lake\n" + a.stdout[-1500:] + "\n--- script\n" + b.stdout[-2500:] + b.stderr[-1500:])
        x, y = outputs(stock), outputs(ours)
        if x.keys() != y.keys(): fail(f"modules with outputs: only lake {sorted(x.keys() - y.keys())}, only script {sorted(y.keys() - x.keys())}", b.stdout[-2500:])
        differ = sorted(m for m in x if x[m] != y[m])
        if differ: fail(f"outputs differ for {differ}", b.stdout[-2500:])
        log = ours / ".lake/rebuild-affected/run.jsonl"
        runs = [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []
        counts["compiled"] = counts.get("compiled", 0) + sum(1 for r in runs if not r["reuse"])
        counts["reused"] = counts.get("reused", 0) + sum(1 for r in runs if r["reuse"])
        counts["failed builds"] = counts.get("failed builds", 0) + (a.returncode != 0)
        if a.returncode == 0 and not target and run(["lake", "build", "--no-build"], ours).returncode != 0:
            fail("after the script, `lake build --no-build` finds something to build")
    print(f"seed {seed}: {steps} steps without a mismatch; {counts}")
    shutil.rmtree(top)


if __name__ == "__main__":
    main()
