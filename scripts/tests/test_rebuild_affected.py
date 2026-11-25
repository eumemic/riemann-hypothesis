#!/usr/bin/env python3
"""Checks rebuild-affected.py against stock Lake on a small project.

Each test edits two copies of the same project, builds one with `lake build` and the other with
rebuild-affected.py, and requires the same exit status and the same outputs for every module. It
also checks which modules the script compiled. The tests run in the order of their names and build
on each other's state. Needs the toolchain of `lean-toolchain`; skipped when `lake` is not
installed. Takes about a minute and a half.
"""
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parent.parent
SCRIPT = SCRIPTS / "rebuild-affected.py"
spec = importlib.util.spec_from_file_location("rebuild_affected", SCRIPT)
ra = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ra)

LAKEFILE = """\
name = "toy"
srcDir = "src"
defaultTargets = ["Toy"]

[[lean_lib]]
name = "Toy"
globs = ["Toy.+"]
"""
HEAD = "module\n\n{imports}@[expose] public section\n\nnamespace Toy\n\n"
SOURCES = {
    "A": ("", """\
structure Geo where
  x : Nat
  y : Nat
  unused : Nat

def base : Nat := 4

def helper (n : Nat) : Nat := n + base

theorem helper_pos (n : Nat) : 0 < helper n := by
  unfold helper base; omega
"""),
    "B": ("public import Toy.A\n\n", """\
def viaHelper : Nat := helper 1

def geo0 : Geo := ⟨1, 2, 3⟩

theorem geo0_x : geo0.x = 1 := rfl
"""),
    "C": ("public import Toy.B\n\n", """\
theorem viaHelper_eq : viaHelper = 5 := rfl

def unrelated : Nat := 7
"""),
    "D": ("public import Toy.C\n\n", "theorem d_only : unrelated + 0 = 7 := by simp [unrelated]\n"),
    "E": ("public import Toy.B\n\n", "theorem geo0_y : geo0.y = 2 := rfl\n\ntheorem geo_x (g : Geo) : g.x = g.x := rfl\n"),
}


def source(name, body=None, imports=None):
    return HEAD.format(imports=SOURCES[name][0] if imports is None else imports) + (SOURCES[name][1] if body is None else body) + "\nend Toy\n"


def outputs(project):
    """{module: fingerprints of its outputs}; the `.server` and `.private` parts by structure."""
    lib, res = project / ".lake/build/lib/lean/Toy", {}
    for olean in sorted(lib.glob("*.olean")):
        module = ra.Module(str(olean), lambda s: s.rsplit(b"/", 1)[-1])     # drop the directory of source paths
        raw = [olean.read_bytes(), olean.with_suffix(".ilean").read_bytes(), olean.with_suffix(".ir").read_bytes(),
               (project / ".lake/build/ir/Toy" / (olean.stem + ".c")).read_bytes()]
        res[olean.stem] = (raw, [module.digest(root) for root in module.roots[1:]])
    return res


class Headers(unittest.TestCase):
    def parse(self, text):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "X.lean").write_text(text)
            return ra.header(str(Path(d) / "X.lean"))

    def test_imports_with_comments(self):
        text = ("/- Copyright\n /- nested -/ still a comment -/\nmodule\n\npublic import A.B\n"
                "import all C.D -- unfold `x`\npublic meta import E\nimport F import G\n/-! doc -/\nimport H\n\n"
                "theorem x : True := trivial\nimport Z\n")
        self.assertEqual(self.parse(text), (True, [("A.B", True, False, False), ("C.D", False, True, False),
                                                   ("E", True, False, True), ("F", False, False, False),
                                                   ("G", False, False, False), ("H", False, False, False)]))

    def test_not_a_module(self):
        self.assertEqual(self.parse("import Mathlib\nopen Nat\n"), (False, [("Mathlib", False, False, False)]))

    def test_words_of_a_source(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "X.lean").write_text("theorem foo' (h : ¬bar₂) : ↑x⁻¹ = Nat.succ! (λy => f'ᵀ y) := by simp [ℝ, α.β, «q»]; exact?% 2*z\n")
            self.assertEqual(ra.source_tokens(str(Path(d) / "X.lean")),
                             {"theorem", "foo'", "h", "bar₂", "x", "Nat", "succ!", "y", "f'", "by", "simp", "ℝ", "α", "β", "q", "exact?", "z"})

    def test_order_in_which_lean_loads_modules(self):
        imports = {"M": [("A", False, False), ("B", False, False)], "A": [("C", True, False), ("P", False, False)],
                   "B": [("C", True, False), ("D", True, False)], "C": [], "D": [], "P": []}
        self.assertEqual(ra.view(imports.__getitem__, "M"), ["C", "A", "D", "B"])


class Toolchain(unittest.TestCase):
    def test_refuses_a_toolchain_it_was_not_checked_with(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "lakefile.toml").write_text(LAKEFILE)
            (Path(d) / "lean-toolchain").write_text("leanprover/lean4:v4.0.0\n")
            run = subprocess.run([sys.executable, str(SCRIPT)], cwd=d, capture_output=True, text=True)
            self.assertNotEqual(run.returncode, 0)
            self.assertIn("CHECKED_TOOLCHAINS", run.stderr)
            self.assertFalse((Path(d) / ".lake").exists())

    def test_the_pinned_toolchain_is_one_it_was_checked_with(self):
        self.assertIn((SCRIPTS.parent / "lean-toolchain").read_text().strip(), ra.CHECKED_TOOLCHAINS)


@unittest.skipUnless(shutil.which("lake"), "needs the Lean toolchain")
class AgainstStockLake(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.TemporaryDirectory(prefix="rebuild-affected-")
        cls.stock, cls.ours = Path(cls.dir.name) / "stock", Path(cls.dir.name) / "ours"
        for project in (cls.stock, cls.ours):
            (project / "src/Toy").mkdir(parents=True)
            (project / "lakefile.toml").write_text(LAKEFILE)
            shutil.copy(SCRIPTS.parent / "lean-toolchain", project)
        cls.write(cls, {name: source(name) for name in SOURCES})
        for project in (cls.stock, cls.ours):
            subprocess.run(["lake", "build"], cwd=project, check=True, capture_output=True)
        cls.run_ours(cls)       # records what each output was built from

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def write(self, files):
        for project in (self.stock, self.ours):
            for name, text in files.items(): (project / "src/Toy" / f"{name}.lean").write_text(text)

    def run_ours(self, *targets):
        result = subprocess.run([sys.executable, str(SCRIPT), *targets], cwd=self.ours, capture_output=True, text=True)
        log = self.ours / ".lake/rebuild-affected/run.jsonl"
        runs = [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []
        return result, {r["m"].rsplit(".", 1)[-1]: ("reused" if r["reuse"] else r["why"]) for r in runs}

    def build(self, files, compiled, reused, fails=False, targets=()):
        """Apply `files` to both projects and build. `compiled` and `reused` are what the script must do."""
        self.write(files)
        stock = subprocess.run(["lake", "build", *targets], cwd=self.stock, capture_output=True, text=True)
        ours, did = self.run_ours(*targets)
        self.assertEqual(stock.returncode != 0, fails, stock.stdout)
        self.assertEqual(ours.returncode != 0, fails, ours.stdout + ours.stderr)
        self.assertEqual(outputs(self.ours), outputs(self.stock))
        self.assertEqual({m for m, what in did.items() if what != "reused"}, set(compiled), did)
        self.assertEqual({m for m, what in did.items() if what == "reused"}, set(reused), did)
        return did

    def test_1_proof_only(self):
        self.build({"A": source("A").replace("unfold helper base; omega", "unfold helper; unfold base; omega")}, "A", "")

    def test_2_removed_field(self):
        did = self.build({"A": source("A").replace("  unused : Nat\n", ""), "B": source("B").replace("⟨1, 2, 3⟩", "⟨1, 2⟩")},
                         "ABE", "CD")
        self.assertEqual(did["E"], "refers to a changed declaration")

    def test_3_swapped_fields(self):
        a = source("A").replace("  unused : Nat\n", "").replace("  x : Nat\n  y : Nat\n", "  y : Nat\n  x : Nat\n")
        self.build({"A": a, "B": source("B").replace("⟨1, 2, 3⟩", "⟨2, 1⟩")}, "ABE", "CD")

    def test_4_definition_reached_by_unfolding(self):
        # `C` proves `viaHelper = 5` by `rfl`. It mentions `viaHelper`, whose own term does not change.
        # `D` uses `simp [unrelated]`, which Lean records as a use of module `C`.
        a = source("A").replace("  unused : Nat\n", "").replace("  x : Nat\n  y : Nat\n", "  y : Nat\n  x : Nat\n")
        did = self.build({"A": a.replace("def base : Nat := 4", "def base : Nat := 2 + 2")}, "ABCD", "E")
        self.assertEqual(did["C"], "refers to a changed declaration")
        self.assertEqual(did["D"], "uses a macro, notation or attribute of a changed module")
        self.build({"A": a.replace("def base : Nat := 4", "def base : Nat := 5")}, "ABC", "E", fails=True)
        self.build({"A": a}, "ABCD", "E")

    def test_5_new_instance(self):
        a = source("A").replace("  unused : Nat\n", "").replace("  x : Nat\n  y : Nat\n", "  y : Nat\n  x : Nat\n")
        did = self.build({"A": a.replace("\nend Toy", "\ninstance : Inhabited (Nat × Nat) := ⟨(0, 0)⟩\n\nend Toy")}, "ABCDE", "")
        self.assertEqual(did["D"], "can see a module with a change that is not tied to one declaration")
        self.build({"A": a}, "A", "BCDE")       # nothing used the instance, so nothing can notice it is gone

    def test_6_module_comes_into_view(self):
        self.run_ours()
        f = HEAD.format(imports="") + "def fresh : Nat := 3\n\nend Toy\n"
        b = source("B", imports="public import Toy.A\npublic import Toy.F\n\n").replace("⟨1, 2, 3⟩", "⟨2, 1⟩")
        self.build({"F": f, "B": b}, "BF", "CDE")
        self.run_ours()
        did = self.build({"F": f.replace("def fresh", "def Sub.unrelated")}, "CDF", "BE")
        self.assertEqual(did["D"], "source mentions a name that was added or dropped")

    def test_7_removed_declaration_still_used(self):
        self.run_ours()
        did = self.build({"C": source("C").replace("def unrelated : Nat := 7\n", "")}, "CD", "", fails=True)
        self.assertEqual(did["D"], "refers to a changed declaration")

    def test_8_first_pass_changes_nothing_in_the_build_directory(self):
        # If a run dies after its first pass, plain `lake build` must still see what is out of date.
        self.write({"C": source("C")})
        subprocess.run(["lake", "build"], cwd=self.stock, capture_output=True)
        self.run_ours(); self.run_ours()
        self.write({"C": source("C").replace("def unrelated : Nat := 7", "def unrelated : Nat := 3 + 4")})
        state, env, _ = ra.prepare(str(self.ours))
        ra.refresh_base(state)
        asked, replayed = ra.probe_pass(state, env, [])
        self.assertEqual([r["m"] for r in asked], ["Toy.C"])
        self.assertIn("Toy.A", replayed)
        for project in (self.stock, self.ours):
            built = subprocess.run(["lake", "build"], cwd=project, capture_output=True, text=True)
            self.assertIn("Built Toy.C", built.stdout)
        self.assertEqual(outputs(self.ours), outputs(self.stock))
        self.build({}, "", "")

    def test_9_run_after_a_failed_run(self):
        # The first run stops at `B`; `E` waits behind it. The second run must still judge `E` by the rule.
        self.run_ours()
        a, b = (self.ours / "src/Toy/A.lean").read_text(), (self.ours / "src/Toy/B.lean").read_text()
        self.build({"A": a.replace("def base : Nat :=", "def base : Nat := 0 +"), "B": b.replace("def viaHelper", "def viaHelper oops")},
                   "AB", "", fails=True)
        did = self.build({"B": b}, "BCD", "E")
        self.assertEqual(did["B"], "refers to a changed declaration")      # its source is again what its last output was built from

    def test_a_change_log_cut_short(self):
        # As after a full disk. A line added after the stump would be lost, so the script starts over.
        self.run_ours()
        with open(self.ours / ".lake/rebuild-affected/log.lines", "ab") as f: f.write(b'Toy.A\t{"taint": "')
        a = (self.ours / "src/Toy/A.lean").read_text()
        self.write({"A": a.replace("def base : Nat :=", "def base : Nat := 1 +")})
        stock = subprocess.run(["lake", "build"], cwd=self.stock, capture_output=True, text=True)
        ours, did = self.run_ours()
        self.assertIn("starting over", ours.stdout)
        self.assertEqual((stock.returncode, ours.returncode), (1, 1), ours.stdout + ours.stderr)     # `viaHelper = 5` is now false
        self.assertEqual(outputs(self.ours), outputs(self.stock))
        self.assertEqual({m for m, what in did.items() if what != "reused"}, set("ABC"), did)
        self.build({"A": a}, "ABC", "E")       # `C` comes out as it was, so Lake does not ask for `D`

    def test_b_unchanged_definition_in_an_edited_module(self):
        # `B` is edited, but not its `viaHelper`, which unfolds to `base`, and `base` changes in `A`.
        # `C` mentions only `viaHelper` and must still be compiled: its `rfl` is now false.
        self.run_ours()
        a, b = (self.ours / "src/Toy/A.lean").read_text(), (self.ours / "src/Toy/B.lean").read_text()
        self.build({"A": a.replace("def base : Nat :=", "def base : Nat := 1 +"),
                    "B": b.replace("def geo0", "def extra : Nat := 0\n\ndef geo0")}, "ABC", "E", fails=True)
        self.build({"A": a, "B": b}, "ABC", "E")

    def test_c_output_replaced_without_the_script(self):
        # Plain `lake build Toy.A` compiles `A` in both projects, so the script has no record of what
        # changed in it. `C` then also comes to see a new module. Its source is the one the script
        # recorded, but it must not be judged by the rule: `viaHelper = 5` is false now.
        self.run_ours()
        a, b = (self.ours / "src/Toy/A.lean").read_text(), (self.ours / "src/Toy/B.lean").read_text()
        self.write({"A": a.replace("def base : Nat :=", "def base : Nat := 1 +")})
        for project in (self.stock, self.ours):
            subprocess.run(["lake", "build", "Toy.A"], cwd=project, capture_output=True, check=True)
        g = HEAD.format(imports="") + "def other : Nat := 1\n\nend Toy\n"
        did = self.build({"G": g, "B": b.replace("public import Toy.A\n", "public import Toy.A\npublic import Toy.G\n")},
                         "BCEG", "", fails=True)
        self.assertEqual(did["C"], "its own inputs changed")
        self.build({"A": a}, "ABCD", "E")      # `D` was not reached above, so it is still not known to be consistent

    def test_d_run_that_stopped_before_a_module_that_sees_other_modules(self):
        # The first run builds only `B`, which now re-exports a new module `H` and has a new definition.
        # In the second run the header of `B`'s output already lists `H`, so `C` seems to see what it
        # saw before. It must be compiled all the same: `H` declares a name that `C` declares too.
        self.run_ours()
        b = (self.ours / "src/Toy/B.lean").read_text()
        h = HEAD.format(imports="") + "def unrelated : Nat := 1\n\nend Toy\n"
        self.build({"H": h, "B": b.replace("public import Toy.A\n", "public import Toy.A\npublic import Toy.H\n")
                                 .replace("def geo0", "def more : Nat := 0\n\ndef geo0")}, "BH", "", targets=["Toy.B"])
        did = self.build({}, "CE", "", fails=True)
        self.assertEqual(did["C"], "its own inputs changed")
        self.build({"H": h.replace("def unrelated", "def another")}, "CDH", "BE")

    def test_e_outputs_of_the_script_do_not_count_as_replaced(self):
        # Otherwise every run would forget which sources it knows, and nothing would fail.
        epoch = lambda: json.loads((self.ours / ".lake/rebuild-affected/epoch").read_text())
        self.run_ours()
        before, a = epoch(), (self.ours / "src/Toy/A.lean").read_text()
        self.build({"A": a.replace("def base : Nat :=", "def base : Nat := 0 +")}, "ABCD", "E")
        self.build({"A": a}, "ABCD", "E")
        self.assertEqual(epoch(), before)
        plain = subprocess.run(["lake", "build", "-v"], cwd=self.ours, capture_output=True, text=True, check=True)
        self.assertNotIn("Built", plain.stdout)         # Lake accepts what the script left
        self.run_ours()
        self.assertEqual(epoch(), before)

    def test_f_build_directory_removed(self):
        # After `lake clean` everything is compiled, although the script still has the old outputs.
        self.run_ours()
        for project in (self.stock, self.ours): shutil.rmtree(project / ".lake/build")
        modules = {path.stem for path in (self.ours / "src/Toy").glob("*.lean")}
        self.build({}, modules, "")

    def test_g_removed_declaration_that_the_source_could_mean(self):
        # In `N`, `unrelated` can mean `Toy.unrelated` or, through `open Sub`, `Toy.Sub.unrelated`. Lean
        # tries both and rejects the second, a string. Nothing in `N`'s output says so, but `N` was
        # elaborated differently, so it is compiled when `Toy.Sub.unrelated` goes away. `D` says
        # `unrelated` too, but never `Sub`, and is not.
        self.run_ours()
        f = HEAD.format(imports="") + 'def Sub.unrelated : String := "s"\n\ndef Sub.kept : Nat := 0\n\nend Toy\n'
        n = HEAD.format(imports="public import Toy.C\npublic import Toy.F\n\n") + "open Sub in\ntheorem n_only : Nat.succ unrelated = 8 := rfl\n\nend Toy\n"
        self.write({"F": f, "N": n})
        for project in (self.stock, self.ours): subprocess.run(["lake", "build"], cwd=project, capture_output=True, check=True)
        self.run_ours()
        self.write({"F": f.replace('def Sub.unrelated : String := "s"\n\n', "")})
        stock = subprocess.run(["lake", "build"], cwd=self.stock, capture_output=True, text=True)
        ours, did = self.run_ours()
        self.assertEqual((stock.returncode, ours.returncode), (0, 0), ours.stdout + ours.stderr)
        self.assertEqual(outputs(self.ours), outputs(self.stock))
        self.assertEqual(did["N"], "source could mean a declaration that was removed or changed, or that lost a generated lemma", did)
        self.assertEqual(did.get("D", "reused"), "reused", did)

    def test_h_import_added_and_nothing_else_changed(self):
        # `C` gets an import that it does not re-export. Its output changes in the header only, so `D`,
        # which Lake compiles again and which used `C` for more than a term, keeps its output.
        self.run_ours()
        p = HEAD.format(imports="") + "def pfresh : Nat := 0\n\nend Toy\n"
        c = (self.ours / "src/Toy/C.lean").read_text()
        self.write({"P": p, "C": c.replace("public import Toy.B\n", "public import Toy.B\nimport Toy.P\n")})
        stock = subprocess.run(["lake", "build"], cwd=self.stock, capture_output=True, text=True)
        ours, did = self.run_ours()
        self.assertEqual((stock.returncode, ours.returncode), (0, 0), ours.stdout + ours.stderr)
        self.assertIn("Built Toy.D", stock.stdout)
        self.assertEqual(outputs(self.ours), outputs(self.stock))
        self.assertEqual((did["C"], did["D"]), ("its own inputs changed", "reused"), did)

    def test_i_generated_lemma_asked_for_and_not_named_in_the_proof(self):
        # Lean generates `helper.eq_1` for the `simp [helper]` in `Q`. `R`, below `Q`, says `simp [helper]`
        # too and has no use for it, so nothing in `R`'s output names `helper`. When `Q` stops asking,
        # compiling `R` again stores a copy of the lemma in `R`.
        self.run_ours()
        q = HEAD.format(imports="public import Toy.A\n\n") + "theorem q_only : helper 1 = 1 + base := by simp [helper]\n\nend Toy\n"
        r = (HEAD.format(imports="public import Toy.Q\n\n")
             + "set_option linter.unusedSimpArgs false in\ntheorem r_only : (2 : Nat) + 0 = 2 := by simp [helper]\n\nend Toy\n")
        self.write({"Q": q, "R": r})
        for project in (self.stock, self.ours): subprocess.run(["lake", "build"], cwd=project, capture_output=True, check=True)
        self.run_ours()
        self.write({"Q": q.replace("by simp [helper]", "rfl")})
        stock = subprocess.run(["lake", "build"], cwd=self.stock, capture_output=True, text=True)
        ours, did = self.run_ours()
        self.assertEqual((stock.returncode, ours.returncode), (0, 0), ours.stdout + ours.stderr)
        self.assertEqual(outputs(self.ours), outputs(self.stock))
        self.assertEqual(did["R"], "source could mean a declaration that was removed or changed, or that lost a generated lemma", did)


if __name__ == "__main__":
    unittest.main()
