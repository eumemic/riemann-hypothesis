# Private imports with `lake shake`

These scripts made the pull request that turns `public import`s into plain ones where the importing
file uses the import only inside proofs. They are not needed to build the project, and they are not
part of that pull request.

`lake shake` computes, from the compiled files, which imports a file needs and whether it needs them
in its exported part. Applied as it is, its result does not compile, and it changes a few
statements without any error (see the last two sections). The scripts find the imports concerned by
compiling and by comparing declarations, mark them `-- shake: keep`, and stop when the tree builds,
`lake shake` has nothing more to propose, and every declaration is what it was before.

## Running it

```bash
# in a checkout with a finished `lake build`; DIR is its absolute path
shake-pipeline.sh DIR ORIG_REV TAG [PHASE] [SEED_SRC]
```

`ORIG_REV` is the commit the checkout is at. Logs go to `~/TAG-*.log`, the summary to
`~/TAG-pipeline.log`, and the result to `~/TAG.patch`, a diff against `ORIG_REV`. `SEED_SRC` is the
`src` directory of an earlier result; its marks are carried over, which saves build rounds. A run
needs the toolchain, Python 3.9 or newer, and the time of three to six builds of the project.

`onto.sh DIR REF TAG` brings the tree a run left onto a newer commit without a new run. It merges
the commit. In a file where both changed the import lines, `union.py` builds the import block from
the result's lines, plus the imports the commit added, minus those it removed. Then it builds, and
a file that fails gets its imports made public and the commit's imports back. The tree compiles
after that, but `lake shake` was not asked again and declarations were not compared, as a run does.
To compare them afterwards, build the commit in a second checkout and run `lean-queries.sh decls`
on both trees and `same.py` on the two outputs.

`why.py DIR` compiles every file that has a marked import with that import made private (or
removed, if it is private) and prints the errors.

The steps:

1. `lean-queries.sh decls` records every declaration of the tree as it is, and
   `lean-queries.sh attrs` the files that set attributes on declarations of other files.
2. `speed.py`: `Lib/Speed.lean` gets `public import Mathlib -- shake: keep` and
   `public import Aesop -- shake: keep`. Mathlib stays imported as a whole. Mathlib imports Aesop
   only at the meta phase, and without the second line `lake shake` adds imports of Aesop files to
   every file whose proofs call `aesop`. `docs.py` edits the three sentences of the documentation
   that describe the import structure.
3. `lake shake --force --add-public-downstream Lib.Speed --fix` over all modules under `src`.
   `--add-public-downstream` keeps `Lib.Speed`, and with it Mathlib, in the public imports of every
   file; without it `lake shake` replaces `import Mathlib` by the Mathlib files each file uses,
   about 45 per file. `src/Statements.lean` is put back afterwards: it is a challenge file and
   imports only Mathlib.
4. `sortimports.py`: in each changed import block the public imports come first, and each group
   is in alphabetical order.
5. Build. For every file that fails, `repair.py` makes its imports public again and puts back the
   imports it had before; if the file fails a second time, it adds the project file that declares a
   namespace or a name the errors call unknown. Build again, until the build passes.
6. `lake shake` again, without `--fix`. It now proposes to undo most of step 5. `refine.py` tries
   these proposals file by file: all of a file's proposals together, and if the file does not
   compile with them, the additions first and then the other changes one import at a time. A file
   is compiled alone, with the arguments Lake used and a copy of the file with the new header. An
   import that can be neither made private nor removed gets `-- shake: keep`, and the errors that
   decided it are printed. Then step 5 again (a change in one file can break a file that imports
   it), and step 6 again, until `lake shake` proposes nothing except for `Statements.lean`.
7. Recheck (skipped with `RECHECK=0`): the marks outside `Lib/Speed.lean` are removed, and step 6
   decides all of them once more.
8. `lean-queries.sh decls` again, and `same.py` compares with step 1. Where a declaration differs,
   `fixattrs.py` gives the file back, as a marked private import, the attribute-setting files of
   step 1 that it could see before and cannot see now; then steps 5 and 6 again. Each import added
   here is then removed once more on its own, and stays only if a declaration differs without it.

## Counting what a change recompiles

`modgraph.py SRC_DIR` reads the import lines and prints, for the files of the project, how many
other files Lake recompiles when the exported part of one file changes. The rule is the one of
`ModuleImportInfo.addImport` in Lake's `Lake/Build/Module.lean` (v4.37): a module is recompiled when
the exported part changes in a module it imports, or in one that such a module reaches through
`public import`s only. It needs no build.

## Imports that `lake shake` gets wrong: the file does not compile

`lake shake` reads which constants the compiled file refers to, and where. Lean moves every proof
that occurs in a definition into an auxiliary theorem, so what such a proof uses counts as a private
use. But Lean elaborates the value of a definition or of an instance with the public imports only,
including the proofs written as terms in it and every goal of a tactic block that builds it. Only a
`by` block that proves a proposition sees the private imports. So a file fails with the import
`lake shake` proposes in these situations:

- A lemma, or a field of a structure, is named in a proof inside a definition:
  `def reduction := (exists_reduction_and_idele_generator 𝔪.ne_bot).choose`, a field
  `continuous_toFun := G.continuous_reindex _ (by simp …)`, or `exact relIndex_map_stdLattice_ne_zero …`
  in the tactic block of an `instance … : Fintype … := by`.
- A definition, an `abbrev` or a `deriving` clause needs an instance of a class that is a
  proposition (`IsProGalois`, `IsMulRightInvariant`, `ContinuousSMul`), and the instance is in the
  imported file.
- An `open` line names a namespace that only the imported file declares, and the file uses nothing
  else of it.

## Imports that `lake shake` gets wrong: a statement changes

A file can change how other files elaborate without any of them referring to it:
`attribute [instance 10] Subalgebra.instSMulSubtypeMem …` in
`Lib/General/NumberTheory/CoefficientRings.lean` lowers the priority of six instances of Mathlib for
every file that can see it. `lake shake` removes that file from importers that do not use its
declarations, and four statements of `Lib/Shimura/Eigenspace.lean` then elaborate with another
instance of scalar multiplication. They still compile, and so do the files that use them.
`lean-queries.sh attrs` lists the files that do this (five, with `Lib.Speed`), and step 8 finds the
places where it matters. `same.py` compares the type of every declaration written in the sources,
and the value of every definition; it does not compare proofs.
