# Rebuilding only what a change can affect

`lake build` compiles a module again whenever a module it can see has a changed public `.olean`,
whether or not it uses what changed. `scripts/rebuild-affected.py` runs the same build but
compiles a module only if the change can affect it, and puts the previous output back otherwise.

```bash
lake exe cache get
python3 scripts/rebuild-affected.py            # once, before editing: learns what the outputs were built from
# edit, or check out another commit
python3 scripts/rebuild-affected.py            # takes the arguments of `lake build`
python3 scripts/rebuild-affected.py --check 50 # also compiles 50 of the reused modules again and compares
```

It is for finding out quickly whether a change breaks something, and for getting a tree to work
in. **It is not a verified build.** Lake accepts the outputs it leaves, so a later `lake build` has
nothing to do, but a reused output was not produced by compiling against the new imports. Use
plain `lake build`, or CI, when the result has to be trusted, and do not publish a cache from a
tree built this way.

Before the first module is compiled, Lake goes over all modules twice, which takes a few minutes
on this repository. For a change that `lake build` handles in a few minutes the script is
therefore slower.

It runs on Linux and macOS, with Python 3.9 or newer, and only with the toolchain it was checked
with (see `Limits`). It can be mixed with `lake build`: when something else than the script has
replaced outputs, the modules that are out of date at that moment are compiled without asking the
rule.

## What it decides

The script's docstring has the rule. In short, a module is compiled if its own inputs changed, or
if its previous output mentions a declaration that changed, was added or was removed, directly or
through a definition that can be unfolded to it. Changes that are not tied to a declaration are
handled by cases: instances, simp lemmas and `grind` patterns count for the constants in their
patterns, lemmas that Lean generates on demand such as `foo.eq_1` count for `foo`, a declaration
that appears, changes or goes away counts for the modules whose source could name it, and anything
the script does not know counts for every module that can see it. A module that sees other modules
than before is treated as if everything in them had been added or removed, provided the rest are
loaded in the same order.

The summary at the end says how many modules were compiled for which reason.

## How it was checked

`scripts/tests/test_rebuild_affected.py` compares it with `lake build` on a small project (needs
the toolchain): after each edit, both must give the same exit status and the same outputs.

For this repository, the rule was replayed over merged batches, using the outputs that CI
published for both ends of each batch. Nothing is built for this. For every module Lake compiled
again in a batch, the rule decides from the old outputs; a module it would reuse counts as a miss
if the output CI published afterwards differs from the old one.

| batch | compiled by Lake | of these edited or new | compiled by the rule | reused | misses | fewer by |
|---|---:|---:|---:|---:|---:|---:|
| b2 | 31,831 | 138 | 29,017 | 2,814 | 0 | 1.1x |
| b3 | 40,686 | 870 | 33,595 | 7,091 | 0 | 1.2x |
| b4 | 32,513 | 1,631 | 10,330 | 22,183 | 0 | 3.1x |
| b5 | 32,067 | 979 | 4,416 | 27,651 | 0 | 7.3x |
| b6 | 36,975 | 8,164 | 9,434 | 27,541 | 0 | 3.9x |
| b7 | 44,850 | 3,226 | 5,047 | 39,803 | 0 | 8.9x |
| b8 | 34,036 | 416 | 11,753 | 22,283 | 0 | 2.9x |
| b9 | 26,870 | 6,157 | 17,569 | 9,301 | 0 | 1.5x |
| b10 | 44,385 | 11,934 | 25,845 | 18,540 | 0 | 1.7x |
| b11 | 27,224 | 772 | 10,068 | 17,156 | 0 | 2.7x |
| b12 | 44,424 | 911 | 9,355 | 35,069 | 0 | 4.7x |
| b13 | 27,398 | 3,098 | 8,853 | 18,545 | 0 | 3.1x |
| b14 | 38,190 | 2,112 | 18,978 | 19,212 | 0 | 2.0x |
| b15 | 37,045 | 3,901 | 9,674 | 27,371 | 0 | 3.8x |
| b16 | 44,086 | 7,568 | 13,320 | 30,766 | 0 | 3.3x |
| b17 | 29,308 | 6,658 | 9,141 | 20,167 | 0 | 3.2x |
| b18 | 30,452 | 8,188 | 10,159 | 20,293 | 0 | 3.0x |
| b19 | 42,818 | 6,011 | 21,358 | 21,460 | 0 | 2.0x |
| b20 | 43,071 | 17,031 | 20,358 | 22,713 | 0 | 2.1x |
| all | 688,229 | 89,765 | 278,270 | 409,959 | 0 | 2.5x |

The rule was developed on b2 to b12: its cases are the kinds of miss found there. The later
batches were each replayed with the rule as it stood before it had seen them. In b13 to b16, 16 of
the 96,323 modules it reused came out different in CI's build, and in b17 to b19, 2 of 61,989.
They are of two kinds, and both are now cases of the rule (the table is with them):

- In 15, an imported module had dropped a declaration that the source of the module could have
  meant. Lean had tried that meaning and rejected it, and without it the output is the same except
  for the counters in generated variable names.
- In 3, an imported module no longer held a lemma that Lean generates on demand (`foo.eq_1`), and
  the module has a `simp [foo]` that had asked for the lemma without the proof naming `foo`.
  Compiling it again stores a copy of the lemma in the module.

Neither kind made a build fail or a proof wrong, but the outputs were not the ones `lake build`
produces. b20 was merged after the last change to the rule: none of the 22,713 modules it reuses
there came out different.

Two differences are not counted as misses, because two compilations of the same source also show
them: the order of the linter messages stored in an `.olean`, and the numbering of local variables
in the compiler's intermediate code.

## Limits

Lean does not record what the elaboration of a module read. The rule is built from what compiled
modules contain, and from the cases that turned up in the replay above. A dependency that leaves
no trace in the output and that none of the cases covers is missed, and then the reused output is
stale without any warning. `--check N` samples for that. Going by the batches the rule had not
seen (18 such modules in 158,312), new kinds of such dependencies should be expected now and then.

The script reads `.olean` files directly and depends on how Lean lays out several structures in
them. It refuses to run with a toolchain that is not listed in `CHECKED_TOOLCHAINS` in the script.
After a toolchain bump, those layouts have to be compared with the Lean source again and the
checks above repeated before the new toolchain is added there.

The script keeps the previous outputs of the modules a run compiles until the next run, so a run
needs that much free disk space.

Warnings of reused modules are not printed again.
