# Checks of `scripts/rebuild-affected.py`

These scripts produced the numbers in `scripts/REBUILD-AFFECTED.md` and in the pull request that
adds `scripts/rebuild-affected.py`. They are not needed to use that script. All of them import the
script itself (from the directory above), so they test the code that ships: the rule, the
comparison of two compiled modules and the reader of `.olean` files.

## Replay over merged batches

CI publishes, for every tree it builds, the outputs of every module (`.ltar` bundles) and a
manifest with the Lake input hash each module was compiled with. For two consecutive trees that
tells which modules Lake compiled again and which of them came out different. The replay asks the
script's rule, module by module and using only the older outputs, whether it would have compiled
the module, and counts a miss whenever it would have reused an output that CI's build shows to
have changed.

```bash
# from the repository root, with the commits a28ad7ec8b..91b2735308 present
R=scripts/rebuild-affected-replay
python3 $R/fetch_meta.py META                                   # receipts and manifests, about 90 MB
python3 $R/batch_extract.py META HIST 40 $(seq 1 19)            # about 440,000 bundles; keeps 115 GB; two and a half hours
for k in $(seq 1 19); do python3 $R/batch_replay.py META HIST . $k; done   # 10 to 25 minutes and 5 GB of memory each
cat HIST/replay-b*-visible-deep.json > results && python3 $R/replay_table.py results
```

`batch_replay.py` explains what it models. Batch `k` is the step from commit `k-1` to commit `k` of
the list in `fetch_meta.py`: 1 is b2, 19 is b20. `results/` has the result files of the run the
table in the document was made from.

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

In b10 and b13 together, 24 reused modules differ from CI's output only in the order of stored
linter messages, which two compilations of the same source also do; they are not counted.

### What the batches the rule had not seen showed

The rule's cases were found on b2 to b12, so it has no misses there. The later batches were first
replayed with the rule as it stood before it had seen them (`results/unseen-b13-b16/` and
`results/unseen-b17-b19/`):

| batch | compiled by Lake | of these edited or new | compiled by the rule | reused | misses | fewer by |
|---|---:|---:|---:|---:|---:|---:|
| b13 | 27,398 | 3,098 | 8,701 | 18,697 | 1 | 3.1x |
| b14 | 38,190 | 2,112 | 18,967 | 19,223 | 1 | 2.0x |
| b15 | 37,045 | 3,901 | 9,615 | 27,430 | 5 | 3.9x |
| b16 | 44,086 | 7,568 | 13,113 | 30,973 | 9 | 3.4x |
| b17 | 29,308 | 6,658 | 9,122 | 20,186 | 0 | 3.2x |
| b18 | 30,452 | 8,188 | 10,154 | 20,298 | 0 | 3.0x |
| b19 | 42,818 | 6,011 | 21,313 | 21,505 | 2 | 2.0x |
| all | 249,297 | 37,536 | 90,985 | 158,312 | 18 | 2.7x |

Fifteen of the eighteen misses, all in b13 to b16, have one cause, found with `token_miss.py` and
`diff_const.py`. A module the missed module sees had dropped a declaration, and every component of
that declaration's name is a word of the missed module's source: the source could have meant it,
through an `open` or the namespace it is in. Lean had tried that meaning and rejected it. Without
it the module elaborates along a slightly different path. In all fifteen, CI's two outputs are
then the same except for the counters in generated variable names, such as
`x._@.Mod.123._hygCtx._hyg.153` against `…_hyg.126` (`hyg_only.py` checks this). Nothing in the old
output points at the dropped declaration. The rule now compiles a module when a declaration is
removed or changed and every component of its name is a word of the module's source.

The other three (one in b14, two in b19) are about lemmas that Lean generates the first time
something asks for them. In b14, an edited module used to hold
`Formalism.IndefR.Cx.CxData.wC.eq_1` and no longer does. The missed module has a `simp` call that
names `wC`, and so asks for that lemma, but the proof it gets names neither the lemma nor `wC`.
CI's build therefore stored a copy of the lemma in the missed module, and the reused output has
none. That is harmless in itself: a module that needs such a lemma and does not see one generates
it, and Lean accepts the same lemma in two modules that a third imports. But it is not the output
of `lake build`. `who_had.py` shows where a lemma was before and after. The rule now compiles a
module when a module it sees drops such a lemma of a declaration and every component of the
declaration's name is a word of the module's source. `fuzz_toy.py` has this situation (its module
`O`), and the version of the script without the case fails there.

The table further up is with both cases. So the seven batches b13 to b19 showed two kinds of
dependency the rule lacked, in 158,312 reused modules. More should be expected. b20 was merged
after the last change to the rule, so it is the one batch in the table that the rule in the table
had not seen: none of the 22,713 modules it reuses there came out different.

## Random edits on a small project

`fuzz_toy.py SEED STEPS` makes two copies of a fourteen-module project and applies the same random
edits to both. One copy is built with `lake build`, the other with the script, and after every
build the exit codes and all outputs must agree. In between it builds single targets, runs plain
`lake build` in the script's copy and makes edits that do not compile.

The script passes 17 seeds of 150 steps each: 1,909 builds compared, 604 of them failing ones, in
which it compiled 9,869 modules and reused 3,198. The version of the script from before
these checks fails on each of the four seeds it was given, within 20 steps; the present one passes
the same seeds. That version lacked the two cases of the rule described above and had three
mistakes, which reading the code had turned up shortly before: it did not log, for an edited
module, the definitions that the module left alone but that unfold to something changed elsewhere;
it trusted its record of a source after plain `lake build` had replaced outputs; and after a run
that stopped early it worked out what a module had seen before from headers that had changed
since. `scripts/tests/test_rebuild_affected.py` has a test for each.

## Comparing trees that were really built

- `cmp_ci.py META HIST .lake/build K` compares a build directory with the outputs CI published for
  the newer tree of batch `K`, for the modules Lake compiled again in that batch.
- `cmp_run.py HIST K RUN_JSONL` compares what the script did in such a build
  (`.lake/rebuild-affected/run.jsonl`) with what the replay of batch `K` says it does.
- `tree_manifest.py BUILD_DIR OUT` fingerprints every module of a build directory, and
  `cmp_manifest.py A B` compares two such files. This is how a tree built by the script was compared
  with one built by `lake build` from the same sources.

## Looking at a miss

`classify_miss.py META K MODULE...` says in which parts and extensions CI's two outputs of a module
differ, `diff_const.py META K MODULE` which names occur in only one version of a changed private
constant, `why_miss.py META HIST K MODULE` which changes the modules it sees logged, and
`token_miss.py META HIST K` which removed or changed declarations the sources of the misses of a
replay could have meant.
