#!/bin/bash
# Minimize the imports of the project with `lake shake`, make the result build, and check that no
# declaration changed.
#
# usage: [RECHECK=0] shake-pipeline.sh DIR ORIG_REV TAG [PHASE] [SEED_SRC]
#   DIR       absolute path of a checkout of ORIG_REV with a finished `lake build`
#   ORIG_REV  the git revision the checkout started from
#   TAG       prefix of the log files in ~
#   PHASE     start at: shake (default) | loop | settle | recheck | final
#   SEED_SRC  src directory of an earlier result: its `-- shake: keep` marks are carried over
#   RECHECK=0 skips the phase that decides every mark once more
# Needs the other scripts of this directory next to it. Writes ~/TAG-pipeline.log (last line DONE)
# and ~/TAG.patch.
export PATH=$HOME/.elan/bin:$PATH
HERE=$(cd "$(dirname "$0")" && pwd)
DIR=$1; ORIG=$2; TAG=$3; PHASE=${4:-shake}; SEED=$5; L=~/$TAG-pipeline.log
cd $DIR || exit 1
mods() { (cd src && find . -name '*.lean' | sed 's|^\./||; s|\.lean$||; s|/|.|g' | sort | tr '\n' ' '); }
say() { echo "$(date -u +%T) $*" >> $L; }
fail() { say "$*"; echo DONE >> $L; exit 1; }

# build, and while files fail: repair their imports and build again
loop() {
  local name=$1 r=1
  rm -f .shake-repair.json
  while :; do
    (time lake build) > ~/$TAG-$name-r$r.log 2>&1; local e=$?
    say "$name round $r: exit $e, built $(grep -cE '^(✔|⚠|ℹ) \[[0-9]+/[0-9]+\] Built ' ~/$TAG-$name-r$r.log), failed $(grep -cE '^✖ \[' ~/$TAG-$name-r$r.log), $(grep -E '^real' ~/$TAG-$name-r$r.log | tr '\t' ' ')"
    [ $e -eq 0 ] && return 0
    python3 $HERE/repair.py $DIR ~/$TAG-$name-r$r.log $ORIG >> $L 2>&1 || { say "STUCK in $name round $r"; return 1; }
    r=$((r+1)); [ $r -gt 40 ] && { say "TOO MANY ROUNDS"; return 1; }
  done
}

# `lake shake` on the built tree; try what it still proposes; build; repeat until it proposes nothing
# (it always proposes to make Statements import Lib.Speed, which is not done)
settle() {
  local name=$1 force=$2 pass n only
  for pass in 1 2 3 4 5 6 7 8; do
    lake shake $force --add-public-downstream Lib.Speed $(mods) > ~/$TAG-$name-dry$pass.log 2>&1; force=
    grep -q '^error' ~/$TAG-$name-dry$pass.log && { say "lake shake failed: $(grep -m1 '^error' ~/$TAG-$name-dry$pass.log | cut -c1-200)"; return 1; }
    n=$(grep -c "^$DIR/src/.*\.lean:$" ~/$TAG-$name-dry$pass.log)
    only=$(grep "^$DIR/src/.*\.lean:$" ~/$TAG-$name-dry$pass.log | grep -vc "/src/Statements.lean:$")
    say "$name pass $pass: lake shake proposes changes in $n files ($only besides Statements)"
    [ $only -eq 0 ] && { say "FIXED POINT"; return 0; }
    python3 $HERE/refine.py $DIR ~/$TAG-$name-dry$pass.log --jobs 12 --skip Statements > ~/$TAG-$name-refine$pass.log 2>&1
    say "refine: $(tail -1 ~/$TAG-$name-refine$pass.log)"
    loop $name-b$pass || return 1
  done
  say "NO FIXED POINT after 8 passes"; return 1
}

if [ $PHASE = shake ]; then
  say "START $DIR at $(git rev-parse --short HEAD), original $ORIG = $(git rev-parse --short $ORIG)"
  echo "before: $(python3 $HERE/modgraph.py src | tr '\n' ' ')" >> $L
  # what the tree is before the change: every declaration, and the files whose attributes reach importers
  $HERE/lean-queries.sh decls $DIR ~/$TAG-decls-before.tsv >> $L 2>&1 || fail "could not list the declarations"
  $HERE/lean-queries.sh declsStrict $DIR ~/$TAG-decls-before-strict.tsv >> $L 2>&1
  $HERE/lean-queries.sh attrs $DIR ~/$TAG-attrs.tsv >> $L 2>&1 || fail "could not list the attributes"
  say "files that give attributes to declarations of other files: $(cut -f1 ~/$TAG-attrs.tsv | sort -u | tr '\n' ' ')"
  rm -rf ~/$TAG-before-src && mkdir ~/$TAG-before-src && git archive $ORIG src | tar -x -C ~/$TAG-before-src
  python3 $HERE/docs.py $DIR >> $L 2>&1 || fail "could not edit the documentation"
  [ -n "$SEED" ] && say "$(python3 $HERE/seed.py $SEED src)"
  # Mathlib stays imported as a whole, through Lib.Speed. Mathlib imports Aesop only at the meta phase,
  # so without the second line `lake shake` adds an Aesop import to every file that calls `aesop`.
  python3 $HERE/speed.py src/Lib/Speed.lean >> $L 2>&1 || fail "could not annotate Lib.Speed"
  lake shake --force --add-public-downstream Lib.Speed --fix $(mods) > ~/$TAG-shake-fix.log 2>&1
  say "shake --fix: exit $?, $(tail -1 ~/$TAG-shake-fix.log)"
  git checkout -q $ORIG -- src/Statements.lean
  say "$(python3 $HERE/sortimports.py $(git diff --name-only $ORIG -- src | grep '\.lean$'))"
  say "changed: $(git diff --shortstat $ORIG -- src)"
  PHASE=loop
fi

if [ $PHASE = loop ]; then
  loop first || fail "first loop failed"
  PHASE=settle
fi

if [ $PHASE = settle ]; then
  settle settle || fail "settle failed"
  PHASE=recheck
fi

# every mark is decided once more, from what `lake shake` proposes without it
if [ $PHASE = recheck ]; then
  if [ "${RECHECK:-1}" = 1 ]; then
    say "recheck: $(python3 $HERE/refine.py $DIR --unmark)"
    settle recheck --force || fail "recheck failed"
  fi
  PHASE=final
fi

# No declaration may differ from the tree before. Where one does, the file has lost sight of a file
# that sets attributes on declarations of other files; it gets that file back, marked.
: > ~/$TAG-added.txt
for round in 1 2 3; do
  $HERE/lean-queries.sh decls $DIR ~/$TAG-decls-after.tsv >> $L 2>&1 || fail "could not list the declarations"
  python3 $HERE/same.py ~/$TAG-decls-before.tsv ~/$TAG-decls-after.tsv --modules-out ~/$TAG-differing.txt >> $L 2>&1 && break
  [ $round -eq 3 ] && fail "declarations still differ"
  python3 $HERE/fixattrs.py add src ~/$TAG-before-src/src ~/$TAG-attrs.tsv ~/$TAG-differing.txt ~/$TAG-added.txt >> $L 2>&1 || fail "a declaration differs for a reason that is not handled"
  loop same$round || fail "loop after fixattrs failed"
  settle same$round || fail "settle after fixattrs failed"
done
# an import added for this stays only if a declaration differs without it
if [ -s ~/$TAG-added.txt ]; then
  while IFS=$'\t' read -r F X <&3; do
    python3 $HERE/fixattrs.py drop src $F $X
    if lake build > ~/$TAG-min.log 2>&1 && $HERE/lean-queries.sh decls $DIR ~/$TAG-decls-try.tsv > /dev/null 2>&1 \
        && python3 $HERE/same.py ~/$TAG-decls-before.tsv ~/$TAG-decls-try.tsv > /dev/null 2>&1; then
      say "not needed: import $X in $F"
    else
      python3 $HERE/fixattrs.py put src $F $X; say "needed: import $X in $F"
    fi
  done 3< ~/$TAG-added.txt
  loop min || fail "loop after minimizing failed"
  settle min || fail "settle after minimizing failed"
  $HERE/lean-queries.sh decls $DIR ~/$TAG-decls-after.tsv >> $L 2>&1 || fail "could not list the declarations"
  python3 $HERE/same.py ~/$TAG-decls-before.tsv ~/$TAG-decls-after.tsv >> $L 2>&1 || fail "declarations differ after minimizing"
fi

lake build --no-build > /dev/null 2>&1; say "lake build --no-build: exit $?"
say "final: $(git diff --shortstat $ORIG -- src GUIDE.md)"
say "marked imports: $(grep -rhE '^(public )?import .* -- shake: keep$' src --include='*.lean' | wc -l) in $(grep -rlE '^(public )?import .* -- shake: keep$' src --include='*.lean' | wc -l) files"
say "changed lines in src that are not import lines:"
git diff -U0 $ORIG -- src | grep -E '^[+-]' | grep -vE '^(\+\+\+|---)' | grep -vE '^[+-](public )?import ' | cut -c1-160 >> $L
git diff --quiet $ORIG -- src/Statements.lean Challenge.lean comparator.json && say "Statements.lean, Challenge.lean and comparator.json are unchanged" || say "PROBLEM: a challenge file changed"
# scripts/tauceti-cache-get.py recognizes an import of a Tau Ceti module only if nothing follows the module name
say "Tau Ceti import lines with trailing text: $(grep -rhE '^(public )?import TauCeti' src --include='*.lean' | grep -vcE '^(public )?import TauCeti[A-Za-z0-9_.]*$')"
echo "after: $(python3 $HERE/modgraph.py src | tr '\n' ' ')" >> $L
python3 $HERE/same.py ~/$TAG-decls-before.tsv ~/$TAG-decls-after.tsv > /dev/null 2>&1; say "same declarations: exit $?"
$HERE/lean-queries.sh declsStrict $DIR ~/$TAG-decls-after-strict.tsv >> $L 2>&1
python3 $HERE/same.py ~/$TAG-decls-before-strict.tsv ~/$TAG-decls-after-strict.tsv > ~/$TAG-strict.txt 2>&1; say "same declarations with the numbering of matchers compared too: exit $? ($(sed -n 2p ~/$TAG-strict.txt))"
$HERE/lean-queries.sh attrs $DIR ~/$TAG-attrs-after.tsv >> $L 2>&1; cmp -s ~/$TAG-attrs.tsv ~/$TAG-attrs-after.tsv && say "same attributes on declarations of other files" || say "PROBLEM: attributes differ"
lake env lean scripts/PrintAxioms.lean >> $L 2>&1
git diff $ORIG -- src GUIDE.md > ~/$TAG.patch; say "patch: $(wc -c < ~/$TAG.patch) bytes, base $(git rev-parse $ORIG)"
echo DONE >> $L
