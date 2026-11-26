#!/bin/bash
# Bring the result of a run onto a newer commit, without a new run.
#
# usage: onto.sh DIR REF TAG
#   DIR  absolute path of the tree a run of shake-pipeline.sh left (built), or that an earlier
#        onto.sh left
#   REF  what to fetch from `origin`, e.g. main
#   TAG  prefix of the log files in ~
# The commit is merged into the tree. Where both changed the import lines of a file, union.py
# merges the import block. Then build; a file that fails gets its imports made public and the
# imports of the commit back (repair.py), until the build passes. This keeps the tree compiling;
# it does not ask `lake shake` again and does not compare declarations, as a run does.
# Writes ~/TAG-onto.log (last line DONE) and ~/TAG.patch, a diff against the commit.
export PATH=$HOME/.elan/bin:$PATH
HERE=$(cd "$(dirname "$0")" && pwd)
DIR=$1; REF=$2; TAG=$3; L=~/$TAG-onto.log
G="git -c user.name=shake -c user.email=shake@localhost"
cd $DIR || exit 1
{ echo "START $(date -u +%FT%TZ) $DIR"
  $G checkout -q -B onto-$TAG && $G add -A src GUIDE.md && { git diff --cached --quiet || $G commit -q -m "result"; }
  git fetch -q origin "+$REF:refs/heads/new-$TAG" || { echo "FETCH FAILED"; echo DONE; exit 1; }
  echo "onto: $(git log --format='%H %cI %s' -1 new-$TAG | cut -c1-130)"
  echo "commits to merge: $(git rev-list --count HEAD..new-$TAG), src files they change: $(git diff --name-only HEAD...new-$TAG -- src | wc -l)"
  $G merge --no-commit --no-ff new-$TAG > ~/$TAG-onto-merge.log 2>&1; echo "merge: exit $?"
  bad=0
  for f in $(git diff --name-only --diff-filter=U); do
    python3 $HERE/union.py "$f" && git add "$f" || bad=1
  done
  [ $bad -eq 0 ] || { echo "CONFLICTS LEFT"; git merge --abort; echo DONE; exit 1; }
  $G commit -q --no-edit -m "merge" 2>/dev/null
  git diff --quiet new-$TAG -- src/Statements.lean Challenge.lean comparator.json && echo "challenge files as in the commit" || echo "PROBLEM: a challenge file differs"
  echo "outside src and GUIDE.md: $(git diff --name-only new-$TAG | grep -vc '^src/\|^GUIDE.md$') files differ from the commit"
  rm -f .shake-repair.json; r=1
  while :; do
    (time lake build) > ~/$TAG-onto-r$r.log 2>&1; e=$?
    echo "round $r: exit $e, built $(grep -cE '^(✔|⚠|ℹ) \[[0-9]+/[0-9]+\] Built ' ~/$TAG-onto-r$r.log), failed $(grep -cE '^✖ \[' ~/$TAG-onto-r$r.log), $(grep -E '^real' ~/$TAG-onto-r$r.log | tr '\t' ' ')"
    [ $e -eq 0 ] && break
    python3 $HERE/repair.py $DIR ~/$TAG-onto-r$r.log new-$TAG || { echo "STUCK"; echo DONE; exit 1; }
    r=$((r+1)); [ $r -gt 12 ] && { echo "TOO MANY ROUNDS"; echo DONE; exit 1; }
  done
  $G add -A src GUIDE.md && { git diff --cached --quiet || $G commit -q -m "repairs"; }
  echo "sorry warnings: $(grep -c 'declaration uses `sorry`' ~/$TAG-onto-r$r.log)"
  lake env lean scripts/PrintAxioms.lean 2>&1 | cut -c1-160
  echo "differs from the commit: $(git diff --shortstat new-$TAG -- src GUIDE.md)"
  echo "changed lines in src that are not import lines: $(git diff -U0 new-$TAG -- src | grep -E '^[+-]' | grep -vE '^(\+\+\+|---)' | grep -vcE '^[+-](public )?import ')"
  echo "after: $(python3 $HERE/modgraph.py src | tr '\n' ' ')"
  git diff new-$TAG -- src GUIDE.md > ~/$TAG.patch; echo "patch: $(wc -c < ~/$TAG.patch) bytes, base $(git rev-parse new-$TAG)"
  echo "END $(date -u +%FT%TZ)"; echo DONE; } > $L 2>&1
