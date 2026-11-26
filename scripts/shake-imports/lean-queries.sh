#!/bin/bash
# Two questions put to Lean about a built tree of the project.
#
#   lean-queries.sh attrs DIR OUT
#       The files of the project that give an instance, simp or reducibility attribute to a
#       declaration of another file, with a command that reaches their importers. One line per
#       attribute: module, kind, declaration, module of the declaration.
#   lean-queries.sh decls DIR OUT
#       Every declaration of the project: module, name, kind, hash of its type, hash of its value,
#       sorted. The numbering of auxiliary proofs, matchers and simp lemmas is left out of the
#       hashes, so two trees that differ only in import lines must give the same lines for the
#       declarations that are written in the sources.
#   lean-queries.sh declsStrict DIR OUT
#       The same with the numbering of matchers kept in the hashes.
export PATH=$HOME/.elan/bin:$PATH
WHAT=$1; DIR=$2; OUT=$3
cd $DIR || exit 1
T=$(mktemp -d)
(cd src && find . -name '*.lean' | sed 's|^\./||; s|\.lean$||; s|/|.|g' | sort | sed 's/^/import /') > $T/Q.lean
cat >> $T/Q.lean <<'LEAN'
namespace ShakeQueries
open Lean Meta

def proj (m : Name) : Bool := m.getRoot == `Lib || m.getRoot == `New || m == `Main || m == `Statements

def normStr (matchers : Bool) (s : String) : String :=
  if s.startsWith "_proof_" then "_proof" else if s.startsWith "_simp_" then "_simp"
  else if matchers && s.startsWith "match_" then "match" else s

def normName (matchers : Bool) : Name → Name
  | .str p s => .str (normName matchers p) (normStr matchers s)
  | .num p n => .num (normName matchers p) n
  | .anonymous => .anonymous

def normExpr (matchers : Bool) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => let n' := normName matchers n; if n' == n then none else some (.const n' ls)
    | _ => none

def attrs : CoreM (Array String) := do
  let env ← getEnv
  let names := env.header.moduleNames
  let home (n : Name) : String := match env.getModuleIdxFor? n with
    | some j => toString names[j.toNat]! | none => "?"
  let mut out : Array String := #[]
  for h : i in [0:names.size] do
    let m := names[i]
    if proj m then
      for e in instanceExtension.ext.getModuleEntries env i do
        if let .global a := e then
          if let some n := a.globalName? then
            if (env.getModuleIdxFor? n).isSome && env.getModuleIdxFor? n != some i then
              out := out.push s!"{m}\tinstance {a.priority}\t{n}\t{home n}"
      for e in simpExtension.ext.getModuleEntries env i do
        if let .global a := e then
          match a with
          | .thm t =>
            if let .decl n _ inv := t.origin then
              if (env.getModuleIdxFor? n).isSome && env.getModuleIdxFor? n != some i then
                out := out.push s!"{m}\tsimp{if inv then " ←" else ""}\t{n}\t{home n}"
          | .toUnfold n =>
            if (env.getModuleIdxFor? n).isSome && env.getModuleIdxFor? n != some i then
              out := out.push s!"{m}\tsimp unfold\t{n}\t{home n}"
          | _ => pure ()
      for e in reducibilityExtraExt.ext.getModuleEntries env i do
        if let .global (n, _) := e then
          out := out.push s!"{m}\treducibility\t{n}\t{home n}"
  return out

def declsWith (matchers : Bool) : CoreM (Array String) := do
  let env ← getEnv
  let names := env.header.moduleNames
  let mut out : Array String := #[]
  for h : i in [0:names.size] do
    let m := names[i]
    if proj m then
      for ci in env.header.moduleData[i]!.constants do
        let kind : String := match ci with
          | ConstantInfo.thmInfo _ => "thm" | ConstantInfo.defnInfo _ => "def"
          | ConstantInfo.axiomInfo _ => "axiom" | ConstantInfo.opaqueInfo _ => "opaque"
          | ConstantInfo.inductInfo _ => "ind" | ConstantInfo.ctorInfo _ => "ctor"
          | ConstantInfo.recInfo _ => "rec" | ConstantInfo.quotInfo _ => "quot"
        let v : String := match ci.value? (allowOpaque := true) with
          | some e => toString (normExpr matchers e).hash | none => "-"
        out := out.push s!"{m}\t{ci.name}\t{kind}\t{(normExpr matchers ci.type).hash}\t{v}"
  return out.qsort (· < ·)

def decls : CoreM (Array String) := declsWith true

/-- As `decls`, but the numbering of matchers is kept in the hashes. -/
def declsStrict : CoreM (Array String) := declsWith false

end ShakeQueries

open Lean in
run_cmd do
  let out ← Elab.Command.liftCoreM ShakeQueries.WHAT
  IO.FS.writeFile "QUERY_OUT" (String.intercalate "\n" out.toList ++ "\n")
LEAN
sed -i "s|QUERY_OUT|$T/out.tsv|; s|ShakeQueries.WHAT|ShakeQueries.$WHAT|" $T/Q.lean
lake env lean $T/Q.lean > $T/log 2>&1; E=$?
head -8 $T/log
[ -f $T/out.tsv ] && cp $T/out.tsv $OUT
rm -rf $T
exit $E
