import LeanNLSemantics.FraCaS.Section1.Monotonicity.BlindEvalCore
import LeanNLSemantics

/-!
# TEMPORARY diagnostic (not part of the evaluation itself)

Two questions, answered from real CI output rather than guessed:

1. For each of the 8 remaining Sections 3-9 bare-theorem misses, which
   tactic in `attemptClose`'s chain fails, and with what error text?
   Plus a few candidate variants of the `aesop`/`grind` steps.
2. How does the shape-unrestricted generic scan fare over Sections 1-2
   (including the 20 bare theorems `BlindEval.lean`'s shape check skips)?

To be deleted once read.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Command
open FraCaS (Answer)
open FraCaS.Section1.Monotonicity (goalHeadConst runTacticOn)
open FraCaS.Section1.Monotonicity.BlindEval (attemptClose)

namespace FraCaS.BlindEvalDiagnostics

def targets : List Lean.Name :=
  [``FraCaS.Section3.fracas_123, ``FraCaS.Section3.fracas_126, ``FraCaS.Section3.fracas_127,
   ``FraCaS.Section3.fracas_129, ``FraCaS.Section4.fracas_173, ``FraCaS.Section6.fracas_246,
   ``FraCaS.Section6.fracas_248, ``FraCaS.Section7.fracas_307]

def showResult : Except String Unit → String
  | .ok () => "CLOSED"
  | .error msg => s!"failed: {msg}"

elab "#diag_misses" : command => liftTermElabM do
  let tacs : List (String × TSyntax `tactic) := [
    ("mono_nl", ← `(tactic| mono_nl)),
    ("aesop_full", ← `(tactic|
      aesop
        (add unfold FraCaS.Section1.Every, unfold FraCaS.Section1.Some,
          unfold FraCaS.Section1.No,
          safe apply FraCaS.Section1.entails_and, safe apply FraCaS.Section1.entails_refl,
          safe apply FraCaS.Section1.some_entails_and, safe apply FraCaS.Section1.entails_narrow,
          safe apply FraCaS.Section1.every_some, safe apply FraCaS.Section1.some_of_nonempty,
          safe apply FraCaS.Section1.every_trans, safe apply FraCaS.Section1.every_mp,
          safe apply FraCaS.Section1.no_iff_not_some, safe apply FraCaS.Section1.atLeast_some,
          safe apply FraCaS.Section1.most_some, safe apply FraCaS.Section1.some_mono_scope,
          safe apply FraCaS.Section1.every_mono_scope, safe apply FraCaS.Section1.atLeast_mono_scope,
          safe apply FraCaS.Section1.some_trans, safe apply FraCaS.Section1.most_trans,
          safe apply FraCaS.Section1.atMost_trans, safe apply FraCaS.Section1.atMost_mono_scope,
          safe apply FraCaS.Section1.atMost_mono_scope_conditioned,
          safe apply FraCaS.Section1.some_restrict, safe apply FraCaS.Section1.every_restrict,
          safe apply FraCaS.Section1.atLeast_restrict, safe apply FraCaS.Section1.atMost_restrict,
          safe apply FraCaS.Section2.exactly_ne, safe apply FraCaS.Section2.exactly_pos_not_no,
          safe apply FraCaS.Section2.some_of_exactly, safe apply FraCaS.Section2.exactly_atLeast,
          safe apply FraCaS.Section2.exactly_atMost, safe apply FraCaS.Section2.every_most))),
    ("aesop_unfold_only", ← `(tactic|
      aesop (add unfold FraCaS.Section1.Every, unfold FraCaS.Section1.Some,
        unfold FraCaS.Section1.No))),
    ("aesop_plain", ← `(tactic| aesop)),
    ("grind", ← `(tactic| grind)),
    ("grind_defs", ← `(tactic|
      grind [FraCaS.Section1.Every, FraCaS.Section1.Some, FraCaS.Section1.No])),
    ("simp_unfold_grind", ← `(tactic|
      (intros; simp only [FraCaS.Section1.Every, FraCaS.Section1.Some,
        FraCaS.Section1.No] at *; grind))),
    ("omega", ← `(tactic| (intros; omega)))
  ]
  for n in targets do
    let ty := (← getConstInfo n).type
    logInfo m!"diag {n} : {ty}"
    for (label, stx) in tacs do
      let r ← runTacticOn ty stx
      logInfo m!"diag {n} / {label}: {showResult r}"

-- Copies of `BlindEvalSections3to9.lean`'s `isNegHead`/`flipConclusion`/
-- scan loop, run over Sections 1-2 (that file has no `.olean` to import).
def isNegHead (headName : Option Lean.Name) : Bool :=
  headName == some ``Not || headName == some ``Ne

partial def flipConclusion (ty : Expr) : MetaM Expr := do
  if ty.isForall then
    forallBoundedTelescope ty (some 1) fun fvars body => do
      let body' ← flipConclusion body
      mkForallFVars fvars body'
  else
    match ty.getAppFn.constName? with
    | some ``Not => return ty.getAppArgs[0]!
    | some ``Ne =>
      let args := ty.getAppArgs
      mkEq args[args.size - 2]! args[args.size - 1]!
    | _ => mkAppM ``Not #[ty]

def bareProblemId (n : Lean.Name) : Option Nat :=
  let s := (toString n).splitOn "." |>.getLast!
  if "fracas_".isPrefixOf s then
    let rest := s.drop "fracas_".length
    if !rest.isEmpty && rest.all Char.isDigit then rest.toNat? else none
  else
    none

def answerToString : Answer → String
  | .yes => "yes"
  | .no => "no"
  | .unknown => "unknown"
  | .undef => "undef"

def runGeneric (namePrefix : Lean.Name) (label : String) : TermElabM Unit := do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    unless name.getPrefix == namePrefix do continue
    unless info.isTheorem do continue
    let some problemNum := bareProblemId name | continue
    let ty := info.type
    let result ←
      try
        let head ← goalHeadConst ty
        let isNeg := isNegHead head
        let closesAsWritten ← attemptClose ty
        let tyFlipped ← flipConclusion ty
        let closesFlipped ← attemptClose tyFlipped
        let hypClose := if isNeg then closesFlipped else closesAsWritten
        let notHypClose := if isNeg then closesAsWritten else closesFlipped
        pure (.ok (head, hypClose, notHypClose) : Except String (Option Lean.Name × Bool × Bool))
      catch e =>
        let msg ← try e.toMessageData.toString catch _ => pure "<unrenderable>"
        pure (.error msg)
    let gold := match FraCaS.problems.find? (·.id == problemNum) with
      | some p => answerToString p.answer
      | none => "none"
    match result with
    | .error msg => logInfo m!"{label} fracas_{problemNum} gold={gold} ERRORED {msg}"
    | .ok (head, hypClose, notHypClose) =>
      let decision :=
        if hypClose && !notHypClose then "yes"
        else if notHypClose && !hypClose then "no"
        else if !hypClose && !notHypClose then "unknown"
        else "contradiction"
      logInfo m!"{label} fracas_{problemNum} head={head} gold={gold} auto={decision}"

elab "#diag_generic_s12" : command => liftTermElabM do
  runGeneric `FraCaS.Section1 "diag_s1"
  runGeneric `FraCaS.Section2 "diag_s2"

end FraCaS.BlindEvalDiagnostics

#diag_misses
#diag_generic_s12
