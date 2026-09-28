import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Existential
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Compose
import LeanNLSemantics.FraCaS.Data.Problems
import LeanNLSemantics

/-!
# Blind evaluation (Section 1 pilot)

Every `fracas_NNN` theorem so far (`Batch1.lean`-`Batch5.lean`) is
*hand-proved*: whoever wrote `theorem fracas_002 : Every P Q → Some P R
→ Some P Q := every_some ...` already knew, from FraCaS's own gold
answer, that this direction is the one that holds - the theorem's own
statement bakes in a decision no automated procedure made. That's the
concern the "self-serving?" review of the axiom audit (`AssumptionAudit
.lean`) raised for axioms; the equivalent concern here is whether the
338/342 headline figure reflects real automated entailment-checking or
just a human confirming, problem by problem, a proof they already knew
existed.

This file is a first, honest attempt at closing that gap, scoped to
Section 1 only (Section 2 and beyond are staged separately - see this
file's own validation-status table as it grows). For every **bare**
`fracas_NNN` theorem in `FraCaS.Section1` (no `_dir1`/`_via_mono_nl`/...
suffix - those exist for the coverage scan's own diversity or for the
countermodel-pair method the `.undef` problems and several others use,
and are not single entailment-shaped statements this procedure could
even pose a yes/no question about; skipped rather than forced), this
file:

1. Takes the theorem's own **type** only, never its hand-written proof
   term - the type is the translated Prop (premises and hypothesis, both
   necessarily a human translation choice, same as any NLI system's
   parsing step), but which *direction* of it is provable is then
   decided by automated tactics alone, not by the proof that already sits
   there.
2. Attempts to automatically close that type directly (**pos**: does
   `premises → hypothesis` hold?) and, separately, the type with its
   final conclusion negated (**neg**: does `premises → ¬hypothesis`
   hold?), via the same fixed tactic chain both times - `mono_nl`,
   `exist_nl`, `mono_nl_compose` (this corpus's own certified fragment,
   `Tactic.lean`/`Existential.lean`/`Compose.lean`), then one `aesop` call
   armed with every general `GQ.lean` lemma and told to unfold `Every`/
   `Some`/`No` (plain `def`s it can't see through on its own -
   `Most`/`AtLeast`/`AtMost`/`Exactly` are already-transparent `abbrev`s;
   see `attemptClose`'s own comment for why the whole list, not a
   hand-picked subset), then `grind`.
3. Turns (pos succeeds, neg fails) into **yes**, (neg succeeds, pos
   fails) into **no**, (neither succeeds) into **unknown**, and (both
   succeed) into a flagged **contradiction** - that last case would mean
   the premises are jointly unsatisfiable under this translation, or one
   of these tactics unsoundly closed a goal it shouldn't have; either way
   it is reported, never silently absorbed into "yes" or "no".
4. Compares that automated decision against `FraCaS.problems`' own gold
   `Answer` (`.yes`/`.no` compared directly; `.unknown` and `.undef` both
   compared against automated `unknown`, since a binary yes/no/unknown
   procedure has no way to tell "genuinely undecided" apart from "the
   source's answer wasn't a literal yes/no/don't-know" - collapsing that
   distinction here rather than claiming a resolution this procedure
   cannot make).

Deliberately not imported by anything (imports the root `LeanNLSemantics`
umbrella to see every already-proved theorem, so importing it back would
be circular) - run directly, the same way `Coverage.lean` already is.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Command
open FraCaS (Answer)

namespace FraCaS.Section1.Monotonicity.BlindEval

def lastComponent (n : Lean.Name) : String :=
  (toString n).splitOn "." |>.getLast!

/-- The FraCaS problem number a **bare** `fracas_NNN` name names - `none`
for anything with a trailing suffix (`_dir1`, `_via_mono_nl`, ...), which
this scan deliberately excludes (see this file's header). -/
def bareProblemId (n : Lean.Name) : Option Nat :=
  let s := lastComponent n
  if "fracas_".isPrefixOf s then
    let rest := s.drop "fracas_".length
    if !rest.isEmpty && rest.all Char.isDigit then rest.toNat? else none
  else
    none

/-- The two-predicate quantifier heads this corpus states entailment
problems with - wider than `Tactic.lean`'s own `quantifierHeads` (which
is deliberately narrowed to what `mono_nl` itself can close: no `No`/
`Most`/`Exactly`), since this check only decides whether a theorem's
*shape* poses a yes/no entailment question at all, not whether any one
tactic can answer it. -/
def blindEvalHeads : List Lean.Name :=
  [``FraCaS.Section1.Every, ``FraCaS.Section1.Some, ``FraCaS.Section1.No,
   ``FraCaS.Section1.Most, ``FraCaS.Section1.AtLeast, ``FraCaS.Section1.AtMost]

/-- Whether a theorem's conclusion, after introducing its implication
chain, is headed by one of `blindEvalHeads` - reuses `introAll` from
`Tactic.lean` (raw, non-`whnf` Pi-check; see its own comment for why)
rather than a second, possibly-inconsistent traversal. -/
def isEntailmentShaped (ty : Expr) : MetaM Bool := do
  let mvar ← mkFreshExprMVar ty (kind := .synthetic)
  let (_, goal) ← introAll mvar.mvarId!
  goal.withContext do
    match (← goal.getType).getAppFn.constName? with
    | some n => return blindEvalHeads.contains n
    | none => return false

/-- Rebuilds `ty`'s Pi-telescope with its final (non-Pi) body wrapped in
`Not` - the "neg" goal's type. Recurses one binder at a time via
`forallBoundedTelescope`, exactly mirroring `introAll`'s own recursive
descent (including the same "no `whnf`" reasoning: a `Every`/`Some`/`No`-
headed body is an application, never itself an `Expr.forallE`, so this
correctly stops there without unfolding through it). -/
partial def negateConclusion (ty : Expr) : MetaM Expr := do
  if ty.isForall then
    forallBoundedTelescope ty (some 1) fun fvars body => do
      let body' ← negateConclusion body
      mkForallFVars fvars body'
  else
    mkAppM ``Not #[ty]

/-- Attempts one tactic against a *fresh* metavariable of type `ty`,
discarding any partial assignment on failure (fresh per attempt, exactly
`Coverage.lean`'s own `runTactic` pattern) - `true` iff it fully closed
the goal. -/
def runTactic (ty : Expr) (tacticStx : Lean.TSyntax `tactic) : TermElabM Bool := do
  try
    let mvar ← mkFreshExprMVar ty (kind := .synthetic)
    let remaining ← Lean.Elab.Tactic.run mvar.mvarId! do
      Lean.Elab.Tactic.evalTactic tacticStx
    return remaining.isEmpty
  catch _ =>
    return false

/-- The `aesop` call below is armed with every general (not
problem-specific) composition/entailment lemma `GQ.lean` already has
(`entails_and` through `atMost_restrict`) - the complete list, not a
hand-picked subset chosen to close any one problem. `most_trans` is in
there for exactly the reason it needs to be: it is what `fracas_026`'s
own hand proof already calls, a previously-proved general fact about
`Most`, not a rule invented for this file - handing the *entire* list to
a generic search is what keeps this from being "one rule added because
problem 26 needed it" (see this file's header for why that distinction
matters to the whole methodology). `mono_nl`/`exist_nl`/`mono_nl_compose`
already encode most of these as a directed, certified search; this is
the same knowledge, given instead to an undirected one, for the goals
(`Most`/`No`-headed) that certified search was never scoped to touch.

The fixed tactic chain both directions get, in order: this corpus's
own certified monotonicity fragment first (`mono_nl`, `exist_nl`,
`mono_nl_compose`), then one `aesop` call - unfolding the plain-`def`
quantifiers (`Every`/`Some`/`No`) it can't see through on its own, and
armed with every general GQ.lean lemma above - then `grind` as a last
resort. Stops at the first success. -/
def attemptClose (ty : Expr) : TermElabM Bool := do
  if ← runTactic ty (← `(tactic| mono_nl)) then return true
  if ← runTactic ty (← `(tactic| exist_nl)) then return true
  if ← runTactic ty (← `(tactic| mono_nl_compose)) then return true
  if ← runTactic ty (← `(tactic|
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
          safe apply FraCaS.Section1.atLeast_restrict, safe apply FraCaS.Section1.atMost_restrict)))
  then return true
  if ← runTactic ty (← `(tactic| grind)) then return true
  return false

/-- `Answer.yes`/`.no` compared directly; `.unknown` and `.undef` both
match an automated `"unknown"` verdict - see this file's header for why
those two gold cases aren't distinguished here. -/
def answerMatches (gold : Answer) (decision : String) : Bool :=
  match gold, decision with
  | .yes, "yes" => true
  | .no, "no" => true
  | .unknown, "unknown" => true
  | .undef, "unknown" => true
  | _, _ => false

/-- `Answer` has no `ToMessageData` instance (only `Repr`/`DecidableEq`),
so mismatches are logged against this plain string, not the value
itself. -/
def answerToString : Answer → String
  | .yes => "yes"
  | .no => "no"
  | .unknown => "unknown"
  | .undef => "undef"

elab "#blind_eval_section1" : command => liftTermElabM do
  let env ← getEnv
  let mut skippedNotBare : Nat := 0
  let mut skippedNotEntailmentShaped : Array Lean.Name := #[]
  let mut matched : Array (Nat × String) := #[]
  let mut mismatches : Array (Nat × String × String) := #[]
  let mut contradictions : Array Nat := #[]
  let mut noGoldEntry : Array Nat := #[]

  for (name, info) in env.constants.toList do
    unless name.getPrefix == `FraCaS.Section1 do continue
    unless info.isTheorem do continue
    let some problemNum := bareProblemId name | do
      unless (lastComponent name).startsWith "fracas_" do continue
      skippedNotBare := skippedNotBare + 1
      continue

    let ty := info.type
    let shaped ← try isEntailmentShaped ty catch _ => pure false
    unless shaped do
      skippedNotEntailmentShaped := skippedNotEntailmentShaped.push name
      continue

    logInfo m!"blind_eval_section1: attempting fracas_{problemNum}"
    let posOk ← attemptClose ty
    let tyNeg ← negateConclusion ty
    let negOk ← attemptClose tyNeg

    let decision :=
      if posOk && !negOk then "yes"
      else if negOk && !posOk then "no"
      else if !posOk && !negOk then "unknown"
      else "contradiction"

    if decision == "contradiction" then
      contradictions := contradictions.push problemNum
      continue

    match FraCaS.problems.find? (·.id == problemNum) with
    | none => noGoldEntry := noGoldEntry.push problemNum
    | some problem =>
      if answerMatches problem.answer decision then
        matched := matched.push (problemNum, decision)
      else
        mismatches := mismatches.push (problemNum, answerToString problem.answer, decision)

  let total := matched.size + mismatches.size + contradictions.size + noGoldEntry.size
  logInfo m!"blind_eval_section1: {matched.size}/{total} automated verdicts match gold \
    ({skippedNotBare} skipped as suffixed/non-bare, \
    {skippedNotEntailmentShaped.size} skipped as not entailment-shaped, \
    {contradictions.size} contradictions, {noGoldEntry.size} with no gold entry)"
  logInfo m!"matched [{matched.size}]: {matched.toList}"
  logInfo m!"mismatches [{mismatches.size}]: {mismatches.toList}"
  logInfo m!"contradictions (both directions closed - flag, do not silently resolve) \
    [{contradictions.size}]: {contradictions.toList}"
  logInfo m!"no gold entry [{noGoldEntry.size}]: {noGoldEntry.toList}"
  logInfo m!"skipped, not entailment-shaped [{skippedNotEntailmentShaped.size}]: \
    {skippedNotEntailmentShaped.toList}"

end FraCaS.Section1.Monotonicity.BlindEval

#blind_eval_section1
