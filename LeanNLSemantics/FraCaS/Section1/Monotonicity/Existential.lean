import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics.FraCaS.Section2.Plurals

/-!
# `exist_nl`: existential-import / quantifier-strength (Category B)

**Validation status**: not yet through CI - see `Tactic.lean`'s header
for this sandbox's standing toolchain constraint. Every API this file
uses is one Phase 1/2 already confirmed working (`introAll`, `extractPQ`,
`extractN`, `nameOf`, `liftMetaTactic1`, `Lean.Elab.Tactic.run` +
`evalTactic`) except `mkFreshExprMVar none` (a metavariable with no type
yet, only assigned later by unification inside `mkAppM`) and `decide` as
the discharged tactic for a numeral side-condition - both new, both
isolated to `applyWithDecidableSide` below, so a failure here would be
easy to localize.

## The semantic principle(s), characterized before writing any tactic
code (per the instruction this file was scoped under)

Inspecting `GQ.lean`'s `every_some`/`most_some`/`atLeast_some` and
`Plurals.lean`'s `some_of_exactly` directly (not assumed) shows **two**
distinct principles, not one - a small coherent family, not thirteen
special cases:

1. **Existential transfer through a universal.** `every_some`'s real
   content, once `R` is seen to be discarded entirely (`fun h ⟨x, hx, _⟩
   => ⟨x, hx, h x hx⟩` never touches the dropped component): *any* fact
   establishing `P` nonempty, combined with `Every P Q`, gives `Some P
   Q`. `GQ.lean`'s new `some_of_nonempty` states this directly over a
   bare `∃ x, P x`; `every_some` remains the same principle specialized
   to one particular witness *source* (a second `Some P R` premise).
   Problem 5's own premise is a bare `∃ x, ambitious x` - a second real
   witness source already present in the corpus, not a hypothetical one.

2. **Positive cardinality gives existence.** `most_some`/`atLeast_some`/
   `some_of_exactly` share one terminal move, visible verbatim in all
   three proofs: `Finset.card_pos.mp` on a positivity fact, then project
   the second half of the resulting `Finset.mem_filter` pair. What
   differs between the three is entirely quantifier-specific arithmetic
   *external* to that shared move - deriving `0 < card (P ∧ Q)` from
   `Most`'s own definition (needs no side fact: `2 * card (P∧Q) > card P
   ≥ 0` already forces it), from `AtLeast n P Q` plus `n ≥ 1`, or from
   `Exactly n P Q` plus `n ≠ 0`. Each of the three lemmas is already
   fully general (arbitrary `P`, `Q`, `n`) - nothing here is proved fresh
   for this file; `exist_nl` only has to *recognize* the shape (a
   stronger quantifier over the *same* `P`, `Q` as a `Some`-headed goal)
   and discharge each lemma's own numeral side-condition mechanically.

Neither principle is a position/polarity substitution - `P`/`Q` never
change between hypothesis and goal here, only the quantifier does - so
this is a genuinely different search from `mono_nl`'s, not a third
`Position`/`MonoRule` cell bolted onto `Signature.lean`'s table (which
stays exactly as Phase 1/2 left it).

**Deliberately not attempted here** (per the standing instruction):
`some_trans`/`atMost_trans` (a different, conditioned-substitution
family), and problems 123/124, whose own proofs chain one of these two
principles *with* a `mono_nl`-style scope substitution in the same
proof term - a real composition this file does not attempt, so both are
expected to remain "eligible but failed" after this phase, not silently
folded in.

## Trace shape

`ExistentialStep` mirrors `MonoStep`'s field shape (`rule`/`sourceHyp`/
`restrictor`/`scope` standing in for `rule`/`factHyp`/`substFrom`/
`substTo`) on purpose, so a future visualizer can render either kind of
step in the same card layout without a separate code path per fragment -
see `Trace.lean`'s own header for the same reasoning applied to
`CombineStep`.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace FraCaS.Section1.Monotonicity

/-- The five dispatchable rules - two witness sources for principle 1
(`someOfNonemptyViaSome`/`someOfNonemptyViaExists`, both closing with
`every_some`/`some_of_nonempty` respectively), three quantifiers for
principle 2 (`atLeastSome`/`mostSome`/`exactlySome`, each an already-
general `GQ.lean`/`Plurals.lean` lemma). None of the five is specific to
any FraCaS problem. -/
inductive ExistentialRule where
  | someOfNonemptyViaSome
  | someOfNonemptyViaExists
  | atLeastSome
  | mostSome
  | exactlySome
  deriving DecidableEq, Repr, Inhabited

/-- See this file's header for why this deliberately mirrors `MonoStep`'s
field shape rather than inventing its own. -/
structure ExistentialStep where
  rule       : ExistentialRule
  sourceHyp  : Lean.Name
  restrictor : Lean.Name
  scope      : Lean.Name
  deriving Repr

/-- Fully-qualified name of `FraCaS.Section2.Exactly`'s head - checked
directly against `Plurals.lean`: same `{A} [Fintype A] (n) (P Q)
[DecidablePred ...]` telescope shape as `AtLeast`/`AtMost`, so
`extractPQ`/`extractN`'s existing "six-argument" case already reads its
`P`/`Q`/`n` back out correctly without any change to `Tactic.lean`. -/
def exactlyHead : Lean.Name := ``FraCaS.Section2.Exactly

/-- Builds `lemmaName` applied to `preArgs ++ [sideCondition, mainFact]`,
leaving the side-condition as a metavariable whose *type* - `n ≥ 1`,
`n ≠ 0`, whatever the lemma's own signature says at that position - is
discovered by `mkAppM`'s own unification, not independently reconstructed
here, then discharges it with `decide` (every FraCaS instance's `n` is a
concrete numeral). Returns `none`, not a thrown error, on any failure -
callers keep searching other candidates. -/
def applyWithDecidableSide (lemmaName : Lean.Name) (preArgs : Array Expr) (mainFact : Expr) :
    MetaM (Option Expr) := do
  try
    let sideMVar ← mkFreshExprMVar none (kind := .synthetic)
    let proof ← mkAppM lemmaName (preArgs ++ #[sideMVar, mainFact])
    let remaining ← Lean.Elab.Tactic.run sideMVar.mvarId! do
      Lean.Elab.Tactic.evalTactic (← `(tactic| decide))
    if remaining.isEmpty then
      some <$> instantiateMVars proof
    else
      pure none
  catch _ =>
    pure none

/-- The Category-B tactic - see this file's header for the two
principles it realizes and what it deliberately doesn't attempt. -/
elab "exist_nl" : tactic => do
  liftMetaTactic1 fun goal => do
    let (_introduced, goal) ← introAll goal
    goal.withContext do
      let goalTy ← goal.getType
      let some goalHeadName := goalTy.getAppFn.constName?
        | throwError "exist_nl: goal is not headed by a named quantifier"
      unless goalHeadName == ``FraCaS.Section1.Some do
        throwError "exist_nl: unsupported goal head {goalHeadName} - exist_nl only closes Some-headed goals (see this file's header for the two principles it covers)"
      let goalArgs := goalTy.getAppArgs
      let some (goalP, goalQ) := extractPQ .some goalArgs
        | throwError "exist_nl: could not read the restrictor/scope out of the goal"

      let lctx ← getLCtx
      let hyps := lctx.decls.toList.filterMap id
        |>.filter (fun d => !d.isImplementationDetail)

      let tryClose (rule : ExistentialRule) (sourceHyp : Lean.Name) (proof : Expr) :
          MetaM Bool := do
        try
          unless ← isDefEq (← inferType proof) goalTy do return false
          let step : ExistentialStep :=
            { rule, sourceHyp, restrictor := (← nameOf goalP), scope := (← nameOf goalQ) }
          logInfo m!"exist_nl: {repr step}"
          goal.assign proof
          return true
        catch _ =>
          return false

      -- Principle 2: a stronger quantifier over the *same* `P`, `Q` as
      -- the goal - no substitution, the quantifier alone weakens.
      --
      -- Quoted names (```` ``Foo ````) are terms, not patterns - matched
      -- via `==` after unwrapping `Option.some`, never as a `match` arm
      -- pattern directly (which only accepts real constructors).
      for d in hyps do
        let dTy := d.type
        let dArgs := dTy.getAppArgs
        match dTy.getAppFn.constName? with
        | some head =>
          if head == ``FraCaS.Section1.AtLeast then
            if let some (dP, dQ) := extractPQ .atLeast dArgs then
              if (← isDefEq dP goalP) && (← isDefEq dQ goalQ) then
                if let some n := extractN .atLeast dArgs then
                  if let some proof ← applyWithDecidableSide
                      ``FraCaS.Section1.atLeast_some #[n, goalP, goalQ] d.toExpr then
                    if ← tryClose .atLeastSome d.userName proof then return none
          else if head == exactlyHead then
            -- `Exactly` shares `AtLeast`/`AtMost`'s exact telescope shape
            -- ({A} [Fintype A] (n) (P Q) [DecidablePred (P∧Q)], six args,
            -- n/P/Q at indices 2/3/4 - checked directly against
            -- `Plurals.lean`), so `extractPQ`/`extractN .atLeast` already
            -- read it correctly with no change needed.
            if let some (dP, dQ) := extractPQ .atLeast dArgs then
              if (← isDefEq dP goalP) && (← isDefEq dQ goalQ) then
                if let some n := extractN .atLeast dArgs then
                  if let some proof ← applyWithDecidableSide
                      ``FraCaS.Section2.some_of_exactly #[n, goalP, goalQ] d.toExpr then
                    if ← tryClose .exactlySome d.userName proof then return none
          else if head == ``FraCaS.Section1.Most then
            -- `Most`'s own telescope is {A} [Fintype A] (P Q) [DecidablePred
            -- P] [DecidablePred (P∧Q)] - six args too, but P/Q sit at
            -- indices 2/3 (no numeral, and *two* instance args, not one) -
            -- checked directly against `GQ.lean`; reusing `extractPQ
            -- .atLeast` here would silently read the wrong slots.
            if dArgs.size == 6 then
              let dP := dArgs[2]!
              let dQ := dArgs[3]!
              if (← isDefEq dP goalP) && (← isDefEq dQ goalQ) then
                try
                  let proof ← mkAppM ``FraCaS.Section1.most_some #[goalP, goalQ, d.toExpr]
                  if ← tryClose .mostSome d.userName proof then return none
                catch _ => pure ()
        | none => pure ()

      -- Principle 1: `Every P Q` (exact match) plus a nonempty-`P`
      -- witness, from a `Some P _` premise (`every_some`, its own scope
      -- discarded) or a bare `∃ x, P x` premise (`some_of_nonempty`).
      let mut everyFact? : Option Expr := none
      for d in hyps do
        let isEvery :=
          match d.type.getAppFn.constName? with
          | some head => head == ``FraCaS.Section1.Every
          | none => false
        if isEvery then
          if let some (dP, dQ) := extractPQ .every d.type.getAppArgs then
            if (← isDefEq dP goalP) && (← isDefEq dQ goalQ) then
              everyFact? := some d.toExpr
      if let some everyFact := everyFact? then
        let expectedExistsTy ← mkAppM ``Exists #[goalP]
        for d in hyps do
          let isSome :=
            match d.type.getAppFn.constName? with
            | some head => head == ``FraCaS.Section1.Some
            | none => false
          if isSome then
            if let some (dP, dR) := extractPQ .some d.type.getAppArgs then
              if ← isDefEq dP goalP then
                try
                  let proof ← mkAppM ``FraCaS.Section1.every_some
                    #[goalP, goalQ, dR, everyFact, d.toExpr]
                  if ← tryClose .someOfNonemptyViaSome d.userName proof then return none
                catch _ => pure ()
          else
            if ← isDefEq d.type expectedExistsTy then
              try
                let proof ← mkAppM ``FraCaS.Section1.some_of_nonempty
                  #[goalP, goalQ, d.toExpr, everyFact]
                if ← tryClose .someOfNonemptyViaExists d.userName proof then return none
              catch _ => pure ()

      throwError "exist_nl: goal is outside the Category-B fragment \
        (no stronger quantifier over the same restrictor/scope, and no \
        Every-plus-nonempty-witness pair, closes it)"

end FraCaS.Section1.Monotonicity
