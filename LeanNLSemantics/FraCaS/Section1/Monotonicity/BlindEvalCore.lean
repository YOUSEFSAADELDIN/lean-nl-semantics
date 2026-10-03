import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Scan
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Existential
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Compose

/-!
# Shared blind-evaluation primitives

The reusable part of `BlindEval.lean`'s own methodology - negate a
goal's conclusion, and attempt to automatically close a goal via this
corpus's certified fragment (`mono_nl`/`exist_nl`/`mono_nl_compose`)
plus `most_nl`/`every_most_nl`/`aesop`/`grind`/`omega` - factored out
here because none of it actually needs the whole corpus in scope, unlike
`BlindEval.lean`'s own `runBlindEval` (which imports the root
`LeanNLSemantics` umbrella to scan every already-proved theorem, and so
can never itself be imported back). `BlindEvalUnknownScan.lean` and
`BlindEvalSections3to9.lean` both need exactly this part, not the
corpus-scanning part each builds for its own section range, and
importing `BlindEval.lean` directly for it would hit the same
circularity `BlindEval.lean`'s own header already explains for
`Coverage.lean` - this file is how all three avoid it, the same way
`Scan.lean` already does one layer down for `Coverage.lean`/
`BlindEval.lean` themselves.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace FraCaS.Section1.Monotonicity.BlindEval

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

/-- Reads `Most`'s own restrictor/scope predicates back out of a fully-
applied occurrence's argument array - `Most`'s own signature, verified
directly against `GQ.lean`'s source: `{A} [Fintype A] (P Q : A → Prop)
[DecidablePred P] [DecidablePred (P∧Q)]`, six entries, P/Q at indices
2/3 (no `n` slot, unlike `AtLeast`/`AtMost` - see `Tactic.lean`'s own
`extractPQ` comment for that layout). -/
def extractMostPQ (args : Array Expr) : Option (Expr × Expr) :=
  if args.size == 6 then some (args[2]!, args[3]!) else none

/-- A small, targeted search for `Most`-headed goals via `GQ.lean`'s
`most_trans` - the one general composition fact `fracas_026`'s hand
proof needs, outside `mono_nl`'s own certified fragment
(`Signature.lean`'s table excludes `Most` entirely - see `Tactic.lean`'s
header). Modeled directly on `searchMonoNl`'s own style: reads `R`/`S`
concretely off matched local hypotheses *before* ever building the
`most_trans` application, rather than leaving them as metavariables for
a bare `apply` to guess at. -/
def searchMostNl (goal : MVarId) : MetaM Bool := do
  let (_introduced, goal) ← introAll goal
  goal.withContext do
    let goalTy ← goal.getType
    let some goalHeadName := goalTy.getAppFn.constName? | return false
    unless goalHeadName == ``FraCaS.Section1.Most do return false
    let some (goalP, goalQ) := extractMostPQ goalTy.getAppArgs | return false
    let lctx ← getLCtx
    let hyps := (lctx.decls.toList.filterMap id).filter (fun d => !d.isImplementationDetail)
    for h1 in hyps do
      let h1Ty ← inferType h1.toExpr
      let some h1Head := h1Ty.getAppFn.constName? | continue
      unless h1Head == ``FraCaS.Section1.Most do continue
      let some (h1P, hR) := extractMostPQ h1Ty.getAppArgs | continue
      unless ← isDefEq h1P goalP do continue
      for h2 in hyps do
        let h2Ty ← inferType h2.toExpr
        let some h2Head := h2Ty.getAppFn.constName? | continue
        unless h2Head == ``FraCaS.Section1.Every do continue
        let h2Args := h2Ty.getAppArgs
        unless h2Args.size == 3 do continue
        let h2P := h2Args[1]!
        let hS := h2Args[2]!
        unless ← isDefEq h2P goalP do continue
        let domTy := (← inferType goalP).bindingDomain!
        let expectedH3P ← withLocalDeclD `x domTy fun x => do
          let conj ← mkAppM ``And #[mkApp hS x, mkApp hR x]
          mkLambdaFVars #[x] conj
        for h3 in hyps do
          let h3Ty ← inferType h3.toExpr
          let some h3Head := h3Ty.getAppFn.constName? | continue
          unless h3Head == ``FraCaS.Section1.Every do continue
          let h3Args := h3Ty.getAppArgs
          unless h3Args.size == 3 do continue
          unless ← isDefEq h3Args[1]! expectedH3P do continue
          unless ← isDefEq h3Args[2]! goalQ do continue
          try
            let proof ← mkAppM ``FraCaS.Section1.most_trans
              #[goalP, hR, hS, goalQ, h1.toExpr, h2.toExpr, h3.toExpr]
            unless ← isDefEq (← inferType proof) goalTy do continue
            goal.assign proof
            return true
          catch _ => continue
    return false

elab "most_nl" : tactic => do
  liftMetaTactic1 fun goal => do
    if ← searchMostNl goal then
      return none
    else
      throwError "most_nl: no (Most, Every, Every) hypothesis triple matches most_trans"

/-- The same targeted-search fix as `most_nl`, for `Section2/Plurals
.lean`'s `every_most` (`Every P Q → (∃x, P x) → Most P Q`). -/
def searchEveryMostNl (goal : MVarId) : MetaM Bool := do
  let (_introduced, goal) ← introAll goal
  goal.withContext do
    let goalTy ← goal.getType
    let some goalHeadName := goalTy.getAppFn.constName? | return false
    unless goalHeadName == ``FraCaS.Section1.Most do return false
    let some (goalP, goalQ) := extractMostPQ goalTy.getAppArgs | return false
    let lctx ← getLCtx
    let hyps := (lctx.decls.toList.filterMap id).filter (fun d => !d.isImplementationDetail)
    for h1 in hyps do
      -- h1 : Every goalP goalQ
      let h1Ty ← inferType h1.toExpr
      let some h1Head := h1Ty.getAppFn.constName? | continue
      unless h1Head == ``FraCaS.Section1.Every do continue
      let h1Args := h1Ty.getAppArgs
      unless h1Args.size == 3 do continue
      unless ← isDefEq h1Args[1]! goalP do continue
      unless ← isDefEq h1Args[2]! goalQ do continue
      for h2 in hyps do
        -- h2 : ∃ x, goalP x
        let h2Ty ← inferType h2.toExpr
        let some h2Head := h2Ty.getAppFn.constName? | continue
        unless h2Head == ``Exists do continue
        let h2Args := h2Ty.getAppArgs
        unless h2Args.size == 2 do continue
        unless ← isDefEq h2Args[1]! goalP do continue
        try
          let proof ← mkAppM ``FraCaS.Section2.every_most #[goalP, goalQ, h2.toExpr, h1.toExpr]
          unless ← isDefEq (← inferType proof) goalTy do continue
          goal.assign proof
          return true
        catch _ => continue
    return false

elab "every_most_nl" : tactic => do
  liftMetaTactic1 fun goal => do
    if ← searchEveryMostNl goal then
      return none
    else
      throwError "every_most_nl: no (Every, Exists) hypothesis pair matches every_most"

/-- The `aesop` call below is armed with every general (not
problem-specific) composition/entailment lemma `GQ.lean` **and**
`Section2/Plurals.lean` already has - the complete list, not a
hand-picked subset chosen to close any one problem.

The fixed tactic chain both directions get, in order: this corpus's
own certified monotonicity fragment first (`mono_nl`, `exist_nl`,
`mono_nl_compose`), then `most_nl`/`every_most_nl`, then one `aesop`
call - unfolding the plain-`def` quantifiers (`Every`/`Some`/`No`) it
can't see through on its own, and armed with every general GQ.lean
lemma above - then `grind`, then `intros; omega` as a last resort (the
one addition made when this chain started covering Sections 3-9 too:
several of those problems - FraCaS's own cardinal comparatives in
particular, see `Section6/Comparatives.lean`'s own header - are literal
`Nat` inequalities their own hand proofs already close with bare
`omega`, so leaving it out would fail every one of those by omission,
not by any real limit on what a generic, non-problem-specific arithmetic
decision procedure can do; `intros` first since `omega` itself doesn't
peel a goal's own leading implications the way `aesop`/`grind` already
do). Stops at the first success. -/
def attemptClose (ty : Expr) : TermElabM Bool := do
  if ← runTacticBool ty (← `(tactic| mono_nl)) then return true
  if ← runTacticBool ty (← `(tactic| exist_nl)) then return true
  if ← runTacticBool ty (← `(tactic| mono_nl_compose)) then return true
  if ← runTacticBool ty (← `(tactic| most_nl)) then return true
  if ← runTacticBool ty (← `(tactic| every_most_nl)) then return true
  if ← runTacticBool ty (← `(tactic|
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
          safe apply FraCaS.Section2.exactly_atMost, safe apply FraCaS.Section2.every_most)))
  then return true
  if ← runTacticBool ty (← `(tactic| grind)) then return true
  if ← runTacticBool ty (← `(tactic| (intros; omega))) then return true
  return false

end FraCaS.Section1.Monotonicity.BlindEval
