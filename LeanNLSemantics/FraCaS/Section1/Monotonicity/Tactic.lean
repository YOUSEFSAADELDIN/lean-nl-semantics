import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Trace

/-!
# `mono_nl`: the Phase-1 certified monotonicity tactic

**Validation status, read before trusting anything below**: this file was
written and reasoned through carefully (every lemma name and argument
order it applies is cross-checked, in the comments below, against the
real, already-read `GQ.lean` source), but it has **not been compiled or
run** - this sandbox's egress policy denies `release.lean-lang.org` (403,
confirmed via the proxy status endpoint, not a fixable client
misconfiguration the way the GF/`cabal` issue in `gf/NOTES.md` was), so no
Lean toolchain can be fetched here. Every other claim in this project has
been backed by a real local build before being written down as fact; this
one cannot be, yet. GitHub Actions can reach the real toolchain, so the
first real confirmation of this file is expected to come from CI, the
same bridging role it played for `build-gf` before a local GF toolchain
became available (see `.github/workflows/build.yml`'s history). Treat
this file as "reasoned through, not yet kernel-checked" until a CI run
(or a session with toolchain access) says otherwise.

## What the tactic does

Closes a goal of the shape `H₁ → H₂ → ... → Concl`, where (after
`intro`s) `Concl` and exactly one hypothesis `Hshape` share the same head
quantifier (`Every`/`Some`/`AtLeast`/`AtMost` - see `Signature.lean`) and
differ in exactly one of their two arguments (`restrictor` xor `scope`),
and some other hypothesis `Hfact` supplies the `Entails` fact
(`Signature.lean`'s polarity table) that difference needs. It closes the
goal by applying the one real `GQ.lean` lemma that shape names - the
kernel checks *that* lemma's already-proved statement, nothing this
tactic invents - and logs the `MonoStep` it computed (not a separately
authored one) as an explanatory trace via `logInfo`.

It fails, loudly (`throwError`, never a silent wrong answer), the moment
the goal is outside this small fragment: an unsupported head (`No`,
`Most`, or anything else), more than one differing argument, zero
differing arguments (a trivial restatement isn't a substitution), or no
hypothesis of the right `Entails` shape in the right direction. An
incorrectly-constructed application also fails loudly, at `mkAppM`'s own
elaboration-time type checking or at this tactic's own defensive
`isDefEq` check before assigning - never at a silent `sorry`-shaped gap,
since none is used anywhere here.

## Why the trace is `logInfo`, not a custom environment extension

A fancier design - the tactic persisting each `MonoStep` into a custom
`Lean.PersistentEnvExtension` keyed by theorem name, queryable later by a
JSON-export script - was considered and set aside for this first,
unvalidated pass: it is real additional metaprogramming surface area
(an environment extension needs its own initialization, a registered
`initialize` block, and careful interaction with `#eval`/incremental
compilation) that this session cannot compile-check even once. `logInfo`
is well-trodden `TacticM` API; the `MonoStep` it prints is the same
value `Tactic.lean` uses to build the proof, not a second, independently
recomputed description of it, so the log line and the real proof cannot
drift apart from each other even though the log line itself isn't
mechanically re-parsed by anything yet. Hardening this into a real
queryable trace store is future work, once this file has a real compile
behind it to iterate against.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace FraCaS.Section1.Monotonicity

/-- Fully-qualified heads this tactic recognizes at a goal's outermost
application, paired with the `Quantifier` they denote. -/
def quantifierHeads : List (Lean.Name × Quantifier) :=
  [(``FraCaS.Section1.Every, .every),
   (``FraCaS.Section1.Some, .some),
   (``FraCaS.Section1.AtLeast, .atLeast),
   (``FraCaS.Section1.AtMost, .atMost)]

/-- The real, already-proved `GQ.lean` lemma each rule applies. Verified
by hand against `GQ.lean`'s own source (read directly, not assumed):
```
every_mono_scope   (P Q R) : Every P Q → (∀ x, Q x → R x) → Every P R
every_restrict     (P Q R) : Every R Q → Every P R → Every P Q
some_mono_scope    (P Q R) : Some P Q → (∀ x, Q x → R x) → Some P R
some_restrict      (P Q R) : Some P Q → Every P R → Some R Q
atLeast_mono_scope (n P Q R) : AtLeast n P Q → (∀ x, Q x → R x) → AtLeast n P R
atLeast_restrict   (n P Q R) : AtLeast n P Q → Every P R → AtLeast n R Q
atMost_mono_scope  (n P Q R) : AtMost n P Q → (∀ x, R x → Q x) → AtMost n P R
atMost_restrict    (n P Q R) : AtMost n P Q → Every R P → AtMost n R Q
```
-/
def MonoRule.lemmaName : MonoRule → Lean.Name
  | .everyMonoScope   => ``FraCaS.Section1.every_mono_scope
  | .everyRestrict    => ``FraCaS.Section1.every_restrict
  | .someMonoScope    => ``FraCaS.Section1.some_mono_scope
  | .someRestrict     => ``FraCaS.Section1.some_restrict
  | .atLeastMonoScope => ``FraCaS.Section1.atLeast_mono_scope
  | .atLeastRestrict  => ``FraCaS.Section1.atLeast_restrict
  | .atMostMonoScope  => ``FraCaS.Section1.atMost_mono_scope
  | .atMostRestrict   => ``FraCaS.Section1.atMost_restrict

/-- Repeatedly `intro`s the goal's leading Π-binders (every problem in
this fragment is stated as a chain of implications ending in the
quantified conclusion), returning the introduced hypotheses and the
resulting goal. Built from `MVarId.intro1` (auto-named, single-binder)
rather than a plural `intros`/named-`intro` helper, to keep this to the
smallest API surface this session can be confident of without being able
to compile it - the hypotheses' display names are cosmetic only (the
trace still identifies the fact hypothesis it used via its real, current
`userName`, whatever `intro1` happened to pick), never load-bearing. -/
partial def introAll (goal : MVarId) : MetaM (Array FVarId × MVarId) := do
  let ty ← whnf (← goal.getType)
  if ty.isForall then
    let (fvarId, goal') ← goal.intro1
    let (rest, goalFinal) ← introAll goal'
    return (#[fvarId] ++ rest, goalFinal)
  else
    return (#[], goal)

/-- Reads a quantifier application's restrictor/scope predicates back out
of its argument array. `Every`/`Some` are plain `def`s with signature
`{A} (P Q : A → Prop)` - a fully-applied occurrence's argument array is
exactly `#[A, P, Q]`, so indices 1/2 are safe by construction, not by
assumption. `AtLeast`/`AtMost` are `abbrev`s with signature `{A}
[Fintype A] (n : Nat) (P Q : A → Prop) [DecidablePred ...]` (`GQ.lean`,
verified directly) - Lean's argument arrays always follow a constant's
own declaration (telescope) order regardless of explicit/implicit-ness,
so a fully-applied occurrence is `#[A, fintypeInst, n, P, Q,
decidablePredInst]`, six entries, P/Q at indices 3/4. -/
def extractPQ (quant : Quantifier) (args : Array Expr) : Option (Expr × Expr) :=
  match quant with
  | .every | .some =>
    if args.size == 3 then some (args[1]!, args[2]!) else none
  | .atLeast | .atMost =>
    if args.size == 6 then some (args[3]!, args[4]!) else none

/-- The numeral argument, for `AtLeast`/`AtMost` only - see `extractPQ`'s
comment for the argument-index layout this relies on. -/
def extractN (quant : Quantifier) (args : Array Expr) : Option Expr :=
  match quant with
  | .atLeast | .atMost => if args.size == 6 then some args[2]! else none
  | .every | .some => none

/-- A local declaration's stable display name: its own `userName` when it
is literally a local variable (true for every predicate this fragment's
target problems ever substitute between - each is a named binder from
the enclosing theorem's own `variable` block), and a pretty-printed
stand-in otherwise, so the tactic never has to fail just to name a step
in the trace. -/
def nameOf (e : Expr) : MetaM Lean.Name := do
  if let .fvar fvarId := e then
    return (← fvarId.getDecl).userName
  else
    return .mkSimple (toString (← ppExpr e))

/-- The Phase-1 monotonicity tactic - see this file's header for the full
algorithm and its validation status. -/
elab "mono_nl" : tactic => do
  liftMetaTactic1 fun goal => do
    let (_introduced, goal) ← introAll goal
    goal.withContext do
      let goalTy ← whnf (← goal.getType)
      let goalHead := goalTy.getAppFn
      let some goalHeadName := goalHead.constName?
        | throwError "mono_nl: goal is not headed by a named quantifier"
      let some quant := quantifierHeads.lookup goalHeadName
        | throwError "mono_nl: unsupported head {goalHeadName} - only Every/Some/AtLeast/AtMost are in the Phase-1 fragment (No/Most are excluded, see Signature.lean)"
      let goalArgs := goalTy.getAppArgs
      let some (goalP, goalQ) := extractPQ quant goalArgs
        | throwError "mono_nl: could not read the restrictor/scope out of the goal"
      -- `n` for AtLeast/AtMost only; safe via `extractPQ`'s success above,
      -- which shares its `args.size == 6` guard with `extractN`. Unused
      -- (and never read) for Every/Some.
      let n : Expr := (extractN quant goalArgs).getD default
      let sig := QuantifierSig.table quant

      let lctx ← getLCtx
      let hyps := lctx.decls.toList.filterMap id
        |>.filter (fun d => !d.isImplementationDetail)

      for shapeDecl in hyps do
        let shapeTy ← whnf shapeDecl.type
        let some shapeHeadName := shapeTy.getAppFn.constName?
          | continue
        if shapeHeadName != goalHeadName then continue
        let shapeArgs := shapeTy.getAppArgs
        let some (shapeP, shapeQ) := extractPQ quant shapeArgs
          | continue
        -- Same numeral bound on both sides - `atLeast_mono_scope` and
        -- friends thread one `n` through premise and conclusion, they
        -- don't relate two different bounds. Matched rather than compared
        -- via `==`, so this never needs a `BEq Quantifier` instance.
        match quant with
        | .atLeast | .atMost =>
          let some shapeN := extractN quant shapeArgs | continue
          unless ← isDefEq shapeN n do continue
        | .every | .some => pure ()
        let restrictorSame ← isDefEq shapeP goalP
        let scopeSame ← isDefEq shapeQ goalQ
        let position? : Option Position :=
          if restrictorSame && !scopeSame then some .scope
          else if !restrictorSame && scopeSame then some .restrictor
          else none
        let some position := position?
          | continue
        let rule := ruleFor quant position
        let (oldVal, newVal) :=
          match position with
          | .scope => (shapeQ, goalQ)
          | .restrictor => (shapeP, goalP)
        let pol := match position with | .scope => sig.scope | .restrictor => sig.restrictor
        let (needFrom, needTo) :=
          match pol with
          | .up => (oldVal, newVal)
          | .down => (newVal, oldVal)
          | .non => (oldVal, newVal) -- unreachable: no fragment cell is `.non` (Signature.lean)
        let expectedFactTy ← mkAppM ``FraCaS.Section1.Every #[needFrom, needTo]

        for factDecl in hyps do
          if factDecl.fvarId == shapeDecl.fvarId then continue
          unless ← isDefEq factDecl.type expectedFactTy do continue
          let shapeExpr := shapeDecl.toExpr
          let factExpr := factDecl.toExpr
          let lemmaArgs : Array Expr ←
            match rule with
            | .everyMonoScope   => pure #[goalP, shapeQ, goalQ, shapeExpr, factExpr]
            | .everyRestrict    => pure #[goalP, goalQ, shapeP, shapeExpr, factExpr]
            | .someMonoScope    => pure #[goalP, shapeQ, goalQ, shapeExpr, factExpr]
            | .someRestrict     => pure #[shapeP, goalQ, goalP, shapeExpr, factExpr]
            | .atLeastMonoScope => pure #[n, goalP, shapeQ, goalQ, shapeExpr, factExpr]
            | .atLeastRestrict  => pure #[n, shapeP, goalQ, goalP, shapeExpr, factExpr]
            | .atMostMonoScope  => pure #[n, goalP, shapeQ, goalQ, shapeExpr, factExpr]
            | .atMostRestrict   => pure #[n, shapeP, goalQ, goalP, shapeExpr, factExpr]
          try
            let proof ← mkAppM rule.lemmaName lemmaArgs
            unless ← isDefEq (← inferType proof) (← goal.getType) do continue
            let step : MonoStep :=
              { position, rule
                factHyp := factDecl.userName
                substFrom := (← nameOf oldVal)
                substTo := (← nameOf newVal) }
            logInfo m!"mono_nl: {repr step}"
            goal.assign proof
            return none
          catch _ =>
            continue
      throwError "mono_nl: goal is outside the Phase-1 monotonicity fragment \
        (no single-position substitution, backed by a matching Entails fact, \
        closes it - this is a small sound fragment, not a general prover)"

end FraCaS.Section1.Monotonicity
