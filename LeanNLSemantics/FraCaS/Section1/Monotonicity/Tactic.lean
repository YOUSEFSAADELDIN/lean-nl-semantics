import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Trace

/-!
# `mono_nl`: the certified monotonicity tactic (Phase 1, 2 + 5)

**Validation status**: this sandbox's egress policy denies
`release.lean-lang.org` (403, confirmed via the proxy status endpoint,
not a fixable client misconfiguration the way the GF/`cabal` issue in
`gf/NOTES.md` was), so no Lean toolchain can be fetched here - every
confirmation of this file has come from CI, the same bridging role it
played for `build-gf` before a local GF toolchain became available.
Phase 1 is confirmed: CI found and this file fixed one real bug (`whnf`
over-unfolding the goal, see `introAll`'s comment) and then ran clean.
Phase 2 (the combine step below) is confirmed as well - both are folded
into the one `searchMonoNl` search below, exercised together on every CI
run since. The running, CI-confirmed corpus-wide count this search
closes (together with Category B/Phase 3/4, layered on top in the other
files that reuse it) is tracked in exactly one place, `Coverage.lean`'s
own header, rather than duplicated here where it would go stale - see
that file for the current numbers.

## What the tactic does

**Phase 1** closes a goal of the shape `H₁ → H₂ → ... → Concl`, where
(after `intro`s) `Concl` and exactly one hypothesis `Hshape` share the
same head quantifier (`Every`/`Some`/`AtLeast`/`AtMost` - see
`Signature.lean`) and differ in exactly one of their two arguments
(`restrictor` xor `scope`), and some other hypothesis `Hfact` directly
supplies the `Entails` fact (`Signature.lean`'s polarity table) that
difference needs.

**Phase 2** widens only how that `Entails` fact is found, never how it's
used: when no single hypothesis supplies it but the needed fact's target
is itself a conjunction `fun x => A x ∧ B x` (`every_trans`'s `S ∧ R`,
`every_mp`'s `P ∧ Q` - both checked directly against `GQ.lean`), the
tactic looks for two `Entails`-shaped facts sharing the same left side
and *combines* them via `GQ.lean`'s `entails_and` (or `entails_refl` for
the trivial "P entails P" case `every_mp`'s own shape needs) into exactly
the fact Phase 1's machinery was already looking for - an explicit
semantic step, not a name-matched special case for any of the FraCaS
problems that happen to need it (`decomposeConjLambda` recognizes the
*shape*, never a specific theorem).

Either way, the tactic closes the goal by applying the one real
`GQ.lean` lemma the position/polarity table names - the kernel checks
*that* lemma's already-proved statement, nothing this tactic invents -
and logs the `MonoStep` (and, in the Phase-2 case, the preceding
`CombineStep`) it actually used, not a separately authored description,
as an explanatory trace via `logInfo`.

**Phase 3** (`Compose.lean`, a separate file - see its own header) widens
the search once more, again never how a fact is *used*: it lets the
"shape" premise itself - the one Phase 1 always required to be a single
real local hypothesis sharing the goal's own head - come from a fact
`Existential.lean`'s five `exist_nl` principles can *synthesize* from a
differently-headed hypothesis instead (`Most`/`AtLeast`/`Exactly`/`Every`
+ witness, all producing a `Some`-headed fact `exist_nl` itself already
knows how to prove). `searchMonoNl` below is written generically against
an `extraShapeFacts` pool for exactly this reason, so this file never
needs to import `Existential.lean` (which already imports this one - a
reverse import would cycle) to support it.

**Phase 5** widens how the `Entails` fact is *used*, the one axis Phase
1/2/3 all deliberately left alone: every substitution rule so far has
required that fact to hold flatly, everywhere (`Every needFrom needTo`).
`atMost_trans`'s own real proof (`GQ.lean`) never has that - only a
`needFrom`-`needTo` link *conditioned* on an auxiliary predicate that
itself only holds within the shape's own restrictor (`Every P S`, `Every
(fun x => S x ∧ needFrom x) needTo`). `GQ.lean`'s `entails_narrow`
combines exactly those two premises into the conditioned fact `Every
(fun x => P x ∧ needFrom x) needTo`, and a *conditioned* counterpart of
the cell's own rule (currently only `atMost_mono_scope_conditioned`,
registered as `MonoRule.atMostMonoScopeConditioned` - see `Trace.lean`)
consumes it. Grounded, not invented for this one problem: the schema's
`Every`-quantifier instance already exists independently as `every_mp`
(see `entails_narrow`'s own doc comment for the exact correspondence).
Like Phase 2, this lives directly in `searchMonoNl` rather than
`Compose.lean`, since it is a new way to *use* a fact - the axis
Phase 3/4's composition deliberately never touches - not a new place to
*find* one.

It fails, loudly (`throwError`, never a silent wrong answer), the moment
the goal is outside this fragment: an unsupported head (`No`, `Most`, or
anything else), more than one differing argument, zero differing
arguments (a trivial restatement isn't a substitution - see
`Coverage.lean`'s separate `isTrivial` check, which keeps these out of
the "eligible but failed" count entirely rather than conflating them
with a genuine monotonicity miss), or no hypothesis - alone or combined -
of the right `Entails` shape in the right direction. An
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
  | .atMostMonoScopeConditioned => ``FraCaS.Section1.atMost_mono_scope_conditioned
  | .atLeastMonoScopeConditioned => ``FraCaS.Section1.atLeast_mono_scope_conditioned

/-- Repeatedly `intro`s the goal's leading Π-binders (every problem in
this fragment is stated as a chain of implications ending in the
quantified conclusion), returning the introduced hypotheses and the
resulting goal. Built from `MVarId.intro1` (auto-named, single-binder)
rather than a plural `intros`/named-`intro` helper, to keep this to the
smallest API surface this session can be confident of without being able
to compile it - the hypotheses' display names are cosmetic only (the
trace still identifies the fact hypothesis it used via its real, current
`userName`, whatever `intro1` happened to pick), never load-bearing.

Deliberately checks `Expr.isForall` on the type *as elaborated*, not its
`whnf` - CI's first real run caught, in exactly the way this project
expects a real build to, that `whnf` unfolds `Every`/`Some`/`AtLeast`/
`AtMost` (all plain `def`s or reducible `abbrev`s) straight through to
their raw `∀ x, ...`/`Exists`/`Nat.le` bodies. For `Every` in particular
that raw body is *itself* a Π-type, so a `whnf`-based check kept
introducing the goal's own bound variable as if it were one more premise
in the implication chain, rather than stopping at the literal `Every P Q`
application this tactic is built to recognize. The chain of premises
this fragment's goals are stated with is already a literal sequence of
`Expr.forallE` nodes at elaboration time - nothing here needs semantic
unfolding to see it - so checking the raw type is not just a fix but the
more correct predicate for what this loop is actually looking for. -/
partial def introAll (goal : MVarId) : MetaM (Array FVarId × MVarId) := do
  let ty ← goal.getType
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

/-- Phase 2: decomposes a lambda `fun x => A x ∧ B x` back into its two
conjuncts `A`, `B` as standalone predicates - purely syntactic (no
`MetaM` needed), matching exactly the shape every conjunctive restrictor
in `every_trans`/`every_mp`'s own premises is written in (`GQ.lean`,
verified directly: `fun x => S x ∧ R x`, `fun x => P x ∧ Q x`). Returns
`none` for anything else - a bare non-conjunctive predicate, or a
genuinely `x`-dependent conjunct that isn't simply "some outer predicate
applied to `x`" - rather than guessing at a shape this fragment doesn't
target. -/
def decomposeConjLambda (e : Expr) : Option (Expr × Expr) :=
  match e with
  | .lam _ _ body _ =>
    match body with
    | .app (.app (.const ``And _) l) r =>
      match l, r with
      | .app a (.bvar 0), .app b (.bvar 0) => some (a, b)
      | _, _ => none
    | _ => none
  | _ => none

/-- The Phase-1/2/3/5 monotonicity search, factored out of `elab "mono_nl"`
so `Compose.lean` can reuse it (see this file's header, "Phase 3") without
this file importing `Existential.lean` (which already imports this file -
a reverse import would cycle). `computeExtra` is handed the post-`introAll`
local context and returns extra candidate "shape" facts - proof term plus
a display label - to try alongside real local hypotheses; `mono_nl` itself
passes `fun _ => pure #[]` (Phase 1/2, unchanged behaviour). Returns `true`
(and assigns `goal`) iff it closed the goal; `false`, never a thrown
error, otherwise - callers decide whether/how to report failure. -/
def searchMonoNl (computeExtra : List LocalDecl → MetaM (Array (Expr × Lean.Name)))
    (goal : MVarId) : MetaM Bool := do
  let (_introduced, goal) ← introAll goal
  goal.withContext do
    -- Raw type, not `whnf` - see `introAll`'s comment: whnf unfolds
    -- these quantifiers straight past the named-application shape this
    -- tactic matches on.
    let goalTy ← goal.getType
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

    -- The "shape" candidates: every real local hypothesis (as before),
    -- plus whatever `computeExtra` synthesizes (Phase 3 only; empty for
    -- `mono_nl` itself). `shapeFvarId?` is `some _` only for a real
    -- hypothesis - it exists purely so the Phase-1 fact-search below can
    -- still exclude the shape hyp from also supplying the fact hyp,
    -- exactly as it always did; a synthesized shape has nothing to
    -- exclude, so it's simply never equal to a real `factDecl.fvarId`.
    let extra ← computeExtra hyps
    let shapeCandidates : Array (Expr × Option FVarId × Option Lean.Name) :=
      (hyps.toArray.map (fun d => (d.toExpr, some d.fvarId, none))) ++
        (extra.map (fun (e, label) => (e, none, some label)))

    for (shapeExpr, shapeFvarId?, shapeLabel?) in shapeCandidates do
      -- Same reasoning as `goalTy` above: no `whnf`.
      let shapeTy ← inferType shapeExpr
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

      -- Applies `rule`'s real GQ.lean lemma to a candidate `factExpr :
      -- expectedFactTy`, exactly as Phase 1 always did - `combine` is
      -- `none` for a real local hypothesis, `some _` when `factExpr` was
      -- synthesized by the Phase-2 step below, and likewise `narrow` for
      -- Phase 5's `entails_narrow`-synthesized fact. Either way this
      -- closure is the *only* place any lemma gets applied: Phase 2/3/5
      -- add new ways to find a fact, never a new way to consume one.
      -- `ruleOverride` lets Phase 5 substitute a *conditioned* rule
      -- (currently only `atMostMonoScopeConditioned`) for the cell's
      -- default flat one without duplicating this whole closure.
      let tryFact (factExpr : Expr) (factHypName : Lean.Name) (combine : Option CombineStep)
          (narrow : Option NarrowStep := none) (ruleOverride : Option MonoRule := none) :
          MetaM Bool := do
        try
          let effRule := ruleOverride.getD rule
          let lemmaArgs : Array Expr ←
            match effRule with
            | .everyMonoScope   => pure #[goalP, shapeQ, goalQ, shapeExpr, factExpr]
            | .everyRestrict    => pure #[goalP, goalQ, shapeP, shapeExpr, factExpr]
            | .someMonoScope    => pure #[goalP, shapeQ, goalQ, shapeExpr, factExpr]
            | .someRestrict     => pure #[shapeP, goalQ, goalP, shapeExpr, factExpr]
            | .atLeastMonoScope => pure #[n, goalP, shapeQ, goalQ, shapeExpr, factExpr]
            | .atLeastRestrict  => pure #[n, shapeP, goalQ, goalP, shapeExpr, factExpr]
            | .atMostMonoScope  => pure #[n, goalP, shapeQ, goalQ, shapeExpr, factExpr]
            | .atMostRestrict   => pure #[n, shapeP, goalQ, goalP, shapeExpr, factExpr]
            | .atMostMonoScopeConditioned => pure #[n, goalP, shapeQ, goalQ, shapeExpr, factExpr]
            | .atLeastMonoScopeConditioned => pure #[n, goalP, shapeQ, goalQ, shapeExpr, factExpr]
          let proof ← mkAppM effRule.lemmaName lemmaArgs
          unless ← isDefEq (← inferType proof) (← goal.getType) do return false
          let step : MonoStep :=
            { position, rule := effRule
              factHyp := factHypName
              substFrom := (← nameOf oldVal)
              substTo := (← nameOf newVal)
              shapeSource := shapeLabel?
              narrow }
          match combine with
          | some c => logInfo m!"mono_nl: combine {repr c}"
          | none => pure ()
          match narrow with
          | some nStep => logInfo m!"mono_nl: narrow {repr nStep}"
          | none => pure ()
          logInfo m!"mono_nl: {repr step}"
          goal.assign proof
          return true
        catch _ =>
          return false

      -- Phase 1: a real local hypothesis of the right `Entails` shape.
      for factDecl in hyps do
        if some factDecl.fvarId == shapeFvarId? then continue
        unless ← isDefEq factDecl.type expectedFactTy do continue
        if ← tryFact factDecl.toExpr factDecl.userName none then return true

      -- Phase 2: no single hypothesis matched. When `needTo` is itself
      -- written as a conjunction `fun x => A x ∧ B x` (`every_trans`'s
      -- `S ∧ R`, `every_mp`'s `P ∧ Q`, both checked directly against
      -- `GQ.lean`), try synthesizing the needed fact instead - combining
      -- two `Every`-shaped facts that share `needFrom` as their own
      -- restrictor into one fact about their conjunction, via `GQ.lean`'s
      -- `entails_and`. `entails_refl needFrom : Every needFrom needFrom`
      -- is always one available candidate (the fact `every_mp`'s own
      -- shape needs, since one conjunct there is `needFrom` itself) -
      -- everything else comes from a real local hypothesis, checked the
      -- same way `expectedFactTy` itself is. This is the one explicit new
      -- semantic step Phase 2 adds; `tryFact` above still does all the
      -- actual proving with it, exactly as it did for a bare hypothesis.
      if let some (partA, partB) := decomposeConjLambda needTo then
        let mut candidates : Array (Expr × Expr × Option Lean.Name) := #[]
        candidates := candidates.push
          (← mkAppM ``FraCaS.Section1.entails_refl #[needFrom], needFrom, none)
        for d in hyps do
          match d.type.getAppFn.constName? with
          | some dHead =>
            if dHead == ``FraCaS.Section1.Every then
              if let some (dP, dQ) := extractPQ .every d.type.getAppArgs then
                if ← isDefEq dP needFrom then
                  candidates := candidates.push (d.toExpr, dQ, some d.userName)
          | none => pure ()
        for (proof1, q1, name1) in candidates do
          unless ← isDefEq q1 partA do continue
          for (proof2, q2, name2) in candidates do
            unless ← isDefEq q2 partB do continue
            try
              let combined ← mkAppM ``FraCaS.Section1.entails_and
                #[needFrom, partA, partB, proof1, proof2]
              let combineStep : CombineStep :=
                { left := name1, right := name2
                  sharedLeft := (← nameOf needFrom)
                  leftConjunct := (← nameOf partA)
                  rightConjunct := (← nameOf partB) }
              if ← tryFact combined (← nameOf needTo) (some combineStep) then return true
            catch _ =>
              continue

      -- Phase 5: the general "conditioned narrowing" schema (see
      -- `GQ.lean`'s `entails_narrow` for its statement and grounding, and
      -- `Trace.lean`'s `NarrowStep`/`atMostMonoScopeConditioned` for why
      -- this is a registered fallback rather than a table cell). Only a
      -- cell with a registered conditioned rule gets one; today that's
      -- `(AtMost, scope)` and `(AtLeast, scope)` - everywhere else `condRule?` is `none`
      -- and this block does nothing, so it can only ever widen what
      -- already-passing goals close, never change how they do.
      let condRule? : Option MonoRule :=
        if rule == .atMostMonoScope then some .atMostMonoScopeConditioned
        else if rule == .atLeastMonoScope then some .atLeastMonoScopeConditioned
        else none
      if let some condRule := condRule? then
        -- The conditioned fact `entails_narrow` would produce is `Every
        -- (fun x => auxRestrictor x ∧ needFrom x) needTo` for some
        -- `auxRestrictor` - found here as a real local hypothesis
        -- (`innerDecl`) via `decomposeConjLambda` on its own restrictor,
        -- exactly the way Phase 2 decomposes `needTo` above (a
        -- different predicate position, the same syntactic move).
        for innerDecl in hyps do
          match innerDecl.type.getAppFn.constName? with
          | some innerHead =>
            if innerHead == ``FraCaS.Section1.Every then
              if let some (innerP, innerQ) := extractPQ .every innerDecl.type.getAppArgs then
                if let some (auxRestrictor, innerNeedFrom) := decomposeConjLambda innerP then
                  if (← isDefEq innerNeedFrom needFrom) && (← isDefEq innerQ needTo) then
                    -- The second premise `entails_narrow` needs: a real
                    -- local hypothesis `Every goalP auxRestrictor` - "the
                    -- shape's own restrictor entails the aux predicate,"
                    -- exactly `atMost_trans`'s own `Every P S` premise.
                    let expectedOuterTy ← mkAppM ``FraCaS.Section1.Every #[goalP, auxRestrictor]
                    for outerDecl in hyps do
                      unless ← isDefEq outerDecl.type expectedOuterTy do continue
                      try
                        let conditioned ← mkAppM ``FraCaS.Section1.entails_narrow
                          #[goalP, auxRestrictor, needFrom, needTo, outerDecl.toExpr, innerDecl.toExpr]
                        let narrowStep : NarrowStep :=
                          { outer := outerDecl.userName, inner := innerDecl.userName
                            viaAux := (← nameOf auxRestrictor) }
                        if ← tryFact conditioned (← nameOf needTo) none (some narrowStep)
                            (some condRule) then
                          return true
                      catch _ =>
                        continue
          | none => pure ()
    return false

/-- The Phase-1/2 monotonicity tactic - see this file's header for the full
algorithm and its validation status. -/
elab "mono_nl" : tactic => do
  liftMetaTactic1 fun goal => do
    if ← searchMonoNl (fun _ => pure #[]) goal then
      return none
    else
      throwError "mono_nl: goal is outside the Phase-1/2 monotonicity fragment \
        (no single-position substitution - backed either by a matching \
        Entails fact directly, by combining two into one via \
        entails_and/entails_refl, or (for AtMost's scope cell) by \
        narrowing one via entails_narrow - closes it; this is a small \
        sound fragment, not a general prover)"

end FraCaS.Section1.Monotonicity
