import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Existential

/-!
# `mono_nl_compose`: composing `exist_nl` into `mono_nl`'s search (Phase 3)

**Investigated before writing any code, per the standing instruction**:
both remaining eligible-but-failed problems, 123 and 124, were initially
plausible candidates for this phase - only 123 actually is one.

Problem 123's real proof (`Section3/Batch1.lean`) is:
```
some_mono_scope reportsNeeded sentByItel onDesk
  (most_some reportsNeeded sentByItel hmost) honDesk
```
`most_some` is exactly `exist_nl`'s existing `mostSome` rule; `some_mono_scope`
is exactly `mono_nl`'s existing `someMonoScope` rule. The *only* thing
missing was a fact of `mono_nl`'s own "shape" position - `Some
reportsNeeded sentByItel` - which is nowhere among the real local
hypotheses (only `Most reportsNeeded sentByItel` is), but which `exist_nl`
already knows how to synthesize. So 123 reduces to *composition*: no new
lemma, no new `ExistentialRule`, no new `MonoRule` - just widening where
`mono_nl` is willing to look for its shape fact.

Problem 124's real proof (`Section3/Batch1.lean`) is:
```
atLeast_mono_scope 2 (fun _ => True) missing removed (le_of_eq hex.symm) hmono
```
`atLeast_mono_scope` is `mono_nl`'s existing rule, but the fact it's fed
- `AtLeast 2 (fun _ => True) missing`, from `le_of_eq hex.symm` - is a
conversion **`Exactly n P Q → AtLeast n P Q`** that none of `exist_nl`'s
five rules produce (all five conclude `Some`, never `AtLeast`). Unlike
123, this is not reachable by recombining what already exists: it needs
one more small fact half of the same numeric-quantifier hierarchy
(`Exactly` is `card = n`; `AtLeast` is `card ≥ n` - literally
`le_of_eq`/`ge_of_eq` on the same underlying comparison), which is
genuinely a new principle, not a composition of the current five. Left
untouched here, per the standing instruction to add nothing this phase
that isn't pure composition of `exist_nl` + `mono_nl` as they already
stand; a future phase could add it as one more clause of `exist_nl`'s own
"quantifier-strength" family (not a new architecture) if wanted, bundled
with `some_trans`/`atMost_trans`.

## The composition itself

`Tactic.lean`'s `searchMonoNl` was factored out of `mono_nl` specifically
to make this possible without a reverse import: it takes a
`computeExtra : List LocalDecl → MetaM (Array (Expr × Lean.Name))`
parameter supplying *extra* candidate "shape" facts (proof term + a
display label) alongside real local hypotheses. `enumerateSomeFacts`
below is that parameter for this file's `mono_nl_compose`: for every
local hypothesis, it tries each of `exist_nl`'s five principles *without*
a specific target restrictor/scope in mind (unlike `exist_nl` itself,
which only looks for one matching a goal it already has) and collects
every `Some`-headed fact that results. `searchMonoNl`'s own,
unchanged-since-Phase-2 logic then decides whether any of those - or a
real hypothesis, exactly as before - actually matches what the goal
needs. Nothing here proves anything `exist_nl` couldn't already prove on
its own; it only makes those proofs available one level up.
-/
open Lean Lean.Meta

namespace FraCaS.Section1.Monotonicity

/-- Every `Some`-headed fact `exist_nl`'s five principles can derive from
`hyps`, regardless of any specific target restrictor/scope - see this
file's header. Mirrors `exist_nl`'s own two-principle dispatch
(`Existential.lean`) exactly, just without the "does it match my goal"
filter, since here the *caller* (`searchMonoNl`) does that matching
against whatever the real goal turns out to need. -/
def enumerateSomeFacts (hyps : List LocalDecl) : MetaM (Array (Expr × Lean.Name)) := do
  let mut out : Array (Expr × Lean.Name) := #[]

  -- Principle 2: a stronger quantifier over the *same* restrictor/scope
  -- as its own source hypothesis - no substitution, only the quantifier
  -- weakens (`atLeastSome`/`exactlySome`/`mostSome`, unchanged from
  -- `Existential.lean`).
  for d in hyps do
    let dArgs := d.type.getAppArgs
    match d.type.getAppFn.constName? with
    | some head =>
      if head == ``FraCaS.Section1.AtLeast then
        if let some (dP, dQ) := extractPQ .atLeast dArgs then
          if let some n := extractN .atLeast dArgs then
            if let some proof ← applyWithDecidableSide
                ``FraCaS.Section1.atLeast_some #[n, dP, dQ] d.toExpr then
              out := out.push (proof, .mkSimple s!"{d.userName} (exist_nl.atLeastSome)")
      else if head == exactlyHead then
        if let some (dP, dQ) := extractPQ .atLeast dArgs then
          if let some n := extractN .atLeast dArgs then
            if let some proof ← applyWithDecidableSide
                ``FraCaS.Section2.some_of_exactly #[n, dP, dQ] d.toExpr then
              out := out.push (proof, .mkSimple s!"{d.userName} (exist_nl.exactlySome)")
      else if head == ``FraCaS.Section1.Most then
        -- Same six-arg, P/Q-at-2/3 shape `Existential.lean` documents.
        if dArgs.size == 6 then
          let dP := dArgs[2]!
          let dQ := dArgs[3]!
          try
            let proof ← mkAppM ``FraCaS.Section1.most_some #[dP, dQ, d.toExpr]
            out := out.push (proof, .mkSimple s!"{d.userName} (exist_nl.mostSome)")
          catch _ => pure ()
    | none => pure ()

  -- Principle 1: `Every P Q` plus a nonempty-`P` witness, from a
  -- `Some P _` hypothesis (`every_some`) or a bare `∃ x, P x` hypothesis
  -- (`some_of_nonempty`) - unchanged from `Existential.lean`, just tried
  -- for every `Every`-headed hypothesis instead of one fixed goal.
  let everyFacts : List (LocalDecl × Expr × Expr) :=
    hyps.filterMap (fun d =>
      match d.type.getAppFn.constName? with
      | some head =>
        if head == ``FraCaS.Section1.Every then
          (extractPQ .every d.type.getAppArgs).map (fun (p, q) => (d, p, q))
        else none
      | none => none)
  for (everyDecl, eP, eQ) in everyFacts do
    let expectedExistsTy ← mkAppM ``Exists #[eP]
    for d in hyps do
      match d.type.getAppFn.constName? with
      | some head =>
        if head == ``FraCaS.Section1.Some then
          if let some (dP, dR) := extractPQ .some d.type.getAppArgs then
            if ← isDefEq dP eP then
              try
                let proof ← mkAppM ``FraCaS.Section1.every_some
                  #[eP, eQ, dR, everyDecl.toExpr, d.toExpr]
                out := out.push (proof,
                  .mkSimple s!"{everyDecl.userName}+{d.userName} (exist_nl.someOfNonemptyViaSome)")
              catch _ => pure ()
        else
          if ← isDefEq d.type expectedExistsTy then
            try
              let proof ← mkAppM ``FraCaS.Section1.some_of_nonempty
                #[eP, eQ, d.toExpr, everyDecl.toExpr]
              out := out.push (proof,
                .mkSimple s!"{everyDecl.userName}+{d.userName} (exist_nl.someOfNonemptyViaExists)")
            catch _ => pure ()
      | none => pure ()

  return out

/-- The Phase-3 composed tactic - see this file's header. Tried as a
third fallback (after `mono_nl`, after `exist_nl`) in `Coverage.lean`,
never a replacement for either. -/
elab "mono_nl_compose" : tactic => do
  liftMetaTactic1 fun goal => do
    if ← searchMonoNl enumerateSomeFacts goal then
      return none
    else
      throwError "mono_nl_compose: goal is outside the Phase-3 fragment \
        (no single-position substitution closes it even after also trying \
        every Some-headed fact exist_nl's own principles can synthesize \
        from a differently-headed hypothesis; this is a small sound \
        fragment, not a general prover)"

end FraCaS.Section1.Monotonicity
