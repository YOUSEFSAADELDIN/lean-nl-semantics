import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Existential

/-!
# `mono_nl_compose`: composing `exist_nl` into `mono_nl`'s search (Phase 3/4)

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
five rules produce (all five conclude `Some`, never `AtLeast`). At the
time, not reachable by recombining what already existed.

## Phase 4: `Exactly → AtLeast`/`AtMost`, and `some_trans`'s combine step

Investigated whether 124 and the two problems `mono_nl_compose` still
missed (027, 044) reduce to *one* common "conditioned-substitution"
schema, per the standing instruction. They don't, cleanly, as one - but
two of the three each reduce their own way:

- **124** needs exactly the `Exactly n P Q → AtLeast n P Q` conversion
  identified above - `GQ.lean`'s `exactly_atLeast`/`exactly_atMost`
  (Section2/`Plurals.lean`) name it directly (`le_of_eq`/`le_of_eq ∘
  .symm` on the same `card (P∧Q)` `Exactly`/`AtLeast`/`AtMost` all share -
  no new mathematical content, the other two directions of the same
  numeric-quantifier-strength hierarchy `atLeast_some`/`most_some`/
  `some_of_exactly` already draw on). This needs **no new tactic
  machinery at all**: `searchMonoNl`'s shape-matching loop already
  compares heads generically, so widening what `enumerateExtraShapeFacts`
  below enumerates (now also `AtLeast`/`AtMost`-headed candidates from an
  `Exactly`-headed hypothesis) is enough - 124 closes via the *same*
  `mono_nl_compose` tactic, unchanged.

- **027** (`some_trans : Some P R → Every P S → Every (fun x => S x ∧ R
  x) Q → Some P Q`) looks parallel to `every_trans`/`every_mp` (already
  solved via Phase 2's `entails_and` feeding `every_mono_scope`) but
  isn't quite the same reduction: working the term out explicitly shows
  it needs one new *mixed* combine lemma, `GQ.lean`'s `some_entails_and`
  (`Some P Q → Every P R → Some P (fun x => R x ∧ Q x)`, `entails_and`'s
  sibling for `Some`+`Every` instead of `Every`+`Every`), then
  `some_mono_scope` (already in `Signature.lean`'s table) consumes the
  result exactly as `every_mono_scope` consumes `entails_and`'s. One new
  general lemma, zero new tactic machinery - `enumerateExtraShapeFacts`
  enumerates candidate `(Some P R, Every P S)` pairs sharing `P` the same
  way Phase 2's own combine search already enumerates candidate `Every`
  pairs.

- **044** (`atMost_trans`) does *not* reduce through composing `exist_nl`
  into `mono_nl`'s search - `mono_nl_compose` still can't close it, and
  correctly so, since nothing here was ever missing a *shape* fact for
  it. Re-derived from scratch afterward (not by this file, see
  `Tactic.lean`'s Phase 5 and `GQ.lean`'s `entails_narrow`), the actual
  gap was a different axis entirely: the licensing fact `atMost_trans`
  needs is never flat, only *conditioned* on an auxiliary restrictor. 044
  is closed by plain `mono_nl` now, needing no composition at all - see
  `CrossCheck.lean`'s header for exactly why.

## The composition itself

`Tactic.lean`'s `searchMonoNl` was factored out of `mono_nl` specifically
to make this possible without a reverse import: it takes a
`computeExtra : List LocalDecl → MetaM (Array (Expr × Lean.Name))`
parameter supplying *extra* candidate "shape" facts (proof term + a
display label) alongside real local hypotheses. `enumerateExtraShapeFacts`
below is that parameter for this file's `mono_nl_compose`: for every
local hypothesis (or pair of hypotheses), it tries each principle
*without* a specific target restrictor/scope in mind (unlike `exist_nl`
itself, which only looks for one matching a goal it already has) and
collects every fact that results, of *whatever* head - `searchMonoNl`'s
shape-matching loop already compares heads generically, so a candidate
whose head doesn't match the current goal is simply skipped downstream,
the same way a real but irrelevant local hypothesis already is.
`searchMonoNl`'s own, unchanged-since-Phase-2 logic then decides whether
any of those - or a real hypothesis, exactly as before - actually matches
what the goal needs. Nothing here proves anything the five `exist_nl`
principles or the two new lemmas couldn't already prove on their own; it
only makes those proofs available one level up.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace FraCaS.Section1.Monotonicity

/-- Every fact - of whatever head - that `exist_nl`'s five principles,
`exactly_atLeast`/`exactly_atMost`, or `some_entails_and` can derive from
`hyps`, regardless of any specific target restrictor/scope - see this
file's header. The first block mirrors `exist_nl`'s own two-principle
dispatch (`Existential.lean`) exactly, just without the "does it match my
goal" filter, since here the *caller* (`searchMonoNl`) does that matching
against whatever the real goal turns out to need; the second and third
blocks are Phase 4's additions, in the same style. -/
def enumerateExtraShapeFacts (hyps : List LocalDecl) : MetaM (Array (Expr × Lean.Name)) := do
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
            -- Phase 4: `Exactly n P Q` also gives `AtLeast n P Q` and
            -- `AtMost n P Q` outright (unconditionally - no decidable
            -- side-condition needed, unlike `some_of_exactly` above), via
            -- `Plurals.lean`'s `exactly_atLeast`/`exactly_atMost`. This is
            -- what lets problem 124 close through `mono_nl_compose`
            -- unchanged - see this file's header.
            try
              let proof ← mkAppM ``FraCaS.Section2.exactly_atLeast #[n, dP, dQ, d.toExpr]
              out := out.push (proof, .mkSimple s!"{d.userName} (compose.exactlyAtLeast)")
            catch _ => pure ()
            try
              let proof ← mkAppM ``FraCaS.Section2.exactly_atMost #[n, dP, dQ, d.toExpr]
              out := out.push (proof, .mkSimple s!"{d.userName} (compose.exactlyAtMost)")
            catch _ => pure ()
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

  -- Phase 4: `Some P R` plus `Every P S`, for any `S` sharing `P` as a
  -- restrictor, gives `Some P (fun x => S x ∧ R x)` via `GQ.lean`'s
  -- `some_entails_and` - the exact fact `some_mono_scope` needs whenever
  -- the real entails-fact locally available is *conditioned* on `S`
  -- rather than flat (`some_trans`'s own shape - problem 27's "a few
  -- committee members are from Sweden; all committee members are people;
  -- all people from Sweden are from Scandinavia"). Reuses `everyFacts`
  -- from Principle 1 above - same "for every `Every P _` hypothesis"
  -- enumeration, a different combine this time.
  for (everyDecl, eP, eS) in everyFacts do
    for d in hyps do
      match d.type.getAppFn.constName? with
      | some head =>
        if head == ``FraCaS.Section1.Some then
          if let some (dP, dR) := extractPQ .some d.type.getAppArgs then
            if ← isDefEq dP eP then
              try
                let proof ← mkAppM ``FraCaS.Section1.some_entails_and
                  #[eP, dR, eS, d.toExpr, everyDecl.toExpr]
                out := out.push (proof,
                  .mkSimple s!"{d.userName}+{everyDecl.userName} (compose.someEntailsAnd)")
              catch _ => pure ()
      | none => pure ()

  return out

/-- The Phase-3/4 composed tactic - see this file's header. Tried as a
third fallback (after `mono_nl`, after `exist_nl`) in `Coverage.lean`,
never a replacement for either. -/
elab "mono_nl_compose" : tactic => do
  liftMetaTactic1 fun goal => do
    if ← searchMonoNl enumerateExtraShapeFacts goal then
      return none
    else
      throwError "mono_nl_compose: goal is outside the Phase-3/4 fragment \
        (no single-position substitution closes it even after also trying \
        every fact exist_nl's principles, exactly_atLeast/exactly_atMost, \
        or some_entails_and can synthesize from a differently-headed \
        hypothesis or hypothesis pair; this is a small sound fragment, \
        not a general prover)"

end FraCaS.Section1.Monotonicity
