import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Scan
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Existential
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Compose
import LeanNLSemantics.FraCaS.Data.Problems

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

set_option hygiene false in
/-- The armed `aesop` step of `attemptClose`: told to unfold the plain-
`def` quantifiers it can't see through on its own (`Every`/`Some`/`No` -
`Most`/`AtLeast`/`AtMost`/`Exactly` are already-reducible `abbrev`s), and
armed with every general (not problem-specific) composition/entailment
lemma `GQ.lean` **and** `Section2/Plurals.lean` has - the complete list,
not a hand-picked subset chosen to close any one problem.

**History, stated plainly because it changed published numbers' meaning:**
until this macro existed, `attemptClose` inlined this call with
`unfold FraCaS.Section1.Every` (no phase) and `safe apply ...` rules.
Aesop requires an explicit phase on `unfold` rules (`norm unfold`), so
*every* invocation failed while building its rule set, before searching
at all - `phase (safe/unsafe/norm) not specified.`, read directly off CI
run 37168342088's per-tactic diagnostics. Because `runTacticOn` turns any
error into an ordinary "did not close", this was completely silent: every
blind-evaluation result published before the fix came from the other
steps of the chain alone, never from `aesop`. The `example`s right below
this macro now make that failure mode a *build* error instead.

`no_iff_not_some` is an `Iff`, so it is a `simp` rule rather than an
`apply` rule (Aesop warns that `apply` on an `A ↔ B` conclusion is almost
never what's meant). The other lemma rules are `unsafe 50%` rather than
`safe`: safe rules are never
backtracked, and once `Every`/`Some` are unfoldable, `apply` can unify
some of these lemmas' conclusions (`entails_refl : Every P P`, unfolding
to `∀ x, P x → P x`) with almost any atomic goal, making no progress -
as a safe rule that dead end would be permanent. -/
macro "blind_aesop" : tactic => `(tactic|
  aesop
    (add norm unfold FraCaS.Section1.Every, norm unfold FraCaS.Section1.Some,
      norm unfold FraCaS.Section1.No,
      unsafe 50% apply FraCaS.Section1.entails_and, unsafe 50% apply FraCaS.Section1.entails_refl,
      unsafe 50% apply FraCaS.Section1.some_entails_and,
      unsafe 50% apply FraCaS.Section1.entails_narrow,
      unsafe 50% apply FraCaS.Section1.every_some,
      unsafe 50% apply FraCaS.Section1.some_of_nonempty,
      unsafe 50% apply FraCaS.Section1.every_trans, unsafe 50% apply FraCaS.Section1.every_mp,
      norm simp FraCaS.Section1.no_iff_not_some,
      unsafe 50% apply FraCaS.Section1.atLeast_some, unsafe 50% apply FraCaS.Section1.most_some,
      unsafe 50% apply FraCaS.Section1.some_mono_scope,
      unsafe 50% apply FraCaS.Section1.every_mono_scope,
      unsafe 50% apply FraCaS.Section1.atLeast_mono_scope,
      unsafe 50% apply FraCaS.Section1.some_trans, unsafe 50% apply FraCaS.Section1.most_trans,
      unsafe 50% apply FraCaS.Section1.atMost_trans,
      unsafe 50% apply FraCaS.Section1.atMost_mono_scope,
      unsafe 50% apply FraCaS.Section1.atMost_mono_scope_conditioned,
      unsafe 50% apply FraCaS.Section1.some_restrict,
      unsafe 50% apply FraCaS.Section1.every_restrict,
      unsafe 50% apply FraCaS.Section1.atLeast_restrict,
      unsafe 50% apply FraCaS.Section1.atMost_restrict,
      unsafe 50% apply FraCaS.Section2.exactly_ne,
      unsafe 50% apply FraCaS.Section2.exactly_pos_not_no,
      unsafe 50% apply FraCaS.Section2.some_of_exactly,
      unsafe 50% apply FraCaS.Section2.exactly_atLeast,
      unsafe 50% apply FraCaS.Section2.exactly_atMost,
      unsafe 50% apply FraCaS.Section2.every_most))

set_option hygiene false in
/-- The same unfolding with no lemma rules at all - a fallback in case the
armed call's larger search spends its budget on lemma applications a
plain search wouldn't need. -/
macro "blind_aesop_unfold" : tactic => `(tactic|
  aesop
    (add norm unfold FraCaS.Section1.Every, norm unfold FraCaS.Section1.Some,
      norm unfold FraCaS.Section1.No))

set_option hygiene false in
/-- `grind`, told to unfold the same three plain-`def` quantifiers (plain
`grind` never sees inside them - it fails on `Every P Q → P x → Q x`,
CI run 37168342088). -/
macro "blind_grind" : tactic => `(tactic|
  grind [FraCaS.Section1.Every, FraCaS.Section1.Some, FraCaS.Section1.No])

-- Canaries: if either `aesop` rule set ever stops building (the silent
-- failure documented on `blind_aesop`), or `blind_grind` stops seeing
-- through the quantifier defs, these fail `lake build` itself.
example {A : Type} (P Q : A → Prop) (x : A) :
    FraCaS.Section1.Every P Q → P x → Q x := by blind_aesop
example {A : Type} (P Q : A → Prop) :
    FraCaS.Section1.No P Q → ¬ FraCaS.Section1.Some P Q := by blind_aesop
example {A : Type} (P Q : A → Prop) (x : A) :
    FraCaS.Section1.Every P Q → P x → Q x := by blind_aesop_unfold
example {A : Type} (P Q : A → Prop) (x : A) :
    FraCaS.Section1.Every P Q → P x → Q x := by blind_grind

/-- Runs one *problem's* whole evaluation (not just one tactic attempt -
`runTacticOn` already isolates those) with a fresh heartbeat budget,
catching a resource-limit failure as an ordinary error via `h`. The scan
loops' own bookkeeping between attempts (`goalHeadConst`, `flipConclusion`,
`negateConclusion` - all of which can `whnf`) is otherwise charged against
the *whole* scanning command's cumulative count: CI run 37169187753, the
first run with a working `aesop`, crossed 200000 heartbeats that way at
`fracas_011` and the uncaught runtime exception aborted the rest of
Section 1's scan. -/
def withFreshBudget {α : Type} (x : TermElabM α) (h : Exception → TermElabM α) : TermElabM α :=
  withCurrHeartbeats <| tryCatchRuntimeEx x h

/-- The fixed tactic chain both directions get, in order: this corpus's
own certified monotonicity fragment first (`mono_nl`, `exist_nl`,
`mono_nl_compose`), then `most_nl`/`every_most_nl`, then `blind_aesop`
and its unarmed fallback `blind_aesop_unfold`, then plain `grind` and
`blind_grind`, then `intros; omega` as a last resort (several Sections
3-9 problems - FraCaS's own cardinal comparatives in particular, see
`Section6/Comparatives.lean`'s own header - are literal `Nat`
inequalities their own hand proofs already close with bare `omega`;
`intros` first since `omega` doesn't peel leading implications itself).
Stops at the first success. Every step is a sound, kernel-checked proof
search, so adding steps can only turn "unknown" into a verdict the
translated `Prop` genuinely supports, or expose jointly inconsistent
premises as a flagged contradiction - a resulting mismatch with gold then
points at the translation, never at the search. -/
def attemptClose (ty : Expr) : TermElabM Bool := do
  if ← runTacticBool ty (← `(tactic| mono_nl)) then return true
  if ← runTacticBool ty (← `(tactic| exist_nl)) then return true
  if ← runTacticBool ty (← `(tactic| mono_nl_compose)) then return true
  if ← runTacticBool ty (← `(tactic| most_nl)) then return true
  if ← runTacticBool ty (← `(tactic| every_most_nl)) then return true
  if ← runTacticBool ty (← `(tactic| blind_aesop)) then return true
  if ← runTacticBool ty (← `(tactic| blind_aesop_unfold)) then return true
  if ← runTacticBool ty (← `(tactic| grind)) then return true
  if ← runTacticBool ty (← `(tactic| blind_grind)) then return true
  if ← runTacticBool ty (← `(tactic| (intros; omega))) then return true
  return false

/-- Whether a (post-Pi-peeling) head constant name is a negation
`flipConclusion` knows how to strip - `Not` directly, or `Ne` (`a ≠ b`),
itself a separate `def` wrapping `Not (a = b)`, so a raw, non-unfolding
head check sees `Ne`, not `Not` (CI run 37157413753: `fracas_278/279/282/
289`, all literal `_ ≠ _` conclusions, were still mislabeled after a
`Not`-only first version). -/
def isNegHead (headName : Option Lean.Name) : Bool :=
  headName == some ``Not || headName == some ``Ne

/-- Like `negateConclusion`, but polarity-aware: strips a leading negation
from the conclusion instead of wrapping a second one around it, when the
conclusion is already negated (`Not`, or `Ne` - see `isNegHead`). Bare
theorems state a `.no` gold answer either way - as a positive hypothesis
whose negation must be derived, or by writing `¬ hypothesis` (`fracas_006`,
`fracas_210`) or `a ≠ b` (`fracas_279`) as the literal conclusion - and
wrapping a second `Not` around an already-negated conclusion asks for a
different, usually-false claim, mislabeling a correct inference as a
mismatch. -/
partial def flipConclusion (ty : Expr) : MetaM Expr := do
  if ty.isForall then
    forallBoundedTelescope ty (some 1) fun fvars body => do
      let body' ← flipConclusion body
      mkForallFVars fvars body'
  else
    match ty.getAppFn.constName? with
    | some ``Not => return ty.getAppArgs[0]!
    | some ``Ne =>
      -- `Ne {α} (a b : α)`: whatever precedes them, the last two
      -- arguments of a fully-applied `Ne` are always `a`/`b`.
      let args := ty.getAppArgs
      mkEq args[args.size - 2]! args[args.size - 1]!
    | _ => mkAppM ``Not #[ty]

/-- The FraCaS problem number a **bare** `fracas_NNN` name names - `none`
for anything with a trailing suffix (`_dir1`/`_dir2`, `_via_mono_nl`,
`_from_gf`, ...): countermodel pairs and re-derivations are not single
entailment-shaped statements to pose a yes/no question about (the
countermodel pairs are evaluated separately, via `BlindEvalUnknown*.lean`'s
generalized claims). -/
def bareProblemId (n : Lean.Name) : Option Nat :=
  let s := lastComponent n
  if "fracas_".isPrefixOf s then
    let rest := s.drop "fracas_".length
    if !rest.isEmpty && rest.all Char.isDigit then rest.toNat? else none
  else
    none

/-- `Answer.yes`/`.no` compared directly; `.unknown` and `.undef` both
match an automated `"unknown"` verdict - a binary yes/no/unknown procedure
cannot tell "genuinely undecided" apart from "the source's answer wasn't a
literal yes/no/don't-know", so that distinction is collapsed rather than
claimed. -/
def answerMatches (gold : FraCaS.Answer) (decision : String) : Bool :=
  match gold, decision with
  | .yes, "yes" => true
  | .no, "no" => true
  | .unknown, "unknown" => true
  | .undef, "unknown" => true
  | _, _ => false

/-- `Answer` has no `ToMessageData` instance, so log lines use this. -/
def answerToString : FraCaS.Answer → String
  | .yes => "yes"
  | .no => "no"
  | .unknown => "unknown"
  | .undef => "undef"

/-- The one bare-theorem scan every section's `#blind_eval_sectionN`
command runs (`BlindEval.lean` for Sections 1-2, `BlindEvalSections3to9
.lean` for 3-9), parameterized only by which namespace's bare
`fracas_NNN` theorems to scan and a label for the log lines. Attempts
**every** bare theorem regardless of its conclusion's shape - the earlier
Sections 1-2 version restricted itself to conclusions headed by a
generalized quantifier, which turned out not to be load-bearing (see
`BLIND_EVAL.md`) - posing "does the hypothesis follow" and "does its
negation follow" via `attemptClose`, with `flipConclusion`/`isNegHead`
keeping the two straight whichever polarity the theorem's own conclusion
was written in. Each theorem's evaluation runs under `withFreshBudget`, so one
unanticipated shape or one expensive search is reported as "errored"
rather than aborting the whole scan. -/
def runBlindEvalGeneric (namePrefix : Lean.Name) (label : String) : TermElabM Unit := do
  let env ← getEnv
  let mut skippedNotBare : Nat := 0
  let mut matched : Array (Nat × String) := #[]
  let mut mismatches : Array (Nat × String × String) := #[]
  let mut contradictions : Array Nat := #[]
  let mut noGoldEntry : Array Nat := #[]
  let mut errored : Array (Nat × String) := #[]

  for (name, info) in env.constants.toList do
    unless name.getPrefix == namePrefix do continue
    unless info.isTheorem do continue
    let some problemNum := bareProblemId name | do
      unless (lastComponent name).startsWith "fracas_" do continue
      skippedNotBare := skippedNotBare + 1
      continue

    let ty := info.type
    logInfo m!"{label}: attempting fracas_{problemNum}"
    let result ← withFreshBudget
      (do
        let isNeg := isNegHead (← goalHeadConst ty)
        let closesAsWritten ← attemptClose ty
        let tyFlipped ← flipConclusion ty
        let closesFlipped ← attemptClose tyFlipped
        -- which query closes the raw hypothesis vs. its negation depends
        -- on whether the theorem's own conclusion already is the negation
        let hypClose := if isNeg then closesFlipped else closesAsWritten
        let notHypClose := if isNeg then closesAsWritten else closesFlipped
        pure (.ok (hypClose, notHypClose) : Except String (Bool × Bool)))
      (fun e => do
        let msg ← try e.toMessageData.toString catch _ => pure "<error message could not be rendered>"
        pure (.error msg))

    match result with
    | .error msg => errored := errored.push (problemNum, msg)
    | .ok (hypClose, notHypClose) =>
      let decision :=
        if hypClose && !notHypClose then "yes"
        else if notHypClose && !hypClose then "no"
        else if !hypClose && !notHypClose then "unknown"
        else "contradiction"

      if decision == "contradiction" then
        contradictions := contradictions.push problemNum
      else
        match FraCaS.problems.find? (·.id == problemNum) with
        | none => noGoldEntry := noGoldEntry.push problemNum
        | some problem =>
          if answerMatches problem.answer decision then
            matched := matched.push (problemNum, decision)
          else
            mismatches := mismatches.push (problemNum, answerToString problem.answer, decision)

  let total := matched.size + mismatches.size + contradictions.size + noGoldEntry.size + errored.size
  logInfo m!"{label}: {matched.size}/{total} automated verdicts match gold \
    ({skippedNotBare} skipped as suffixed/non-bare, \
    {contradictions.size} contradictions, {noGoldEntry.size} with no gold entry, \
    {errored.size} errored during attempt)"
  logInfo m!"matched [{matched.size}]: {matched.toList}"
  logInfo m!"mismatches [{mismatches.size}]: {mismatches.toList}"
  logInfo m!"contradictions (both directions closed - flag, do not silently resolve) \
    [{contradictions.size}]: {contradictions.toList}"
  logInfo m!"no gold entry [{noGoldEntry.size}]: {noGoldEntry.toList}"
  logInfo m!"errored during attempt (flag - an unanticipated proof shape, not a yes/no/unknown \
    verdict) [{errored.size}]: {errored.toList}"

end FraCaS.Section1.Monotonicity.BlindEval
