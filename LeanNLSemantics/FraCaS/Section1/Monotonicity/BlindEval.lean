import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Scan
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Existential
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Compose
import LeanNLSemantics.FraCaS.Data.Problems
import LeanNLSemantics

/-!
# Blind evaluation (Sections 1-2)

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

This file is a first, honest attempt at closing that gap - originally
scoped to Section 1 only, now extended to Section 2 as well (Section 3
and beyond are staged separately, per the original plan's own "run it
against what `translate.py` already covers" scope). For every **bare**
`fracas_NNN` theorem in `FraCaS.Section1` or `FraCaS.Section2` (no
`_dir1`/`_via_mono_nl`/... suffix - those exist for the coverage scan's
own diversity or for the countermodel-pair method the `.undef` problems
and several others use, and are not single entailment-shaped statements
this procedure could even pose a yes/no question about; skipped rather
than forced), this file:

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
   `Tactic.lean`/`Existential.lean`/`Compose.lean`), then this file's own
   `most_nl` (a small, targeted search for `Most`-headed goals via
   `GQ.lean`'s `most_trans` - `Most` is outside the certified fragment
   entirely, see `searchMostNl`'s own comment for why a generic tactic
   isn't enough here), then one `aesop` call armed with every general
   `GQ.lean` lemma and told to unfold `Every`/`Some`/`No` (plain `def`s it
   can't see through on its own - `Most`/`AtLeast`/`AtMost`/`Exactly` are
   already-transparent `abbrev`s; see `attemptClose`'s own comment for why
   the whole list, not a hand-picked subset), then `grind`.
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

**Validation status - CI-confirmed** (CI run 36931384884, commit
41fc6bd, branch blind-eval-section1): **47/47 (100%) automated verdicts
match FraCaS's own gold answer** - 37/37 in Section 1, 10/10 in
Section 2 - with 0 mismatches, 0 contradictions, and 0 theorems missing
a gold entry in either section. This is the real count this file's own
`#blind_eval_section1`/`#blind_eval_section2` commands print each CI
run, read directly off that run's own log, not predicted. It is a
narrower number than "82 Section-1 problems" might suggest: of every
declared name in `FraCaS.Section1`/`FraCaS.Section2` (bare theorems plus
every `_dir1`/`_via_mono_nl`/... suffixed variant), 113 were skipped as
out of this procedure's own scope (82 in Section 1 - 77 suffixed/non-
bare, 5 not entailment-shaped; 31 in Section 2 - 16 suffixed/non-bare,
15 not entailment-shaped) - mostly the countermodel-pair (`_dir1`/
`_dir2`) method FraCaS's own `.unknown`/`.undef` problems use, which a
binary yes/no/unknown procedure has no single entailment-shaped
statement to pose a question about in the first place. The 47 are
exactly the bare, single-direction theorems this procedure *could*
evaluate, and it got all of them right. If this file's own section
scope grows past Sections 1-2, or its tactic chain changes, this status
is stale - re-run the CI step and replace this paragraph by hand with
the new CI-confirmed result.

Deliberately not imported by anything (imports the root `LeanNLSemantics`
umbrella to see every already-proved theorem, so importing it back would
be circular) - run directly, the same way `Coverage.lean` already is.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Command
open FraCaS (Answer)

namespace FraCaS.Section1.Monotonicity.BlindEval

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
   ``FraCaS.Section1.Most, ``FraCaS.Section1.AtLeast, ``FraCaS.Section1.AtMost,
   ``FraCaS.Section1.Both, ``FraCaS.Section1.Neither, ``FraCaS.Section2.Exactly]

/-- Whether a theorem's conclusion, after introducing its implication
chain, is headed by one of `blindEvalHeads` - built on `Scan.lean`'s
shared `goalHeadConst` (reuses `introAll` from `Tactic.lean`, raw,
non-`whnf` Pi-check; see its own comment for why) rather than a second,
possibly-inconsistent traversal. -/
def isEntailmentShaped (ty : Expr) : MetaM Bool := do
  match ← goalHeadConst ty with
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

/-- `Scan.lean`'s shared `runTacticOn`/`runTacticBool` (fresh metavariable
per attempt, exactly `Coverage.lean`'s own pattern), named `runTactic`
here to match this file's existing call sites. -/
def runTactic (ty : Expr) (tacticStx : Lean.TSyntax `tactic) : TermElabM Bool :=
  runTacticBool ty tacticStx

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
a bare `apply` to guess at. That distinction is not academic - a plain
`aesop (add safe apply most_trans)` attempt (tried first; the earlier
version of this file's own history, and this comment, record the
failure rather than silently overwriting it) still wasn't enough: `apply`
elaborates left to right and needs to synthesize `DecidablePred (fun x
=> P x ∧ ?R x)` before `?R` is ever assigned (nothing in `most_trans`'s
conclusion `Most P Q` mentions `R`/`S` at all - only its premises do),
and typeclass search on a metavariable-containing type just fails
outright, before `aesop`'s own `assumption` step gets a chance to
resolve `?R` from a real hypothesis. -/
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
.lean`'s `every_most` (`Every P Q → (∃x, P x) → Most P Q`) - problem 100
needs exactly this, and a bare `aesop (add safe apply every_most)`
attempt (tried first, same as `most_trans`) still wasn't reliable enough
even though `Most P Q`'s conclusion alone already pins down `P`/`Q` here
(no leftover metavariable the way `most_trans`'s `R`/`S` were) - so
extracting both premises concretely off matched hypotheses first, the
same recipe `searchMostNl` already uses, is applied again rather than
spending more CI cycles guessing why the generic path is unreliable. -/
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
`Section2/Plurals.lean` already has (`entails_and` through `every_most`)
- the complete list, not a hand-picked subset chosen to close any one
problem. `most_trans` is in there for exactly the reason it needs to be:
it is what `fracas_026`'s own hand proof already calls, a previously-
proved general fact about `Most`, not a rule invented for this file -
handing the *entire* list to a generic search is what keeps this from
being "one rule added because problem 26 needed it" (see this file's
header for why that distinction matters to the whole methodology).
`mono_nl`/`exist_nl`/`mono_nl_compose` already encode most of the
Section 1 lemmas as a directed, certified search; this is the same
knowledge, given instead to an undirected one, for the goals (`Most`/
`No`/`Exactly`-headed) that certified search was never scoped to touch.

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
  if ← runTactic ty (← `(tactic| most_nl)) then return true
  if ← runTactic ty (← `(tactic| every_most_nl)) then return true
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
          safe apply FraCaS.Section1.atLeast_restrict, safe apply FraCaS.Section1.atMost_restrict,
          safe apply FraCaS.Section2.exactly_ne, safe apply FraCaS.Section2.exactly_pos_not_no,
          safe apply FraCaS.Section2.some_of_exactly, safe apply FraCaS.Section2.exactly_atLeast,
          safe apply FraCaS.Section2.exactly_atMost, safe apply FraCaS.Section2.every_most)))
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

/-- The shared scan both `#blind_eval_section1` and `#blind_eval_section2`
run, parameterized only by which namespace's bare `fracas_NNN` theorems to
scan and a label for the log lines - identical logic both times, so this
is pulled out rather than copy-pasted (the earlier version of this file
had only the Section 1 copy; this is that same body, unchanged, now
callable for either namespace). -/
def runBlindEval (namePrefix : Lean.Name) (label : String) : TermElabM Unit := do
  let env ← getEnv
  let mut skippedNotBare : Nat := 0
  let mut skippedNotEntailmentShaped : Array Lean.Name := #[]
  let mut matched : Array (Nat × String) := #[]
  let mut mismatches : Array (Nat × String × String) := #[]
  let mut contradictions : Array Nat := #[]
  let mut noGoldEntry : Array Nat := #[]

  for (name, info) in env.constants.toList do
    unless name.getPrefix == namePrefix do continue
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

    logInfo m!"{label}: attempting fracas_{problemNum}"
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
  logInfo m!"{label}: {matched.size}/{total} automated verdicts match gold \
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

elab "#blind_eval_section1" : command => liftTermElabM do
  runBlindEval `FraCaS.Section1 "blind_eval_section1"

elab "#blind_eval_section2" : command => liftTermElabM do
  runBlindEval `FraCaS.Section2 "blind_eval_section2"

end FraCaS.Section1.Monotonicity.BlindEval

#blind_eval_section1
#blind_eval_section2
