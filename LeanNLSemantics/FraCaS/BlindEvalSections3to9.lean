import LeanNLSemantics.FraCaS.Section1.Monotonicity.BlindEvalCore
import LeanNLSemantics

/-!
# Blind evaluation (Sections 3-9)

`BlindEval.lean` (Sections 1-2 only) restricts its scan to theorems whose
conclusion is headed by one of the fixed generalized-quantifier names
(`Every`/`Some`/`Most`/...) — a real restriction there, since Section 1/2's
own `Signature.lean` table and this corpus's certified monotonicity
fragment are both built around exactly that closed vocabulary, and a bare
theorem headed by anything else genuinely isn't a question this
procedure's own tactics have anything to say about.

Sections 3-9 have no equivalent shared vocabulary to restrict to in the
first place: each section's own "approach" header (`Section3/Anaphora
.lean`, `Section6/Comparatives.lean`, `Section9/Attitudes.lean`, ...)
describes bespoke, per-problem hypotheses over free predicate/individual
variables - possessive-pronoun bundles, Skolem-function donkey readings,
cardinal `Nat` comparisons, assumed factivity-connecting facts - with no
small fixed head-symbol algebra the way Section 1's GQ layer has. Most of
these sections' own headers say outright that **no new lemmas are
needed**: the "semantic" step was already folded into each problem's own
premises (an assumed connecting fact, a Skolem function, a literal `Nat`
inequality), leaving genuinely generic first-order/propositional
reasoning - or `Section1.Every`/`Some` reused unchanged, wherever a
problem's standard is itself quantified (`Comparatives.lean`'s header) -
to get from premises to hypothesis. So this scan drops the shape
restriction entirely and attempts every bare `fracas_NNN` theorem in
Sections 3-9, regardless of its conclusion's head, via the exact same
`attemptClose`/`negateConclusion` pipeline `BlindEvalCore.lean` already
provides (now including `omega` in its fallback chain - see that file's
own header for why that one addition was needed specifically for this
scan's cardinal-comparative problems).

This still skips every suffixed name (`_dir1`/`_dir2`/`_from_gf`/...) the
same way `BlindEval.lean` does, for the same reason: a countermodel pair
isn't a single entailment-shaped statement this binary procedure has
anything to pose a question about. Extending the generic-Prop
countermodel-pair technique `BlindEvalUnknownScan.lean` built for
Sections 1-2's 46 `.unknown`/`.undef` problems to these sections' own
(likely larger, given how much more `.unknown`-heavy anaphora/ellipsis/
attitude-opacity judgments tend to be) countermodel pairs is separate,
not-yet-attempted follow-up work, scoped on its own rather than folded
into this file.

Deliberately not imported by anything (imports the root `LeanNLSemantics`
umbrella to see every already-proved theorem, so importing it back would
be circular) - run directly, the same way `BlindEval.lean`/`Coverage.lean`
already are.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Command
open FraCaS (Answer)
open FraCaS.Section1.Monotonicity.BlindEval (attemptClose negateConclusion)

namespace FraCaS.BlindEvalSections3to9

/-- The FraCaS problem number a **bare** `fracas_NNN` name names - `none`
for anything with a trailing suffix. Identical in spirit to `BlindEval
.lean`'s own `bareProblemId`; duplicated rather than imported, since that
copy lives inside `BlindEval.lean` itself, which (like this file) has no
persistent `.olean` for anything else to import against - see this file's
own header and `BlindEvalCore.lean`'s for the same reasoning applied to
`attemptClose`/`negateConclusion`. -/
def bareProblemId (n : Lean.Name) : Option Nat :=
  let s := (toString n).splitOn "." |>.getLast!
  if "fracas_".isPrefixOf s then
    let rest := s.drop "fracas_".length
    if !rest.isEmpty && rest.all Char.isDigit then rest.toNat? else none
  else
    none

/-- `Answer.yes`/`.no` compared directly; `.unknown` and `.undef` both
match an automated `"unknown"` verdict - see `BlindEval.lean`'s header for
why those two gold cases aren't distinguished here. -/
def answerMatches (gold : Answer) (decision : String) : Bool :=
  match gold, decision with
  | .yes, "yes" => true
  | .no, "no" => true
  | .unknown, "unknown" => true
  | .undef, "unknown" => true
  | _, _ => false

def answerToString : Answer → String
  | .yes => "yes"
  | .no => "no"
  | .unknown => "unknown"
  | .undef => "undef"

/-- The shared scan every `#blind_eval_section{3..9}` command runs,
parameterized only by which namespace's bare `fracas_NNN` theorems to
scan and a label for the log lines - the same structure as `BlindEval
.lean`'s own `runBlindEval`, minus its shape restriction (see this file's
header) and with a per-theorem `try/catch` added, since these sections'
proof shapes are far more varied than Section 1/2's and one unanticipated
shape genuinely shouldn't be able to abort the whole scan. -/
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
      unless ((toString name).splitOn "." |>.getLast!).startsWith "fracas_" do continue
      skippedNotBare := skippedNotBare + 1
      continue

    let ty := info.type
    logInfo m!"{label}: attempting fracas_{problemNum}"
    -- `try`/`catch` is kept strictly expression-level (bound via `←`),
    -- never wrapping a `continue` directly - the same shape `Scan.lean`'s
    -- own `runTacticOn` and `BlindEval.lean`'s `isEntailmentShaped` call
    -- already use, rather than a new, unverified interaction between
    -- `continue`/`break` and `catch` with no local compiler to check it.
    let result ←
      try
        let posOk ← attemptClose ty
        let tyNeg ← negateConclusion ty
        let negOk ← attemptClose tyNeg
        pure (.ok (posOk, negOk) : Except String (Bool × Bool))
      catch e =>
        let msg ← try e.toMessageData.toString catch _ => pure "<error message could not be rendered>"
        pure (.error msg)

    match result with
    | .error msg => errored := errored.push (problemNum, msg)
    | .ok (posOk, negOk) =>
      let decision :=
        if posOk && !negOk then "yes"
        else if negOk && !posOk then "no"
        else if !posOk && !negOk then "unknown"
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

elab "#blind_eval_section3" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section3 "blind_eval_section3"

elab "#blind_eval_section4" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section4 "blind_eval_section4"

elab "#blind_eval_section5" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section5 "blind_eval_section5"

elab "#blind_eval_section6" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section6 "blind_eval_section6"

elab "#blind_eval_section7" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section7 "blind_eval_section7"

elab "#blind_eval_section8" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section8 "blind_eval_section8"

elab "#blind_eval_section9" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section9 "blind_eval_section9"

end FraCaS.BlindEvalSections3to9

#blind_eval_section3
#blind_eval_section4
#blind_eval_section5
#blind_eval_section6
#blind_eval_section7
#blind_eval_section8
#blind_eval_section9
