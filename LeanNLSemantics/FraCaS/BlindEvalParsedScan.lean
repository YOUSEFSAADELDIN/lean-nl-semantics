import LeanNLSemantics.FraCaS.Section1.Monotonicity.BlindEvalCore
import LeanNLSemantics.FraCaS.BlindEvalParsed

/-!
# End-to-end blind evaluation scan

Runs the same `attemptClose` chain, with the same polarity-aware
`flipConclusion`/`isNegHead` logic as `runBlindEvalGeneric`, over the
claims in `BlindEvalParsed.lean` - FraCaS problems translated from their
original English with no human in the translation step (see
`scripts/gen_blind_eval_parsed.py`). So unlike every other scan, a
mismatch here can come from the parse, the reading ranker, `translate.py`,
the generic assembly, or a background-knowledge premise the pipeline
deliberately never supplies - not only from the inference step.

Deliberately not imported by anything - run directly, as its own CI step.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open FraCaS.Section1.Monotonicity (goalHeadConst)
open FraCaS.Section1.Monotonicity.BlindEval
  (attemptClose flipConclusion isNegHead answerMatches answerToString withFreshBudget)

namespace FraCaS.BlindEvalParsedScan

elab "#blind_eval_parsed" : command => liftTermElabM do
  let env ← getEnv
  let mut matched : Array (Nat × String) := #[]
  let mut mismatches : Array (Nat × String × String) := #[]
  let mut contradictions : Array Nat := #[]
  let mut missing : Array Nat := #[]
  let mut errored : Array (Nat × String) := #[]

  for (idn, gold, claimName) in FraCaS.blindEvalParsedRegistry do
    let some ty := (env.find? claimName).bind (·.value?)
      | do
        missing := missing.push idn
        continue
    logInfo m!"blind_eval_parsed: attempting fracas_{idn}"
    let result ← withFreshBudget
      (do
        let isNeg := isNegHead (← goalHeadConst ty)
        let closesAsWritten ← attemptClose ty
        let closesFlipped ← attemptClose (← flipConclusion ty)
        let hypClose := if isNeg then closesFlipped else closesAsWritten
        let notHypClose := if isNeg then closesAsWritten else closesFlipped
        pure (.ok (hypClose, notHypClose) : Except String (Bool × Bool)))
      (fun e => do
        let msg ← try e.toMessageData.toString catch _ => pure "<error message could not be rendered>"
        pure (.error msg))
    match result with
    | .error msg => errored := errored.push (idn, msg)
    | .ok (hypClose, notHypClose) =>
      let decision :=
        if hypClose && !notHypClose then "yes"
        else if notHypClose && !hypClose then "no"
        else if !hypClose && !notHypClose then "unknown"
        else "contradiction"
      if decision == "contradiction" then
        contradictions := contradictions.push idn
      else if answerMatches gold decision then
        matched := matched.push (idn, decision)
      else
        mismatches := mismatches.push (idn, answerToString gold, decision)

  let total := matched.size + mismatches.size + contradictions.size + missing.size + errored.size
  logInfo m!"blind_eval_parsed: {matched.size}/{total} automated verdicts match gold \
    ({contradictions.size} contradictions, {missing.size} missing claim constants, \
    {errored.size} errored during attempt)"
  logInfo m!"matched [{matched.size}]: {matched.toList}"
  logInfo m!"mismatches (problem, gold, automated) [{mismatches.size}]: {mismatches.toList}"
  logInfo m!"contradictions (both directions closed - flag, do not silently resolve) \
    [{contradictions.size}]: {contradictions.toList}"
  logInfo m!"missing claim constants [{missing.size}]: {missing.toList}"
  logInfo m!"errored during attempt [{errored.size}]: {errored.toList}"

end FraCaS.BlindEvalParsedScan

#blind_eval_parsed
