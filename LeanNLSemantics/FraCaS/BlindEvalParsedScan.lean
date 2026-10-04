import LeanNLSemantics.FraCaS.Section1.Monotonicity.BlindEvalCore
import LeanNLSemantics.FraCaS.BlindEvalParsed

/-!
# End-to-end blind evaluation scan

Runs the same `attemptClose` chain as `runBlindEvalGeneric` over the
claims in `BlindEvalParsed.lean` - FraCaS problems translated from their
original English with no human in the translation step (see
`scripts/gen_blind_eval_parsed.py`). So unlike every other scan, a
mismatch here can come from the parse, the reading ranker, `translate.py`,
the generic assembly, or a background-knowledge premise the pipeline
deliberately never supplies - not only from the inference step.

Deliberately not imported by anything - run directly, as its own CI step.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open FraCaS.Section1.Monotonicity.BlindEval
  (attemptClose answerMatches answerToString withFreshBudget)

namespace FraCaS.BlindEvalParsedScan

/-- One pass over a registry of end-to-end claims; `label` prefixes the
log lines so the two variants' results are reported separately. -/
def runParsed (registry : List (Nat × FraCaS.Answer × Lean.Name × Lean.Name)) (label : String) :
    TermElabM Unit := do
  let env ← getEnv
  let mut matched : Array (Nat × String) := #[]
  let mut mismatches : Array (Nat × String × String) := #[]
  let mut contradictions : Array Nat := #[]
  let mut missing : Array Nat := #[]
  let mut errored : Array (Nat × String) := #[]

  for (idn, gold, yesName, noName) in registry do
    let some yesTy := (env.find? yesName).bind (·.value?)
      | do
        missing := missing.push idn
        continue
    let some noTy := (env.find? noName).bind (·.value?)
      | do
        missing := missing.push idn
        continue
    logInfo m!"{label}: attempting fracas_{idn}"
    -- Each problem comes as two claims (see the generator's header): the
    -- "yes" claim pairs the weakest reading of the premises with the
    -- strongest of the hypothesis, the "no" claim the weakest of each with
    -- the hypothesis negated - so a verdict holds under every reading.
    let result ← withFreshBudget
      (do
        let hypClose ← attemptClose yesTy
        let notHypClose ← attemptClose noTy
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
  logInfo m!"{label}: {matched.size}/{total} automated verdicts match gold \
    ({contradictions.size} contradictions, {missing.size} missing claim constants, \
    {errored.size} errored during attempt)"
  logInfo m!"matched [{matched.size}]: {matched.toList}"
  logInfo m!"mismatches (problem, gold, automated) [{mismatches.size}]: {mismatches.toList}"
  logInfo m!"contradictions (both directions closed - flag, do not silently resolve) \
    [{contradictions.size}]: {contradictions.toList}"
  logInfo m!"missing claim constants [{missing.size}]: {missing.toList}"
  logInfo m!"errored during attempt [{errored.size}]: {errored.toList}"

-- Without background knowledge: exactly what the parsed English says.
elab "#blind_eval_parsed" : command => liftTermElabM do
  runParsed FraCaS.blindEvalParsedRegistry "blind_eval_parsed"

-- The same claims with `gf/background.py`'s problem-independent
-- background knowledge added as premises (tree-structural entailments and
-- a small degree-semantics lexicon - see that file for the full list).
elab "#blind_eval_parsed_bk" : command => liftTermElabM do
  runParsed FraCaS.blindEvalParsedBkRegistry "blind_eval_parsed_bk"

end FraCaS.BlindEvalParsedScan

#blind_eval_parsed
#blind_eval_parsed_bk
