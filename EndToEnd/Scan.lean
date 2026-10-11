import EndToEnd

/-!
# End-to-end evaluation scan

Runs the end-to-end prover (`EndToEnd/Prover.lean`'s
`attemptCloseEndToEnd`) over the claims in `EndToEnd/Claims.lean` -
FraCaS problems translated from their original English with no human in
the translation step (see `EndToEnd/gen_claims.py`). So unlike the
hand-written corpus's scans, a mismatch here can come from the parse, the
reading ranker, `translate.py`, the generic assembly, or a missing
background-knowledge premise - not only from the inference step.

These are development-set figures: the grammar, translator and prover
were extended by looking at which of these same problems failed.

Not part of any library - run directly, as its own CI job.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open FraCaS.Section1.Monotonicity.BlindEval
  (answerMatches answerToString withFreshBudget)

namespace FraCaS.EndToEnd.Scan

/-- One pass over a registry of end-to-end claims; `label` prefixes the
log lines so the two variants' results are reported separately. -/
def runParsed (registry : List (Nat × FraCaS.Answer × List Lean.Name × List Lean.Name))
    (label : String) : TermElabM Unit := do
  let env ← getEnv
  let mut matched : Array (Nat × String) := #[]
  let mut mismatches : Array (Nat × String × String) := #[]
  let mut contradictions : Array Nat := #[]
  let mut missing : Array Nat := #[]
  let mut errored : Array (Nat × String) := #[]

  for (idn, gold, yesNames, noNames) in registry do
    let yesTys := yesNames.filterMap fun n => (env.find? n).bind (·.value?)
    let noTys := noNames.filterMap fun n => (env.find? n).bind (·.value?)
    if yesTys.length != yesNames.length || noTys.length != noNames.length || yesTys.isEmpty then
      missing := missing.push idn
      continue
    logInfo m!"{label}: attempting fracas_{idn}"
    -- One yes/no claim pair per consistent assignment of readings (see
    -- the generator's header): "yes" only if every yes-claim is proved,
    -- "no" only if every no-claim is - so no verdict depends on choosing
    -- one reading of ambiguous English.
    let result ← withFreshBudget
      (do
        let mut hypClose := true
        for ty in yesTys do
          if hypClose then
            hypClose ← FraCaS.EndToEnd.attemptCloseEndToEnd ty
        let mut notHypClose := true
        for ty in noTys do
          if notHypClose then
            notHypClose ← FraCaS.EndToEnd.attemptCloseEndToEnd ty
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
elab "#end_to_end_eval" : command => liftTermElabM do
  runParsed FraCaS.EndToEnd.registry "end_to_end"

-- The same claims with `EndToEnd/background.py`'s problem-independent
-- background knowledge added as premises (tree-structural entailments and
-- a small degree-semantics lexicon - see that file for the full list).
elab "#end_to_end_eval_bk" : command => liftTermElabM do
  runParsed FraCaS.EndToEnd.registryBk "end_to_end_bk"

end FraCaS.EndToEnd.Scan

#end_to_end_eval
#end_to_end_eval_bk
