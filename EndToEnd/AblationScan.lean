import EndToEnd
import EndToEnd.Ablations

/-!
# Soundness ablation scan

Scores every claim individually, with no short-circuit: each reading
assignment's "yes" and "no" claim of the baseline (`EndToEnd/Claims.lean`)
and of each ablation (`EndToEnd/Ablations.lean`, the problems whose claims
change when one safeguard is switched off - see `EndToEnd/ablations.py`).
Each line it logs,

  `per_claim LABEL PROBLEM GOLD yes=... no=...`,

has one character per reading assignment: `1` proved, `0` not proved, `e`
the attempt raised an error, `m` the claim is missing.
`EndToEnd/ablation_report.py` turns the log into verdicts under each
reading rule (every reading, one reading, any reading) and counts wrong
answers; recomputing the every-reading rule reproduces `Scan.lean`'s
verdicts, which checks the two scans agree.

Not part of any library - run directly, as its own CI job.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open FraCaS.Section1.Monotonicity.BlindEval (answerToString withFreshBudget)

namespace FraCaS.EndToEnd.AblationScan

/-- One claim, with the scan's fresh budget. -/
def attempt (ty : Expr) : TermElabM String :=
  withFreshBudget
    (do pure (if ← FraCaS.EndToEnd.attemptCloseEndToEnd ty then "1" else "0"))
    (fun _ => pure "e")

def perClaim (names : List Lean.Name) : TermElabM String := do
  let env ← getEnv
  let mut out := ""
  for n in names do
    match (env.find? n).bind (·.value?) with
    | some ty => out := out ++ (← attempt ty)
    | none => out := out ++ "m"
  return out

def runPerClaim (registry : List (Nat × FraCaS.Answer × List Lean.Name × List Lean.Name))
    (label : String) : TermElabM Unit := do
  for (idn, gold, yesNames, noNames) in registry do
    let ys ← perClaim yesNames
    let ns ← perClaim noNames
    logInfo m!"per_claim {label} {idn} {answerToString gold} yes={ys} no={ns}"

elab "#ablation_scan" : command => liftTermElabM do
  runPerClaim FraCaS.EndToEnd.registry "baseline"
  runPerClaim FraCaS.EndToEnd.registryBk "baseline_bk"
  for (name, reg, regBk) in FraCaS.EndToEnd.Ablations.all do
    runPerClaim reg name
    runPerClaim regBk (name ++ "_bk")

end FraCaS.EndToEnd.AblationScan

#ablation_scan
