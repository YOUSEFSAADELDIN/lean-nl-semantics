import EndToEnd
import EndToEnd.Encodings.Section5
import EndToEnd.Encodings.Commitments

/-!
# Noun encodings compared: FraCaS Section 5

Scores FraCaS Section 5 in four encodings (`EndToEnd/Encodings/
README.md`) with one generic prover: `aesop`, then `grind`, each told only
to unfold the quantifier definitions F's claims use (`Every`, `Some`,
`No`). F (the pipeline's own claims, with background knowledge) is also
scored with the pipeline's own prover, for reference.

Not part of any library - run directly, as its own CI job.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open FraCaS.Section1.Monotonicity (runTacticBool)
open FraCaS.Section1.Monotonicity.BlindEval (answerMatches answerToString withFreshBudget)

namespace FraCaS.Encodings.Scan

/-- The one prover every encoding gets. -/
def attemptGeneric (ty : Expr) : TermElabM Bool := do
  if ← runTacticBool ty (← `(tactic| blind_aesop_unfold)) then return true
  if ← runTacticBool ty (← `(tactic| blind_grind)) then return true
  return false

def prove (prover : Expr → TermElabM Bool) (n : Lean.Name) : TermElabM String := do
  match (← getEnv).find? n |>.bind (·.value?) with
  | none => return "m"
  | some ty => withFreshBudget (do pure (if ← prover ty then "1" else "0")) (fun _ => pure "e")

def verdict (yes no : List String) : String :=
  let y := !yes.isEmpty && yes.all (· == "1")
  let n := !no.isEmpty && no.all (· == "1")
  if y && n then "contradiction" else if y then "yes" else if n then "no" else "unknown"

def report (label : String) (rows : List (Nat × FraCaS.Answer × String)) : TermElabM Unit := do
  let matched := rows.filter fun (_, g, v) => answerMatches g v
  let wrong := rows.filter fun (_, g, v) => v != "unknown" && !answerMatches g v
  logInfo m!"encoding {label}: {matched.length}/{rows.length} match gold, {wrong.length} wrong: \
    {wrong.map fun (i, g, v) => (i, answerToString g, v)}"
  for (i, g, v) in rows do
    logInfo m!"encoding_verdict {label} {i} {answerToString g} {v}"

def runEncoding (label : String) (reg : List (Nat × FraCaS.Answer × Lean.Name × Lean.Name)) :
    TermElabM Unit := do
  let mut rows : List (Nat × FraCaS.Answer × String) := []
  for (i, g, y, n) in reg do
    rows := rows ++ [(i, g, verdict [← prove attemptGeneric y] [← prove attemptGeneric n])]
  report label rows

def runF (label : String) (prover : Expr → TermElabM Bool) : TermElabM Unit := do
  let mut rows : List (Nat × FraCaS.Answer × String) := []
  for (i, g, ys, ns) in FraCaS.EndToEnd.registryBk do
    if 197 ≤ i && i ≤ 219 then
      let yv ← ys.mapM (prove prover)
      let nv ← ns.mapM (prove prover)
      rows := rows ++ [(i, g, verdict yv nv)]
  report label rows

elab "#encoding_scan" : command => liftTermElabM do
  runF "F" attemptGeneric
  runEncoding "P" FraCaS.Encodings.registryP
  runEncoding "W" FraCaS.Encodings.registryW
  runEncoding "M" FraCaS.Encodings.registryM
  runF "F_pipeline_prover" FraCaS.EndToEnd.attemptCloseEndToEnd

end FraCaS.Encodings.Scan

#encoding_scan
