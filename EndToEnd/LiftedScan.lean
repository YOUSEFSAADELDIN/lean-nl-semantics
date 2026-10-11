import EndToEnd
import EndToEnd.Encodings.Lifted

/-!
# Noun encodings compared, Phase 2: every problem the pipeline reaches

Scores the pipeline's claims with background knowledge (F,
`EndToEnd/Claims.lean`) against the same claims with nouns as types
(`EndToEnd/Encodings/Lifted.lean`: `M`, and `MInj` with injective
embeddings), on the problems whose claims quantify over a noun - on every
other problem the two are the same claim. Each problem's verdict follows
the pipeline's rule: "yes" only if every reading's yes-claim is proved,
"no" only if every reading's no-claim is.

Which encoding and which prover is read from the environment variable
`LIFTED_SCAN` (`F_pipeline`, `M_generic`, ...), so CI runs the six
combinations as parallel jobs. "pipeline" is the pipeline's own prover
(`attemptCloseEndToEnd`); "generic" is `aesop`, then `grind`, as in
`EncodingScan.lean`.

Not part of any library - run directly, by the `encodings-phase2` CI job.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open FraCaS.Section1.Monotonicity (runTacticBool)
open FraCaS.Section1.Monotonicity.BlindEval (answerMatches answerToString withFreshBudget)

namespace FraCaS.Encodings.LiftedScan

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

def run (label : String) (prover : Expr → TermElabM Bool)
    (reg : List (Nat × FraCaS.Answer × List Lean.Name × List Lean.Name)) : TermElabM Unit := do
  let mut rows : List (Nat × FraCaS.Answer × String) := []
  for (i, g, ys, ns) in reg do
    if FraCaS.Encodings.Lifted.typed.contains i then
      let yv ← ys.mapM (prove prover)
      let nv ← ns.mapM (prove prover)
      let v := verdict yv nv
      logInfo m!"lifted_verdict {label} {i} {answerToString g} {v}"
      rows := rows ++ [(i, g, v)]
  let matched := rows.filter fun (_, g, v) => answerMatches g v
  let wrong := rows.filter fun (_, g, v) => v != "unknown" && !answerMatches g v
  logInfo m!"lifted {label}: {matched.length}/{rows.length} match gold, {wrong.length} wrong: \
    {wrong.map fun (i, g, v) => (i, answerToString g, v)}"

elab "#lifted_scan" : command => liftTermElabM do
  let which := (← IO.getEnv "LIFTED_SCAN").getD ""
  let reg := match which.splitOn "_" with
    | "F" :: _ => FraCaS.EndToEnd.registryBk
    | "M" :: _ => FraCaS.Encodings.Lifted.registryMBk
    | "MInj" :: _ => FraCaS.Encodings.Lifted.registryMInjBk
    | _ => []
  let prover := if which.endsWith "_pipeline" then FraCaS.EndToEnd.attemptCloseEndToEnd else attemptGeneric
  if reg.isEmpty then
    throwError "set LIFTED_SCAN to <F|M|MInj>_<pipeline|generic>, got {repr which}"
  run which prover reg

end FraCaS.Encodings.LiftedScan

#lifted_scan
