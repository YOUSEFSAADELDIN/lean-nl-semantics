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
`LIFTED_SCAN` (`F_pipeline`, `M_generic`, ...), so CI runs the
combinations as parallel jobs. "pipeline" is the pipeline's own prover
(`attemptCloseEndToEnd`); "generic" is `aesop`, then `grind`, as in
`EncodingScan.lean`; "transfer" is the pipeline's prover after rewriting
M's quantifiers into F's by the transfer lemmas (`EndToEnd/Encodings/
Typed.lean`).

Not part of any library - run directly, by the `encodings-phase2` CI job.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open FraCaS.Section1.Monotonicity (runTacticBool)
open FraCaS.Section1.Monotonicity.BlindEval (answerMatches answerToString withFreshBudget)

namespace FraCaS.Encodings.LiftedScan

/-- The generic prover, told to unfold the quantifier definitions of
both encodings (F's `Every`/`Some`/`No`, M's `EveryT`/`SomeT`/`NoT` and
`IsA`): each encoding gets its own definitions opened, nothing more. -/
def attemptGeneric (ty : Expr) : TermElabM Bool := do
  if ← runTacticBool ty (← `(tactic|
      aesop (add norm unfold FraCaS.Section1.Every, norm unfold FraCaS.Section1.Some,
        norm unfold FraCaS.Section1.No, norm unfold FraCaS.Encodings.Typed.EveryT,
        norm unfold FraCaS.Encodings.Typed.SomeT, norm unfold FraCaS.Encodings.Typed.NoT,
        norm unfold FraCaS.Encodings.Typed.IsA))) then return true
  if ← runTacticBool ty (← `(tactic|
      grind [FraCaS.Section1.Every, FraCaS.Section1.Some, FraCaS.Section1.No,
        FraCaS.Encodings.Typed.EveryT, FraCaS.Encodings.Typed.SomeT,
        FraCaS.Encodings.Typed.NoT, FraCaS.Encodings.Typed.IsA])) then return true
  return false

/-- M's claim rewritten by the transfer lemmas (`EndToEnd/Encodings/
Typed.lean`) into the pipeline's quantifiers, each noun read as `IsA eN`;
the counting lemmas apply only where the claim states the embedding
injective (MInj). `none` if nothing was rewritten; `some none` if the
rewriting alone proved it. -/
def transfer (ty : Expr) : TermElabM (Option (Option Expr)) := do
  let g ← mkFreshExprMVar ty
  try
    let gs ← Lean.Elab.Tactic.run g.mvarId! do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        simp (config := { contextual := true }) only [FraCaS.Encodings.Typed.every_t,
          FraCaS.Encodings.Typed.some_t, FraCaS.Encodings.Typed.no_t,
          FraCaS.Encodings.Typed.atLeast_t, FraCaS.Encodings.Typed.atMost_t,
          FraCaS.Encodings.Typed.exactly_t, FraCaS.Encodings.Typed.most_t,
          FraCaS.Encodings.Typed.more_t, FraCaS.Encodings.Typed.both_t,
          FraCaS.Encodings.Typed.neither_t, and_true]))
    match gs with
    | [] => return some none
    | [g'] => return some (some (← instantiateMVars (← g'.getType)))
    | _ => return none
  catch _ => return none

/-- The pipeline's prover, after the transfer. -/
def attemptTransfer (ty : Expr) : TermElabM Bool := do
  match ← withFreshBudget (transfer ty) (fun _ => pure none) with
  | some none => return true
  | some (some ty') => FraCaS.EndToEnd.attemptCloseEndToEnd ty'
  | none => FraCaS.EndToEnd.attemptCloseEndToEnd ty

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
  logInfo m!"lifted_matched {label} {matched.map (·.1)}"

elab "#lifted_scan" : command => liftTermElabM do
  let which := (← IO.getEnv "LIFTED_SCAN").getD ""
  let reg := match which.splitOn "_" with
    | "F" :: _ => FraCaS.EndToEnd.registryBk
    | "M" :: _ => FraCaS.Encodings.Lifted.registryMBk
    | "MInj" :: _ => FraCaS.Encodings.Lifted.registryMInjBk
    | _ => []
  let prover := if which.endsWith "_pipeline" then FraCaS.EndToEnd.attemptCloseEndToEnd
    else if which.endsWith "_transfer" then attemptTransfer else attemptGeneric
  if reg.isEmpty then
    throwError "set LIFTED_SCAN to <F|M|MInj>_<pipeline|generic|transfer>, got {repr which}"
  run which prover reg

end FraCaS.Encodings.LiftedScan

#lifted_scan
