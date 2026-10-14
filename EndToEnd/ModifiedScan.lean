import EndToEnd
import EndToEnd.Encodings.Modified
import EndToEnd.Encodings.Pullback

/-!
# Noun encodings compared, Phase 3: the modified nouns of Section 1

Scores the 8 problems the lexical-premise audit tags `noun`
(`EndToEnd/Encodings/Modified.lean`) in five forms: F's own claims
without and with background knowledge (`EndToEnd/Claims.lean`), and P, W
and M, which restate F's fused modified nouns and add no background
knowledge. Each problem's verdict follows the pipeline's rule: "yes" only
if every reading's yes-claim is proved, "no" only if every reading's
no-claim is.

Provers:
- "pipeline": the pipeline's own prover (`attemptCloseEndToEnd`);
- "generic": `aesop`, then `grind`, told to unfold every, some and no in
  both encodings and `IsA` (as in `LiftedScan.lean`);
- "pull" (M only): M's typed quantifiers read as quantifiers on the
  noun's type (`EndToEnd/Encodings/Pullback.lean`, no injectivity
  needed), then the pipeline's prover.

Every proof the generic prover finds is kernel-checked, as the pipeline's
are; the "pull" rewriting is ordinary elaboration by proved lemmas.

Not part of any library - run directly, by the `encodings-modified` CI job.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open FraCaS.Section1.Monotonicity (runTacticChecked)
open FraCaS.Section1.Monotonicity.BlindEval (answerMatches answerToString withFreshBudget)

namespace FraCaS.Encodings.ModifiedScan

def attemptGeneric (ty : Expr) : TermElabM Bool := do
  if ← runTacticChecked ty (← `(tactic|
      aesop (add norm unfold FraCaS.Section1.Every, norm unfold FraCaS.Section1.Some,
        norm unfold FraCaS.Section1.No, norm unfold FraCaS.Encodings.Typed.EveryT,
        norm unfold FraCaS.Encodings.Typed.SomeT, norm unfold FraCaS.Encodings.Typed.NoT,
        norm unfold FraCaS.Encodings.Typed.IsA))) then return true
  if ← runTacticChecked ty (← `(tactic|
      grind [FraCaS.Section1.Every, FraCaS.Section1.Some, FraCaS.Section1.No,
        FraCaS.Encodings.Typed.EveryT, FraCaS.Encodings.Typed.SomeT,
        FraCaS.Encodings.Typed.NoT, FraCaS.Encodings.Typed.IsA])) then return true
  return false

/-- M's claim with its typed quantifiers pulled back to the nouns' types.
`none` if nothing was rewritten; `some none` if the rewriting proved it. -/
def pull (ty : Expr) : TermElabM (Option (Option Expr)) := do
  let g ← mkFreshExprMVar ty
  try
    let gs ← Lean.Elab.Tactic.run g.mvarId! do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        simp only [FraCaS.Encodings.Typed.every_pull, FraCaS.Encodings.Typed.some_pull,
          FraCaS.Encodings.Typed.no_pull, FraCaS.Encodings.Typed.atLeast_pull,
          FraCaS.Encodings.Typed.atMost_pull, FraCaS.Encodings.Typed.exactly_pull,
          FraCaS.Encodings.Typed.most_pull, FraCaS.Encodings.Typed.more_pull,
          FraCaS.Encodings.Typed.both_pull, FraCaS.Encodings.Typed.neither_pull]))
    match gs with
    | [] => return some none
    | [g'] => return some (some (← instantiateMVars (← g'.getType)))
    | _ => return none
  catch _ => return none

def attemptPull (ty : Expr) : TermElabM Bool := do
  match ← withFreshBudget (pull ty) (fun _ => pure none) with
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
    if FraCaS.Encodings.Modified.problems.contains i then
      let v := verdict (← ys.mapM (prove prover)) (← ns.mapM (prove prover))
      logInfo m!"modified_verdict {label} {i} {answerToString g} {v}"
      rows := rows ++ [(i, g, v)]
  let matched := rows.filter fun (_, g, v) => answerMatches g v
  let wrong := rows.filter fun (_, g, v) => v != "unknown" && !answerMatches g v
  logInfo m!"modified {label}: {matched.length}/{rows.length} match gold, {wrong.length} wrong: \
    {wrong.map fun (i, g, v) => (i, answerToString g, v)}"
  logInfo m!"modified_matched {label} {matched.map (·.1)}"

open FraCaS.Encodings.Modified in
elab "#modified_scan" : command => liftTermElabM do
  let pipeline := FraCaS.EndToEnd.attemptCloseEndToEnd
  run "F_pipeline" pipeline FraCaS.EndToEnd.registry
  run "F_generic" attemptGeneric FraCaS.EndToEnd.registry
  run "F_bk_pipeline" pipeline FraCaS.EndToEnd.registryBk
  run "F_bk_generic" attemptGeneric FraCaS.EndToEnd.registryBk
  run "P_pipeline" pipeline registryP
  run "P_generic" attemptGeneric registryP
  run "W_pipeline" pipeline registryW
  run "W_generic" attemptGeneric registryW
  run "M_pull" attemptPull registryM
  run "M_generic" attemptGeneric registryM

end FraCaS.Encodings.ModifiedScan

#modified_scan
