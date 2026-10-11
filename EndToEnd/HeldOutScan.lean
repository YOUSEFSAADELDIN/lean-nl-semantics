import EndToEnd
import EndToEnd.HeldOut.Claims

/-!
# The held-out test: scoring the MED problems the frozen pipeline reaches

The same prover (`attemptCloseEndToEnd`) and the same every-reading rule
as `Scan.lean`, on `EndToEnd/HeldOut/Claims.lean`. MED's labels are two-way:
"entailment", or "neutral" (which includes contradiction). So:

- a **match** is "yes" on entailment, or "no"/"unknown" on neutral;
- a **wrong answer** is "yes" on neutral, or "no" on entailment (the
  hypothesis refuted where it follows); a reading assignment proving both
  is reported as a contradiction;
- "unknown" on entailment is a **miss**: not wrong, not matched.

Run with and without background knowledge, as `Scan.lean` does. Not part
of any library - run directly, by the `heldout` CI job.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open FraCaS.Section1.Monotonicity.BlindEval (withFreshBudget)

namespace FraCaS.HeldOut.Scan

def attempt (ty : Expr) : TermElabM String := do
  return if ← FraCaS.EndToEnd.attemptCloseEndToEnd ty then "1" else "0"

def prove (n : Lean.Name) : TermElabM String := do
  match (← getEnv).find? n |>.bind (·.value?) with
  | none => return "m"
  | some ty => withFreshBudget (attempt ty) (fun _ => pure "e")

def verdict (yes no : List String) : String :=
  let y := !yes.isEmpty && yes.all (· == "1")
  let n := !no.isEmpty && no.all (· == "1")
  if y && n then "contradiction" else if y then "yes" else if n then "no" else "unknown"

def run (label : String) (reg : List (Nat × Bool × List Lean.Name × List Lean.Name)) :
    TermElabM Unit := do
  let mut rows : List (Nat × Bool × String) := []
  for (i, entails, ys, ns) in reg do
    let v := verdict (← ys.mapM prove) (← ns.mapM prove)
    logInfo m!"heldout_verdict {label} {i} {if entails then "entailment" else "neutral"} {v}"
    rows := rows ++ [(i, entails, v)]
  let matched := rows.filter fun (_, e, v) => if e then v == "yes" else (v == "no" || v == "unknown")
  let wrong := rows.filter fun (_, e, v) =>
    v == "contradiction" || (e && v == "no") || (!e && v == "yes")
  let decided := rows.filter fun (_, _, v) => v == "yes" || v == "no"
  let ent := rows.filter (·.2.1)
  logInfo m!"heldout {label}: {rows.length} reached; {matched.length} match gold; \
    {wrong.length} wrong: {wrong.map fun (i, e, v) => (i, e, v)}; \
    {decided.length} decided (yes/no); entailment problems proved: \
    {(ent.filter (·.2.2 == "yes")).length}/{ent.length}"

elab "#heldout_scan" : command => liftTermElabM do
  run "as_translated" FraCaS.HeldOut.registry
  run "with_background" FraCaS.HeldOut.registryBk

end FraCaS.HeldOut.Scan

#heldout_scan
