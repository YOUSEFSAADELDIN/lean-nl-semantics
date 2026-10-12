import EndToEnd
import EndToEnd.HeldOut.SICK.Claims

/-!
# The second held-out test: scoring the SICK pairs the frozen pipeline reaches

The same prover (`attemptCloseEndToEnd`) and the same every-reading rule
as `Scan.lean` and `HeldOutScan.lean`, on `EndToEnd/HeldOut/SICK/Claims.lean`.
SICK's labels are three-way, so, as for FraCaS:

- a **match** is "yes" on entailment, "no" on contradiction, or
  "unknown" on neutral;
- a **wrong answer** is "yes" on a pair that is not entailment, "no" on
  one that is not contradiction, or a reading assignment proving both;
- "unknown" on entailment or contradiction is a **miss**.

Precision and recall are computed from the `sick_verdict` lines
(`HeldOut/SICK/README.md`). Run with and without background knowledge.
Not part of any library - run directly, by the `sick` CI job.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open FraCaS.Section1.Monotonicity.BlindEval (withFreshBudget)

namespace FraCaS.HeldOut.SICK.Scan

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

def run (label : String) (reg : List (Nat × String × List Lean.Name × List Lean.Name)) :
    TermElabM Unit := do
  let mut rows : List (Nat × String × String) := []
  for (i, gold, ys, ns) in reg do
    let v := verdict (← ys.mapM prove) (← ns.mapM prove)
    logInfo m!"sick_verdict {label} {i} {gold} {v}"
    rows := rows ++ [(i, gold, v)]
  let matched := rows.filter fun (_, g, v) =>
    (g == "E" && v == "yes") || (g == "C" && v == "no") || (g == "N" && v == "unknown")
  let wrong := rows.filter fun (_, g, v) =>
    v == "contradiction" || (v == "yes" && g != "E") || (v == "no" && g != "C")
  let decided := rows.filter fun (_, _, v) => v == "yes" || v == "no"
  logInfo m!"sick {label}: {rows.length} reached; {matched.length} match gold; \
    {wrong.length} wrong: {wrong}; {decided.length} decided (yes/no)"

/-- `SICK_SCAN` = `<as_translated|with_background>:<k>/<n>` scores the k-th
of n interleaved shards of one registry; the report sums the shards. -/
elab "#sick_scan" : command => liftTermElabM do
  let spec := (← IO.getEnv "SICK_SCAN").getD "with_background:0/1"
  let (label, shard) := match spec.splitOn ":" with
    | [l, s] => (l, s)
    | _ => ("", "")
  let (k, n) := match shard.splitOn "/" with
    | [a, b] => (a.toNat!, b.toNat!)
    | _ => (0, 1)
  let reg := if label == "as_translated" then FraCaS.HeldOut.SICK.registry
    else if label == "with_background" then FraCaS.HeldOut.SICK.registryBk else []
  if reg.isEmpty || n == 0 then
    throwError "set SICK_SCAN to <as_translated|with_background>:<k>/<n>, got {repr spec}"
  let mine := (reg.zipIdx.filter fun (_, i) => i % n == k).map (·.1)
  run s!"{label} shard {k}/{n}" mine

end FraCaS.HeldOut.SICK.Scan

#sick_scan
