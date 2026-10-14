import Lean
import Lean.Util.CollectAxioms
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic

/-!
# Shared corpus-scanning primitives

`Coverage.lean`'s own header explains it reuses `Tactic.lean`'s
`introAll`/`quantifierHeads` "rather than re-implementing the same head
check a second, possibly-inconsistent way" - but `Coverage.lean` and
`BlindEval.lean` ended up doing exactly that *relative to each other*:
each independently built a "synthetic goal, introduce its whole
implication chain, read the conclusion's head constant" primitive
(`Coverage.lean`'s `isEligible`/`concludingHead`, `BlindEval.lean`'s
`isEntailmentShaped`) and a "run one tactic against a fresh
metavariable, catch failure" runner (`Coverage.lean`'s own closure
inside `#mono_nl_coverage`, `BlindEval.lean`'s top-level `runTactic`).
Factored out here so both files share one copy of each - `lastComponent`
too, identical in both.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace FraCaS.Section1.Monotonicity

/-- The last component of a (possibly namespaced) declaration name, as a
plain string - e.g. `FraCaS.Section3.fracas_114` ↦ `"fracas_114"`. -/
def lastComponent (n : Lean.Name) : String :=
  (toString n).splitOn "." |>.getLast!

/-- `ty`'s conclusion's head constant, after introducing its whole
implication chain on a fresh synthetic metavariable - `none` when the
result isn't even a named application (e.g. a bare `∀`/`∃` left over
from a definition unfolding, or a `Prop` variable). Reuses `introAll`
from `Tactic.lean` rather than a second, possibly-inconsistent
traversal. -/
def goalHeadConst (ty : Expr) : MetaM (Option Lean.Name) := do
  let mvar ← mkFreshExprMVar ty (kind := .synthetic)
  let (_, goal) ← introAll mvar.mvarId!
  goal.withContext do
    return (← goal.getType).getAppFn.constName?

/-- Attempts one tactic against a *fresh* metavariable of type `ty`,
discarding any partial assignment on failure - `.ok ()` iff it fully
closed the goal, `.error msg` with the caught exception's rendered
message otherwise (or `"tactic left goals open"` if the tactic ran to
completion without closing every goal it left).

Each attempt gets its own fresh heartbeat budget (`withCurrHeartbeats`),
and a resource-limit failure (`maxHeartbeats`/`maxRecDepth`) is caught as
an ordinary failed attempt via `tryCatchRuntimeEx` - plain `try`/`catch`
deliberately rethrows those "runtime" exceptions in every `CoreM`-based
monad (`Lean/CoreM.lean`'s `Core.tryCatch`), and the heartbeat counter is
otherwise shared by the *whole* scanning command, so without both of
these one slow search (a real `aesop` run, say) could exhaust the budget
and abort every remaining problem in the scan, not just its own attempt. -/
def runTacticOn (ty : Expr) (tacticStx : Lean.TSyntax `tactic) :
    TermElabM (Except String Unit) :=
  withCurrHeartbeats <| tryCatchRuntimeEx
    (do
      let mvar ← mkFreshExprMVar ty (kind := .synthetic)
      let remaining ← Lean.Elab.Tactic.run mvar.mvarId! do
        Lean.Elab.Tactic.evalTactic tacticStx
      if remaining.isEmpty then
        pure (.ok ())
      else
        pure (.error "tactic left goals open"))
    (fun e => do
      let msg ←
        try
          e.toMessageData.toString
        catch _ =>
          pure "<error message could not be rendered>"
      pure (.error msg))

/-- `runTacticOn`, discarding the failure message for call sites that
only need success/failure. -/
def runTacticBool (ty : Expr) (tacticStx : Lean.TSyntax `tactic) : TermElabM Bool := do
  match ← runTacticOn ty tacticStx with
  | .ok () => return true
  | .error _ => return false

/-- Lean's three standard axioms: the only ones an accepted proof may use. -/
def standardAxioms : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Why the proof `pf` of `ty` is not accepted, or `none` if it is. It must
have no metavariables and no `sorry`; the kernel must accept it as a
theorem of type `ty` (added to a copy of the environment, then
discarded); and it may use no axiom outside `standardAxioms`. -/
def kernelRejects (ty pf : Expr) : TermElabM (Option String) := do
  if ty.hasMVar || pf.hasMVar then return some "metavariables left in the proof"
  if pf.hasSorry then return some "the proof uses sorry"
  let name ← mkFreshUserName `kernelCheck
  let decl := Declaration.thmDecl { name, levelParams := [], type := ty, value := pf }
  let opts ← getOptions
  match (← getEnv).unlockAsync.addDeclCore (Core.getMaxHeartbeats opts).toUSize
      (maxRecDepth.get opts).toUSize decl none with
  | .error _ => return some "the kernel rejects the proof"
  | .ok env =>
    let axioms ← withEnv env (collectAxioms name)
    match axioms.toList.find? (· ∉ standardAxioms) with
    | some ax => return some s!"the proof uses the axiom {ax}"
    | none => return none

/-- `runTacticBool`, with the proof the tactic
finds checked by `kernelRejects` before it counts. A rejection is logged
as `kernel_check rejected` and counts as a failed attempt. -/
def runTacticChecked (ty : Expr) (tacticStx : Lean.TSyntax `tactic) : TermElabM Bool :=
  withCurrHeartbeats <| tryCatchRuntimeEx
    (do
      let ty ← instantiateMVars ty
      let mvar ← mkFreshExprMVar ty (kind := .synthetic)
      let remaining ← Lean.Elab.Tactic.run mvar.mvarId! do
        Lean.Elab.Tactic.evalTactic tacticStx
      unless remaining.isEmpty do return false
      let pf ← instantiateMVars mvar
      match ← kernelRejects ty pf with
      | none => return true
      | some why =>
        logInfo m!"kernel_check rejected {tacticStx.raw}: {why}"
        return false)
    (fun _ => pure false)

-- Canaries for `kernelRejects`: it accepts a real proof and rejects a
-- `sorry` and an ill-typed term (the last can only be caught by the
-- kernel itself).
#eval show TermElabM Unit from do
  let ty := mkConst ``True
  if let some why ← kernelRejects ty (mkConst ``True.intro) then
    throwError "kernel check rejects True.intro: {why}"
  if (← kernelRejects ty (← mkSorry ty false)).isNone then
    throwError "kernel check accepts sorry"
  if (← kernelRejects ty (mkConst ``Nat.zero)).isNone then
    throwError "kernel check accepts an ill-typed proof"

end FraCaS.Section1.Monotonicity
