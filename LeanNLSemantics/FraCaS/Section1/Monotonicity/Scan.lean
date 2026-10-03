import Lean
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
completion without closing every goal it left). -/
def runTacticOn (ty : Expr) (tacticStx : Lean.TSyntax `tactic) :
    TermElabM (Except String Unit) :=
  try
    let mvar ← mkFreshExprMVar ty (kind := .synthetic)
    let remaining ← Lean.Elab.Tactic.run mvar.mvarId! do
      Lean.Elab.Tactic.evalTactic tacticStx
    if remaining.isEmpty then
      pure (.ok ())
    else
      pure (.error "tactic left goals open")
  catch e =>
    let msg ←
      try
        e.toMessageData.toString
      catch _ =>
        pure "<error message could not be rendered>"
    pure (.error msg)

/-- `runTacticOn`, discarding the failure message for call sites that
only need success/failure. -/
def runTacticBool (ty : Expr) (tacticStx : Lean.TSyntax `tactic) : TermElabM Bool := do
  match ← runTacticOn ty tacticStx with
  | .ok () => return true
  | .error _ => return false

end FraCaS.Section1.Monotonicity
