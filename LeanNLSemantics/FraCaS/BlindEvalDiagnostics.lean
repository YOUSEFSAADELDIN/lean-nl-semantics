import LeanNLSemantics.FraCaS.Section1.Monotonicity.BlindEvalCore
import LeanNLSemantics

/-!
# TEMPORARY diagnostic (not part of the evaluation itself)

For every bare theorem the blind evaluation still reports as a mismatch
(as of CI run 37168342088), which of the repaired chain's steps close
its type *as written* (each is a proved theorem, so that direction is
true), and with what error text the others fail. To be deleted once read.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Command
open FraCaS.Section1.Monotonicity (runTacticOn)

namespace FraCaS.BlindEvalDiagnostics

def targets : List Lean.Name :=
  [``FraCaS.Section1.fracas_006, ``FraCaS.Section1.fracas_014, ``FraCaS.Section1.fracas_038,
   ``FraCaS.Section1.fracas_046, ``FraCaS.Section1.fracas_070, ``FraCaS.Section2.fracas_089,
   ``FraCaS.Section2.fracas_099, ``FraCaS.Section2.fracas_101, ``FraCaS.Section2.fracas_103,
   ``FraCaS.Section2.fracas_105, ``FraCaS.Section2.fracas_106, ``FraCaS.Section2.fracas_111,
   ``FraCaS.Section3.fracas_123, ``FraCaS.Section3.fracas_126, ``FraCaS.Section3.fracas_127,
   ``FraCaS.Section3.fracas_129, ``FraCaS.Section4.fracas_173, ``FraCaS.Section6.fracas_246,
   ``FraCaS.Section6.fracas_248, ``FraCaS.Section7.fracas_307]

def showResult : Except String Unit → String
  | .ok () => "CLOSED"
  | .error msg => s!"failed: {msg}"

elab "#diag_misses" : command => liftTermElabM do
  let tacs : List (String × TSyntax `tactic) := [
    ("blind_aesop", ← `(tactic| blind_aesop)),
    ("blind_aesop_unfold", ← `(tactic| blind_aesop_unfold)),
    ("grind", ← `(tactic| grind)),
    ("blind_grind", ← `(tactic| blind_grind)),
    ("omega", ← `(tactic| (intros; omega)))
  ]
  for n in targets do
    let ty := (← getConstInfo n).type
    logInfo m!"diag {n} : {ty}"
    for (label, stx) in tacs do
      let r ← runTacticOn ty stx
      logInfo m!"diag {n} / {label}: {showResult r}"

end FraCaS.BlindEvalDiagnostics

#diag_misses
