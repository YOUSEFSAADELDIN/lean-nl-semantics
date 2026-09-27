import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics

/-!
# Corpus-wide coverage scan

**Validation status**: written, not run - see `Tactic.lean`'s header for
why (this sandbox cannot fetch a Lean toolchain at all this session, so
nothing here has produced a single real result yet). This file's whole
point is to *report a result* (how many of the 342 FraCaS problems
structurally fall inside the Phase-1 fragment), which is categorically
different from `Tactic.lean`/`CrossCheck.lean`: those are code that
*might* have a bug CI will catch; this one simply has no output at all
until it is actually run once, by CI or a session with toolchain access.
No coverage number is claimed anywhere in this project until this command
has actually produced one.

`#mono_nl_coverage` scans every already-proved theorem in the whole
FraCaS suite (`import LeanNLSemantics`, the project's own root umbrella
import, pulls in all nine sections) whose name's last component starts
with `fracas_`, and attempts `mono_nl`
against a *fresh* goal of that theorem's own already-elaborated type -
never touching or re-proving the original theorem, only asking "does the
Phase-1 fragment's search procedure, unmodified, happen to also close
this same goal shape." Per the standing instruction this reasoner was
scoped under, nothing here adds a rule *because* some corpus example
needs it - the fragment scanned is exactly `Signature.lean`/`Trace.lean`'s
already-fixed eight-rule table, and a theorem the scan fails to close is
reported as unsupported, not used to justify widening the tactic.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Command

namespace FraCaS.Section1.Monotonicity

/-- The last component of a (possibly namespaced) declaration name, as a
plain string - e.g. `FraCaS.Section3.fracas_114` ↦ `"fracas_114"`. -/
def lastComponent (n : Lean.Name) : String :=
  (toString n).splitOn "." |>.getLast!

/-- `#mono_nl_coverage` walks every constant in the environment whose name
looks like a FraCaS theorem, tries `mono_nl` against a synthetic copy of
its statement, and reports which ones it closes. Never touches the
original declarations - each attempt is a disposable metavariable. -/
elab "#mono_nl_coverage" : command => liftTermElabM do
  let env ← getEnv
  let mut supported : Array Lean.Name := #[]
  let mut unsupported : Array Lean.Name := #[]
  for (name, info) in env.constants.toList do
    unless (lastComponent name).startsWith "fracas_" do continue
    unless info.isTheorem do continue
    let ty := info.type
    let ok ←
      try
        let mvar ← mkFreshExprMVar ty (kind := .synthetic)
        let remaining ← Lean.Elab.Tactic.run mvar.mvarId! do
          Lean.Elab.Tactic.evalTactic (← `(tactic| mono_nl))
        pure remaining.isEmpty
      catch _ =>
        pure false
    if ok then
      supported := supported.push name
    else
      unsupported := unsupported.push name
  logInfo m!"mono_nl coverage: {supported.size} supported, {unsupported.size} not, \
    out of {supported.size + unsupported.size} FraCaS theorems scanned"
  logInfo m!"supported: {supported.toList}"
  logInfo m!"NOT in the Phase-1 fragment: {unsupported.toList}"

end FraCaS.Section1.Monotonicity

#mono_nl_coverage
