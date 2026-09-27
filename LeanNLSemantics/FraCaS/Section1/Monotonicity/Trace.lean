import LeanNLSemantics.FraCaS.Section1.Monotonicity.Signature

/-!
# The reasoning trace format

Typed, stable representations for what `Tactic.lean`'s `mono_nl` does -
not `String`s: a `Position`/`MonoRule` enum each, and a `MonoStep`/
`MonoTrace` that names local declarations by their real `Lean.Name`
(every predicate `mono_nl` ever substitutes between is a named local
hypothesis or a named binder from the enclosing theorem's own
`variable` block, so `Lean.Name` is a handle already present in the
source, not an invented indirection). Pretty-printing a `MonoStep` into
something a reader or Visualizer B can show is a separate, later
concern (an export step run against the elaborated environment) - this
file only fixes the shape of the data itself.

The trace is explanatory, not load-bearing: `Tactic.lean` closes the
goal by applying one of `GQ.lean`'s own already-proved lemmas, and it is
*that* application the Lean kernel checks. A `MonoStep` is a record of
which lemma was applied and to what, logged alongside the real proof via
`logInfo`, not a certificate an interpreter re-verifies - see
`Tactic.lean`'s own header for why that stronger design (a reflected
formula language with one generic soundness theorem) is deliberately not
attempted yet.
-/
namespace FraCaS.Section1.Monotonicity

/-- Which of a quantifier's two substitutable arguments a step touches. -/
inductive Position where
  | restrictor
  | scope
  deriving DecidableEq, Repr, Inhabited

/-- The eight rules of the Phase-1 fragment, one per `(Quantifier,
Position)` cell of `QuantifierSig.table` - see `Signature.lean`'s header
for why all eight (not just the ones the original fourteen target
problems need) are in scope. `MonoRule.lemmaName` (`Tactic.lean`) maps
each to the real `GQ.lean` theorem it applies. -/
inductive MonoRule where
  | everyMonoScope
  | everyRestrict
  | someMonoScope
  | someRestrict
  | atLeastMonoScope
  | atLeastRestrict
  | atMostMonoScope
  | atMostRestrict
  deriving DecidableEq, Repr, Inhabited

def MonoRule.quantifier : MonoRule → Quantifier
  | .everyMonoScope | .everyRestrict => .every
  | .someMonoScope | .someRestrict => .some
  | .atLeastMonoScope | .atLeastRestrict => .atLeast
  | .atMostMonoScope | .atMostRestrict => .atMost

def MonoRule.position : MonoRule → Position
  | .everyRestrict | .someRestrict | .atLeastRestrict | .atMostRestrict => .restrictor
  | .everyMonoScope | .someMonoScope | .atLeastMonoScope | .atMostMonoScope => .scope

/-- The unique rule for a given `(Quantifier, Position)` cell - total,
since the fragment's table (`Signature.lean`) covers all eight cells. -/
def ruleFor : Quantifier → Position → MonoRule
  | .every, .scope => .everyMonoScope
  | .every, .restrictor => .everyRestrict
  | .some, .scope => .someMonoScope
  | .some, .restrictor => .someRestrict
  | .atLeast, .scope => .atLeastMonoScope
  | .atLeast, .restrictor => .atLeastRestrict
  | .atMost, .scope => .atMostMonoScope
  | .atMost, .restrictor => .atMostRestrict

/-- One substitution step. `factHyp` is the local hypothesis whose type
supplied the `Entails` fact (i.e. `GQ.Every substFrom substTo` in the
polarity-correct order - see `Tactic.lean`); `substFrom`/`substTo` name
the two predicate values themselves, read off their declaration's
`userName` when they are bare local variables (always true for every
problem this fragment has been checked against so far) and a
pretty-printed stand-in name otherwise. When the fact came from a
Phase-2 `combine` step rather than a single local hypothesis, `factHyp`
names the *synthesized* fact (see `CombineStep`), not a real declaration. -/
structure MonoStep where
  position  : Position
  rule      : MonoRule
  factHyp   : Lean.Name
  substFrom : Lean.Name
  substTo   : Lean.Name
  deriving Repr

/-- Phase 2's one new kind of step: joining two `Every`-shaped facts
sharing a restrictor into a fact about their conjunction, via `GQ.lean`'s
`entails_and` (or `entails_refl` when one side is the trivial reflexive
fact, named `none` here since it has no supplying hypothesis of its
own). Not a `(Quantifier, Position)` substitution itself - `Signature.
lean`'s table says nothing about conjunction - so kept separate from
`MonoStep` rather than forced into its shape; a `MonoTrace` carries at
most one of these, immediately followed by the `MonoStep` that consumes
the fact it produces. This is the trace-level mirror of the "explicit
semantic step" `Tactic.lean`'s `combineFacts` performs before ever
calling into the existing per-quantifier substitution machinery. -/
structure CombineStep where
  left          : Option Lean.Name
  right         : Option Lean.Name
  sharedLeft    : Lean.Name
  leftConjunct  : Lean.Name
  rightConjunct : Lean.Name
  deriving Repr

/-- The trace for one theorem: which theorem, an optional `combine` step
(Phase 2 only - `none` for every Phase-1 theorem, unchanged), and the
single substitution step that closes the goal, consuming either a real
local hypothesis (Phase 1) or the `combine` step's synthesized fact
(Phase 2). -/
structure MonoTrace where
  theoremName : Lean.Name
  combine     : Option CombineStep
  step        : MonoStep
  deriving Repr

end FraCaS.Section1.Monotonicity
