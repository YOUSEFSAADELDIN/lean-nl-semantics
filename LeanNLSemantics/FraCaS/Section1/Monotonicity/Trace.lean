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
pretty-printed stand-in name otherwise. -/
structure MonoStep where
  position  : Position
  rule      : MonoRule
  factHyp   : Lean.Name
  substFrom : Lean.Name
  substTo   : Lean.Name
  deriving Repr

/-- The trace for one theorem: which theorem, and the (here: always
single) step `mono_nl` used to close it. A list rather than a single
`MonoStep` because nothing about the format itself is single-step-only -
`Tactic.lean`'s search procedure is - so a later fragment extension that
chains rules (e.g. to reach the conjunctive `every_trans` shape) grows
`MonoTrace.steps`, not this structure. -/
structure MonoTrace where
  theoremName : Lean.Name
  steps       : List MonoStep
  deriving Repr

end FraCaS.Section1.Monotonicity
