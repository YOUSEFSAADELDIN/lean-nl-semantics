import LeanNLSemantics.MTT.CN

/-!
# A joint model for this project's 8 primitive-vocabulary axioms

Closes the third part of the assumption audit
(`LeanNLSemantics/FraCaS/AssumptionAudit.lean`'s own header records the
first two: every axiom used anywhere in the project, per theorem, and
which of those are custom rather than Lean/Mathlib's standard three).
That audit already found the full axiom footprint of this entire
project is exactly 8 declarations - `CN.lean`'s `walk`, `Tense.lean`'s
`Event`/`Time`/`runtime`/`utteranceTime`/`before`, `Adjectives.lean`'s
`Tall`, and `DotTypes.lean`'s `Physical`/`Informational` - and that none
of them are reachable from any FraCaS theorem (`FraCaS/` never imports
`MTT/` at all), so there is nothing to jointly model for the FraCaS
corpus itself: zero custom axioms there, full stop. What's left is
these 8, entirely confined to the separate MTT semantic-framework
module.

Every one of the 8 is a *primitive-vocabulary* axiom - either a bare
`Type` or an uninterpreted function/relation over an already-fresh
type - never a `Prop` asserted true outright. That distinction matters:
introducing an opaque type or an unconstrained symbol is always
conservative (it can never make a false statement provable, the way an
axiom like `axiom problem_167_answer : Follows` obviously could), so
consistency here just means each axiom's stated type is inhabited, and
- since several of them share types (`runtime`/`utteranceTime`/`before`
all mention `Event`/`Time`) - inhabited *jointly*, by one consistent
choice, not by 8 separate choices that happen to individually work but
might silently disagree with each other.

The witnesses below are ordinary `def`s, not axioms - each one
type-checking at exactly the axiom's own stated type (copied verbatim)
is itself the proof that type is inhabited, checked by the kernel, not
asserted by this comment. This file does not import `Tense.lean`,
`Adjectives.lean`, or `DotTypes.lean` - it only imports `CN.lean`,
needed for `CN .animal`'s actual type, not for the `walk` axiom that
happens to live in the same file - so nothing here could accidentally
reuse the very axiom it's modeling. The `#print axioms` line after each
witness checks that directly rather than assuming it: every one is
expected to depend on nothing beyond Lean/Mathlib's standard three,
exactly like the FraCaS corpus itself.
-/

namespace MTT.AxiomModel

/-- Witness for `axiom Event : Type`. -/
abbrev EventW : Type := Unit

/-- Witness for `axiom Time : Type`. -/
abbrev TimeW : Type := Nat

/-- Witness for `axiom runtime : Event → Time`, over the two witnesses
above rather than a fresh, possibly-disagreeing pair - this is the
"joint" part of a joint model. -/
def runtimeW : EventW → TimeW := fun _ => 0

/-- Witness for `axiom utteranceTime : Time`, same `TimeW` as `runtimeW`
maps into. -/
def utteranceTimeW : TimeW := 0

/-- Witness for `axiom before : Time → Time → Prop`, again over `TimeW` -
a genuine strict order, not just a placeholder relation, so `Past`/
`Future` (`Tense.lean`'s only actual users of `before`) come out
meaningfully non-trivial under this model too. -/
def beforeW : TimeW → TimeW → Prop := (· < ·)

/-- Witness for `axiom Tall : ∀ {A : Type}, A → Prop`. -/
def TallW : ∀ {A : Type}, A → Prop := fun {A} _ => True

/-- Witness for `axiom walk : CN .animal → Prop`, over the real `CN`
type `CN.lean` already defines (not a toy stand-in), since that type
itself is concrete and computable - only the predicate on it is
axiomatized in the original. -/
def walkW : CN .animal → Prop := fun _ => True

/-- Witness for `axiom Physical : Type`. -/
abbrev PhysicalW : Type := Unit

/-- Witness for `axiom Informational : Type`. -/
abbrev InformationalW : Type := Unit

#print axioms EventW
#print axioms TimeW
#print axioms runtimeW
#print axioms utteranceTimeW
#print axioms beforeW
#print axioms TallW
#print axioms walkW
#print axioms PhysicalW
#print axioms InformationalW

end MTT.AxiomModel
