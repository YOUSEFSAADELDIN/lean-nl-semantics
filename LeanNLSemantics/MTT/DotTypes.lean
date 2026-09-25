/-!
# Dot-types for copredication

Pustejovsky-style dot-types (`Phy • Info` for `book`) let a single lexical
item license predicates from either "aspect" — "heavy" (physical) and
"boring" (informational) book — without treating the noun as ambiguous.
CoqLACL's `Individuation.v` develops this further (e.g. "picked up and
mastered three books"); this file only sets up the basic carrier type.
-/
import LeanNLSemantics.MTT.CN

namespace MTT

/-- The two aspects of a dot-typed CN, paired so that either projection is
available to a predicate. -/
structure DotType (A B : Type) where
  phy : A
  info : B

axiom Physical : Type
axiom Informational : Type

def Book : Type := DotType Physical Informational

instance : Coe Book Physical := ⟨DotType.phy⟩
instance : Coe Book Informational := ⟨DotType.info⟩

end MTT
