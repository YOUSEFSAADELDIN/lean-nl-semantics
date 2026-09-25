import LeanNLSemantics.MTT.CN

/-!
# Dot-types for copredication

Pustejovsky-style dot-types (`Phy • Info` for `book`) let a single lexical
item license predicates from either "aspect" — "heavy" (physical) and
"boring" (informational) book — without treating the noun as ambiguous.
CoqLACL's `Individuation.v` develops this further (e.g. "picked up and
mastered three books"); this file only sets up the basic carrier type.

Related prior art, confirmed by reading the source directly: linglib's
`Studies/Pustejovsky1995.lean` already formalizes this chapter's type
coercion — a `SemType` lattice plus qualia-projection shifters
(`Alias`/`Applies`/`Shifter`) deciding which readings of e.g. "began a
book" are available. That's argument-*selection* coercion between type
*tags* used to check whether a reading exists, not MTT's CNs-as-types
with genuine elements to quantify over — `DotType` here is a real Lean
`Type` you build individuals of and quantify over, not a lattice node. Not
a duplicate, but close enough that a fragment needing Pustejovsky-style
coercion (not copredication specifically) should probably reuse their
`SemType`/`Shifter` machinery via `LinglibBridge.lean` rather than
re-deriving it here.
-/

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
