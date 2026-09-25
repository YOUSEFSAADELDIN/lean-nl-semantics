import LeanNLSemantics.MTT.CN
import LeanNLSemantics.MTT.Quantifiers

/-!
# Dot-types for copredication

Pustejovsky-style dot-types (`Phy • Info` for `book`) let a single lexical
item license predicates from either "aspect" — "heavy" (physical) and
"boring" (informational) book — without treating the noun as ambiguous.
CoqLACL's `Individuation.v` develops this further (e.g. "picked up and
mastered three books").

The `Copredication` section below is a faithful port of `atlas/mtt_ranta/
MTT.v` Part 6 (CL20 §5.2, App. 6). Its own comment flags an artifact of
the Coq encoding worth repeating: the record also has pairing, which real
dot-types forbid — only the elimination behaviour (the two projections)
is used, matching Pustejovsky's own restriction. Not ported: T-DOT3
(`copred_coercion_demo`), which relies on a Coq `Local Coercion` inside a
section-parameterized record — the source comment itself notes this
doesn't generalise past Coq's section mechanics.

Related prior art, confirmed by reading the source directly: linglib's
`Studies/Pustejovsky1995.lean` already formalizes a different chapter's
type coercion — a `SemType` lattice plus qualia-projection shifters
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

/-- The dot-type `Phy • Info` (`MTT.v`'s `PhyInfo`): a record with both
projections, used only for its elimination behaviour. -/
structure DotType (A B : Type) where
  phy : A
  info : B

axiom Physical : Type
axiom Informational : Type

/-- A concrete instantiation where `Book` literally *is* the dot-type. A
real fragment might instead have `Book` merely *coerce into*
`DotType Physical Informational` via a separate function (carrying more
structure, e.g. qualia, beyond the raw pair) — that's the shape `MTT.v`
actually uses and the `Copredication` section below is stated against;
this is the special case where that function is `id`. -/
def Book : Type := DotType Physical Informational

instance : Coe Book Physical := ⟨DotType.phy⟩
instance : Coe Book Informational := ⟨DotType.info⟩

section Copredication

variable {A : Type} (bk : A → DotType Physical Informational)
variable (pickup : Physical → Prop) (master : Informational → Prop)

/-- "x picked up and mastered b": each verb selects its aspect through
the dot-type projections (CL20 §5.2, "John picked up and mastered the
book"). -/
def pickupAndMaster (b : A) : Prop :=
  pickup (bk b).phy ∧ master (bk b).info

/-- T-DOT1. Copredication entails each conjunct. -/
theorem copred_left (b : A) :
    pickupAndMaster bk pickup master b → pickup (bk b).phy :=
  fun ⟨h, _⟩ => h

theorem copred_right (b : A) :
    pickupAndMaster bk pickup master b → master (bk b).info :=
  fun ⟨_, h⟩ => h

/-- T-DOT2. Under quantification: "John picked up and mastered some
book" entails "John picked up some book" and "John mastered some book"
(CL20 §5.3.3 shape). -/
theorem copred_some :
    Some' A (pickupAndMaster bk pickup master) →
      Some' A (fun b => pickup (bk b).phy) ∧ Some' A (fun b => master (bk b).info) :=
  fun ⟨b, h1, h2⟩ => ⟨⟨b, h1⟩, ⟨b, h2⟩⟩

end Copredication

end MTT
