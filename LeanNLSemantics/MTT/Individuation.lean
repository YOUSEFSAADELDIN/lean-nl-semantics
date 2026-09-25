import LeanNLSemantics.MTT.DotTypes

/-!
# Individuation (counting relative to an identity criterion)

Faithful port of `atlas/mtt_ranta/MTT.v` Part 7 (CL20 §5.3): CNs come
with identity criteria; how many books there are depends on whether
books are individuated physically or informationally.

This one turned out not to need the `Prop`-irrelevance caveat flagged
elsewhere in this repo (`CN.lean`, `Adjectives.lean`) — it compares plain
`=` on projections of a concrete model, not *which* proof a Σ-type
carries. That caveat may still matter for a richer individuation account
(CoqLACL's `Individuation.v` leans more on setoids/witnesses); it simply
isn't exercised by this specific, simpler formalization.
-/

namespace MTT

/-- "There are at least two `A`s, relative to the identity criterion
`R`": two elements `R` does not identify. -/
def countGe2 (A : Type) (R : A → A → Prop) : Prop :=
  ∃ x y : A, ¬ R x y

section Individuation

/-- The concrete two-copies/one-content lexicon: two physical copies
(`Bool`), one informational content (`Unit`). -/
def Phy0 : Type := Bool
def Info0 : Type := Unit
def Book0 : Type := Bool -- the two copies

def bk0 (b : Book0) : DotType Phy0 Info0 := ⟨b, ()⟩

def phyEq (a b : Book0) : Prop := (bk0 a).phy = (bk0 b).phy
def infoEq (a b : Book0) : Prop := (bk0 a).info = (bk0 b).info

/-- T-IND1. Physically individuated, there are (at least) two books. -/
theorem two_books_phy : countGe2 Book0 phyEq :=
  ⟨true, false, by decide⟩

/-- T-IND2. Informationally individuated, "two books" is refutable: the
copies collapse (CL20 §5.3.1: "picked up two books" vs "mastered two
books" individuate differently). -/
theorem not_two_books_info : ¬ countGe2 Book0 infoEq := by
  rintro ⟨x, y, h⟩
  exact h rfl

end Individuation

end MTT
