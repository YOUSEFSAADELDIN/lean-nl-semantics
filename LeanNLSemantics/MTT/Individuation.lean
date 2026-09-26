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
(`Bool`), one informational content (`Unit`). `abbrev`, not `def`, on
every one of these (including `Phy0`/`Info0`/`Book0`, not just `bk0`
below): `by decide` on `phyEq`/`infoEq` needs typeclass search to unfold
the *entire* chain down to `Bool`'s `DecidableEq`, and a plain `def` is
opaque to instance search at every link — making only `bk0` reducible
first still failed ("failed to synthesize Decidable ¬phyEq true false"),
since `Phy0`/`Book0` themselves were still blocking it. Unlike Coq's
`Definition`, which unfolds much more eagerly under
`unfold`/`simpl`/`compute`. -/
abbrev Phy0 : Type := Bool
abbrev Info0 : Type := Unit
abbrev Book0 : Type := Bool -- the two copies

abbrev bk0 (b : Book0) : DotType Phy0 Info0 := ⟨b, ()⟩

abbrev phyEq (a b : Book0) : Prop := (bk0 a).phy = (bk0 b).phy
abbrev infoEq (a b : Book0) : Prop := (bk0 a).info = (bk0 b).info

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
