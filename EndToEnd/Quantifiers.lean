import LeanNLSemantics.FraCaS.Section1.GQ

/-!
# Quantifiers and lemmas used only by the end-to-end pipeline

Definitions the end-to-end translation (`gf/translate.py`'s readings,
`EndToEnd/gen_claims.py`) produces or its prover (`EndToEnd/Prover.lean`)
needs, and that the hand-written FraCaS corpus does not use. They live
here rather than in `FraCaS/Section1/GQ.lean` so the corpus library stays
exactly what the hand-written theorems need.
-/

namespace FraCaS.EndToEnd

open FraCaS.Section1

/-- "More P are Q than are R" - the quantity comparative ("ITEL won more
orders than APCOM did": `More order (win itel) (win apcom)`), a
three-place quantifier comparing two counts over the same restrictor.
Exists only for the end-to-end pipeline (`gf/translate.py`); the
hand-written Section 6 theorems state these problems over `Nat` counts
directly. -/
abbrev More {A : Type*} [Fintype A] (P Q R : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] [DecidablePred fun x => P x ∧ R x] : Prop :=
  card (fun x => P x ∧ Q x) > card (fun x => P x ∧ R x)

/-- `More P Q R` gives `Some P Q`: a count strictly above another count
is positive - FraCaS 230's "ITEL won more orders than APCOM did ⊢ ITEL
won some orders" shape (number-neutral "some"). -/
theorem more_some {A : Type*} [Fintype A] (P Q R : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] [DecidablePred fun x => P x ∧ R x]
    (h : More P Q R) : Some P Q := by
  have h' : card (fun x => P x ∧ Q x) > card (fun x => P x ∧ R x) := h
  have hpos : 0 < card (fun x => P x ∧ Q x) := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter] at hx
  exact ⟨x, hx.2⟩

/-- `More P Q R` and `AtLeast n P R` give `AtLeast (n + 1) P Q` - FraCaS
232's "more orders than APCOM did, APCOM won ten orders ⊢ ITEL won at
least eleven orders" shape. -/
theorem more_atLeast {A : Type*} [Fintype A] (n : Nat) (P Q R : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] [DecidablePred fun x => P x ∧ R x]
    (h : More P Q R) (hR : AtLeast n P R) : AtLeast (n + 1) P Q := by
  have h1 : card (fun x => P x ∧ Q x) > card (fun x => P x ∧ R x) := h
  have h2 : card (fun x => P x ∧ R x) ≥ n := hR
  show card (fun x => P x ∧ Q x) ≥ n + 1
  omega

/-- `atMost_trans`'s upward counterpart: if at least `n` `P`s are `Q`,
every `P` is an `S`, and every `S` that is `Q` is `R`, then at least `n`
`P`s are `R` - FraCaS 27's "a few committee members are from Sweden,
all committee members are people, all people from Sweden are from
Scandinavia ⊢ at least a few committee members are from Scandinavia"
shape (`some_trans` for a counted quantifier). -/
theorem atLeast_trans {A : Type*} [Fintype A] (n : Nat) (P Q S R : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] [DecidablePred fun x => P x ∧ R x]
    (h1 : AtLeast n P Q) (h2 : Every P S) (h3 : Every (fun x => S x ∧ Q x) R) : AtLeast n P R := by
  have hsub : (Finset.univ.filter fun x => P x ∧ Q x) ⊆ Finset.univ.filter fun x => P x ∧ R x := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, h3 x ⟨h2 x hx.1, hx.2⟩⟩
  have hle : card (fun x => P x ∧ Q x) ≤ card (fun x => P x ∧ R x) := Finset.card_le_card hsub
  have h1' : card (fun x => P x ∧ Q x) ≥ n := h1
  show card (fun x => P x ∧ R x) ≥ n
  omega

end FraCaS.EndToEnd
