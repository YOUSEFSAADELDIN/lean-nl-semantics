import EndToEnd.Encodings.Modified
import EndToEnd.Encodings.Equivalence

/-!
# Phase 3: what the encodings commit to, settled by hand

The provers of `EndToEnd/ModifiedScan.lean` miss most of P's, W's and M's
claims on the modified nouns of Section 1 (`Modified.lean`). Each miss is
valid, proved here.

What none of them proves is 76's second reading, which reads "few" as
the opaque `Few`. Its one meaning postulate lets the scope shrink, not
the restrictor, so "few committee members are from southern Europe" does
not give "few female committee members are": not in P, W or M, nor in F
with background knowledge. So 76 stays unknown in every encoding, by the
pipeline's rule that "yes" needs every reading.
-/

namespace FraCaS.Encodings.Modified
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed
open FraCaS.Encodings.Equivalence (card_filter_mono)

/-- Counting through a noun's embedding is monotone in what is counted;
no injectivity needed. -/
theorem cardT_mono {N A : Type} [Fintype N] (e : N → A) {P Q : A → Prop}
    (h : ∀ y, P (e y) → Q (e y)) : cardT e P ≤ cardT e Q := by
  unfold cardT
  exact card_filter_mono h

/-! ## P: the noun conjoined with an intersective adjective -/

theorem p_055 : P.fracas_055_yes_0 ∧ P.fracas_055_yes_1 := by
  constructor
  · unfold P.fracas_055_yes_0
    intros
    rename_i h
    obtain ⟨x, hx, hq⟩ := h
    exact ⟨x, hx.1, hq⟩
  · unfold P.fracas_055_yes_1
    intros
    rename_i h _
    exact le_trans h (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩))

theorem p_057 : P.fracas_057_yes_0 := by
  unfold P.fracas_057_yes_0
  intros
  rename_i h
  exact le_trans h (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩))

theorem p_059 : P.fracas_059_yes_0 := by
  unfold P.fracas_059_yes_0
  intros
  rename_i h
  exact le_trans h (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩))

theorem p_063 : P.fracas_063_yes_0 := by
  unfold P.fracas_063_yes_0
  intros
  rename_i h
  exact le_trans h (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩))

theorem p_076_reading_0 : P.fracas_076_yes_0 := by
  unfold P.fracas_076_yes_0
  intros
  rename_i h
  exact le_trans (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩)) h

theorem p_080 : P.fracas_080_yes_0 := by
  unfold P.fracas_080_yes_0
  intros
  rename_i h
  exact le_trans (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩)) h

/-! ## W: the same, at the actual world -/

theorem w_055 : W.fracas_055_yes_0 ∧ W.fracas_055_yes_1 := by
  constructor
  · unfold W.fracas_055_yes_0
    intros
    rename_i h
    obtain ⟨x, hx, hq⟩ := h
    exact ⟨x, hx.1, hq⟩
  · unfold W.fracas_055_yes_1
    intros
    rename_i h _
    exact le_trans h (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩))

theorem w_057 : W.fracas_057_yes_0 := by
  unfold W.fracas_057_yes_0
  intros
  rename_i h
  exact le_trans h (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩))

theorem w_059 : W.fracas_059_yes_0 := by
  unfold W.fracas_059_yes_0
  intros
  rename_i h
  exact le_trans h (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩))

theorem w_063 : W.fracas_063_yes_0 := by
  unfold W.fracas_063_yes_0
  intros
  rename_i h
  exact le_trans h (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩))

theorem w_076_reading_0 : W.fracas_076_yes_0 := by
  unfold W.fracas_076_yes_0
  intros
  rename_i h
  exact le_trans (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩)) h

theorem w_080 : W.fracas_080_yes_0 := by
  unfold W.fracas_080_yes_0
  intros
  rename_i h
  exact le_trans (card_filter_mono (by intro x hx; exact ⟨hx.1.1, hx.2⟩)) h

/-! ## M: the adjective restricts the noun's type

Premise and hypothesis count the same type, so no injectivity is needed
(`cardT_mono`). -/

theorem m_029 : M.fracas_029_yes_0 := by
  unfold M.fracas_029_yes_0
  intros
  rename_i hmono hprem
  obtain ⟨h1, h2⟩ := hprem
  exact ⟨h1, fun y hy => hmono _ _ (by rintro x ⟨y', -, rfl⟩; exact ⟨y', rfl⟩) _ (h2 y hy)⟩

theorem m_055 : M.fracas_055_yes_0 ∧ M.fracas_055_yes_1 := by
  constructor
  · unfold M.fracas_055_yes_0
    intros
    rename_i h
    obtain ⟨y, -, hq⟩ := h
    exact ⟨y, trivial, hq⟩
  · unfold M.fracas_055_yes_1
    intros
    rename_i h _
    exact le_trans h (cardT_mono _ fun y hy => ⟨trivial, hy.2⟩)

theorem m_057 : M.fracas_057_yes_0 := by
  unfold M.fracas_057_yes_0
  intros
  rename_i h
  exact le_trans h (cardT_mono _ fun y hy => ⟨trivial, hy.2⟩)

theorem m_059 : M.fracas_059_yes_0 := by
  unfold M.fracas_059_yes_0
  intros
  rename_i h
  exact le_trans h (cardT_mono _ fun y hy => ⟨trivial, hy.2⟩)

theorem m_063 : M.fracas_063_yes_0 := by
  unfold M.fracas_063_yes_0
  intros
  rename_i h
  exact le_trans h (cardT_mono _ fun y hy => ⟨trivial, hy.2⟩)

theorem m_076_reading_0 : M.fracas_076_yes_0 := by
  unfold M.fracas_076_yes_0
  intros
  rename_i h
  exact le_trans (cardT_mono _ fun y hy => ⟨trivial, hy.2⟩) h

theorem m_080 : M.fracas_080_yes_0 := by
  unfold M.fracas_080_yes_0
  intros
  rename_i h
  exact le_trans (cardT_mono _ fun y hy => ⟨trivial, hy.2⟩) h

end FraCaS.Encodings.Modified
