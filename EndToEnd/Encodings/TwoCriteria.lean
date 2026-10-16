import EndToEnd.Encodings.CountingLaws
import EndToEnd.Encodings.TranslationMulti

/-!
# Counting by two criteria is the least of the mixed single criteria

A copredicated noun ("John picked up and mastered three books") counts
things that are distinct by two criteria at once, say by volume and by
text (`TranslationMulti.countF`, Gotham's double distinctness). Those
counts need not come from any single criterion
(`FullAbstractionMulti.not_single`). This file says what they are.

**Mixed criteria.** Divide the texts into two groups, `S` and the rest.
Count a thing by its volume if its text is in `S`, and by its text
otherwise (`mix c1 c2 S`). That is a single criterion.

**`count2_eq_min`.** The number of `Q`s distinct by both criteria is the
least, over all ways `S` of dividing the texts, of the number of `Q`s
counted by the mixed criterion:

- every mixed criterion counts at least as many (`count2_le_mix`):
  things distinct both ways are distinct by any mixture;
- some mixed criterion counts exactly as many (`exists_mix_le`). This is
  König's theorem for bipartite graphs (volumes and texts, each thing an
  edge), proved here from Hall's marriage theorem in Mathlib.

**`copredication_is_min`.** So a copredicated noun counts as the least of
a family of nouns with one criterion each, with the same things and
embedding. By `CountingLaws.representation` each of those counts is an
integer coverage function: **counting by two criteria is a minimum of
coverage functions.** Whether every such minimum arises from two
criteria is open.
-/

namespace FraCaS.Encodings.TwoCriteria
open FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence
open FraCaS.Encodings.TranslationMulti (countF le_countF_bool_iff)
open FraCaS.Encodings.FullAbstraction (NounI)
open Classical

variable {N K1 K2 : Type} [Fintype N]

/-! ## Counting by two criteria -/

/-- The size of a largest set of `Q`s distinct by `c1` and by `c2`. -/
noncomputable def count2 (c1 : N → K1) (c2 : N → K2) (Q : N → Prop) : Nat :=
  ((Finset.univ.filter Q).powerset.filter
    (fun S : Finset N => Set.InjOn c1 ↑S ∧ Set.InjOn c2 ↑S)).sup Finset.card

theorem le_count2_iff (c1 : N → K1) (c2 : N → K2) (Q : N → Prop) (n : Nat) :
    n ≤ count2 c1 c2 Q ↔
      ∃ S : Finset N, n ≤ S.card ∧ (∀ x ∈ S, Q x) ∧ Set.InjOn c1 ↑S ∧ Set.InjOn c2 ↑S := by
  unfold count2
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨∅, Nat.zero_le _, by simp, by simp, by simp⟩
    · obtain ⟨S, hS, hle⟩ := (Finset.le_sup_iff hn).mp h
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      exact ⟨S, hle, fun x hx => (Finset.mem_filter.mp (hS.1 hx)).2, hS.2.1, hS.2.2⟩
  · rintro ⟨S, hn, hQ, h1, h2⟩
    refine le_trans hn (Finset.le_sup (f := Finset.card) ?_)
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ x hx⟩, h1, h2⟩

/-- It is `TranslationMulti`'s count by a family of two criteria. -/
theorem countF_eq_count2 {K : Bool → Type} (c : ∀ i, N → K i) (Q : N → Prop) :
    countF c Q = count2 (c true) (c false) Q := by
  apply le_antisymm
  · obtain ⟨S, h1, h2, h3, h4⟩ := (le_countF_bool_iff c Q (countF c Q)).mp le_rfl
    exact (le_count2_iff _ _ _ _).mpr ⟨S, h1, h2, h3, h4⟩
  · obtain ⟨S, h1, h2, h3, h4⟩ :=
      (le_count2_iff (c true) (c false) Q (count2 (c true) (c false) Q)).mp le_rfl
    exact (le_countF_bool_iff c Q _).mpr ⟨S, h1, h2, h3, h4⟩

/-- A set splits into the members that are `p` and those that are not. -/
theorem card_filter_split {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun a => ¬ p a)).card = s.card := by
  have hu : s.filter p ∪ s.filter (fun a => ¬ p a) = s := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hp : p a
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨h, hp⟩
  have hi : (s.filter p ∩ s.filter (fun a => ¬ p a)).card = 0 := by
    by_contra h0
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp ha
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have e := Finset.card_union_add_card_inter (s.filter p) (s.filter (fun a => ¬ p a))
  rw [hu, hi] at e
  omega

/-! ## Mixed criteria -/

/-- Count by `c1` (volume) when `c2` (text) is in `S`, by `c2` otherwise. -/
noncomputable def mix (c1 : N → K1) (c2 : N → K2) (S : Finset K2) (y : N) : K2 ⊕ K1 :=
  if c2 y ∈ S then Sum.inr (c1 y) else Sum.inl (c2 y)

/-- **Every mixed criterion counts at least as many.** -/
theorem count2_le_mix (c1 : N → K1) (c2 : N → K2) (Q : N → Prop) (S : Finset K2) :
    count2 c1 c2 Q ≤ countBy (mix c1 c2 S) Q := by
  obtain ⟨D, hn, hQ, h1, h2⟩ := (le_count2_iff c1 c2 Q _).mp le_rfl
  have hinj : Set.InjOn (mix c1 c2 S) ↑D := by
    intro a ha b hb h
    unfold mix at h
    by_cases ha2 : c2 a ∈ S <;> by_cases hb2 : c2 b ∈ S
    · rw [if_pos ha2, if_pos hb2] at h
      exact h1 ha hb (Sum.inr.inj h)
    · rw [if_pos ha2, if_neg hb2] at h
      exact absurd h Sum.inr_ne_inl
    · rw [if_neg ha2, if_pos hb2] at h
      exact absurd h Sum.inl_ne_inr
    · rw [if_neg ha2, if_neg hb2] at h
      exact h2 ha hb (Sum.inl.inj h)
  calc count2 c1 c2 Q ≤ D.card := hn
    _ = (D.image (mix c1 c2 S)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ countBy (mix c1 c2 S) Q :=
        Finset.card_le_card (Finset.image_subset_image fun y hy =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ y hy⟩)

/-- **Some mixed criterion counts exactly as many** (König's theorem,
from Hall's). -/
theorem exists_mix_le (c1 : N → K1) (c2 : N → K2) (Q : N → Prop) :
    ∃ S : Finset K2, countBy (mix c1 c2 S) Q ≤ count2 c1 c2 Q := by
  -- the texts of the `Q`s, and the volumes holding each text
  let L : Finset K2 := (Finset.univ.filter Q).image c2
  let nb : K2 → Finset K1 := fun t => (Finset.univ.filter (fun y => Q y ∧ c2 y = t)).image c1
  -- the deficiency of a set of texts, and a set of texts of largest deficiency
  let df : Finset K2 → Nat := fun S => S.card - (S.biUnion nb).card
  obtain ⟨S0, hS0, hmax⟩ := Finset.exists_max_image L.powerset df ⟨∅, Finset.empty_mem_powerset _⟩
  have hdd : df S0 = S0.card - (S0.biUnion nb).card := rfl
  -- Hall: with `df S0` extra volumes, every text can be matched
  let T : {t // t ∈ L} → Finset (K1 ⊕ Fin (df S0)) :=
    fun t => (nb t.1).disjSum (Finset.univ : Finset (Fin (df S0)))
  have hall : ∀ s : Finset {t // t ∈ L}, s.card ≤ (s.biUnion T).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · simp
    · have hSL : s.image Subtype.val ⊆ L := fun t ht => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
        exact i.2
      have hS : (s.image Subtype.val).card = s.card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      have hle : df (s.image Subtype.val) ≤ df S0 := hmax _ (Finset.mem_powerset.mpr hSL)
      have hle' : (s.image Subtype.val).card - ((s.image Subtype.val).biUnion nb).card ≤ df S0 :=
        hle
      have hsub : ((s.image Subtype.val).biUnion nb).disjSum (Finset.univ : Finset (Fin (df S0)))
          ⊆ s.biUnion T := by
        intro z hz
        cases z with
        | inl a =>
          obtain ⟨t, ht, ha⟩ := Finset.mem_biUnion.mp (Finset.inl_mem_disjSum.mp hz)
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
          exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.inl_mem_disjSum.mpr ha⟩
        | inr j =>
          exact Finset.mem_biUnion.mpr ⟨i0, hi0, Finset.inr_mem_disjSum.mpr (Finset.mem_univ j)⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at hc
      omega
  obtain ⟨f, hfinj, hfT⟩ : ∃ f : {t // t ∈ L} → K1 ⊕ Fin (df S0),
      Function.Injective f ∧ ∀ x, f x ∈ T x := by
    first
    | exact (Finset.all_card_le_biUnion_card_iff_existsInjective T).mp hall
    | exact (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp hall
  -- the texts matched to real volumes
  let M := (Finset.univ : Finset {t // t ∈ L}).filter (fun t => ∃ a, f t = Sum.inl a)
  have hcomp : ((Finset.univ : Finset {t // t ∈ L}).filter
      (fun t => ¬ ∃ a, f t = Sum.inl a)).card ≤ df S0 := by
    have hsub : ((Finset.univ : Finset {t // t ∈ L}).filter
        (fun t => ¬ ∃ a, f t = Sum.inl a)).image f ⊆
          (Finset.univ : Finset (Fin (df S0))).image Sum.inr := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      have hn := (Finset.mem_filter.mp ht).2
      cases hft : f t with
      | inl a => exact (hn ⟨a, hft⟩).elim
      | inr j => exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_image_of_injective _ Sum.inr_injective,
      Finset.card_univ, Fintype.card_fin] at hc
    exact hc
  have huniv : (Finset.univ : Finset {t // t ∈ L}).card = L.card := by
    rw [Finset.card_univ, Fintype.card_coe]
  have hsplit : M.card + ((Finset.univ : Finset {t // t ∈ L}).filter
      (fun t => ¬ ∃ a, f t = Sum.inl a)).card = L.card := by
    rw [← huniv]
    exact card_filter_split _ _
  -- each matched text has a thing with that text and that volume
  have hex : ∀ t ∈ M, ∃ y, Q y ∧ c2 y = t.1 ∧ f t = Sum.inl (c1 y) := by
    intro t ht
    obtain ⟨a, ha⟩ := (Finset.mem_filter.mp ht).2
    have hmem := hfT t
    rw [ha] at hmem
    obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp (Finset.inl_mem_disjSum.mp hmem)
    obtain ⟨hQy, hct⟩ := (Finset.mem_filter.mp hy).2
    exact ⟨y, hQy, hct, by rw [ha, hya]⟩
  let g : {t // t ∈ M} → N := fun t => (hex t.1 t.2).choose
  have hg : ∀ t : {t // t ∈ M}, Q (g t) ∧ c2 (g t) = t.1.1 ∧ f t.1 = Sum.inl (c1 (g t)) :=
    fun t => (hex t.1 t.2).choose_spec
  have hginj : Function.Injective g := by
    intro t t' h
    have e : t.1.1 = t'.1.1 := by rw [← (hg t).2.1, ← (hg t').2.1, h]
    exact Subtype.ext (Subtype.ext e)
  have hcount : M.card ≤ count2 c1 c2 Q := by
    have hD : (M.attach.image g).card = M.card := by
      rw [Finset.card_image_of_injective _ hginj, Finset.card_attach]
    rw [← hD]
    refine (le_count2_iff c1 c2 Q _).mpr ⟨M.attach.image g, le_rfl, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hy
      exact (hg t).1
    · intro y hy y' hy' h
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      obtain ⟨t', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy')
      have hff : f t.1 = f t'.1 := by rw [(hg t).2.2, (hg t').2.2, h]
      exact congrArg g (Subtype.ext (hfinj hff))
    · intro y hy y' hy' h
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      obtain ⟨t', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy')
      have e : t.1.1 = t'.1.1 := by rw [← (hg t).2.1, ← (hg t').2.1, h]
      exact congrArg g (Subtype.ext (Subtype.ext e))
  -- so at least `|L| - df S0` things are distinct both ways
  have hbig : L.card - df S0 ≤ count2 c1 c2 Q := by omega
  -- the mixed criterion that attains it
  by_cases hd : df S0 = 0
  · refine ⟨∅, ?_⟩
    have hsub0 : (Finset.univ.filter Q).image (mix c1 c2 ∅) ⊆ L.image Sum.inl := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      have hne : c2 y ∉ (∅ : Finset K2) := fun h => by simp at h
      refine Finset.mem_image.mpr ⟨c2 y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
      unfold mix
      rw [if_neg hne]
    have e1 := Finset.card_le_card hsub0
    have e2 := Finset.card_image_le (s := L) (f := Sum.inl (β := K1))
    have hc : countBy (mix c1 c2 ∅) Q = ((Finset.univ.filter Q).image (mix c1 c2 ∅)).card := rfl
    omega
  · refine ⟨S0, ?_⟩
    have hsub : S0 ⊆ L := Finset.mem_powerset.mp hS0
    have himg : (Finset.univ.filter Q).image (mix c1 c2 S0) ⊆
        (L.filter (fun t => ¬ t ∈ S0)).image Sum.inl ∪ (S0.biUnion nb).image Sum.inr := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      have hQy := (Finset.mem_filter.mp hy).2
      unfold mix
      by_cases h2 : c2 y ∈ S0
      · rw [if_pos h2]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c1 y, Finset.mem_biUnion.mpr
          ⟨c2 y, h2, Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQy, rfl⟩,
            rfl⟩⟩, rfl⟩)
      · rw [if_neg h2]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c2 y, Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQy⟩, rfl⟩, h2⟩, rfl⟩)
    have e1 := Finset.card_le_card himg
    have e2 := Finset.card_union_le ((L.filter (fun t => ¬ t ∈ S0)).image Sum.inl)
      ((S0.biUnion nb).image (Sum.inr : K1 → K2 ⊕ K1))
    have e3 := Finset.card_image_le (s := L.filter (fun t => ¬ t ∈ S0)) (f := Sum.inl (β := K1))
    have e4 := Finset.card_image_le (s := S0.biUnion nb) (f := Sum.inr (α := K2))
    have e5 : (L.filter (fun t => t ∈ S0)).card + (L.filter (fun t => ¬ t ∈ S0)).card = L.card :=
      card_filter_split _ _
    have e6 : S0.card ≤ (L.filter (fun t => t ∈ S0)).card :=
      Finset.card_le_card fun t ht => Finset.mem_filter.mpr ⟨hsub ht, ht⟩
    have hc : countBy (mix c1 c2 S0) Q = ((Finset.univ.filter Q).image (mix c1 c2 S0)).card := rfl
    omega

/-- **Counting by two criteria is the least mixed count.** -/
theorem count2_eq_min (c1 : N → K1) (c2 : N → K2) (Q : N → Prop) :
    (∀ S, count2 c1 c2 Q ≤ countBy (mix c1 c2 S) Q) ∧
      ∃ S, count2 c1 c2 Q = countBy (mix c1 c2 S) Q := by
  refine ⟨count2_le_mix c1 c2 Q, ?_⟩
  obtain ⟨S, hS⟩ := exists_mix_le c1 c2 Q
  exact ⟨S, le_antisymm (count2_le_mix c1 c2 Q S) hS⟩

/-! ## Copredicated nouns as minima of nouns with one criterion -/

/-- The noun with the same things and embedding, counted by the mixed
criterion. -/
noncomputable def mixNoun {A : Type} (T : Type) [Fintype T] (emb : T → A) (c1 : T → K1)
    (c2 : T → K2) (S : Finset K2) : NounI A :=
  ⟨T, inferInstance, emb, K2 ⊕ K1, mix c1 c2 S⟩

theorem mixNoun_count {A : Type} (T : Type) [Fintype T] (emb : T → A) (c1 : T → K1)
    (c2 : T → K2) (S : Finset K2) (P : A → Prop) :
    (mixNoun T emb c1 c2 S).count P = countBy (mix c1 c2 S) (fun y => P (emb y)) :=
  countBy_eq_of_kernel fun _ _ _ _ => Iff.rfl

/-- **A copredicated noun counts as the least of a family of nouns with
one criterion each.** -/
theorem copredication_is_min {A : Type} (T : Type) [Fintype T] (emb : T → A) (c1 : T → K1)
    (c2 : T → K2) (P : A → Prop) :
    (∀ S, count2 c1 c2 (fun y => P (emb y)) ≤ (mixNoun T emb c1 c2 S).count P) ∧
      ∃ S, count2 c1 c2 (fun y => P (emb y)) = (mixNoun T emb c1 c2 S).count P := by
  obtain ⟨h1, S, h2⟩ := count2_eq_min c1 c2 (fun y => P (emb y))
  exact ⟨fun S => (h1 S).trans (mixNoun_count T emb c1 c2 S P).ge,
    S, h2.trans (mixNoun_count T emb c1 c2 S P).symm⟩

end FraCaS.Encodings.TwoCriteria

/-- info: 'FraCaS.Encodings.TwoCriteria.count2_eq_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.TwoCriteria.count2_eq_min

/-- info: 'FraCaS.Encodings.TwoCriteria.copredication_is_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.TwoCriteria.copredication_is_min
