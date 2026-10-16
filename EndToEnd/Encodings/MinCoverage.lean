import EndToEnd.Encodings.TwoCriteria

/-!
# Not every minimum of coverage functions is counting by two criteria

`TwoCriteria.lean` shows that counting by two criteria is a minimum of
coverage functions (`copredication_is_min`). Here: the converse fails.

- **`isMinCov_of_isCount2`.** Every counting function of a noun with two
  criteria is a minimum of integer coverage functions.
- **Two laws of counting by criteria**, which minima of coverage
  functions need not obey:
  - **subadditivity** (`count2_subadd`): `count (P ∪ Q) ≤ count P + count Q`.
    A set of things distinct by both criteria splits into its `P` part
    and the rest;
  - **"at most one" is decided by pairs** (`count2_pairwise`): if each of
    `P ∪ Q`, `Q ∪ R`, `P ∪ R` has at most one thing counted, so does
    `P ∪ Q ∪ R`. Two things distinct both ways lie together in one of
    the three.
- **`not_subadd_example`.** With two individuals, the minimum of "units
  meeting `{a}`" and "units meeting `{b}`" is 0 on each and 1 on both:
  not subadditive, so not counting by two criteria.
- **`not_pairwise_example`.** With three individuals, the minimum of
  three coverage functions, each with one unit covering a pair and one
  covering the third individual, is 1 on every pair and 2 on all three.
  It is subadditive (`f3_subadd`) but breaks the pairwise law.

So the counting functions of nouns with two criteria lie strictly
between the coverage functions (one criterion; strictly, by
`FullAbstractionMulti.not_single`) and the minima of coverage functions.
Both laws hold for any family of criteria, by the same arguments; they
are proved here for two. An exact characterization remains open.
-/

namespace FraCaS.Encodings.MinCoverage
open FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence
open FraCaS.Encodings.FullAbstraction (NounI meetsSum count_meets)
open FraCaS.Encodings.TwoCriteria
open Classical

/-! ## The two classes -/

/-- `f` counts the things of some noun with two criteria. -/
def IsCount2 {A : Type} (f : (A → Prop) → Nat) : Prop :=
  ∃ (T : Type) (_ : Fintype T) (emb : T → A) (K1 K2 : Type) (c1 : T → K1) (c2 : T → K2),
    ∀ P, count2 c1 c2 (fun y => P (emb y)) = f P

/-- `f` is the least of a family of integer coverage functions, the least
attained at every `P`. -/
def IsMinCov {A : Type} [Fintype A] (f : (A → Prop) → Nat) : Prop :=
  ∃ (ι : Type) (u : ι → Finset A → Nat),
    (∀ i P, f P ≤ meetsSum (u i) P) ∧ ∀ P, ∃ i, f P = meetsSum (u i) P

/-- **Counting by two criteria is a minimum of coverage functions.** -/
theorem isMinCov_of_isCount2 {A : Type} [Fintype A] {f : (A → Prop) → Nat}
    (hf : IsCount2 f) : IsMinCov f := by
  obtain ⟨T, inst, emb, K1, K2, c1, c2, h⟩ := hf
  refine ⟨Finset K2, fun S => (mixNoun T emb c1 c2 S).units, fun S P => ?_, fun P => ?_⟩
  · rw [← h P, ← count_meets]
    exact (copredication_is_min T emb c1 c2 P).1 S
  · obtain ⟨S, hS⟩ := (copredication_is_min T emb c1 c2 P).2
    exact ⟨S, by rw [← h P, ← count_meets]; exact hS⟩

/-! ## Two laws of counting by two criteria -/

section
variable {T K1 K2 : Type} [Fintype T] (c1 : T → K1) (c2 : T → K2)

theorem two_le_count2_iff (Q : T → Prop) :
    2 ≤ count2 c1 c2 Q ↔ ∃ y y', Q y ∧ Q y' ∧ c1 y ≠ c1 y' ∧ c2 y ≠ c2 y' := by
  constructor
  · intro h
    obtain ⟨S, h2, hQ, hi1, hi2⟩ := (le_count2_iff c1 c2 Q 2).mp h
    obtain ⟨a, ha, b, hb, hab⟩ := (Finset.one_lt_card (s := S)).mp (by omega)
    exact ⟨a, b, hQ a ha, hQ b hb, fun e => hab (hi1 ha hb e), fun e => hab (hi2 ha hb e)⟩
  · rintro ⟨y, y', hy, hy', h1, h2⟩
    have hne : y ≠ y' := fun e => h1 (congrArg c1 e)
    have hmem : ∀ x, x ∈ ({y, y'} : Finset T) → x = y ∨ x = y' := fun x hx => by
      rcases Finset.mem_insert.mp hx with e | hx
      · exact Or.inl e
      · exact Or.inr (Finset.mem_singleton.mp hx)
    refine (le_count2_iff c1 c2 Q 2).mpr ⟨{y, y'}, (Finset.card_pair hne).ge, fun x hx => ?_, ?_, ?_⟩
    · rcases hmem x hx with rfl | rfl
      · exact hy
      · exact hy'
    · intro a ha b hb hab
      rcases hmem a (Finset.mem_coe.mp ha) with rfl | rfl <;>
        rcases hmem b (Finset.mem_coe.mp hb) with rfl | rfl
      · rfl
      · exact absurd hab h1
      · exact absurd hab.symm h1
      · rfl
    · intro a ha b hb hab
      rcases hmem a (Finset.mem_coe.mp ha) with rfl | rfl <;>
        rcases hmem b (Finset.mem_coe.mp hb) with rfl | rfl
      · rfl
      · exact absurd hab h2
      · exact absurd hab.symm h2
      · rfl

/-- **Subadditivity.** -/
theorem count2_subadd (P Q : T → Prop) :
    count2 c1 c2 (fun y => P y ∨ Q y) ≤ count2 c1 c2 P + count2 c1 c2 Q := by
  obtain ⟨D, hn, hPQ, h1, h2⟩ := (le_count2_iff c1 c2 (fun y => P y ∨ Q y) _).mp le_rfl
  have hs := card_filter_split D P
  have hsub1 : (↑(D.filter P) : Set T) ⊆ ↑D := Finset.coe_subset.mpr (Finset.filter_subset _ _)
  have hsub2 : (↑(D.filter (fun y => ¬ P y)) : Set T) ⊆ ↑D :=
    Finset.coe_subset.mpr (Finset.filter_subset _ _)
  have hA : (D.filter P).card ≤ count2 c1 c2 P :=
    (le_count2_iff c1 c2 P _).mpr ⟨D.filter P, le_rfl, fun x hx => (Finset.mem_filter.mp hx).2,
      h1.mono hsub1, h2.mono hsub1⟩
  have hB : (D.filter (fun y => ¬ P y)).card ≤ count2 c1 c2 Q :=
    (le_count2_iff c1 c2 Q _).mpr ⟨D.filter (fun y => ¬ P y), le_rfl, fun x hx => by
      obtain ⟨hxD, hnP⟩ := Finset.mem_filter.mp hx
      exact (hPQ x hxD).resolve_left hnP, h1.mono hsub2, h2.mono hsub2⟩
  omega

/-- **"At most one" is decided by pairs.** -/
theorem count2_pairwise (P Q R : T → Prop)
    (hpq : count2 c1 c2 (fun y => P y ∨ Q y) ≤ 1) (hqr : count2 c1 c2 (fun y => Q y ∨ R y) ≤ 1)
    (hpr : count2 c1 c2 (fun y => P y ∨ R y) ≤ 1) :
    count2 c1 c2 (fun y => P y ∨ Q y ∨ R y) ≤ 1 := by
  by_contra hlt
  obtain ⟨y, y', hy, hy', h1, h2⟩ :=
    (two_le_count2_iff c1 c2 (fun y => P y ∨ Q y ∨ R y)).mp (by omega)
  have bad : ∀ U : T → Prop, count2 c1 c2 U ≤ 1 → U y → U y' → False := fun U hU hu hu' => by
    have := (two_le_count2_iff c1 c2 U).mpr ⟨y, y', hu, hu', h1, h2⟩
    omega
  rcases hy with h | h | h <;> rcases hy' with h' | h' | h'
  · exact bad _ hpq (Or.inl h) (Or.inl h')
  · exact bad _ hpq (Or.inl h) (Or.inr h')
  · exact bad _ hpr (Or.inl h) (Or.inr h')
  · exact bad _ hpq (Or.inr h) (Or.inl h')
  · exact bad _ hpq (Or.inr h) (Or.inr h')
  · exact bad _ hqr (Or.inl h) (Or.inr h')
  · exact bad _ hpr (Or.inr h) (Or.inl h')
  · exact bad _ hqr (Or.inr h) (Or.inl h')
  · exact bad _ hqr (Or.inr h) (Or.inr h')

end

theorem IsCount2.subadd {A : Type} {f : (A → Prop) → Nat} (hf : IsCount2 f) (P Q : A → Prop) :
    f (fun x => P x ∨ Q x) ≤ f P + f Q := by
  obtain ⟨T, inst, emb, K1, K2, c1, c2, h⟩ := hf
  calc f (fun x => P x ∨ Q x) = count2 c1 c2 (fun y => P (emb y) ∨ Q (emb y)) := (h _).symm
    _ ≤ count2 c1 c2 (fun y => P (emb y)) + count2 c1 c2 (fun y => Q (emb y)) :=
        count2_subadd c1 c2 _ _
    _ = f P + f Q := by rw [h P, h Q]

theorem IsCount2.pairwise {A : Type} {f : (A → Prop) → Nat} (hf : IsCount2 f)
    (P Q R : A → Prop) (hpq : f (fun x => P x ∨ Q x) ≤ 1) (hqr : f (fun x => Q x ∨ R x) ≤ 1)
    (hpr : f (fun x => P x ∨ R x) ≤ 1) : f (fun x => P x ∨ Q x ∨ R x) ≤ 1 := by
  obtain ⟨T, inst, emb, K1, K2, c1, c2, h⟩ := hf
  rw [← h] at hpq hqr hpr ⊢
  exact count2_pairwise c1 c2 (fun y => P (emb y)) (fun y => Q (emb y)) (fun y => R (emb y))
    hpq hqr hpr

/-! ## Coverage functions with single units -/

/-- One unit covering `S0`. -/
noncomputable def oneUnit {A : Type} (S0 : Finset A) : Finset A → Nat := fun S => if S = S0 then 1 else 0

theorem meetsSum_oneUnit {A : Type} [Fintype A] (S0 : Finset A) (P : A → Prop) :
    meetsSum (oneUnit S0) P = if ∃ x ∈ S0, P x then 1 else 0 := by
  unfold meetsSum oneUnit
  rw [Finset.sum_eq_single S0]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem meetsSum_oneUnit_pos {A : Type} [Fintype A] (S0 : Finset A) (P : A → Prop)
    (h : ∃ x ∈ S0, P x) : meetsSum (oneUnit S0) P = 1 := by
  rw [meetsSum_oneUnit, if_pos h]

theorem meetsSum_oneUnit_neg {A : Type} [Fintype A] (S0 : Finset A) (P : A → Prop)
    (h : ¬ ∃ x ∈ S0, P x) : meetsSum (oneUnit S0) P = 0 := by
  rw [meetsSum_oneUnit, if_neg h]

theorem meetsSum_add {A : Type} [Fintype A] (u v : Finset A → Nat) (P : A → Prop) :
    meetsSum (fun S => u S + v S) P = meetsSum u P + meetsSum v P := by
  unfold meetsSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun R _ => ?_
  split_ifs <;> simp

/-! ## Two individuals: not subadditive -/

/-- The least of "units meeting `{true}`" and "units meeting `{false}`". -/
noncomputable def f2 (P : Bool → Prop) : Nat :=
  min (meetsSum (oneUnit {true}) P) (meetsSum (oneUnit {false}) P)

theorem f2_isMinCov : IsMinCov f2 := by
  refine ⟨Bool, fun b => if b then oneUnit {true} else oneUnit {false}, fun b P => ?_, fun P => ?_⟩
  · cases b
    · exact min_le_right _ _
    · exact min_le_left _ _
  · rcases min_choice (meetsSum (oneUnit {true}) P) (meetsSum (oneUnit {false}) P) with e | e
    · exact ⟨true, e⟩
    · exact ⟨false, e⟩

/-- **A minimum of coverage functions that is not counting by two
criteria.** -/
theorem not_subadd_example : IsMinCov f2 ∧ ¬ IsCount2 f2 := by
  refine ⟨f2_isMinCov, fun hf => ?_⟩
  have h := hf.subadd (fun x => x = true) (fun x => x = false)
  have e1 : f2 (fun x => x = true ∨ x = false) = 1 := by
    unfold f2
    rw [meetsSum_oneUnit_pos {true} (fun x => x = true ∨ x = false)
        ⟨true, Finset.mem_singleton_self _, Or.inl rfl⟩,
      meetsSum_oneUnit_pos {false} (fun x => x = true ∨ x = false)
        ⟨false, Finset.mem_singleton_self _, Or.inr rfl⟩]
    exact min_self 1
  have e2 : f2 (fun x => x = true) = 0 := by
    unfold f2
    rw [meetsSum_oneUnit_neg {false} (fun x => x = true) (by decide)]
    exact Nat.min_zero _
  have e3 : f2 (fun x => x = false) = 0 := by
    unfold f2
    rw [meetsSum_oneUnit_neg {true} (fun x => x = false) (by decide)]
    exact Nat.zero_min _
  omega

/-! ## Three individuals: subadditive, but not decided by pairs -/

/-- One unit covering the pair without `i`, one covering `i`. -/
noncomputable def g (S1 : Finset (Fin 3)) (i : Fin 3) : Finset (Fin 3) → Nat :=
  fun S => oneUnit S1 S + oneUnit {i} S

noncomputable def f3 (P : Fin 3 → Prop) : Nat :=
  min (meetsSum (g {1, 2} 0) P) (min (meetsSum (g {0, 2} 1) P) (meetsSum (g {0, 1} 2) P))

theorem f3_isMinCov : IsMinCov f3 := by
  refine ⟨Option Bool,
    fun o => match o with
      | none => g {1, 2} 0
      | some false => g {0, 2} 1
      | some true => g {0, 1} 2,
    fun o P => ?_, fun P => ?_⟩
  · match o with
    | none => exact min_le_left _ _
    | some false => exact (min_le_right _ _).trans (min_le_left _ _)
    | some true => exact (min_le_right _ _).trans (min_le_right _ _)
  · rcases min_choice (meetsSum (g {1, 2} 0) P)
        (min (meetsSum (g {0, 2} 1) P) (meetsSum (g {0, 1} 2) P)) with e | e
    · exact ⟨none, e⟩
    · rcases min_choice (meetsSum (g {0, 2} 1) P) (meetsSum (g {0, 1} 2) P) with e' | e'
      · exact ⟨some false, e.trans e'⟩
      · exact ⟨some true, e.trans e'⟩

theorem meetsSum_g (S1 : Finset (Fin 3)) (i : Fin 3) (P : Fin 3 → Prop) :
    meetsSum (g S1 i) P = meetsSum (oneUnit S1) P + meetsSum (oneUnit {i}) P :=
  meetsSum_add _ _ P

/-- `f3` in closed form: 0, 1 or 2 by how many individuals are `P`. -/
theorem f3_eq (P : Fin 3 → Prop) :
    f3 P = if P 0 ∧ P 1 ∧ P 2 then 2 else if P 0 ∨ P 1 ∨ P 2 then 1 else 0 := by
  unfold f3
  rw [meetsSum_g, meetsSum_g, meetsSum_g]
  simp only [meetsSum_oneUnit]
  by_cases h0 : P 0 <;> by_cases h1 : P 1 <;> by_cases h2 : P 2 <;> simp [h0, h1, h2] <;> omega

/-- `f3` is subadditive. -/
theorem f3_subadd (P Q : Fin 3 → Prop) : f3 (fun x => P x ∨ Q x) ≤ f3 P + f3 Q := by
  rw [f3_eq, f3_eq, f3_eq]
  by_cases a0 : P 0 <;> by_cases a1 : P 1 <;> by_cases a2 : P 2 <;>
    by_cases b0 : Q 0 <;> by_cases b1 : Q 1 <;> by_cases b2 : Q 2 <;>
      simp [a0, a1, a2, b0, b1, b2] <;> omega

/-- **A subadditive minimum of coverage functions that is not counting by
two criteria**: 1 on every pair of individuals, 2 on all three. -/
theorem not_pairwise_example :
    IsMinCov f3 ∧ (∀ P Q, f3 (fun x => P x ∨ Q x) ≤ f3 P + f3 Q) ∧ ¬ IsCount2 f3 := by
  refine ⟨f3_isMinCov, f3_subadd, fun hf => ?_⟩
  have h := hf.pairwise (fun x => x = 0) (fun x => x = 1) (fun x => x = 2)
    (by rw [f3_eq]; simp) (by rw [f3_eq]; simp) (by rw [f3_eq]; simp)
  rw [f3_eq] at h
  simp at h

end FraCaS.Encodings.MinCoverage

/-- info: 'FraCaS.Encodings.MinCoverage.not_pairwise_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.MinCoverage.not_pairwise_example

/-- info: 'FraCaS.Encodings.MinCoverage.isMinCov_of_isCount2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.MinCoverage.isMinCov_of_isCount2
