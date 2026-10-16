import EndToEnd.Encodings.MinCoverage

/-!
# The two laws are not enough: an odd-cycle law

`MinCoverage.lean` gives two laws of counting by two criteria
(subadditivity, and "at most one" decided by pairs) and shows that some
minima of coverage functions break them. Are the two laws sufficient,
i.e. is every minimum of coverage functions that obeys them counting by
two criteria? No.

**A third law (`count2_cycle5`, `IsCount2.cycle5`).** Take five
individuals, each counted at least once, in a cycle in which every two
neighbours count at most one together. Then some two non-neighbours also
count at most one together.

Why: things that pairwise share a volume or a text all share one volume
or one text, a *hub* (`hub_of_pairwise`). Each individual's things carry
the hub of the pair on its left and of the pair on its right, so two
consecutive hubs are equal, or one is a volume and the other a text.
Around a cycle of odd length they cannot always alternate, so two
consecutive hubs are equal, and the two individuals around them share
it.

**The example (`f5`).** Five individuals in a cycle; count the largest
set of them no two of which are neighbours. It is the minimum of five
coverage functions (`f5_isMinCov`), it is subadditive (`f5_subadd`) and
obeys the pairwise law (`f5_pairwise`), but it breaks the odd-cycle law,
so it is not counting by two criteria (`two_laws_not_sufficient`).

The same argument gives the law for any odd cycle of length at least 5;
only 5 is proved. That points to perfect graphs (line graphs of
bipartite graphs are perfect, and odd cycles of length at least 5 are
not); whether the counting functions of two criteria are characterized
that way is not checked.
-/

namespace FraCaS.Encodings.OddCycle
open FraCaS.Encodings.Counting
open FraCaS.Encodings.FullAbstraction (meetsSum)
open FraCaS.Encodings.TwoCriteria
open FraCaS.Encodings.MinCoverage
open Classical

/-! ## Facts about the five-cycle, by computation -/

theorem fin5_add41 : ∀ i : Fin 5, i + 4 + 1 = i := by decide
theorem fin5_add42 : ∀ i : Fin 5, i + 4 + 2 = i + 1 := by decide

theorem no_alternation : ∀ b0 b1 b2 b3 b4 : Bool,
    b4 ≠ b0 → b0 ≠ b1 → b1 ≠ b2 → b2 ≠ b3 → b3 ≠ b4 → False := by decide

/-! ## Hubs -/

section
variable {T K1 K2 : Type} [Fintype T] (c1 : T → K1) (c2 : T → K2)

/-- A thing lies on a hub: a volume (`inl`) or a text (`inr`). -/
def onHub (h : K1 ⊕ K2) (y : T) : Prop :=
  match h with
  | .inl v => c1 y = v
  | .inr t => c2 y = t

/-- **Things that pairwise share a volume or a text share a hub.** -/
theorem hub_of_pairwise (Q : T → Prop) (hne : ∃ y, Q y)
    (hpw : ∀ y y', Q y → Q y' → c1 y = c1 y' ∨ c2 y = c2 y') :
    ∃ h : K1 ⊕ K2, ∀ y, Q y → onHub c1 c2 h y := by
  obtain ⟨y0, hy0⟩ := hne
  by_cases hall : ∀ y, Q y → c1 y = c1 y0
  · exact ⟨.inl (c1 y0), hall⟩
  · push_neg at hall
    obtain ⟨y1, hy1, hc1⟩ := hall
    have ht : c2 y1 = c2 y0 := (hpw y1 y0 hy1 hy0).resolve_left hc1
    refine ⟨.inr (c2 y0), fun y hy => ?_⟩
    show c2 y = c2 y0
    by_contra hc
    have a := (hpw y y0 hy hy0).resolve_right hc
    have b := (hpw y y1 hy hy1).resolve_right (fun e => hc (e.trans ht))
    exact hc1 (b.symm.trans a)

theorem le_one_iff_pairwise (Q : T → Prop) :
    count2 c1 c2 Q ≤ 1 ↔ ∀ y y', Q y → Q y' → c1 y = c1 y' ∨ c2 y = c2 y' := by
  constructor
  · intro h y y' hy hy'
    by_contra hc
    push_neg at hc
    have := (two_le_count2_iff c1 c2 Q).mpr ⟨y, y', hy, hy', hc.1, hc.2⟩
    omega
  · intro h
    by_contra hlt
    obtain ⟨y, y', hy, hy', h1, h2⟩ := (two_le_count2_iff c1 c2 Q).mp (by omega)
    rcases h y y' hy hy' with e | e
    · exact h1 e
    · exact h2 e

theorem one_le_count2_iff (Q : T → Prop) : 1 ≤ count2 c1 c2 Q ↔ ∃ y, Q y := by
  constructor
  · intro h
    obtain ⟨S, h1, hQ, -, -⟩ := (le_count2_iff c1 c2 Q 1).mp h
    obtain ⟨y, hy⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨y, hQ y hy⟩
  · rintro ⟨y, hy⟩
    refine (le_count2_iff c1 c2 Q 1).mpr ⟨{y}, (Finset.card_singleton y).symm.le, fun z hz => ?_,
      by simp, by simp⟩
    rw [Finset.mem_singleton.mp hz]
    exact hy

/-- **The odd-cycle law.** -/
theorem count2_cycle5 (E : Fin 5 → T → Prop) (hne : ∀ i, 1 ≤ count2 c1 c2 (E i))
    (hadj : ∀ i, count2 c1 c2 (fun y => E i y ∨ E (i + 1) y) ≤ 1) :
    ∃ i, count2 c1 c2 (fun y => E i y ∨ E (i + 2) y) ≤ 1 := by
  -- a hub for each pair of neighbours, and a thing of each individual
  have hhub : ∀ i, ∃ h : K1 ⊕ K2, ∀ y, (E i y ∨ E (i + 1) y) → onHub c1 c2 h y := fun i =>
    hub_of_pairwise c1 c2 (fun y => E i y ∨ E (i + 1) y)
      (let ⟨y, hy⟩ := (one_le_count2_iff c1 c2 (E i)).mp (hne i); ⟨y, Or.inl hy⟩)
      ((le_one_iff_pairwise c1 c2 _).mp (hadj i))
  choose h hh using hhub
  have hz : ∀ i, ∃ y, E i y := fun i => (one_le_count2_iff c1 c2 (E i)).mp (hne i)
  choose z hzE using hz
  -- each individual's thing lies on the hubs on its two sides
  have hleft : ∀ i, onHub c1 c2 (h (i + 4)) (z i) := fun i => by
    apply hh (i + 4) (z i)
    right
    rw [fin5_add41]
    exact hzE i
  have hright : ∀ i, onHub c1 c2 (h i) (z i) := fun i => hh i (z i) (Or.inl (hzE i))
  -- so two consecutive hubs are equal, or of different kinds
  have hstep : ∀ i, h (i + 4) = h i ∨ (h (i + 4)).isLeft ≠ (h i).isLeft := fun i => by
    have l := hleft i
    have r := hright i
    cases e1 : h (i + 4) with
    | inl v =>
      cases e2 : h i with
      | inl v' =>
        rw [e1] at l
        rw [e2] at r
        exact Or.inl (congrArg Sum.inl
          ((show c1 (z i) = v from l).symm.trans (show c1 (z i) = v' from r)))
      | inr t' => exact Or.inr (by simp)
    | inr t =>
      cases e2 : h i with
      | inl v' => exact Or.inr (by simp)
      | inr t' =>
        rw [e1] at l
        rw [e2] at r
        exact Or.inl (congrArg Sum.inr
          ((show c2 (z i) = t from l).symm.trans (show c2 (z i) = t' from r)))
  by_cases heq : ∃ i, h (i + 4) = h i
  · obtain ⟨i, hi⟩ := heq
    refine ⟨i + 4, (le_one_iff_pairwise c1 c2 _).mpr fun y y' hy hy' => ?_⟩
    rw [fin5_add42] at hy hy'
    have hy2 : onHub c1 c2 (h i) y := by
      rcases hy with hy | hy
      · rw [← hi]
        exact hh (i + 4) y (Or.inl hy)
      · exact hh i y (Or.inr hy)
    have hy2' : onHub c1 c2 (h i) y' := by
      rcases hy' with hy' | hy'
      · rw [← hi]
        exact hh (i + 4) y' (Or.inl hy')
      · exact hh i y' (Or.inr hy')
    cases e : h i with
    | inl v =>
      rw [e] at hy2 hy2'
      exact Or.inl ((show c1 y = v from hy2).trans (show c1 y' = v from hy2').symm)
    | inr t =>
      rw [e] at hy2 hy2'
      exact Or.inr ((show c2 y = t from hy2).trans (show c2 y' = t from hy2').symm)
  · push_neg at heq
    have alt : ∀ i, (h (i + 4)).isLeft ≠ (h i).isLeft := fun i => (hstep i).resolve_left (heq i)
    have a0 := alt 0
    have a1 := alt 1
    have a2 := alt 2
    have a3 := alt 3
    have a4 := alt 4
    rw [show (0 : Fin 5) + 4 = 4 by decide] at a0
    rw [show (1 : Fin 5) + 4 = 0 by decide] at a1
    rw [show (2 : Fin 5) + 4 = 1 by decide] at a2
    rw [show (3 : Fin 5) + 4 = 2 by decide] at a3
    rw [show (4 : Fin 5) + 4 = 3 by decide] at a4
    exact (no_alternation (h 0).isLeft (h 1).isLeft (h 2).isLeft (h 3).isLeft (h 4).isLeft
      a0 a1 a2 a3 a4).elim

end

theorem IsCount2.cycle5 {A : Type} {f : (A → Prop) → Nat} (hf : IsCount2 f) (x : Fin 5 → A)
    (hne : ∀ i, 1 ≤ f (fun a => a = x i))
    (hadj : ∀ i, f (fun a => a = x i ∨ a = x (i + 1)) ≤ 1) :
    ∃ i, f (fun a => a = x i ∨ a = x (i + 2)) ≤ 1 := by
  obtain ⟨T, inst, emb, K1, K2, c1, c2, h⟩ := hf
  obtain ⟨i, hi⟩ := count2_cycle5 c1 c2 (fun i y => emb y = x i)
    (fun i => (hne i).trans_eq (h (fun a => a = x i)).symm)
    (fun i => (h (fun a => a = x i ∨ a = x (i + 1))).trans_le (hadj i))
  exact ⟨i, (h (fun a => a = x i ∨ a = x (i + 2))).symm.trans_le hi⟩

/-! ## The five-cycle as a minimum of coverage functions -/

/-- Rotation `r`: one unit covering `r, r+1, r+4`, one covering
`r+2, r+3, r+4`. -/
def U1 (r : Fin 5) : Finset (Fin 5) := {r, r + 1, r + 4}
def U2 (r : Fin 5) : Finset (Fin 5) := {r + 2, r + 3, r + 4}

noncomputable def g5 (r : Fin 5) : Finset (Fin 5) → Nat := fun S => oneUnit (U1 r) S + oneUnit (U2 r) S

/-- The largest set of the `P`s no two of which are neighbours in the
five-cycle, as the least of the five rotations. -/
noncomputable def f5 (P : Fin 5 → Prop) : Nat :=
  Finset.univ.inf' Finset.univ_nonempty (fun r => meetsSum (g5 r) P)

theorem f5_isMinCov : IsMinCov f5 := by
  refine ⟨Fin 5, g5, fun r P => Finset.inf'_le _ (Finset.mem_univ r), fun P => ?_⟩
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun r => meetsSum (g5 r) P)
  exact ⟨r, hr⟩

theorem meetsSum_g5 (r : Fin 5) (P : Fin 5 → Prop) :
    meetsSum (g5 r) P = meetsSum (oneUnit (U1 r)) P + meetsSum (oneUnit (U2 r)) P :=
  meetsSum_add _ _ P

theorem meetsSum_oneUnit_le {A : Type} [Fintype A] (S0 : Finset A) (P : A → Prop) :
    meetsSum (oneUnit S0) P ≤ 1 := by
  rw [meetsSum_oneUnit]
  split_ifs <;> simp

theorem covers : ∀ r i : Fin 5, i ∈ U1 r ∨ i ∈ U2 r := by decide

theorem nonadj_meets : ∀ r i j : Fin 5, i ≠ j → j ≠ i + 1 → i ≠ j + 1 →
    (i ∈ U1 r ∨ j ∈ U1 r) ∧ (i ∈ U2 r ∨ j ∈ U2 r) := by decide

theorem adj_avoids : ∀ k : Fin 5, k ∉ U2 k ∧ k + 1 ∉ U2 k := by decide

theorem nbr_left : ∀ i j : Fin 5, i = j + 1 → j = i + 4 := by decide

theorem not_both_sides : ∀ i : Fin 5,
    ¬ (i + 4 = i + 1 ∨ i + 1 = i + 4 + 1 ∨ i + 4 = i + 1 + 1) := by decide

theorem plus4_plus1 : ∀ i : Fin 5, i + 4 + 1 = i := fin5_add41

theorem f5_le_two (P : Fin 5 → Prop) : f5 P ≤ 2 := by
  refine (Finset.inf'_le _ (Finset.mem_univ 0)).trans ?_
  show meetsSum (g5 0) P ≤ 2
  rw [meetsSum_g5]
  have := meetsSum_oneUnit_le (U1 0) P
  have := meetsSum_oneUnit_le (U2 0) P
  omega

theorem one_le_f5 (P : Fin 5 → Prop) (i : Fin 5) (hi : P i) : 1 ≤ f5 P := by
  refine Finset.le_inf' _ _ fun r _ => ?_
  show 1 ≤ meetsSum (g5 r) P
  rw [meetsSum_g5]
  rcases covers r i with h | h
  · rw [meetsSum_oneUnit_pos (U1 r) P ⟨i, h, hi⟩]
    omega
  · rw [meetsSum_oneUnit_pos (U2 r) _ ⟨i, h, hi⟩]
    omega

/-- Two non-neighbours count two. -/
theorem two_le_f5 (P : Fin 5 → Prop) (i j : Fin 5) (hi : P i) (hj : P j) (hij : i ≠ j)
    (h1 : j ≠ i + 1) (h2 : i ≠ j + 1) : 2 ≤ f5 P := by
  refine Finset.le_inf' _ _ fun r _ => ?_
  show 2 ≤ meetsSum (g5 r) P
  rw [meetsSum_g5]
  obtain ⟨a, b⟩ := nonadj_meets r i j hij h1 h2
  have ea : meetsSum (oneUnit (U1 r)) P = 1 := by
    rcases a with a | a
    · exact meetsSum_oneUnit_pos _ _ ⟨i, a, hi⟩
    · exact meetsSum_oneUnit_pos _ _ ⟨j, a, hj⟩
  have eb : meetsSum (oneUnit (U2 r)) P = 1 := by
    rcases b with b | b
    · exact meetsSum_oneUnit_pos _ _ ⟨i, b, hi⟩
    · exact meetsSum_oneUnit_pos _ _ ⟨j, b, hj⟩
  omega

/-- Counting at most one is lying within two neighbours. -/
theorem f5_le_one_iff (S : Fin 5 → Prop) :
    f5 S ≤ 1 ↔ ∀ i j, S i → S j → i = j ∨ j = i + 1 ∨ i = j + 1 := by
  constructor
  · intro h i j hi hj
    by_contra hc
    push_neg at hc
    have := two_le_f5 S i j hi hj hc.1 hc.2.1 hc.2.2
    omega
  · intro hC
    -- the `S`s lie within `k, k+1` for some `k`
    have hk : ∃ k : Fin 5, ∀ j, S j → j = k ∨ j = k + 1 := by
      by_cases hne : ∃ i, S i
      · obtain ⟨i, hi⟩ := hne
        by_cases hn : S (i + 1)
        · refine ⟨i, fun j hj => ?_⟩
          rcases hC i j hi hj with e | e | e
          · exact Or.inl e.symm
          · exact Or.inr e
          · exfalso
            have hj4 := nbr_left i j e
            rw [hj4] at hj
            rcases hC (i + 4) (i + 1) hj hn with e' | e' | e'
            · exact not_both_sides i (Or.inl e')
            · exact not_both_sides i (Or.inr (Or.inl e'))
            · exact not_both_sides i (Or.inr (Or.inr e'))
        · refine ⟨i + 4, fun j hj => ?_⟩
          rcases hC i j hi hj with e | e | e
          · right
            rw [plus4_plus1]
            exact e.symm
          · exact (hn (e ▸ hj)).elim
          · exact Or.inl (nbr_left i j e)
      · push_neg at hne
        exact ⟨0, fun j hj => absurd hj (hne j)⟩
    obtain ⟨k, hk⟩ := hk
    refine (Finset.inf'_le _ (Finset.mem_univ k)).trans ?_
    show meetsSum (g5 k) S ≤ 1
    rw [meetsSum_g5, meetsSum_oneUnit_neg (U2 k) S ?_]
    · have := meetsSum_oneUnit_le (U1 k) S
      omega
    · rintro ⟨j, hj, hSj⟩
      rcases hk j hSj with e | e
      · rw [e] at hj
        exact (adj_avoids k).1 hj
      · rw [e] at hj
        exact (adj_avoids k).2 hj

/-! ## It obeys both laws -/

theorem f5_congr {P P' : Fin 5 → Prop} (h : ∀ x, P x ↔ P' x) : f5 P = f5 P' := by
  have e : P = P' := funext fun x => propext (h x)
  rw [e]

theorem f5_subadd (P Q : Fin 5 → Prop) : f5 (fun x => P x ∨ Q x) ≤ f5 P + f5 Q := by
  by_cases hP : ∃ i, P i
  · by_cases hQ : ∃ i, Q i
    · obtain ⟨i, hi⟩ := hP
      obtain ⟨j, hj⟩ := hQ
      have := one_le_f5 P i hi
      have := one_le_f5 Q j hj
      have := f5_le_two (fun x => P x ∨ Q x)
      omega
    · push_neg at hQ
      rw [f5_congr (P := fun x => P x ∨ Q x) (P' := P)
        fun x => ⟨fun h => h.resolve_right (hQ x), Or.inl⟩]
      omega
  · push_neg at hP
    rw [f5_congr (P := fun x => P x ∨ Q x) (P' := Q)
      fun x => ⟨fun h => h.resolve_left (hP x), Or.inr⟩]
    omega

theorem f5_pairwise (P Q R : Fin 5 → Prop) (hpq : f5 (fun x => P x ∨ Q x) ≤ 1)
    (hqr : f5 (fun x => Q x ∨ R x) ≤ 1) (hpr : f5 (fun x => P x ∨ R x) ≤ 1) :
    f5 (fun x => P x ∨ Q x ∨ R x) ≤ 1 := by
  rw [f5_le_one_iff] at hpq hqr hpr ⊢
  intro i j hi hj
  rcases hi with h | h | h <;> rcases hj with h' | h' | h'
  · exact hpq i j (Or.inl h) (Or.inl h')
  · exact hpq i j (Or.inl h) (Or.inr h')
  · exact hpr i j (Or.inl h) (Or.inr h')
  · exact hpq i j (Or.inr h) (Or.inl h')
  · exact hpq i j (Or.inr h) (Or.inr h')
  · exact hqr i j (Or.inl h) (Or.inr h')
  · exact hpr i j (Or.inr h) (Or.inl h')
  · exact hqr i j (Or.inr h) (Or.inl h')
  · exact hqr i j (Or.inr h) (Or.inr h')

/-- **The two laws are not sufficient.** `f5` is a minimum of coverage
functions, subadditive, and obeys the pairwise law, but it is not
counting by two criteria. -/
theorem two_laws_not_sufficient :
    IsMinCov f5 ∧ (∀ P Q, f5 (fun x => P x ∨ Q x) ≤ f5 P + f5 Q) ∧
      (∀ P Q R, f5 (fun x => P x ∨ Q x) ≤ 1 → f5 (fun x => Q x ∨ R x) ≤ 1 →
        f5 (fun x => P x ∨ R x) ≤ 1 → f5 (fun x => P x ∨ Q x ∨ R x) ≤ 1) ∧
      ¬ IsCount2 f5 := by
  refine ⟨f5_isMinCov, f5_subadd, f5_pairwise, fun hf => ?_⟩
  have nd : ∀ i : Fin 5, i ≠ i + 2 ∧ i + 2 ≠ i + 1 ∧ i ≠ i + 2 + 1 := by decide
  obtain ⟨i, hi⟩ := hf.cycle5 id (fun i => one_le_f5 _ i rfl)
    (fun i => (f5_le_one_iff _).mpr fun a b ha hb => by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl rfl)
  have := two_le_f5 (fun a => a = id i ∨ a = id (i + 2)) i (i + 2) (Or.inl rfl) (Or.inr rfl)
    (nd i).1 (nd i).2.1 (nd i).2.2
  omega

end FraCaS.Encodings.OddCycle

/-- info: 'FraCaS.Encodings.OddCycle.two_laws_not_sufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.OddCycle.two_laws_not_sufficient

/-- info: 'FraCaS.Encodings.OddCycle.count2_cycle5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.OddCycle.count2_cycle5
