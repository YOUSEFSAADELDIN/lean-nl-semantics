import EndToEnd.Encodings.OddCycle

/-!
# The claw law and the odd-cycle laws of every length

`OddCycle.lean` proves one law of counting by two criteria for cycles of
five individuals. This file proves it for odd cycles of every length,
and adds a law about claws. Both come from the same fact: things that
pairwise share a volume or a text share one *hub*, a volume or a text
(`OddCycle.hub_of_pairwise`).

**The claw law (`count2_claw`, `IsCount2.claw`).** Let `X` have
something counted. If `X` counts at most one together with each of
`Y`, `Z` and `W`, then two of `Y`, `Z`, `W` count at most one together.
The three hubs, of `X ∪ Y`, `X ∪ Z` and `X ∪ W`, all pass through one
thing of `X`. A thing has one volume and one text, so two hubs of the
same kind are equal, and of three hubs two have the same kind
(`hub_step`).

**The odd-cycle laws (`count2_oddCycle`, `IsCount2.oddCycle`).** Take
`2m + 1` individuals in a cycle (indexed by `ZMod (2m + 1)`), each
counted at least once, every two neighbours counting at most one
together. Then for some `i`, the individuals `i` and `i + 2` count at
most one together. Each individual's things lie on the hubs of both its
pairs, so two consecutive hubs are equal or of different kinds. Around a
cycle of odd length the kinds cannot alternate all the way round, so two
consecutive hubs are equal, and the individuals on either side of them
share it. For `m = 2` this is `OddCycle.count2_cycle5`. For `m = 1` the
conclusion is about neighbours and is immediate. Even cycles have no
such law: in an even cycle of books whose neighbours share, in turn, a
volume and a text, every two books two apart count as two.

In graph terms, with one thing per individual, counting by two criteria
is the independence number of the line graph of a bipartite multigraph.
These laws say that graph has no induced claw and no odd hole
(`paper/A2-draft.md`, §9).
-/

namespace FraCaS.Encodings.ForbiddenLaws
open FraCaS.Encodings.TwoCriteria
open FraCaS.Encodings.MinCoverage
open FraCaS.Encodings.OddCycle
open Classical

section
variable {T K1 K2 : Type} [Fintype T] (c1 : T → K1) (c2 : T → K2)

/-- Things that all lie on one hub count at most one. -/
theorem le_one_of_onHub (h : K1 ⊕ K2) (Q : T → Prop) (hQ : ∀ y, Q y → onHub c1 c2 h y) :
    count2 c1 c2 Q ≤ 1 := by
  refine (le_one_iff_pairwise c1 c2 Q).mpr fun y y' hy hy' => ?_
  have a := hQ y hy
  have b := hQ y' hy'
  cases h with
  | inl v => exact Or.inl ((show c1 y = v from a).trans (show c1 y' = v from b).symm)
  | inr t => exact Or.inr ((show c2 y = t from a).trans (show c2 y' = t from b).symm)

/-- **Two hubs through one thing are equal, or of different kinds.** -/
theorem hub_step {h h' : K1 ⊕ K2} {y : T} (a : onHub c1 c2 h y) (b : onHub c1 c2 h' y) :
    h = h' ∨ h'.isLeft = !h.isLeft := by
  cases h with
  | inl v =>
    cases h' with
    | inl v' =>
      exact Or.inl (congrArg Sum.inl ((show c1 y = v from a).symm.trans (show c1 y = v' from b)))
    | inr t' => exact Or.inr rfl
  | inr t =>
    cases h' with
    | inl v' => exact Or.inr rfl
    | inr t' =>
      exact Or.inl (congrArg Sum.inr ((show c2 y = t from a).symm.trans (show c2 y = t' from b)))

/-- A pair counting at most one, with something counted, has a hub. -/
theorem pair_hub (P Q : T → Prop) (hne : ∃ y, P y)
    (h : count2 c1 c2 (fun y => P y ∨ Q y) ≤ 1) :
    ∃ hb : K1 ⊕ K2, ∀ y, (P y ∨ Q y) → onHub c1 c2 hb y :=
  hub_of_pairwise c1 c2 _ (let ⟨y, hy⟩ := hne; ⟨y, Or.inl hy⟩)
    ((le_one_iff_pairwise c1 c2 _).mp h)

/-- Two sets whose things lie on one hub count at most one together. -/
theorem le_one_of_two_hubs {a b : K1 ⊕ K2} (hab : a = b) (Y Z : T → Prop)
    (hY : ∀ y, Y y → onHub c1 c2 a y) (hZ : ∀ y, Z y → onHub c1 c2 b y) :
    count2 c1 c2 (fun y => Y y ∨ Z y) ≤ 1 := by
  subst hab
  refine le_one_of_onHub c1 c2 a _ fun y hy => ?_
  rcases hy with h | h
  · exact hY y h
  · exact hZ y h

/-- **The claw law.** -/
theorem count2_claw (X Y Z W : T → Prop) (hX : 1 ≤ count2 c1 c2 X)
    (hY : count2 c1 c2 (fun y => X y ∨ Y y) ≤ 1)
    (hZ : count2 c1 c2 (fun y => X y ∨ Z y) ≤ 1)
    (hW : count2 c1 c2 (fun y => X y ∨ W y) ≤ 1) :
    count2 c1 c2 (fun y => Y y ∨ Z y) ≤ 1 ∨ count2 c1 c2 (fun y => Y y ∨ W y) ≤ 1 ∨
      count2 c1 c2 (fun y => Z y ∨ W y) ≤ 1 := by
  obtain ⟨x, hx⟩ := (one_le_count2_iff c1 c2 X).mp hX
  obtain ⟨a, ha⟩ := pair_hub c1 c2 X Y ⟨x, hx⟩ hY
  obtain ⟨b, hb⟩ := pair_hub c1 c2 X Z ⟨x, hx⟩ hZ
  obtain ⟨d, hd⟩ := pair_hub c1 c2 X W ⟨x, hx⟩ hW
  have hYa : ∀ y, Y y → onHub c1 c2 a y := fun y h => ha y (Or.inr h)
  have hZb : ∀ y, Z y → onHub c1 c2 b y := fun y h => hb y (Or.inr h)
  have hWd : ∀ y, W y → onHub c1 c2 d y := fun y h => hd y (Or.inr h)
  -- the three hubs pass through `x`
  rcases hub_step c1 c2 (ha x (Or.inl hx)) (hb x (Or.inl hx)) with e1 | e1
  · exact Or.inl (le_one_of_two_hubs c1 c2 e1 Y Z hYa hZb)
  rcases hub_step c1 c2 (ha x (Or.inl hx)) (hd x (Or.inl hx)) with e2 | e2
  · exact Or.inr (Or.inl (le_one_of_two_hubs c1 c2 e2 Y W hYa hWd))
  rcases hub_step c1 c2 (hb x (Or.inl hx)) (hd x (Or.inl hx)) with e3 | e3
  · exact Or.inr (Or.inr (le_one_of_two_hubs c1 c2 e3 Z W hZb hWd))
  -- otherwise `b` and `d` both differ in kind from `a`, and from each other
  exfalso
  rw [e2, e1] at e3
  generalize a.isLeft = p at e3
  cases p <;> simp at e3

/-- **The odd-cycle law, for a cycle of length `2m + 1`.** -/
theorem count2_oddCycle (m : ℕ) (E : ZMod (2 * m + 1) → T → Prop)
    (hne : ∀ i, 1 ≤ count2 c1 c2 (E i))
    (hadj : ∀ i, count2 c1 c2 (fun y => E i y ∨ E (i + 1) y) ≤ 1) :
    ∃ i, count2 c1 c2 (fun y => E i y ∨ E (i + 2) y) ≤ 1 := by
  -- a hub for each pair of neighbours, and a thing of each individual
  have hhub : ∀ i, ∃ hb : K1 ⊕ K2, ∀ y, (E i y ∨ E (i + 1) y) → onHub c1 c2 hb y := fun i =>
    pair_hub c1 c2 (E i) (E (i + 1)) ((one_le_count2_iff c1 c2 (E i)).mp (hne i)) (hadj i)
  choose h hh using hhub
  have hz : ∀ i, ∃ y, E i y := fun i => (one_le_count2_iff c1 c2 (E i)).mp (hne i)
  choose z hzE using hz
  -- the thing of individual `i + 1` lies on the hubs `h i` and `h (i + 1)`
  have hstep : ∀ i, h i = h (i + 1) ∨ (h (i + 1)).isLeft = !(h i).isLeft := fun i =>
    hub_step c1 c2 (hh i (z (i + 1)) (Or.inr (hzE (i + 1))))
      (hh (i + 1) (z (i + 1)) (Or.inl (hzE (i + 1))))
  by_cases heq : ∃ i, h i = h (i + 1)
  · obtain ⟨i, hi⟩ := heq
    refine ⟨i, le_one_of_onHub c1 c2 (h i) _ fun y hy => ?_⟩
    rcases hy with hy | hy
    · exact hh i y (Or.inl hy)
    · rw [hi]
      exact hh (i + 1) y (Or.inr (by rwa [add_assoc, one_add_one_eq_two]))
  · -- otherwise the kinds alternate all the way round, which an odd cycle forbids
    have alt : ∀ i, (h (i + 1)).isLeft = !(h i).isLeft := fun i =>
      (hstep i).resolve_left fun e => heq ⟨i, e⟩
    have hb1 : ∀ k : ℕ, (h ((k + 1 : ℕ) : ZMod (2 * m + 1))).isLeft =
        !(h ((k : ℕ) : ZMod (2 * m + 1))).isLeft := fun k => by
      rw [Nat.cast_succ]
      exact alt _
    have hb2 : ∀ k : ℕ, (h ((2 * k : ℕ) : ZMod (2 * m + 1))).isLeft =
        (h ((0 : ℕ) : ZMod (2 * m + 1))).isLeft := fun k => by
      induction k with
      | zero => rw [Nat.mul_zero]
      | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, hb1, hb1, ih, Bool.not_not]
    have hn : (h ((2 * m + 1 : ℕ) : ZMod (2 * m + 1))).isLeft =
        (h ((0 : ℕ) : ZMod (2 * m + 1))).isLeft := by
      rw [ZMod.natCast_self, Nat.cast_zero]
    rw [hb1, hb2] at hn
    generalize (h ((0 : ℕ) : ZMod (2 * m + 1))).isLeft = p at hn
    cases p <;> simp at hn

end

/-! ## The laws for counting functions -/

/-- **The claw law**, for any counting function of a noun with two
criteria. -/
theorem IsCount2.claw {A : Type} {f : (A → Prop) → Nat} (hf : IsCount2 f) (X Y Z W : A → Prop)
    (hX : 1 ≤ f X) (hY : f (fun a => X a ∨ Y a) ≤ 1) (hZ : f (fun a => X a ∨ Z a) ≤ 1)
    (hW : f (fun a => X a ∨ W a) ≤ 1) :
    f (fun a => Y a ∨ Z a) ≤ 1 ∨ f (fun a => Y a ∨ W a) ≤ 1 ∨ f (fun a => Z a ∨ W a) ≤ 1 := by
  obtain ⟨T, inst, emb, K1, K2, c1, c2, h⟩ := hf
  rcases count2_claw c1 c2 (fun y => X (emb y)) (fun y => Y (emb y)) (fun y => Z (emb y))
      (fun y => W (emb y)) (hX.trans_eq (h X).symm)
      ((h (fun a => X a ∨ Y a)).trans_le hY) ((h (fun a => X a ∨ Z a)).trans_le hZ)
      ((h (fun a => X a ∨ W a)).trans_le hW) with r | r | r
  · exact Or.inl ((h (fun a => Y a ∨ Z a)).symm.trans_le r)
  · exact Or.inr (Or.inl ((h (fun a => Y a ∨ W a)).symm.trans_le r))
  · exact Or.inr (Or.inr ((h (fun a => Z a ∨ W a)).symm.trans_le r))

/-- **The odd-cycle law of length `2m + 1`**, for any counting function of
a noun with two criteria. -/
theorem IsCount2.oddCycle {A : Type} {f : (A → Prop) → Nat} (hf : IsCount2 f) (m : ℕ)
    (x : ZMod (2 * m + 1) → A) (hne : ∀ i, 1 ≤ f (fun a => a = x i))
    (hadj : ∀ i, f (fun a => a = x i ∨ a = x (i + 1)) ≤ 1) :
    ∃ i, f (fun a => a = x i ∨ a = x (i + 2)) ≤ 1 := by
  obtain ⟨T, inst, emb, K1, K2, c1, c2, h⟩ := hf
  obtain ⟨i, hi⟩ := count2_oddCycle c1 c2 m (fun i y => emb y = x i)
    (fun i => (hne i).trans_eq (h (fun a => a = x i)).symm)
    (fun i => (h (fun a => a = x i ∨ a = x (i + 1))).trans_le (hadj i))
  exact ⟨i, (h (fun a => a = x i ∨ a = x (i + 2))).symm.trans_le hi⟩

end FraCaS.Encodings.ForbiddenLaws

/-- info: 'FraCaS.Encodings.ForbiddenLaws.IsCount2.claw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.ForbiddenLaws.IsCount2.claw

/-- info: 'FraCaS.Encodings.ForbiddenLaws.IsCount2.oddCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.ForbiddenLaws.IsCount2.oddCycle
