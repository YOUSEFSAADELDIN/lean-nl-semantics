import EndToEnd.Encodings.Counting

/-!
# Phase 4, continued: four checks from the literature

`paper/A-literature.md` records what the papers on individuation and
copredication say. This file checks four points from them in Lean, with
the counting of `Counting.lean` (`countBy f P`: the `P`s counted by "same
`f`-value").

1. **Gotham's (2017) arguments (100) and (103)**, in his own form
   ("every book", not "every book he picked up").
   - (100) "John picked up `n` books. John mastered every book. ⇒ John
     mastered `n` books" is invalid with dot types (`M_G100_not_valid`)
     and valid with one-domain predicates (`P_G100_valid`).
   - (103) "...defaced every book ⇒ John defaced `n` books" is valid in
     both (`M_G103_valid`, `P_G103_valid`): both verbs count physical
     objects.
2. **Luo's (2012) passengers.** "EasyJet transported `n` passengers" does
   not entail "EasyJet transported `n` persons": one person on `n`
   journeys is `n` passengers. With nouns as types, a passenger type
   embedded in the persons, it is not valid (`M_EJ_not_valid`), and its
   converse is (`M_EJ_converse`). With one-domain predicates it is
   valid (`P_EJ_valid`).
3. **Double distinctness.** "John picked up and mastered `n` books" needs
   `n` books distinct physically *and* informationally (Gotham's (85);
   Chatzikyriakidis & Luo 2018, (36)). `AtLeastBoth` states that.
   - It entails "picked up `n` books" and "mastered `n` books"
     (`M_copred_left`, `M_copred_right`; Gotham's (122)-(123)).
   - It is exactly Chatzikyriakidis & Luo's `Three` over their
     dot-setoid, pairwise distinct with "same" meaning "same volume or
     same text" (`atLeastDot_iff`).
4. **That dot-setoid's relation is not transitive.** Chatzikyriakidis &
   Luo (2018, p. 135) say the relation "does result in an equivalence
   relation". With two copies of one text and an anthology it is not
   transitive (`dotSame_not_transitive`). It is transitive once each
   volume has one text (`dotSame_trans_of`), the view their n. 4 says
   they incline to. Their counting uses only pairwise distinctness
   (point 3), so their predictions do not depend on transitivity.
   `DotSetoid.lean` shows that no other equivalence relation would do
   either.
-/

namespace FraCaS.Encodings.Criteria
open FraCaS.Section1 FraCaS.Encodings.Counting
open FraCaS.Encodings.Equivalence (card_filter_mono)
open FraCaS.Encodings.Copredication (OneTextPerVolume)

/-! ## 1. Gotham's (100) and (103) -/

def P_G100 (n : Nat) : Prop :=
  ∀ {A : Type} [Fintype A] (book pickedUp mastered : A → Prop)
    [DecidablePred fun x => book x ∧ pickedUp x] [DecidablePred fun x => book x ∧ mastered x],
    AtLeast n book pickedUp → (∀ x, book x → mastered x) → AtLeast n book mastered

def P_G103 (n : Nat) : Prop :=
  ∀ {A : Type} [Fintype A] (book pickedUp defaced : A → Prop)
    [DecidablePred fun x => book x ∧ pickedUp x] [DecidablePred fun x => book x ∧ defaced x],
    AtLeast n book pickedUp → (∀ x, book x → defaced x) → AtLeast n book defaced

theorem P_G100_valid (n : Nat) : P_G100 n := by
  unfold P_G100
  intro A _ book pickedUp mastered _ _ h1 h2
  exact le_trans h1 (card_filter_mono (by intro x hx; exact ⟨hx.1, h2 x hx.1⟩))

theorem P_G103_valid (n : Nat) : P_G103 n := by
  unfold P_G103
  intro A _ book pickedUp defaced _ _ h1 h2
  exact le_trans h1 (card_filter_mono (by intro x hx; exact ⟨hx.1, h2 x hx.1⟩))

def M_G100 (n : Nat) : Prop :=
  ∀ (Phy Info Book : Type) [Fintype Book] [DecidableEq Phy] [DecidableEq Info]
    (bk : Book → MTT.DotType Phy Info) (pickedUp : Phy → Prop) (mastered : Info → Prop)
    [DecidablePred fun b => pickedUp (bk b).phy] [DecidablePred fun b => mastered (bk b).info],
    countBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy) ≥ n →
    (∀ b, mastered (bk b).info) →
    countBy (fun b => (bk b).info) (fun b => mastered (bk b).info) ≥ n

/-- `n` copies of one text, for any `n ≥ 2`. -/
theorem M_G100_not_valid (n : Nat) (hn : 2 ≤ n) : ¬ M_G100 n := by
  intro h
  unfold M_G100 at h
  have h1 : countBy (fun b : Fin n => b) (fun _ => True) ≥ n := by
    rw [countBy_of_injective (fun b : Fin n => b) (fun _ _ hab => hab)]
    simp [card]
  have h2 := h (Fin n) Unit (Fin n) (fun b => ⟨b, ()⟩) (fun _ => True) (fun _ => True)
    h1 (fun _ => trivial)
  have h3 : countBy (fun _ : Fin n => ()) (fun _ => True) ≤ 1 := by
    unfold countBy
    exact (Finset.card_le_univ _).trans (by simp)
  exact absurd (le_trans h2 h3) (by omega)

/-- Both verbs count physical objects, so (103) is valid with dot types. -/
theorem M_G103_valid (n : Nat) {Phy Info Book : Type} [Fintype Book] [DecidableEq Phy]
    (bk : Book → MTT.DotType Phy Info) (pickedUp defaced : Phy → Prop)
    [DecidablePred fun b => pickedUp (bk b).phy] [DecidablePred fun b => defaced (bk b).phy] :
    countBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy) ≥ n →
    (∀ b, defaced (bk b).phy) →
    countBy (fun b => (bk b).phy) (fun b => defaced (bk b).phy) ≥ n := by
  intro h1 h2
  exact le_trans h1 (countBy_mono (P := fun b => pickedUp (bk b).phy)
    (Q := fun b => defaced (bk b).phy) _ fun b _ => h2 b)

/-! ## 2. Luo's passengers -/

/-- With one domain of persons and `passenger` a predicate of them. -/
def P_EJ (n : Nat) : Prop :=
  ∀ {A : Type} [Fintype A] (passenger person transported : A → Prop)
    [DecidablePred fun x => passenger x ∧ transported x]
    [DecidablePred fun x => person x ∧ transported x],
    (∀ x, passenger x → person x) →
    AtLeast n passenger transported → AtLeast n person transported

theorem P_EJ_valid (n : Nat) : P_EJ n := by
  unfold P_EJ
  intro A _ passenger person transported _ _ hsub h
  exact le_trans h (card_filter_mono (by intro x hx; exact ⟨hsub x hx.1, hx.2⟩))

/-- With nouns as types: a passenger type, each passenger the journey of
some person (`personOf`, Luo's first projection out of
`Σp:Person. Journey(p)`). Passengers are counted by their own identity,
persons by the person's. -/
def M_EJ (n : Nat) : Prop :=
  ∀ (Person Passenger : Type) [Fintype Passenger] [DecidableEq Passenger] [DecidableEq Person]
    (personOf : Passenger → Person) (transported : Passenger → Prop) [DecidablePred transported],
    countBy id transported ≥ n → countBy personOf transported ≥ n

/-- One person on `n` journeys, for any `n ≥ 2`. -/
theorem M_EJ_not_valid (n : Nat) (hn : 2 ≤ n) : ¬ M_EJ n := by
  intro h
  unfold M_EJ at h
  have h1 : countBy (id : Fin n → Fin n) (fun _ => True) ≥ n := by
    rw [countBy_of_injective id Function.injective_id]
    simp [card]
  have h2 := h Unit (Fin n) (fun _ => ()) (fun _ => True) h1
  have h3 : countBy (fun _ : Fin n => ()) (fun _ => True) ≤ 1 := by
    unfold countBy
    exact (Finset.card_le_univ _).trans (by simp)
  exact absurd (le_trans h2 h3) (by omega)

/-- `n` persons transported means at least `n` passengers transported. -/
theorem M_EJ_converse (n : Nat) {Person Passenger : Type} [Fintype Passenger]
    [DecidableEq Passenger] [DecidableEq Person] (personOf : Passenger → Person)
    (transported : Passenger → Prop) [DecidablePred transported] :
    countBy personOf transported ≥ n → countBy id transported ≥ n :=
  fun h => le_trans h (countBy_le_of_factor personOf id personOf (fun _ => rfl) transported)

/-! ## 3. Double distinctness -/

/-- At least `n` of the `P`s, pairwise distinct by both `f` and `g`. -/
def AtLeastBoth {N B C : Type} (n : Nat) (f : N → B) (g : N → C) (P : N → Prop) : Prop :=
  ∃ S : Finset N, n ≤ S.card ∧ (∀ x ∈ S, P x) ∧ Set.InjOn f ↑S ∧ Set.InjOn g ↑S

/-- Chatzikyriakidis & Luo's (2018) `Three` over a dot-setoid, for any
number: pairwise distinct, where "same" is "same by `f` or same by `g`". -/
def AtLeastDot {N B C : Type} (n : Nat) (f : N → B) (g : N → C) (P : N → Prop) : Prop :=
  ∃ S : Finset N, n ≤ S.card ∧ (∀ x ∈ S, P x) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ (f x = f y ∨ g x = g y)

theorem injOn_both_iff {N B C : Type} (f : N → B) (g : N → C) (S : Set N) :
    (Set.InjOn f S ∧ Set.InjOn g S) ↔ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ (f x = f y ∨ g x = g y) := by
  constructor
  · rintro ⟨hf, hg⟩ x hx y hy hxy (h | h)
    · exact hxy (hf hx hy h)
    · exact hxy (hg hx hy h)
  · intro H
    refine ⟨?_, ?_⟩
    · intro x hx y hy h
      by_contra hxy
      exact H x hx y hy hxy (Or.inl h)
    · intro x hx y hy h
      by_contra hxy
      exact H x hx y hy hxy (Or.inr h)

/-- Pairwise distinctness under "same volume or same text" is distinctness
in both: the two accounts of double distinctness agree. -/
theorem atLeastDot_iff {N B C : Type} (n : Nat) (f : N → B) (g : N → C) (P : N → Prop) :
    AtLeastDot n f g P ↔ AtLeastBoth n f g P := by
  constructor
  · rintro ⟨S, h1, h2, h3⟩
    obtain ⟨hf, hg⟩ := (injOn_both_iff f g ↑S).mpr h3
    exact ⟨S, h1, h2, hf, hg⟩
  · rintro ⟨S, h1, h2, hf, hg⟩
    exact ⟨S, h1, h2, (injOn_both_iff f g ↑S).mp ⟨hf, hg⟩⟩

theorem atLeastBoth_swap {N B C : Type} {n : Nat} {f : N → B} {g : N → C} {P : N → Prop} :
    AtLeastBoth n f g P → AtLeastBoth n g f P :=
  fun ⟨S, h1, h2, hf, hg⟩ => ⟨S, h1, h2, hg, hf⟩

/-- Distinct in both, counted by one: at least as many. -/
theorem countBy_ge_of_both {N B C : Type} [Fintype N] [DecidableEq B] (n : Nat) (f : N → B)
    (g : N → C) {P Q : N → Prop} [DecidablePred Q] (hPQ : ∀ x, P x → Q x)
    (h : AtLeastBoth n f g P) : countBy f Q ≥ n := by
  obtain ⟨S, hS, hP, hf, -⟩ := h
  unfold countBy
  show n ≤ ((Finset.univ.filter Q).image f).card
  calc n ≤ S.card := hS
    _ = (S.image f).card := (Finset.card_image_of_injOn hf).symm
    _ ≤ ((Finset.univ.filter Q).image f).card :=
      Finset.card_le_card (Finset.image_subset_image fun x hx =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ x (hP x hx)⟩)

/-- Gotham's (122): "John picked up and mastered `n` books ⇒ John picked
up `n` books". -/
theorem M_copred_left (n : Nat) {Phy Info Book : Type} [Fintype Book] [DecidableEq Phy]
    (bk : Book → MTT.DotType Phy Info) (pickedUp : Phy → Prop) (mastered : Info → Prop)
    [DecidablePred fun b => pickedUp (bk b).phy] :
    AtLeastBoth n (fun b => (bk b).phy) (fun b => (bk b).info)
      (fun b => pickedUp (bk b).phy ∧ mastered (bk b).info) →
    countBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy) ≥ n := by
  intro h
  exact countBy_ge_of_both (P := fun b => pickedUp (bk b).phy ∧ mastered (bk b).info)
    (Q := fun b => pickedUp (bk b).phy) n _ _ (fun _ hx => hx.1) h

/-- Gotham's (123): "...⇒ John mastered `n` books". -/
theorem M_copred_right (n : Nat) {Phy Info Book : Type} [Fintype Book] [DecidableEq Info]
    (bk : Book → MTT.DotType Phy Info) (pickedUp : Phy → Prop) (mastered : Info → Prop)
    [DecidablePred fun b => mastered (bk b).info] :
    AtLeastBoth n (fun b => (bk b).phy) (fun b => (bk b).info)
      (fun b => pickedUp (bk b).phy ∧ mastered (bk b).info) →
    countBy (fun b => (bk b).info) (fun b => mastered (bk b).info) ≥ n := by
  intro h
  exact countBy_ge_of_both (P := fun b => pickedUp (bk b).phy ∧ mastered (bk b).info)
    (Q := fun b => mastered (bk b).info) n _ _ (fun _ hx => hx.2) (atLeastBoth_swap h)

/-! ## 4. Is "same volume or same text" an equivalence relation? -/

/-- Chatzikyriakidis & Luo's (2018, §4.2) identity on the dot-type, on
books: the same volume or the same text. -/
def DotSame {Phy Info Book : Type} (bk : Book → MTT.DotType Phy Info) (b b' : Book) : Prop :=
  (bk b).phy = (bk b').phy ∨ (bk b).info = (bk b').info

theorem dotSame_refl {Phy Info Book : Type} (bk : Book → MTT.DotType Phy Info) (b : Book) :
    DotSame bk b b :=
  Or.inl rfl

theorem dotSame_symm {Phy Info Book : Type} (bk : Book → MTT.DotType Phy Info) {b b' : Book} :
    DotSame bk b b' → DotSame bk b' b
  | .inl h => .inl h.symm
  | .inr h => .inr h.symm

/-- Not transitive: `x` is a copy of *Crime and Punishment* in volume 1,
`y` a copy of it in volume 2, and `z` another text bound in volume 2. `x`
and `y` share a text, `y` and `z` a volume, `x` and `z` neither. -/
theorem dotSame_not_transitive :
    ¬ ∀ (Phy Info Book : Type) (bk : Book → MTT.DotType Phy Info) (x y z : Book),
      DotSame bk x y → DotSame bk y z → DotSame bk x z := by
  intro h
  have := h Bool Bool (Bool × Bool) (fun b => ⟨b.1, b.2⟩) (false, false) (true, false)
    (true, true) (Or.inr rfl) (Or.inl rfl)
  simp [DotSame] at this

/-- Transitive once each volume has one text (Chatzikyriakidis & Luo's
n. 4 inclination). -/
theorem dotSame_trans_of {Phy Info Book : Type} (bk : Book → MTT.DotType Phy Info)
    (htext : OneTextPerVolume bk) {x y z : Book} :
    DotSame bk x y → DotSame bk y z → DotSame bk x z := by
  rintro (hxy | hxy) (hyz | hyz)
  · exact Or.inl (hxy.trans hyz)
  · exact Or.inr ((htext x y hxy).trans hyz)
  · exact Or.inr (hxy.trans (htext y z hyz))
  · exact Or.inr (hxy.trans hyz)

end FraCaS.Encodings.Criteria
