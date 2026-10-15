import EndToEnd.Encodings.Criteria

/-!
# No setoid counts copredicated books

Chatzikyriakidis & Luo (2018) interpret common nouns as setoids, types
with an equivalence relation, and count with a generic numeral that
asks for elements pairwise distinct under the relation ((32), p. 131).
For "John picked up and mastered three books" they use the dot-setoid,
whose relation is "same volume or same text" (§4.2, p. 134). Pairwise
distinctness under it is double distinctness, the reading they want
((47)), and Gotham's (2017) too (`atLeastDot_iff`). They add (p. 135):
"as far as correctness is concerned, as long as it is an equivalence
relation, it would do. Our definition does result in an equivalence
relation."

`Criteria.lean` showed the relation is not transitive once one text has
two copies and one volume holds two texts (`dotSame_not_transitive`).
This file shows the problem is not the choice of relation:

- **`exists_setoid_iff`.** For any books, with any volume map `f` and
  text map `g`, some equivalence relation's pairwise-distinctness
  numerals coincide with double distinctness, for every number and
  every predicate, **if and only if** "same volume or same text" is
  transitive on those books. The only candidate is that relation
  itself.
- **`no_setoid`.** In a library with two copies of *Crime and
  Punishment*, one of them bound with *Notes from Underground*, no
  equivalence relation does it. Every setoid on those three books
  miscounts "picked up and mastered two books" for some choice of what
  John picked up and mastered: it counts two where there is one, or one
  where there are two.

Chatzikyriakidis & Luo's n. 4 (p. 123) accepts such libraries,
following Asher and Gotham, while saying they "incline to believe"
otherwise. So under the view they adopt, the counting in their (47)
cannot come from any setoid, and their remark that any equivalence
relation "would do" cannot be met. Their predictions are those of
double distinctness, which are right. What fails is the claim that a
setoid delivers them.

Gotham (2017, (14), p. 339) states the same reading with *two*
relations, PHYS and INFO, each transitive and symmetric: a plurality
compressible by neither. That is `AtLeastBoth`, distinct under each of
two equivalence relations. The theorem says two cannot be traded for
one.

Since counting a setoid's pairwise-distinct elements is counting its
equivalence classes, this also places copredication outside counting
by a single identity criterion, the setting of `Characterization.lean`.
-/

namespace FraCaS.Encodings.DotSetoid
open FraCaS.Encodings.Criteria

variable {N B C : Type}

/-- Chatzikyriakidis & Luo's generic numeral, for any number and any
relation `E`: at least `n` of the `P`s, pairwise distinct under `E`. -/
def AtLeastBy (n : Nat) (E : N → N → Prop) (P : N → Prop) : Prop :=
  ∃ S : Finset N, n ≤ S.card ∧ (∀ x ∈ S, P x) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ E x y

/-- The dot-setoid's relation on books: the same volume or the same text. -/
def Same (f : N → B) (g : N → C) (x y : N) : Prop := f x = f y ∨ g x = g y

theorem same_symm {f : N → B} {g : N → C} {x y : N} : Same f g x y → Same f g y x
  | .inl h => .inl h.symm
  | .inr h => .inr h.symm

/-- Over "same volume or same text", the generic numeral is double
distinctness (`Criteria.atLeastDot_iff`). -/
theorem atLeastBy_same_iff (n : Nat) (f : N → B) (g : N → C) (P : N → Prop) :
    AtLeastBy n (Same f g) P ↔ AtLeastBoth n f g P :=
  atLeastDot_iff n f g P

/-- "At least two" of two given things holds exactly when neither is
related to the other. -/
theorem atLeastBy_two_pair [DecidableEq N] {E : N → N → Prop} {x y : N} (hxy : x ≠ y) :
    AtLeastBy 2 E (fun a => a = x ∨ a = y) ↔ (¬ E x y ∧ ¬ E y x) := by
  constructor
  · rintro ⟨S, hS, hP, hD⟩
    have hsub : S ⊆ {x, y} := fun a ha => by
      rcases hP a ha with rfl | rfl <;> simp
    have heq : S = {x, y} :=
      Finset.eq_of_subset_of_card_le hsub ((Finset.card_pair hxy).le.trans hS)
    have hx : x ∈ S := by rw [heq]; simp
    have hy : y ∈ S := by rw [heq]; simp
    exact ⟨hD x hx y hy hxy, hD y hy x hx (Ne.symm hxy)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨{x, y}, (Finset.card_pair hxy).ge, ?_, ?_⟩
    · intro a ha
      simpa using ha
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact h1
      · exact h2
      · exact absurd rfl hab

/-- **A setoid gives double distinctness exactly when "same volume or
same text" is transitive.** For given books, volumes and texts: some
equivalence relation's numerals agree with double distinctness for
every number and predicate if and only if the dot-setoid's relation is
transitive on these books. -/
theorem exists_setoid_iff [DecidableEq N] (f : N → B) (g : N → C) :
    (∃ E : N → N → Prop, Equivalence E ∧
      ∀ (n : Nat) (P : N → Prop), AtLeastBy n E P ↔ AtLeastBoth n f g P) ↔
    ∀ x y z, Same f g x y → Same f g y z → Same f g x z := by
  constructor
  · rintro ⟨E, hE, hcount⟩
    -- The relation is forced: two books are related exactly when they
    -- share a volume or a text, by "at least two" of the two of them.
    have key : ∀ x y, E x y ↔ Same f g x y := by
      intro x y
      by_cases hxy : x = y
      · subst hxy
        exact ⟨fun _ => Or.inl rfl, fun _ => hE.refl x⟩
      · have h := (atLeastBy_two_pair (E := E) hxy).symm.trans
          ((hcount 2 _).trans ((atLeastBy_same_iff 2 f g _).symm.trans
            (atLeastBy_two_pair (E := Same f g) hxy)))
        constructor
        · intro hExy
          by_contra hS
          exact (h.mpr ⟨hS, fun h' => hS (same_symm h')⟩).1 hExy
        · intro hS
          by_contra hExy
          exact (h.mp ⟨hExy, fun h' => hExy (hE.symm h')⟩).1 hS
    intro x y z hxy hyz
    exact (key x z).mp (hE.trans ((key x y).mpr hxy) ((key y z).mpr hyz))
  · intro htrans
    exact ⟨Same f g, ⟨fun _ => Or.inl rfl, fun h => same_symm h, fun h1 h2 => htrans _ _ _ h1 h2⟩,
      fun n P => atLeastBy_same_iff n f g P⟩

/-! ## The library of `Criteria.dotSame_not_transitive` -/

/-- Two copies of *Crime and Punishment*, and *Notes from Underground*
bound in the same volume as the second copy. -/
inductive Lib | cp1 | cp2 | nfu
  deriving DecidableEq

/-- Volumes: the first copy is volume 1; the second copy and *Notes from
Underground* share volume 2. -/
def vol : Lib → Bool
  | .cp1 => false
  | .cp2 => true
  | .nfu => true

/-- Texts: both copies are *Crime and Punishment*. -/
def text : Lib → Bool
  | .cp1 => false
  | .cp2 => false
  | .nfu => true

/-- **No setoid counts these books.** No equivalence relation on the
three books makes the generic numeral agree with double distinctness. -/
theorem no_setoid :
    ¬ ∃ E : Lib → Lib → Prop, Equivalence E ∧
      ∀ (n : Nat) (P : Lib → Prop), AtLeastBy n E P ↔ AtLeastBoth n vol text P := by
  rw [exists_setoid_iff]
  intro h
  have := h .cp1 .cp2 .nfu (Or.inr rfl) (Or.inl rfl)
  simp [Same, vol, text] at this

/-- What double distinctness says of the library: John picked up and
mastered two books when he did so with the first copy and *Notes from
Underground* (two volumes, two texts), but not when he did so with the
two copies (one text) or with the second copy and *Notes from
Underground* (one volume). Any setoid gets one of these wrong. -/
theorem library_counts :
    AtLeastBoth 2 vol text (fun b => b = .cp1 ∨ b = .nfu) ∧
    ¬ AtLeastBoth 2 vol text (fun b => b = .cp1 ∨ b = .cp2) ∧
    ¬ AtLeastBoth 2 vol text (fun b => b = .cp2 ∨ b = .nfu) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← atLeastBy_same_iff, atLeastBy_two_pair (x := .cp1) (y := .nfu) (by decide)]
    simp [Same, vol, text]
  · rw [← atLeastBy_same_iff, atLeastBy_two_pair (x := .cp1) (y := .cp2) (by decide)]
    simp [Same, vol, text]
  · rw [← atLeastBy_same_iff, atLeastBy_two_pair (x := .cp2) (y := .nfu) (by decide)]
    simp [Same, vol, text]

end FraCaS.Encodings.DotSetoid
