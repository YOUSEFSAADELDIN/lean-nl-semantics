import EndToEnd.Quantifiers
import LeanNLSemantics.FraCaS.Section2.Plurals

/-!
# Quantifiers over a noun's type, and their transfer to predicates

Phase 2 of the noun-encoding comparison (`EndToEnd/Encodings/README.md`)
states the pipeline's claims with each quantified noun as a type `N`,
embedded into the individuals by `e : N → A`. A determiner ranges over
`N`; what it says of an element is said of its individual, `e y` - verbs
and adjectives stay predicates of individuals, as in Phases 1a and 1b.
`C` is what restricts the noun further (a relative clause), `fun _ =>
True` when nothing does.

The transfer lemmas say exactly when this changes nothing. Every, some
and no transfer always: `EveryT e C Q ↔ Every (fun x => IsA e x ∧ C x) Q`,
where `IsA e x` - "x is an N" - is that `x` is the image of some element
of `N`. The counting determiners transfer when `e` is injective
(`cardT_eq`), and not in general (`counting_needs_injectivity`): with
nouns as types, "two Ns" counts elements of `N`, which need not be two
individuals. That is MTT's individuation question (Chatzikyriakidis &
Luo); the MInj variant states injectivity, the M variant does not.

So a claim stated with `EveryT`, ..., `MoreT` and `IsA` and injective
embeddings is the pipeline's claim with each noun `n` read as `IsA eN`;
and since every predicate `n` is `IsA` of the inclusion of `{x // n x}`,
the two are valid together. The opaque `Many` and `Few` are the
exception: stated at every type in M, at the individuals in F.
-/

namespace FraCaS.Encodings.Typed
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd

variable {N A : Type}

/-- "x is an N": `x` is the individual of some element of `N`. -/
def IsA (e : N → A) (x : A) : Prop := ∃ y, e y = x

def EveryT (e : N → A) (C Q : A → Prop) : Prop := ∀ y, C (e y) → Q (e y)
def SomeT (e : N → A) (C Q : A → Prop) : Prop := ∃ y, C (e y) ∧ Q (e y)
def NoT (e : N → A) (C Q : A → Prop) : Prop := ∀ y, C (e y) → ¬ Q (e y)

/-- How many elements of `N` satisfy `P` (of their individuals). -/
noncomputable def cardT [Fintype N] (e : N → A) (P : A → Prop) : Nat := by
  classical exact (Finset.univ.filter fun y => P (e y)).card

def MostT [Fintype N] (e : N → A) (C Q : A → Prop) : Prop :=
  2 * cardT e (fun x => C x ∧ Q x) > cardT e C
def AtLeastT [Fintype N] (n : Nat) (e : N → A) (C Q : A → Prop) : Prop :=
  cardT e (fun x => C x ∧ Q x) ≥ n
def AtMostT [Fintype N] (n : Nat) (e : N → A) (C Q : A → Prop) : Prop :=
  cardT e (fun x => C x ∧ Q x) ≤ n
def ExactlyT [Fintype N] (n : Nat) (e : N → A) (C Q : A → Prop) : Prop :=
  cardT e (fun x => C x ∧ Q x) = n
def BothT [Fintype N] (e : N → A) (C Q : A → Prop) : Prop :=
  cardT e C = 2 ∧ EveryT e C Q
def NeitherT [Fintype N] (e : N → A) (C Q : A → Prop) : Prop :=
  cardT e C = 2 ∧ NoT e C Q
def MoreT [Fintype N] (e : N → A) (C Q R : A → Prop) : Prop :=
  cardT e (fun x => C x ∧ Q x) > cardT e (fun x => C x ∧ R x)

/-! ## Transfer -/

theorem every_t (e : N → A) (C Q : A → Prop) :
    EveryT e C Q ↔ Every (fun x => IsA e x ∧ C x) Q := by
  constructor
  · rintro h x ⟨⟨y, rfl⟩, hc⟩
    exact h y hc
  · intro h y hc
    exact h (e y) ⟨⟨y, rfl⟩, hc⟩

theorem some_t (e : N → A) (C Q : A → Prop) :
    SomeT e C Q ↔ Some (fun x => IsA e x ∧ C x) Q := by
  constructor
  · rintro ⟨y, hc, hq⟩
    exact ⟨e y, ⟨⟨y, rfl⟩, hc⟩, hq⟩
  · rintro ⟨x, ⟨⟨y, rfl⟩, hc⟩, hq⟩
    exact ⟨y, hc, hq⟩

theorem no_t (e : N → A) (C Q : A → Prop) :
    NoT e C Q ↔ No (fun x => IsA e x ∧ C x) Q := by
  constructor
  · rintro h x ⟨⟨y, rfl⟩, hc⟩
    exact h y hc
  · intro h y hc
    exact h (e y) ⟨⟨y, rfl⟩, hc⟩

/-- Counting through an injective embedding counts individuals. -/
theorem cardT_eq [Fintype N] [Fintype A] (e : N → A) (he : Function.Injective e) (P : A → Prop)
    [DecidablePred fun x => IsA e x ∧ P x] :
    cardT e P = card (fun x => IsA e x ∧ P x) := by
  classical
  unfold cardT card
  rw [← Finset.card_map ⟨e, he⟩]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, IsA]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, hy⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, hy, rfl⟩

/-- `card` does not depend on how its predicate is stated. -/
theorem card_iff [Fintype A] {P P' : A → Prop} [DecidablePred P] [DecidablePred P']
    (h : ∀ x, P x ↔ P' x) : card P = card P' := by
  unfold card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h x

open Classical in
/-- `cardT` of a conjunction, as the pipeline's `card` of its restrictor's conjunction. -/
theorem cardT_and [Fintype N] [Fintype A] (e : N → A) (he : Function.Injective e) (C Q : A → Prop) :
    cardT e (fun x => C x ∧ Q x) = card (fun x => (IsA e x ∧ C x) ∧ Q x) := by
  rw [cardT_eq e he]
  exact card_iff fun _ => and_assoc.symm

open Classical in
theorem atLeast_t [Fintype N] [Fintype A] (e : N → A) (he : Function.Injective e) (n : Nat)
    (C Q : A → Prop) : AtLeastT n e C Q ↔ AtLeast n (fun x => IsA e x ∧ C x) Q := by
  have h := cardT_and e he C Q
  simp only [AtLeastT, AtLeast]
  constructor <;> intro <;> omega

open Classical in
theorem atMost_t [Fintype N] [Fintype A] (e : N → A) (he : Function.Injective e) (n : Nat)
    (C Q : A → Prop) : AtMostT n e C Q ↔ AtMost n (fun x => IsA e x ∧ C x) Q := by
  have h := cardT_and e he C Q
  simp only [AtMostT, AtMost]
  constructor <;> intro <;> omega

open Classical in
theorem exactly_t [Fintype N] [Fintype A] (e : N → A) (he : Function.Injective e) (n : Nat)
    (C Q : A → Prop) : ExactlyT n e C Q ↔ Exactly n (fun x => IsA e x ∧ C x) Q := by
  have h := cardT_and e he C Q
  simp only [ExactlyT, Exactly]
  constructor <;> intro <;> omega

open Classical in
theorem most_t [Fintype N] [Fintype A] (e : N → A) (he : Function.Injective e)
    (C Q : A → Prop) : MostT e C Q ↔ Most (fun x => IsA e x ∧ C x) Q := by
  have h := cardT_and e he C Q
  have h' := cardT_eq e he C
  simp only [MostT, Most]
  constructor <;> intro <;> omega

open Classical in
theorem more_t [Fintype N] [Fintype A] (e : N → A) (he : Function.Injective e)
    (C Q R : A → Prop) : MoreT e C Q R ↔ More (fun x => IsA e x ∧ C x) Q R := by
  have h := cardT_and e he C Q
  have h' := cardT_and e he C R
  simp only [MoreT, More]
  constructor <;> intro <;> omega

open Classical in
theorem both_t [Fintype N] [Fintype A] (e : N → A) (he : Function.Injective e)
    (C Q : A → Prop) : BothT e C Q ↔ Both (fun x => IsA e x ∧ C x) Q := by
  have h := cardT_eq e he C
  simp only [BothT, Both, every_t]
  rw [h]

open Classical in
theorem neither_t [Fintype N] [Fintype A] (e : N → A) (he : Function.Injective e)
    (C Q : A → Prop) : NeitherT e C Q ↔ Neither (fun x => IsA e x ∧ C x) Q := by
  have h := cardT_eq e he C
  simp only [NeitherT, Neither, no_t]
  rw [h]

open Classical in
/-- Without injectivity the counting determiners do not transfer: two
elements of a noun's type that are one individual count as two Ns. Here
`Bool` embeds into one individual: "at least two Ns" holds of the type,
and fails of the individuals that are Ns. -/
theorem counting_needs_injectivity :
    AtLeastT 2 (fun _ : Bool => ()) (fun _ => True) (fun _ => True) ∧
    ¬ AtLeast 2 (fun x => IsA (fun _ : Bool => ()) x ∧ True) (fun _ => True) := by
  constructor
  · simp [AtLeastT, cardT]
  · intro h
    have h1 : card (fun x : Unit => (IsA (fun _ : Bool => ()) x ∧ True) ∧ True) ≤ 1 := by
      unfold card
      exact (Finset.card_filter_le _ _).trans (by simp)
    simp only [AtLeast] at h
    omega

end FraCaS.Encodings.Typed
