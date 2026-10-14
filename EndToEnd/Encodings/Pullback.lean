import EndToEnd.Encodings.Typed

/-!
# Quantifiers over a noun's type, read as quantifiers on that type

`Typed.lean` transfers a typed quantifier to the individuals, and for the
counting determiners that needs the noun's embedding to be injective. This
file reads it on the noun's own type instead, with no condition at all:
`AtLeastT n e C Q` says exactly what `AtLeast n` says of the predicates
`C ∘ e` and `Q ∘ e` of the type's elements. Counting elements of `N` is
counting elements of `N`, whatever `e` identifies.

Phase 3 of the noun-encoding comparison (`README.md` here) uses it to
score M's claims with the pipeline's own prover: where a premise and a
hypothesis count the same noun's type, as "at least three female
commissioners" and "at least three commissioners" do in M, the pulled-back
claim is an ordinary claim about predicates of that type.
-/

namespace FraCaS.Encodings.Typed
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd

variable {N A : Type}

theorem every_pull (e : N → A) (C Q : A → Prop) :
    EveryT e C Q ↔ Every (fun y => C (e y)) (fun y => Q (e y)) := Iff.rfl

theorem some_pull (e : N → A) (C Q : A → Prop) :
    SomeT e C Q ↔ Some (fun y => C (e y)) (fun y => Q (e y)) := Iff.rfl

theorem no_pull (e : N → A) (C Q : A → Prop) :
    NoT e C Q ↔ No (fun y => C (e y)) (fun y => Q (e y)) := Iff.rfl

/-- Counting through `e` is counting on `N`; no injectivity needed. -/
theorem cardT_pull [Fintype N] (e : N → A) (P : A → Prop) [DecidablePred fun y => P (e y)] :
    cardT e P = card (fun y => P (e y)) := by
  unfold cardT card
  congr!

open Classical in
theorem atLeast_pull [Fintype N] (e : N → A) (n : Nat) (C Q : A → Prop) :
    AtLeastT n e C Q ↔ AtLeast n (fun y => C (e y)) (fun y => Q (e y)) := by
  have h := cardT_pull e (fun x => C x ∧ Q x)
  simp only [AtLeastT, AtLeast]
  constructor <;> intro <;> omega

open Classical in
theorem atMost_pull [Fintype N] (e : N → A) (n : Nat) (C Q : A → Prop) :
    AtMostT n e C Q ↔ AtMost n (fun y => C (e y)) (fun y => Q (e y)) := by
  have h := cardT_pull e (fun x => C x ∧ Q x)
  simp only [AtMostT, AtMost]
  constructor <;> intro <;> omega

open Classical in
theorem exactly_pull [Fintype N] (e : N → A) (n : Nat) (C Q : A → Prop) :
    ExactlyT n e C Q ↔ Exactly n (fun y => C (e y)) (fun y => Q (e y)) := by
  have h := cardT_pull e (fun x => C x ∧ Q x)
  simp only [ExactlyT, Exactly]
  constructor <;> intro <;> omega

open Classical in
theorem most_pull [Fintype N] (e : N → A) (C Q : A → Prop) :
    MostT e C Q ↔ Most (fun y => C (e y)) (fun y => Q (e y)) := by
  have h := cardT_pull e (fun x => C x ∧ Q x)
  have h' := cardT_pull e C
  simp only [MostT, Most]
  constructor <;> intro <;> omega

open Classical in
theorem more_pull [Fintype N] (e : N → A) (C Q R : A → Prop) :
    MoreT e C Q R ↔ More (fun y => C (e y)) (fun y => Q (e y)) (fun y => R (e y)) := by
  have h := cardT_pull e (fun x => C x ∧ Q x)
  have h' := cardT_pull e (fun x => C x ∧ R x)
  simp only [MoreT, More]
  constructor <;> intro <;> omega

open Classical in
theorem both_pull [Fintype N] (e : N → A) (C Q : A → Prop) :
    BothT e C Q ↔ Both (fun y => C (e y)) (fun y => Q (e y)) := by
  have h := cardT_pull e C
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

open Classical in
theorem neither_pull [Fintype N] (e : N → A) (C Q : A → Prop) :
    NeitherT e C Q ↔ Neither (fun y => C (e y)) (fun y => Q (e y)) := by
  have h := cardT_pull e C
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

end FraCaS.Encodings.Typed
