import LeanNLSemantics.FraCaS.Section2.Plurals

/-!
# Shared machinery for FraCaS Section 3 (Anaphora)

Section 3 tests pronoun/anaphora resolution (referential and bound
pronouns, donkey sentences, e-type anaphora, dependent plurals,
paycheque pronouns, modal subordination, reflexives). This project does
not build general anaphora-resolution machinery (an assignment-function/
discourse-referent apparatus, as in DRT) — instead, each problem's
pronoun is resolved by hand into the Lean formalization directly, the
same way named individuals and definite descriptions already are
elsewhere in this port. Concretely, two recurring encodings:

- **Referential pronouns across sentences** ("Smith attended a meeting.
  She chaired it.") are formalized as *one* combined statement sharing
  the same bound variable for the antecedent and its pronoun, rather
  than as two separate premises — this is exactly what "keeping track of
  the same entity across sentences" (FraCaS's own `<why>` for problem
  121) means concretely in Lean: `∃m, attended smith m ∧ chaired smith m`,
  not two unrelated existentials.
- **Bound/donkey pronouns** ("Every committee has a chairman. He is
  appointed by its members." / "Every customer who owns a computer has a
  service contract for it.") are formalized with a Skolem-style function
  or an inner universal tying the pronoun to the binder, e.g. `∀x,
  P x → Q x (f x)` or `∀x, P x → ∀y, R x y → S x y` — the standard
  donkey-sentence move, chosen per-problem to match the reading FraCaS's
  own gold answer actually tests (see `Batch2.lean`'s problem 136 for a
  case where the *weak* donkey reading, not the *strong/universal* one
  used in 134/135, is the one that matches).

This file adds one small piece of arithmetic `Batch2.lean`'s problem 137
needs: relating `card (fun _ => True)` (the "how many things are there
at all" count) to `Fintype.card`, so a proportion problem can be posed
over an abstract `Fintype` with a stated total rather than a concrete
enumerated type.
-/

namespace FraCaS.Section3

open FraCaS.Section1
open FraCaS.Section2

/-- The whole-domain count, `card (fun _ => True)`, is just
`Fintype.card` — lets a proportion problem state "100 companies" as a
hypothesis on an abstract `Fintype`, instead of forcing a concrete
100-element type just to make `card` compute. -/
theorem card_true_eq_card_type {A : Type*} [Fintype A] :
    card (fun _ : A => True) = Fintype.card A := by
  rw [← Finset.card_univ]
  congr 1
  apply Finset.ext
  intro x
  simp

end FraCaS.Section3
