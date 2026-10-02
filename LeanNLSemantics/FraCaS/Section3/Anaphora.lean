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

One caveat to "no general machinery," specific to the GF cross-check
tooling rather than the Lean formalization above (which stays entirely
hand-written either way): `gf/translate.py`'s `translate_discourse`
function is a real, reusable (if deliberately narrow) cross-sentential
pronoun-resolution mechanism — a personal subject pronoun resolves to
the most recently introduced personal referent, an impersonal object
pronoun to the most recent impersonal (existentially-bound) one — that
independently reproduces problem 120's own referential-pronoun
formalization above (`∃m, attended smith m ∧ chaired smith m`) from the
raw GF trees, confirmed via `scripts/gen_gf_cross_check.py`'s own
`_build_fracas_120`. It does not yet cover any other id in this file
(121's PP-complement verb and three-sentence chain, the donkey-pronoun
Skolemization, or anything else below) — those remain exactly as hand-
resolved as this header already describes, extended only when another
confirmed GF tree needs more, the same incremental discipline
`translate.py`'s own `_try_translate_*` functions already follow.
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
  have heq : (Finset.univ.filter fun _ : A => True) = (Finset.univ : Finset A) :=
    Finset.ext (fun x => by simp)
  calc card (fun _ : A => True) = (Finset.univ.filter fun _ : A => True).card := rfl
    _ = (Finset.univ : Finset A).card := congrArg Finset.card heq
    _ = Fintype.card A := Finset.card_univ

end FraCaS.Section3
