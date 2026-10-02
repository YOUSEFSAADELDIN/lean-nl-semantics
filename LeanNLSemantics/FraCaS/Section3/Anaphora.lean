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
pronoun to the most recent impersonal referent (preferring a proper
noun over a same-gender indefinite mentioned in between, when both are
candidates), and an indefinite object becomes either a fresh
existential or a fresh named individual depending on which the real
theorem's own type needs (a discourse-structural fact the tree's own
shape alone doesn't decide). It independently reproduces both problem
120's own referential-pronoun formalization above (`∃m, attended smith
m ∧ chaired smith m`) and problem 121's own three-sentence ternary one
(`delivered smith itel report ∧ delivered smith itel invoice ∧
delivered smith itel proposal`, "them" correctly preferring ITEL over
the report/invoice mentioned nearer it) from the raw GF trees, confirmed
via `scripts/gen_gf_cross_check.py`'s own `_build_fracas_120`/
`_build_fracas_121`.

Two more ids, 139 and 140, are likewise reproduced from their raw GF
trees, but through `translate_cl` itself rather than through
`translate_discourse` — both are single-sentence reflexive shapes, not
cross-sentential threading, so they fit `translate_cl`'s own per-sentence
dispatch instead: `_try_translate_reflexive_indefinite_subject` handles
139's ditransitive reflexive ("A company director awarded himself a
large payrise"), existentially binding the subject and dropping the
ditransitive object (`∃d, awardLargePayrise d d`); `_try_translate_
sentential_complement` composed with `_try_translate_reflexive_named_
subject` handles 140's "John said that Bill had hurt himself," recursing
`translate_cl` on the embedded clause rather than hand-resolving it
(`said john (hurt bill bill)`). Confirmed via `_build_fracas_139`/
`_build_fracas_140`.

A third pipeline, `_try_translate_skolem_universal_premise`/
`_try_translate_skolem_continuation`, reproduces 131 and 132's shared
dependent-plural/paycheque pattern: "each department has a dedicated
line" only becomes a Skolem function (one line per department) because
a LATER sentence anaphorically continues it — "they rent them from BT"
(131) continues at the bound variable itself, giving `∀d, department d
→ rentBt d (dedicatedLineOf d)`; "the sales department rents it from
BT" (132) continues at one named instance instead,
`rentBt salesDepartment (dedicatedLineOf salesDepartment)` — the exact
same context-dependence `translate_discourse`'s own `existential_objects`
flag already makes explicit for 120/121. Confirmed via
`_build_fracas_131`/`_build_fracas_132`.

A fourth pipeline, `_try_translate_universal_existential_premise`/
`_try_translate_universal_existential_continuation`, reproduces 122's
own donkey-pronoun MERGE: "every committee has a chairman" uses the
SAME "every X has a Y" shape 131/132's premise 1 does, but needs a
THIRD distinct reading of it here — an existentially-bound witness
SHARED with (not a function of) premise 2's own continuation, nested
INSIDE the same universal scope as one conjunction rather than two
separate antecedents. Premise 2's own "he is appointed by its members"
additionally needed passive-VP parsing (`PassV2` + `by8agent_Prep`) and
a possessive-pronoun-governed agent phrase, neither handled anywhere
else in this translator — both narrowly scoped to this one shape,
confirmed to reproduce the prior hand-built derivation byte-for-byte
(`∀c, committee c → ∃ch, chairman ch c ∧ appointMember ch c`, the
witness variable `ch` falling back to a two-letter prefix to avoid
colliding with the bound variable `c`, since "committee" and "chairman"
start with the same letter). Confirmed via `_build_fracas_122`.

A fifth pipeline, `_try_translate_cardinal_adjective_property`/
`_try_translate_cardinal_passive_property`, reproduces 124's own
cardinal/set-based anaphora: "two out of ten machines are missing"
(premise 1) and "two machines have been removed" (the hypothesis) each
reduce to just a count plus an adjective's/verb's own name — the
restrictor noun ("machines") and the partitive's own denominator ("out
of ten") carry no information in this id's own real theorem at all,
which treats the whole domain as being exactly the ten machines via a
trivial `fun _ => True` restrictor. Confirmed via `_build_fracas_124`.

A definite-description-licensed total function (138) reuses 131/132's
own `_try_translate_skolem_universal_premise` directly for its premise
1 (the Skolem function's own name only, not the bound/witness
variables 131/132's own continuation needs, since 138 never weakens
back to an existential), paired with a new `_try_translate_definite_
skolem_application` that recovers the Skolem function's application to
a named individual straight from the HYPOTHESIS's own fully explicit
"the cover page OF R-95-103" (an `of`-PP-linked definite description) —
not from premise 3's own bare "the cover page", whose tree has no link
to R-95-103 at all (that link is a discourse fact, and premise 3/the
hypothesis share the identical fact textually anyway, so premise 3 is
no longer read at all). Confirmed via `_build_fracas_138`.

Together these nine ids (120/121/122/124/131/132/138/139/140) do not
cover any other id in this file — genuine multi-reading referential
ambiguity (128-130) or e-type "upgrade the witness set to the whole
set" anaphora (133) are each a genuinely different resolution mechanism
from all six pipelines above, not an incremental extension of any of
them — left hand-resolved exactly as this header already describes,
extended only when another confirmed GF tree needs more, the same
incremental discipline `translate.py`'s own `_try_translate_*`
functions already follow.
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
