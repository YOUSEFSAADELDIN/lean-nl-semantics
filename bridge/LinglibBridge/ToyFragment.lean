import LinglibBridge
import Linglib.Fragments.English.Toy

/-!
# A real linglib fragment, not an invented one

`LinglibBridge.lean`'s own header envisions "a real fragment['s chosen]
`E`" feeding `Lexicon`/`CN'` directly, and `Section5Pilot.lean`'s own
`S5Individual` is a step toward that — but it is still an entity domain
*this project* invented, shaped to match FraCaS's own Section 5
vocabulary, not something linglib itself ships. This file instead uses
`Linglib.Fragments.English.Toy`'s own `Semantics.Montague.ToyEntity` —
linglib's pedagogical four-entity model (`john`, `mary`, `pizza`,
`book`), built the model-theoretic way, with real predicate denotations
(`ToyLexicon.student_sem`, `.person_sem`, `.thing_sem`) read directly off
a mathlib first-order `Structure` — genuinely external content this
project did not author.

This also exercises the general case `Lexicon.embed_mono`'s own
docstring describes and every instance built so far has sidestepped:
"fragment-specific lexical content, not provable in general." Both
`toyLexicon` and `section5Lexicon` are `KindedLexicon`s — `embed_mono`
there comes free from `le_trans` because every individual carries one
stipulated most-specific tag. Nothing here stipulates that `student`,
`person` and `thing` nest inside one another: `ToyFacts.student`,
`.person` and `.thing` are three *independent* functions linglib's own
model happens to make extensionally nested (every student is a person,
every person is a thing, in this one model). `embed_mono` below is
discharged by actually checking that extensional fact over all four
entities via `decide`, using linglib's own `DecidablePred` instances for
these predicates — real lexical content, verified, not assumed, and not
derivable from any shared `kind` function because there isn't one.
-/

namespace MTT.LinglibBridge

/-! ## A three-tag lattice over linglib's own `student`/`person`/`thing` -/

/-- `student ≤ person ≤ thing`, matching `ToyFacts`'s own extensional
nesting over the four toy entities — checked below, not assumed. -/
inductive ToyCNTag where
  | thing
  | person
  | student
  deriving DecidableEq, Repr

instance : Fintype ToyCNTag where
  elems := {.thing, .person, .student}
  complete x := by cases x <;> decide

def ToyCNTag.ancestors : ToyCNTag → List ToyCNTag
  | .thing => [.thing]
  | .person => [.person, .thing]
  | .student => [.student, .person, .thing]

instance : PartialOrder ToyCNTag where
  le a b := b ∈ a.ancestors
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := ToyCNTag) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (b ∈ a.ancestors))

/-! ## The lexicon, over linglib's own entities and predicates -/

/-- `embed` reads each tag's membership directly off linglib's own
`ToyLexicon` denotations — no `kind` function, no `KindedLexicon`. -/
def toyFragmentLexicon : Lexicon ToyCNTag Semantics.Montague.ToyEntity where
  embed t := match t with
    | .thing => Semantics.Montague.ToyLexicon.thing_sem
    | .person => Semantics.Montague.ToyLexicon.person_sem
    | .student => Semantics.Montague.ToyLexicon.student_sem
  embed_mono := by
    intro a b hab
    cases a <;> cases b <;>
      first
        | exact absurd hab (by decide)
        | decide

/-! ## A concrete instance -/

/-- John, as a student-typed element of the bridge's own `CN'` — not
stipulated, `decide`-checked against `ToyLexicon.student_sem` directly. -/
def johnAsStudent : CN' toyFragmentLexicon .student :=
  ⟨Semantics.Montague.ToyEntity.john,
    (by decide : Semantics.Montague.ToyLexicon.student_sem Semantics.Montague.ToyEntity.john)⟩

/-- John widens to a person for free — `CN'.widen`'s only obligation,
`.student ≤ .person`, is exactly the fact `embed_mono` above already
checked holds for every entity, not just John. -/
example : CN' toyFragmentLexicon .person :=
  CN'.widen toyFragmentLexicon (by decide) johnAsStudent

/-- The same fact stated as a bare implication over linglib's own
predicates, matching `Section5Pilot.lean`'s own style of corollary: not
a new proof, `CN'.widen` specialised to this one edge. -/
example :
    Semantics.Montague.ToyLexicon.student_sem Semantics.Montague.ToyEntity.john →
      Semantics.Montague.ToyLexicon.person_sem Semantics.Montague.ToyEntity.john :=
  fun h => (CN'.widen toyFragmentLexicon (by decide)
    (⟨Semantics.Montague.ToyEntity.john, h⟩ : CN' toyFragmentLexicon .student)).2

end MTT.LinglibBridge
