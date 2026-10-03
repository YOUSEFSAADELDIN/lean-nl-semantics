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
a new proof, `Lexicon.embed_mono` itself (what `CN'.widen` is built
from) specialised to this one edge and this one entity. `a`/`b` are
pinned explicitly rather than left for unification to find through the
`.property` projection on a `CN'.widen` result, which leaves `b` an
unresolved metavariable at the point `by decide` needs a concrete goal. -/
example :
    Semantics.Montague.ToyLexicon.student_sem Semantics.Montague.ToyEntity.john →
      Semantics.Montague.ToyLexicon.person_sem Semantics.Montague.ToyEntity.john :=
  toyFragmentLexicon.embed_mono (a := .student) (b := .person) (by decide)
    Semantics.Montague.ToyEntity.john

/-! ## The general theorem, over real external content

Everything above exercises `Lexicon`/`CN'`/`embed_mono` directly, but
never the one genuinely general result this bridge has proven,
`LinglibBridge.lean`'s own `CN'.intersective_widen`. Applying it here —
rather than only ever at `L := section5Lexicon`, as
`Section5Pilot.lean`'s `fracas_202_bridge`/`fracas_214_bridge` do — is
what tells apart "a theorem about `section5Lexicon`" from "a theorem
about `Lexicon`": the same one line of proof, unchanged, specializes to
a lexicon built from someone else's model instead of this project's own.

The intersective predicate has to be independent of the `student`/
`person`/`thing` tag hierarchy itself, or this would secretly just be
`embed_mono` again. `ToyLexicon.laughs_sem` is: linglib's own fact about
who laughs, unrelated to anyone's student/person/thing status, read off
`toyStructure`'s `laugh` relation the same way `student_sem` is — not
`ToyFacts.laugh` directly, which (unlike the `_sem` denotations) carries
no `Decidable` instance of its own; CI caught this the first time this
section was pushed, rather than it being foreseen. -/

/-- John, as a laughing student: `CN' toyFragmentLexicon .student`
paired with `ToyLexicon.laughs_sem`, both real — `johnAsStudent` is
reused, and `laughs_sem john` is `decide`-checked against linglib's own
fact, exactly as `johnAsStudent`'s own witness was. -/
def johnLaughingStudent :
    MTT.Intersective (CN' toyFragmentLexicon .student)
      (fun z => Semantics.Montague.ToyLexicon.laughs_sem z.1) :=
  ⟨johnAsStudent,
    (by decide : Semantics.Montague.ToyLexicon.laughs_sem Semantics.Montague.ToyEntity.john)⟩

/-- "A laughing student" widens to "a laughing person" along the same
`.student ≤ .person` edge `embed_mono` already checked holds for every
entity — via `CN'.intersective_widen` itself, not a hand-rolled
`CN'.widen` call: the general bridge theorem applied to real linglib
content, confirming it is not only ever exercised against
`section5Lexicon`. -/
theorem johnLaughingPerson :
    MTT.Intersective (CN' toyFragmentLexicon .person)
      (fun z => Semantics.Montague.ToyLexicon.laughs_sem z.1) :=
  CN'.intersective_widen toyFragmentLexicon (by decide)
    Semantics.Montague.ToyLexicon.laughs_sem johnLaughingStudent

end MTT.LinglibBridge
