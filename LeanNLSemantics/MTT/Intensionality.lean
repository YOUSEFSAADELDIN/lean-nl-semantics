import Mathlib

/-!
# What a noun meaning must be for FraCaS 215 to come out "unknown"

FraCaS 214 and 215 share their premises — "All legal authorities are law
lecturers. All law lecturers are legal authorities." — and differ only in
the adjective of the hypothesis:

- 214: "All **fat** legal authorities are fat law lecturers." Gold: yes.
- 215: "All **competent** legal authorities are competent law lecturers."
  Gold: unknown.

Competence is judged relative to the noun ("competent *as* a legal
authority"), so two nouns with the same members can still differ. The
hand-written corpus (`FraCaS/Section5/Batch2.lean`) says exactly this in
its docstrings, but encodes 215 as two opaque propositions
(`competentAsLegalAuth`, `competentAsLawLect : Prop`) rather than composing
"competent" with a noun meaning. This file asks which kinds of noun meaning
let "competent N" be composed *and* leave 215 open, and proves the answer
for five candidates:

1. **Nouns as extensional predicates** (`E → Prop`, the corpus's and
   linglib's `Ty.et`): any adjective `(E → Prop) → (E → Prop)` forces 215 to
   "yes" (`extensional_forces_215`). Coextensive predicates are equal
   (`funext`, `propext`), so the adjective cannot tell them apart.
2. **Nouns as subtypes of one domain** (`{x // P x}`): coextensive nouns
   are then *equal types*, so any type-indexed adjective, MTT-style
   `(X : Type) → X → Prop` (`Adjectives.lean`'s `SubsCN`), is forced to
   "yes" as well (`subtype_forces_215`).
3. **Nouns as tags in a partial order** (`CN.lean`'s `CNTag`, which this
   repo's MTT core uses): "all A are B" and "all B are A" make the tags
   mutually subtyped, hence *equal* by antisymmetry, so again "yes"
   (`partialOrder_forces_215`). The repo's own MTT model does not get 215.
4. **Nouns as codes in a universe, with subtyping a preorder** (MTT proper:
   Luo's CN universe with coercive subtyping, which is a preorder, not a
   partial order): there is a model where the two nouns have literally the
   same carrier and identity coercions both ways, yet "competent" differs
   on them, so 215 stays open (`code_leaves_215_open`), while 214's "fat",
   a predicate on the carrier, still follows (`code_214_yes`).
5. **Nouns as intensions** (Montague with possible worlds, `W → E → Prop`):
   coextensive at the actual world need not mean coextensive at every
   world, so 215 also stays open (`worlds_leave_215_open`).

So MTT's edge here is real but precise: over *extensional* predicates
(1–3), noun meanings that are codes rather than extensions (4) get 215
compositionally, which extensional predicates provably cannot. It is not an
edge over intensional Montague semantics (5), which gets the same verdict
with possible worlds instead of a universe of codes; and it needs a
preorder of coercions, not the partial order this repo's `CNTag` uses.

A sixth case qualifies 1, and it is the one a published system uses.
`extensional_forces_215` depends on two extensionality principles:
propositional extensionality (`propext`, an axiom in Lean) and function
extensionality (`funext`, a theorem in Lean via `Quot.sound`). Coq assumes
neither by default, so there a predicate `object → Prop` is *not*
determined by its extension, and an adjective `(object → Prop) → (object →
Prop)` can tell coextensive nouns apart. FraCoq (Bernardy &
Chatzikyriakidis, IWCS 2017) relies on this: it keeps nouns as predicates
(`CN := object → Prop`) and gets 214 by declaring "fat" an
`ExtensionalSubsectiveA`, an adjective that comes with an explicit proof
that it respects coextensive nouns, while an undeclared adjective such as
"competent" stays free to differ. So the precise statement is: noun
meanings must be finer than extensions, and either codes (4), worlds (5),
or an intensional metatheory without these two principles (FraCoq's Coq)
provides that; extensional predicates in a metatheory with them (1–3, and
Lean as used here) do not. The same paper leaves "common nouns as types"
versus predicates as an open comparison ("we hope that results will shed
light on the theoretical advantages of the two approaches").
-/

namespace MTT.Intensionality

/-! ## 1. Nouns as extensional predicates -/

/-- Whatever an adjective does to a noun predicate, coextensive nouns give
coextensive results: 215's hypothesis follows from its premises for every
adjective meaning `(E → Prop) → (E → Prop)`. -/
theorem extensional_forces_215 {E : Type*} (adj : (E → Prop) → (E → Prop))
    (legalAuthority lawLecturer : E → Prop)
    (h₁ : ∀ x, legalAuthority x → lawLecturer x) (h₂ : ∀ x, lawLecturer x → legalAuthority x) :
    ∀ x, adj legalAuthority x → adj lawLecturer x := by
  have h : legalAuthority = lawLecturer := funext fun x => propext ⟨h₁ x, h₂ x⟩
  subst h
  exact fun _ hx => hx

/-! ## 2. Nouns as subtypes of one domain -/

/-- With nouns as subtypes `{x // P x}` of one domain, coextensive nouns are
equal types, so an adjective indexed by the noun's type cannot tell them
apart either: the coercion from legal authorities to law lecturers preserves
every type-indexed adjective. -/
theorem subtype_forces_215 {E : Type} (adj : (X : Type) → X → Prop)
    (legalAuthority lawLecturer : E → Prop)
    (h₁ : ∀ x, legalAuthority x → lawLecturer x) (h₂ : ∀ x, lawLecturer x → legalAuthority x) :
    ∀ y : {x // legalAuthority x},
      adj {x // legalAuthority x} y → adj {x // lawLecturer x} ⟨y.1, h₁ y.1 y.2⟩ := by
  have h : legalAuthority = lawLecturer := funext fun x => propext ⟨h₁ x, h₂ x⟩
  subst h
  intro y hy
  have hy' : (⟨y.1, h₁ y.1 y.2⟩ : {x // legalAuthority x}) = y := Subtype.ext rfl
  rw [hy']
  exact hy

/-! ## 3. Nouns as tags in a partial order -/

/-- If "all A are B" and "all B are A" are subtyping edges in a partial
order of noun tags (as `CN.lean`'s `CNTag` is), the two tags are equal, so
any tag-indexed adjective transfers. -/
theorem partialOrder_forces_215 {T E : Type*} [PartialOrder T] (adj : T → E → Prop)
    (legalAuthority lawLecturer : T)
    (h₁ : legalAuthority ≤ lawLecturer) (h₂ : lawLecturer ≤ legalAuthority) :
    ∀ x, adj legalAuthority x → adj lawLecturer x := by
  have h : legalAuthority = lawLecturer := le_antisymm h₁ h₂
  subst h
  exact fun _ hx => hx

/-! ## 4. Nouns as codes, with subtyping a preorder -/

/-- Codes for the two nouns of 214/215. -/
inductive Noun where
  | legalAuthority
  | lawLecturer
  deriving DecidableEq

/-- Both nouns denote the *same* carrier: every legal authority is a law
lecturer and vice versa in the strongest possible sense. -/
abbrev El : Noun → Type := fun _ => ℕ

/-- The subtyping coercions in both directions: the identity. -/
def up : El .legalAuthority → El .lawLecturer := fun x => x
def down : El .lawLecturer → El .legalAuthority := fun x => x

/-- The coercions are mutually inverse: the two nouns are coextensive. -/
theorem up_down (y : El .lawLecturer) : up (down y) = y := rfl
theorem down_up (x : El .legalAuthority) : down (up x) = x := rfl

/-- 215 stays open: an adjective indexed by the noun's code ("competent as
an N") can hold of someone as a legal authority and fail of the same
individual, coerced, as a law lecturer. -/
theorem code_leaves_215_open :
    ∃ (adj : (n : Noun) → El n → Prop) (x : El .legalAuthority),
      adj .legalAuthority x ∧ ¬ adj .lawLecturer (up x) :=
  ⟨fun n _ => n = .legalAuthority, 0, rfl, fun h => Noun.noConfusion h⟩

/-- 214 still follows: "fat" is a predicate of the individual, not of the
noun, so it is preserved by the coercion. -/
theorem code_214_yes (fat : ℕ → Prop) :
    ∀ x : El .legalAuthority, fat x → fat (up x) :=
  fun _ hx => hx

/-! ## 5. Nouns as intensions (Montague with possible worlds) -/

/-- The premises hold at the actual world `w₀` only; "competent" may look
at the noun's intension elsewhere, so 215 stays open here too. -/
theorem worlds_leave_215_open :
    ∃ (W E : Type) (w₀ : W) (adj : (W → E → Prop) → (W → E → Prop))
      (legalAuthority lawLecturer : W → E → Prop),
      (∀ x, legalAuthority w₀ x → lawLecturer w₀ x) ∧
      (∀ x, lawLecturer w₀ x → legalAuthority w₀ x) ∧
      ∃ x, adj legalAuthority w₀ x ∧ ¬ adj lawLecturer w₀ x :=
  ⟨Bool, Unit, true, fun P _ x => P false x, fun _ _ => True, fun w _ => w = true,
    fun _ _ => rfl, fun _ _ => trivial, (), trivial, fun h => Bool.false_ne_true h⟩

end MTT.Intensionality
