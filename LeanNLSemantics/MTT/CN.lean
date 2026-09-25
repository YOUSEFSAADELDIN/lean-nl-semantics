import Mathlib

/-!
# Common nouns as types

Following Chatzikyriakidis & Luo (JoLLI 2014, "Natural Language Inference
in Coq"; LACL 2016), common nouns (CNs) are interpreted as *types*, not as
predicates over a fixed domain of individuals (contrast linglib's
`Semantics.Composition.Ty.et := E → Prop`).

`CoqLACL/MainCoq.v` (read directly from the source repo) declares one
`Parameter` per CN and one hand-written `Axiom … Coercion …` per subtyping
edge — e.g. `Axiom mh : man -> human. Coercion mh : man >-> human.` A
literal Lean transliteration of that (`axiom Man : Type`, a `Coe` instance
per edge) is possible, but leaves two things unchecked: whether `@[coe]`
attaches to an `axiom` on a given toolchain, and whether two coercion
*paths* between the same two CNs agree (Coq warns about ambiguous
coercion paths; Lean does not).

This file instead follows the pattern already proven out in
`hawkrobe/linglib`'s `Studies/Pustejovsky1995.lean` (read directly from
that repo): an `inductive` tag type with an explicit `ancestors` list,
a `PartialOrder` instance derived from it, and `by decide` proofs — all
checkable on a `Fintype`. That gives coherence *for free*: `CNTag.le` is a
`Prop`, Lean has definitional proof irrelevance for `Prop`, so any two
proofs of `a ≤ b` yield the same widening function, definitionally. See
the `rfl`-checked example near the bottom of this file for the concrete
payoff.

(Note: linglib's `Pustejovsky1995.lean` uses the same shape of lattice for
a different purpose — argument-selection coercion on lexicon *entries*,
not quantification over a CN's own elements. It's directly relevant prior
art, not a duplicate; see `CREDITS.md`.)
-/
namespace MTT

/-- The universe of common nouns for this fragment, as a finite tag type.
Extend per grammar fragment; keep `ancestors` a genuine DAG walk (each tag
lists itself first, then everything it subtypes, ending at a shared root)
so the `PartialOrder` laws below hold. -/
inductive CNTag where
  | thing
  | animal
  | human
  | man
  | woman
  deriving DecidableEq, Repr, Fintype

/-- Each tag's ancestors, itself first. Mirrors
`Pustejovsky1995.SemType.ancestors` in shape. -/
def CNTag.ancestors : CNTag → List CNTag
  | .thing => [.thing]
  | .animal => [.animal, .thing]
  | .human => [.human, .animal, .thing]
  | .man => [.man, .human, .animal, .thing]
  | .woman => [.woman, .human, .animal, .thing]

/-- Subtyping: `a ≤ b` when `b` is an ancestor of `a` (`a` is-a `b`). -/
instance : PartialOrder CNTag where
  le a b := b ∈ a.ancestors
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := CNTag) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (b ∈ a.ancestors))

/-- `Man ≤ Human ≤ Animal`, checked, not assumed. -/
example : CNTag.man ≤ .human ∧ CNTag.human ≤ .animal ∧ CNTag.man ≤ .animal := by decide

/-- A minimal concrete individual domain: every individual carries its
*most specific* CN tag. This is a toy model — one individual per
`(kind, name)` pair — good enough to make `CN` computable and to give at
least one `#eval`/`decide`-able sanity check, rather than resting the
whole library on opaque axioms the way `CoqLACL`/a literal port would. -/
structure Individual where
  kind : CNTag
  name : String
  deriving DecidableEq, Repr

/-- The CN `t`, as a type: individuals whose most specific kind is `t` or
below it in the lattice. This is the Lean encoding of Luo's "CNs as
types" — `CN .man` is literally the type "Man", not a predicate on a
fixed domain. -/
def CN (t : CNTag) : Type := {x : Individual // x.kind ≤ t}

/-- Widen a CN element along any subtyping proof. Because `a ≤ b : Prop`
and Lean's `Prop` is definitionally proof-irrelevant, `CN.widen h₁ = CN.widen h₂`
for *any* two proofs `h₁ h₂ : a ≤ b` — composite coercion paths through the
lattice are guaranteed to agree, not just hoped to. -/
def CN.widen {a b : CNTag} (h : a ≤ b) : CN a → CN b :=
  fun x => ⟨x.1, le_trans x.2 h⟩

/-- Named `Coe` instances for the covering edges only, for the same `↑`
ergonomics CoqLACL's `Coercion` declarations gave — each is just
`CN.widen` specialised to one edge, so it cannot disagree with the
general widening function. Declare only covering edges; `CoeTC` chains
the rest. -/
instance : Coe (CN .human) (CN .animal) := ⟨CN.widen (by decide)⟩
instance : Coe (CN .man) (CN .human) := ⟨CN.widen (by decide)⟩
instance : Coe (CN .woman) (CN .human) := ⟨CN.widen (by decide)⟩

/-- A one-place verb, typed at the widest CN it applies to. Still an
uninterpreted symbol (as in CoqLACL) — the CN *type* it quantifies over is
concrete and computable, but predicates on it don't need to be. -/
axiom walk : CN .animal → Prop

def johnI : Individual := ⟨.man, "john"⟩
def john : CN .man := ⟨johnI, by decide⟩

/-- `walk john` elaborates via the registered `Man → Human → Animal`
`Coe` chain (`CoeTC`). Smallest possible regression test for subtyping. -/
example : Prop := walk john

/-- The coherence property the CoqLACL-transliteration approach could only
assert in a comment: two different routes widening `john` from `Man` to
`Thing` (direct, and via `Human`) produce the same value, by `rfl` — not
merely propositionally equal, but definitionally so, because the two
routes' `Prop`-valued proof obligations are irrelevant to the result. -/
example :
    CN.widen (a := .man) (b := .thing) (by decide) john
      = CN.widen (a := .human) (b := .thing) (by decide)
          (CN.widen (a := .man) (b := .human) (by decide) john) := by
  rfl

end MTT
