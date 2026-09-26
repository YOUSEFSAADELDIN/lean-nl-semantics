import LeanNLSemantics.MTT.CN

/-!
# Quantifiers

In MTT, a quantifier's domain is a common noun *type*, not a predicate
paired with a domain restriction (contrast Montague's generalized
quantifiers over `E → Prop`). This is the same `(A : Type) → (A → Prop) →
Prop` shape used throughout CoqLACL's `MainCoq.v`.
-/

namespace MTT

def Some' (A : Type) (P : A → Prop) : Prop := ∃ x : A, P x
def Every (A : Type) (P : A → Prop) : Prop := ∀ x : A, P x
def No' (A : Type) (P : A → Prop) : Prop := ∀ x : A, ¬ P x

/-!
**Gotcha (no coercion through function types):** Lean will not turn
`walk : CN .animal → Prop` into `CN .man → Prop` just because `CN .man`
coerces to `CN .animal`. Coercive subtyping propagates contravariantly
through Π-types in MTT; Lean's elaborator does not do this automatically.
The GF→Lean emitter must always eta-expand: write `fun x => walk x`,
never bare `walk`, as the predicate argument to a quantifier — the
coercion is then inserted at the single argument `x`, which the following
example checks.

Do not "fix" this with a generic
`instance [Coe A B] : Coe (B → Prop) (A → Prop)`: unrestricted instances
between function types are a known source of elaboration loops. If the
named-edge `Coe` instances don't cover a needed pair, call `CN.widen (by
decide)` explicitly rather than adding one.
-/
example : Prop := Some' (CN .man) (fun x => walk x)

/-!
## The rest of Part 1 (`atlas/mtt_ranta/MTT.v`, ported)

CNs-as-types and the polymorphic quantifiers, faithfully ported from
`MTT.v` Part 1 (CL20 §3.1 table, §3.2.1 after Luo 2012's "Common nouns as
types"). Credited there, not re-derived here.
-/

/-- The indefinite article "a" (CL20 §3.1) — definitionally `Some'`,
kept as a separate name because the paper does. -/
def aIndef : (A : Type) → (A → Prop) → Prop := Some'

/-- The strong (Σ-type) existential (CL20 §1.4.2, note 26): UTT has
*both* the weak propositional existential `Some'` and this strong Sigma
— comparing only `Some'` against Ranta's Sigma elsewhere is not a
limitation of MTT as a whole. -/
def StrongSome (A : Type) (P : A → Prop) : Type := {x : A // P x}

/-- The general Sigma constructor also permits `Type`-valued fibres;
`StrongSome` is its `Prop`-valued specialisation, not its limit. -/
def StrongPackage (A : Type) (P : A → Type) : Type := Sigma P

def StrongSome.witness {A : Type} {P : A → Prop} (s : StrongSome A P) : A := s.1

theorem strong_some_to_some {A : Type} {P : A → Prop} :
    StrongSome A P → Some' A P := fun ⟨x, hx⟩ => ⟨x, hx⟩

theorem strong_witness_sound {A : Type} {P : A → Prop} (s : StrongSome A P) :
    P s.witness := s.2

end MTT
