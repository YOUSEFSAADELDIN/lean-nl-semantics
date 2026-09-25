/-!
# Quantifiers

In MTT, a quantifier's domain is a common noun *type*, not a predicate
paired with a domain restriction (contrast Montague's generalized
quantifiers over `E → Prop`). This is the same `(A : Type) → (A → Prop) →
Prop` shape used throughout CoqLACL's `MainCoq.v`.
-/
import LeanNLSemantics.MTT.CN

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

end MTT
