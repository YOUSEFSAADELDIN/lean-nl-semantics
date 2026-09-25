import LeanNLSemantics.MTT.CN
import LeanNLSemantics.MTT.Quantifiers

/-!
# Adjectival modification

CoqLACL models intersective and subsective adjectives as Σ-types
(dependent record types): "tall man" is the type of pairs of a man and a
proof that he is tall. Lean's `Subtype` is the corresponding structure.

Caveat flagged in the research briefing: Lean has definitional proof
irrelevance for `Prop`, which Coq's `Prop` does not have in the same form.
Anything that hinges on *which* proof a Σ-type carries (identity criteria,
individuation — see `DotTypes.lean`) needs re-checking against this
difference rather than assumed to transfer unchanged from CoqLACL.
-/

namespace MTT

/-- An intersective adjective restricts a CN to those elements satisfying
an extra property: `Intersective (CN .man) Tall` is "tall man". -/
def Intersective (A : Type) (P : A → Prop) : Type := {x : A // P x}

/-- Forgetting the extra proof recovers the `A` value, which then flows
through `CN`'s own `Coe` chain. Kept as an explicit function rather than a
registered `Coe` instance: `Coe`'s source position is a semi-out-param,
and CI caught what the doc comments elsewhere only warned about in the
abstract — a generic `Coe (Intersective A P) A` instance is rejected
("does not provide concrete values for (semi-)out-params") because `P`
isn't recoverable from the target type alone. Same tradeoff as
`CN.widen`: explicit call, not silent `↑`. -/
def Intersective.forget {A : Type} {P : A → Prop} : Intersective A P → A := Subtype.val

axiom Tall : ∀ {A : Type}, A → Prop

/-- "every tall man walks" -/
example : Prop := Every (Intersective (CN .man) Tall) (fun x => walk x.forget)

end MTT
