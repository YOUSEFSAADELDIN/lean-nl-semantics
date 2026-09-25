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
import LeanNLSemantics.MTT.CN
import LeanNLSemantics.MTT.Quantifiers

namespace MTT

/-- An intersective adjective restricts a CN to those elements satisfying
an extra property: `Intersective Man Tall` is "tall man". The forgetful
map back to `A` (`Subtype.val`) is registered as a coercion, so "tall man"
can itself be used wherever a `Man` (or, chained, a `Human` or `Animal`)
is expected. -/
def Intersective (A : Type) (P : A → Prop) : Type := {x : A // P x}

instance {A : Type} {P : A → Prop} : Coe (Intersective A P) A := ⟨Subtype.val⟩

axiom Tall : ∀ {A : Type}, A → Prop

/-- "every tall man walks" -/
example : Prop := Every (Intersective Man Tall) (fun x => walk x)

end MTT
