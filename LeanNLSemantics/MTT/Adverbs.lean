import LeanNLSemantics.MTT.Quantifiers

/-!
# Veridical adverbs

Faithful port of `atlas/mtt_ranta/MTT.v` Part 5 (CL20 §4.5.1–4.5.2).
Manner adverbs are predicate modifiers packaged with their veridicality
proof — a Σ-type over the modifier space, so "walks quickly" entailing
"walks" is a projection, not a separate axiom per adverb.
-/

namespace MTT

/-- A veridical adverb over `A`: a predicate modifier together with a
proof it never introduces truth the base predicate lacked. -/
def VAdv (A : Type) : Type :=
  {op : (A → Prop) → A → Prop // ∀ P x, op P x → P x}

/-- T-ADV1. Veridicality: "John walks quickly" entails "John walks" — by
the packaged proof (CL20 §4.5.1). -/
theorem adv_veridical {A : Type} (walk : A → Prop) (adv : VAdv A) (x : A) :
    adv.1 walk x → walk x := adv.2 walk x

/-- T-ADV2. The space is inhabited: the intersective manner reading of
"quickly" := doing it while being quick (CL20 §4.5.2). -/
def quickly {A : Type} (quick : A → Prop) : VAdv A :=
  ⟨fun P x => P x ∧ quick x, fun _ _ ⟨hp, _⟩ => hp⟩

theorem quickly_veridical {A : Type} (walk quick : A → Prop) (x : A) :
    (quickly quick).1 walk x → walk x :=
  adv_veridical walk (quickly quick) x

/-- T-ADV3. Quantified veridicality: "some A walks quickly" entails
"some A walks" (used in the NLI suite, MTT.v Part 8). -/
theorem adv_some {A : Type} (walk : A → Prop) (adv : VAdv A) :
    Some' A (adv.1 walk) → Some' A walk :=
  fun ⟨x, hx⟩ => ⟨x, adv.2 walk x hx⟩

end MTT
