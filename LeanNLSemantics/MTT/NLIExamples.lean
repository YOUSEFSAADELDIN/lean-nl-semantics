import LeanNLSemantics.MTT.Subtyping
import LeanNLSemantics.MTT.Adjectives

/-!
# NLI mini-suite

Faithful port of `atlas/mtt_ranta/MTT.v` Part 8 (CL14; CL20 ch. 6): eight
small entailments in the style of Chatzikyriakidis & Luo's original NLI
work, composing the Part 1-4 machinery (quantifiers, subtyping,
adjectives). Distinct from the real Phase 2 work (the full 346-problem
FraCaS suite, `FraCaS/Data/Problems.lean`) — this is eight worked
examples, not a benchmark, and none of them touch the vendored FraCaS
data.
-/

namespace MTT

section NLI

variable {Man Human : Type} (mh : Man → Human)
variable (walk talk : Human → Prop) (black : Man → Prop)
variable (john : Man)

/-- N1. `every` + an inhabitant gives `some`. -/
theorem nli_every_some :
    Every Man (predLift mh walk) → Some' Man (predLift mh walk) :=
  fun h => ⟨john, h john⟩

/-- N2. `every P` + `some Q` gives `some (P and Q)`. -/
theorem nli_every_and_some :
    Every Human walk → Some' Human talk → Some' Human (fun x => walk x ∧ talk x) :=
  fun he ⟨x, hx⟩ => ⟨x, he x, hx⟩

/-- N3. `no` is the (constructive) negation of `some`, both directions —
generic over any `A`, not actually tied to `Man`/`Human` despite living
in this section (matching `MTT.v`'s own placement). -/
theorem nli_no_iff {A : Type} (P : A → Prop) : No' A P ↔ ¬ Some' A P :=
  ⟨fun h ⟨x, hx⟩ => h x hx, fun h x hx => h ⟨x, hx⟩⟩

/-- N4. Coercion monotonicity instance: "some black man walks" entails
"some human walks" — adjective drop (T-ADJ1) and subtyping monotonicity
(T-SUB2) composed. -/
theorem nli_black_man_walks :
    Some' (Intersective Man black) (fun z => walk (mh z.forget)) → Some' Human walk :=
  fun h => some_mono mh walk (inter_noun_drop black (fun x => walk (mh x)) h)

/-- N5. "John walks and talks" entails "John walks" (conjunction). -/
theorem nli_conj : walk (mh john) ∧ talk (mh john) → walk (mh john) :=
  fun ⟨h, _⟩ => h

/-- N6. Disjunction introduction: "John walks" entails "John walks or
talks". -/
theorem nli_disj : walk (mh john) → walk (mh john) ∨ talk (mh john) :=
  Or.inl

/-- N7. `every Human` gives the instance at a coerced individual. -/
theorem nli_instance : Every Human walk → walk (mh john) :=
  fun h => h (mh john)

/-- N8. `no` and `some` together are absurd (a mini consistency check). -/
theorem nli_no_some_absurd : No' Human walk → Some' Human walk → False :=
  fun hn ⟨x, hx⟩ => hn x hx

end NLI

end MTT
