import LeanNLSemantics.MTT.CN
import LeanNLSemantics.MTT.Quantifiers

/-!
# Adjectival modification

Faithful port of `atlas/mtt_ranta/MTT.v` Part 4 (CL20 §3.3 case study),
one block per adjective class, plus this repo's own concrete example
against the `CNTag` model in `CN.lean`.

Caveat flagged in the original scaffolding (still open, not yet needed by
anything ported here): Lean has definitional proof irrelevance for
`Prop`, which Coq's `Prop` does not have in the same form. Anything that
hinges on *which* proof a Σ-type carries (individuation, `DotTypes.lean`)
needs re-checking against this difference rather than assumed to
transfer unchanged.
-/

namespace MTT

/-! ## Intersective adjectives (CL20 §3.3.1) -/

/-- An intersective adjective restricts a CN to those elements satisfying
an extra property: `Intersective (CN .man) Tall` is "tall man"
(`MTT.v`'s `inter_cn`). -/
def Intersective (A : Type) (P : A → Prop) : Type := {x : A // P x}

/-- Forgetting the extra proof recovers the `A` value, which then flows
through `CN`'s own `Coe` chain. Kept as an explicit function rather than a
registered `Coe` instance: `Coe`'s source position is a semi-out-param,
and CI caught what earlier doc comments only warned about in the
abstract — a generic `Coe (Intersective A P) A` instance is rejected
("does not provide concrete values for (semi-)out-params") because `P`
isn't recoverable from the target type alone. Same tradeoff as
`CN.widen`: explicit call, not silent `↑`. -/
def Intersective.forget {A : Type} {P : A → Prop} : Intersective A P → A := Subtype.val

/-- T-ADJ1. Noun drop: "some black man walks" entails "some man walks"
(CL20 §3.3.1: the first projection realises the inference). -/
theorem inter_noun_drop {A : Type} (P Q : A → Prop) :
    Some' (Intersective A P) (fun z => Q z.forget) → Some' A Q :=
  fun ⟨⟨x, _⟩, hq⟩ => ⟨x, hq⟩

/-- T-ADJ2. Adjective extraction: "some black man walks" entails "some
man is black". -/
theorem inter_adj_drop {A : Type} (P Q : A → Prop) :
    Some' (Intersective A P) (fun z => Q z.forget) → Some' A P :=
  fun ⟨⟨x, hx⟩, _⟩ => ⟨x, hx⟩

/-- T-ADJ3. The intersective iff: quantifying over the modified CN is
quantifying over the conjunction — intersectivity *is* this equivalence
(CL20 §3.3.1). -/
theorem intersective_iff {A : Type} (P Q : A → Prop) :
    Some' (Intersective A P) (fun z => Q z.forget) ↔ Some' A (fun x => P x ∧ Q x) := by
  constructor
  · rintro ⟨⟨x, hx⟩, hq⟩
    exact ⟨x, hx, hq⟩
  · rintro ⟨x, hp, hq⟩
    exact ⟨⟨x, hp⟩, hq⟩

/-- T-ADJ4. `Every` over the modified CN is the guarded universal. -/
theorem intersective_every_iff {A : Type} (P Q : A → Prop) :
    Every (Intersective A P) (fun z => Q z.forget) ↔ Every A (fun x => P x → Q x) := by
  constructor
  · intro h x hp
    exact h ⟨x, hp⟩
  · intro h z
    exact h z.forget z.2

axiom Tall : ∀ {A : Type}, A → Prop

/-- "every tall man walks", against this repo's own concrete `CNTag`
model rather than an abstract `A` — the one piece here not from `MTT.v`
itself. -/
example : Prop := Every (Intersective (CN .man) Tall) (fun x => walk x.forget)

/-! ## Subsective adjectives (CL20 §3.3.2) -/

/-- A subsective adjective is a polymorphic, CN-relative predicate:
"skilful" is skilful *as* an `A` — `Adj A x`, not a fixed predicate on
`A` (`MTT.v`'s `subs_cn`). -/
def SubsCN (A : Type) (Adj : (X : Type) → X → Prop) : Type := {x : A // Adj A x}

def SubsCN.forget {A : Type} {Adj : (X : Type) → X → Prop} : SubsCN A Adj → A := Subtype.val

/-- T-ADJ5. Noun drop still holds: a skilful surgeon is a surgeon. -/
theorem subs_noun_drop {A : Type} (Adj : (X : Type) → X → Prop) (Q : A → Prop) :
    Some' (SubsCN A Adj) (fun z => Q z.forget) → Some' A Q :=
  fun ⟨⟨x, _⟩, hq⟩ => ⟨x, hq⟩

/-- T-ADJ6. Subsectivity does NOT transfer along a coercion: there is a
CN-relative predicate, a coercion, and a witness that is `Adj`-as-`A` but
not `Adj`-as-`B` — "a skilful surgeon need not be a skilful man" (CL20
§3.3.2). Countermodel: `Adj X _ := "X has at most one element"`,
`Unit → Bool`. -/
theorem subsective_not_transferable :
    ∃ (Adj : (X : Type) → X → Prop) (A B : Type) (c : A → B) (x : A),
      Adj A x ∧ ¬ Adj B (c x) := by
  refine ⟨fun X _ => ∀ u v : X, u = v, Unit, Bool, fun _ => true, (), ?_, ?_⟩
  · intro u v
    rfl
  · intro h
    exact Bool.noConfusion (h true false)

/-! ## Privative adjectives (CL20 §3.3.3) -/

variable (RGun FGun : Type)

/-- Privative adjectives: the noun is extended to a sum of real and fake
objects — "gun" in the wide sense is the sum (`MTT.v`'s `Gun`). -/
def Gun : Type := RGun ⊕ FGun

def realGun (g : Gun RGun FGun) : Prop := ∃ r : RGun, g = Sum.inl r
def fakeGun (g : Gun RGun FGun) : Prop := ∃ f : FGun, g = Sum.inr f

/-- T-ADJ7. A fake gun is a gun, in the extended sense: typing. -/
theorem fake_is_gun (f : FGun) : fakeGun RGun FGun (Sum.inr f) := ⟨f, rfl⟩

/-- T-ADJ8. A fake gun is provably not a real gun: privativity (CL20
§3.3.3). -/
theorem fake_not_real (f : FGun) : ¬ realGun RGun FGun (Sum.inr f) :=
  fun ⟨_, hr⟩ => Sum.noConfusion hr

/-- T-ADJ9. Every gun is really real or fake, exclusively. -/
theorem gun_partition (g : Gun RGun FGun) :
    (realGun RGun FGun g ∨ fakeGun RGun FGun g) ∧
      ¬ (realGun RGun FGun g ∧ fakeGun RGun FGun g) := by
  cases g with
  | inl r =>
    refine ⟨Or.inl ⟨r, rfl⟩, ?_⟩
    rintro ⟨_, _, hf⟩
    exact Sum.noConfusion hf
  | inr f =>
    refine ⟨Or.inr ⟨f, rfl⟩, ?_⟩
    rintro ⟨⟨_, hr⟩, _⟩
    exact Sum.noConfusion hr

/-! ## Non-committal adjectives (CL20 §3.3.4) -/

/-- T-ADJ10. Non-committal adjectives ("alleged"): opacity is witnessed —
there is a predicate modifier and an instance where the modified holds
and the unmodified fails, so no veridicality theorem is provable (the
*absence* of a theorem is the datum, CL20 §3.3.4). -/
theorem noncommittal_witness :
    ∃ (op : (Nat → Prop) → Nat → Prop) (P : Nat → Prop) (x : Nat),
      op P x ∧ ¬ P x :=
  ⟨fun _ _ => True, fun _ => False, 0, trivial, id⟩

end MTT
