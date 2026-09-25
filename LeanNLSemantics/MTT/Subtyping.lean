import LeanNLSemantics.MTT.Quantifiers

/-!
# Subtyping as explicit coercions

Faithful port of `atlas/mtt_ranta/MTT.v` Part 2 (Chatzikyriakidis & Luo
2020 §2.4, §3.2.2), generic over any lifting function `c : A → B` between
CNs — not tied to this repo's `CNTag` lattice. `CN.widen h : CN a → CN b`
(`CN.lean`) is one instance of such a `c`; these theorems apply to it
directly, and to any future model (e.g. `LinglibBridge`) without change.
-/

namespace MTT

variable {A B C : Type} (c : A → B) (d : B → C)

/-- Composition of coercions is composition of liftings. -/
def subComp : A → C := fun x => d (c x)

/-- Contravariant lifting on predicate spaces: if `A ≤ B` then
`(B → Prop) ≤ (A → Prop)`. -/
def predLift (P : B → Prop) : A → Prop := fun x => P (c x)

/-- T-SUB1. `every` is anti-monotone along a coercion: "every human
walks" entails "every man walks" (CL20 §3.2.2). -/
theorem every_anti (P : B → Prop) : Every B P → Every A (predLift c P) :=
  fun h x => h (c x)

/-- T-SUB2. `some` is monotone: "some man walks" entails "some human
walks" (CL20 §3.2.2). -/
theorem some_mono (P : B → Prop) : Some' A (predLift c P) → Some' B P :=
  fun ⟨x, hx⟩ => ⟨c x, hx⟩

/-- T-SUB3. `no` is anti-monotone: "no human walks" entails "no man
walks". -/
theorem no_anti (P : B → Prop) : No' B P → No' A (predLift c P) :=
  fun h x hx => h (c x) hx

/-- T-SUB4. Lifting respects composition definitionally. -/
theorem predLift_comp (P : C → Prop) (x : A) :
    predLift c (fun y => P (d y)) x = P (subComp c d x) := rfl

end MTT
