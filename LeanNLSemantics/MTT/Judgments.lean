/-!
# Judgmental interpretations and propositional forms

Faithful port of `atlas/mtt_ranta/MTT.v` Part 3 (CL20 §3.2.3, §7.1). The
judgmental interpretation of "John is a man" is the judgment `john : Man`
itself; its *propositional form* at a supertype `B` is "some `A` maps to
`b`". Generic over any coercions `c : A → B`, `d : B → C` — no import of
`CN.lean` needed.
-/

namespace MTT

variable {A B C : Type} (c : A → B) (d : B → C)

/-- The propositional form of a judgment at the supertype `B`: "`b` is
(the image of) an `A`" (CL20 §3.2.3, §7.1). -/
def inProp (b : B) : Prop := ∃ a : A, c a = b

/-- T-JP1. A judgment entails its propositional form: from `a : A` we get
the proposition "`c a` is an `A`" (CL20 §3.2.3). -/
theorem judgment_to_prop (a : A) : inProp c (c a) := ⟨a, rfl⟩

/-- T-JP2. Propositional forms compose along coercions (CL20 §7.1). -/
theorem in_prop_compose (b : B) (h : inProp c b) :
    ∃ a : A, d (c a) = d b := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, congrArg d ha⟩

end MTT
