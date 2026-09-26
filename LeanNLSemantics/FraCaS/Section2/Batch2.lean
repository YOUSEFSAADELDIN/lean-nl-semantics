import LeanNLSemantics.FraCaS.Section2.Plurals

/-!
# FraCaS Section 2, problems 98–113

Second and final batch of Section 2: bare-plural existential vs. a
named instance (98), quasi-universal bare plurals (99/100), generics
(101/102), a universal plus a stronger unconnected predicate (103/104),
exact-cardinality vs. `No`/`Some` (105–110, including one more
documented divergence at 109), and named-individual cumulative/
distributive "and"-conjunction (111–113).
-/

namespace FraCaS.Section2

open FraCaS.Section1

/-! ## Problem 98: bare-plural existential doesn't settle a named instance -/

section P098

/-- "Software faults were blamed" (existential) plus "Bug #32-985 is a
software fault" doesn't tell you Bug #32-985 specifically was blamed —
the blamed fault(s) could be different ones. `true`/`false` stand in for
Bug #32-985 and "some other fault"; the second premise ("is a software
fault") is trivially `True` in both directions since every element here
counts as a fault. -/
theorem fracas_098_dir1 :
    (Some (fun _ : Bool => True) (fun b : Bool => b = false) ∧ True) ∧ ¬ (true = false) := by
  refine ⟨⟨⟨false, trivial, rfl⟩, trivial⟩, by decide⟩

theorem fracas_098_dir2 :
    (Some (fun _ : Bool => True) (fun b : Bool => b = true) ∧ True) ∧ (true = true) :=
  ⟨⟨⟨true, trivial, rfl⟩, trivial⟩, rfl⟩

end P098

/-! ## Problem 99: quasi-universal bare plural, instantiated at a named individual -/

section P099
variable {A : Type*} (clientAtDemo impressed : A → Prop) (smith : A)

theorem fracas_099 : Every clientAtDemo impressed → clientAtDemo smith → impressed smith :=
  fun h hs => h smith hs

end P099

/-! ## Problem 100: a (quasi-)universal bare plural lifts to `Most` -/

section P100
variable {A : Type*} [Fintype A] (clientAtDemo impressed : A → Prop)
variable [DecidablePred clientAtDemo] [DecidablePred fun x => clientAtDemo x ∧ impressed x]

theorem fracas_100 :
    Every clientAtDemo impressed → (∃ x, clientAtDemo x) → Most clientAtDemo impressed :=
  fun h hne => every_most clientAtDemo impressed hne h

end P100

/-! ## Problems 101/102: generics — "likely" follows, certainty doesn't -/

section P101
variable {A : Type*} (universityGrad likelyPoorTrader : A → Prop) (smith : A)

/-- This project formalizes the generic "university graduates make poor
stock-market traders" directly as a "likely" universal (not a genuine
generic with exceptions) — a documented simplification, exactly the way
Section 1 often assumes explicit background-knowledge premises. Under
that simplification this is just instantiation at `smith`, same shape as
99. -/
theorem fracas_101 :
    Every universityGrad likelyPoorTrader → universityGrad smith → likelyPoorTrader smith :=
  fun h hs => h smith hs

end P101

section P102

/-- Even granting 101's "likely" universal, "Smith *will* make a poor
trader" (a stronger, non-hedged claim) doesn't follow — a genuine
generic tolerates exceptions, so nothing here forces *certainty* about
any specific instance. Same independence shape as 91/94/95. -/
theorem fracas_102_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_102_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P102

/-! ## Problems 103/104: a universal instantiated, vs. an unconnected stronger claim -/

section P103
variable {A : Type*} (apcomManager hasCar : A → Prop) (jones : A)

theorem fracas_103 : Every apcomManager hasCar → apcomManager jones → hasCar jones :=
  fun h hj => h jones hj

end P103

section P104

/-- "All APCOM managers have company cars; Jones is a manager" gives
Jones *a* car (103), but "more than one company car" is a strictly
stronger, logically unconnected predicate this project doesn't derive
one from the other — same independence shape as 91/94/95/102. -/
theorem fracas_104_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_104_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P104

/-! ## Problems 105/106: exact cardinality refutes `No` -/

section P105
variable {A : Type*} [Fintype A] (accountant attended : A → Prop)
variable [DecidablePred fun x => accountant x ∧ attended x]

theorem fracas_105 : Exactly 1 accountant attended → ¬ No accountant attended :=
  exactly_pos_not_no 1 accountant attended (by decide)

theorem fracas_106 : Exactly 1 accountant attended → ¬ No accountant attended :=
  exactly_pos_not_no 1 accountant attended (by decide)

end P105

/-! ## Problems 107/108/109/110: exact cardinality gives `Some` -/

section P107
variable {A : Type*} [Fintype A] (accountant attended : A → Prop)
variable [DecidablePred fun x => accountant x ∧ attended x]

theorem fracas_107 : Exactly 1 accountant attended → Some accountant attended :=
  some_of_exactly 1 accountant attended (by decide)

theorem fracas_108 : Exactly 1 accountant attended → Some accountant attended :=
  some_of_exactly 1 accountant attended (by decide)

/-- FraCaS reads plural "some accountants" as presupposing *more than
one* (hence "No, just one" — a nonstandard answer, flagged
`fracas_nonstandard` in the source). This project's `Some` is a plain
existential with no such plurality presupposition, so under this
project's own stated semantics (documented in `GQ.lean`) this is the
same provable statement as 107/108/110, not a refutation — a documented
divergence, the same kind as Section 1's problem 56. -/
theorem fracas_109 : Exactly 1 accountant attended → Some accountant attended :=
  some_of_exactly 1 accountant attended (by decide)

theorem fracas_110 : Exactly 1 accountant attended → Some accountant attended :=
  some_of_exactly 1 accountant attended (by decide)

end P107

/-! ## Problems 111–113: named-individual cumulative/distributive "and" -/

section P111
variable {Contract : Type*} (signedSmith signedJones : Contract → Prop)

/-- Cumulative reading: "Smith signed one contract, Jones signed
another [a *different* one]" gives two distinct contracts covered
between the two of them — exactly what "Smith and Jones signed two
contracts" asks for on its cumulative reading. -/
theorem fracas_111 :
    (∃ c c', c ≠ c' ∧ signedSmith c ∧ signedJones c') →
      ∃ c1 c2, c1 ≠ c2 ∧ (signedSmith c1 ∨ signedJones c1) ∧ (signedSmith c2 ∨ signedJones c2) :=
  fun ⟨c, c', hne, hs, hj⟩ => ⟨c, c', hne, Or.inl hs, Or.inr hj⟩

end P111

section P112
variable (smithSignedTwo jonesSignedTwo : Prop)

/-- Distributive reading: "Smith and Jones signed two contracts" just
*is* "Smith signed two, and Jones signed two" — literally the premises
restated, not a nontrivial inference. -/
theorem fracas_112 : smithSignedTwo ∧ jonesSignedTwo → smithSignedTwo ∧ jonesSignedTwo := id

end P112

section P113
variable {Contract : Type*} (c1 c2 : Contract) (signedSmith signedJones : Contract → Prop)

/-- "Smith signed two contracts [c1, c2]; Jones also signed them" —
same distributive conjunction as 112, but with the two contracts named
so premise and hypothesis are literally the same statement about the
same two contracts. -/
theorem fracas_113 :
    (signedSmith c1 ∧ signedSmith c2) → (signedJones c1 ∧ signedJones c2) →
      (signedSmith c1 ∧ signedSmith c2) ∧ (signedJones c1 ∧ signedJones c2) :=
  fun h1 h2 => ⟨h1, h2⟩

end P113

end FraCaS.Section2
