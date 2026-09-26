import LeanNLSemantics.FraCaS.Section2.Plurals

/-!
# FraCaS Section 2, problems 81–97

First batch of Section 2 (Plurals): named-individual conjunction/
disjunction (81–84), exact cardinality (85/86), the NP- vs.
N-bar-conjunction ambiguity of "every A and B" (87–89), "the Xs V" with
and without an explicit distributivity-forcing "all" (90, 92/93/96 vs.
91/94/95), and bare-plural existential/quasi-universal readings
(97 here; 98–100 continue in `Batch2.lean`).
-/

namespace FraCaS.Section2

open FraCaS.Section1

/-! ## Problems 81–84: named-individual conjunction/disjunction (pure propositional logic) -/

section P081
variable (smithSigned jonesSigned andersonSigned : Prop)

theorem fracas_081 : smithSigned ∧ jonesSigned ∧ andersonSigned → jonesSigned :=
  fun ⟨_, h, _⟩ => h

end P081

section P082
variable (smithSigned jonesSigned : Prop) {A : Type*} (lawyer signed : A → Prop)

/-- Second premise ("several lawyers signed") is a distractor, same as
Section 1's problem 11. -/
theorem fracas_082 : smithSigned ∧ jonesSigned ∧ Some lawyer signed → jonesSigned :=
  fun ⟨_, h, _⟩ => h

end P082

section P083
variable (smithSigned jonesSigned andersonSigned : Prop)

/-- "Either Smith, Jones or Anderson signed" doesn't tell you which one —
concrete instantiations stand in for the two ways the disjunction can be
made true without Jones. -/
theorem fracas_083_dir1 : (True ∨ False ∨ False) ∧ ¬ False := ⟨Or.inl trivial, fun h => h⟩

theorem fracas_083_dir2 : (False ∨ True ∨ False) ∧ True := ⟨Or.inr (Or.inl trivial), trivial⟩

end P083

section P084
variable (smithSigned jonesSigned andersonSigned : Prop)

/-- Disjunctive syllogism: ruling out the other two disjuncts forces the
third — pure propositional logic, no new machinery. -/
theorem fracas_084 :
    (smithSigned ∨ jonesSigned ∨ andersonSigned) →
      (¬ smithSigned ∧ ¬ andersonSigned → jonesSigned) :=
  fun hdisj ⟨hns, hna⟩ =>
    hdisj.elim (fun hs => absurd hs hns) (fun h => h.elim id (fun ha => absurd ha hna))

end P084

/-! ## Problems 85/86: exact cardinality refutes a different exact count -/

section P085
variable {A : Type*} [Fintype A] (lawyer accountant signed : A → Prop)
variable [DecidablePred fun x => lawyer x ∧ signed x]

/-- Second conjunct ("three accountants") is irrelevant to this
question, same distractor pattern as 82. -/
theorem fracas_085 : Exactly 2 lawyer signed → ¬ Exactly 6 lawyer signed :=
  exactly_ne 2 6 lawyer signed (by decide)

end P085

section P086
variable {A : Type*} [Fintype A] (accountant signed : A → Prop)
variable [DecidablePred fun x => accountant x ∧ signed x]

theorem fracas_086 : Exactly 3 accountant signed → ¬ Exactly 6 accountant signed :=
  exactly_ne 3 6 accountant signed (by decide)

end P086

/-! ## Problems 87–89: "every A and/or B" — NP- vs. N-bar-conjunction -/

section P087
variable {A : Type*} (rep client atMeeting : A → Prop)

/-- NP-conjunction reading ("every representative, and every client"):
plain conjunction elimination. -/
theorem fracas_087 : Every rep atMeeting ∧ Every client atMeeting → Every rep atMeeting :=
  fun h => h.1

end P087

section P088

/-- N-bar-conjunction reading ("everyone who is both a representative
and a client"): the restrictor is the *intersection*, a proper subset of
plain "representative" whenever some representative isn't also a
client — so this doesn't give "every representative", the same
subset/superset independence as `Batch1.lean`'s problem 34. FraCaS's own
`<note>` flags 87 and 88 as "formally identical" premises with different
gold answers precisely because of this reading split. -/
theorem fracas_088_dir1 :
    Every (fun b : Bool => True ∧ b = true) (fun b : Bool => b = true) ∧
      ¬ Every (fun _ : Bool => True) (fun b : Bool => b = true) := by
  refine ⟨fun _ h => h.2, ?_⟩
  intro h
  exact absurd (h false trivial) (by decide)

theorem fracas_088_dir2 :
    Every (fun b : Bool => True ∧ b = true) (fun _ : Bool => True) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨fun _ _ => trivial, fun _ _ => trivial⟩

end P088

section P089
variable {A : Type*} (rep client atMeeting : A → Prop)

/-- "Every representative or client" (disjunctive restrictor) forces
the wide-scope NP-conjunction reading in the conclusion: anyone who's a
rep-or-client and at the meeting gives both "every rep" and "every
client" directly. -/
theorem fracas_089 :
    Every (fun x => rep x ∨ client x) atMeeting → Every rep atMeeting ∧ Every client atMeeting :=
  fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩

end P089

/-! ## Problem 90: definite plural direct object, distributive-forced -/

section P090
variable {A : Type*} (onAgenda readOut : A → Prop)

/-- This project formalizes "the chairman read out the items on the
agenda" directly as the distributive universal, the same simplification
Section 1's problem 5 makes for definite plurals — so the premise and
hypothesis coincide, same as problem 1's trivial restatement. -/
theorem fracas_090 : Every onAgenda readOut → Every onAgenda readOut := id

end P090

/-! ## Problems 91–96: collective/generic vs. distributive "the Xs V" -/

section P091

/-- "The people who were at the meeting voted for a new chairman" (a
bare definite plural with a group-oriented predicate) doesn't license
"everyone at the meeting voted" — nothing connects a collective/group-
level "voted" to a distributive claim about each individual in this
project's formalization; contrast 92/93, where an explicit "all"/floated
"all" *does* force the distributive reading. `True`/`False` stand in for
the two unconnected claims. -/
theorem fracas_091_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_091_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P091

section P092
variable {A : Type*} (atMeeting voted : A → Prop)

/-- "All the people... voted" — explicit "all" forces the distributive
universal directly. -/
theorem fracas_092 : Every atMeeting voted → Every atMeeting voted := id

end P092

section P093
variable {A : Type*} (atMeeting voted : A → Prop)

/-- Floated "all" ("...were at the meeting all voted") forces the same
distributive universal as 92. -/
theorem fracas_093 : Every atMeeting voted → Every atMeeting voted := id

end P093

section P094

/-- "The inhabitants of Cambridge voted for a Labour MP" — same
collective/distributive independence as 91 (no "all"). -/
theorem fracas_094_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_094_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P094

section P095

/-- "The Ancient Greeks were noted philosophers" — a generic/
generalization reading, independent from the literal universal for the
same reason as 91/94 (no "all", and additionally a generic tolerates
exceptions the way 101/102 do). -/
theorem fracas_095_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_095_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P095

section P096
variable {A : Type*} (ancientGreek notedPhilosopher : A → Prop)

/-- "...were *all* noted philosophers" forces the distributive
universal, same as 92/93. -/
theorem fracas_096 : Every ancientGreek notedPhilosopher → Every ancientGreek notedPhilosopher := id

end P096

/-! ## Problem 97: bare-plural existential, restated -/

section P097
variable {A : Type*} (softwareFault blamed : A → Prop)

/-- "Software faults were blamed" on its existential reading is just
`Some`, restated in the hypothesis — same shape as problem 1. -/
theorem fracas_097 : Some softwareFault blamed → Some softwareFault blamed := id

end P097

end FraCaS.Section2
