import LeanNLSemantics.FraCaS.Section1.GQ

/-!
# FraCaS Section 1, problems 46–59

Fourth batch of the Phase 2 harness, continuing `Batch3.lean`. Mostly
new vocabulary/subsections rather than one theme: problem 46 repeats
problem 38's "`No` + scope-weakening refutes an existential" shape;
47/48 are the `AtLeast`/`AtMost` analogues of the `.unknown`/`.yes`
split already seen for `Every` at problems 34 and 44 (new
`atMost_mono_scope` lemma); 49/55/57/59 are a "drop the restrictor to
its known superset" pattern (new `some_restrict` lemma); 50–53 are a
different converse from 34–37's — narrowing *which* group's universal
you're licensed to state, not adding a fact about it; 54 is a genuine
independence case that looks like problem 22 but isn't (the negation is
restricted to a subgroup); 56 is flagged as a genuine divergence between
this project's simplified treatment of "many" and FraCaS's own; 58 is
a real `Most`-cardinality countermodel.
-/

namespace FraCaS.Section1

/-! ## Problem 46: `No` + scope-weakening refutes an existential (same shape as 38) -/

section P046
variable {A : Type*} (commissioner timeAtHome lotOfTime : A → Prop)

theorem fracas_046 :
    No commissioner timeAtHome → (∀ x, lotOfTime x → timeAtHome x) → ¬ Some commissioner lotOfTime :=
  fun hno hmono hsome =>
    (no_iff_not_some commissioner timeAtHome).mp hno (some_mono_scope commissioner lotOfTime timeAtHome hsome hmono)

end P046

/-! ## Problem 47: `AtLeast`, converse of 31's scope-widening — `.unknown` -/

section P047

/-- "At least three commissioners spend time at home" doesn't bound "at
least three spend *a lot of* time" — the general count could be met
entirely by people who don't spend a lot. -/
theorem fracas_047_dir1 :
    AtLeast 3 (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) ∧
      ¬ AtLeast 3 (fun _ : Fin 3 => True) (fun _ : Fin 3 => False) := by
  constructor <;> decide

theorem fracas_047_dir2 :
    AtLeast 3 (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) ∧
      AtLeast 3 (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) := by
  constructor <;> decide

end P047

/-! ## Problem 48: `AtMost` scope-narrowing — genuinely `.yes` -/

section P048
variable {A : Type*} [Fintype A] (commissioner timeAtHome lotOfTime : A → Prop)
variable [DecidablePred fun x => commissioner x ∧ timeAtHome x]
variable [DecidablePred fun x => commissioner x ∧ lotOfTime x]

theorem fracas_048 :
    AtMost 10 commissioner timeAtHome → (∀ x, lotOfTime x → timeAtHome x) →
      AtMost 10 commissioner lotOfTime :=
  atMost_mono_scope 10 commissioner timeAtHome lotOfTime

end P048

/-! ## Problem 49: dropping the restrictor to a known superset -/

section P049
variable {A : Type*} (swede wonNobel scandinavian : A → Prop)

theorem fracas_049 :
    Some swede wonNobel → Every swede scandinavian → Some scandinavian wonNobel :=
  some_restrict swede wonNobel scandinavian

end P049

/-! ## Problems 50–53: narrowing which group's universal you're licensed to state -/

/-! Shared shape for 50–53 (every/all/each/the-residents): "every
Canadian resident can travel; every Canadian resident is a North
American resident" doesn't license "every North American resident can
travel" — Canadian residents being able to travel says nothing about
the other North American residents. Countermodel: two elements, one a
Canadian resident (who travels, per the premise) and one not (who
doesn't) — Booleans standing in for "is exactly the Canadian-resident
element". -/
section P050
theorem fracas_050_dir1 :
    (Every (fun b : Bool => b = true) (fun b : Bool => b = true) ∧
        Every (fun b : Bool => b = true) (fun _ : Bool => True)) ∧
      ¬ Every (fun _ : Bool => True) (fun b : Bool => b = true) := by
  refine ⟨⟨fun _ h => h, fun _ _ => trivial⟩, ?_⟩
  intro h
  exact absurd (h false trivial) (by decide)

theorem fracas_050_dir2 :
    (Every (fun b : Bool => b = true) (fun _ : Bool => True) ∧
        Every (fun b : Bool => b = true) (fun _ : Bool => True)) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨fun _ _ => trivial, fun _ _ => trivial⟩, fun _ _ => trivial⟩
end P050

section P051
theorem fracas_051_dir1 :
    (Every (fun b : Bool => b = true) (fun b : Bool => b = true) ∧
        Every (fun b : Bool => b = true) (fun _ : Bool => True)) ∧
      ¬ Every (fun _ : Bool => True) (fun b : Bool => b = true) := by
  refine ⟨⟨fun _ h => h, fun _ _ => trivial⟩, ?_⟩
  intro h
  exact absurd (h false trivial) (by decide)

theorem fracas_051_dir2 :
    (Every (fun b : Bool => b = true) (fun _ : Bool => True) ∧
        Every (fun b : Bool => b = true) (fun _ : Bool => True)) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨fun _ _ => trivial, fun _ _ => trivial⟩, fun _ _ => trivial⟩
end P051

section P052
theorem fracas_052_dir1 :
    (Every (fun b : Bool => b = true) (fun b : Bool => b = true) ∧
        Every (fun b : Bool => b = true) (fun _ : Bool => True)) ∧
      ¬ Every (fun _ : Bool => True) (fun b : Bool => b = true) := by
  refine ⟨⟨fun _ h => h, fun _ _ => trivial⟩, ?_⟩
  intro h
  exact absurd (h false trivial) (by decide)

theorem fracas_052_dir2 :
    (Every (fun b : Bool => b = true) (fun _ : Bool => True) ∧
        Every (fun b : Bool => b = true) (fun _ : Bool => True)) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨fun _ _ => trivial, fun _ _ => trivial⟩, fun _ _ => trivial⟩
end P052

section P053
theorem fracas_053_dir1 :
    (Every (fun b : Bool => b = true) (fun b : Bool => b = true) ∧
        Every (fun b : Bool => b = true) (fun _ : Bool => True)) ∧
      ¬ Every (fun _ : Bool => True) (fun b : Bool => b = true) := by
  refine ⟨⟨fun _ h => h, fun _ _ => trivial⟩, ?_⟩
  intro h
  exact absurd (h false trivial) (by decide)

theorem fracas_053_dir2 :
    (Every (fun b : Bool => b = true) (fun _ : Bool => True) ∧
        Every (fun b : Bool => b = true) (fun _ : Bool => True)) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨fun _ _ => trivial, fun _ _ => trivial⟩, fun _ _ => trivial⟩
end P053

/-! ## Problem 54: `No`, restricted to a subgroup — `.unknown` -/

section P054

/-- "No Scandinavian delegate finished the report on time" says nothing
about non-Scandinavian delegates — unlike problem 22's "no delegate"
(unrestricted), this doesn't even bound whether *some* delegate finished
on time. Direction 1: nobody at all finishes on time. Direction 2: the
one non-Scandinavian delegate does. -/
theorem fracas_054_dir1 :
    No (fun b : Bool => b = true) (fun _ : Bool => False) ∧
      ¬ Some (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨fun _ _ h => h, ?_⟩
  rintro ⟨_, _, h⟩; exact h

theorem fracas_054_dir2 :
    No (fun b : Bool => b = true) (fun b : Bool => b = false) ∧
      Some (fun _ : Bool => True) (fun b : Bool => b = false) := by
  refine ⟨?_, false, trivial, rfl⟩
  intro b hb
  simp only [hb]
  decide

end P054

/-! ## Problem 55: dropping the restrictor (same shape as 49) -/

section P055
variable {A : Type*} (irishDelegate finishOnTime delegate : A → Prop)

theorem fracas_055 :
    Some irishDelegate finishOnTime → Every irishDelegate delegate → Some delegate finishOnTime :=
  some_restrict irishDelegate finishOnTime delegate

end P055

/-! ## Problem 56: a genuine divergence from FraCaS's own gold answer -/

section P056

/-- FraCaS marks this `.unknown`: "many" is a genuinely *proportional*
determiner (see `GQ.lean`'s `Most` doc comment - this project now models
"many" as `Most`, not `Some`), so "many British delegates got results"
doesn't bound "many delegates got results" - the British could be a
strict majority of a tiny British contingent while being far short of a
majority of the overall delegate population. Direction 1: both British
delegates (of four total delegates) got results - a majority of the
British delegates, but only half of all delegates, not a majority.
Direction 2: everyone got results, so both hold together. Superseded a
`some_restrict`-based proof that treated "many" as a plain, restrictor-
widening-monotone existential like "several"/"a few" (57/59) - genuinely
different for "many" specifically, per FraCaS's own gold answer here. -/
theorem fracas_056_dir1 :
    Most (fun x : Fin 4 => x.val < 2) (fun x : Fin 4 => x.val < 2) ∧
      ¬ Most (fun _ : Fin 4 => True) (fun x : Fin 4 => x.val < 2) := by
  decide

theorem fracas_056_dir2 :
    Most (fun x : Fin 4 => x.val < 2) (fun _ : Fin 4 => True) ∧
      Most (fun _ : Fin 4 => True) (fun _ : Fin 4 => True) := by
  decide

end P056

/-! ## Problem 57: dropping the restrictor (same shape as 49/55) -/

section P057
variable {A : Type*} (portugueseDelegate published delegate : A → Prop)

theorem fracas_057 :
    Some portugueseDelegate published → Every portugueseDelegate delegate →
      Some delegate published :=
  some_restrict portugueseDelegate published delegate

end P057

/-! ## Problem 58: `Most` over a restricted domain doesn't lift to the whole domain -/

section P058

/-- "Most Europeans who are resident in Europe can travel" doesn't give
"most Europeans can travel": five Europeans, only two resident, both of
whom travel (so trivially "most" of the resident sub-population do) —
but whether "most" of *all five* travel is independent of that.
Direction 1: only the two residents travel (majority-of-all fails,
2·2 ≯ 5). Direction 2: everyone travels (majority-of-all holds too). -/
theorem fracas_058_dir1 :
    Most (fun x : Fin 5 => True ∧ x.val < 2) (fun x : Fin 5 => x.val < 2) ∧
      ¬ Most (fun _ : Fin 5 => True) (fun x : Fin 5 => x.val < 2) := by
  constructor <;> decide

theorem fracas_058_dir2 :
    Most (fun x : Fin 5 => True ∧ x.val < 2) (fun _ : Fin 5 => True) ∧
      Most (fun _ : Fin 5 => True) (fun _ : Fin 5 => True) := by
  constructor <;> decide

end P058

/-! ## Problem 59: dropping the restrictor (same shape as 49/55/57) -/

section P059
variable {A : Type*} (femaleCommitteeMember scandinavian committeeMember : A → Prop)

theorem fracas_059 :
    Some femaleCommitteeMember scandinavian → Every femaleCommitteeMember committeeMember →
      Some committeeMember scandinavian :=
  some_restrict femaleCommitteeMember scandinavian committeeMember

end P059

end FraCaS.Section1
