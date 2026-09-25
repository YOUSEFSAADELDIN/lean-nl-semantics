import LeanNLSemantics.FraCaS.Section1.GQ

/-!
# FraCaS Section 1, problems 22–31 (the "delegate"/"commissioner" subsection)

Second batch of the Phase 2 harness, continuing `Batch1.lean`. This
subsection is specifically about **adjunct dropping**: "finished the
report *on time*" vs. "finished the report". FraCaS's own `<why>` notes
say it plainly — dropping an adjunct is a valid inference in a positive
context (problems 23–25) but not in a negative one (problems 22, 30),
where it's genuinely undecidable, not false. Problems 26–29/31 are
`Batch1.lean`'s Most/Some/Every/AtLeast composition shapes recurring
with three-premise chains.
-/

namespace FraCaS.Section1

/-! ## Problem 22: adjunct-dropping fails in a negative context (`.unknown`) -/

section P022

/-- "No delegate finished the report on time" doesn't settle "no
delegate finished the report" either way: direction 1, a delegate
finishes late (premise true, hypothesis false); direction 2, no delegate
finishes at all (premise true, hypothesis true). Two predicates
(`finishOnTime`, `finish`) over one domain, exactly as the `<why>` note
says — "on time" can't be dropped under negation. -/
theorem fracas_022_dir1 :
    No (fun _ : Bool => True) (fun _ : Bool => False) ∧
      ¬ No (fun _ : Bool => True) (fun _ : Bool => True) := by
  refine ⟨fun _ _ h => h, ?_⟩
  intro h
  exact h true trivial trivial

theorem fracas_022_dir2 :
    No (fun _ : Bool => True) (fun _ : Bool => False) ∧
      No (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨fun _ _ h => h, fun _ _ h => h⟩

end P022

/-! ## Problems 23–25: adjunct-dropping is fine in a positive context -/

section P023
variable {A : Type*} (delegate finishOnTime finish : A → Prop)

theorem fracas_023 :
    Some delegate finishOnTime → (∀ x, finishOnTime x → finish x) → Some delegate finish :=
  some_mono_scope delegate finishOnTime finish

end P023

section P024
variable {A : Type*} (delegate interestingResult result : A → Prop)

theorem fracas_024 :
    Some delegate interestingResult → (∀ x, interestingResult x → result x) →
      Some delegate result :=
  some_mono_scope delegate interestingResult result

end P024

section P025
variable {A : Type*} (delegate publishedInNewspapers published : A → Prop)

theorem fracas_025 :
    Some delegate publishedInNewspapers → (∀ x, publishedInNewspapers x → published x) →
      Some delegate published :=
  some_mono_scope delegate publishedInNewspapers published

end P025

/-! ## Problem 26: `most` chained through two universals -/

section P026
variable {A : Type*} [Fintype A]
variable (european resident person travel : A → Prop)
variable [DecidablePred european] [DecidablePred fun x => european x ∧ resident x]
variable [DecidablePred fun x => european x ∧ travel x]

theorem fracas_026 :
    Most european resident → Every european person →
      Every (fun x => person x ∧ resident x) travel →
        Most european travel :=
  most_trans european resident person travel

end P026

/-! ## Problem 27: `Some` chained through two universals -/

section P027
variable {A : Type*} (committee swedish person scandinavian : A → Prop)

theorem fracas_027 :
    Some committee swedish → Every committee person →
      Every (fun x => person x ∧ swedish x) scandinavian →
        Some committee scandinavian :=
  some_trans committee swedish person scandinavian

end P027

/-! ## Problem 28: "few", chained — `.undef`/`.unknown`, independent both ways -/

section P028

/-- "Few committee members are from Portugal" (formalized, as in problem
12, as a small upper bound) plus two universal side-facts still doesn't
settle "there are few from southern Europe": southern-Europeanness could
come from committee members who aren't Portuguese at all, which the
premises say nothing about. Direction 1: nobody is Portuguese, but
everybody happens to be from southern Europe anyway (premises true,
hypothesis — "few are" — false). -/
theorem fracas_028_dir1 :
    (AtMost 1 (fun _ : Bool => True) (fun _ : Bool => False) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ False) (fun _ : Bool => True)) ∧
      ¬ AtMost 1 (fun _ : Bool => True) (fun _ : Bool => True) := by
  refine ⟨⟨by decide, fun _ _ => trivial, fun _ h => h.2.elim⟩, by decide⟩

/-- Direction 2: nobody is Portuguese, and nobody is from southern
Europe either (premises true, hypothesis true) — same countermodel
shape, opposite southern-Europe assignment. -/
theorem fracas_028_dir2 :
    (AtMost 1 (fun _ : Bool => True) (fun _ : Bool => False) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ False) (fun _ : Bool => False)) ∧
      AtMost 1 (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨⟨by decide, fun _ _ => trivial, fun _ h => h.2.elim⟩, by decide⟩

end P028

/-! ## Problem 29: `both` (`Every`) scope-weakening -/

section P029
variable {A : Type*} (commissioner leadingBusinessman businessman : A → Prop)

theorem fracas_029 :
    Every commissioner leadingBusinessman →
      (∀ x, leadingBusinessman x → businessman x) →
        Every commissioner businessman :=
  every_mono_scope commissioner leadingBusinessman businessman

end P029

/-! ## Problem 30: `neither` (`No`) fails to drop an adjunct (`.unknown`) -/

section P030

/-- Same shape as problem 22 with `No` instead of "no delegate": "neither
commissioner spends *a lot of* time at home" doesn't settle "neither
spends time at home" — direction 1, someone spends some (not "a lot of")
time; direction 2, nobody spends any time at all. -/
theorem fracas_030_dir1 :
    No (fun _ : Bool => True) (fun _ : Bool => False) ∧
      ¬ No (fun _ : Bool => True) (fun _ : Bool => True) := by
  refine ⟨fun _ _ h => h, ?_⟩
  intro h
  exact h true trivial trivial

theorem fracas_030_dir2 :
    No (fun _ : Bool => True) (fun _ : Bool => False) ∧
      No (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨fun _ _ h => h, fun _ _ h => h⟩

end P030

/-! ## Problem 31: `AtLeast` scope-weakening -/

section P031
variable {A : Type*} [Fintype A] (commissioner lotOfTime someTime : A → Prop)
variable [DecidablePred fun x => commissioner x ∧ lotOfTime x]
variable [DecidablePred fun x => commissioner x ∧ someTime x]

theorem fracas_031 :
    AtLeast 3 commissioner lotOfTime → (∀ x, lotOfTime x → someTime x) →
      AtLeast 3 commissioner someTime :=
  atLeast_mono_scope 3 commissioner lotOfTime someTime

end P031

end FraCaS.Section1
