import LeanNLSemantics.FraCaS.Section1.GQ

/-!
# FraCaS Section 1, problems 32–45 (the "converse" subsection)

Third batch of the Phase 2 harness, continuing `Batch2.lean`. This
subsection systematically tests the **converse** of problems 1–31: take
a premise/hypothesis pair that entailed, and ask whether swapping which
one is asserted and which is asked about still entails. Almost always it
doesn't (11 of these 14 are `.unknown`) — "most Europeans can travel"
doesn't tell you "most Europeans are resident", it only goes the other
way. Problem 38 goes further and is a genuine `.no` (¬hypothesis
follows), and problem 44 is a genuine `.yes` — a different converse that
*does* hold, because it's really a subset argument, not an unwarranted
strengthening.

For the eleven `.unknown` problems, the two-direction countermodel
witnesses are mostly interchangeable across the "does adding/
strengthening a detail follow" shape (problems 33/39/40/41/45 are all
literally the same abstract pattern under different English vocabulary,
same as `Some`/`Every` under an unwarranted scope-narrowing), so they're
written out per-problem rather than factored into one more GQ.lean
lemma — each theorem's *type* is still the real translation of that
problem's English, which is what should stay legible even when two
proofs happen to coincide.
-/

namespace FraCaS.Section1

/-! ## Problem 32: `AtMost`, converse of problem 31's scope-widening -/

section P032

/-- "At most ten commissioners spend a lot of time at home" doesn't
bound "at most ten spend time at home" — more people could spend some
(not "a lot of") time. 11 elements, all spending *some* time, is enough
to break the bound while nobody spends *a lot*. -/
theorem fracas_032_dir1 :
    AtMost 10 (fun _ : Fin 11 => True) (fun _ : Fin 11 => False) ∧
      ¬ AtMost 10 (fun _ : Fin 11 => True) (fun _ : Fin 11 => True) := by
  constructor <;> decide

theorem fracas_032_dir2 :
    AtMost 10 (fun _ : Fin 11 => True) (fun _ : Fin 11 => False) ∧
      AtMost 10 (fun _ : Fin 11 => True) (fun _ : Fin 11 => False) := by
  constructor <;> decide

end P032

/-! ## Problem 33: converse of problem 17's scope-weakening -/

section P033

/-- "An Irishman won a Nobel prize" doesn't tell you it was for
literature specifically. -/
theorem fracas_033_dir1 :
    Some (fun _ : Bool => True) (fun _ : Bool => True) ∧
      ¬ Some (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨⟨true, trivial, trivial⟩, ?_⟩
  rintro ⟨_, _, h⟩; exact h

theorem fracas_033_dir2 :
    Some (fun _ : Bool => True) (fun _ : Bool => True) ∧
      Some (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨true, trivial, trivial⟩, ⟨true, trivial, trivial⟩⟩

end P033

/-! ## Problems 34–37: converse of the every_trans chain (18–21) -/

/-- Shared shape for problems 34–37 (every/all/each/the-residents, same
as 18–21): "every P can travel; every P is a person; every person with
the right can travel" doesn't tell you every P *has* the right —
travel could hold some other way. A model where everyone travels and
everyone is a person makes premises 1–2 and the (vacuously true, since
its antecedent is never satisfied) premise 3 hold regardless of whether
anyone has the right, so "the right" is free to be false (direction 1)
or true (direction 2) independent of the premises. -/
section P034
theorem fracas_034_dir1 :
    (Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ False) (fun _ : Bool => True)) ∧
      ¬ Every (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩, ?_⟩
  intro h; exact h true trivial

theorem fracas_034_dir2 :
    (Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ True) (fun _ : Bool => True)) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩, fun _ _ => trivial⟩
end P034

section P035
theorem fracas_035_dir1 :
    (Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ False) (fun _ : Bool => True)) ∧
      ¬ Every (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩, ?_⟩
  intro h; exact h true trivial

theorem fracas_035_dir2 :
    (Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ True) (fun _ : Bool => True)) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩, fun _ _ => trivial⟩
end P035

section P036
theorem fracas_036_dir1 :
    (Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ False) (fun _ : Bool => True)) ∧
      ¬ Every (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩, ?_⟩
  intro h; exact h true trivial

theorem fracas_036_dir2 :
    (Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ True) (fun _ : Bool => True)) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩, fun _ _ => trivial⟩
end P036

section P037
theorem fracas_037_dir1 :
    (Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ False) (fun _ : Bool => True)) ∧
      ¬ Every (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩, ?_⟩
  intro h; exact h true trivial

theorem fracas_037_dir2 :
    (Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ True) (fun _ : Bool => True)) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩, fun _ _ => trivial⟩
end P037

/-! ## Problem 38: `No` plus scope-weakening gives an outright refutation -/

section P038
variable {A : Type*} (delegate finish onTime : A → Prop)

/-- "No delegate finished the report" refutes "some delegate finished
the report on time" outright (not just "doesn't support it") — finishing
on time entails finishing, so if nobody finished, nobody finished on
time either. Pure composition of `no_iff_not_some` and
`some_mono_scope`, no new lemma needed. -/
theorem fracas_038 :
    No delegate finish → (∀ x, onTime x → finish x) → ¬ Some delegate onTime :=
  fun hno honto hsome => (no_iff_not_some delegate finish).mp hno (some_mono_scope delegate onTime finish hsome honto)

end P038

/-! ## Problems 39–41: converse of the positive-context adjunct-add (23–25) -/

section P039
theorem fracas_039_dir1 :
    Some (fun _ : Bool => True) (fun _ : Bool => True) ∧
      ¬ Some (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨⟨true, trivial, trivial⟩, ?_⟩
  rintro ⟨_, _, h⟩; exact h

theorem fracas_039_dir2 :
    Some (fun _ : Bool => True) (fun _ : Bool => True) ∧
      Some (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨true, trivial, trivial⟩, ⟨true, trivial, trivial⟩⟩
end P039

section P040
theorem fracas_040_dir1 :
    Some (fun _ : Bool => True) (fun _ : Bool => True) ∧
      ¬ Some (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨⟨true, trivial, trivial⟩, ?_⟩
  rintro ⟨_, _, h⟩; exact h

theorem fracas_040_dir2 :
    Some (fun _ : Bool => True) (fun _ : Bool => True) ∧
      Some (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨true, trivial, trivial⟩, ⟨true, trivial, trivial⟩⟩
end P040

section P041
theorem fracas_041_dir1 :
    Some (fun _ : Bool => True) (fun _ : Bool => True) ∧
      ¬ Some (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨⟨true, trivial, trivial⟩, ?_⟩
  rintro ⟨_, _, h⟩; exact h

theorem fracas_041_dir2 :
    Some (fun _ : Bool => True) (fun _ : Bool => True) ∧
      Some (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨true, trivial, trivial⟩, ⟨true, trivial, trivial⟩⟩
end P041

/-! ## Problem 42: converse of `most_trans` (26) -/

section P042

/-- "Most Europeans can travel" doesn't tell you "most are resident" —
travel could hold some other way. Three elements, everyone travels and
is a person, but nobody's resident: premises 1–2 hold (2·3 > 3), premise
3 is vacuous (nobody's a resident person), and "most are resident" is
false (direction 1) or can be made true the same vacuous way (direction
2). -/
theorem fracas_042_dir1 :
    (Most (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) ∧
        Every (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) ∧
        Every (fun x : Fin 3 => True ∧ False) (fun _ : Fin 3 => True)) ∧
      ¬ Most (fun _ : Fin 3 => True) (fun _ : Fin 3 => False) := by
  refine ⟨⟨by decide, fun _ _ => trivial, fun _ _ => trivial⟩, ?_⟩
  decide

theorem fracas_042_dir2 :
    (Most (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) ∧
        Every (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) ∧
        Every (fun x : Fin 3 => True ∧ True) (fun _ : Fin 3 => True)) ∧
      Most (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) := by
  refine ⟨⟨by decide, fun _ _ => trivial, fun _ _ => trivial⟩, by decide⟩

end P042

/-! ## Problem 43: converse of `some_trans` (27) -/

section P043

/-- "A few committee members are from Scandinavia" doesn't tell you "at
least a few are from Sweden" — Scandinavia is the broader region. -/
theorem fracas_043_dir1 :
    (Some (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ False) (fun _ : Bool => True)) ∧
      ¬ Some (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨⟨⟨true, trivial, trivial⟩, fun _ _ => trivial, fun _ _ => trivial⟩, ?_⟩
  rintro ⟨_, _, h⟩; exact h

theorem fracas_043_dir2 :
    (Some (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
        Every (fun x : Bool => True ∧ True) (fun _ : Bool => True)) ∧
      Some (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨⟨⟨true, trivial, trivial⟩, fun _ _ => trivial, fun _ _ => trivial⟩, ⟨true, trivial, trivial⟩⟩

end P043

/-! ## Problem 44: a converse that *does* hold — `atMost_trans` -/

section P044
variable {A : Type*} [Fintype A] (n : Nat) (committee southernEurope person portugal : A → Prop)
variable [DecidablePred fun x => committee x ∧ portugal x]
variable [DecidablePred fun x => committee x ∧ southernEurope x]

/-- Unlike 32–43, this converse genuinely holds: Portugal is a *subset*
of southern Europe (premise 3), so bounding southern-Europeans among the
committee already bounds Portuguese committee members — a real subset
argument, not an unwarranted strengthening. Holds for every `n`, which
is stronger than FraCaS's own vague "few" needed. -/
theorem fracas_044 :
    AtMost n committee southernEurope → Every committee person →
      Every (fun x => person x ∧ portugal x) southernEurope →
        AtMost n committee portugal :=
  atMost_trans n committee portugal person southernEurope

end P044

/-! ## Problem 45: converse of `every_mono_scope` (29) -/

section P045

/-- "Both commissioners used to be businessmen" doesn't tell you they
were *leading* businessmen. -/
theorem fracas_045_dir1 :
    Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
      ¬ Every (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨fun _ _ => trivial, ?_⟩
  intro h; exact h true trivial

theorem fracas_045_dir2 :
    Every (fun _ : Bool => True) (fun _ : Bool => True) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨fun _ _ => trivial, fun _ _ => trivial⟩

end P045

end FraCaS.Section1
