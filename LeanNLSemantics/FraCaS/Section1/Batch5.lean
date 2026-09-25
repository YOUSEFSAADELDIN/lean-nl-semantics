import LeanNLSemantics.FraCaS.Section1.GQ

/-!
# FraCaS Section 1, problems 60–80 (the final subsection)

Fifth and final batch of the Phase 2 harness, completing Section 1's 80
problems. This subsection is built around **restrictor variance**:
narrowing or widening which subgroup a determiner ranges over (female
committee members vs. committee members, Irish delegates vs. delegates,
Canadian residents vs. North American residents, ...). The pattern that
emerges, mirroring `atLeast_mono_scope`/`atMost_mono_scope`'s
scope-variance split from `Batch4.lean`:

- `Some`/`Every`/`Most` are only licensed to **narrow** a restrictor
  going the *transitive* direction (`every_restrict`/`some_restrict`
  already existed; a broad `Every`/`Some` about a superset restricts
  down to any subset) — going the other way (subset fact ⊢ superset
  claim) is `.unknown` (65/71–73/75, and 60/61 for `AtMost`/`Every`).
- `AtLeast` transfers **up** from subset to superset (`atLeast_restrict`,
  63/79's converse), `AtMost` transfers **down** from superset to subset
  (`atMost_restrict`, 76/80), each the direction that actually holds —
  attempting them backwards (64/79) is independent.

Problems 61/62/77/78 revisit the "both"/"neither" cardinality
presupposition `GQ.lean` explicitly documents skipping (`both`/`neither`
treated as plain `Every`/`No`, no "exactly two" side-condition). FraCaS's
own gold answer there is itself a conditional hedge ("Yes, if both
commissioners are female; otherwise..."), not a flat yes/no/unknown —
a presupposition-failure case a two/three-valued semantics can't
literally reproduce. Under this project's presupposition-free
simplification, 77/78 (broad ⊢ narrow) are genuinely provable and 61/62
(narrow ⊢ broad) are genuinely independent, both noted as such rather
than forced to match FraCaS's hedge.
-/

namespace FraCaS.Section1

/-! ## Problem 60: `AtMost`, restrictor-widening — `.unknown` -/

section P060

/-- "Few female committee members are from southern Europe" doesn't
bound "few committee members are" — the non-female members could all be
from southern Europe too. -/
theorem fracas_060_dir1 :
    AtMost 1 (fun b : Bool => b = true) (fun _ : Bool => True) ∧
      ¬ AtMost 1 (fun _ : Bool => True) (fun _ : Bool => True) := by
  constructor <;> decide

theorem fracas_060_dir2 :
    AtMost 1 (fun b : Bool => b = true) (fun b : Bool => b = true) ∧
      AtMost 1 (fun _ : Bool => True) (fun b : Bool => b = true) := by
  constructor <;> decide

end P060

/-! ## Problem 61: `Every`, restrictor-widening — presupposition case, `.undef` -/

section P061

/-- Under this project's presupposition-free "both = Every" reading
(see this file's header), "every female commissioner used to be in
business" doesn't give "every commissioner did" — the male ones could
diverge. FraCaS's own hedge is about whether "both" presupposes exactly
two female commissioners, a different question this simplification
doesn't model; see the header. -/
theorem fracas_061_dir1 :
    Every (fun b : Bool => b = true) (fun b : Bool => b = true) ∧
      ¬ Every (fun _ : Bool => True) (fun b : Bool => b = true) := by
  refine ⟨fun _ h => h, ?_⟩
  intro h; exact absurd (h false trivial) (by decide)

theorem fracas_061_dir2 :
    Every (fun b : Bool => b = true) (fun _ : Bool => True) ∧
      Every (fun _ : Bool => True) (fun _ : Bool => True) :=
  ⟨fun _ _ => trivial, fun _ _ => trivial⟩

end P061

/-! ## Problem 62: `No`, restricted to a subgroup — same shape as 54, `.undef` -/

section P062

/-- "Neither female commissioner spends a lot of time at home" says
nothing about male commissioners — same independence as problem 54,
under the same presupposition-free reading as problem 61. -/
theorem fracas_062_dir1 :
    No (fun b : Bool => b = true) (fun _ : Bool => False) ∧
      ¬ Some (fun _ : Bool => True) (fun _ : Bool => False) := by
  refine ⟨fun _ _ h => h, ?_⟩
  rintro ⟨_, _, h⟩; exact h

theorem fracas_062_dir2 :
    No (fun b : Bool => b = true) (fun b : Bool => b = false) ∧
      Some (fun _ : Bool => True) (fun b : Bool => b = false) := by
  refine ⟨?_, false, trivial, rfl⟩
  intro b hb
  simp only [hb]
  decide

end P062

/-! ## Problem 63: `AtLeast`, restrictor-narrowing — genuinely `.yes` -/

section P063
variable {A : Type*} [Fintype A] (femaleCommissioner timeAtHome commissioner : A → Prop)
variable [DecidablePred fun x => femaleCommissioner x ∧ timeAtHome x]
variable [DecidablePred fun x => commissioner x ∧ timeAtHome x]

theorem fracas_063 :
    AtLeast 3 femaleCommissioner timeAtHome → Every femaleCommissioner commissioner →
      AtLeast 3 commissioner timeAtHome :=
  atLeast_restrict 3 femaleCommissioner timeAtHome commissioner

end P063

/-! ## Problem 64: `AtMost`, restrictor-widening — same shape as 60, `.unknown` -/

section P064

theorem fracas_064_dir1 :
    AtMost 1 (fun b : Bool => b = true) (fun _ : Bool => True) ∧
      ¬ AtMost 1 (fun _ : Bool => True) (fun _ : Bool => True) := by
  constructor <;> decide

theorem fracas_064_dir2 :
    AtMost 1 (fun b : Bool => b = true) (fun b : Bool => b = true) ∧
      AtMost 1 (fun _ : Bool => True) (fun b : Bool => b = true) := by
  constructor <;> decide

end P064

/-! ## Problem 65: converse of 49 — `.unknown` -/

section P065

/-- "A Scandinavian won a Nobel prize; every Swede is a Scandinavian"
doesn't tell you "a Swede won a Nobel prize" — the winner might be a
non-Swedish Scandinavian. -/
theorem fracas_065_dir1 :
    (Some (fun _ : Bool => True) (fun b : Bool => b = false) ∧
        Every (fun b : Bool => b = true) (fun _ : Bool => True)) ∧
      ¬ Some (fun b : Bool => b = true) (fun b : Bool => b = false) := by
  refine ⟨⟨⟨false, trivial, rfl⟩, fun _ _ => trivial⟩, ?_⟩
  rintro ⟨b, hb1, hb2⟩
  rw [hb1] at hb2
  exact absurd hb2 (by decide)

theorem fracas_065_dir2 :
    (Some (fun _ : Bool => True) (fun b : Bool => b = true) ∧
        Every (fun b : Bool => b = true) (fun _ : Bool => True)) ∧
      Some (fun b : Bool => b = true) (fun b : Bool => b = true) :=
  ⟨⟨⟨true, trivial, rfl⟩, fun _ _ => trivial⟩, ⟨true, rfl, rfl⟩⟩

end P065

/-! ## Problems 66–69, 77: `Every`, restrictor-narrowing — genuinely `.yes` -/

section P066
variable {A : Type*} (naResident travel canadianResident : A → Prop)

theorem fracas_066 :
    Every naResident travel → Every canadianResident naResident → Every canadianResident travel :=
  every_restrict canadianResident travel naResident

theorem fracas_067 :
    Every naResident travel → Every canadianResident naResident → Every canadianResident travel :=
  every_restrict canadianResident travel naResident

theorem fracas_068 :
    Every naResident travel → Every canadianResident naResident → Every canadianResident travel :=
  every_restrict canadianResident travel naResident

end P066

section P069
variable {A : Type*} (residentWestern rightToLive residentMajorWestern : A → Prop)

theorem fracas_069 :
    Every residentWestern rightToLive → Every residentMajorWestern residentWestern →
      Every residentMajorWestern rightToLive :=
  every_restrict residentMajorWestern rightToLive residentWestern

end P069

/-! ## Problem 70: `No` refutes a subgroup existential (composition, no new lemma) -/

section P070
variable {A : Type*} (delegate finishOnTime scandinavianDelegate : A → Prop)

theorem fracas_070 :
    No delegate finishOnTime → Every scandinavianDelegate delegate →
      ¬ Some scandinavianDelegate finishOnTime :=
  fun hno hsub hsome =>
    (no_iff_not_some delegate finishOnTime).mp hno (some_restrict scandinavianDelegate finishOnTime delegate hsome hsub)

end P070

/-! ## Problems 71–73, 75: `Some` over a broad group doesn't narrow — `.unknown` -/

section P071

/-- "Some delegates finished the survey on time" doesn't tell you "some
Irish delegates" did — the ones who finished on time might all be
non-Irish. No stated subset premise is even needed to see this fails
(unlike 65, where one was given and it still failed). -/
theorem fracas_071_dir1 :
    Some (fun _ : Bool => True) (fun b : Bool => b = false) ∧
      ¬ Some (fun b : Bool => b = true) (fun b : Bool => b = false) := by
  refine ⟨⟨false, trivial, rfl⟩, ?_⟩
  rintro ⟨b, hb1, hb2⟩
  rw [hb1] at hb2
  exact absurd hb2 (by decide)

theorem fracas_071_dir2 :
    Some (fun _ : Bool => True) (fun b : Bool => b = true) ∧
      Some (fun b : Bool => b = true) (fun b : Bool => b = true) :=
  ⟨⟨true, trivial, rfl⟩, ⟨true, rfl, rfl⟩⟩

end P071

section P072
theorem fracas_072_dir1 :
    Some (fun _ : Bool => True) (fun b : Bool => b = false) ∧
      ¬ Some (fun b : Bool => b = true) (fun b : Bool => b = false) := by
  refine ⟨⟨false, trivial, rfl⟩, ?_⟩
  rintro ⟨b, hb1, hb2⟩
  rw [hb1] at hb2
  exact absurd hb2 (by decide)

theorem fracas_072_dir2 :
    Some (fun _ : Bool => True) (fun b : Bool => b = true) ∧
      Some (fun b : Bool => b = true) (fun b : Bool => b = true) :=
  ⟨⟨true, trivial, rfl⟩, ⟨true, rfl, rfl⟩⟩
end P072

section P073
theorem fracas_073_dir1 :
    Some (fun _ : Bool => True) (fun b : Bool => b = false) ∧
      ¬ Some (fun b : Bool => b = true) (fun b : Bool => b = false) := by
  refine ⟨⟨false, trivial, rfl⟩, ?_⟩
  rintro ⟨b, hb1, hb2⟩
  rw [hb1] at hb2
  exact absurd hb2 (by decide)

theorem fracas_073_dir2 :
    Some (fun _ : Bool => True) (fun b : Bool => b = true) ∧
      Some (fun b : Bool => b = true) (fun b : Bool => b = true) :=
  ⟨⟨true, trivial, rfl⟩, ⟨true, rfl, rfl⟩⟩
end P073

section P075
theorem fracas_075_dir1 :
    Some (fun _ : Bool => True) (fun b : Bool => b = false) ∧
      ¬ Some (fun b : Bool => b = true) (fun b : Bool => b = false) := by
  refine ⟨⟨false, trivial, rfl⟩, ?_⟩
  rintro ⟨b, hb1, hb2⟩
  rw [hb1] at hb2
  exact absurd hb2 (by decide)

theorem fracas_075_dir2 :
    Some (fun _ : Bool => True) (fun b : Bool => b = true) ∧
      Some (fun b : Bool => b = true) (fun b : Bool => b = true) :=
  ⟨⟨true, trivial, rfl⟩, ⟨true, rfl, rfl⟩⟩
end P075

/-! ## Problem 74: `Most` over the whole population doesn't narrow — `.unknown` -/

section P074

/-- "Most Europeans can travel" doesn't tell you "most Europeans
resident outside Europe can" — five Europeans, only those outside
Europe (elements 0,1) might be exactly the ones who *don't* travel,
while the majority (2,3,4) who do travel are all resident *in* Europe. -/
theorem fracas_074_dir1 :
    Most (fun _ : Fin 5 => True) (fun x : Fin 5 => 2 ≤ x.val) ∧
      ¬ Most (fun x : Fin 5 => x.val < 2) (fun x : Fin 5 => 2 ≤ x.val) := by
  constructor <;> decide

theorem fracas_074_dir2 :
    Most (fun _ : Fin 5 => True) (fun _ : Fin 5 => True) ∧
      Most (fun x : Fin 5 => x.val < 2) (fun _ : Fin 5 => True) := by
  constructor <;> decide

end P074

/-! ## Problem 76: `AtMost`, restrictor-narrowing — genuinely `.yes` (mirrors 63) -/

section P076
variable {A : Type*} [Fintype A] (committee southernEurope femaleCommittee : A → Prop)
variable [DecidablePred fun x => committee x ∧ southernEurope x]
variable [DecidablePred fun x => femaleCommittee x ∧ southernEurope x]

theorem fracas_076 :
    AtMost 1 committee southernEurope → Every femaleCommittee committee →
      AtMost 1 femaleCommittee southernEurope :=
  atMost_restrict 1 committee southernEurope femaleCommittee

end P076

/-! ## Problem 77: `Every`, restrictor-narrowing — genuinely `.yes` (see problem 61) -/

section P077
variable {A : Type*} (commissioner usedToBeInBusiness femaleCommissioner : A → Prop)

theorem fracas_077 :
    Every commissioner usedToBeInBusiness → Every femaleCommissioner commissioner →
      Every femaleCommissioner usedToBeInBusiness :=
  every_restrict femaleCommissioner usedToBeInBusiness commissioner

end P077

/-! ## Problem 78: `No` restricted downward — genuinely refutes (see problem 62) -/

section P078
variable {A : Type*} (commissioner lotOfTime femaleCommissioner : A → Prop)

theorem fracas_078 :
    No commissioner lotOfTime → Every femaleCommissioner commissioner →
      ¬ Some femaleCommissioner lotOfTime :=
  fun hno hsub hsome =>
    (no_iff_not_some commissioner lotOfTime).mp hno (some_restrict femaleCommissioner lotOfTime commissioner hsome hsub)

end P078

/-! ## Problem 79: `AtLeast`, restrictor-narrowing the wrong way — `.unknown` -/

section P079

/-- "At least three commissioners spend time at home" doesn't bound "at
least three *male* commissioners" — the three could all be female. -/
theorem fracas_079_dir1 :
    AtLeast 3 (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) ∧
      ¬ AtLeast 3 (fun x : Fin 3 => x.val < 1) (fun _ : Fin 3 => True) := by
  constructor <;> decide

theorem fracas_079_dir2 :
    AtLeast 3 (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) ∧
      AtLeast 3 (fun _ : Fin 3 => True) (fun _ : Fin 3 => True) := by
  constructor <;> decide

end P079

/-! ## Problem 80: `AtMost`, restrictor-narrowing — genuinely `.yes` (mirrors 76) -/

section P080
variable {A : Type*} [Fintype A] (commissioner timeAtHome femaleCommissioner : A → Prop)
variable [DecidablePred fun x => commissioner x ∧ timeAtHome x]
variable [DecidablePred fun x => femaleCommissioner x ∧ timeAtHome x]

theorem fracas_080 :
    AtMost 10 commissioner timeAtHome → Every femaleCommissioner commissioner →
      AtMost 10 femaleCommissioner timeAtHome :=
  atMost_restrict 10 commissioner timeAtHome femaleCommissioner

end P080

end FraCaS.Section1
