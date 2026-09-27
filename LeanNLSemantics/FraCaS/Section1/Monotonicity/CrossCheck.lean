import LeanNLSemantics.FraCaS.Section1.Monotonicity.Compose

/-!
# Phase-1 demonstration: `mono_nl` against the fourteen target problems

**Validation status**: see `Tactic.lean`'s header. This file's first CI
run found a real bug in `mono_nl` itself (`whnf` over-unfolding the goal,
fixed there) via these exact fourteen theorems failing to elaborate -
i.e. this cross-check already did its job once, catching a genuine
mistake before it could be mistaken for a working tactic. Awaiting a
second CI run against the fix before treating any of these fourteen as
confirmed.

Unlike `Section1/GFCrossCheck.lean`'s cross-check (two *independently
arrived at* formalizations - a hand proof and a separately GF-translated
one - agreeing on the same proposition), this file checks a different
thing: that `mono_nl` *automatically reconstructs*, from the bare goal
shape alone, the same already-proved `GQ.lean` lemma and argument order
each of these fourteen problems' hand proof cited directly. Each theorem
below restates one target problem's exact original statement (same
variable names, same premises, same conclusion, copied from its `Batch*.
lean` file rather than imported, since nothing here needs the original
proof *term* - only its statement) and proves it with `by mono_nl`
instead of the direct lemma application `Batch*.lean` uses. The original
theorems in `Batch2.lean`/`Batch4.lean`/`Batch5.lean` are untouched -
this file is additive, the same non-invasive pattern `GFCrossCheck.lean`
already established.

Problems 66, 67, and 68 share one statement verbatim in the original
source (three FraCaS problems, one underlying English/logical shape), so
one cross-check theorem stands for all three rather than being repeated
three times for no new information - the same "don't re-run an identical
check under a new label" principle `gf/run_gf_tests.py` documents for its
own duplicate sentences. Problems 18, 19, and 20 are the same situation.

Problems 13 and 18-21, added for Phase 2, exercise the new combine step
(`Tactic.lean`'s `entails_and`/`entails_refl` search) rather than a
direct hypothesis match - `mono_nl` reconstructs `every_mp`'s and
`every_trans`'s own recipe (combine two premises into a conjunction, then
substitute) without either being named anywhere in `Tactic.lean`.

Problems 2-5, 10, 15, and 107-110, added for Category B, use `exist_nl`
instead of `mono_nl` - a different tactic entirely (see `Existential.
lean`'s header for why this is a genuinely different search, not a third
`mono_nl` rule), covering `every_some`'s/`some_of_nonempty`'s existential-
transfer principle (2-5) and `most_some`'s/`atLeast_some`'s/
`some_of_exactly`'s positive-cardinality principle (10, 15, 107-110).
Problems 107-110 share one statement (same pattern as 66-68/18-20).

Problem 123, added for Phase 3 (`Compose.lean`), uses `mono_nl_compose`:
its real proof composes `exist_nl`'s `mostSome` (deriving `Some
reportsNeeded sentByItel` from `Most reportsNeeded sentByItel`) with
`mono_nl`'s own `someMonoScope`, exactly the way `Section3/Batch1.lean`'s
hand proof does.

Problems 124 and 27, added for Phase 4 (`Compose.lean`), also use
`mono_nl_compose` unchanged - only what it enumerates was widened. 124
composes the new `exactly_atLeast` (`Exactly 2 P Q → AtLeast 2 P Q`) with
`mono_nl`'s existing `atLeastMonoScope`; 27 composes the new
`some_entails_and` (`Some P R → Every P S → Some P (S∧R)`) with `mono_nl`'s
existing `someMonoScope` - see `Compose.lean`'s header for the full
characterization, and for why 044 (`atMost_trans`), the last remaining
eligible-but-failed problem, does *not* reduce this way and was left
unsupported.
-/
namespace FraCaS.Section1.Monotonicity

open FraCaS.Section1
open FraCaS.Section2

section P029
variable {A : Type*} (commissioner leadingBusinessman businessman : A → Prop)

theorem fracas_029_via_mono_nl :
    Every commissioner leadingBusinessman →
      (∀ x, leadingBusinessman x → businessman x) →
        Every commissioner businessman := by mono_nl

end P029

section P031
variable {A : Type*} [Fintype A] (commissioner lotOfTime someTime : A → Prop)
variable [DecidablePred fun x => commissioner x ∧ lotOfTime x]
variable [DecidablePred fun x => commissioner x ∧ someTime x]

theorem fracas_031_via_mono_nl :
    AtLeast 3 commissioner lotOfTime → (∀ x, lotOfTime x → someTime x) →
      AtLeast 3 commissioner someTime := by mono_nl

end P031

section P048
variable {A : Type*} [Fintype A] (commissioner timeAtHome lotOfTime : A → Prop)
variable [DecidablePred fun x => commissioner x ∧ timeAtHome x]
variable [DecidablePred fun x => commissioner x ∧ lotOfTime x]

theorem fracas_048_via_mono_nl :
    AtMost 10 commissioner timeAtHome → (∀ x, lotOfTime x → timeAtHome x) →
      AtMost 10 commissioner lotOfTime := by mono_nl

end P048

section P049
variable {A : Type*} (swede wonNobel scandinavian : A → Prop)

theorem fracas_049_via_mono_nl :
    Some swede wonNobel → Every swede scandinavian → Some scandinavian wonNobel := by mono_nl

end P049

section P055
variable {A : Type*} (irishDelegate finishOnTime delegate : A → Prop)

theorem fracas_055_via_mono_nl :
    Some irishDelegate finishOnTime → Every irishDelegate delegate → Some delegate finishOnTime := by
  mono_nl

end P055

section P057
variable {A : Type*} (portugueseDelegate published delegate : A → Prop)

theorem fracas_057_via_mono_nl :
    Some portugueseDelegate published → Every portugueseDelegate delegate →
      Some delegate published := by mono_nl

end P057

section P059
variable {A : Type*} (femaleCommitteeMember scandinavian committeeMember : A → Prop)

theorem fracas_059_via_mono_nl :
    Some femaleCommitteeMember scandinavian → Every femaleCommitteeMember committeeMember →
      Some committeeMember scandinavian := by mono_nl

end P059

section P063
variable {A : Type*} [Fintype A] (femaleCommissioner timeAtHome commissioner : A → Prop)
variable [DecidablePred fun x => femaleCommissioner x ∧ timeAtHome x]
variable [DecidablePred fun x => commissioner x ∧ timeAtHome x]

theorem fracas_063_via_mono_nl :
    AtLeast 3 femaleCommissioner timeAtHome → Every femaleCommissioner commissioner →
      AtLeast 3 commissioner timeAtHome := by mono_nl

end P063

section P066
variable {A : Type*} (naResident travel canadianResident : A → Prop)

/-- Stands for problems 66, 67, and 68 alike - see this file's header. -/
theorem fracas_066_via_mono_nl :
    Every naResident travel → Every canadianResident naResident → Every canadianResident travel := by
  mono_nl

end P066

section P069
variable {A : Type*} (residentWestern rightToLive residentMajorWestern : A → Prop)

theorem fracas_069_via_mono_nl :
    Every residentWestern rightToLive → Every residentMajorWestern residentWestern →
      Every residentMajorWestern rightToLive := by mono_nl

end P069

section P076
variable {A : Type*} [Fintype A] (committee southernEurope femaleCommittee : A → Prop)
variable [DecidablePred fun x => committee x ∧ southernEurope x]
variable [DecidablePred fun x => femaleCommittee x ∧ southernEurope x]

theorem fracas_076_via_mono_nl :
    AtMost 1 committee southernEurope → Every femaleCommittee committee →
      AtMost 1 femaleCommittee southernEurope := by mono_nl

end P076

section P077
variable {A : Type*} (commissioner usedToBeInBusiness femaleCommissioner : A → Prop)

theorem fracas_077_via_mono_nl :
    Every commissioner usedToBeInBusiness → Every femaleCommissioner commissioner →
      Every femaleCommissioner usedToBeInBusiness := by mono_nl

end P077

section P013
variable {A : Type*} (leadingTenor excellent indispensable : A → Prop)

theorem fracas_013_via_mono_nl :
    Every leadingTenor excellent →
      Every (fun x => leadingTenor x ∧ excellent x) indispensable →
        Every leadingTenor indispensable := by mono_nl

end P013

section P018
variable {A : Type*} (european right person travelFreely : A → Prop)

/-- Stands for problems 18, 19, and 20 alike - see this file's header. -/
theorem fracas_018_via_mono_nl :
    Every european right → Every european person →
      Every (fun x => person x ∧ right x) travelFreely →
        Every european travelFreely := by mono_nl

end P018

section P021
variable {A : Type*} (residentMemberState right individual travelFreely : A → Prop)

theorem fracas_021_via_mono_nl :
    Every residentMemberState right → Every residentMemberState individual →
      Every (fun x => individual x ∧ right x) travelFreely →
        Every residentMemberState travelFreely := by mono_nl

end P021

section P002
variable {A : Type*} (italianMan wantsGreatTenor isGreatTenor : A → Prop)

/-- Stands for problems 2 and 3 alike (identical statement in the
original source, same as 66-68/18-20). -/
theorem fracas_002_via_exist_nl :
    Every italianMan wantsGreatTenor → Some italianMan isGreatTenor →
      Some italianMan wantsGreatTenor := by exist_nl

end P002

section P004
variable {A : Type*} (italianTenor wantsGreat isGreat : A → Prop)

theorem fracas_004_via_exist_nl :
    Every italianTenor wantsGreat → Some italianTenor isGreat →
      Some italianTenor wantsGreat := by exist_nl

end P004

section P005
variable {A : Type*} (ambitious italianPred : A → Prop)

theorem fracas_005_via_exist_nl (hNonempty : ∃ x, ambitious x) :
    Every ambitious italianPred → Some ambitious italianPred := by exist_nl

end P005

section P010
variable {A : Type*} [Fintype A] (greatTenor italianPred : A → Prop)
variable [DecidablePred greatTenor] [DecidablePred fun x => greatTenor x ∧ italianPred x]

theorem fracas_010_via_exist_nl :
    Most greatTenor italianPred → Some greatTenor italianPred := by exist_nl

end P010

section P015
variable {A : Type*} [Fintype A] (tenor takesPart : A → Prop)
variable [DecidablePred fun x => tenor x ∧ takesPart x]

theorem fracas_015_via_exist_nl :
    AtLeast 3 tenor takesPart → Some tenor takesPart := by exist_nl

end P015

section P107
variable {A : Type*} [Fintype A] (accountant attended : A → Prop)
variable [DecidablePred fun x => accountant x ∧ attended x]

/-- Stands for problems 107-110 alike (identical statement in the
original source). -/
theorem fracas_107_via_exist_nl :
    Exactly 1 accountant attended → Some accountant attended := by exist_nl

end P107

section P123
variable {A : Type*} [Fintype A] (reportsNeeded sentByItel onDesk : A → Prop)
variable [DecidablePred reportsNeeded] [DecidablePred fun x => reportsNeeded x ∧ sentByItel x]

theorem fracas_123_via_mono_nl_compose :
    Most reportsNeeded sentByItel → (∀ x, sentByItel x → onDesk x) →
      Some reportsNeeded onDesk := by mono_nl_compose

end P123

section P124
variable {A : Type*} [Fintype A] (missing removed : A → Prop)
variable [DecidablePred fun x : A => True ∧ missing x] [DecidablePred fun x : A => True ∧ removed x]

theorem fracas_124_via_mono_nl_compose :
    Exactly 2 (fun _ : A => True) missing → (∀ x, missing x → removed x) →
      AtLeast 2 (fun _ : A => True) removed := by mono_nl_compose

end P124

section P027
variable {A : Type*} (committee swedish person scandinavian : A → Prop)

theorem fracas_027_via_mono_nl_compose :
    Some committee swedish → Every committee person →
      Every (fun x => person x ∧ swedish x) scandinavian →
        Some committee scandinavian := by mono_nl_compose

end P027

end FraCaS.Section1.Monotonicity
