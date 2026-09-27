import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic

/-!
# Phase-1 demonstration: `mono_nl` against the fourteen target problems

**Validation status**: see `Tactic.lean`'s header - none of this has been
compiled yet (this sandbox's Lean toolchain fetch is policy-denied, not a
fixable misconfiguration), so nothing below is a confirmed result until a
real build (CI, or a session with toolchain access) says so.

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
own duplicate sentences.
-/
namespace FraCaS.Section1.Monotonicity

open FraCaS.Section1

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

end FraCaS.Section1.Monotonicity
