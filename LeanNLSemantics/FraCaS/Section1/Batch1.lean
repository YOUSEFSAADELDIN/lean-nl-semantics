import LeanNLSemantics.FraCaS.Section1.GQ

/-!
# FraCaS Section 1, problems 1–21 (the "tenor"/"European" subsections)

First batch of the Phase 2 harness: hand-formalizations of FraCaS
Section 1 (Generalized Quantifiers) problems, each proved against its
gold `Answer` from `FraCaS/Data/Problems.lean` (`fracas_NNN.answer`
matches this file's proof shape — `.yes` problems prove `premises →
hypothesis`, `.no` problems prove `premises → ¬hypothesis`).

This is **not** an automated theorem prover: Lean has no decision
procedure for arbitrary natural-language entailment, so "attempt both
directions" (the methodology agreed on for Phase 2) means what it means
in FraCoq/CoqLACL too — each sentence is hand-translated into a
restrictor/scope pair over `Section1.Every`/`Some`/`No`/... (see `GQ.lean`),
and *then* Lean checks whether the resulting entailment (or its negation)
actually holds. For the two `.undef` problems in this batch (12, 16 —
MacCartney's `fracas_nonstandard` cases, whose gold answer was itself a
hedge like "Not many", not a literal yes/no/unknown), "attempted both
directions" means exhibiting one concrete countermodel per direction:
a model satisfying the premises where the hypothesis holds, and another
where it doesn't, which is the constructive way to show neither
`premises → hypothesis` nor `premises → ¬hypothesis` is a validity —
the same countermodel method `Adjectives.lean`'s T-ADJ6 uses.

Vocabulary is scoped locally to each problem's own `section`, not shared
project-wide, since two problems both mentioning "tenor" are not
claiming to quantify over the same domain.
-/

namespace FraCaS.Section1

/-! ## Problem 1 -/

section P001
variable {A : Type*} (italian becameGreatestTenor : A → Prop)

/-- "an Italian became the world's greatest tenor" ⊢ "There was an
Italian who became the world's greatest tenor" — same claim restated,
not a nontrivial inference. -/
theorem fracas_001 : Some italian becameGreatestTenor → Some italian becameGreatestTenor :=
  id

end P001

/-! ## Problems 2–4: "every/all/each P want Q; some P are R ⊢ some P want Q" -/

section P002
variable {A : Type*} (italianMan wantsGreatTenor isGreatTenor : A → Prop)

theorem fracas_002 :
    Every italianMan wantsGreatTenor → Some italianMan isGreatTenor →
      Some italianMan wantsGreatTenor :=
  every_some italianMan wantsGreatTenor isGreatTenor

theorem fracas_003 :
    Every italianMan wantsGreatTenor → Some italianMan isGreatTenor →
      Some italianMan wantsGreatTenor :=
  every_some italianMan wantsGreatTenor isGreatTenor

end P002

section P004
variable {A : Type*} (italianTenor wantsGreat isGreat : A → Prop)

theorem fracas_004 :
    Every italianTenor wantsGreat → Some italianTenor isGreat →
      Some italianTenor wantsGreat :=
  every_some italianTenor wantsGreat isGreat

end P004

/-! ## Problem 5: definite plural, existential import assumed explicitly -/

section P005
variable {A : Type*} (ambitious italianPred : A → Prop)

/-- "The really ambitious tenors are Italian" ⊢ "There are really
ambitious tenors who are Italian". Definite plurals presuppose their
restrictor is nonempty (unlike "every", which is vacuously true of an
empty restrictor); `hNonempty` makes that presupposition an explicit
premise rather than silently assuming it. -/
theorem fracas_005 (hNonempty : ∃ x, ambitious x) :
    Every ambitious italianPred → Some ambitious italianPred := by
  obtain ⟨x, hx⟩ := hNonempty
  exact fun h => ⟨x, hx, h x hx⟩

end P005

/-! ## Problem 6: `no` licenses the negative, not the positive -/

section P006
variable {A : Type*} (reallyGreatTenor modest : A → Prop)

theorem fracas_006 : No reallyGreatTenor modest → ¬ Some reallyGreatTenor modest :=
  (no_iff_not_some reallyGreatTenor modest).mp

end P006

/-! ## Problems 7–9: some/many/several are all `Some` restatements -/

section P007
variable {A : Type*} (greatTenor swedish : A → Prop)
theorem fracas_007 : Some greatTenor swedish → Some greatTenor swedish := id
end P007

section P008
variable {A : Type*} (greatTenor german : A → Prop)
theorem fracas_008 : Some greatTenor german → Some greatTenor german := id
end P008

section P009
variable {A : Type*} (greatTenor british : A → Prop)
theorem fracas_009 : Some greatTenor british → Some greatTenor british := id
end P009

/-! ## Problem 10: `most` gives `some` -/

section P010
variable {A : Type*} [Fintype A] (greatTenor italianPred : A → Prop)
variable [DecidablePred greatTenor] [DecidablePred fun x => greatTenor x ∧ italianPred x]

theorem fracas_010 : Most greatTenor italianPred → Some greatTenor italianPred :=
  most_some greatTenor italianPred

end P010

/-! ## Problem 11: second premise is a distractor -/

section P011
variable {A : Type*} (greatTenor singsPopular likesPopular : A → Prop)

theorem fracas_011 :
    Some greatTenor singsPopular → Some greatTenor likesPopular → Some greatTenor singsPopular :=
  fun h _ => h

end P011

/-! ## Problem 12: "few" — `.undef`, independent in both directions -/

section P012

/-- "Few great tenors are poor" formalized as a small upper bound (the
gold answer itself is a hedge, "Not many", not a precise truth value —
see this file's header), reusing `AtMost` the same way problem 16 does.
Direction 1: a model where at most two (here: zero) great tenors are
poor, and indeed none are — so the premise doesn't force the hypothesis. -/
theorem fracas_012_dir1 :
    AtMost 2 (fun _ : Bool => True) (fun _ : Bool => False) ∧
      ¬ Some (fun _ : Bool => True) (fun _ : Bool => False) := by
  constructor
  · decide
  · rintro ⟨_, _, h⟩; exact h

/-- Direction 2: a model where at most two (here: both) great tenors are
poor, and both are — so the premise doesn't force the hypothesis's
negation either. Together with `fracas_012_dir1`, this is the
countermodel method's verdict: undecided, matching the gold `.undef`. -/
theorem fracas_012_dir2 :
    AtMost 2 (fun _ : Bool => True) (fun _ : Bool => True) ∧
      Some (fun _ : Bool => True) (fun _ : Bool => True) := by
  refine ⟨by decide, ⟨true, trivial, trivial⟩⟩

end P012

/-! ## Problem 13: `both` as universal, chained with a second universal -/

section P013
variable {A : Type*} (leadingTenor excellent indispensable : A → Prop)

theorem fracas_013 :
    Every leadingTenor excellent →
      Every (fun x => leadingTenor x ∧ excellent x) indispensable →
        Every leadingTenor indispensable :=
  every_mp leadingTenor excellent indispensable

end P013

/-! ## Problem 14: `neither` refutes a named instance -/

section P014
variable {A : Type*} (leadingTenor cheap : A → Prop) (pavarotti : A)

theorem fracas_014 :
    No leadingTenor cheap → leadingTenor pavarotti →
      ¬ (leadingTenor pavarotti ∧ cheap pavarotti) :=
  fun hno hlead ⟨_, hc⟩ => hno pavarotti hlead hc

end P014

/-! ## Problem 15: numeric lower bound gives existence -/

section P015
variable {A : Type*} [Fintype A] (tenor takesPart : A → Prop)
variable [DecidablePred fun x => tenor x ∧ takesPart x]

theorem fracas_015 : AtLeast 3 tenor takesPart → Some tenor takesPart :=
  atLeast_some 3 tenor takesPart (by norm_num)

end P015

/-! ## Problem 16: "at most two" — `.undef`, independent in both directions -/

section P016

/-- Same countermodel shape as problem 12: "at most two tenors will
contribute" holds vacuously (direction 1) or with both contributing
(direction 2), so it doesn't settle "there are tenors who will
contribute" either way. -/
theorem fracas_016_dir1 :
    AtMost 2 (fun _ : Bool => True) (fun _ : Bool => False) ∧
      ¬ Some (fun _ : Bool => True) (fun _ : Bool => False) := by
  constructor
  · decide
  · rintro ⟨_, _, h⟩; exact h

theorem fracas_016_dir2 :
    AtMost 2 (fun _ : Bool => True) (fun _ : Bool => True) ∧
      Some (fun _ : Bool => True) (fun _ : Bool => True) := by
  refine ⟨by decide, ⟨true, trivial, trivial⟩⟩

end P016

/-! ## Problem 17: scope-predicate weakening -/

section P017
variable {A : Type*} (irishman wonNobelLit wonNobel : A → Prop)

theorem fracas_017 :
    Some irishman wonNobelLit → (∀ x, wonNobelLit x → wonNobel x) → Some irishman wonNobel :=
  some_mono_scope irishman wonNobelLit wonNobel

end P017

/-! ## Problems 18–21: three-premise universal transitivity -/

section P018
variable {A : Type*} (european right person travelFreely : A → Prop)

theorem fracas_018 :
    Every european right → Every european person →
      Every (fun x => person x ∧ right x) travelFreely →
        Every european travelFreely :=
  every_trans european right person travelFreely

theorem fracas_019 :
    Every european right → Every european person →
      Every (fun x => person x ∧ right x) travelFreely →
        Every european travelFreely :=
  every_trans european right person travelFreely

theorem fracas_020 :
    Every european right → Every european person →
      Every (fun x => person x ∧ right x) travelFreely →
        Every european travelFreely :=
  every_trans european right person travelFreely

end P018

section P021
variable {A : Type*} (residentMemberState right individual travelFreely : A → Prop)

theorem fracas_021 :
    Every residentMemberState right → Every residentMemberState individual →
      Every (fun x => individual x ∧ right x) travelFreely →
        Every residentMemberState travelFreely :=
  every_trans residentMemberState right individual travelFreely

end P021

end FraCaS.Section1
