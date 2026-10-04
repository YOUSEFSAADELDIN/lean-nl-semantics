import LeanNLSemantics.FraCaS.Section7.Temporal

/-!
# FraCaS Section 7, problems 261–276

Event-ordering chains via real `Nat` timestamps: transitivity and
before/after converses hold outright for telic, punctual-enough
predicates (261/262/264–268/270), but the same chain over a bare
repeated activity or state (269/271–274) is `.unknown`, since a second
bare mention need not pick out the same occasion. Problem 275 tests
"before"'s non-factivity about its embedded clause. Problem 276 (empty
question/hypothesis in the original) is skipped, per
`FraCaS/Types.lean`'s documented degenerate-problem list.
-/

namespace FraCaS.Section7

/-! ## Problems 261/262: transitivity of before/after -/

section P261
variable (tSmith tJones tAnderson : Nat)

theorem fracas_261 :
    tSmith < tJones → tJones < tAnderson → tSmith < tAnderson := by omega

end P261

section P262
variable (tSmith tJones tAnderson : Nat)

theorem fracas_262 :
    tSmith > tJones → tJones > tAnderson → tSmith > tAnderson := by omega

end P262

/-! ## Problem 263: mixed "present"/"left" chain over states, unknown -/

section P263

/-- Mixing a state ("was present") with an achievement ("left") across
two premises doesn't compose the same way a pure achievement chain
does: "Smith present after Jones left" and "Jones left after Anderson
present" don't pin down a single timestamp for each event the way
261/262 do. Using real `Nat` timestamps here would be unsound (`<`'s own
transitivity would make the conclusion trivially provable, contradicting
the genuine independence FraCaS reports) - opaque facts, not arithmetic,
are the faithful encoding of a state/achievement composition that
doesn't go through. -/
theorem fracas_263_dir1
    (smithPresentAfterJonesLeft jonesLeftAfterAndersonPresent
      smithPresentAfterAndersonPresent : Prop)
    (h : smithPresentAfterJonesLeft ∧ jonesLeftAfterAndersonPresent)
    (hNot : ¬ smithPresentAfterAndersonPresent) :
    (smithPresentAfterJonesLeft ∧ jonesLeftAfterAndersonPresent) ∧
      ¬ smithPresentAfterAndersonPresent := ⟨h, hNot⟩

theorem fracas_263_dir2
    (smithPresentAfterJonesLeft jonesLeftAfterAndersonPresent
      smithPresentAfterAndersonPresent : Prop)
    (h : smithPresentAfterJonesLeft ∧ jonesLeftAfterAndersonPresent)
    (hYes : smithPresentAfterAndersonPresent) :
    (smithPresentAfterJonesLeft ∧ jonesLeftAfterAndersonPresent) ∧
      smithPresentAfterAndersonPresent := ⟨h, hYes⟩

end P263

/-! ## Problems 264–268: before/after are exact converses -/

section P264
variable (tSmith tJones : Nat)

theorem fracas_264 : tSmith < tJones → tJones > tSmith := by omega

end P264

section P265
variable (tSmith tJones : Nat)

theorem fracas_265 : tSmith > tJones → tJones < tSmith := by omega

end P265

section P266
variable (tSmith tJones : Nat)

theorem fracas_266 : tJones < tSmith → tSmith > tJones := by omega

end P266

section P267
variable (tJones tSmith : Nat)

theorem fracas_267 : tJones < tSmith → tSmith > tJones := by omega

end P267

section P268
variable (tJones tSmith : Nat)

theorem fracas_268 : tJones > tSmith → tSmith < tJones := by omega

end P268

/-! ## Problem 269: a bare repeated activity, unknown -/

section P269

/-- "Smith swam" (bare activity) mentioned twice need not denote the
same swimming occasion each time, unlike 270's telic "swam to the
shore" — so the converse of before/after can't be assumed to transfer.
Opaque facts (not real timestamps) for the same reason as 263: real
`Nat` `<`/`>` would make the converse trivially provable, which is
exactly what this problem's `.unknown` gold answer says doesn't hold. -/
theorem fracas_269_dir1 (smithSwam jonesSwam smithSwamBeforeJonesSwam
      jonesSwamAfterSmithSwam : Prop)
    (h : smithSwam ∧ jonesSwam ∧ smithSwamBeforeJonesSwam)
    (hNot : ¬ jonesSwamAfterSmithSwam) :
    (smithSwam ∧ jonesSwam ∧ smithSwamBeforeJonesSwam) ∧ ¬ jonesSwamAfterSmithSwam :=
  ⟨h, hNot⟩

theorem fracas_269_dir2 (smithSwam jonesSwam smithSwamBeforeJonesSwam
      jonesSwamAfterSmithSwam : Prop)
    (h : smithSwam ∧ jonesSwam ∧ smithSwamBeforeJonesSwam)
    (hYes : jonesSwamAfterSmithSwam) :
    (smithSwam ∧ jonesSwam ∧ smithSwamBeforeJonesSwam) ∧ jonesSwamAfterSmithSwam :=
  ⟨h, hYes⟩

end P269

/-! ## Problem 270: a telic accomplishment, the converse holds -/

section P270
variable (tSmith tJones : Nat)

theorem fracas_270 : tSmith < tJones → tJones > tSmith := by omega

end P270

/-! ## Problems 271–274: bare repeated states/activities, unknown -/

section P271

/-- "Smith was present. Jones was present. Smith was present after Jones
was present. Was Jones present before Smith was present?" — a bare
repeated-state chain, same independence shape as 263/269 and the same
reason real timestamps would be unsound here (state "after"/"before"
don't compose like achievement timestamps do). -/
theorem fracas_271_dir1 (smithPresent jonesPresent smithPresentAfterJonesPresent
      jonesPresentBeforeSmithPresent : Prop)
    (h : smithPresent ∧ jonesPresent ∧ smithPresentAfterJonesPresent)
    (hNot : ¬ jonesPresentBeforeSmithPresent) :
    (smithPresent ∧ jonesPresent ∧ smithPresentAfterJonesPresent) ∧
      ¬ jonesPresentBeforeSmithPresent := ⟨h, hNot⟩

theorem fracas_271_dir2 (smithPresent jonesPresent smithPresentAfterJonesPresent
      jonesPresentBeforeSmithPresent : Prop)
    (h : smithPresent ∧ jonesPresent ∧ smithPresentAfterJonesPresent)
    (hYes : jonesPresentBeforeSmithPresent) :
    (smithPresent ∧ jonesPresent ∧ smithPresentAfterJonesPresent) ∧
      jonesPresentBeforeSmithPresent := ⟨h, hYes⟩

end P271

section P272

/-- The reverse pairing from 271: "Smith was present before Jones was
present. Was Jones present after Smith was present?" -/
theorem fracas_272_dir1 (smithPresent jonesPresent smithPresentBeforeJonesPresent
      jonesPresentAfterSmithPresent : Prop)
    (h : smithPresent ∧ jonesPresent ∧ smithPresentBeforeJonesPresent)
    (hNot : ¬ jonesPresentAfterSmithPresent) :
    (smithPresent ∧ jonesPresent ∧ smithPresentBeforeJonesPresent) ∧
      ¬ jonesPresentAfterSmithPresent := ⟨h, hNot⟩

theorem fracas_272_dir2 (smithPresent jonesPresent smithPresentBeforeJonesPresent
      jonesPresentAfterSmithPresent : Prop)
    (h : smithPresent ∧ jonesPresent ∧ smithPresentBeforeJonesPresent)
    (hYes : jonesPresentAfterSmithPresent) :
    (smithPresent ∧ jonesPresent ∧ smithPresentBeforeJonesPresent) ∧
      jonesPresentAfterSmithPresent := ⟨h, hYes⟩

end P272

section P273

/-- Same shape as 271, over "writing a report" (another unbounded
activity) instead of "present". -/
theorem fracas_273_dir1 (smithWritingReport jonesWritingReport
      smithWritingBeforeJonesWriting jonesWritingAfterSmithWriting : Prop)
    (h : smithWritingReport ∧ jonesWritingReport ∧ smithWritingBeforeJonesWriting)
    (hNot : ¬ jonesWritingAfterSmithWriting) :
    (smithWritingReport ∧ jonesWritingReport ∧ smithWritingBeforeJonesWriting) ∧
      ¬ jonesWritingAfterSmithWriting := ⟨h, hNot⟩

theorem fracas_273_dir2 (smithWritingReport jonesWritingReport
      smithWritingBeforeJonesWriting jonesWritingAfterSmithWriting : Prop)
    (h : smithWritingReport ∧ jonesWritingReport ∧ smithWritingBeforeJonesWriting)
    (hYes : jonesWritingAfterSmithWriting) :
    (smithWritingReport ∧ jonesWritingReport ∧ smithWritingBeforeJonesWriting) ∧
      jonesWritingAfterSmithWriting := ⟨h, hYes⟩

end P273

section P274

/-- The reverse pairing from 273. -/
theorem fracas_274_dir1 (smithWritingReport jonesWritingReport
      smithWritingAfterJonesWriting jonesWritingBeforeSmithWriting : Prop)
    (h : smithWritingReport ∧ jonesWritingReport ∧ smithWritingAfterJonesWriting)
    (hNot : ¬ jonesWritingBeforeSmithWriting) :
    (smithWritingReport ∧ jonesWritingReport ∧ smithWritingAfterJonesWriting) ∧
      ¬ jonesWritingBeforeSmithWriting := ⟨h, hNot⟩

theorem fracas_274_dir2 (smithWritingReport jonesWritingReport
      smithWritingAfterJonesWriting jonesWritingBeforeSmithWriting : Prop)
    (h : smithWritingReport ∧ jonesWritingReport ∧ smithWritingAfterJonesWriting)
    (hYes : jonesWritingBeforeSmithWriting) :
    (smithWritingReport ∧ jonesWritingReport ∧ smithWritingAfterJonesWriting) ∧
      jonesWritingBeforeSmithWriting := ⟨h, hYes⟩

end P274

/-! ## Problem 275: "before" is non-factive about its embedded clause -/

section P275

/-- "Smith left the meeting before he lost his temper" doesn't assert
that he ever *did* lose his temper — "before" locates a (possibly
counterfactual) reference point without committing to it, unlike
"after". -/
theorem fracas_275_dir1 (smithLeftBeforeLostTemper smithLostTemper : Prop)
    (h : smithLeftBeforeLostTemper) (hNot : ¬ smithLostTemper) :
    smithLeftBeforeLostTemper ∧ ¬ smithLostTemper := ⟨h, hNot⟩

theorem fracas_275_dir2 (smithLeftBeforeLostTemper smithLostTemper : Prop)
    (h : smithLeftBeforeLostTemper) (hYes : smithLostTemper) :
    smithLeftBeforeLostTemper ∧ smithLostTemper := ⟨h, hYes⟩

end P275

end FraCaS.Section7
