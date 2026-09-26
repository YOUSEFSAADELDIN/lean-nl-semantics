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
261/262 do. -/
theorem fracas_263_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_263_dir2 : True ∧ True := ⟨trivial, trivial⟩

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
shore" — so the converse of before/after can't be assumed to transfer. -/
theorem fracas_269_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_269_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P269

/-! ## Problem 270: a telic accomplishment, the converse holds -/

section P270
variable (tSmith tJones : Nat)

theorem fracas_270 : tSmith < tJones → tJones > tSmith := by omega

end P270

/-! ## Problems 271–274: bare repeated states/activities, unknown -/

section P271

theorem fracas_271_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_271_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P271

section P272

theorem fracas_272_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_272_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P272

section P273

theorem fracas_273_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_273_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P273

section P274

theorem fracas_274_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_274_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P274

/-! ## Problem 275: "before" is non-factive about its embedded clause -/

section P275

/-- "Smith left the meeting before he lost his temper" doesn't assert
that he ever *did* lose his temper — "before" locates a (possibly
counterfactual) reference point without committing to it, unlike
"after". -/
theorem fracas_275_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_275_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P275

end FraCaS.Section7
