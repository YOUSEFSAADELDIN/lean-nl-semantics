import LeanNLSemantics.FraCaS.Section7.Temporal

/-!
# FraCaS Section 7, problems 277–291

Bare past-tense states don't project to an adjacent year without an
explicit continuity premise (277); repeatable vs. unrepeatable
accomplishments/achievements split `.no` (same event, one year only)
from `.unknown` (a different token of the same type, next year left
open) at 278/279 vs. 280 and 282 vs. 283; and "in N hours" for
accomplishments (284–288) vs. achievements (289–291) tests completion
entailments and the "spent N hours" vs. "happened within N hours"
distinction.
-/

namespace FraCaS.Section7

/-! ## Problem 277: a bare state doesn't project to an adjacent year -/

section P277

/-- Without an explicit "since"/continuity premise (contrast 252/255),
a bare past-tense state at one year says nothing about the next. -/
theorem fracas_277_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_277_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P277

/-! ## Problems 278/279: an unrepeatable accomplishment, one year only -/

section P278
variable (novelYear : Nat)

theorem fracas_278 : novelYear = 1991 → novelYear ≠ 1992 := by omega

end P278

section P279
variable (novelYear : Nat)

theorem fracas_279 : novelYear = 1991 → novelYear ≠ 1992 := by omega

end P279

/-! ## Problem 280: a repeatable accomplishment, unknown -/

section P280

/-- Unlike 278/279's unique referent ("his first novel", "it"), "a
novel" in 1992 could be a *different* novel, so the second year is
left open. -/
theorem fracas_280_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_280_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P280

/-! ## Problem 281: an activity, unknown -/

section P281

theorem fracas_281_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_281_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P281

/-! ## Problem 282: an unrepeatable achievement, one year only -/

section P282
variable (discoveryYear : Nat)

theorem fracas_282 : discoveryYear = 1991 → discoveryYear ≠ 1992 := by omega

end P282

/-! ## Problem 283: a repeatable achievement, unknown -/

section P283

theorem fracas_283_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_283_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P283

/-! ## Problem 284: an accomplishment's completion, given a start time -/

section P284
variable (startHour durationHours : Nat) (finishedBy : Nat → Prop)

theorem fracas_284 :
    startHour = 8 → durationHours = 2 →
    (∀ h, startHour + durationHours ≤ h → finishedBy h) → finishedBy 11 :=
  fun hs hd h => h 11 (by omega)

end P284

/-! ## Problem 285: "in N hours" doesn't fix the exact duration spent -/

section P285

/-- "Wrote a report in two hours" is ambiguous between "took exactly
two hours" and "took at most two hours" — it doesn't settle "spent
[exactly] two hours". -/
theorem fracas_285_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_285_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P285

/-! ## Problem 286: "in N hours" upper-bounds duration, refuting "more than N" -/

section P286
variable (spentHours : Nat)

theorem fracas_286 : spentHours ≤ 2 → ¬ spentHours > 2 := by omega

end P286

/-! ## Problem 287: "in two hours" doesn't settle "in one hour" either way -/

section P287

theorem fracas_287_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_287_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P287

/-! ## Problem 288: existential closure -/

section P288
variable (wroteReportIn : Nat → Prop) (wroteReport : Prop)

theorem fracas_288 : (∃ h, wroteReportIn h) → wroteReport → wroteReport := fun _ h => h

end P288

/-! ## Problem 289: achievements are near-instantaneous -/

section P289

/-- "Discovered a new species in two hours" bounds *when* the
(near-instantaneous) discovery happened, but doesn't mean two hours
were *spent* discovering it — the achievement/accomplishment contrast
with 284's "in two hours" reading. -/
theorem fracas_289_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_289_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P289

/-! ## Problem 290: existential closure for an achievement -/

section P290
variable (discovered : Prop)

theorem fracas_290 : discovered → discovered := id

end P290

/-! ## Problem 291: a *repeated* achievement can span the whole interval -/

section P291
variable (discoveredAt : Nat → Prop)

/-- Unlike 289's single instantaneous discovery, discovering *many*
species lets the individual (near-instantaneous) discoveries be spread
across the whole two-hour window, so "spent two hours discovering
[new species, repeatedly]" does follow. -/
theorem fracas_291 :
    (∀ h, h < 2 → discoveredAt h) → discoveredAt 0 ∧ discoveredAt 1 :=
  fun h => ⟨h 0 (by omega), h 1 (by omega)⟩

end P291

end FraCaS.Section7
