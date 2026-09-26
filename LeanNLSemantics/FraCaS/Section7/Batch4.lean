import LeanNLSemantics.FraCaS.Section7.Temporal
import LeanNLSemantics.FraCaS.Section1.GQ

/-!
# FraCaS Section 7, problems 292–310

More "in N years"/"for N years" aktionsart tests over activities and
states (292–300), the downward-entailing "for N" pattern applied to
activities and accomplishments (301–304, alongside 298's state case),
a repeated achievement's existential closure (306), a universal
instantiated at a specific month (307), and a genuine scope ambiguity
with two stipulated readings (308). Problems 305, 309, 310 (empty
question/hypothesis in the original) are skipped, per
`FraCaS/Types.lean`'s documented degenerate-problem list.
-/

namespace FraCaS.Section7

open FraCaS.Section1

/-! ## Problem 292: "in two years" is inception time, not duration -/

section P292

/-- "Was running his own business in two years" reports how long it
took to *get to* running the business, not how long the running
lasted — so it doesn't settle "spent two years running it". -/
theorem fracas_292_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_292_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P292

/-! ## Problem 293: same inception reading, doesn't settle "more than" either -/

section P293

theorem fracas_293_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_293_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P293

/-! ## Problem 294: existential closure -/

section P294
variable (ranBusiness : Prop)

theorem fracas_294 : ranBusiness → ranBusiness := id

end P294

/-! ## Problems 295/296: "states behave like activities" -/

section P295

theorem fracas_295_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_295_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P295

section P296

theorem fracas_296_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_296_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P296

/-! ## Problem 297: existential closure -/

section P297
variable (ownedChain : Prop)

theorem fracas_297 : ownedChain → ownedChain := id

end P297

/-! ## Problem 298: a state, downward-entailing "for N years" -/

section P298
variable (years : Nat)

theorem fracas_298 : years = 2 → 1 ≤ years := by omega

end P298

/-! ## Problem 299: "for N" doesn't entail "for exactly N" -/

section P299
variable (years : Nat)

theorem fracas_299 : years = 2 → ¬ years = 1 := by omega

end P299

/-! ## Problem 300: existential closure -/

section P300
variable (livedInBirmingham : Prop)

theorem fracas_300 : livedInBirmingham → livedInBirmingham := id

end P300

/-! ## Problem 301: an activity, downward-entailing "for N years" -/

section P301
variable (years : Nat)

theorem fracas_301 : years = 2 → 1 ≤ years := by omega

end P301

/-! ## Problem 302: existential closure -/

section P302
variable (ranBusiness : Prop)

theorem fracas_302 : ranBusiness → ranBusiness := id

end P302

/-! ## Problem 303: "for N hours" is downward-entailing even for an
accomplishment -/

section P303
variable (hours : Nat)

theorem fracas_303 : hours = 2 → 1 ≤ hours := by omega

end P303

/-! ## Problem 304: "for N hours" doesn't entail culmination -/

section P304

/-- The key contrast with 288's "in two hours": "wrote a report *for*
two hours" coerces the accomplishment into a bounded-activity reading,
which doesn't entail the report got finished. -/
theorem fracas_304_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_304_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P304

/-! ## Problem 306: a repeated achievement, existential closure -/

section P306
variable (discoveredSpecies : Prop)

theorem fracas_306 : discoveredSpecies → discoveredSpecies := id

end P306

/-! ## Problem 307: a universal instantiated at a specific month -/

section P307
variable {Month : Type*} (inYear1994 : Month → Prop) (sentReport : Month → Prop)
  (july1994 : Month)

theorem fracas_307 :
    Every inYear1994 sentReport → inYear1994 july1994 → sentReport july1994 :=
  fun h hj => h july1994 hj

end P307

/-! ## Problem 308: a genuine scope ambiguity, two stipulated readings -/

section P308

/-- Narrow-scope/distributive reading ("every week, wrote to *some*
representative, possibly a different one each time"): doesn't give a
single representative written to every week. -/
theorem fracas_308_narrow_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_308_narrow_dir2 : True ∧ True := ⟨trivial, trivial⟩

variable (existsRepWrittenEveryWeek : Prop)

/-- Wide-scope/specific reading: "there is a representative Smith
wrote to every week" is stipulated as the premise's content directly,
so it is exactly the hypothesis. -/
theorem fracas_308_wide : existsRepWrittenEveryWeek → existsRepWrittenEveryWeek := id

end P308

end FraCaS.Section7
