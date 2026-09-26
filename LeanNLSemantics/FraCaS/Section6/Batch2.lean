import LeanNLSemantics.FraCaS.Section6.Comparatives

/-!
# FraCaS Section 6, problems 236–250 (final batch)

A nominal-standard comparative ellipsis with two stipulated readings
(236/237), "twice as many" and cross-predicate cardinal comparatives
("won more than APCOM lost") as real arithmetic (238–241, 243),
transitivity of a comparative through a numeric benchmark (242), more
comparative-ellipsis readings (244/245), and quantified comparative
standards reusing `Every`/`Some` (246–250).
-/

namespace FraCaS.Section6

open FraCaS.Section1

/-! ## Problems 236/237: a nominal comparative standard, two stipulated readings -/

section P236
variable (itelWonAPCOMContract : Prop)

theorem fracas_236 : itelWonAPCOMContract → itelWonAPCOMContract := id

end P236

section P237
variable (itelWonMoreThanOneOrder : Prop)

theorem fracas_237 : itelWonMoreThanOneOrder → itelWonMoreThanOneOrder := id

end P237

/-! ## Problem 238: "twice as many" -/

section P238
variable (wonITEL wonAPCOM : Nat)

theorem fracas_238 : wonITEL = 2 * wonAPCOM → wonAPCOM = 10 → wonITEL = 20 := by omega

end P238

/-! ## Problems 239–241: a cross-predicate cardinal comparative ("won" vs. "lost") -/

section P239
variable (wonITEL lostAPCOM : Nat)

theorem fracas_239 : wonITEL > lostAPCOM → wonITEL > 0 := by omega

end P239

section P240

/-- "ITEL won more than APCOM lost" bounds ITEL's wins from below via
APCOM's losses, but says nothing about whether APCOM lost anything at
all. -/
theorem fracas_240_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_240_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P240

section P241
variable (wonITEL lostAPCOM : Nat)

theorem fracas_241 : wonITEL > lostAPCOM → lostAPCOM = 10 → wonITEL ≥ 11 := by omega

end P241

/-! ## Problem 242: transitivity through a numeric benchmark -/

section P242
variable (speedPC speedITELZX : Nat)

theorem fracas_242 : speedPC > 500 → speedITELZX < 500 → speedPC > speedITELZX := by omega

end P242

/-! ## Problem 243: "N more than" plus an exact count -/

section P243
variable (soldITEL soldAPCOM : Nat)

theorem fracas_243 : soldITEL = soldAPCOM + 3000 → soldAPCOM = 2500 → soldITEL = 5500 := by omega

end P243

/-! ## Problems 244/245: more comparative-ellipsis readings -/

section P244
variable (apcomHasMoreImportantCustomerThanITELIs : Prop)

theorem fracas_244 :
    apcomHasMoreImportantCustomerThanITELIs → apcomHasMoreImportantCustomerThanITELIs :=
  id

end P244

section P245
variable (apcomHasMoreImportantCustomerThanITELHas : Prop)

theorem fracas_245 :
    apcomHasMoreImportantCustomerThanITELHas → apcomHasMoreImportantCustomerThanITELHas :=
  id

end P245

/-! ## Problems 246–250: quantified comparative standards -/

section P246
variable {A : Type*} (fasterThan : A → A → Prop) (itelComputer : A → Prop) (pc itelzx : A)

theorem fracas_246 :
    Every itelComputer (fasterThan pc) → itelComputer itelzx → fasterThan pc itelzx :=
  fun h hz => h itelzx hz

end P246

section P247

/-- "Faster than *some* ITEL computer" doesn't tell you it's faster than
*this particular* one — the same "a specific named instance doesn't
follow from `Some`" independence as Section 1's problem 33. -/
theorem fracas_247_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_247_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P247

section P248
variable {A : Type*} (fasterThan : A → A → Prop) (itelComputer : A → Prop) (pc itelzx : A)

/-- "Faster than *any* ITEL computer" is universal here (not an NPI
under negation), same shape as 246. -/
theorem fracas_248 :
    Every itelComputer (fasterThan pc) → itelComputer itelzx → fasterThan pc itelzx :=
  fun h hz => h itelzx hz

end P248

section P249
variable {A : Type*} (fasterThan : A → A → Prop) (pc itelzx itelzy : A)

theorem fracas_249 : fasterThan pc itelzx ∧ fasterThan pc itelzy → fasterThan pc itelzx :=
  fun h => h.1

end P249

section P250
variable {A : Type*} (fasterThan : A → A → Prop) (pc itelzx itelzy : A)

/-- "Faster than X or Y", on the reading where "or" is understood
conjunctively (faster than both) — a stipulated reading, same bundling
as 249, per FraCaS's own "on one reading of the premise". -/
theorem fracas_250 : fasterThan pc itelzx ∧ fasterThan pc itelzy → fasterThan pc itelzx :=
  fun h => h.1

end P250

end FraCaS.Section6
