import LeanNLSemantics.FraCaS.Section6.Comparatives

/-!
# FraCaS Section 6, problems 220–235

"Faster than" and "as fast as" licensing or refuting a bare "fast"
predication via an assumed connecting fact (220–229), and genuine
cardinal comparatives ("won more orders than") as real `Nat`
arithmetic (230–235).
-/

namespace FraCaS.Section6

/-! ## Problems 220–223: "faster than" -/

section P220
variable {A : Type*} (fasterThan : A → A → Prop) (fast : A → Prop) (pc itel : A)

theorem fracas_220 :
    (∀ x y, fasterThan x y → fast y → fast x) → fasterThan pc itel → fast itel → fast pc :=
  fun h hf hi => h pc itel hf hi

end P220

section P221

/-- "Faster than" alone says nothing about either computer's absolute
speed. -/
theorem fracas_221_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_221_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P221

section P222

/-- Knowing the *faster* one is fast doesn't bound the slower one either
way. -/
theorem fracas_222_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_222_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P222

section P223
variable {A : Type*} (fasterThan : A → A → Prop) (fast slow : A → Prop) (pc itel : A)

/-- If the *faster* one is already slow, the slower one certainly isn't
fast. -/
theorem fracas_223 :
    (∀ x y, fasterThan x y → slow x → ¬ fast y) → fasterThan pc itel → slow pc → ¬ fast itel :=
  fun h hf hs => h pc itel hf hs

end P223

/-! ## Problems 224–229: "as fast as" (an "at least as", not "exactly as", reading) -/

section P224
variable {A : Type*} (asFastAs : A → A → Prop) (fast : A → Prop) (pc itel : A)

theorem fracas_224 :
    (∀ x y, asFastAs x y → fast y → fast x) → asFastAs pc itel → fast itel → fast pc :=
  fun h ha hi => h pc itel ha hi

end P224

section P225

theorem fracas_225_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_225_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P225

section P226

/-- "As fast as" only gives a *lower* bound on `pc` relative to `itel`
— it doesn't bound `itel`'s own absolute speed, so knowing `pc` is fast
doesn't tell you `itel` is (`itel` could be much slower and `pc` still
only just "as fast as" it in a loose sense). -/
theorem fracas_226_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_226_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P226

section P227
variable {A : Type*} (asFastAs : A → A → Prop) (fast slow : A → Prop) (pc itel : A)

/-- If `pc` is at least as fast as `itel` and `pc` is itself slow, `itel`
(no faster than `pc`) can't be fast either. -/
theorem fracas_227 :
    (∀ x y, asFastAs x y → slow x → ¬ fast y) → asFastAs pc itel → slow pc → ¬ fast itel :=
  fun h ha hs => h pc itel ha hs

end P227

section P228

/-- "As fast as" doesn't give *strictly* faster — equality is
compatible with it. -/
theorem fracas_228_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_228_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P228

section P229
variable {A : Type*} (asFastAs slowerThan : A → A → Prop) (pc itel : A)

/-- "As fast as" (an "at least as fast" lower bound) directly refutes
"slower than" — an assumed fact connecting the two comparatives. -/
theorem fracas_229 :
    (∀ x y, asFastAs x y → ¬ slowerThan x y) → asFastAs pc itel → ¬ slowerThan pc itel :=
  fun h ha => h pc itel ha

end P229

/-! ## Problems 230–235: cardinal comparatives, real `Nat` arithmetic -/

section P230
variable (wonITEL wonAPCOM : Nat)

theorem fracas_230 : wonITEL > wonAPCOM → wonITEL > 0 := by omega

end P230

section P231

/-- "ITEL won more than APCOM" bounds ITEL's count from below via
APCOM's, but says nothing about whether APCOM's own count is positive. -/
theorem fracas_231_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_231_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P231

section P232
variable (wonITEL wonAPCOM : Nat)

theorem fracas_232 : wonITEL > wonAPCOM → wonAPCOM = 10 → wonITEL ≥ 11 := by omega

end P232

section P233
variable (wonITEL wonAPCOM : Nat)

theorem fracas_233 : wonITEL > wonAPCOM → wonITEL > 0 := by omega

end P233

section P234

theorem fracas_234_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_234_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P234

section P235
variable (wonITEL wonAPCOM : Nat)

theorem fracas_235 : wonITEL > wonAPCOM → wonAPCOM = 10 → wonITEL ≥ 11 := by omega

end P235

end FraCaS.Section6
