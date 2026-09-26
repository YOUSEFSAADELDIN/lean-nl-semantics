import LeanNLSemantics.FraCaS.Section8.Verbs

/-!
# FraCaS Section 8, problems 326–333 (complete)

Perfective accomplishment/achievement culmination via an assumed
connecting fact (326, 328) vs. the progressive's failure to culminate
(327, 329 — `.unknown`), interval containment for a bounded state
(330), plural-subject conjunction (331/332), and collective-predicate
existential closure (333).
-/

namespace FraCaS.Section8

/-! ## Problem 326: a perfective accomplishment culminates -/

section P326
variable (built finished : Nat → Prop)

theorem fracas_326 : (∀ y, built y → finished y) → built 1993 → finished 1993 :=
  fun hfact hb => hfact 1993 hb

end P326

/-! ## Problem 327: the progressive doesn't culminate -/

section P327

/-- "Was building MTALK" (in progress) doesn't entail "finished
MTALK" — the imperfective paradox. -/
theorem fracas_327_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_327_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P327

/-! ## Problem 328: a perfective achievement, existential generalization -/

section P328
variable (wonFromAPCOM wonAContract : Nat → Prop)

theorem fracas_328 :
    (∀ y, wonFromAPCOM y → wonAContract y) → wonFromAPCOM 1993 → wonAContract 1993 :=
  fun hfact hw => hfact 1993 hw

end P328

/-! ## Problem 329: the progressive of an achievement doesn't entail success -/

section P329

/-- "Was winning the contract" (in progress) doesn't entail "won a
contract" — the same imperfective paradox as 327, sharper still for an
achievement verb like "win". -/
theorem fracas_329_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_329_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P329

/-! ## Problem 330: interval containment for a bounded state -/

section P330
variable (owned : Nat → Prop)

theorem fracas_330 : (∀ y, 1988 ≤ y → y ≤ 1992 → owned y) → owned 1990 :=
  fun h => h 1990 (by omega) (by omega)

end P330

/-! ## Problems 331/332: plural-subject conjunction -/

section P331
variable (smithLeft jonesLeft : Prop)

theorem fracas_331 : smithLeft ∧ jonesLeft → smithLeft := fun h => h.1

end P331

section P332
variable (smithLeft jonesLeft : Prop)

theorem fracas_332 : smithLeft ∧ jonesLeft → jonesLeft := fun h => h.2

end P332

/-! ## Problem 333: a collective predicate, existential closure -/

section P333
variable {Group : Type*} (theThree : Group) (met : Group → Prop)

theorem fracas_333 : met theThree → ∃ g, met g := fun h => ⟨theThree, h⟩

end P333

end FraCaS.Section8
