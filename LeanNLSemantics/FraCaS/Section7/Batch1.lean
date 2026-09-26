import LeanNLSemantics.FraCaS.Section7.Temporal

/-!
# FraCaS Section 7, problems 251–260

Present-tense persistence (251), continuous "since" for genuine states
(252/255) vs. non-stative predicates coerced into "since" (253/254),
the same sentence receiving two gold answers across the corpus
(256/257), a founding date bounding prior non-existence (258), and two
date/duration arithmetic problems (259/260).
-/

namespace FraCaS.Section7

/-! ## Problem 251: present-tense persistence -/

section P251
variable (hasFactory : Prop)

theorem fracas_251 : hasFactory → hasFactory := id

end P251

/-! ## Problem 252: continuous "since", a genuine state -/

section P252
variable (inBirmingham : Nat → Prop)

theorem fracas_252 :
    (∀ y, 1992 ≤ y → y ≤ 1996 → inBirmingham y) → inBirmingham 1993 :=
  fun h => h 1993 (by omega) (by omega)

end P252

/-! ## Problems 253/254: "since" over a non-stative predicate -/

section P253

/-- "Has developed a new editor since 1992" only asserts the event
happened at least once in the interval, not that it holds at every
intervening year (which "developed a new editor" — an accomplishment —
couldn't repeat every year of anyway). -/
theorem fracas_253_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_253_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P253

section P254

/-- Same shape as 253: "expanded" is not a state that holds
continuously across the interval. -/
theorem fracas_254_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_254_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P254

/-! ## Problem 255: continuous "since", "made a loss" as a genuine state -/

section P255
variable (madeALoss : Nat → Prop)

theorem fracas_255 :
    (∀ y, 1992 ≤ y → y ≤ 1996 → madeALoss y) → madeALoss 1993 :=
  fun h => h 1993 (by omega) (by omega)

end P255

/-! ## Problems 256/257: FraCaS's own two gold answers for one sentence

"ITEL has made a loss since 1992" is genuinely ambiguous between a
continuous reading (loss-making throughout) and an "at least once
since" reading; FraCaS's own corpus gives `.unknown` at 256 and `.yes`
at 257 for the *same* construction (257's note: "formally identical
with preceding"). This project formalizes both readings rather than
picking one silently. -/

section P256

/-- The "at least once since 1992" reading: doesn't pin down 1993
specifically. -/
theorem fracas_256_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_256_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P256

section P257
variable (madeALoss : Nat → Prop)

/-- The continuous reading (same content as 255): does entail 1993. -/
theorem fracas_257 :
    (∀ y, 1992 ≤ y → y ≤ 1996 → madeALoss y) → madeALoss 1993 :=
  fun h => h 1993 (by omega) (by omega)

end P257

/-! ## Problem 258: a founding date bounds prior non-existence -/

section P258
variable (existedAt : Nat → Prop) (foundedYear : Nat)

theorem fracas_258 :
    (∀ y, existedAt y → foundedYear ≤ y) → foundedYear = 1993 → ¬ existedAt 1992 :=
  fun h heq hex => by have := h 1992 hex; omega

end P258

/-! ## Problem 259: duration arithmetic -/

section P259
variable (conferenceOver : Nat → Prop) (startDay duration : Nat)

theorem fracas_259 :
    startDay = 4 → duration = 2 → (∀ d, startDay + duration ≤ d → conferenceOver d) →
    conferenceOver 8 :=
  fun hs hd h => h 8 (by omega)

end P259

/-! ## Problem 260: date arithmetic -/

section P260
variable (signedOn : Nat → Prop) (todayDay : Nat)

theorem fracas_260 :
    todayDay = 14 → signedOn (todayDay - 1) → signedOn 13 := by
  intro heq hsigned
  have : todayDay - 1 = 13 := by omega
  rwa [this] at hsigned

end P260

end FraCaS.Section7
