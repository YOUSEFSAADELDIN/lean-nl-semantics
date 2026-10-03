import LeanNLSemantics.FraCaS.Section7.Temporal

/-!
# FraCaS Section 7, problems 311–325 (final batch)

Ordering already given by "then" (311), universal instantiation over
delivery events, both affirmative and negative (312/313), interval
continuity arithmetic (314/315), a completion-time argument by
contradiction (316), a serialized-events cardinality bound (317), a
duration inequality (318), additive interval arithmetic (319/321),
factive attitude verbs (320/322), and order-theoretic reasoning about
"stops"/"continues" "the moment" a threshold is reached (323/324), plus
existential transfer for "discover" (325).
-/

namespace FraCaS.Section7

/-! ## Problem 311: ordering already given by "then" -/

section P311
variable (leftHouse taxiToStation : Nat)

theorem fracas_311 : leftHouse < taxiToStation → leftHouse < taxiToStation := id

end P311

/-! ## Problems 312/313: a universal delivery habit, affirmative and negative -/

section P312
variable (delivered late : Nat → Prop)

theorem fracas_312 :
    (∀ d, delivered d → late d) → delivered 1993 → late 1993 :=
  fun h hd => h 1993 hd

end P312

section P313
variable (delivered late : Nat → Prop)

theorem fracas_313 :
    (∀ d, delivered d → ¬ late d) → delivered 1993 → ¬ late 1993 :=
  fun h hd => h 1993 hd

end P313

/-! ## Problem 314: interval continuity, "still in Paris" -/

section P314
variable (inParis : Nat → Prop)

theorem fracas_314 :
    (∀ d, 5 ≤ d → d ≤ 15 → inParis d) → inParis 7 :=
  fun h => h 7 (by omega) (by omega)

end P314

/-! ## Problem 315: interval continuity, "travelling for three days" -/

section P315
variable (travelling : Nat → Prop) (arrivalDay : Nat)

theorem fracas_315 :
    arrivalDay ≥ 3 →
    (∀ d, arrivalDay - 3 ≤ d → d < arrivalDay → travelling d) →
    travelling (arrivalDay - 1) :=
  fun hge h => h (arrivalDay - 1) (by omega) (by omega)

end P315

/-! ## Problem 316: a completion time bounded by contradiction -/

section P316
variable (employed unemployedAt : Nat → Prop) (graduationTime : Nat)

theorem fracas_316 :
    (∀ t, graduationTime ≤ t → employed t) →
    (∀ t, unemployedAt t → ¬ employed t) →
    (∃ t, unemployedAt t) →
    ∃ t, unemployedAt t ∧ t < graduationTime := by
  intro hemp hcompl hex
  obtain ⟨t0, ht0⟩ := hex
  refine ⟨t0, ht0, ?_⟩
  by_contra hcon
  push_neg at hcon
  exact hcompl t0 ht0 (hemp t0 hcon)

end P316

/-! ## Problem 317: sixteen serialized events, each at least half a day -/

section P317
variable (totalHalfDays minPerRep : Nat)

theorem fracas_317 :
    minPerRep ≥ 1 → totalHalfDays ≥ 16 * minPerRep → totalHalfDays > 14 := by
  intro hmin htot
  omega

end P317

/-! ## Problem 318: a strict duration inequality -/

section P318
variable (jonesStart jonesEnd maryStart maryEnd : Nat)

theorem fracas_318 :
    jonesStart < maryStart → maryStart < maryEnd → maryEnd < jonesEnd →
    ¬ (maryEnd - maryStart = jonesEnd - jonesStart) := by
  intro h1 h2 h3
  omega

end P318

/-! ## Problem 319: additive interval arithmetic -/

section P319
variable (yearsPrev yearsPresent : Nat)

theorem fracas_319 : yearsPrev = 8 → yearsPresent > 10 → yearsPrev + yearsPresent ≥ 15 := by
  intro h1 h2
  omega

end P319

/-! ## Problem 320: a factive attitude verb -/

section P320
variable (knewNeverAllowed neverAllowedToWriteMemoirs : Prop)

/-- "Knew that P" is factive: an assumed fact connecting "Jones knew he
would never be allowed to write his memoirs" to the complement itself,
plus modus ponens — the same shape as `fracas_334`'s own "knew", not a
bare `id` restating the complement as itself (which would leave "knew"
unmodeled entirely, no different from premise and hypothesis being
literally the same Prop). -/
theorem fracas_320 :
    (knewNeverAllowed → neverAllowedToWriteMemoirs) → knewNeverAllowed →
      neverAllowedToWriteMemoirs :=
  fun hfact hknew => hfact hknew

end P320

/-! ## Problem 321: additive interval arithmetic -/

section P321
variable (pastVisits futureVisits : Nat)

theorem fracas_321 :
    pastVisits = 2 → futureVisits = 2 → pastVisits + futureVisits ≥ 4 := by
  intro h1 h2
  omega

end P321

/-! ## Problem 322: a factive attitude verb, through a conjunction -/

section P322
variable (knewFuture discovers furious : Prop)

/-- Same factivity of "knew" as 320 (an assumed fact plus modus ponens,
not a bare `id`), carried through the embedded conjunction: "I knew
that [she would discover ... and be furious]" entails the conjunction
itself. -/
theorem fracas_322 :
    (knewFuture → (discovers ∧ furious)) → knewFuture → (discovers ∧ furious) :=
  fun hfact hknew => hfact hknew

end P322

/-! ## Problem 323: "stops the moment he is broke" — an equality by antisymmetry -/

section P323
variable {A : Type*} (stopTime brokeTime : A → Nat)

theorem fracas_323 :
    (∀ x, stopTime x ≥ brokeTime x) → (∀ x, stopTime x ≤ brokeTime x) →
    ∀ x, stopTime x = brokeTime x :=
  fun h1 h2 x => le_antisymm (h2 x) (h1 x)

end P323

/-! ## Problem 324: "continues until he is broke" -/

section P324
variable {A : Type*} (stopTime brokeTime : A → Nat)

theorem fracas_324 :
    (∀ x, stopTime x ≥ brokeTime x) → ∀ x t, t < brokeTime x → t < stopTime x :=
  fun h x t ht => by have := h x; omega

end P324

/-! ## Problem 325: existential transfer for "discover" -/

section P325
variable {A : Type*} (knowsWasAsleep discovers : A → Prop)

theorem fracas_325 :
    (∀ x, knowsWasAsleep x → discovers x) → (∃ x, knowsWasAsleep x) → ∃ x, discovers x :=
  fun h hex => hex.imp h

end P325

end FraCaS.Section7
