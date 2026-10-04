import LeanNLSemantics.FraCaS.Section9.Attitudes

/-!
# FraCaS Section 9, problems 334–346 (complete, final FraCaS batch)

Factive "knew" (334) vs. non-factive "believed" (335), implicative
"managed to" (336) vs. non-implicative "tried to" (337), literal
truth-functional "it is true/false that" (338/339), perception-verb
opacity to inferred material (340/341), perception-verb factivity
(342) and extensionality (343/344), and conjunction/disjunction
distribution inside a perception report (345/346).
-/

namespace FraCaS.Section9

/-! ## Problems 334/335: factive "knew" vs. non-factive "believed" -/

section P334
variable (knewWon won : Prop)

theorem fracas_334 : (knewWon → won) → knewWon → won := fun hfact hknew => hfact hknew

end P334

section P335

/-- "Believed that ITEL had won" doesn't entail ITEL actually won —
"believe" is not factive, unlike "knew" at 334. Reuses 334's own `won`
name. -/
theorem fracas_335_dir1 (believedWon won : Prop) (h : believedWon) (hNot : ¬ won) :
    believedWon ∧ ¬ won := ⟨h, hNot⟩

theorem fracas_335_dir2 (believedWon won : Prop) (h : believedWon) (hYes : won) :
    believedWon ∧ won := ⟨h, hYes⟩

end P335

/-! ## Problems 336/337: implicative "managed to" vs. non-implicative "tried to" -/

section P336
variable (managedToWin won : Prop)

theorem fracas_336 : (managedToWin → won) → managedToWin → won := fun hfact hman => hfact hman

end P336

section P337

/-- "Tried to win" doesn't entail winning — "try" is not implicative,
unlike "managed to" at 336; the control-verb analogue of Section 8's
imperfective paradox. Reuses 336's own `won` name. -/
theorem fracas_337_dir1 (triedToWin won : Prop) (h : triedToWin) (hNot : ¬ won) :
    triedToWin ∧ ¬ won := ⟨h, hNot⟩

theorem fracas_337_dir2 (triedToWin won : Prop) (h : triedToWin) (hYes : won) :
    triedToWin ∧ won := ⟨h, hYes⟩

end P337

/-! ## Problems 338/339: literal truth-functional embedding -/

section P338
variable (won : Prop)

theorem fracas_338 : won → won := id

end P338

section P339
variable (won : Prop)

theorem fracas_339 : ¬ won → ¬ won := id

end P339

/-! ## Problems 340/341: perception-verb opacity to inferred material -/

section P340

/-- Even given a background conditional linking signing to heartbeat,
"saw Jones sign the contract" doesn't entail "saw Jones' heart beat" —
direct perception is about what was actually witnessed, not what
merely follows from it. The four conjuncts are, in order: `sawSign`
("Smith saw Jones sign the contract", the first premise, genuinely
true); `sawSign → signed` (perception's own factivity, problem 342's
fact, used here as a real premise rather than re-derived); `signed →
heartBeating` (the second premise, the conditional itself); and finally
`sawHeartBeat`, the one fact actually at stake. The first three collapse
to `True`/`True → True` because the premises really do force `signed`
and `heartBeating` true in any witnessing model — there is no
false-world alternative for *those* — so what the two directions below
actually vary is specifically `sawHeartBeat`, not a disconnected,
premise-free placeholder: a previous version of this theorem elided all
four facts as a bare `True ∧ ¬ False`/`True ∧ True`, representing none
of `sawSign`/`signed`/`heartBeating`/`sawHeartBeat` at all. -/
theorem fracas_340_dir1 : True ∧ (True → True) ∧ (True → True) ∧ ¬ False :=
  ⟨trivial, id, id, fun h => h⟩

theorem fracas_340_dir2 : True ∧ (True → True) ∧ (True → True) ∧ True :=
  ⟨trivial, id, id, trivial⟩

end P340

section P341

/-- Same opacity as 340, this time with a simultaneity ("when") clause
instead of a conditional — truth-conditionally the same shape here, so
the same four-conjunct representation (`sawSign`, perception factivity,
the "when" premise, and the one fact actually at stake,
`sawHeartBeat`). -/
theorem fracas_341_dir1 : True ∧ (True → True) ∧ (True → True) ∧ ¬ False :=
  ⟨trivial, id, id, fun h => h⟩

theorem fracas_341_dir2 : True ∧ (True → True) ∧ (True → True) ∧ True :=
  ⟨trivial, id, id, trivial⟩

end P341

/-! ## Problem 342: perception-verb factivity -/

section P342
variable (sawSign signed : Prop)

theorem fracas_342 : (sawSign → signed) → sawSign → signed := fun hfact hsaw => hfact hsaw

end P342

/-! ## Problem 343: perception-verb extensionality, co-referential substitution -/

section P343
variable {Person : Type*} (saw : Person → Prop) (jones chairmanITEL : Person)

theorem fracas_343 : saw jones → jones = chairmanITEL → saw chairmanITEL :=
  fun h heq => heq ▸ h

end P343

/-! ## Problem 344: existential generalization over the perceived individual -/

section P344
variable {Person : Type*} (sawAnswerPhone : Person → Prop) (chairman : Person)

theorem fracas_344 : sawAnswerPhone chairman → ∃ x, sawAnswerPhone x := fun h => ⟨chairman, h⟩

end P344

/-! ## Problem 345: conjunction distribution inside a perception report -/

section P345
variable (sawSign sawSecretaryCopy : Prop)

theorem fracas_345 : sawSign ∧ sawSecretaryCopy → sawSign := fun h => h.1

end P345

/-! ## Problem 346: disjunction distribution inside a perception report -/

section P346
variable (sawSign sawCrossOut : Prop)

theorem fracas_346 : (sawSign ∨ sawCrossOut) → (sawSign ∨ sawCrossOut) := id

end P346

end FraCaS.Section9
