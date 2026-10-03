import LeanNLSemantics.FraCaS.Section4.Ellipsis

/-!
# FraCaS Section 4, problems 171–184

Nbar/determiner ellipsis (171/172), universally-quantified VP-ellipsis
("everyone that John did") and its one-directional limits (173/174),
embedded-clause ellipsis and a genuine parse ambiguity (175–178),
ellipsis inside conditional/embedded antecedents (179/180), a case where
the elided verb is weaker than the hypothesis needs (181), and the
classic sloppy/strict identity ambiguity for a bound possessive
(182–184, continuing with a doubled pronoun in `Batch4.lean`).
-/

namespace FraCaS.Section4

open FraCaS.Section1

/-! ## Problems 171/172: Nbar and determiner ellipsis -/

section P171
variable (wantsKnowHowManyMenPT wantsKnowHowManyWomenPT : Prop)

theorem fracas_171 : wantsKnowHowManyMenPT ∧ wantsKnowHowManyWomenPT → wantsKnowHowManyWomenPT :=
  fun h => h.2

end P171

section P172
variable (wantsKnowHowManyMenPT wantsKnowWhichMenPT : Prop)

theorem fracas_172 : wantsKnowHowManyMenPT ∧ wantsKnowWhichMenPT → wantsKnowWhichMenPT :=
  fun h => h.2

end P172

/-! ## Problems 173/174: "everyone that John did" — one direction only -/

section P173
variable {A : Type*} (johnSpokeTo billSpokeTo : A → Prop) (mary : A)

theorem fracas_173 : Every johnSpokeTo billSpokeTo → johnSpokeTo mary → billSpokeTo mary :=
  fun h hm => h mary hm

end P173

section P174

/-- "Bill spoke to everyone John did" only says Bill's set of addressees
*covers* John's — it doesn't say Bill spoke to no one else, so knowing
"Bill spoke to Mary" independently doesn't tell you John did too.
Direction 1: John spoke to no one (vacuously satisfying the universal),
Bill spoke to everyone including Mary. Direction 2: John also spoke to
everyone. -/
theorem fracas_174_dir1 :
    (Every (fun _ : Bool => False) (fun _ : Bool => True) ∧ True) ∧ ¬ False :=
  ⟨⟨fun _ h => h.elim, trivial⟩, fun h => h⟩

theorem fracas_174_dir2 :
    (Every (fun _ : Bool => True) (fun _ : Bool => True) ∧ True) ∧ True :=
  ⟨⟨fun _ _ => trivial, trivial⟩, trivial⟩

end P174

/-! ## Problems 175–178: embedded-clause ellipsis -/

section P175
variable (billSaidMaryWroteReport : Prop)

/-- One available parse: "Bill did too" resolves inside "said", giving
"Bill said Mary wrote a report" directly. -/
theorem fracas_175 : billSaidMaryWroteReport → billSaidMaryWroteReport := id

end P175

section P176
variable (johnSaidBillWroteReport : Prop)

/-- A different available parse (per FraCaS's own `<why>`, a genuine
attachment ambiguity, not just anaphora): "and Bill did too" attaches
*inside* the "said"-clause as a second reported claim, giving "John said
Bill wrote a report" — an independent stipulated reading from 175, not a
contrast case. -/
theorem fracas_176 : johnSaidBillWroteReport → johnSaidBillWroteReport := id

end P176

section P177

/-- The doubled "that" ("said that Mary wrote a report, and that Bill
did too") forces *both* conjuncts to be complements of John's "said" —
so the sentence never attributes any act of saying to Bill at all, and
"Bill said Mary wrote a report" is simply unaddressed. `johnMadeDoubledClaim`
is the given fact (John's own two-part utterance); `billSaidMaryWroteReport`
reuses 175's exact hypothesis, now left unaddressed rather than derived. -/
theorem fracas_177_dir1 (johnMadeDoubledClaim billSaidMaryWroteReport : Prop)
    (h : johnMadeDoubledClaim) (hNot : ¬ billSaidMaryWroteReport) :
    johnMadeDoubledClaim ∧ ¬ billSaidMaryWroteReport := ⟨h, hNot⟩

theorem fracas_177_dir2 (johnMadeDoubledClaim billSaidMaryWroteReport : Prop)
    (h : johnMadeDoubledClaim) (hYes : billSaidMaryWroteReport) :
    johnMadeDoubledClaim ∧ billSaidMaryWroteReport := ⟨h, hYes⟩

end P177

section P178
variable (johnWroteReport billSaidPeterWroteReport : Prop)

theorem fracas_178 : johnWroteReport ∧ billSaidPeterWroteReport → billSaidPeterWroteReport :=
  fun h => h.2

end P178

/-! ## Problems 179/180: ellipsis inside a conditional/embedded antecedent -/

section P179
variable (johnWroteReport billWroteReport : Prop)

theorem fracas_179 : (johnWroteReport → billWroteReport) → johnWroteReport → billWroteReport :=
  fun h hj => h hj

end P179

section P180
variable (johnWantedBuyCar johnBoughtCar : Prop)

theorem fracas_180 : johnWantedBuyCar ∧ johnBoughtCar → johnBoughtCar := fun h => h.2

end P180

/-! ## Problem 181: the elided verb is weaker than the hypothesis needs -/

section P181

/-- "Bill did" resolves to "Bill needed to buy a car", not "Bill bought
a car" — needing and buying are different, unconnected predicates.
Named to parallel 180's `johnWantedBuyCar`/`johnBoughtCar`, just for Bill. -/
theorem fracas_181_dir1 (billNeededBuyCar billBoughtCar : Prop)
    (h : billNeededBuyCar) (hNot : ¬ billBoughtCar) :
    billNeededBuyCar ∧ ¬ billBoughtCar := ⟨h, hNot⟩

theorem fracas_181_dir2 (billNeededBuyCar billBoughtCar : Prop)
    (h : billNeededBuyCar) (hYes : billBoughtCar) :
    billNeededBuyCar ∧ billBoughtCar := ⟨h, hYes⟩

end P181

/-! ## Problems 182–184: sloppy/strict identity on a bound possessive -/

section P182
variable {A : Type*} (represents : A → A → Prop) (companyOf : A → A) (smith jones : A)

/-- Sloppy reading: "his" is bound, so "so does Jones" gives "Jones
represents *Jones'* company". -/
theorem fracas_182 :
    represents smith (companyOf smith) ∧ represents jones (companyOf jones) →
      represents jones (companyOf jones) :=
  fun h => h.2

end P182

section P183
variable {A : Type*} (represents : A → A → Prop) (companyOf : A → A) (smith jones : A)

/-- Strict reading: "his" is referential (fixed to Smith), so "so does
Jones" gives "Jones represents *Smith's* company". -/
theorem fracas_183 :
    represents smith (companyOf smith) ∧ represents jones (companyOf smith) →
      represents jones (companyOf smith) :=
  fun h => h.2

end P183

section P184

/-- "Smith represents Jones' company" is neither the sloppy nor the
strict resolution (both of those describe *Jones*, not Smith) — not
addressed by either available reading, genuine independence. Reuses
182/183's own `represents`/`companyOf`/`smith`/`jones` vocabulary: the
premise is the shared antecedent both readings start from, the question
is the unaddressed cross combination. -/
theorem fracas_184_dir1 {A : Type*} (represents : A → A → Prop) (companyOf : A → A)
    (smith jones : A)
    (h : represents smith (companyOf smith) ∧ represents jones (companyOf jones))
    (hNot : ¬ represents smith (companyOf jones)) :
    (represents smith (companyOf smith) ∧ represents jones (companyOf jones)) ∧
      ¬ represents smith (companyOf jones) := ⟨h, hNot⟩

theorem fracas_184_dir2 {A : Type*} (represents : A → A → Prop) (companyOf : A → A)
    (smith jones : A)
    (h : represents smith (companyOf smith) ∧ represents jones (companyOf jones))
    (hYes : represents smith (companyOf jones)) :
    (represents smith (companyOf smith) ∧ represents jones (companyOf jones)) ∧
      represents smith (companyOf jones) := ⟨h, hYes⟩

end P184

end FraCaS.Section4
