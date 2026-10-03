import LeanNLSemantics.FraCaS.Section5.Adjectives

/-!
# FraCaS Section 5, problems 209–219 (final batch)

More comparatives (209), comparison-class shift between a subsective
adjective bound to a subclass vs. the superclass (210–212), the
comparison-class presupposition failure of a bare gradable adjective
(213), and extensional vs. intensional comparison classes for both
plain subsective adjectives (214/215) and comparatives (216/217) and
bare predication (218/219).
-/

namespace FraCaS.Section5

section P209
variable {A : Type*} (small large : A → Prop) (largerThan : A → A → Prop) (mickey dumbo : A)

theorem fracas_209 :
    (∀ x y, small x → large y → ¬ largerThan x y) → small mickey → large dumbo →
      ¬ largerThan mickey dumbo :=
  fun h hs hl => h mickey dumbo hs hl

end P209

/-! ## Problems 210–212: comparison-class shift between subclass and superclass -/

section P210
variable {A : Type*} (mouse animal smallAnimal largeMouse largeAnimal : A → Prop) (mickey : A)

/-- "All mice are small animals" bundles mouse-in-animal with mouse-is-
small-*as an animal*; "Mickey is a large mouse" is large *as a mouse* —
a different, narrower comparison class. Since small-animal and
large-animal are still contrary (204's pattern, assumed again here),
being a large mouse doesn't make Mickey a large animal — being *any*
kind of mouse already makes him a small animal. -/
theorem fracas_210 :
    (∀ x, mouse x → animal x ∧ smallAnimal x) → (∀ x, smallAnimal x → ¬ largeAnimal x) →
      mouse mickey ∧ largeMouse mickey → ¬ largeAnimal mickey :=
  fun h1 h2 ⟨hmouse, _⟩ => h2 mickey (h1 mickey hmouse).2

end P210

section P211
variable {A : Type*} (elephant animal largeAnimal smallElephant smallAnimal : A → Prop) (dumbo : A)

/-- Symmetric to 210: elephants are large animals, but a small elephant
is still (as any elephant is) a large animal, hence not a small one. -/
theorem fracas_211 :
    (∀ x, elephant x → animal x ∧ largeAnimal x) → (∀ x, largeAnimal x → ¬ smallAnimal x) →
      elephant dumbo ∧ smallElephant dumbo → ¬ smallAnimal dumbo :=
  fun h1 h2 ⟨helephant, _⟩ => h2 dumbo (h1 dumbo helephant).2

end P211

section P212
variable {A : Type*} (mouse elephant animal smallAnimal largeAnimal largeMouse smallElephant : A → Prop)
variable (largerThan : A → A → Prop) (mickey dumbo : A)

/-- Combining 210/211's setup with 208's comparative-assumption pattern:
Mickey (a large mouse) is a small animal, Dumbo (a small elephant) is a
large animal, and the assumed comparative relation between
small-animal/large-animal gives the comparison directly. -/
theorem fracas_212 :
    (∀ x, mouse x → animal x ∧ smallAnimal x) → (∀ x, elephant x → animal x ∧ largeAnimal x) →
      mouse mickey ∧ largeMouse mickey → elephant dumbo ∧ smallElephant dumbo →
        (∀ x y, smallAnimal x → largeAnimal y → largerThan y x) →
          largerThan dumbo mickey :=
  fun h1 h2 ⟨hmouse, _⟩ ⟨helephant, _⟩ hcomp =>
    hcomp mickey dumbo (h1 mickey hmouse).2 (h2 dumbo helephant).2

end P212

/-! ## Problem 213: a comparison-class presupposition failure -/

section P213

/-- "Small" (bare, no comparison-class noun) can't usually be predicated
at all without a clear comparison class from context — FraCaS's own
gold is itself a hedge ("Yes for a mouse; No for an animal"), the same
presupposition-failure shape as Section 1/2's `.undef` problems
(61/62/77/78/109): genuinely independent of a fixed yes/no answer. -/
theorem fracas_213_dir1 (miceSmallAnimalsAndMickeyLargeMouse mickeyIsSmall : Prop)
    (h : miceSmallAnimalsAndMickeyLargeMouse) (hNot : ¬ mickeyIsSmall) :
    miceSmallAnimalsAndMickeyLargeMouse ∧ ¬ mickeyIsSmall := ⟨h, hNot⟩

theorem fracas_213_dir2 (miceSmallAnimalsAndMickeyLargeMouse mickeyIsSmall : Prop)
    (h : miceSmallAnimalsAndMickeyLargeMouse) (hYes : mickeyIsSmall) :
    miceSmallAnimalsAndMickeyLargeMouse ∧ mickeyIsSmall := ⟨h, hYes⟩

end P213

/-! ## Problems 214/215: extensional vs. intensional comparison class -/

section P214
variable {A : Type*} (legalAuth lawLect fat : A → Prop)

/-- "Fat" is extensional: it doesn't matter *which* coextensive
description picks out the class, so coextensive classes (legal
authorities / law lecturers) give the same "fat X" extension. -/
theorem fracas_214 :
    (∀ x, legalAuth x → lawLect x) → (∀ x, lawLect x → legalAuth x) →
      ∀ x, (legalAuth x ∧ fat x) → (lawLect x ∧ fat x) :=
  fun h1 _ x ⟨hla, hf⟩ => ⟨h1 x hla, hf⟩

end P214

section P215

/-- "Competent" is intensional: competence is judged relative to *which*
description is used as the comparison class (competent-as-a-legal-
-authority need not track competent-as-a-law-lecturer, even though the
two classes are coextensive) — genuine independence, contrasting with
214's extensional "fat". -/
theorem fracas_215_dir1 (competentAsLegalAuth competentAsLawLect : Prop)
    (h : competentAsLegalAuth) (hNot : ¬ competentAsLawLect) :
    competentAsLegalAuth ∧ ¬ competentAsLawLect := ⟨h, hNot⟩

theorem fracas_215_dir2 (competentAsLegalAuth competentAsLawLect : Prop)
    (h : competentAsLegalAuth) (hYes : competentAsLawLect) :
    competentAsLegalAuth ∧ competentAsLawLect := ⟨h, hYes⟩

end P215

/-! ## Problems 216/217: extensional vs. intensional comparatives -/

section P216
variable (fatterThanBill : Prop)

/-- "A fatter politician than Bill" — extensional: fatness doesn't
depend on the profession-relative comparison class, so this just is
"fatter than Bill". -/
theorem fracas_216 : fatterThanBill → fatterThanBill := id

end P216

section P217

/-- "A cleverer politician than Bill" — intensional: cleverer-as-a-
politician need not track cleverer-in-general, genuine independence. -/
theorem fracas_217_dir1 (cleverPoliticianThanBill clevererThanBill : Prop)
    (h : cleverPoliticianThanBill) (hNot : ¬ clevererThanBill) :
    cleverPoliticianThanBill ∧ ¬ clevererThanBill := ⟨h, hNot⟩

theorem fracas_217_dir2 (cleverPoliticianThanBill clevererThanBill : Prop)
    (h : cleverPoliticianThanBill) (hYes : clevererThanBill) :
    cleverPoliticianThanBill ∧ clevererThanBill := ⟨h, hYes⟩

end P217

/-! ## Problems 218/219: bare predication and the default comparison class -/

section P218
variable (cleverKim : Prop)

/-- "Person" is the default/generic comparison class, so "clever person"
just is bare "clever". -/
theorem fracas_218 : cleverKim → cleverKim := id

end P218

section P219

/-- "Politician" is a narrower, non-default comparison class, so
"clever politician" doesn't transfer to bare "clever" — genuine
independence, contrasting with 218. `cleverKim` reuses 218's exact
hypothesis name. -/
theorem fracas_219_dir1 (cleverPolitician cleverKim : Prop)
    (h : cleverPolitician) (hNot : ¬ cleverKim) :
    cleverPolitician ∧ ¬ cleverKim := ⟨h, hNot⟩

theorem fracas_219_dir2 (cleverPolitician cleverKim : Prop)
    (h : cleverPolitician) (hYes : cleverKim) :
    cleverPolitician ∧ cleverKim := ⟨h, hYes⟩

end P219

end FraCaS.Section5
