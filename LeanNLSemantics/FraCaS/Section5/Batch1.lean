import LeanNLSemantics.FraCaS.Section5.Adjectives

/-!
# FraCaS Section 5, problems 197–208

Affirmative adjective noun/adjective-drop (197, 203), privative
adjectives (198), adjective-ordering with a privative and an affirmative
adjective stacked (199–201), an intersective adjective distributing
across a CN-subtyping coercion (202), contrary (not contradictory)
comparison-class adjectives (204–207), and comparatives via an assumed
relation (208, continuing in `Batch2.lean`).
-/

namespace FraCaS.Section5

/-! ## Problem 197: affirmative adjective, noun drop -/

section P197
variable {Person Thing : Type*} (diamond genuine : Thing → Prop) (hasA : Person → Thing → Prop)
variable (john : Person)

theorem fracas_197 :
    (∃ d, diamond d ∧ genuine d ∧ hasA john d) → ∃ d, diamond d ∧ hasA john d :=
  fun ⟨d, hdia, _, hh⟩ => ⟨d, hdia, hh⟩

end P197

/-! ## Problem 198: a privative adjective -/

section P198
variable {A : Type*} (formerUnivStudent univStudent : A → Prop) (john : A)

/-- Per FraCaS's own chosen `.no` reading (not the "opinions differ, may
just be `.unknown`" alternative it also flags): "former N" is treated as
privative, the same pattern `Adjectives.lean`'s `fake_not_real` gives
"fake gun" — an explicit assumed fact, not derived from anything more
basic. -/
theorem fracas_198 :
    (∀ x, formerUnivStudent x → ¬ univStudent x) → formerUnivStudent john → ¬ univStudent john :=
  fun hpriv hj => hpriv john hj

end P198

/-! ## Problems 199–201: adjective ordering with a stacked privative + affirmative -/

section P199
variable (successful : Prop)

/-- "A successful former university student" — "successful" is
outermost, so it predicates of John directly regardless of "former"'s
privativity underneath; this project encodes that by making the
resolved premise directly assert "successful", matching FraCaS's own
gloss "(for a former university student)" — trivial once resolved this
way. -/
theorem fracas_199 : successful → successful := id

end P199

section P200

/-- "A former successful university student" — now "successful" is
*embedded under* "former" (part of what John used to be), so it says
nothing about present-tense John — genuine independence, the same
unrelated-claims shape used throughout Sections 1–4. -/
theorem fracas_200_dir1 (wasFormerSuccessfulUnivStudent currentlySuccessful : Prop)
    (h : wasFormerSuccessfulUnivStudent) (hNot : ¬ currentlySuccessful) :
    wasFormerSuccessfulUnivStudent ∧ ¬ currentlySuccessful := ⟨h, hNot⟩

theorem fracas_200_dir2 (wasFormerSuccessfulUnivStudent currentlySuccessful : Prop)
    (h : wasFormerSuccessfulUnivStudent) (hYes : currentlySuccessful) :
    wasFormerSuccessfulUnivStudent ∧ currentlySuccessful := ⟨h, hYes⟩

end P200

section P201

/-- Same stacking as 200: "former" is the *outermost* operator over the
whole "successful university student" description, so it blocks
noun-drop entirely — John need not currently be a university student at
all (he may have stopped being a successful one without ever having
stopped being a student, or vice versa; per FraCaS's own `<why>`). -/
theorem fracas_201_dir1 (wasFormerSuccessfulUnivStudent currentlyUnivStudent : Prop)
    (h : wasFormerSuccessfulUnivStudent) (hNot : ¬ currentlyUnivStudent) :
    wasFormerSuccessfulUnivStudent ∧ ¬ currentlyUnivStudent := ⟨h, hNot⟩

theorem fracas_201_dir2 (wasFormerSuccessfulUnivStudent currentlyUnivStudent : Prop)
    (h : wasFormerSuccessfulUnivStudent) (hYes : currentlyUnivStudent) :
    wasFormerSuccessfulUnivStudent ∧ currentlyUnivStudent := ⟨h, hYes⟩

end P201

/-! ## Problem 202: an intersective adjective distributes across CN-subtyping -/

section P202
variable {A : Type*} (mammal animal fourLegged : A → Prop)

/-- "[N1 entails N2] entails [Adj(N1) entails Adj(N2)]" for an
intersective adjective like "four-legged" — restricting an already-
narrower class by an independent extra predicate stays narrower. -/
theorem fracas_202 :
    (∀ x, mammal x → animal x) → ∀ x, (mammal x ∧ fourLegged x) → (animal x ∧ fourLegged x) :=
  fun h x ⟨hm, hf⟩ => ⟨h x hm, hf⟩

end P202

/-! ## Problem 203: adjective drop -/

section P203
variable {A : Type*} (fourLegged animal : A → Prop) (dumbo : A)

theorem fracas_203 : fourLegged dumbo ∧ animal dumbo → fourLegged dumbo := fun h => h.1

end P203

/-! ## Problems 204–207: contrary, not contradictory -/

section P204
variable {A : Type*} (small large : A → Prop) (mickey : A)

theorem fracas_204 : (∀ x, small x → ¬ large x) → small mickey → ¬ large mickey :=
  fun h hs => h mickey hs

end P204

section P205
variable {A : Type*} (small large : A → Prop) (dumbo : A)

theorem fracas_205 : (∀ x, large x → ¬ small x) → large dumbo → ¬ small dumbo :=
  fun h hl => h dumbo hl

end P205

section P206

/-- "Not small" doesn't give "large" — contrary predicates leave a
middle ground (e.g. medium-sized). Reuses 204/205's `small`/`large`
vocabulary and `mickey`. -/
theorem fracas_206_dir1 {A : Type*} (small large : A → Prop) (mickey : A)
    (h : ¬ small mickey) (hNot : ¬ large mickey) :
    ¬ small mickey ∧ ¬ large mickey := ⟨h, hNot⟩

theorem fracas_206_dir2 {A : Type*} (small large : A → Prop) (mickey : A)
    (h : ¬ small mickey) (hYes : large mickey) :
    ¬ small mickey ∧ large mickey := ⟨h, hYes⟩

end P206

section P207

/-- "Not large" doesn't give "small", symmetric to 206. Reuses 204/205's
`small`/`large` vocabulary and `dumbo`. -/
theorem fracas_207_dir1 {A : Type*} (small large : A → Prop) (dumbo : A)
    (h : ¬ large dumbo) (hNot : ¬ small dumbo) :
    ¬ large dumbo ∧ ¬ small dumbo := ⟨h, hNot⟩

theorem fracas_207_dir2 {A : Type*} (small large : A → Prop) (dumbo : A)
    (h : ¬ large dumbo) (hYes : small dumbo) :
    ¬ large dumbo ∧ small dumbo := ⟨h, hYes⟩

end P207

/-! ## Problem 208: a comparative via an assumed relation -/

section P208
variable {A : Type*} (small large : A → Prop) (smallerThan : A → A → Prop) (mickey dumbo : A)

/-- Per FraCaS's own `<why>`: the comparative relation between "small"
and "large" is an assumed fact connecting the base gradable adjectives,
not derived from anything more primitive. -/
theorem fracas_208 :
    (∀ x y, small x → large y → smallerThan x y) → small mickey → large dumbo →
      smallerThan mickey dumbo :=
  fun h hs hl => h mickey dumbo hs hl

end P208

end FraCaS.Section5
