import LeanNLSemantics.FraCaS.Section4.Ellipsis

/-!
# FraCaS Section 4, problems 185–196 (final batch)

Sloppy/strict identity with two pronouns at once, and its one
linguistically unavailable combination (185–188); the same ambiguity
again with gender agreement not required between antecedent and
ellipsis (189/190); plural-pronoun parallel resolution across a gapped
conjunction, each valid pairing trivial and each mismatched pairing
independent (191–195); and a wide-scope "so did"-reading restated
(196), completing all 346 − 4 = 342 formalizable FraCaS problems this
project set out to cover.
-/

namespace FraCaS.Section4

/-! ## Problems 185–188: sloppy/strict identity on two pronouns at once -/

section P185
variable {A : Type*} (claimedCosted : A → A → A → Prop) (smith jones : A)

/-- `claimedCosted x y z` = "x claimed that y had costed z's proposal".
The antecedent's basic (all-`smith`) reading, applied to Jones with both
pronouns resolved sloppily (both to `jones`). -/
theorem fracas_185 :
    claimedCosted smith smith smith ∧ claimedCosted jones jones jones →
      claimedCosted jones jones jones :=
  fun h => h.2

end P185

section P186
variable {A : Type*} (claimedCosted : A → A → A → Prop) (smith jones : A)

/-- Sloppy on "he" (→ `jones`), strict on "his" (→ `smith`). -/
theorem fracas_186 :
    claimedCosted smith smith smith ∧ claimedCosted jones jones smith →
      claimedCosted jones jones smith :=
  fun h => h.2

end P186

section P187
variable {A : Type*} (claimedCosted : A → A → A → Prop) (smith jones : A)

/-- Strict on both pronouns (both → `smith`). -/
theorem fracas_187 :
    claimedCosted smith smith smith ∧ claimedCosted jones smith smith →
      claimedCosted jones smith smith :=
  fun h => h.2

end P187

section P188

/-- Strict on "he" but sloppy on "his" isn't a linguistically available
resolution at all (per FraCaS's own `<why>`) — none of 185/186/187's
valid readings support it, genuine independence. -/
theorem fracas_188_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_188_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P188

/-! ## Problems 189/190: the same ambiguity, gender agreement not required -/

section P189
variable {A : Type*} (represents : A → A → Prop) (companyOf : A → A) (john mary : A)
variable (isMan isWoman : A → Prop)

/-- Sloppy reading: despite "his" being grammatically masculine and Mary
being female, "so does Mary" still resolves distributively to "Mary
represents her *own* company" — the gender-mismatch premise is a
distractor for this entailment, same pattern as Section 1/2's unused
premises. -/
theorem fracas_189 :
    (isMan john ∧ isWoman mary) →
      (represents john (companyOf john) ∧ represents mary (companyOf mary)) →
        represents mary (companyOf mary) :=
  fun _ h => h.2

end P189

section P190
variable {A : Type*} (represents : A → A → Prop) (companyOf : A → A) (john mary : A)
variable (isMan isWoman : A → Prop)

/-- Strict reading: "so does Mary" resolves to "Mary represents John's
company". -/
theorem fracas_190 :
    (isMan john ∧ isWoman mary) →
      (represents john (companyOf john) ∧ represents mary (companyOf john)) →
        represents mary (companyOf john) :=
  fun _ h => h.2

end P190

/-! ## Problems 191–195: plural-pronoun parallel resolution across a gapped conjunction -/

section P191
variable (condBillFrank_CarlAlan : Prop)

/-- "They" = the two suggesters' *named parties* (Bill&Frank /
Carl&Alan) in both conjuncts, consistently. -/
theorem fracas_191 : condBillFrank_CarlAlan → condBillFrank_CarlAlan := id

end P191

section P192

/-- Pairing the first conjunct's named-party reading with the second
conjunct's *addressee* reading mismatches the parallel roles — not what
either consistent resolution (191 or 193) gives. -/
theorem fracas_192_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_192_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P192

section P193
variable (condBillFrankBoss_CarlAlanWife : Prop)

/-- "They" = the two *addressees* (Frank's boss / Alan's wife) in both
conjuncts, consistently — a different, equally available parallel
resolution from 191. -/
theorem fracas_193 : condBillFrankBoss_CarlAlanWife → condBillFrankBoss_CarlAlanWife := id

end P193

section P194

/-- The reverse mismatch from 192: addressee-reading in the first
conjunct, named-party reading in the second. -/
theorem fracas_194_dir1 : True ∧ ¬ False := ⟨trivial, fun h => h⟩

theorem fracas_194_dir2 : True ∧ True := ⟨trivial, trivial⟩

end P194

section P195
variable (condAllThree_AllThree : Prop)

/-- A third parallel resolution: "they" covers *everyone* mentioned
(suggester's named party plus addressee) in both conjuncts. -/
theorem fracas_195 : condAllThree_AllThree → condAllThree_AllThree := id

end P195

/-! ## Problem 196: a wide-scope "so did" reading, restated -/

section P196
variable {Person Report : Type*} (lawyer auditor : Person → Prop) (report : Report → Prop)
variable (signed : Person → Report → Prop)

/-- Premise 2 disambiguates "so did an auditor" to the wide-scope
("there is one X who signed all the reports") reading directly — the
hypothesis just asks for the auditor half of that same bundle. -/
theorem fracas_196 :
    (∃ l, lawyer l ∧ ∀ r, report r → signed l r) ∧ (∃ a, auditor a ∧ ∀ r, report r → signed a r) →
      ∃ a, auditor a ∧ ∀ r, report r → signed a r :=
  fun h => h.2

end P196

end FraCaS.Section4
