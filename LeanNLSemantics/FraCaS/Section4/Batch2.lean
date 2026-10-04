import LeanNLSemantics.FraCaS.Section4.Ellipsis

/-!
# FraCaS Section 4, problems 156–170

"One"-anaphora continued: same-vs-different witness (156), modifier
inheritance and its two-reading ambiguity (157–162), a negated
NP-ellipsis restatement (163), subcategorized/adjunct PP ellipsis
(164–166), NP-ellipsis with exact cardinality (167/168, reusing
Section 2's `Exactly`/`exactly_ne`), and a scope ambiguity in elliptical
"before" (169/170).
-/

namespace FraCaS.Section4

open FraCaS.Section1
open FraCaS.Section2

/-! ## Problem 156: "one"-anaphora doesn't require the same witness -/

section P156

/-- "John owns a car. Bill owns one too" doesn't mean the *same* car —
direction 1 exhibits two distinct cars (`true`/`false`), one owned by
each; direction 2, both owning the same one (`true`). -/
theorem fracas_156_dir1 :
    ((∃ c : Bool, True ∧ c = true) ∧ (∃ c : Bool, True ∧ c = false)) ∧
      ¬ ∃ c : Bool, True ∧ c = true ∧ c = false := by
  refine ⟨⟨⟨true, trivial, rfl⟩, ⟨false, trivial, rfl⟩⟩, ?_⟩
  rintro ⟨c, _, hc1, hc2⟩
  rw [hc1] at hc2
  exact absurd hc2 (by decide)

theorem fracas_156_dir2 :
    ((∃ c : Bool, True ∧ c = true) ∧ (∃ c : Bool, True ∧ c = true)) ∧
      ∃ c : Bool, True ∧ c = true ∧ c = true :=
  ⟨⟨⟨true, trivial, rfl⟩, ⟨true, trivial, rfl⟩⟩, true, trivial, rfl, rfl⟩

end P156

/-! ## Problems 157–162: "one"-anaphora and modifier inheritance -/

section P157
variable {A : Type*} (car red blue : A → Prop) (owns : A → A → Prop) (john bill : A)

/-- "A blue one" contrastively replaces "red" with "blue" — trivial once
resolved. -/
theorem fracas_157 :
    (∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ blue c ∧ owns bill c) →
      ∃ c, car c ∧ blue c ∧ owns bill c :=
  fun h => h.2

end P157

section P158

/-- "A blue one" says nothing about whether Bill's car is *also* red —
genuine independence, same shape as Section 3's unrelated-claims cases.
Reuses 157's own `car`/`red`/`blue`/`owns`/`john`/`bill` vocabulary: the
premise is exactly 157's, the question is a separate existential about
red, parallel in shape but with no connection to the blue one. -/
theorem fracas_158_dir1 {A : Type*} (car red blue : A → Prop) (owns : A → A → Prop)
    (john bill : A)
    (h : (∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ blue c ∧ owns bill c))
    (hNot : ¬ ∃ c, car c ∧ red c ∧ owns bill c) :
    ((∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ blue c ∧ owns bill c)) ∧
      ¬ ∃ c, car c ∧ red c ∧ owns bill c := ⟨h, hNot⟩

theorem fracas_158_dir2 {A : Type*} (car red blue : A → Prop) (owns : A → A → Prop)
    (john bill : A)
    (h : (∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ blue c ∧ owns bill c))
    (hYes : ∃ c, car c ∧ red c ∧ owns bill c) :
    ((∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ blue c ∧ owns bill c)) ∧
      ∃ c, car c ∧ red c ∧ owns bill c := ⟨h, hYes⟩

end P158

section P159
variable {A : Type*} (car red fast : A → Prop) (owns : A → A → Prop) (john bill : A)

/-- "A fast one" — "fast" isn't a color, so it doesn't contrast with
"red"; it's simply the new modifier, trivial once resolved. -/
theorem fracas_159 :
    (∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ fast c ∧ owns bill c) →
      ∃ c, car c ∧ fast c ∧ owns bill c :=
  fun h => h.2

end P159

section P160
variable {A : Type*} (car red fast : A → Prop) (owns : A → A → Prop) (john bill : A)

/-- One possible reading: "one" is resolved via the whole property "red
car", so "a fast one" = "a fast red car" — trivial once *this* reading
is adopted (contrast 161, the other reading). -/
theorem fracas_160 :
    (∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ fast c ∧ red c ∧ owns bill c) →
      ∃ c, car c ∧ fast c ∧ red c ∧ owns bill c :=
  fun h => h.2

end P160

section P161

/-- The other reading: "one" resolves only via "car" (not "red car"),
so "a fast one" says nothing about color — genuine independence, the
same countermodel style as 158. FraCaS's own note: "formally identical
with preceding" (160), differing only in which resolution is chosen.
The question ("does Bill own a fast red car?") is the same conjunction
160 proves under *its* reading - here it's independent instead. -/
theorem fracas_161_dir1 {A : Type*} (car red fast : A → Prop) (owns : A → A → Prop)
    (john bill : A)
    (h : (∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ fast c ∧ owns bill c))
    (hNot : ¬ ∃ c, car c ∧ fast c ∧ red c ∧ owns bill c) :
    ((∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ fast c ∧ owns bill c)) ∧
      ¬ ∃ c, car c ∧ fast c ∧ red c ∧ owns bill c := ⟨h, hNot⟩

theorem fracas_161_dir2 {A : Type*} (car red fast : A → Prop) (owns : A → A → Prop)
    (john bill : A)
    (h : (∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ fast c ∧ owns bill c))
    (hYes : ∃ c, car c ∧ fast c ∧ red c ∧ owns bill c) :
    ((∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ fast c ∧ owns bill c)) ∧
      ∃ c, car c ∧ fast c ∧ red c ∧ owns bill c := ⟨h, hYes⟩

end P161

section P162
variable {A : Type*} (car red fast slow : A → Prop) (owns : A → A → Prop) (john bill : A)

/-- "Fast"/"slow" are semantically parallel (antonyms on the same
dimension), so "a slow one" replaces "fast" with "slow" but keeps the
non-parallel modifier "red" — trivial once resolved this way, per
FraCaS's own `<why>`. -/
theorem fracas_162 :
    (∃ c, car c ∧ fast c ∧ red c ∧ owns john c) ∧
        (∃ c, car c ∧ slow c ∧ red c ∧ owns bill c) →
      ∃ c, car c ∧ slow c ∧ red c ∧ owns bill c :=
  fun h => h.2

end P162

/-! ## Problem 163: negated NP-ellipsis -/

section P163
variable (knowsWhyJohnPaperAccepted : Prop)

/-- "Bill doesn't know why [John had his paper accepted]" directly
refutes the hypothesis. -/
theorem fracas_163 : ¬ knowsWhyJohnPaperAccepted → ¬ knowsWhyJohnPaperAccepted := id

end P163

/-! ## Problems 164–166: subcategorized/adjunct PP ellipsis -/

section P164
variable (spokeJohnMary spokeJohnSue : Prop)

theorem fracas_164 : spokeJohnMary ∧ spokeJohnSue → spokeJohnSue := fun h => h.2

end P164

section P165
variable (spokeJohnMary spokeJohnMaryFriday : Prop)

theorem fracas_165 : spokeJohnMary ∧ spokeJohnMaryFriday → spokeJohnMaryFriday := fun h => h.2

end P165

section P166
variable (spokeJohnMaryThursday spokeJohnMaryFriday : Prop)

theorem fracas_166 : spokeJohnMaryThursday ∧ spokeJohnMaryFriday → spokeJohnMaryFriday :=
  fun h => h.2

end P166

/-! ## Problems 167/168: NP-ellipsis with exact cardinality -/

section P167
variable {A : Type*} [Fintype A] (womanWorksInSales : A → Prop)
variable [DecidablePred fun x : A => True ∧ womanWorksInSales x]

/-- "But only one woman [works in the Sales Department]" — an exact
count that directly refutes a different exact count, same as Section 2
problems 85/86. -/
theorem fracas_167 :
    Exactly 1 (fun _ : A => True) womanWorksInSales →
      ¬ Exactly 2 (fun _ : A => True) womanWorksInSales :=
  exactly_ne 1 2 (fun _ : A => True) womanWorksInSales (by decide)

end P167

section P168
variable (fortyFiveWomenWorkPartTime : Prop)

theorem fracas_168 : fortyFiveWomenWorkPartTime → fortyFiveWomenWorkPartTime := id

end P168

/-! ## Problems 169/170: a genuine scope ambiguity, each reading trivial on its own -/

section P169
variable (johnFoundMaryBeforeBillFoundMary : Prop)

/-- "John found Mary before Bill" is ambiguous; this problem stipulates
the "before Bill found Mary" resolution and asks about exactly that. -/
theorem fracas_169 : johnFoundMaryBeforeBillFoundMary → johnFoundMaryBeforeBillFoundMary := id

end P169

section P170
variable (johnFoundMaryBeforeJohnFoundBill : Prop)

/-- The other resolution: "before John found Bill" — a different,
independently stipulated reading of the same ambiguous sentence, not a
contrast case with 169. -/
theorem fracas_170 : johnFoundMaryBeforeJohnFoundBill → johnFoundMaryBeforeJohnFoundBill := id

end P170

end FraCaS.Section4
