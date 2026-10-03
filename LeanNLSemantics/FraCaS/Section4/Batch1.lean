import LeanNLSemantics.FraCaS.Section4.Ellipsis

/-!
# FraCaS Section 4, problems 142–155

VP-ellipsis "so did X"/"X did too" carrying (or not carrying) tense,
polarity, mood, number, and temporal/PP adjuncts across to the elided
site (142–149), gapping with PP modifiers (150–154), and "one"-anaphora
(155, continuing in `Batch2.lean`).
-/

namespace FraCaS.Section4

open FraCaS.Section1
open FraCaS.Section2

/-! ## Problems 142–145: temporal adverbials carried across ellipsis, or not -/

section P142
variable (spokeJohnMary spokeBillMary : Prop)

theorem fracas_142 : spokeJohnMary ∧ spokeBillMary → spokeBillMary := fun h => h.2

end P142

section P143

/-- "So did Bill" was resolved (in 142) *before* premise 3 adds a
temporal adverbial to John's case — that adverbial doesn't retroactively
apply to Bill, so it's silent on whether Bill spoke to Mary specifically
*at four o'clock*. `spokeBillMary` is the already-established fact (142's
own content); `spokeAt4BillMary` is the independent question. -/
theorem fracas_143_dir1 (spokeBillMary spokeAt4BillMary : Prop)
    (h : spokeBillMary) (hNot : ¬ spokeAt4BillMary) :
    spokeBillMary ∧ ¬ spokeAt4BillMary := ⟨h, hNot⟩

theorem fracas_143_dir2 (spokeBillMary spokeAt4BillMary : Prop)
    (h : spokeBillMary) (hYes : spokeAt4BillMary) :
    spokeBillMary ∧ spokeAt4BillMary := ⟨h, hYes⟩

end P143

section P144
variable (spokeAt4JohnMary spokeAt4BillMary : Prop)

/-- Here the adverbial is *in* the antecedent clause itself, so "so did
Bill" resolves to the whole thing including "at four o'clock". -/
theorem fracas_144 : spokeAt4JohnMary ∧ spokeAt4BillMary → spokeAt4BillMary := fun h => h.2

end P144

section P145
variable (spokeAt5BillMary : Prop)

/-- "And Bill did at five o'clock" supplies its own (different, and
overriding) adverbial directly — trivial restatement once resolved. -/
theorem fracas_145 : spokeAt5BillMary → spokeAt5BillMary := id

end P145

/-! ## Problems 146–149: tense/polarity/mood/number agreement not necessary -/

section P146
variable (spokeBillMary : Prop)

/-- "John has spoken to Mary. Bill is going to [speak to Mary]." — this
project doesn't model tense as a separate parameter from the underlying
fact, so future/perfect surface tense on the ellipsis doesn't change the
formalized content. -/
theorem fracas_146 : spokeBillMary → spokeBillMary := id

end P146

section P147
variable (spokeBillMaryMonday : Prop)

/-- "Bill didn't [speak to Mary on Monday]" — negative ellipsis directly
refutes the hypothesis, regardless of the antecedent's own polarity. -/
theorem fracas_147 : ¬ spokeBillMaryMonday → ¬ spokeBillMaryMonday := id

end P147

section P148
variable (spokeBillMary : Prop)

/-- "Bill has [spoken to Mary]" — premise 1 is a question (not asserted
content), so only premise 2's positive ellipsis carries any content, and
it's the hypothesis outright. -/
theorem fracas_148 : spokeBillMary → spokeBillMary := id

end P148

section P149
variable {A : Type*} (student spokeMary : A → Prop)

/-- "The students have too [spoken to Mary]" — a distributive universal
over "student" (Section 2's simplification for definite plurals), no
number-agreement machinery needed. -/
theorem fracas_149 : Every student spokeMary → Every student spokeMary := id

end P149

/-! ## Problems 150–154: gapping with PP modifiers -/

section P150
variable {Person City Vehicle : Type*} (wentTo : Person → City → Vehicle → Prop)
variable (john bill : Person) (paris : City) (car train : Vehicle)

theorem fracas_150 : wentTo john paris car ∧ wentTo bill paris train → wentTo bill paris train :=
  fun h => h.2

end P150

section P151
variable {Person City Vehicle : Type*} (wentTo : Person → City → Vehicle → Prop)
variable (john bill : Person) (paris berlin : City) (car train : Vehicle)

theorem fracas_151 :
    wentTo john paris car ∧ wentTo bill berlin train → wentTo bill berlin train :=
  fun h => h.2

end P151

section P152
variable {Person City Vehicle : Type*} (wentTo : Person → City → Vehicle → Prop)
variable (john bill : Person) (paris berlin : City) (car : Vehicle)

theorem fracas_152 : wentTo john paris car ∧ wentTo bill berlin car → wentTo bill berlin car :=
  fun h => h.2

end P152

section P153
variable {Student City Vehicle : Type*} (goingTo : Student → City → Vehicle → Prop)
variable (john : Student) (paris : City) (car train : Vehicle)

/-- "The students by train" — a distributive universal over the
gapped predicate, no subject-verb-agreement machinery needed. -/
theorem fracas_153 :
    goingTo john paris car ∧ Every (fun _ : Student => True) (fun s => goingTo s paris train) →
      Every (fun _ : Student => True) (fun s => goingTo s paris train) :=
  fun h => h.2

end P153

section P154
variable {Person City Vehicle : Type*} (wentTo : Person → City → Vehicle → Prop)
variable (john bill : Person) (paris : City) (car train : Vehicle)

/-- Cross-sentential gapping: the same shape as 150, split across two
sentences instead of one conjoined clause. -/
theorem fracas_154 : wentTo john paris car ∧ wentTo bill paris train → wentTo bill paris train :=
  fun h => h.2

end P154

/-! ## Problem 155: "one"-anaphora, bare -/

section P155
variable {A : Type*} (car : A → Prop) (owns : A → A → Prop) (john bill : A)

theorem fracas_155 :
    (∃ c, car c ∧ owns john c) ∧ (∃ c, car c ∧ owns bill c) → ∃ c, car c ∧ owns bill c :=
  fun h => h.2

end P155

end FraCaS.Section4
