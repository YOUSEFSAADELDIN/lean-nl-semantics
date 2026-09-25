import LeanNLSemantics.FraCaS.Section3.Anaphora

/-!
# FraCaS Section 3, problems 114–126

First batch of Section 3 (Anaphora): possessive-pronoun presupposition
bundling (114–119), cross-sentential referential pronouns sharing a
bound variable (120–123), and dependent-plural/paycheque-pronoun
Skolemization together with cardinality-based anaphora (124–126).
-/

namespace FraCaS.Section3

open FraCaS.Section1
open FraCaS.Section2

/-! ## Problems 114–116: possessive pronoun presupposition, bundled as a conjunction -/

section P114
variable {A : Type*} (mary maryWorkstation : A) (female : A → Prop) (hasA usedBy : A → A → Prop)

/-- "Mary used her workstation" is formalized as a bundle: Mary is
female (what "her" presupposes about the possessor), Mary has a
workstation (what any possessive presupposes exists), and Mary used it —
matching Section 1 problem 5's treatment of definite-article
presupposition as an explicit conjunct. 114/115/116 are then just
projections out of the same bundle. -/
theorem fracas_114 :
    female mary ∧ hasA mary maryWorkstation ∧ usedBy mary maryWorkstation →
      usedBy mary maryWorkstation :=
  fun h => h.2.2

theorem fracas_115 :
    female mary ∧ hasA mary maryWorkstation ∧ usedBy mary maryWorkstation →
      hasA mary maryWorkstation :=
  fun h => h.2.1

theorem fracas_116 :
    female mary ∧ hasA mary maryWorkstation ∧ usedBy mary maryWorkstation → female mary :=
  fun h => h.1

end P114

/-! ## Problems 117–119: the same bundle, now bound to a quantifier via a Skolem function -/

section P117
variable {A : Type*} (student : A → Prop) (mary : A) (workstationOf : A → A)
variable (female hasA usedBy : A → A → Prop)

/-- "Every student used her workstation": the bound possessive "her"
becomes a Skolem function `workstationOf : A → A` assigning each student
their own workstation, the standard way to formalize a bound pronoun
without building general anaphora machinery (see `Anaphora.lean`'s
header). -/
theorem fracas_117 :
    (∀ x, student x → female x ∧ hasA x (workstationOf x) ∧ usedBy x (workstationOf x)) →
      student mary → usedBy mary (workstationOf mary) :=
  fun h hs => (h mary hs).2.2

theorem fracas_118 :
    (∀ x, student x → female x ∧ hasA x (workstationOf x) ∧ usedBy x (workstationOf x)) →
      student mary → hasA mary (workstationOf mary) :=
  fun h hs => (h mary hs).2.1

end P117

section P119
variable {A : Type*} (student : A → Prop) (mary : A) (workstationOf : A → A)
variable (usedBy : A → A → Prop)

/-- "No student used her workstation": the question's "a workstation"
continues the discourse reference to *her* [the student's own]
workstation rather than introducing a fresh one — same
`workstationOf`-continuation as 117/118, but through `No` this time. -/
theorem fracas_119 :
    (∀ x, student x → ¬ usedBy x (workstationOf x)) → student mary →
      ¬ usedBy mary (workstationOf mary) :=
  fun h hs => h mary hs

end P119

/-! ## Problems 120–123: cross-sentential referential pronouns share a bound variable -/

section P120
variable {A : Type*} (smith : A) (attended chaired : A → A → Prop)

/-- "Smith attended a meeting. She chaired it." — "she"/"it" are the
*same* Smith and the *same* meeting as the first sentence, formalized by
literally reusing the same bound variable `m` across both conjuncts
(`Anaphora.lean`'s header), not two independent existentials. -/
theorem fracas_120 : (∃ m, attended smith m ∧ chaired smith m) → ∃ m, chaired smith m :=
  fun ⟨m, _, hc⟩ => ⟨m, hc⟩

end P120

section P121
variable {A : Type*} (smith itel report invoice proposal : A) (delivered : A → A → A → Prop)

/-- Three sentences, one shared "them" (ITEL) and "she" (Smith) — bundled
as one three-way conjunction, matching FraCaS's own `<why>` ("keeping
track of the same entities across more than two sentences"); the
hypothesis just restates it. -/
theorem fracas_121 :
    delivered smith itel report ∧ delivered smith itel invoice ∧ delivered smith itel proposal →
      delivered smith itel report ∧ delivered smith itel invoice ∧ delivered smith itel proposal :=
  id

end P121

section P122
variable {A : Type*} (committee : A → Prop) (chairman appointedByMembers : A → A → Prop)

/-- "Every committee has a chairman. He is appointed by its members." —
the bound "he"/"its" are folded directly into one combined statement
("every committee has a chairman who is appointed by its members"), so
the hypothesis just restates the premise; modal subordination itself
isn't modeled, only its net truth-conditional content (the same
simplification `Anaphora.lean`'s header describes for bound pronouns). -/
theorem fracas_122 :
    (∀ c, committee c → ∃ ch, chairman ch c ∧ appointedByMembers ch c) →
      ∀ c, committee c → ∃ ch, chairman ch c ∧ appointedByMembers ch c :=
  id

end P122

section P123
variable {A : Type*} [Fintype A] (reportsNeeded sentByItel onDesk : A → Prop)
variable [DecidablePred reportsNeeded] [DecidablePred fun x => reportsNeeded x ∧ sentByItel x]

/-- "ITEL has sent most of the reports Smith needs. They [the sent ones]
are on her desk." Composes two Section 1 lemmas: `most_some` gets a
witness among the sent reports, `some_mono_scope` moves that witness's
property from "sent" to "on desk" via the (anaphorically continued)
premise 2. -/
theorem fracas_123 :
    Most reportsNeeded sentByItel → (∀ x, sentByItel x → onDesk x) →
      Some reportsNeeded onDesk :=
  fun hmost honDesk => some_mono_scope reportsNeeded sentByItel onDesk (most_some reportsNeeded sentByItel hmost) honDesk

end P123

/-! ## Problems 124–126: dependent-plural/cardinal anaphora -/

section P124
variable {A : Type*} [Fintype A] (missing removed : A → Prop)
variable [DecidablePred fun x : A => True ∧ missing x] [DecidablePred fun x : A => True ∧ removed x]

/-- "Two out of ten machines are missing. They have been removed." — the
missing ones (an `Exactly`-many set) are exactly the ones the second
sentence's "they" picks out and asserts were removed; `atLeast_mono_scope`
(Section 1) then transfers the lower bound across. -/
theorem fracas_124 :
    Exactly 2 (fun _ : A => True) missing → (∀ x, missing x → removed x) →
      AtLeast 2 (fun _ : A => True) removed :=
  fun hex hmono => atLeast_mono_scope 2 (fun _ : A => True) missing removed (le_of_eq hex.symm) hmono

end P124

section P125

/-- "Have eight machines been removed?" doesn't follow — the other eight
(non-missing) machines' removal status is simply unconstrained by "the
missing two have been removed". Direction 1: only the two missing ones
are removed. Direction 2: everything is removed (still consistent with
"the missing two were removed"). -/
theorem fracas_125_dir1 :
    (Exactly 2 (fun _ : Fin 10 => True) (fun x => x.val < 2) ∧
        ∀ x : Fin 10, x.val < 2 → x.val < 2) ∧
      ¬ AtLeast 8 (fun _ : Fin 10 => True) (fun x : Fin 10 => x.val < 2) := by
  refine ⟨⟨by decide, fun _ h => h⟩, ?_⟩
  decide

theorem fracas_125_dir2 :
    (Exactly 2 (fun _ : Fin 10 => True) (fun x => x.val < 2) ∧
        ∀ x : Fin 10, x.val < 2 → True) ∧
      AtLeast 8 (fun _ : Fin 10 => True) (fun _ : Fin 10 => True) := by
  refine ⟨⟨by decide, fun _ _ => trivial⟩, ?_⟩
  decide

end P125

section P126
variable {A : Type*} [Fintype A] (missing hereYesterday : A → Prop)
variable [DecidablePred fun x : A => True ∧ missing x] [DecidablePred fun x : A => True ∧ hereYesterday x]

/-- "They [the two missing] were all here yesterday" plus the unstated
but clearly intended background fact that the other eight (still
present) machines were here yesterday too (`h2`) together cover the
whole domain, giving "ten machines were here yesterday" as an exact
count via `Anaphora.lean`'s `card_true_eq_card_type`. -/
theorem fracas_126 (hcard : Fintype.card A = 10)
    (_hmissing : Exactly 2 (fun _ : A => True) missing)
    (h1 : ∀ x, missing x → hereYesterday x) (h2 : ∀ x, ¬ missing x → hereYesterday x) :
    Exactly 10 (fun _ : A => True) hereYesterday := by
  have hall : ∀ x : A, hereYesterday x := fun x => (Classical.em (missing x)).elim (h1 x) (h2 x)
  have heq : (Finset.univ.filter fun x => True ∧ hereYesterday x) = Finset.univ :=
    Finset.ext (fun x => by simp [hall x])
  have hc : card (fun x : A => True ∧ hereYesterday x) = Fintype.card A := by
    rw [← Finset.card_univ]; exact congrArg Finset.card heq
  exact hc.trans hcard

end P126

end FraCaS.Section3
