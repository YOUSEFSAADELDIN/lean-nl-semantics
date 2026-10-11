import Mathlib

/-!
# Section 3 anaphora with dependent types, without stipulated functions

The hand-written corpus (`FraCaS/Section3/Batch1.lean`, `Batch2.lean`)
does not model cross-sentential anaphora; its translator resolves each
pronoun by hand before Lean sees the problem:

- 117–119, 131, 132 and 138 take a function (`workstationOf`, `lineOf`,
  `coverPageOf : A → A`) as a *variable of the theorem* and state "every
  student used her workstation" as `∀ x, student x → … usedBy x
  (workstationOf x)`. English asserts that each student *has* a
  workstation; a function choosing one is an extra commitment, which over
  `Prop` costs the axiom of choice (`prop_skolem` below) and is here
  stipulated instead.
- 122 folds its two sentences ("Every committee has a chairman. He is
  appointed by its members.") into one premise, so the proof is `id`.
- 133 rewrites "ITEL maintains them" as "every computer GFI owns, ITEL
  maintains" by hand.

The obstacle is not Lean-specific: once "∃ a line" is closed, a later
"them" cannot refer to its witness. Lean makes it concrete, since `∃`
lives in `Prop` and its witness cannot be projected out. Dependent types
(Ranta 1994; Bekki's Dependent Type Semantics) treat a discourse as a
*context*: an indefinite is a Σ-type, an element of which carries its
witness, and each later sentence is typed in the context of the earlier
ones' proofs, so a pronoun is a projection. Below, `Σ'` (`PSigma`, in
`Type`, unlike `∃`) carries the witness.

Each problem is stated with its premises as English gives them — "each
department has a line" as `(d : Department) → Σ' l : Line, HasLine d l`,
no function assumed — and each pronoun as a projection. The proofs use no
axioms at all (the `#print axioms` lines below report it in CI's build
log), and the function the corpus stipulates is *derived*
(`lineOf_derived`): type theory's axiom of choice is a theorem
(`type_theoretic_choice`).

**Prior art.** This is Dependent Type Semantics (Bekki, "Representing
Anaphora with Dependent Types", LACL 2014) and Ranta's Type-Theoretical
Grammar, applied by hand. In DTS a pronoun is an underspecified
`@`-operator, and "anaphora resolution involves proof search": a resolved
pronoun becomes a projection term such as `π1 π1 π2 (c)`, the shape of
`(p d).1` here. This file picks each projection by hand; it does not search
for it. What it adds is the comparison: the same FraCaS problems stated in
this repo's corpus with stipulated choice functions, and here with none and
no axioms. FraCoq (Bernardy & Chatzikyriakidis, NoDaLiDa 2019) handles
these sections with a monadic dynamic semantics instead (0.86 on
anaphora), the model-theoretic counterpart.

Two honest limits, both proved rather than asserted:

- **133 is not obtained.** A projection gives "them" = the computers that
  witness "several computers"; FraCaS's hypothesis needs *all* the
  computers GFI owns (the e-type, maximal reading). `projection_misses_133`
  is a countermodel: the projection reading holds and the hypothesis
  fails. Maximality is an extra ingredient dependent types do not supply.
- **119 depends on a reading.** Its "no" holds only if "Mary used a
  workstation" continues "her workstation"; as a fresh indefinite it is
  not refuted. The corpus makes the same choice; `anaphora_119` below states
  it explicitly.
-/

namespace MTT.DependentAnaphora

/-! ## The axiom of choice: a theorem over Σ, an axiom over ∃ -/

/-- Over Σ-types, "every `d` has some `l`" already contains the function
choosing `l`: no axiom. -/
def type_theoretic_choice {D L : Type} {R : D → L → Prop}
    (p : (d : D) → Σ' l : L, R d l) : Σ' f : D → L, ∀ d, R d (f d) :=
  ⟨fun d => (p d).1, fun d => (p d).2⟩

/-- Over `∃` (in `Prop`), getting the function needs `Classical.choice`. -/
theorem prop_skolem {D L : Type} {R : D → L → Prop}
    (h : ∀ d, ∃ l, R d l) : ∃ f : D → L, ∀ d, R d (f d) :=
  ⟨fun d => Classical.choose (h d), fun d => Classical.choose_spec (h d)⟩

/-! ## 114–116: "Mary used her workstation." -/

section P114
variable {Human Workstation : Type} (Female : Human → Prop)
variable (Owns Used : Human → Workstation → Prop) (mary : Human)

/-- "Her" presupposes a female owner; the sentence asserts that Mary used
that workstation. The context is one Σ-proof of all of it. -/
abbrev Premise114 := Σ' _ : Female mary, Σ' w : Workstation, Owns mary w ∧ Used mary w

/-- 114: "Mary's workstation was used." -/
theorem anaphora_114 (p : Premise114 Female Owns Used mary) :
    ∃ w, Owns mary w ∧ Used mary w :=
  ⟨p.2.1, p.2.2⟩

/-- 115: "Mary has a workstation." -/
theorem anaphora_115 (p : Premise114 Female Owns Used mary) : ∃ w, Owns mary w :=
  ⟨p.2.1, p.2.2.1⟩

/-- 116: "Mary is female." -/
theorem anaphora_116 (p : Premise114 Female Owns Used mary) : Female mary := p.1

end P114

/-! ## 117–119: "Every student used her workstation." -/

section P117
variable {Student Workstation : Type} (Owns Used : Student → Workstation → Prop)
variable (mary : Student)

/-- 117: "… Mary is a student. ⇒ Mary used her workstation." Mary *is* a
student is the typing `mary : Student`; "her workstation" is the
projection of the first premise at Mary. -/
theorem anaphora_117 (p : (s : Student) → Σ' w : Workstation, Owns s w ∧ Used s w) :
    ∃ w, Owns mary w ∧ Used mary w :=
  ⟨(p mary).1, (p mary).2⟩

/-- 118: "⇒ Mary has a workstation." -/
theorem anaphora_118 (p : (s : Student) → Σ' w : Workstation, Owns s w ∧ Used s w) :
    ∃ w, Owns mary w :=
  ⟨(p mary).1, (p mary).2.1⟩

/-- 119: "No student used her workstation. Mary is a student. ⇒ Mary used
a workstation" — gold no, on the reading where "a workstation" continues
"her workstation" (the corpus's reading too). "Her workstation" under
"no" still presupposes that each student has one (`p`); the assertion is
about that workstation. -/
theorem anaphora_119 (p : (s : Student) → Σ' w : Workstation, Owns s w)
    (h : ∀ s, ¬ Used s (p s).1) : ¬ Used mary (p mary).1 :=
  h mary

end P117

/-! ## 120: "Smith attended a meeting. She chaired it." -/

theorem anaphora_120 {Human Meeting : Type} (Attended Chaired : Human → Meeting → Prop)
    (smith : Human) (p : Σ' m : Meeting, Attended smith m) (q : Chaired smith p.1) :
    ∃ m, Chaired smith m :=
  ⟨p.1, q⟩

/-! ## 122: "Every committee has a chairman. He is appointed by its members." -/

/-- The second sentence is typed in the context of the first's proof `p`:
"he" is `(p c).1`, the chairman the first sentence provides for `c`. No
folding of the two sentences into one. -/
theorem anaphora_122 {Committee Human : Type} (Chairman : Human → Committee → Prop)
    (AppointedByMembers : Human → Committee → Prop)
    (p : (c : Committee) → Σ' h : Human, Chairman h c)
    (q : ∀ c, AppointedByMembers (p c).1 c) :
    ∀ c, ∃ h, Chairman h c ∧ AppointedByMembers h c :=
  fun c => ⟨(p c).1, (p c).2, q c⟩

/-! ## 131–132: "Each department has a dedicated line." -/

section P131
variable {Department Line : Type} (HasLine RentsFromBT : Department → Line → Prop)

/-- 131: "They rent them from BT. ⇒ Every department rents a line from BT."
"They" ranges over the departments, "them" is each one's line. -/
theorem anaphora_131 (p : (d : Department) → Σ' l : Line, HasLine d l)
    (q : ∀ d, RentsFromBT d (p d).1) : ∀ d, ∃ l, RentsFromBT d l :=
  fun d => ⟨(p d).1, q d⟩

/-- 132: "The sales department rents it from BT. ⇒ The sales department
rents a line from BT." "It" is the sales department's own line. -/
theorem anaphora_132 (sales : Department) (p : (d : Department) → Σ' l : Line, HasLine d l)
    (q : RentsFromBT sales (p sales).1) : ∃ l, RentsFromBT sales l :=
  ⟨(p sales).1, q⟩

/-- The corpus's stipulated `lineOf` and its premise `∀ d, hasLine d
(lineOf d)` follow from the faithful premise, with no axiom. -/
theorem lineOf_derived (p : (d : Department) → Σ' l : Line, HasLine d l) :
    ∃ lineOf : Department → Line, ∀ d, HasLine d (lineOf d) :=
  ⟨(type_theoretic_choice p).1, (type_theoretic_choice p).2⟩

end P131

/-! ## 138: "Every report has a cover page. R-95-103 is a report. Smith
signed the cover page." -/

/-- "The cover page" is resolved to the one the context provides for the
only report mentioned, `(p r95103).1`; the hypothesis "Smith signed the
cover page of R-95-103" then follows. (The corpus's version omits the
first premise and proves `h → h`.) -/
theorem anaphora_138 {Report Page Human : Type} (CoverOf : Page → Report → Prop)
    (Signed : Human → Page → Prop) (smith : Human) (r95103 : Report)
    (p : (r : Report) → Σ' c : Page, CoverOf c r) (q : Signed smith (p r95103).1) :
    ∃ c, CoverOf c r95103 ∧ Signed smith c :=
  ⟨(p r95103).1, (p r95103).2, q⟩

/-! ## 133: the limit — projection is not the e-type reading -/

/-- The countermodel for 133: GFI owns three computers (`Fin 3`), the
witnesses of "several computers" are the first two, and ITEL maintains
exactly those. -/
def owns133 : Fin 3 → Prop := fun _ => True
def maintains133 (c : Fin 3) : Prop := c.val < 2
def witnesses133 (i : Fin 2) : Fin 3 := Fin.castSucc i

/-- "GFI owns several computers. ITEL maintains them. ⇒ ITEL maintains all
the computers that GFI owns" (gold yes). With "them" read as the
computers witnessing "several" — what a projection gives — the premises
hold and the hypothesis fails. -/
theorem projection_misses_133 :
    (∀ i, owns133 (witnesses133 i)) ∧ (∀ i, maintains133 (witnesses133 i)) ∧
      ¬ ∀ c, owns133 c → maintains133 c := by
  refine ⟨fun _ => trivial, fun i => ?_, fun h => ?_⟩
  · simpa [maintains133, witnesses133] using i.isLt
  · exact absurd (h 2 trivial) (show ¬ ((2 : Fin 3).val < 2) by decide)

end MTT.DependentAnaphora

#print axioms MTT.DependentAnaphora.type_theoretic_choice
#print axioms MTT.DependentAnaphora.prop_skolem
#print axioms MTT.DependentAnaphora.anaphora_117
#print axioms MTT.DependentAnaphora.anaphora_122
#print axioms MTT.DependentAnaphora.anaphora_131
#print axioms MTT.DependentAnaphora.lineOf_derived
#print axioms MTT.DependentAnaphora.anaphora_138
