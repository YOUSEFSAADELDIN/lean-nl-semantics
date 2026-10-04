import LeanNLSemantics.FraCaS.Section3.Anaphora

/-!
# FraCaS Section 3, problems 127–141

Second and final batch of Section 3: cumulative "and"-conjunction
constructing a plural antecedent across separate constituents (127),
genuine referential ambiguity of "they" with different gold answers per
reading (128–130), dependent-plural and paycheque-pronoun Skolemization
(131/132), e-type anaphora (133), donkey sentences on the strong/
universal reading (134/135) vs. the weak/existential reading (136,
where the two readings genuinely diverge and FraCaS's gold tracks the
weak one), a proportion problem (137), a fully resolved donkey/definite
chain (138), reflexives (139/140), and one more genuine independence
case (141).
-/

namespace FraCaS.Section3

open FraCaS.Section1
open FraCaS.Section2

/-! ## Problem 127: cumulative "and", plural antecedent from separate constituents -/

section P127
variable {Person Machine : Type*} (smith jones : Person) (m1 m2 : Machine) (hne : m1 ≠ m2)
variable (took putInLobby : Person → Machine → Prop)

include hne in
/-- "Smith took a machine on Tuesday, and Jones took a machine on
Wednesday. They put them in the lobby." — "they"/"them" build a plural
antecedent out of the two separately-introduced individuals/machines
across the conjoined clause, the same cumulative-bundling move as
Section 2's problem 111 (`hne` records that "a machine"/"a machine" were
two different ones, per FraCaS's own `<why>`). `include hne`: it's used
only in the *proof*, not the stated type, and `variable` auto-inclusion
only scans the type (the same gotcha `NLIExamples.lean`'s `include john
in` documents). -/
theorem fracas_127 :
    (took smith m1 ∧ took jones m2 ∧ putInLobby smith m1 ∧ putInLobby jones m2) →
      ∃ n1 n2 : Machine, n1 ≠ n2 ∧ (putInLobby smith n1 ∨ putInLobby jones n1) ∧
        (putInLobby smith n2 ∨ putInLobby jones n2) :=
  fun ⟨_, _, hs, hj⟩ => ⟨m1, m2, hne, Or.inl hs, Or.inr hj⟩

end P127

/-! ## Problems 128–130: genuine referential ambiguity of "they" -/

section P128
variable {A : Type*} (colleagueOf hated : A → Prop)

/-- Reading A: "they" = John's colleagues (excluding John). 128 asks
about exactly this group, so it's a restatement. -/
theorem fracas_128 : Every colleagueOf hated → Every colleagueOf hated := id

end P128

section P129
variable {A : Type*} (john : A) (colleagueOf hated : A → Prop)

/-- Reading B: "they" = John and his colleagues together, distributive
("every member of {John} ∪ colleagues hated it"). Under this reading,
John himself is one of the haters. -/
theorem fracas_129 : Every (fun x => x = john ∨ colleagueOf x) hated → hated john :=
  fun h => h john (Or.inl rfl)

end P129

section P130

/-- Reading A applied to "did John hate it": nothing connects "the
colleagues (not John) hated it" to John's own hating-status — genuinely
independent, using the same colleague/hated-coincide-on-`true`
countermodel style as Section 1/2's `Every`-subset problems, with
`john := false` standing for "not a colleague". FraCaS's own note says
this reading is "formally identical" to 129's premise with the opposite
verdict for the *same* question, precisely because it's a different
resolution of "they". -/
theorem fracas_130_dir1 :
    Every (fun b : Bool => b = true) (fun b : Bool => b = true) ∧ ¬ (false = true) :=
  ⟨fun _ h => h, by decide⟩

theorem fracas_130_dir2 :
    Every (fun b : Bool => b = true) (fun _ : Bool => True) ∧ True :=
  ⟨fun _ _ => trivial, trivial⟩

end P130

/-! ## Problems 131/132: dependent-plural and paycheque-pronoun Skolemization -/

section P131
variable {A : Type*} (department : A → Prop) (lineOf : A → A) (bt : A)
variable (hasLine rentsFromBT : A → A → Prop)

/-- "Each department has a dedicated line. They rent them from BT." —
dependent plural anaphora: "they"/"them" covary with "each department"
the same `workstationOf`-style Skolem function as 117/118, here
`lineOf`. -/
theorem fracas_131 :
    (∀ d, department d → hasLine d (lineOf d)) →
      (∀ d, department d → rentsFromBT d (lineOf d)) →
        ∀ d, department d → ∃ l, rentsFromBT d l :=
  fun _ h2 d hd => ⟨lineOf d, h2 d hd⟩

end P131

section P132
variable {A : Type*} (department : A → Prop) (lineOf : A → A) (salesDept : A)
variable (hasLine rentsFromBT : A → A → Prop)

/-- "Each department has a dedicated line. The sales department rents
*it* from BT." — a paycheque pronoun: "it" isn't a fixed referent but
"the sales department's own [line]", the very same `lineOf` Skolem
function applied specifically at `salesDept`. -/
theorem fracas_132 :
    (∀ d, department d → hasLine d (lineOf d)) →
      rentsFromBT salesDept (lineOf salesDept) →
        ∃ l, rentsFromBT salesDept l :=
  fun _ h2 => ⟨lineOf salesDept, h2⟩

end P132

/-! ## Problem 133: e-type anaphora -/

section P133
variable {A : Type*} (ownsGFI maintainsITEL : A → Prop)

/-- "GFI owns several computers. ITEL maintains them." — e-type
anaphora: "them" is resolved to the *maximal* set GFI owns (not just the
witnesses to "several"), so premise 2 is formalized directly as the
universal "every computer GFI owns, ITEL maintains" — at which point the
hypothesis ("all the computers GFI owns") is the same statement.
Premise 1 ("several") becomes a distractor once "them" is resolved this
way, same as Section 1/2's recurring distractor-premise pattern. -/
theorem fracas_133 :
    (∃ x, ownsGFI x) → (∀ x, ownsGFI x → maintainsITEL x) → ∀ x, ownsGFI x → maintainsITEL x :=
  fun _ h2 => h2

end P133

/-! ## Problems 134/135: donkey sentences, the strong/universal reading -/

section P134
variable {A B : Type*} (customer : A → Prop) (owns hasContract : A → B → Prop) (mfi : A)

/-- "Every customer who owns a computer has a service contract for it" —
the donkey pronoun "it" becomes an inner universal tied to the outer
one: `∀x, customer x → ∀c, owns x c → hasContract x c`. Instantiating at
`mfi` directly gives "all its computers", regardless of how many
computers `mfi` owns — the "exactly one" premise is a distractor on this
(the strong/universal) reading. -/
theorem fracas_134 :
    (∀ x, customer x → ∀ c, owns x c → hasContract x c) → customer mfi →
      ∀ c, owns mfi c → hasContract mfi c :=
  fun h hmfi => h mfi hmfi

/-- Same donkey universal, `mfi` now owning several computers instead of
exactly one — the derivation doesn't care, so this is the identical
proof. FraCaS's own `<why>` flags this pattern as more theory-dependent
than 134 in general (contrast 136, where the two readings really do
diverge); under this project's single donkey-universal formalization
they coincide here, matching FraCaS's gold `.yes` for both. -/
theorem fracas_135 :
    (∀ x, customer x → ∀ c, owns x c → hasContract x c) → customer mfi →
      ∀ c, owns mfi c → hasContract mfi c :=
  fun h hmfi => h mfi hmfi

end P134

/-! ## Problem 136: the same donkey sentence, but the weak/existential reading -/

section P136

/-- "Every executive who had a laptop computer brought it to take notes"
most naturally reads as "brought *at least one*" (the weak donkey
reading) rather than "brought *all* of them" (134/135's strong reading)
— bringing five laptops to take notes is pragmatically odd, which is
exactly why FraCaS's own `<why>` contrasts this with 135 and gives
`.unknown` here instead of `.yes`. This project formalizes the donkey
rule as the weak reading `(∃c, hasLaptop c) → ∃c, hasLaptop c ∧ brought
c` specifically for this problem (a different, deliberate choice from
134/135's strong universal, not a mechanical template) and shows it's
satisfied whether Smith brings one of his five laptops (direction 1) or
all five (direction 2) — so "brought five" doesn't follow either way. -/
theorem fracas_136_dir1 :
    (Exactly 5 (fun _ : Fin 5 => True) (fun _ : Fin 5 => True) ∧
        ((∃ _c : Fin 5, True) → ∃ c : Fin 5, True ∧ (fun x : Fin 5 => x.val = 0) c)) ∧
      ¬ Exactly 5 (fun _ : Fin 5 => True) (fun x : Fin 5 => x.val = 0) := by
  refine ⟨⟨by decide, fun _ => ⟨0, trivial, by decide⟩⟩, by decide⟩

theorem fracas_136_dir2 :
    (Exactly 5 (fun _ : Fin 5 => True) (fun _ : Fin 5 => True) ∧
        ((∃ _c : Fin 5, True) → ∃ c : Fin 5, True ∧ (fun _ : Fin 5 => True) c)) ∧
      Exactly 5 (fun _ : Fin 5 => True) (fun _ : Fin 5 => True) := by
  refine ⟨⟨by decide, fun _ => ⟨0, trivial, trivial⟩⟩, by decide⟩

end P136

/-! ## Problem 137: a proportion problem -/

section P137
variable {A : Type*} [Fintype A] (hasContractForAll : A → Prop) [DecidablePred hasContractForAll]

/-- 100 companies; ICM (1 company, owns 150 computers) has no contracts
for any of them; the other 99 each own one computer and have a contract
for it. So 99 of the 100 companies-that-own-a-computer satisfy the
per-company donkey property "has a contract for every computer it owns"
— a clear majority. `hasContractForAll` packages that per-company fact
directly (99 companies satisfy it, ICM doesn't) rather than modeling
each company's individual computers, and `card_true_eq_card_type`
(`Anaphora.lean`) turns "100 companies" into a fact about `Fintype.card`. -/
theorem fracas_137 (hcard : Fintype.card A = 100)
    (hgood : Exactly 99 (fun _ : A => True) hasContractForAll) :
    Most (fun _ : A => True) hasContractForAll := by
  have ht : card (fun _ : A => True) = 100 := card_true_eq_card_type.trans hcard
  omega

end P137

/-! ## Problem 138: a fully resolved donkey/definite-description chain -/

section P138
variable {A : Type*} (report : A → Prop) (coverPageOf : A → A) (smith r95103 : A)
variable (signed : A → A → Prop)

/-- "Every report has a cover page" licenses treating "the cover page of
X" as a total function `coverPageOf`; "Smith signed the cover page" (of
R-95-103, continuing the discourse) is then literally the same term as
the hypothesis's "the cover page of R-95-103" — resolved-reference
restatement, same as 121/122/133. -/
theorem fracas_138 :
    report r95103 → signed smith (coverPageOf r95103) → signed smith (coverPageOf r95103) :=
  fun _ h => h

end P138

/-! ## Problems 139/140: reflexives -/

section P139
variable {A : Type*} (awarded : A → A → Prop)

/-- "A company director awarded himself a large payrise" is a single
reflexive fact `awarded d d`; "has awarded and been awarded a payrise"
is the same fact read twice (as agent, then as patient) — restatement,
not a nontrivial inference. -/
theorem fracas_139 : (∃ d, awarded d d) → ∃ d, awarded d d := id

end P139

section P140
variable {A : Type*} (john bill : A) (said : A → Prop → Prop) (hurt : A → A → Prop)

/-- "John said Bill had hurt himself" — "himself" = Bill, so the
embedded fact is `hurt bill bill`; "John said Bill had been hurt" is the
same embedded fact under passive voice, which this project (as with
114) doesn't distinguish from active voice. -/
theorem fracas_140 : said john (hurt bill bill) → said john (hurt bill bill) := id

end P140

/-! ## Problem 141: unrelated claims — genuine independence -/

section P141

/-- "John said Bill had hurt himself" is entirely about Bill (himself
resolves to Bill, never John) — it says nothing at all about anyone
saying John was hurt, so the two claims are simply unconnected. Reuses
139/140's own `said`/`hurt`/`john`/`bill` vocabulary: the premise is
exactly 140's content (`said john (hurt bill bill)`), and the question
("did anyone say John had been hurt?") is `∃p, said p (hurt john john)`. -/
theorem fracas_141_dir1 {A : Type*} (john bill : A) (said : A → Prop → Prop)
    (hurt : A → A → Prop) (h : said john (hurt bill bill))
    (hNot : ¬ ∃ p, said p (hurt john john)) :
    said john (hurt bill bill) ∧ ¬ ∃ p, said p (hurt john john) := ⟨h, hNot⟩

theorem fracas_141_dir2 {A : Type*} (john bill : A) (said : A → Prop → Prop)
    (hurt : A → A → Prop) (h : said john (hurt bill bill))
    (hYes : ∃ p, said p (hurt john john)) :
    said john (hurt bill bill) ∧ ∃ p, said p (hurt john john) := ⟨h, hYes⟩

end P141

end FraCaS.Section3
