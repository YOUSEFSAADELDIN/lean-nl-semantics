import LeanNLSemantics.FraCaS.Section1.GQ

/-!
# Shared machinery for FraCaS Section 2 (Plurals)

Section 2 is far less uniform than Section 1: rather than one
determiner-monotonicity phenomenon worked across many vocabularies, it's
~10 distinct plural phenomena (named-individual conjunction, exact
cardinality, NP- vs N-bar-conjunction ambiguity, distributive-forcing
"all", collective-vs-distributive predication, bare-plural existential
vs. quasi-universal readings, generics, cumulative/distributive
"and"-conjunction) each needing its own small piece of machinery rather
than one shared combinator. This file adds only what Section 1's
`GQ.lean` doesn't already have: exact cardinality (`Exactly`) and two
lemmas connecting it to `Some`/`No`, plus one lemma making the
"universal survives to majority, given nonemptiness" step explicit
(`every_most`). Everything else in this section either reuses `GQ.lean`
directly or is small enough to write inline per problem.
-/

namespace FraCaS.Section2

open FraCaS.Section1

/-- "Exactly n P are Q" — Section 2's own determiner ("exactly two
lawyers", "just one accountant"), not needed anywhere in Section 1. -/
abbrev Exactly {A : Type*} [Fintype A] (n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] : Prop :=
  card (fun x => P x ∧ Q x) = n

/-- Two different exact counts of the same restrictor/scope pair are
mutually exclusive — problems 85/86's "exactly two lawyers signed ⊢ not
six lawyers signed" shape (a cardinality is a specific number, not a
range). -/
theorem exactly_ne {A : Type*} [Fintype A] (m n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] (hmn : m ≠ n) :
    Exactly m P Q → ¬ Exactly n P Q :=
  fun h1 h2 => hmn (h1.symm.trans h2)

/-- A nonzero exact count refutes `No` — problems 105/106's "just one
accountant attended ⊢ not no accountants/accountant attended" shape. -/
theorem exactly_pos_not_no {A : Type*} [Fintype A] (n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] (hn : n ≠ 0) (h : Exactly n P Q) : ¬ No P Q := by
  intro hno
  have hempty : (Finset.univ.filter fun x => P x ∧ Q x) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun x _ hx => hno x hx.1 hx.2)
  have hzero : card (fun x => P x ∧ Q x) = 0 := by simp [hempty]
  omega

/-- A nonzero exact count gives `Some` — problems 107/108/110's "just one
accountant attended ⊢ some accountant(s) attended" shape (also 109,
where this project's `Some` — a plain existential, no "more than one"
plurality presupposition — diverges from FraCaS's own nonstandard
reading; see `Batch2.lean`). -/
theorem some_of_exactly {A : Type*} [Fintype A] (n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] (hn : n ≠ 0) (h : Exactly n P Q) : Some P Q := by
  have hpos : 0 < card (fun x => P x ∧ Q x) := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter] at hx
  exact ⟨x, hx.2⟩

/-- `Every P Q` lifts to `Most P Q`, given `P` is nonempty (100% is a
majority, but only if there's anyone to be a majority *of*) — problem
100's "clients were impressed [quasi-universal reading] ⊢ most clients
were impressed" shape. -/
theorem every_most {A : Type*} [Fintype A] (P Q : A → Prop)
    [DecidablePred P] [DecidablePred fun x => P x ∧ Q x]
    (hne : ∃ x, P x) (h : Every P Q) : Most P Q := by
  have heq : (Finset.univ.filter fun x => P x ∧ Q x) = Finset.univ.filter P := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, h x hx⟩⟩
  have heqc : card (fun x => P x ∧ Q x) = card P := by simp [heq]
  obtain ⟨x0, hx0⟩ := hne
  have hpos : 0 < card P := by
    have hmem : x0 ∈ Finset.univ.filter P := by simp [Finset.mem_filter, hx0]
    exact Finset.card_pos.mpr ⟨x0, hmem⟩
  have hgoal : 2 * card (fun x => P x ∧ Q x) > card P := by omega
  exact hgoal

end FraCaS.Section2
