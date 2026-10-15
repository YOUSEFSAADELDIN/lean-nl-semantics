import EndToEnd.Encodings.Selection

/-!
# What a noun means, as far as inference can tell

`Characterization.lean` shows a noun's identity criterion matters to
inference, and the translation theorems show predicates with criteria
lose nothing against types. This file asks the question both point to:
which part of a noun's interpretation do sentences actually see?

A noun is interpreted by a finite type, its embedding into the
individuals and an identity criterion (`NounI`). Its **counting units**
are the criterion's values; each unit covers the individuals its
elements embed to (`NounI.unit`). `NounI.units S` says how many units
cover exactly the set of individuals `S`.

**`obsEq_iff` (full abstraction).** Two interpretations of a noun are
indistinguishable by every formula of the fragment, in every context
(any interpretation of the other nouns, the verbs, the relations and
the names), exactly when they have the same counting units with the
same multiplicities: the same multiset of covered sets.

- One person on three journeys is three passenger units, each covering
  that person. Two copies of one novel, counted as texts, are one unit
  covering both copies.
- **Nouns that count individuals are their extensions
  (`obsEq_byInd_iff`).** For such a noun two interpretations are
  indistinguishable exactly when their extensions agree: Montague's
  nouns as predicates.

So, inferentially, a count noun means a multiset of nonempty sets of
individuals. Nouns as types with criteria and nouns as predicates with
criteria are two ways of writing one down.

How the proof goes. "Every", "some", "no" and "is an `N`" see only the
extension, the union of the units. "Exactly `j` `N`s are `v`", with `v`
free to mean any set `P`, sees how many units meet `P` (`count_meets`).
Those counts determine the multiset (`eq_of_meets`): the units inside a
set `S` are all units less those meeting its complement, and the units
equal to `S` follow by strong induction on `S`. The vocabulary needs one
verb.

Nouns with several criteria (copredication) are in
`FullAbstractionMulti.lean`: there the counts are all sentences see,
and they need not come from any single criterion.
-/

namespace FraCaS.Encodings.FullAbstraction
open FraCaS.Encodings.Typed FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence
open FraCaS.Encodings.Relational
open FraCaS.Encodings.Selection (countBy_congr)
open Classical

/-! ## Combinatorics: counts that meet every set determine a family -/

section Comb
variable {A : Type} [Fintype A]

/-- The total weight of the sets that meet `P`. -/
noncomputable def meetsSum (u : Finset A → ℕ) (P : A → Prop) : ℕ :=
  ∑ R : Finset A, if ∃ x ∈ R, P x then u R else 0

theorem split_sub (u : Finset A → ℕ) (S : Finset A) :
    (∑ R : Finset A, if R ⊆ S then u R else 0) + meetsSum u (fun x => x ∉ S) =
      ∑ R : Finset A, u R := by
  unfold meetsSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun R _ => ?_
  split_ifs with h1 h2 h2
  · exfalso
    obtain ⟨x, hx, hxS⟩ := h2
    exact hxS (h1 hx)
  · omega
  · omega
  · exfalso
    exact h2 (Finset.not_subset.mp h1)

theorem subsets_eq {u u' : Finset A → ℕ} (h0 : u ∅ = u' ∅)
    (H : ∀ P, meetsSum u P = meetsSum u' P) (S : Finset A) :
    (∑ R : Finset A, if R ⊆ S then u R else 0) = ∑ R : Finset A, if R ⊆ S then u' R else 0 := by
  have hE : (∑ R : Finset A, if R ⊆ (∅ : Finset A) then u R else 0) =
      ∑ R : Finset A, if R ⊆ (∅ : Finset A) then u' R else 0 := by
    refine Finset.sum_congr rfl fun R _ => ?_
    split_ifs with h
    · rw [Finset.subset_empty.mp h, h0]
    · rfl
  have t1 := split_sub u ∅
  have t2 := split_sub u' ∅
  have s1 := split_sub u S
  have s2 := split_sub u' S
  have m0 := H (fun x => x ∉ (∅ : Finset A))
  have mS := H (fun x => x ∉ S)
  omega

theorem split_eq_ssub (v : Finset A → ℕ) (S : Finset A) :
    (∑ R : Finset A, if R ⊆ S then v R else 0) = v S + ∑ R : Finset A, if R ⊂ S then v R else 0 := by
  have hpt : ∀ R : Finset A, (if R ⊆ S then v R else 0) =
      (if R = S then v R else 0) + (if R ⊂ S then v R else 0) := by
    intro R
    by_cases hb : R = S
    · subst hb
      rw [if_pos (Finset.Subset.refl _), if_pos rfl, if_neg (ssubset_irrefl _)]
      omega
    · by_cases ha : R ⊆ S
      · rw [if_pos ha, if_neg hb, if_pos (Finset.ssubset_iff_subset_ne.mpr ⟨ha, hb⟩)]
        omega
      · rw [if_neg ha, if_neg hb, if_neg (fun hc => ha (Finset.ssubset_iff_subset_ne.mp hc).1)]
  calc (∑ R : Finset A, if R ⊆ S then v R else 0)
      = ∑ R : Finset A, ((if R = S then v R else 0) + (if R ⊂ S then v R else 0)) :=
        Finset.sum_congr rfl fun R _ => hpt R
    _ = (∑ R : Finset A, if R = S then v R else 0) + ∑ R : Finset A, if R ⊂ S then v R else 0 :=
        Finset.sum_add_distrib
    _ = v S + ∑ R : Finset A, if R ⊂ S then v R else 0 := by
        rw [Finset.sum_eq_single S (fun b _ hb => if_neg hb)
          (fun h => absurd (Finset.mem_univ S) h), if_pos rfl]

/-- **Counts that meet every set determine the family**, given its
weight on the empty set. -/
theorem eq_of_meets {u u' : Finset A → ℕ} (h0 : u ∅ = u' ∅)
    (H : ∀ P, meetsSum u P = meetsSum u' P) : ∀ S, u S = u' S := by
  intro S
  exact Finset.strongInduction (p := fun S => u S = u' S) (fun S ih => by
    have hV := subsets_eq h0 H S
    rw [split_eq_ssub u S, split_eq_ssub u' S] at hV
    have hW : (∑ R : Finset A, if R ⊂ S then u R else 0) =
        ∑ R : Finset A, if R ⊂ S then u' R else 0 :=
      Finset.sum_congr rfl fun R _ => by
        split_ifs with h
        · exact ih R h
        · rfl
    omega) S

end Comb

/-! ## Noun interpretations and contexts -/

variable {Noun Verb Rel Name A : Type}

/-- An interpretation of a noun: a finite type, its embedding into the
individuals, and an identity criterion. -/
structure NounI (A : Type) where
  T : Type
  fin : Fintype T
  emb : T → A
  K : Type
  crit : T → K

instance (I : NounI A) : Fintype I.T := I.fin

/-- How many of the noun's things are `P`, counted by its criterion. -/
noncomputable def NounI.count (I : NounI A) (P : A → Prop) : Nat :=
  countBy I.crit (fun y => P (I.emb y))

/-- Being one of the noun's individuals. -/
def NounI.ext (I : NounI A) (x : A) : Prop := ∃ y, I.emb y = x

/-- A context: every noun's interpretation, and the verbs, relations and
names. -/
structure Ctx (Noun Verb Rel Name A : Type) where
  noun : Noun → NounI A
  verb : Verb → A → Prop
  rel : Rel → A → A → Prop
  name : Name → A

noncomputable def Ctx.interp (M : Ctx Noun Verb Rel Name A) : Interp Noun Verb Rel Name A where
  q d n C Q := detBy (M.noun n).count (M.noun n).emb d C Q
  more n C Q S := (M.noun n).count (fun x => C x ∧ Q x) > (M.noun n).count (fun x => C x ∧ S x)
  isA n := (M.noun n).ext
  verb := M.verb
  rel := M.rel
  name := M.name

/-- The context with noun `n0` interpreted by `I`. -/
noncomputable def Ctx.set (M : Ctx Noun Verb Rel Name A) (n0 : Noun) (I : NounI A) :
    Ctx Noun Verb Rel Name A :=
  { M with noun := fun n => if n = n0 then I else M.noun n }

theorem Ctx.set_self (M : Ctx Noun Verb Rel Name A) (n0 : Noun) (I : NounI A) :
    (M.set n0 I).noun n0 = I := if_pos rfl

theorem Ctx.set_ne (M : Ctx Noun Verb Rel Name A) {n n0 : Noun} (I : NounI A) (h : n ≠ n0) :
    (M.set n0 I).noun n = M.noun n := if_neg h

/-- Two interpretations of `n0` are indistinguishable: no formula, in no
context, tells them apart. -/
def ObsEq (n0 : Noun) (I I' : NounI A) : Prop :=
  ∀ (M : Ctx Noun Verb Rel Name A) (φ : Form Noun Verb Rel Name) (ρ : Nat → A),
    Form.eval (M.set n0 I).interp φ ρ ↔ Form.eval (M.set n0 I').interp φ ρ

/-! ## What the sentences see: the extension and the counts -/

theorem detBy_obs {T T' : Type} (e : T → A) (e' : T' → A) {cnt cnt' : (A → Prop) → Nat}
    (hE : ∀ x, (∃ y, e y = x) ↔ (∃ y, e' y = x)) (hc : ∀ P, cnt P = cnt' P) (d : Det)
    (C Q : A → Prop) : detBy cnt e d C Q ↔ detBy cnt' e' d C Q := by
  have hall : ∀ R : A → Prop, (∀ y, R (e y)) ↔ (∀ y, R (e' y)) := fun R =>
    ⟨fun h y => by
      obtain ⟨z, hz⟩ := (hE (e' y)).mpr ⟨y, rfl⟩
      rw [← hz]
      exact h z,
     fun h y => by
      obtain ⟨z, hz⟩ := (hE (e y)).mp ⟨y, rfl⟩
      rw [← hz]
      exact h z⟩
  have hex : ∀ R : A → Prop, (∃ y, R (e y)) ↔ (∃ y, R (e' y)) := fun R =>
    ⟨fun ⟨y, hy⟩ => by
      obtain ⟨z, hz⟩ := (hE (e y)).mp ⟨y, rfl⟩
      exact ⟨z, hz ▸ hy⟩,
     fun ⟨y, hy⟩ => by
      obtain ⟨z, hz⟩ := (hE (e' y)).mpr ⟨y, rfl⟩
      exact ⟨z, hz ▸ hy⟩⟩
  cases d with
  | every => exact hall (fun x => C x → Q x)
  | some => exact hex (fun x => C x ∧ Q x)
  | no => exact hall (fun x => C x → ¬ Q x)
  | most =>
    show 2 * cnt (fun x => C x ∧ Q x) > cnt C ↔ 2 * cnt' (fun x => C x ∧ Q x) > cnt' C
    rw [hc, hc]
  | both =>
    show cnt C = 2 ∧ EveryT e C Q ↔ cnt' C = 2 ∧ EveryT e' C Q
    rw [hc]
    exact and_congr Iff.rfl (hall (fun x => C x → Q x))
  | neither =>
    show cnt C = 2 ∧ NoT e C Q ↔ cnt' C = 2 ∧ NoT e' C Q
    rw [hc]
    exact and_congr Iff.rfl (hall (fun x => C x → ¬ Q x))
  | atLeast k =>
    show cnt (fun x => C x ∧ Q x) ≥ k ↔ cnt' (fun x => C x ∧ Q x) ≥ k
    rw [hc]
  | atMost k =>
    show cnt (fun x => C x ∧ Q x) ≤ k ↔ cnt' (fun x => C x ∧ Q x) ≤ k
    rw [hc]
  | exactly k =>
    show cnt (fun x => C x ∧ Q x) = k ↔ cnt' (fun x => C x ∧ Q x) = k
    rw [hc]

/-- Interpretations with the same extension and the same counts agree on
everything. -/
theorem agree_of (M : Ctx Noun Verb Rel Name A) (n0 : Noun) {I I' : NounI A}
    (hE : ∀ x, I.ext x ↔ I'.ext x) (hc : ∀ P, I.count P = I'.count P) :
    (M.set n0 I).interp.Agree (M.set n0 I').interp where
  q d n C Q := by
    show detBy ((M.set n0 I).noun n).count ((M.set n0 I).noun n).emb d C Q ↔
      detBy ((M.set n0 I').noun n).count ((M.set n0 I').noun n).emb d C Q
    by_cases h : n = n0
    · subst h
      rw [M.set_self, M.set_self]
      exact detBy_obs I.emb I'.emb hE hc d C Q
    · rw [M.set_ne I h, M.set_ne I' h]
  more n C Q S := by
    show ((M.set n0 I).noun n).count (fun x => C x ∧ Q x) >
        ((M.set n0 I).noun n).count (fun x => C x ∧ S x) ↔
      ((M.set n0 I').noun n).count (fun x => C x ∧ Q x) >
        ((M.set n0 I').noun n).count (fun x => C x ∧ S x)
    by_cases h : n = n0
    · subst h
      rw [M.set_self, M.set_self, hc, hc]
    · rw [M.set_ne I h, M.set_ne I' h]
  isA n x := by
    show ((M.set n0 I).noun n).ext x ↔ ((M.set n0 I').noun n).ext x
    by_cases h : n = n0
    · subst h
      rw [M.set_self, M.set_self]
      exact hE x
    · rw [M.set_ne I h, M.set_ne I' h]
  verb _ _ := Iff.rfl
  rel _ _ _ := Iff.rfl
  name _ := rfl

theorem count_congr (I : NounI A) {P P' : A → Prop} (h : ∀ x, P x ↔ P' x) :
    I.count P = I.count P' := by
  unfold NounI.count
  exact countBy_congr fun y => h _

theorem count_empty (I : NounI A) (hA : IsEmpty A) (P : A → Prop) : I.count P = 0 := by
  have : IsEmpty I.T := ⟨fun y => hA.false (I.emb y)⟩
  unfold NounI.count countBy
  simp

/-- Indistinguishable interpretations have the same extension: "some
`n0` is `v`", with `v` true of one individual. -/
theorem ext_of_obs (v : Verb) {n0 : Noun} {I I' : NounI A}
    (h : ObsEq (Verb := Verb) (Rel := Rel) (Name := Name) n0 I I') (x : A) :
    I.ext x ↔ I'.ext x := by
  let M : Ctx Noun Verb Rel Name A := ⟨fun _ => I, fun _ y => y = x, fun _ _ _ => False, fun _ => x⟩
  have key : ∀ J : NounI A,
      Form.eval (M.set n0 J).interp (.quant .some n0 (.verb v (.var 0)) .top) (fun _ => x) ↔
        J.ext x := by
    intro J
    show SomeT ((M.set n0 J).noun n0).emb (fun y => y = x) (fun _ => True) ↔ J.ext x
    rw [M.set_self]
    exact ⟨fun ⟨y, hy, _⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy, trivial⟩⟩
  exact (key I).symm.trans ((h M _ _).trans (key I'))

/-- Indistinguishable interpretations have the same counts: "exactly `j`
`n0`s are `v`", with `v` true of `P`. -/
theorem count_of_obs (v : Verb) {n0 : Noun} {I I' : NounI A}
    (h : ObsEq (Verb := Verb) (Rel := Rel) (Name := Name) n0 I I') (P : A → Prop) :
    I.count P = I'.count P := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a⟩⟩
  · rw [count_empty I hA, count_empty I' hA]
  · let M : Ctx Noun Verb Rel Name A := ⟨fun _ => I, fun _ => P, fun _ _ _ => False, fun _ => a⟩
    have key : ∀ (J : NounI A) (j : Nat),
        Form.eval (M.set n0 J).interp (.quant (.exactly j) n0 (.verb v (.var 0)) .top)
          (fun _ => a) ↔ J.count (fun z => P z ∧ True) = j := by
      intro J j
      show ((M.set n0 J).noun n0).count (fun z => P z ∧ True) = j ↔
        J.count (fun z => P z ∧ True) = j
      rw [M.set_self]
    have h1 := (key I' (I.count (fun z => P z ∧ True))).mp ((h M _ _).mp ((key I _).mpr rfl))
    have hPI := count_congr I (P := fun z => P z ∧ True) (P' := P)
      (fun z => ⟨fun hz => hz.1, fun hz => ⟨hz, trivial⟩⟩)
    have hPI' := count_congr I' (P := fun z => P z ∧ True) (P' := P)
      (fun z => ⟨fun hz => hz.1, fun hz => ⟨hz, trivial⟩⟩)
    omega

/-! ## Counting units -/

/-- The individuals a unit covers. -/
noncomputable def NounI.unit (I : NounI A) (k : I.K) : Finset A :=
  (Finset.univ.filter (fun y => I.crit y = k)).image I.emb

/-- The units. -/
noncomputable def NounI.keys (I : NounI A) : Finset I.K := Finset.univ.image I.crit

/-- How many units cover exactly `S`. -/
noncomputable def NounI.units (I : NounI A) (S : Finset A) : Nat :=
  (I.keys.filter (fun k => I.unit k = S)).card

theorem NounI.mem_unit (I : NounI A) (k : I.K) (x : A) :
    x ∈ I.unit k ↔ ∃ y, I.crit y = k ∧ I.emb y = x := by
  unfold NounI.unit
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
    exact ⟨y, (Finset.mem_filter.mp hy).2, rfl⟩
  · rintro ⟨y, hk, rfl⟩
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩

theorem units_empty (I : NounI A) : I.units ∅ = 0 := by
  unfold NounI.units
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hu
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hk
  have hy : I.emb y ∈ I.unit (I.crit y) := (I.mem_unit _ _).mpr ⟨y, rfl, rfl⟩
  rw [hu] at hy
  simp at hy

theorem count_eq (I : NounI A) (P : A → Prop) :
    I.count P = (I.keys.filter (fun k => ∃ x ∈ I.unit k, P x)).card := by
  unfold NounI.count countBy NounI.keys
  congr 1
  ext k
  constructor
  · intro hk
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩, I.emb y, ?_,
      (Finset.mem_filter.mp hy).2⟩
    exact (I.mem_unit _ _).mpr ⟨y, rfl, rfl⟩
  · intro hk
    obtain ⟨-, x, hx, hP⟩ := Finset.mem_filter.mp hk
    obtain ⟨y, hyk, rfl⟩ := (I.mem_unit _ _).mp hx
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩, hyk⟩

/-- **A noun counts by its units**: how many `N`s are `P` is the weight
of the units that meet `P`. -/
theorem count_meets [Fintype A] (I : NounI A) (P : A → Prop) :
    I.count P = meetsSum I.units P := by
  rw [count_eq, Finset.card_eq_sum_card_fiberwise (f := I.unit) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  unfold meetsSum
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hS : ∃ x ∈ S, P x
  · rw [if_pos hS]
    unfold NounI.units
    congr 1
    ext k
    constructor
    · intro hk
      obtain ⟨hk1, hu⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk1).1, hu⟩
    · intro hk
      obtain ⟨hk1, hu⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hk1, by rw [hu]; exact hS⟩, hu⟩
  · rw [if_neg hS, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk hu
    exact hS (hu ▸ (Finset.mem_filter.mp hk).2)

theorem ext_iff_count (I : NounI A) (x : A) : I.ext x ↔ 0 < I.count (fun z => z = x) := by
  unfold NounI.count countBy
  constructor
  · rintro ⟨y, hy⟩
    exact Finset.card_pos.mpr
      ⟨I.crit y, Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩⟩
  · intro h
    obtain ⟨k, hk⟩ := Finset.card_pos.mp h
    obtain ⟨y, hy, -⟩ := Finset.mem_image.mp hk
    exact ⟨y, (Finset.mem_filter.mp hy).2⟩

/-! ## Full abstraction -/

/-- **Full abstraction.** Two interpretations of a noun are
indistinguishable by every formula in every context exactly when they
have the same counting units, with the same multiplicities. -/
theorem obsEq_iff [Fintype A] (v : Verb) (n0 : Noun) (I I' : NounI A) :
    ObsEq (Verb := Verb) (Rel := Rel) (Name := Name) n0 I I' ↔ ∀ S, I.units S = I'.units S := by
  constructor
  · intro h
    have hc := count_of_obs v h
    exact eq_of_meets (by rw [units_empty, units_empty])
      (fun P => (count_meets I P).symm.trans ((hc P).trans (count_meets I' P)))
  · intro hu
    have hm : I.units = I'.units := funext hu
    have hc : ∀ P, I.count P = I'.count P := fun P => by
      rw [count_meets, count_meets, hm]
    have hE : ∀ x, I.ext x ↔ I'.ext x := fun x => by
      rw [ext_iff_count, ext_iff_count, hc]
    intro M φ ρ
    exact (agree_of M n0 hE hc).eval φ ρ

/-! ## Nouns that count individuals are their extensions -/

/-- The same type and embedding, counted by the individuals' own
identity. -/
def NounI.byInd (I : NounI A) : NounI A := ⟨I.T, I.fin, I.emb, A, I.emb⟩

theorem count_byInd [Fintype A] (I : NounI A) (P : A → Prop) :
    I.byInd.count P = (Finset.univ.filter (fun x => I.ext x ∧ P x)).card := by
  unfold NounI.count countBy
  show ((Finset.univ.filter (fun y => P (I.emb y))).image I.emb).card = _
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨y, rfl⟩, (Finset.mem_filter.mp hy).2⟩
  · intro hx
    obtain ⟨-, ⟨y, rfl⟩, hP⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩, rfl⟩

/-- **Montague, recovered.** For nouns that count individuals, two
interpretations are indistinguishable exactly when their extensions
agree. -/
theorem obsEq_byInd_iff [Fintype A] (v : Verb) (n0 : Noun) (I J : NounI A) :
    ObsEq (Verb := Verb) (Rel := Rel) (Name := Name) n0 I.byInd J.byInd ↔
      ∀ x, I.ext x ↔ J.ext x := by
  constructor
  · intro h x
    exact ext_of_obs v h x
  · intro hE M φ ρ
    have hc : ∀ P, I.byInd.count P = J.byInd.count P := fun P => by
      rw [count_byInd, count_byInd]
      congr 1
      exact Finset.filter_congr (fun x _ => and_congr (hE x) Iff.rfl)
    exact (agree_of (I := I.byInd) (I' := J.byInd) M n0 hE hc).eval φ ρ

end FraCaS.Encodings.FullAbstraction

/-- info: 'FraCaS.Encodings.FullAbstraction.obsEq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.FullAbstraction.obsEq_iff
