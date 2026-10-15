import EndToEnd.Encodings.Relational

/-!
# Nouns as types, translated word by word into nouns as predicates

`validI_iff` and `validRI_iff` show nouns as types and nouns as
predicates validate the same entailments when counting is by
individuals. `Characterization.lean` shows they part ways exactly when
a noun counts by its own identity criterion, as Chatzikyriakidis & Luo
(2018) have nouns do: one person on two journeys is two passengers. The
predicate accounts of such counting (Gotham 2017; Asher 2011) keep
nouns as predicates but enrich the model: a domain that contains the
things counted (passenger journeys, composite books), a relation of
being one individual, and individuation relations to count by.

This file shows that the two are the same logic, for the fragment of
`Relational.lean` (determiners, "more", one- and two-place verbs,
identity, connectives, nested quantifiers).

- **Source.** Nouns as types with identity criteria (`CModel`): each
  noun is a finite type embedded in the individuals and counts by its
  criterion (`cI`).
- **Target.** Nouns as predicates with criteria (`PCModel`): one finite
  domain; nouns, verbs and relations are predicates of it; a relation
  `same` of being one individual, which the predicates respect; and for
  each noun a criterion on the domain, which its determiners count by
  (`pcI`).
- **The translation (`tr`)** is word by word: every word and
  construction goes to itself, except identity ("`t` is `u`"), which
  goes to the relation `same`.

**`validC_iff`.** An entailment is valid with nouns as types and
identity criteria exactly when its translation is valid with nouns as
predicates and criteria. Two model constructions do it:

- `toPC`: a typed model becomes a predicate model whose domain
  is its individuals plus one object for each element of each noun's
  type (the passenger journeys, say), each object standing for its
  individual (`toPC_eval`).
- `PCModel.quotC`: a predicate model becomes a typed model whose
  individuals are its `same`-classes and whose types are its nouns'
  members (`quot_eval`).

So in this fragment nouns as types, even with identity criteria, are
inferentially a notational variant of nouns as predicates over a domain
with an identity relation and criteria of individuation. Nothing
inferential is owed to nouns being types. What the predicate side needs
is ontology: a domain containing what is counted.

The lexicon is assumed finite (`Fintype Noun`), so that the domain of
`toPC` is finite. Each noun has one criterion; copredication, which
counts by two at once (`DotSetoid.lean`), is not covered.
-/

namespace FraCaS.Encodings.Translation
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed
open FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence FraCaS.Encodings.Relational

variable {Noun Verb Rel Name : Type}

/-! ## The translation -/

/-- Word by word: identity becomes the relation `none`, "being one
individual"; every other word and construction is kept. -/
def tr : Form Noun Verb Rel Name → Form Noun Verb (Option Rel) Name
  | .verb v t => .verb v t
  | .rel r t u => .rel (some r) t u
  | .isA n t => .isA n t
  | .eq t u => .rel none t u
  | .top => .top
  | .not φ => .not (tr φ)
  | .and φ ψ => .and (tr φ) (tr ψ)
  | .or φ ψ => .or (tr φ) (tr ψ)
  | .imp φ ψ => .imp (tr φ) (tr ψ)
  | .quant d n C Q => .quant d n (tr C) (tr Q)
  | .more n C Q S => .more n (tr C) (tr Q) (tr S)

/-! ## Nouns as predicates with criteria -/

/-- One finite domain with predicates for nouns and verbs, relations, a
relation `same` of being one individual that they respect, and a
criterion for each noun. -/
structure PCModel (Noun Verb Rel Name : Type) where
  A : Type
  fin : Fintype A
  noun : Noun → A → Prop
  verb : Verb → A → Prop
  rel : Rel → A → A → Prop
  name : Name → A
  same : A → A → Prop
  same_equiv : Equivalence same
  K : Noun → Type
  crit : ∀ n, A → K n
  noun_cong : ∀ n a b, same a b → noun n a → noun n b
  verb_cong : ∀ v a b, same a b → verb v a → verb v b
  rel_cong : ∀ r a a' b b', same a a' → same b b' → rel r a b → rel r a' b'

instance (G : PCModel Noun Verb Rel Name) : Fintype G.A := G.fin

open Classical in
/-- How many `n`s are `P`, counted by `n`'s criterion. -/
noncomputable def PCModel.countP (G : PCModel Noun Verb Rel Name) (n : Noun) (P : G.A → Prop) :
    Nat :=
  countBy (fun y : {a // G.noun n a} => G.crit n y.val) (fun y => P y.val)

/-- The predicate encoding's interpretation: a determiner over `n`
ranges over the members of `n` and counts by `n`'s criterion. -/
noncomputable def pcI (G : PCModel Noun Verb Rel Name) : Interp Noun Verb (Option Rel) Name G.A where
  q d n C Q := detBy (G.countP n) (fun y : {a // G.noun n a} => y.val) d C Q
  more n C Q S := G.countP n (fun x => C x ∧ Q x) > G.countP n (fun x => C x ∧ S x)
  isA := G.noun
  verb := G.verb
  rel r := r.elim G.same G.rel
  name := G.name

/-! ## Validity -/

/-- Valid with nouns as types and identity criteria. -/
def ValidC (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) : Prop :=
  ∀ (M : CModel Noun Verb Name) (R : Rel → M.A → M.A → Prop) (ρ : Nat → M.A),
    (∀ ψ ∈ Γ, Form.eval (cI M R) ψ ρ) → Form.eval (cI M R) φ ρ

/-- The translation is valid with nouns as predicates and criteria. -/
def ValidPC (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) : Prop :=
  ∀ (G : PCModel Noun Verb Rel Name) (ρ : Nat → G.A),
    (∀ ψ ∈ Γ, Form.eval (pcI G) (tr ψ) ρ) → Form.eval (pcI G) (tr φ) ρ

/-! ## Two ways of counting that see the same things -/

theorem countBy_sim {N N' K K' : Type} {_ : Fintype N} {_ : Fintype N'} {_ : DecidableEq K}
    {_ : DecidableEq K'} {crit : N → K} {crit' : N' → K'} {j : K → K'}
    (hj : Function.Injective j) {P : N → Prop} {P' : N' → Prop} {_ : DecidablePred P}
    {_ : DecidablePred P'}
    (h1 : ∀ y, P y → ∃ a, P' a ∧ crit' a = j (crit y))
    (h2 : ∀ a, P' a → ∃ y, P y ∧ crit' a = j (crit y)) :
    countBy crit' P' = countBy crit P := by
  unfold countBy
  refine Eq.trans ?_ (Finset.card_image_of_injective _ hj)
  congr 1
  ext k
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨y, hy, he⟩ := h2 a ha
    exact ⟨crit y, ⟨y, hy, rfl⟩, he.symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨a, ha, he⟩ := h1 y hy
    exact ⟨a, ha, he⟩

/-- Two determiner meanings agree when each element of one domain has a
counterpart in the other that the restrictor and scope treat alike, and
the counts agree. -/
theorem detBy_sim {N N' A A' : Type} {cnt : (A → Prop) → Nat} {cnt' : (A' → Prop) → Nat}
    {e : N → A} {e' : N' → A'} (d : Det) {C Q : A → Prop} {C' Q' : A' → Prop}
    (h1 : ∀ y, ∃ a, (C' (e' a) ↔ C (e y)) ∧ (Q' (e' a) ↔ Q (e y)))
    (h2 : ∀ a, ∃ y, (C' (e' a) ↔ C (e y)) ∧ (Q' (e' a) ↔ Q (e y)))
    (hc1 : cnt' (fun x => C' x ∧ Q' x) = cnt (fun x => C x ∧ Q x)) (hc2 : cnt' C' = cnt C) :
    detBy cnt' e' d C' Q' ↔ detBy cnt e d C Q := by
  have hEv : EveryT e' C' Q' ↔ EveryT e C Q := by
    constructor
    · intro h y hy
      obtain ⟨a, hC, hQ⟩ := h1 y
      exact hQ.mp (h a (hC.mpr hy))
    · intro h a ha
      obtain ⟨y, hC, hQ⟩ := h2 a
      exact hQ.mpr (h y (hC.mp ha))
  have hNo : NoT e' C' Q' ↔ NoT e C Q := by
    constructor
    · intro h y hy hq
      obtain ⟨a, hC, hQ⟩ := h1 y
      exact h a (hC.mpr hy) (hQ.mpr hq)
    · intro h a ha hq
      obtain ⟨y, hC, hQ⟩ := h2 a
      exact h y (hC.mp ha) (hQ.mp hq)
  have hSome : SomeT e' C' Q' ↔ SomeT e C Q := by
    constructor
    · rintro ⟨a, ha, hq⟩
      obtain ⟨y, hC, hQ⟩ := h2 a
      exact ⟨y, hC.mp ha, hQ.mp hq⟩
    · rintro ⟨y, hy, hq⟩
      obtain ⟨a, hC, hQ⟩ := h1 y
      exact ⟨a, hC.mpr hy, hQ.mpr hq⟩
  cases d with
  | every => exact hEv
  | some => exact hSome
  | no => exact hNo
  | most =>
    show 2 * cnt' (fun x => C' x ∧ Q' x) > cnt' C' ↔ 2 * cnt (fun x => C x ∧ Q x) > cnt C
    rw [hc1, hc2]
  | both =>
    show cnt' C' = 2 ∧ EveryT e' C' Q' ↔ cnt C = 2 ∧ EveryT e C Q
    rw [hc2]
    exact and_congr Iff.rfl hEv
  | neither =>
    show cnt' C' = 2 ∧ NoT e' C' Q' ↔ cnt C = 2 ∧ NoT e C Q
    rw [hc2]
    exact and_congr Iff.rfl hNo
  | atLeast k =>
    show cnt' (fun x => C' x ∧ Q' x) ≥ k ↔ cnt (fun x => C x ∧ Q x) ≥ k
    rw [hc1]
  | atMost k =>
    show cnt' (fun x => C' x ∧ Q' x) ≤ k ↔ cnt (fun x => C x ∧ Q x) ≤ k
    rw [hc1]
  | exactly k =>
    show cnt' (fun x => C' x ∧ Q' x) = k ↔ cnt (fun x => C x ∧ Q x) = k
    rw [hc1]

theorem gt_congr {a b c d : Nat} (h1 : a = c) (h2 : b = d) : a > b ↔ c > d := by
  subst h1; subst h2; exact Iff.rfl

theorem comp_push {A B : Type} (f : A → B) (x : A) (ρ : Nat → A) :
    f ∘ push x ρ = push (f x) (f ∘ ρ) := by
  funext k
  cases k <;> rfl

/-! ## From predicates to types: individuals are `same`-classes -/

def PCModel.setoid (G : PCModel Noun Verb Rel Name) : Setoid G.A := ⟨G.same, G.same_equiv⟩

open Classical in
/-- The typed model of a predicate model: individuals are classes of
`same`, each noun's type is its members, and each counts by its
criterion. -/
noncomputable def PCModel.quotC (G : PCModel Noun Verb Rel Name) : CModel Noun Verb Name where
  A := Quotient G.setoid
  fin := inferInstance
  T n := {a : G.A // G.noun n a}
  finT _ := inferInstance
  emb _ y := Quotient.mk G.setoid y.val
  verb v x := ∃ a, Quotient.mk G.setoid a = x ∧ G.verb v a
  name c := Quotient.mk G.setoid (G.name c)
  K := G.K
  crit n y := G.crit n y.val

/-- The relations of the typed model of a predicate model. -/
def PCModel.relQ (G : PCModel Noun Verb Rel Name) :
    Rel → G.quotC.A → G.quotC.A → Prop :=
  fun r x y => ∃ a b, Quotient.mk G.setoid a = x ∧ Quotient.mk G.setoid b = y ∧ G.rel r a b

theorem PCModel.mk_eq (G : PCModel Noun Verb Rel Name) {a b : G.A} :
    Quotient.mk G.setoid a = Quotient.mk G.setoid b ↔ G.same a b :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

theorem PCModel.term_mk (G : PCModel Noun Verb Rel Name) (ρ : Nat → G.A) :
    ∀ t : Term Name, Term.eval G.quotC.name (Quotient.mk G.setoid ∘ ρ) t =
      Quotient.mk G.setoid (Term.eval G.name ρ t)
  | .var _ => rfl
  | .name _ => rfl

theorem PCModel.count_quot (G : PCModel Noun Verb Rel Name) (n : Noun) {Pm : G.quotC.A → Prop}
    {P : G.A → Prop} (h : ∀ a, Pm (Quotient.mk G.setoid a) ↔ P a) :
    G.quotC.countC n Pm = G.countP n P := by
  unfold CModel.countC PCModel.countP
  refine countBy_sim (j := id) Function.injective_id ?_ ?_
  · intro y hy
    exact ⟨y, (h y.val).mpr hy, rfl⟩
  · intro a ha
    exact ⟨a, (h a.val).mp ha, rfl⟩

/-- A predicate model and its typed model make the same formulas true,
identity read as `same`. -/
theorem PCModel.quot_eval (G : PCModel Noun Verb Rel Name) :
    ∀ (φ : Form Noun Verb Rel Name) (ρ : Nat → G.A),
      Form.eval (cI G.quotC G.relQ) φ (Quotient.mk G.setoid ∘ ρ) ↔ Form.eval (pcI G) (tr φ) ρ
  | .verb v t, ρ => by
    show (∃ a, Quotient.mk G.setoid a = Term.eval G.quotC.name (Quotient.mk G.setoid ∘ ρ) t ∧
      G.verb v a) ↔ G.verb v (Term.eval G.name ρ t)
    rw [G.term_mk ρ t]
    exact ⟨fun ⟨a, ha, hv⟩ => G.verb_cong v a _ (G.mk_eq.mp ha) hv, fun hv => ⟨_, rfl, hv⟩⟩
  | .rel r t u, ρ => by
    show (∃ a b, Quotient.mk G.setoid a = Term.eval G.quotC.name (Quotient.mk G.setoid ∘ ρ) t ∧
      Quotient.mk G.setoid b = Term.eval G.quotC.name (Quotient.mk G.setoid ∘ ρ) u ∧
      G.rel r a b) ↔ G.rel r (Term.eval G.name ρ t) (Term.eval G.name ρ u)
    rw [G.term_mk ρ t, G.term_mk ρ u]
    exact ⟨fun ⟨a, b, ha, hb, hr⟩ => G.rel_cong r a _ b _ (G.mk_eq.mp ha) (G.mk_eq.mp hb) hr,
      fun hr => ⟨_, _, rfl, rfl, hr⟩⟩
  | .isA n t, ρ => by
    show (∃ y : {a // G.noun n a}, Quotient.mk G.setoid y.val =
      Term.eval G.quotC.name (Quotient.mk G.setoid ∘ ρ) t) ↔ G.noun n (Term.eval G.name ρ t)
    rw [G.term_mk ρ t]
    exact ⟨fun ⟨y, hy⟩ => G.noun_cong n _ _ (G.mk_eq.mp hy) y.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  | .eq t u, ρ => by
    show Term.eval G.quotC.name (Quotient.mk G.setoid ∘ ρ) t =
      Term.eval G.quotC.name (Quotient.mk G.setoid ∘ ρ) u ↔
      G.same (Term.eval G.name ρ t) (Term.eval G.name ρ u)
    rw [G.term_mk ρ t, G.term_mk ρ u]
    exact G.mk_eq
  | .top, _ => Iff.rfl
  | .not φ, ρ => not_congr (G.quot_eval φ ρ)
  | .and φ ψ, ρ => and_congr (G.quot_eval φ ρ) (G.quot_eval ψ ρ)
  | .or φ ψ, ρ => or_congr (G.quot_eval φ ρ) (G.quot_eval ψ ρ)
  | .imp φ ψ, ρ => imp_congr (G.quot_eval φ ρ) (G.quot_eval ψ ρ)
  | .quant d n C Q, ρ => by
    have hC : ∀ a : G.A, Form.eval (cI G.quotC G.relQ) C
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (pcI G) (tr C) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (cI G.quotC G.relQ) C)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval C (push a ρ))
    have hQ : ∀ a : G.A, Form.eval (cI G.quotC G.relQ) Q
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (pcI G) (tr Q) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (cI G.quotC G.relQ) Q)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval Q (push a ρ))
    refine detBy_sim d ?_ ?_ ?_ ?_
    · intro y
      exact ⟨y, hC y.val, hQ y.val⟩
    · intro a
      exact ⟨a, hC a.val, hQ a.val⟩
    · exact G.count_quot n fun a => and_congr (hC a) (hQ a)
    · exact G.count_quot n hC
  | .more n C Q S, ρ => by
    have hC : ∀ a : G.A, Form.eval (cI G.quotC G.relQ) C
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (pcI G) (tr C) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (cI G.quotC G.relQ) C)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval C (push a ρ))
    have hQ : ∀ a : G.A, Form.eval (cI G.quotC G.relQ) Q
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (pcI G) (tr Q) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (cI G.quotC G.relQ) Q)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval Q (push a ρ))
    have hS : ∀ a : G.A, Form.eval (cI G.quotC G.relQ) S
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (pcI G) (tr S) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (cI G.quotC G.relQ) S)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval S (push a ρ))
    exact gt_congr (G.count_quot n fun a => and_congr (hC a) (hQ a))
      (G.count_quot n fun a => and_congr (hC a) (hS a))

/-! ## From types to predicates: one object per element of each type -/

/-- The individual an object of the predicate model stands for. -/
def proj (M : CModel Noun Verb Name) : M.A ⊕ (Σ m, M.T m) → M.A
  | .inl x => x
  | .inr ⟨m, y⟩ => M.emb m y

open Classical in
/-- An element of `n`'s type that an object stands for: the element
itself for an object made from `n`'s type, some element with the same
individual otherwise. -/
noncomputable def pickT (M : CModel Noun Verb Name) (n : Noun) (a : M.A ⊕ (Σ m, M.T m))
    (h : ∃ y, M.emb n y = proj M a) : M.T n :=
  if h' : ∃ y, a = .inr ⟨n, y⟩ then Classical.choose h' else Classical.choose h

theorem pickT_spec (M : CModel Noun Verb Name) (n : Noun) (a : M.A ⊕ (Σ m, M.T m))
    (h : ∃ y, M.emb n y = proj M a) : M.emb n (pickT M n a h) = proj M a := by
  unfold pickT
  split
  · next h' => exact congrArg (proj M) (Classical.choose_spec h').symm
  · exact Classical.choose_spec h

theorem pickT_inr (M : CModel Noun Verb Name) (n : Noun) (y : M.T n)
    (h : ∃ y', M.emb n y' = proj M (.inr ⟨n, y⟩)) : pickT M n (.inr ⟨n, y⟩) h = y := by
  have h' : ∃ y', (Sum.inr ⟨n, y⟩ : M.A ⊕ (Σ m, M.T m)) = .inr ⟨n, y'⟩ := ⟨y, rfl⟩
  unfold pickT
  rw [dite_cond_eq_true (eq_true h')]
  have e := (Sigma.mk.inj_iff.mp (Sum.inr.inj (Classical.choose_spec h'))).2
  exact (eq_of_heq e).symm

open Classical in
/-- An object's value under `n`'s criterion: that of the element of
`n`'s type it stands for. -/
noncomputable def critPC (M : CModel Noun Verb Name) (n : Noun) (a : M.A ⊕ (Σ m, M.T m)) :
    Option (M.K n) :=
  if h : ∃ y, M.emb n y = proj M a then some (M.crit n (pickT M n a h)) else none

theorem critPC_of (M : CModel Noun Verb Name) (n : Noun) (a : M.A ⊕ (Σ m, M.T m))
    (h : ∃ y, M.emb n y = proj M a) : critPC M n a = some (M.crit n (pickT M n a h)) := by
  unfold critPC
  rw [dite_cond_eq_true (eq_true h)]

theorem critPC_inr (M : CModel Noun Verb Name) (n : Noun) (y : M.T n) :
    critPC M n (.inr ⟨n, y⟩) = some (M.crit n y) := by
  rw [critPC_of M n (.inr ⟨n, y⟩) ⟨y, rfl⟩, pickT_inr]

section
variable [Fintype Noun]

open Classical in
/-- The predicate model of a typed model: its domain is the individuals
plus one object for each element of each noun's type; an object is an
`n` when its individual is, and counts by `n`'s criterion as the
element it stands for. -/
noncomputable def toPC (M : CModel Noun Verb Name) (R : Rel → M.A → M.A → Prop) :
    PCModel Noun Verb Rel Name where
  A := M.A ⊕ (Σ m, M.T m)
  fin := inferInstance
  noun n a := IsA (M.emb n) (proj M a)
  verb v a := M.verb v (proj M a)
  rel r a b := R r (proj M a) (proj M b)
  name c := .inl (M.name c)
  same a b := proj M a = proj M b
  same_equiv := ⟨fun _ => rfl, fun h => Eq.symm h, fun h1 h2 => Eq.trans h1 h2⟩
  K n := Option (M.K n)
  crit n a := critPC M n a
  noun_cong n a b h hn := by
    obtain ⟨y, hy⟩ := hn
    exact ⟨y, hy.trans h⟩
  verb_cong v a b h hv := by
    show M.verb v (proj M b)
    rw [← show proj M a = proj M b from h]
    exact hv
  rel_cong r a a' b b' h1 h2 hr := by
    show R r (proj M a') (proj M b')
    rw [← show proj M a = proj M a' from h1, ← show proj M b = proj M b' from h2]
    exact hr

theorem term_proj (M : CModel Noun Verb Name) (R : Rel → M.A → M.A → Prop)
    (ρ : Nat → (toPC M R).A) :
    ∀ t : Term Name, proj M (Term.eval (toPC M R).name ρ t) = Term.eval M.name (proj M ∘ ρ) t
  | .var _ => rfl
  | .name _ => rfl

theorem count_toPC (M : CModel Noun Verb Name) (R : Rel → M.A → M.A → Prop) (n : Noun)
    {P' : (toPC M R).A → Prop} {P : M.A → Prop} (h : ∀ a, P' a ↔ P (proj M a)) :
    (toPC M R).countP n P' = M.countC n P := by
  unfold PCModel.countP CModel.countC
  refine countBy_sim (j := some) (Option.some_injective _) ?_ ?_
  · intro y hy
    exact ⟨⟨.inr ⟨n, y⟩, ⟨y, rfl⟩⟩, (h _).mpr hy, critPC_inr M n y⟩
  · intro a ha
    refine ⟨pickT M n a.val a.2, ?_, critPC_of M n a.val a.2⟩
    have := (h a.val).mp ha
    rw [← pickT_spec M n a.val a.2] at this
    exact this

/-- A typed model and its predicate model make the same formulas true,
identity read as `same`. -/
theorem toPC_eval (M : CModel Noun Verb Name) (R : Rel → M.A → M.A → Prop) :
    ∀ (φ : Form Noun Verb Rel Name) (ρ : Nat → (toPC M R).A),
      Form.eval (pcI (toPC M R)) (tr φ) ρ ↔ Form.eval (cI M R) φ (proj M ∘ ρ)
  | .verb v t, ρ => by
    show M.verb v (proj M (Term.eval (toPC M R).name ρ t)) ↔
      M.verb v (Term.eval M.name (proj M ∘ ρ) t)
    rw [term_proj]
  | .rel r t u, ρ => by
    show R r (proj M (Term.eval (toPC M R).name ρ t)) (proj M (Term.eval (toPC M R).name ρ u)) ↔
      R r (Term.eval M.name (proj M ∘ ρ) t) (Term.eval M.name (proj M ∘ ρ) u)
    rw [term_proj, term_proj]
  | .isA n t, ρ => by
    show IsA (M.emb n) (proj M (Term.eval (toPC M R).name ρ t)) ↔
      IsA (M.emb n) (Term.eval M.name (proj M ∘ ρ) t)
    rw [term_proj]
  | .eq t u, ρ => by
    show proj M (Term.eval (toPC M R).name ρ t) = proj M (Term.eval (toPC M R).name ρ u) ↔
      Term.eval M.name (proj M ∘ ρ) t = Term.eval M.name (proj M ∘ ρ) u
    rw [term_proj, term_proj]
  | .top, _ => Iff.rfl
  | .not φ, ρ => not_congr (toPC_eval M R φ ρ)
  | .and φ ψ, ρ => and_congr (toPC_eval M R φ ρ) (toPC_eval M R ψ ρ)
  | .or φ ψ, ρ => or_congr (toPC_eval M R φ ρ) (toPC_eval M R ψ ρ)
  | .imp φ ψ, ρ => imp_congr (toPC_eval M R φ ρ) (toPC_eval M R ψ ρ)
  | .quant d n C Q, ρ => by
    have hC : ∀ a, Form.eval (pcI (toPC M R)) (tr C) (push a ρ) ↔
        Form.eval (cI M R) C (push (proj M a) (proj M ∘ ρ)) := fun a =>
      (toPC_eval M R C (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (cI M R) C) (comp_push (proj M) a ρ)))
    have hQ : ∀ a, Form.eval (pcI (toPC M R)) (tr Q) (push a ρ) ↔
        Form.eval (cI M R) Q (push (proj M a) (proj M ∘ ρ)) := fun a =>
      (toPC_eval M R Q (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (cI M R) Q) (comp_push (proj M) a ρ)))
    refine detBy_sim d ?_ ?_ ?_ ?_
    · intro y
      exact ⟨⟨.inr ⟨n, y⟩, ⟨y, rfl⟩⟩, hC _, hQ _⟩
    · intro a
      refine ⟨pickT M n a.val a.2, ?_, ?_⟩
      · exact (hC a.val).trans (iff_of_eq (congrArg
          (fun x => Form.eval (cI M R) C (push x (proj M ∘ ρ))) (pickT_spec M n a.val a.2).symm))
      · exact (hQ a.val).trans (iff_of_eq (congrArg
          (fun x => Form.eval (cI M R) Q (push x (proj M ∘ ρ))) (pickT_spec M n a.val a.2).symm))
    · exact count_toPC M R n fun a => and_congr (hC a) (hQ a)
    · exact count_toPC M R n hC
  | .more n C Q S, ρ => by
    have hC : ∀ a, Form.eval (pcI (toPC M R)) (tr C) (push a ρ) ↔
        Form.eval (cI M R) C (push (proj M a) (proj M ∘ ρ)) := fun a =>
      (toPC_eval M R C (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (cI M R) C) (comp_push (proj M) a ρ)))
    have hQ : ∀ a, Form.eval (pcI (toPC M R)) (tr Q) (push a ρ) ↔
        Form.eval (cI M R) Q (push (proj M a) (proj M ∘ ρ)) := fun a =>
      (toPC_eval M R Q (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (cI M R) Q) (comp_push (proj M) a ρ)))
    have hS : ∀ a, Form.eval (pcI (toPC M R)) (tr S) (push a ρ) ↔
        Form.eval (cI M R) S (push (proj M a) (proj M ∘ ρ)) := fun a =>
      (toPC_eval M R S (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (cI M R) S) (comp_push (proj M) a ρ)))
    exact gt_congr (count_toPC M R n fun a => and_congr (hC a) (hQ a))
      (count_toPC M R n fun a => and_congr (hC a) (hS a))

/-- **The translation theorem.** An entailment is valid with nouns as
types counting by identity criteria exactly when its word-by-word
translation is valid with nouns as predicates over a domain with a
relation of being one individual and criteria of individuation. -/
theorem validC_iff (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) :
    ValidC Γ φ ↔ ValidPC Γ φ := by
  constructor
  · intro h G ρ hΓ
    have key := G.quot_eval
    exact (key φ ρ).mp (h G.quotC G.relQ (Quotient.mk G.setoid ∘ ρ)
      fun ψ hψ => (key ψ ρ).mpr (hΓ ψ hψ))
  · intro h M R ρ hΓ
    have key := toPC_eval M R
    exact (key φ (Sum.inl ∘ ρ)).mp (h (toPC M R) (Sum.inl ∘ ρ)
      fun ψ hψ => (key ψ (Sum.inl ∘ ρ)).mpr (hΓ ψ hψ))

end

end FraCaS.Encodings.Translation
