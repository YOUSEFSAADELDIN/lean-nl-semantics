import EndToEnd.Encodings.Translation
import EndToEnd.Encodings.Criteria

/-!
# The translation theorem with several criteria per noun

`Translation.lean` translates nouns as types with one identity criterion
per noun into nouns as predicates with criteria. Copredication needs
more: "John picked up and mastered three books" counts books distinct
physically *and* informationally (Gotham 2017; Chatzikyriakidis & Luo
2018, (47)), and `DotSetoid.lean` shows no single equivalence relation,
and so no single criterion, gives that count. This file lets each noun
have a family of criteria.

**Counting by several criteria (`countF`).** The `P`s, counted by a
family of criteria, are as many as the largest set of `P`s pairwise
distinct under every criterion of the family. With two criteria this is
the size of a largest matching between the two criteria's values (the
volumes and the texts), each book an edge.

- With two criteria, "at least `n`" is double distinctness
  (`le_countF_bool_iff`): Gotham's non-compressibility by PHYS and by
  INFO ((11), (14)), and Chatzikyriakidis & Luo's `Three` over their
  dot-setoid (`Criteria.atLeastDot_iff`). "At most `n`" is its negation,
  "no `n + 1` books distinct both ways".
- "Most", "both", "neither" and "exactly" count by the same function.
  The literature settles only the numerals; this is the natural
  extension, not a reading taken from it.

**`validM_iff`.** With each noun counting by a family of criteria
(`MCModel`, `cM`), an entailment is valid with nouns as types exactly
when its word-by-word translation (`Translation.tr`) is valid with nouns
as predicates over a domain with an identity relation and the same
families of criteria (`MPCModel`, `pcM`). The model constructions are
those of `Translation.lean`, with families of criteria (`toPCM`,
`MPCModel.quotM`).

Each noun must have at least one criterion (`nonempty`). With none, a
count would count a type's elements, which `toPCM`'s domain does not
preserve. Every noun in Chatzikyriakidis & Luo (2018) has one.
-/

namespace FraCaS.Encodings.TranslationMulti
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed
open FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence FraCaS.Encodings.Relational
open FraCaS.Encodings.Criteria (AtLeastBoth)
open FraCaS.Encodings.Translation (tr detBy_sim gt_congr comp_push)

variable {Noun Verb Rel Name : Type}

/-! ## Counting by a family of criteria -/

open Classical in
/-- The size of a largest set of `P`s pairwise distinct under every
criterion `c i`. -/
noncomputable def countF {N ι : Type} {K : ι → Type} [Fintype N] (c : ∀ i, N → K i)
    (P : N → Prop) : Nat :=
  ((Finset.univ.filter P).powerset.filter (fun S : Finset N => ∀ i, Set.InjOn (c i) ↑S)).sup
    Finset.card

theorem le_countF_iff {N ι : Type} {K : ι → Type} [Fintype N] (c : ∀ i, N → K i)
    (P : N → Prop) (n : Nat) :
    n ≤ countF c P ↔ ∃ S : Finset N, n ≤ S.card ∧ (∀ x ∈ S, P x) ∧ ∀ i, Set.InjOn (c i) ↑S := by
  classical
  unfold countF
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨∅, Nat.zero_le _, by simp, fun _ => by simp⟩
    · obtain ⟨S, hS, hle⟩ := (Finset.le_sup_iff hn).mp h
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      exact ⟨S, hle, fun x hx => (Finset.mem_filter.mp (hS.1 hx)).2, hS.2⟩
  · rintro ⟨S, hn, hP, hc⟩
    refine le_trans hn (Finset.le_sup (f := Finset.card) ?_)
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP x hx⟩, hc⟩

/-- With two criteria, "at least `n`" is double distinctness. -/
theorem le_countF_bool_iff {N : Type} {K : Bool → Type} [Fintype N] (c : ∀ i, N → K i)
    (P : N → Prop) (n : Nat) : n ≤ countF c P ↔ AtLeastBoth n (c true) (c false) P := by
  rw [le_countF_iff]
  constructor
  · rintro ⟨S, h1, h2, h3⟩
    exact ⟨S, h1, h2, h3 true, h3 false⟩
  · rintro ⟨S, h1, h2, h3, h4⟩
    exact ⟨S, h1, h2, fun i => by cases i <;> assumption⟩

/-- A map that carries the `P'`s to `P`s and reflects every criterion
does not lose count. -/
theorem countF_le_of_map {N N' ι : Type} {K K' : ι → Type} {_ : Fintype N} {_ : Fintype N'}
    {c : ∀ i, N → K i} {c' : ∀ i, N' → K' i} {P : N → Prop} {P' : N' → Prop} (g : N' → N)
    (hι : Nonempty ι) (hP : ∀ a, P' a → P (g a))
    (hc : ∀ i a b, P' a → P' b → c i (g a) = c i (g b) → c' i a = c' i b) :
    countF c' P' ≤ countF c P := by
  classical
  obtain ⟨S', hn, hP', hc'⟩ := (le_countF_iff c' P' _).mp le_rfl
  obtain ⟨i₀⟩ := hι
  have hg : Set.InjOn g ↑S' := by
    intro a ha b hb hab
    exact hc' i₀ ha hb (hc i₀ a b (hP' a ha) (hP' b hb) (congrArg (c i₀) hab))
  have key : S'.card ≤ countF c P := by
    rw [← Finset.card_image_of_injOn hg]
    refine (le_countF_iff c P _).mpr ⟨S'.image g, le_rfl, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact hP a (hP' a ha)
    · intro i x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact congrArg g (hc' i ha hb (hc i a b (hP' a ha) (hP' b hb) hxy))
  exact le_trans hn key

/-! ## Nouns as types with families of criteria -/

/-- A typed model in which each noun counts by a nonempty family of
criteria. -/
structure MCModel (Noun Verb Name : Type) extends TModel Noun Verb Name where
  ι : Noun → Type
  nonempty : ∀ n, Nonempty (ι n)
  K : ∀ n, ι n → Type
  crit : ∀ n (i : ι n), T n → K n i

/-- How many `n`s are `P`, counted by `n`'s criteria. -/
noncomputable def MCModel.countM (M : MCModel Noun Verb Name) (n : Noun) (P : M.A → Prop) :
    Nat :=
  countF (fun i => M.crit n i) (fun y => P (M.emb n y))

noncomputable def cM (M : MCModel Noun Verb Name) (R : Rel → M.A → M.A → Prop) :
    Interp Noun Verb Rel Name M.A where
  q d n C Q := detBy (M.countM n) (M.emb n) d C Q
  more n C Q S := M.countM n (fun x => C x ∧ Q x) > M.countM n (fun x => C x ∧ S x)
  isA := M.toTModel.isA
  verb := M.verb
  rel := R
  name := M.name

/-! ## Nouns as predicates with families of criteria -/

structure MPCModel (Noun Verb Rel Name : Type) where
  A : Type
  fin : Fintype A
  noun : Noun → A → Prop
  verb : Verb → A → Prop
  rel : Rel → A → A → Prop
  name : Name → A
  same : A → A → Prop
  same_equiv : Equivalence same
  ι : Noun → Type
  nonempty : ∀ n, Nonempty (ι n)
  K : ∀ n, ι n → Type
  crit : ∀ n (i : ι n), A → K n i
  noun_cong : ∀ n a b, same a b → noun n a → noun n b
  verb_cong : ∀ v a b, same a b → verb v a → verb v b
  rel_cong : ∀ r a a' b b', same a a' → same b b' → rel r a b → rel r a' b'

instance (G : MPCModel Noun Verb Rel Name) : Fintype G.A := G.fin

open Classical in
noncomputable def MPCModel.countP (G : MPCModel Noun Verb Rel Name) (n : Noun)
    (P : G.A → Prop) : Nat :=
  countF (fun i (y : {a // G.noun n a}) => G.crit n i y.val) (fun y => P y.val)

noncomputable def pcM (G : MPCModel Noun Verb Rel Name) :
    Interp Noun Verb (Option Rel) Name G.A where
  q d n C Q := detBy (G.countP n) (fun y : {a // G.noun n a} => y.val) d C Q
  more n C Q S := G.countP n (fun x => C x ∧ Q x) > G.countP n (fun x => C x ∧ S x)
  isA := G.noun
  verb := G.verb
  rel r := r.elim G.same G.rel
  name := G.name

def ValidM (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) : Prop :=
  ∀ (M : MCModel Noun Verb Name) (R : Rel → M.A → M.A → Prop) (ρ : Nat → M.A),
    (∀ ψ ∈ Γ, Form.eval (cM M R) ψ ρ) → Form.eval (cM M R) φ ρ

def ValidPM (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) : Prop :=
  ∀ (G : MPCModel Noun Verb Rel Name) (ρ : Nat → G.A),
    (∀ ψ ∈ Γ, Form.eval (pcM G) (tr ψ) ρ) → Form.eval (pcM G) (tr φ) ρ

/-! ## From predicates to types -/

def MPCModel.setoid (G : MPCModel Noun Verb Rel Name) : Setoid G.A := ⟨G.same, G.same_equiv⟩

open Classical in
noncomputable def MPCModel.quotM (G : MPCModel Noun Verb Rel Name) : MCModel Noun Verb Name where
  A := Quotient G.setoid
  fin := inferInstance
  T n := {a : G.A // G.noun n a}
  finT _ := inferInstance
  emb _ y := Quotient.mk G.setoid y.val
  verb v x := ∃ a, Quotient.mk G.setoid a = x ∧ G.verb v a
  name c := Quotient.mk G.setoid (G.name c)
  ι := G.ι
  nonempty := G.nonempty
  K := G.K
  crit n i y := G.crit n i y.val

def MPCModel.relQ (G : MPCModel Noun Verb Rel Name) :
    Rel → G.quotM.A → G.quotM.A → Prop :=
  fun r x y => ∃ a b, Quotient.mk G.setoid a = x ∧ Quotient.mk G.setoid b = y ∧ G.rel r a b

theorem MPCModel.mk_eq (G : MPCModel Noun Verb Rel Name) {a b : G.A} :
    Quotient.mk G.setoid a = Quotient.mk G.setoid b ↔ G.same a b :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

theorem MPCModel.term_mk (G : MPCModel Noun Verb Rel Name) (ρ : Nat → G.A) :
    ∀ t : Term Name, Term.eval G.quotM.name (Quotient.mk G.setoid ∘ ρ) t =
      Quotient.mk G.setoid (Term.eval G.name ρ t)
  | .var _ => rfl
  | .name _ => rfl

theorem MPCModel.count_quot (G : MPCModel Noun Verb Rel Name) (n : Noun)
    {Pm : G.quotM.A → Prop} {P : G.A → Prop} (h : ∀ a, Pm (Quotient.mk G.setoid a) ↔ P a) :
    G.quotM.countM n Pm = G.countP n P := by
  unfold MCModel.countM MPCModel.countP
  apply le_antisymm
  · exact countF_le_of_map (fun y => y) (G.nonempty n) (fun y hy => (h y.val).mp hy)
      (fun _ _ _ _ _ hab => hab)
  · exact countF_le_of_map (fun y => y) (G.nonempty n) (fun y hy => (h y.val).mpr hy)
      (fun _ _ _ _ _ hab => hab)

theorem MPCModel.quot_eval (G : MPCModel Noun Verb Rel Name) :
    ∀ (φ : Form Noun Verb Rel Name) (ρ : Nat → G.A),
      Form.eval (cM G.quotM G.relQ) φ (Quotient.mk G.setoid ∘ ρ) ↔ Form.eval (pcM G) (tr φ) ρ
  | .verb v t, ρ => by
    show (∃ a, Quotient.mk G.setoid a = Term.eval G.quotM.name (Quotient.mk G.setoid ∘ ρ) t ∧
      G.verb v a) ↔ G.verb v (Term.eval G.name ρ t)
    rw [G.term_mk ρ t]
    exact ⟨fun ⟨a, ha, hv⟩ => G.verb_cong v a _ (G.mk_eq.mp ha) hv, fun hv => ⟨_, rfl, hv⟩⟩
  | .rel r t u, ρ => by
    show (∃ a b, Quotient.mk G.setoid a = Term.eval G.quotM.name (Quotient.mk G.setoid ∘ ρ) t ∧
      Quotient.mk G.setoid b = Term.eval G.quotM.name (Quotient.mk G.setoid ∘ ρ) u ∧
      G.rel r a b) ↔ G.rel r (Term.eval G.name ρ t) (Term.eval G.name ρ u)
    rw [G.term_mk ρ t, G.term_mk ρ u]
    exact ⟨fun ⟨a, b, ha, hb, hr⟩ => G.rel_cong r a _ b _ (G.mk_eq.mp ha) (G.mk_eq.mp hb) hr,
      fun hr => ⟨_, _, rfl, rfl, hr⟩⟩
  | .isA n t, ρ => by
    show (∃ y : {a // G.noun n a}, Quotient.mk G.setoid y.val =
      Term.eval G.quotM.name (Quotient.mk G.setoid ∘ ρ) t) ↔ G.noun n (Term.eval G.name ρ t)
    rw [G.term_mk ρ t]
    exact ⟨fun ⟨y, hy⟩ => G.noun_cong n _ _ (G.mk_eq.mp hy) y.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  | .eq t u, ρ => by
    show Term.eval G.quotM.name (Quotient.mk G.setoid ∘ ρ) t =
      Term.eval G.quotM.name (Quotient.mk G.setoid ∘ ρ) u ↔
      G.same (Term.eval G.name ρ t) (Term.eval G.name ρ u)
    rw [G.term_mk ρ t, G.term_mk ρ u]
    exact G.mk_eq
  | .top, _ => Iff.rfl
  | .not φ, ρ => not_congr (G.quot_eval φ ρ)
  | .and φ ψ, ρ => and_congr (G.quot_eval φ ρ) (G.quot_eval ψ ρ)
  | .or φ ψ, ρ => or_congr (G.quot_eval φ ρ) (G.quot_eval ψ ρ)
  | .imp φ ψ, ρ => imp_congr (G.quot_eval φ ρ) (G.quot_eval ψ ρ)
  | .quant d n C Q, ρ => by
    have hC : ∀ a : G.A, Form.eval (cM G.quotM G.relQ) C
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (pcM G) (tr C) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (cM G.quotM G.relQ) C)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval C (push a ρ))
    have hQ : ∀ a : G.A, Form.eval (cM G.quotM G.relQ) Q
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (pcM G) (tr Q) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (cM G.quotM G.relQ) Q)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval Q (push a ρ))
    refine detBy_sim d ?_ ?_ ?_ ?_
    · intro y
      exact ⟨y, hC y.val, hQ y.val⟩
    · intro a
      exact ⟨a, hC a.val, hQ a.val⟩
    · exact G.count_quot n fun a => and_congr (hC a) (hQ a)
    · exact G.count_quot n hC
  | .more n C Q S, ρ => by
    have hC : ∀ a : G.A, Form.eval (cM G.quotM G.relQ) C
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (pcM G) (tr C) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (cM G.quotM G.relQ) C)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval C (push a ρ))
    have hQ : ∀ a : G.A, Form.eval (cM G.quotM G.relQ) Q
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (pcM G) (tr Q) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (cM G.quotM G.relQ) Q)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval Q (push a ρ))
    have hS : ∀ a : G.A, Form.eval (cM G.quotM G.relQ) S
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (pcM G) (tr S) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (cM G.quotM G.relQ) S)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval S (push a ρ))
    exact gt_congr (G.count_quot n fun a => and_congr (hC a) (hQ a))
      (G.count_quot n fun a => and_congr (hC a) (hS a))

/-! ## From types to predicates -/

/-- The individual an object of the predicate model stands for. -/
def MCModel.proj (M : MCModel Noun Verb Name) : M.A ⊕ (Σ m, M.T m) → M.A
  | .inl x => x
  | .inr ⟨m, y⟩ => M.emb m y

open Classical in
noncomputable def MCModel.pick (M : MCModel Noun Verb Name) (n : Noun)
    (a : M.A ⊕ (Σ m, M.T m)) (h : ∃ y, M.emb n y = M.proj a) : M.T n :=
  if h' : ∃ y, a = .inr ⟨n, y⟩ then Classical.choose h' else Classical.choose h

theorem MCModel.pick_spec (M : MCModel Noun Verb Name) (n : Noun) (a : M.A ⊕ (Σ m, M.T m))
    (h : ∃ y, M.emb n y = M.proj a) : M.emb n (M.pick n a h) = M.proj a := by
  unfold MCModel.pick
  split
  · next h' => exact congrArg M.proj (Classical.choose_spec h').symm
  · exact Classical.choose_spec h

theorem MCModel.pick_inr (M : MCModel Noun Verb Name) (n : Noun) (y : M.T n)
    (h : ∃ y', M.emb n y' = M.proj (.inr ⟨n, y⟩)) : M.pick n (.inr ⟨n, y⟩) h = y := by
  have h' : ∃ y', (Sum.inr ⟨n, y⟩ : M.A ⊕ (Σ m, M.T m)) = .inr ⟨n, y'⟩ := ⟨y, rfl⟩
  unfold MCModel.pick
  split
  · next h'' =>
    exact (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj (Classical.choose_spec h''))).2).symm
  · next hn => exact absurd h' hn

open Classical in
/-- An object's value under one of `n`'s criteria: that of the element
of `n`'s type it stands for. -/
noncomputable def critM (M : MCModel Noun Verb Name) (n : Noun) (i : M.ι n)
    (a : M.A ⊕ (Σ m, M.T m)) : Option (M.K n i) :=
  if h : ∃ y, M.emb n y = M.proj a then some (M.crit n i (M.pick n a h)) else none

theorem critM_of (M : MCModel Noun Verb Name) (n : Noun) (i : M.ι n) (a : M.A ⊕ (Σ m, M.T m))
    (h : ∃ y, M.emb n y = M.proj a) : critM M n i a = some (M.crit n i (M.pick n a h)) := by
  unfold critM
  split
  · rfl
  · next hn => exact absurd h hn

theorem critM_inr (M : MCModel Noun Verb Name) (n : Noun) (i : M.ι n) (y : M.T n) :
    critM M n i (.inr ⟨n, y⟩) = some (M.crit n i y) := by
  rw [critM_of M n i (.inr ⟨n, y⟩) ⟨y, rfl⟩, M.pick_inr]

section
variable [Fintype Noun]

open Classical in
/-- The predicate model of a typed model: individuals plus one object
per element of each noun's type, each counting under `n`'s criteria as
the element it stands for. -/
noncomputable def toPCM (M : MCModel Noun Verb Name) (R : Rel → M.A → M.A → Prop) :
    MPCModel Noun Verb Rel Name where
  A := M.A ⊕ (Σ m, M.T m)
  fin := inferInstance
  noun n a := IsA (M.emb n) (M.proj a)
  verb v a := M.verb v (M.proj a)
  rel r a b := R r (M.proj a) (M.proj b)
  name c := .inl (M.name c)
  same a b := M.proj a = M.proj b
  same_equiv := ⟨fun _ => rfl, fun h => Eq.symm h, fun h1 h2 => Eq.trans h1 h2⟩
  ι := M.ι
  nonempty := M.nonempty
  K n i := Option (M.K n i)
  crit n i a := critM M n i a
  noun_cong n a b h hn := by
    obtain ⟨y, hy⟩ := hn
    exact ⟨y, hy.trans h⟩
  verb_cong v a b h hv := by
    show M.verb v (M.proj b)
    rw [← show M.proj a = M.proj b from h]
    exact hv
  rel_cong r a a' b b' h1 h2 hr := by
    show R r (M.proj a') (M.proj b')
    rw [← show M.proj a = M.proj a' from h1, ← show M.proj b = M.proj b' from h2]
    exact hr

theorem term_projM (M : MCModel Noun Verb Name) (R : Rel → M.A → M.A → Prop)
    (ρ : Nat → (toPCM M R).A) :
    ∀ t : Term Name, M.proj (Term.eval (toPCM M R).name ρ t) = Term.eval M.name (M.proj ∘ ρ) t
  | .var _ => rfl
  | .name _ => rfl

theorem count_toPCM (M : MCModel Noun Verb Name) (R : Rel → M.A → M.A → Prop) (n : Noun)
    {P' : (toPCM M R).A → Prop} {P : M.A → Prop} (h : ∀ a, P' a ↔ P (M.proj a)) :
    (toPCM M R).countP n P' = M.countM n P := by
  unfold MPCModel.countP MCModel.countM
  apply le_antisymm
  · refine countF_le_of_map (fun a => M.pick n a.val a.2) (M.nonempty n) ?_ ?_
    · intro a ha
      exact Eq.mpr (congrArg P (M.pick_spec n a.val a.2)) ((h a.val).mp ha)
    · intro i a b _ _ hab
      exact (critM_of M n i a.val a.2).trans
        ((congrArg some hab).trans (critM_of M n i b.val b.2).symm)
  · refine countF_le_of_map (fun y => (⟨.inr ⟨n, y⟩, ⟨y, rfl⟩⟩ : {a // (toPCM M R).noun n a}))
      (M.nonempty n) ?_ ?_
    · intro y hy
      exact (h _).mpr hy
    · intro i y z _ _ hyz
      have e : some (M.crit n i y) = some (M.crit n i z) :=
        (critM_inr M n i y).symm.trans (hyz.trans (critM_inr M n i z))
      exact Option.some.inj e

theorem toPCM_eval (M : MCModel Noun Verb Name) (R : Rel → M.A → M.A → Prop) :
    ∀ (φ : Form Noun Verb Rel Name) (ρ : Nat → (toPCM M R).A),
      Form.eval (pcM (toPCM M R)) (tr φ) ρ ↔ Form.eval (cM M R) φ (M.proj ∘ ρ)
  | .verb v t, ρ => by
    show M.verb v (M.proj (Term.eval (toPCM M R).name ρ t)) ↔
      M.verb v (Term.eval M.name (M.proj ∘ ρ) t)
    rw [term_projM]
  | .rel r t u, ρ => by
    show R r (M.proj (Term.eval (toPCM M R).name ρ t)) (M.proj (Term.eval (toPCM M R).name ρ u)) ↔
      R r (Term.eval M.name (M.proj ∘ ρ) t) (Term.eval M.name (M.proj ∘ ρ) u)
    rw [term_projM, term_projM]
  | .isA n t, ρ => by
    show IsA (M.emb n) (M.proj (Term.eval (toPCM M R).name ρ t)) ↔
      IsA (M.emb n) (Term.eval M.name (M.proj ∘ ρ) t)
    rw [term_projM]
  | .eq t u, ρ => by
    show M.proj (Term.eval (toPCM M R).name ρ t) = M.proj (Term.eval (toPCM M R).name ρ u) ↔
      Term.eval M.name (M.proj ∘ ρ) t = Term.eval M.name (M.proj ∘ ρ) u
    rw [term_projM, term_projM]
  | .top, _ => Iff.rfl
  | .not φ, ρ => not_congr (toPCM_eval M R φ ρ)
  | .and φ ψ, ρ => and_congr (toPCM_eval M R φ ρ) (toPCM_eval M R ψ ρ)
  | .or φ ψ, ρ => or_congr (toPCM_eval M R φ ρ) (toPCM_eval M R ψ ρ)
  | .imp φ ψ, ρ => imp_congr (toPCM_eval M R φ ρ) (toPCM_eval M R ψ ρ)
  | .quant d n C Q, ρ => by
    have hC : ∀ a, Form.eval (pcM (toPCM M R)) (tr C) (push a ρ) ↔
        Form.eval (cM M R) C (push (M.proj a) (M.proj ∘ ρ)) := fun a =>
      (toPCM_eval M R C (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (cM M R) C) (comp_push M.proj a ρ)))
    have hQ : ∀ a, Form.eval (pcM (toPCM M R)) (tr Q) (push a ρ) ↔
        Form.eval (cM M R) Q (push (M.proj a) (M.proj ∘ ρ)) := fun a =>
      (toPCM_eval M R Q (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (cM M R) Q) (comp_push M.proj a ρ)))
    refine detBy_sim d ?_ ?_ ?_ ?_
    · intro y
      exact ⟨⟨.inr ⟨n, y⟩, ⟨y, rfl⟩⟩, hC _, hQ _⟩
    · intro a
      refine ⟨M.pick n a.val a.2, ?_, ?_⟩
      · exact (hC a.val).trans (iff_of_eq (congrArg
          (fun x => Form.eval (cM M R) C (push x (M.proj ∘ ρ))) (M.pick_spec n a.val a.2).symm))
      · exact (hQ a.val).trans (iff_of_eq (congrArg
          (fun x => Form.eval (cM M R) Q (push x (M.proj ∘ ρ))) (M.pick_spec n a.val a.2).symm))
    · exact count_toPCM M R n fun a => and_congr (hC a) (hQ a)
    · exact count_toPCM M R n hC
  | .more n C Q S, ρ => by
    have hC : ∀ a, Form.eval (pcM (toPCM M R)) (tr C) (push a ρ) ↔
        Form.eval (cM M R) C (push (M.proj a) (M.proj ∘ ρ)) := fun a =>
      (toPCM_eval M R C (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (cM M R) C) (comp_push M.proj a ρ)))
    have hQ : ∀ a, Form.eval (pcM (toPCM M R)) (tr Q) (push a ρ) ↔
        Form.eval (cM M R) Q (push (M.proj a) (M.proj ∘ ρ)) := fun a =>
      (toPCM_eval M R Q (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (cM M R) Q) (comp_push M.proj a ρ)))
    have hS : ∀ a, Form.eval (pcM (toPCM M R)) (tr S) (push a ρ) ↔
        Form.eval (cM M R) S (push (M.proj a) (M.proj ∘ ρ)) := fun a =>
      (toPCM_eval M R S (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (cM M R) S) (comp_push M.proj a ρ)))
    exact gt_congr (count_toPCM M R n fun a => and_congr (hC a) (hQ a))
      (count_toPCM M R n fun a => and_congr (hC a) (hS a))

/-- **The translation theorem with families of criteria.** An entailment
is valid with nouns as types counting by families of criteria, as
copredicated nouns count, exactly when its word-by-word translation is
valid with nouns as predicates over a domain with an identity relation
and the same families of criteria. -/
theorem validM_iff (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) :
    ValidM Γ φ ↔ ValidPM Γ φ := by
  constructor
  · intro h G ρ hΓ
    have key := G.quot_eval
    exact (key φ ρ).mp (h G.quotM G.relQ (Quotient.mk G.setoid ∘ ρ)
      fun ψ hψ => (key ψ ρ).mpr (hΓ ψ hψ))
  · intro h M R ρ hΓ
    have key := toPCM_eval M R
    exact (key φ (Sum.inl ∘ ρ)).mp (h (toPCM M R) (Sum.inl ∘ ρ)
      fun ψ hψ => (key ψ (Sum.inl ∘ ρ)).mpr (hΓ ψ hψ))

end

end FraCaS.Encodings.TranslationMulti
