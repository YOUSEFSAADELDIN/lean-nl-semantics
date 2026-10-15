import EndToEnd.Encodings.TranslationMulti

/-!
# The verb chooses the criterion

Chatzikyriakidis & Luo (2018) count a noun by the identity criterion of
the predicate applied to it: "the identity criterion of the object CN
... is determined by the domain of the predicate" ((43)-(45), p. 133).
"John picked up three books" counts physically, "John mastered three
books" informationally, "John picked up and mastered three books" both
ways ((36), (46)-(47)), and so does "John mastered three heavy books",
where the adjective has a say too ((48)-(54)). They add that how the
criteria are decided is "a little bit more complicated" when verbs and
adjectives both play a role (p. 136), and give no general rule.

`Translation.lean` and `TranslationMulti.lean` modelled this with noun
senses, a separate noun for "book counted physically" and for "book
counted informationally", as C&L's own (41)-(42) are two setoids. This
file keeps one lexical entry per noun and lets the sentence choose.

- **The lexicon (`AspLex`)** gives each verb's and relation's argument
  an aspect (`Phy`, `Info`, ...): the domain of the predicate.
- **Elaboration (`labelQ`)** labels each quantifier with the aspects at
  which its variable is used, in the restrictor or the scope. This
  reconstruction of the rule gives each of C&L's examples (37), (38),
  (36), (48) and (55).
- **Typed models (`VModel`)** give each noun one type, and one criterion
  for each aspect. A quantifier counts by the criteria of its label's
  aspects, or by the noun's default criterion when the variable is used
  at no aspect (`countV`).
- **Predicate models (`VPModel`)** give each noun one predicate, and
  criteria on the domain for each aspect, as Gotham's PHYS and INFO.

**`validV_iff`**: with the verb choosing the criterion, an entailment is
valid with nouns as types exactly when its translation (`Translation.tr`,
identity to "same individual") is valid with nouns as predicates. The
model constructions are those of `TranslationMulti.lean`, with one type
or predicate per noun rather than per sense.

**Gotham's (122) (`gotham122_V`, `gotham122_VP`).** "John picked up and
mastered three books ⇒ John picked up three books" is valid. With one
lexical entry the two quantifiers count the same books, by two criteria
and by one. With two noun senses as unrelated nouns, as in
`TranslationMulti.lean`, nothing links them.
-/

namespace FraCaS.Encodings.VerbCriteria
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed
open FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence FraCaS.Encodings.Relational
open FraCaS.Encodings.Translation (tr detBy_sim gt_congr comp_push)
open FraCaS.Encodings.TranslationMulti (countF le_countF_iff countF_le_of_map)

variable {Noun Verb Rel Name Asp : Type}

/-! ## Elaboration: which aspects a quantifier's variable is used at -/

/-- The aspect of each argument position: the domain of the predicate. -/
structure AspLex (Verb Rel Asp : Type) where
  verb : Verb → Asp
  arg1 : Rel → Asp
  arg2 : Rel → Asp

/-- The aspect `a`, if the term is the variable `k`. -/
def onVar (k : Nat) (a : Asp) : Term Name → List Asp
  | .var j => if j = k then [a] else []
  | .name _ => []

/-- The aspects at which variable `k` is used in a formula. -/
def uses (L : AspLex Verb Rel Asp) : Form Noun Verb Rel Name → Nat → List Asp
  | .verb v t, k => onVar k (L.verb v) t
  | .rel r t u, k => onVar k (L.arg1 r) t ++ onVar k (L.arg2 r) u
  | .isA _ _, _ => []
  | .eq _ _, _ => []
  | .top, _ => []
  | .not φ, k => uses L φ k
  | .and φ ψ, k => uses L φ k ++ uses L ψ k
  | .or φ ψ, k => uses L φ k ++ uses L ψ k
  | .imp φ ψ, k => uses L φ k ++ uses L ψ k
  | .quant _ _ C Q, k => uses L C (k + 1) ++ uses L Q (k + 1)
  | .more _ C Q S, k => uses L C (k + 1) ++ uses L Q (k + 1) ++ uses L S (k + 1)

/-- Label each quantifier with the aspects its variable is used at, in
its restrictor and its scope. -/
def labelQ (L : AspLex Verb Rel Asp) : Form Noun Verb Rel Name → Form (Noun × List Asp) Verb Rel Name
  | .verb v t => .verb v t
  | .rel r t u => .rel r t u
  | .isA n t => .isA (n, []) t
  | .eq t u => .eq t u
  | .top => .top
  | .not φ => .not (labelQ L φ)
  | .and φ ψ => .and (labelQ L φ) (labelQ L ψ)
  | .or φ ψ => .or (labelQ L φ) (labelQ L ψ)
  | .imp φ ψ => .imp (labelQ L φ) (labelQ L ψ)
  | .quant d n C Q => .quant d (n, uses L C 0 ++ uses L Q 0) (labelQ L C) (labelQ L Q)
  | .more n C Q S =>
    .more (n, uses L C 0 ++ uses L Q 0 ++ uses L S 0) (labelQ L C) (labelQ L Q) (labelQ L S)

/-- The aspects counted by: those used, or the default when none is. -/
def eff (d : Asp) : List Asp → List Asp
  | [] => [d]
  | k :: ks => k :: ks

theorem eff_nonempty (d : Asp) : ∀ ks : List Asp, Nonempty {k // k ∈ eff d ks}
  | [] => ⟨⟨d, by simp [eff]⟩⟩
  | k :: _ => ⟨⟨k, by simp [eff]⟩⟩

/-! ## Nouns as types, one entry per noun -/

/-- A typed model with one type per noun and one criterion per aspect. -/
structure VModel (Noun Verb Name Asp : Type) extends TModel Noun Verb Name where
  K : Noun → Asp → Type
  crit : ∀ n k, T n → K n k
  dflt : Noun → Asp

/-- How many `l.1`s are `P`, counted by the criteria of `l`'s aspects. -/
noncomputable def VModel.countV (M : VModel Noun Verb Name Asp) (l : Noun × List Asp)
    (P : M.A → Prop) : Nat :=
  countF (fun (i : {k // k ∈ eff (M.dflt l.1) l.2}) => M.crit l.1 i.val) (fun y => P (M.emb l.1 y))

noncomputable def vI (M : VModel Noun Verb Name Asp) (R : Rel → M.A → M.A → Prop) :
    Interp (Noun × List Asp) Verb Rel Name M.A where
  q d l C Q := detBy (M.countV l) (M.emb l.1) d C Q
  more l C Q S := M.countV l (fun x => C x ∧ Q x) > M.countV l (fun x => C x ∧ S x)
  isA l := M.toTModel.isA l.1
  verb := M.verb
  rel := R
  name := M.name

/-- More criteria, and a stronger condition, count fewer. -/
theorem VModel.countV_anti (M : VModel Noun Verb Name Asp) {n : Noun} {ks ks' : List Asp}
    {P P' : M.A → Prop} (hk : ∀ k ∈ eff (M.dflt n) ks, k ∈ eff (M.dflt n) ks')
    (hP : ∀ x, P' x → P x) : M.countV (n, ks') P' ≤ M.countV (n, ks) P := by
  unfold VModel.countV
  obtain ⟨S, hn, hS, hinj⟩ := (le_countF_iff _ _ _).mp (le_refl (countF
    (fun (i : {k // k ∈ eff (M.dflt n) ks'}) => M.crit n i.val) (fun y => P' (M.emb n y))))
  exact le_trans hn ((le_countF_iff _ _ _).mpr
    ⟨S, le_rfl, fun x hx => hP _ (hS x hx), fun i => hinj ⟨i.val, hk i.val i.2⟩⟩)

/-! ## Nouns as predicates, one predicate per noun -/

structure VPModel (Noun Verb Rel Name Asp : Type) where
  A : Type
  fin : Fintype A
  noun : Noun → A → Prop
  verb : Verb → A → Prop
  rel : Rel → A → A → Prop
  name : Name → A
  same : A → A → Prop
  same_equiv : Equivalence same
  K : Noun → Asp → Type
  crit : ∀ n k, A → K n k
  dflt : Noun → Asp
  noun_cong : ∀ n a b, same a b → noun n a → noun n b
  verb_cong : ∀ v a b, same a b → verb v a → verb v b
  rel_cong : ∀ r a a' b b', same a a' → same b b' → rel r a b → rel r a' b'

instance (G : VPModel Noun Verb Rel Name Asp) : Fintype G.A := G.fin

open Classical in
noncomputable def VPModel.countP (G : VPModel Noun Verb Rel Name Asp) (l : Noun × List Asp)
    (P : G.A → Prop) : Nat :=
  countF (fun (i : {k // k ∈ eff (G.dflt l.1) l.2}) (y : {a // G.noun l.1 a}) =>
    G.crit l.1 i.val y.val) (fun y => P y.val)

noncomputable def vpI (G : VPModel Noun Verb Rel Name Asp) :
    Interp (Noun × List Asp) Verb (Option Rel) Name G.A where
  q d l C Q := detBy (G.countP l) (fun y : {a // G.noun l.1 a} => y.val) d C Q
  more l C Q S := G.countP l (fun x => C x ∧ Q x) > G.countP l (fun x => C x ∧ S x)
  isA l := G.noun l.1
  verb := G.verb
  rel r := r.elim G.same G.rel
  name := G.name

def ValidV (L : AspLex Verb Rel Asp) (Γ : List (Form Noun Verb Rel Name))
    (φ : Form Noun Verb Rel Name) : Prop :=
  ∀ (M : VModel Noun Verb Name Asp) (R : Rel → M.A → M.A → Prop) (ρ : Nat → M.A),
    (∀ ψ ∈ Γ, Form.eval (vI M R) (labelQ L ψ) ρ) → Form.eval (vI M R) (labelQ L φ) ρ

def ValidVP (L : AspLex Verb Rel Asp) (Γ : List (Form Noun Verb Rel Name))
    (φ : Form Noun Verb Rel Name) : Prop :=
  ∀ (G : VPModel Noun Verb Rel Name Asp) (ρ : Nat → G.A),
    (∀ ψ ∈ Γ, Form.eval (vpI G) (tr (labelQ L ψ)) ρ) → Form.eval (vpI G) (tr (labelQ L φ)) ρ

/-! ## From predicates to types -/

def VPModel.setoid (G : VPModel Noun Verb Rel Name Asp) : Setoid G.A := ⟨G.same, G.same_equiv⟩

open Classical in
noncomputable def VPModel.quotV (G : VPModel Noun Verb Rel Name Asp) :
    VModel Noun Verb Name Asp where
  A := Quotient G.setoid
  fin := inferInstance
  T n := {a : G.A // G.noun n a}
  finT _ := inferInstance
  emb _ y := Quotient.mk G.setoid y.val
  verb v x := ∃ a, Quotient.mk G.setoid a = x ∧ G.verb v a
  name c := Quotient.mk G.setoid (G.name c)
  K := G.K
  crit n k y := G.crit n k y.val
  dflt := G.dflt

def VPModel.relQ (G : VPModel Noun Verb Rel Name Asp) :
    Rel → G.quotV.A → G.quotV.A → Prop :=
  fun r x y => ∃ a b, Quotient.mk G.setoid a = x ∧ Quotient.mk G.setoid b = y ∧ G.rel r a b

theorem VPModel.mk_eq (G : VPModel Noun Verb Rel Name Asp) {a b : G.A} :
    Quotient.mk G.setoid a = Quotient.mk G.setoid b ↔ G.same a b :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

theorem VPModel.term_mk (G : VPModel Noun Verb Rel Name Asp) (ρ : Nat → G.A) :
    ∀ t : Term Name, Term.eval G.quotV.name (Quotient.mk G.setoid ∘ ρ) t =
      Quotient.mk G.setoid (Term.eval G.name ρ t)
  | .var _ => rfl
  | .name _ => rfl

theorem VPModel.count_quot (G : VPModel Noun Verb Rel Name Asp) (l : Noun × List Asp)
    {Pm : G.quotV.A → Prop} {P : G.A → Prop} (h : ∀ a, Pm (Quotient.mk G.setoid a) ↔ P a) :
    G.quotV.countV l Pm = G.countP l P := by
  unfold VModel.countV VPModel.countP
  apply le_antisymm
  · exact countF_le_of_map (fun y => y) (eff_nonempty _ _) (fun y hy => (h y.val).mp hy)
      (fun _ _ _ _ _ hab => hab)
  · exact countF_le_of_map (fun y => y) (eff_nonempty _ _) (fun y hy => (h y.val).mpr hy)
      (fun _ _ _ _ _ hab => hab)

theorem VPModel.quot_eval (G : VPModel Noun Verb Rel Name Asp) :
    ∀ (φ : Form (Noun × List Asp) Verb Rel Name) (ρ : Nat → G.A),
      Form.eval (vI G.quotV G.relQ) φ (Quotient.mk G.setoid ∘ ρ) ↔ Form.eval (vpI G) (tr φ) ρ
  | .verb v t, ρ => by
    show (∃ a, Quotient.mk G.setoid a = Term.eval G.quotV.name (Quotient.mk G.setoid ∘ ρ) t ∧
      G.verb v a) ↔ G.verb v (Term.eval G.name ρ t)
    rw [G.term_mk ρ t]
    exact ⟨fun ⟨a, ha, hv⟩ => G.verb_cong v a _ (G.mk_eq.mp ha) hv, fun hv => ⟨_, rfl, hv⟩⟩
  | .rel r t u, ρ => by
    show (∃ a b, Quotient.mk G.setoid a = Term.eval G.quotV.name (Quotient.mk G.setoid ∘ ρ) t ∧
      Quotient.mk G.setoid b = Term.eval G.quotV.name (Quotient.mk G.setoid ∘ ρ) u ∧
      G.rel r a b) ↔ G.rel r (Term.eval G.name ρ t) (Term.eval G.name ρ u)
    rw [G.term_mk ρ t, G.term_mk ρ u]
    exact ⟨fun ⟨a, b, ha, hb, hr⟩ => G.rel_cong r a _ b _ (G.mk_eq.mp ha) (G.mk_eq.mp hb) hr,
      fun hr => ⟨_, _, rfl, rfl, hr⟩⟩
  | .isA l t, ρ => by
    show (∃ y : {a // G.noun l.1 a}, Quotient.mk G.setoid y.val =
      Term.eval G.quotV.name (Quotient.mk G.setoid ∘ ρ) t) ↔ G.noun l.1 (Term.eval G.name ρ t)
    rw [G.term_mk ρ t]
    exact ⟨fun ⟨y, hy⟩ => G.noun_cong l.1 _ _ (G.mk_eq.mp hy) y.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  | .eq t u, ρ => by
    show Term.eval G.quotV.name (Quotient.mk G.setoid ∘ ρ) t =
      Term.eval G.quotV.name (Quotient.mk G.setoid ∘ ρ) u ↔
      G.same (Term.eval G.name ρ t) (Term.eval G.name ρ u)
    rw [G.term_mk ρ t, G.term_mk ρ u]
    exact G.mk_eq
  | .top, _ => Iff.rfl
  | .not φ, ρ => not_congr (G.quot_eval φ ρ)
  | .and φ ψ, ρ => and_congr (G.quot_eval φ ρ) (G.quot_eval ψ ρ)
  | .or φ ψ, ρ => or_congr (G.quot_eval φ ρ) (G.quot_eval ψ ρ)
  | .imp φ ψ, ρ => imp_congr (G.quot_eval φ ρ) (G.quot_eval ψ ρ)
  | .quant d l C Q, ρ => by
    have hC : ∀ a : G.A, Form.eval (vI G.quotV G.relQ) C
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (vpI G) (tr C) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (vI G.quotV G.relQ) C)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval C (push a ρ))
    have hQ : ∀ a : G.A, Form.eval (vI G.quotV G.relQ) Q
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (vpI G) (tr Q) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (vI G.quotV G.relQ) Q)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval Q (push a ρ))
    refine detBy_sim d ?_ ?_ ?_ ?_
    · intro y
      exact ⟨y, hC y.val, hQ y.val⟩
    · intro a
      exact ⟨a, hC a.val, hQ a.val⟩
    · exact G.count_quot l fun a => and_congr (hC a) (hQ a)
    · exact G.count_quot l hC
  | .more l C Q S, ρ => by
    have hC : ∀ a : G.A, Form.eval (vI G.quotV G.relQ) C
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (vpI G) (tr C) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (vI G.quotV G.relQ) C)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval C (push a ρ))
    have hQ : ∀ a : G.A, Form.eval (vI G.quotV G.relQ) Q
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (vpI G) (tr Q) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (vI G.quotV G.relQ) Q)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval Q (push a ρ))
    have hS : ∀ a : G.A, Form.eval (vI G.quotV G.relQ) S
        (push (Quotient.mk G.setoid a) (Quotient.mk G.setoid ∘ ρ)) ↔
        Form.eval (vpI G) (tr S) (push a ρ) := fun a =>
      (iff_of_eq (congrArg (Form.eval (vI G.quotV G.relQ) S)
        (comp_push (Quotient.mk G.setoid) a ρ).symm)).trans (G.quot_eval S (push a ρ))
    exact gt_congr (G.count_quot l fun a => and_congr (hC a) (hQ a))
      (G.count_quot l fun a => and_congr (hC a) (hS a))

/-! ## From types to predicates -/

def VModel.proj (M : VModel Noun Verb Name Asp) : M.A ⊕ (Σ m, M.T m) → M.A
  | .inl x => x
  | .inr ⟨m, y⟩ => M.emb m y

open Classical in
noncomputable def VModel.pick (M : VModel Noun Verb Name Asp) (n : Noun)
    (a : M.A ⊕ (Σ m, M.T m)) (h : ∃ y, M.emb n y = M.proj a) : M.T n :=
  if h' : ∃ y, a = .inr ⟨n, y⟩ then Classical.choose h' else Classical.choose h

theorem VModel.pick_spec (M : VModel Noun Verb Name Asp) (n : Noun) (a : M.A ⊕ (Σ m, M.T m))
    (h : ∃ y, M.emb n y = M.proj a) : M.emb n (M.pick n a h) = M.proj a := by
  unfold VModel.pick
  split
  · next h' => exact congrArg M.proj (Classical.choose_spec h').symm
  · exact Classical.choose_spec h

theorem VModel.pick_inr (M : VModel Noun Verb Name Asp) (n : Noun) (y : M.T n)
    (h : ∃ y', M.emb n y' = M.proj (.inr ⟨n, y⟩)) : M.pick n (.inr ⟨n, y⟩) h = y := by
  have h' : ∃ y', (Sum.inr ⟨n, y⟩ : M.A ⊕ (Σ m, M.T m)) = .inr ⟨n, y'⟩ := ⟨y, rfl⟩
  unfold VModel.pick
  split
  · next h'' =>
    exact (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj (Classical.choose_spec h''))).2).symm
  · next hn => exact absurd h' hn

open Classical in
noncomputable def critV (M : VModel Noun Verb Name Asp) (n : Noun) (k : Asp)
    (a : M.A ⊕ (Σ m, M.T m)) : Option (M.K n k) :=
  if h : ∃ y, M.emb n y = M.proj a then some (M.crit n k (M.pick n a h)) else none

theorem critV_of (M : VModel Noun Verb Name Asp) (n : Noun) (k : Asp) (a : M.A ⊕ (Σ m, M.T m))
    (h : ∃ y, M.emb n y = M.proj a) : critV M n k a = some (M.crit n k (M.pick n a h)) := by
  unfold critV
  split
  · rfl
  · next hn => exact absurd h hn

theorem critV_inr (M : VModel Noun Verb Name Asp) (n : Noun) (k : Asp) (y : M.T n) :
    critV M n k (.inr ⟨n, y⟩) = some (M.crit n k y) := by
  rw [critV_of M n k (.inr ⟨n, y⟩) ⟨y, rfl⟩, M.pick_inr]

section
variable [Fintype Noun]

open Classical in
noncomputable def toVP (M : VModel Noun Verb Name Asp) (R : Rel → M.A → M.A → Prop) :
    VPModel Noun Verb Rel Name Asp where
  A := M.A ⊕ (Σ m, M.T m)
  fin := inferInstance
  noun n a := IsA (M.emb n) (M.proj a)
  verb v a := M.verb v (M.proj a)
  rel r a b := R r (M.proj a) (M.proj b)
  name c := .inl (M.name c)
  same a b := M.proj a = M.proj b
  same_equiv := ⟨fun _ => rfl, fun h => Eq.symm h, fun h1 h2 => Eq.trans h1 h2⟩
  K n k := Option (M.K n k)
  crit n k a := critV M n k a
  dflt := M.dflt
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

theorem term_projV (M : VModel Noun Verb Name Asp) (R : Rel → M.A → M.A → Prop)
    (ρ : Nat → (toVP M R).A) :
    ∀ t : Term Name, M.proj (Term.eval (toVP M R).name ρ t) = Term.eval M.name (M.proj ∘ ρ) t
  | .var _ => rfl
  | .name _ => rfl

theorem count_toVP (M : VModel Noun Verb Name Asp) (R : Rel → M.A → M.A → Prop)
    (l : Noun × List Asp) {P' : (toVP M R).A → Prop} {P : M.A → Prop}
    (h : ∀ a, P' a ↔ P (M.proj a)) : (toVP M R).countP l P' = M.countV l P := by
  unfold VPModel.countP VModel.countV
  apply le_antisymm
  · refine countF_le_of_map (fun a => M.pick l.1 a.val a.2) (eff_nonempty _ _) ?_ ?_
    · intro a ha
      exact Eq.mpr (congrArg P (M.pick_spec l.1 a.val a.2)) ((h a.val).mp ha)
    · intro i a b _ _ hab
      exact (critV_of M l.1 i.val a.val a.2).trans
        ((congrArg some hab).trans (critV_of M l.1 i.val b.val b.2).symm)
  · refine countF_le_of_map
      (fun y => (⟨.inr ⟨l.1, y⟩, ⟨y, rfl⟩⟩ : {a // (toVP M R).noun l.1 a}))
      (eff_nonempty _ _) ?_ ?_
    · intro y hy
      exact (h _).mpr hy
    · intro i y z _ _ hyz
      have e : some (M.crit l.1 i.val y) = some (M.crit l.1 i.val z) :=
        (critV_inr M l.1 i.val y).symm.trans (hyz.trans (critV_inr M l.1 i.val z))
      exact Option.some.inj e

theorem toVP_eval (M : VModel Noun Verb Name Asp) (R : Rel → M.A → M.A → Prop) :
    ∀ (φ : Form (Noun × List Asp) Verb Rel Name) (ρ : Nat → (toVP M R).A),
      Form.eval (vpI (toVP M R)) (tr φ) ρ ↔ Form.eval (vI M R) φ (M.proj ∘ ρ)
  | .verb v t, ρ => by
    show M.verb v (M.proj (Term.eval (toVP M R).name ρ t)) ↔
      M.verb v (Term.eval M.name (M.proj ∘ ρ) t)
    rw [term_projV]
  | .rel r t u, ρ => by
    show R r (M.proj (Term.eval (toVP M R).name ρ t)) (M.proj (Term.eval (toVP M R).name ρ u)) ↔
      R r (Term.eval M.name (M.proj ∘ ρ) t) (Term.eval M.name (M.proj ∘ ρ) u)
    rw [term_projV, term_projV]
  | .isA l t, ρ => by
    show IsA (M.emb l.1) (M.proj (Term.eval (toVP M R).name ρ t)) ↔
      IsA (M.emb l.1) (Term.eval M.name (M.proj ∘ ρ) t)
    rw [term_projV]
  | .eq t u, ρ => by
    show M.proj (Term.eval (toVP M R).name ρ t) = M.proj (Term.eval (toVP M R).name ρ u) ↔
      Term.eval M.name (M.proj ∘ ρ) t = Term.eval M.name (M.proj ∘ ρ) u
    rw [term_projV, term_projV]
  | .top, _ => Iff.rfl
  | .not φ, ρ => not_congr (toVP_eval M R φ ρ)
  | .and φ ψ, ρ => and_congr (toVP_eval M R φ ρ) (toVP_eval M R ψ ρ)
  | .or φ ψ, ρ => or_congr (toVP_eval M R φ ρ) (toVP_eval M R ψ ρ)
  | .imp φ ψ, ρ => imp_congr (toVP_eval M R φ ρ) (toVP_eval M R ψ ρ)
  | .quant d l C Q, ρ => by
    have hC : ∀ a, Form.eval (vpI (toVP M R)) (tr C) (push a ρ) ↔
        Form.eval (vI M R) C (push (M.proj a) (M.proj ∘ ρ)) := fun a =>
      (toVP_eval M R C (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (vI M R) C) (comp_push M.proj a ρ)))
    have hQ : ∀ a, Form.eval (vpI (toVP M R)) (tr Q) (push a ρ) ↔
        Form.eval (vI M R) Q (push (M.proj a) (M.proj ∘ ρ)) := fun a =>
      (toVP_eval M R Q (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (vI M R) Q) (comp_push M.proj a ρ)))
    refine detBy_sim d ?_ ?_ ?_ ?_
    · intro y
      exact ⟨⟨.inr ⟨l.1, y⟩, ⟨y, rfl⟩⟩, hC _, hQ _⟩
    · intro a
      refine ⟨M.pick l.1 a.val a.2, ?_, ?_⟩
      · exact (hC a.val).trans (iff_of_eq (congrArg
          (fun x => Form.eval (vI M R) C (push x (M.proj ∘ ρ))) (M.pick_spec l.1 a.val a.2).symm))
      · exact (hQ a.val).trans (iff_of_eq (congrArg
          (fun x => Form.eval (vI M R) Q (push x (M.proj ∘ ρ))) (M.pick_spec l.1 a.val a.2).symm))
    · exact count_toVP M R l fun a => and_congr (hC a) (hQ a)
    · exact count_toVP M R l hC
  | .more l C Q S, ρ => by
    have hC : ∀ a, Form.eval (vpI (toVP M R)) (tr C) (push a ρ) ↔
        Form.eval (vI M R) C (push (M.proj a) (M.proj ∘ ρ)) := fun a =>
      (toVP_eval M R C (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (vI M R) C) (comp_push M.proj a ρ)))
    have hQ : ∀ a, Form.eval (vpI (toVP M R)) (tr Q) (push a ρ) ↔
        Form.eval (vI M R) Q (push (M.proj a) (M.proj ∘ ρ)) := fun a =>
      (toVP_eval M R Q (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (vI M R) Q) (comp_push M.proj a ρ)))
    have hS : ∀ a, Form.eval (vpI (toVP M R)) (tr S) (push a ρ) ↔
        Form.eval (vI M R) S (push (M.proj a) (M.proj ∘ ρ)) := fun a =>
      (toVP_eval M R S (push a ρ)).trans
        (iff_of_eq (congrArg (Form.eval (vI M R) S) (comp_push M.proj a ρ)))
    exact gt_congr (count_toVP M R l fun a => and_congr (hC a) (hQ a))
      (count_toVP M R l fun a => and_congr (hC a) (hS a))

/-- **The translation theorem with the verb choosing the criterion.**
With one type or one predicate per noun, and each quantifier counting by
the criteria of the aspects its variable is used at, an entailment is
valid with nouns as types exactly when its word-by-word translation is
valid with nouns as predicates. -/
theorem validV_iff (L : AspLex Verb Rel Asp) (Γ : List (Form Noun Verb Rel Name))
    (φ : Form Noun Verb Rel Name) : ValidV L Γ φ ↔ ValidVP L Γ φ := by
  constructor
  · intro h G ρ hΓ
    have key := G.quot_eval
    exact (key (labelQ L φ) ρ).mp (h G.quotV G.relQ (Quotient.mk G.setoid ∘ ρ)
      fun ψ hψ => (key (labelQ L ψ) ρ).mpr (hΓ ψ hψ))
  · intro h M R ρ hΓ
    have key := toVP_eval M R
    exact (key (labelQ L φ) (Sum.inl ∘ ρ)).mp (h (toVP M R) (Sum.inl ∘ ρ)
      fun ψ hψ => (key (labelQ L ψ) (Sum.inl ∘ ρ)).mpr (hΓ ψ hψ))

end

/-! ## Gotham's (122), with one lexical entry for "book" -/

inductive BNoun | book
  deriving DecidableEq
inductive BRel | pickUp | master
inductive BName | john
inductive BAsp | human | phy | info
  deriving DecidableEq

instance : Fintype BNoun := ⟨{.book}, fun n => by cases n; simp⟩

/-- Picking up takes a physical object, mastering an informational one. -/
def bLex : AspLex Empty BRel BAsp where
  verb v := v.elim
  arg1 _ := .human
  arg2
    | .pickUp => .phy
    | .master => .info

/-- "John picked up and mastered three books." -/
def p122 : Form BNoun Empty BRel BName :=
  .quant (.atLeast 3) .book .top
    (.and (.rel .pickUp (.name .john) (.var 0)) (.rel .master (.name .john) (.var 0)))

/-- "John picked up three books." -/
def h122 : Form BNoun Empty BRel BName :=
  .quant (.atLeast 3) .book .top (.rel .pickUp (.name .john) (.var 0))

/-- Elaboration counts the premise both ways and the conclusion physically. -/
theorem labelQ_p122 : labelQ bLex p122 =
    .quant (.atLeast 3) (.book, [.phy, .info]) .top
      (.and (.rel .pickUp (.name .john) (.var 0)) (.rel .master (.name .john) (.var 0))) := rfl

theorem labelQ_h122 : labelQ bLex h122 =
    .quant (.atLeast 3) (.book, [.phy]) .top (.rel .pickUp (.name .john) (.var 0)) := rfl

theorem gotham122_V : ValidV (Asp := BAsp) bLex [p122] h122 := by
  intro M R ρ hΓ
  have h := hΓ p122 (List.mem_singleton_self _)
  rw [labelQ_p122] at h
  rw [labelQ_h122]
  refine le_trans h (M.countV_anti ?_ fun x hx => ⟨hx.1, hx.2.1⟩)
  intro k hk
  simp only [eff, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk ⊢
  exact Or.inl hk

theorem gotham122_VP : ValidVP (Asp := BAsp) bLex [p122] h122 :=
  (validV_iff bLex [p122] h122).mp gotham122_V

end FraCaS.Encodings.VerbCriteria
