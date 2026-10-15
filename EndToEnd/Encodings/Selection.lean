import EndToEnd.Encodings.Relational

/-!
# Selectional restrictions: what nouns as types add to well-formedness

Chatzikyriakidis & Luo (2017: 49) count selectional restrictions in
favour of nouns as types: "#the television ate the cake" is a type
error, since `eat` takes an animate argument and `television` is not a
subtype of it. With nouns as predicates over one domain the sentence is
well formed, and gets a truth value. This is a claim about which
sentences are *well formed*, not about which entailments are valid, so
it is tested here by comparing typing judgements.

A lexicon (`Sig`) gives each noun, each verb argument position and each
name a type, with subtyping between types. `WT S Γ φ` says the formula
`φ` (of `Relational.lean`'s fragment) is well typed in context `Γ`: each
verb and relation is applied to terms whose types are subtypes of its
argument types, and a quantifier over noun `n` binds a variable of `n`'s
type.

**What decides well-formedness (`wt_iff_of_sameFit`).** Call two types
*alike for selection* when they fit the same argument positions: each
is a subtype of a verb's or relation's argument type exactly when the
other is (`SameFit`). Then two lexicons whose nouns' and names' types
are pairwise alike make exactly the same sentences well formed. So
well-formedness sees a noun's type only through which argument
positions it fits (its *profile*), never the type itself.

**Sorted predicates suffice (`wt_sorts_iff`).** For any lexicon `S`,
the lexicon `S.sorts` has one sort per profile: a sort is a set of
argument types, ordered by reverse inclusion. Its nouns are predicates
over their sort, as in a many-sorted Montague semantics (Retoré 2013's
option (2), "a small ontology"; Mery & Retoré 2013), not types of their
own. `S` and `S.sorts` make exactly the same sentences well formed.
Nouns that fit the same argument positions ("man" and "woman" when
every verb that takes one takes the other) share a sort.

**What typing does for truth (`domain_irrelevance`).** In a model that
respects the types (`Fits`), a well-typed formula's truth never depends
on what a verb or relation does outside its argument types. So, on the
sentences MTT accepts, a verb typed on its domain (MTT's `eat :
Animate → Prop`) and any predicate of all individuals that extends it
give the same truth values. The proof needs the quantifiers to be
conservative (`Conservative`): a quantifier over `n` looks only at the
`n`s. Typed quantifiers are conservative by construction
(`tII_conservative`), and the corpus's determiners are too, by the
equivalence (`pI_conservative`).

**Where the encodings differ (`table_talks_contingent`).** A sentence
the types rule out, "some table talks", has a truth value with nouns as
predicates over one domain, and it depends on what `talk` does to
tables. Both MTT and the sorted lexicon reject it
(`not_wt_table_talks`, `not_wt_sorts_table_talks`).

So the selectional-restriction advantage is owed to typing the verbs'
argument positions, which a many-sorted predicate encoding also does.
It is not owed to each noun being a type. As with dependent types in
Section 3 (`Section3D.lean`), the credit goes to the type structure
around the nouns.

`isA` and identity are checked for scope only: "`t` is an `n`" and
"`t` is `u`" are well formed for any typed terms, as Retoré's
recognising predicates are defined on the top sort.
-/

namespace FraCaS.Encodings.Selection
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed
open FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence FraCaS.Encodings.Relational

variable {Noun Verb Rel Name : Type}

/-! ## Lexicons and typing -/

/-- A lexicon's types: a preorder of types (subtyping), the type of each
noun, of each verb's argument, of each relation's two arguments, and of
each name. -/
structure Sig (Noun Verb Rel Name : Type) where
  Ty : Type
  le : Ty → Ty → Prop
  le_refl : ∀ t, le t t
  le_trans : ∀ a b c, le a b → le b c → le a c
  noun : Noun → Ty
  verb : Verb → Ty
  arg1 : Rel → Ty
  arg2 : Rel → Ty
  name : Name → Ty

/-- A term's type, given the types of the bound variables. -/
inductive HasTy (S : Sig Noun Verb Rel Name) (Γ : List S.Ty) : Term Name → S.Ty → Prop
  | var {k : Nat} {τ : S.Ty} : Γ[k]? = some τ → HasTy S Γ (.var k) τ
  | name (c : Name) : HasTy S Γ (.name c) (S.name c)

/-- Well typed: every verb and relation applies to terms of subtypes of
its argument types. -/
inductive WT (S : Sig Noun Verb Rel Name) : List S.Ty → Form Noun Verb Rel Name → Prop
  | verb {Γ v t τ} : HasTy S Γ t τ → S.le τ (S.verb v) → WT S Γ (.verb v t)
  | rel {Γ r t u τ σ} : HasTy S Γ t τ → HasTy S Γ u σ → S.le τ (S.arg1 r) →
      S.le σ (S.arg2 r) → WT S Γ (.rel r t u)
  | isA {Γ n t τ} : HasTy S Γ t τ → WT S Γ (.isA n t)
  | eq {Γ t u τ σ} : HasTy S Γ t τ → HasTy S Γ u σ → WT S Γ (.eq t u)
  | top {Γ} : WT S Γ .top
  | not {Γ φ} : WT S Γ φ → WT S Γ (.not φ)
  | and {Γ φ ψ} : WT S Γ φ → WT S Γ ψ → WT S Γ (.and φ ψ)
  | or {Γ φ ψ} : WT S Γ φ → WT S Γ ψ → WT S Γ (.or φ ψ)
  | imp {Γ φ ψ} : WT S Γ φ → WT S Γ ψ → WT S Γ (.imp φ ψ)
  | quant {Γ d n C Q} : WT S (S.noun n :: Γ) C → WT S (S.noun n :: Γ) Q →
      WT S Γ (.quant d n C Q)
  | more {Γ n C Q R} : WT S (S.noun n :: Γ) C → WT S (S.noun n :: Γ) Q →
      WT S (S.noun n :: Γ) R → WT S Γ (.more n C Q R)

/-! ## Well-formedness sees only which argument positions a type fits -/

/-- Two types, of two lexicons over the same words, fit the same
argument positions. -/
def SameFit (S S' : Sig Noun Verb Rel Name) (τ : S.Ty) (τ' : S'.Ty) : Prop :=
  (∀ v, S.le τ (S.verb v) ↔ S'.le τ' (S'.verb v)) ∧
  (∀ r, S.le τ (S.arg1 r) ↔ S'.le τ' (S'.arg1 r)) ∧
  (∀ r, S.le τ (S.arg2 r) ↔ S'.le τ' (S'.arg2 r))

theorem SameFit.symm {S S' : Sig Noun Verb Rel Name} {τ : S.Ty} {τ' : S'.Ty}
    (h : SameFit S S' τ τ') : SameFit S' S τ' τ :=
  ⟨fun v => (h.1 v).symm, fun r => (h.2.1 r).symm, fun r => (h.2.2 r).symm⟩

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : ∀ {k : Nat} {a : α}, l[k]? = some a → ∃ b, l'[k]? = some b ∧ R a b := by
  induction h with
  | nil => intro k a hk; simp at hk
  | cons hab _ ih =>
    intro k a hk
    cases k with
    | zero =>
      rw [List.getElem?_cons_zero] at hk
      cases hk
      exact ⟨_, List.getElem?_cons_zero, hab⟩
    | succ k =>
      rw [List.getElem?_cons_succ] at hk
      obtain ⟨b, hb, hr⟩ := ih hk
      exact ⟨b, by rw [List.getElem?_cons_succ]; exact hb, hr⟩

theorem forall₂_swap {α β : Type} {R : α → β → Prop} {R' : β → α → Prop}
    (hR : ∀ a b, R a b → R' b a) {l : List α} {l' : List β} (h : List.Forall₂ R l l') :
    List.Forall₂ R' l' l := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hR _ _ hab) ih

theorem forall₂_map {α β : Type} {R : α → β → Prop} (f : α → β) (hf : ∀ a, R a (f a)) :
    ∀ l : List α, List.Forall₂ R l (l.map f)
  | [] => .nil
  | a :: l => .cons (hf a) (forall₂_map f hf l)

theorem hasTy_transfer {S S' : Sig Noun Verb Rel Name}
    (hc : ∀ c, SameFit S S' (S.name c) (S'.name c)) {Γ : List S.Ty} {Γ' : List S'.Ty}
    (hΓ : List.Forall₂ (SameFit S S') Γ Γ') {t : Term Name} {τ : S.Ty} (h : HasTy S Γ t τ) :
    ∃ τ', HasTy S' Γ' t τ' ∧ SameFit S S' τ τ' := by
  cases h with
  | var hk =>
    obtain ⟨τ', hk', hs⟩ := forall₂_getElem? hΓ hk
    exact ⟨τ', .var hk', hs⟩
  | name c => exact ⟨S'.name c, .name c, hc c⟩

theorem wt_transfer {S S' : Sig Noun Verb Rel Name}
    (hn : ∀ n, SameFit S S' (S.noun n) (S'.noun n))
    (hc : ∀ c, SameFit S S' (S.name c) (S'.name c)) {Γ : List S.Ty}
    {φ : Form Noun Verb Rel Name} (h : WT S Γ φ) :
    ∀ {Γ' : List S'.Ty}, List.Forall₂ (SameFit S S') Γ Γ' → WT S' Γ' φ := by
  induction h with
  | verb ht hle =>
    intro Γ' hΓ
    obtain ⟨τ', ht', hs⟩ := hasTy_transfer hc hΓ ht
    exact .verb ht' ((hs.1 _).mp hle)
  | rel ht hu hle1 hle2 =>
    intro Γ' hΓ
    obtain ⟨τ', ht', hs⟩ := hasTy_transfer hc hΓ ht
    obtain ⟨σ', hu', hs'⟩ := hasTy_transfer hc hΓ hu
    exact .rel ht' hu' ((hs.2.1 _).mp hle1) ((hs'.2.2 _).mp hle2)
  | isA ht =>
    intro Γ' hΓ
    obtain ⟨τ', ht', -⟩ := hasTy_transfer hc hΓ ht
    exact .isA ht'
  | eq ht hu =>
    intro Γ' hΓ
    obtain ⟨τ', ht', -⟩ := hasTy_transfer hc hΓ ht
    obtain ⟨σ', hu', -⟩ := hasTy_transfer hc hΓ hu
    exact .eq ht' hu'
  | top => intro _ _; exact .top
  | not _ ih => intro Γ' hΓ; exact .not (ih hΓ)
  | and _ _ ih1 ih2 => intro Γ' hΓ; exact .and (ih1 hΓ) (ih2 hΓ)
  | or _ _ ih1 ih2 => intro Γ' hΓ; exact .or (ih1 hΓ) (ih2 hΓ)
  | imp _ _ ih1 ih2 => intro Γ' hΓ; exact .imp (ih1 hΓ) (ih2 hΓ)
  | @quant _ _ n _ _ _ _ ihC ihQ =>
    intro Γ' hΓ
    exact .quant (ihC (.cons (hn n) hΓ)) (ihQ (.cons (hn n) hΓ))
  | @more _ n _ _ _ _ _ _ ihC ihQ ihR =>
    intro Γ' hΓ
    exact .more (ihC (.cons (hn n) hΓ)) (ihQ (.cons (hn n) hΓ)) (ihR (.cons (hn n) hΓ))

/-- **Well-formedness sees only fit.** Lexicons whose nouns and names
have types alike for selection, in contexts alike for selection, make
the same formulas well formed. -/
theorem wt_iff_of_sameFit {S S' : Sig Noun Verb Rel Name}
    (hn : ∀ n, SameFit S S' (S.noun n) (S'.noun n))
    (hc : ∀ c, SameFit S S' (S.name c) (S'.name c)) {Γ : List S.Ty} {Γ' : List S'.Ty}
    (hΓ : List.Forall₂ (SameFit S S') Γ Γ') (φ : Form Noun Verb Rel Name) :
    WT S Γ φ ↔ WT S' Γ' φ :=
  ⟨fun h => wt_transfer hn hc h hΓ,
    fun h => wt_transfer (fun n => (hn n).symm) (fun c => (hc c).symm) h
      (forall₂_swap (R := SameFit S S') (fun _ _ h => SameFit.symm h) hΓ)⟩

/-! ## Sorted predicates: one sort per profile -/

/-- `d` is the type of some argument position. -/
def Sig.IsDom (S : Sig Noun Verb Rel Name) (d : S.Ty) : Prop :=
  (∃ v, S.verb v = d) ∨ (∃ r, S.arg1 r = d) ∨ (∃ r, S.arg2 r = d)

/-- A type's profile: the argument positions' types it is a subtype of. -/
def Sig.prof (S : Sig Noun Verb Rel Name) (t : S.Ty) : S.Ty → Prop :=
  fun d => S.IsDom d ∧ S.le t d

/-- The many-sorted lexicon: its sorts are profiles, ordered by reverse
inclusion, and each word's sort is its type's profile. -/
def Sig.sorts (S : Sig Noun Verb Rel Name) : Sig Noun Verb Rel Name where
  Ty := S.Ty → Prop
  le P Q := ∀ d, Q d → P d
  le_refl _ _ h := h
  le_trans _ _ _ h1 h2 d hd := h1 d (h2 d hd)
  noun n := S.prof (S.noun n)
  verb v := S.prof (S.verb v)
  arg1 r := S.prof (S.arg1 r)
  arg2 r := S.prof (S.arg2 r)
  name c := S.prof (S.name c)

/-- Against an argument position's type, a type's profile is below the
position's profile exactly when the type is below the position's type. -/
theorem Sig.prof_le_iff (S : Sig Noun Verb Rel Name) {t d : S.Ty} (hd : S.IsDom d) :
    S.sorts.le (S.prof t) (S.prof d) ↔ S.le t d := by
  constructor
  · intro h
    exact (h d ⟨hd, S.le_refl d⟩).2
  · intro htd e he
    exact ⟨he.1, S.le_trans _ _ _ htd he.2⟩

theorem Sig.sameFit_prof (S : Sig Noun Verb Rel Name) (t : S.Ty) :
    SameFit S S.sorts t (S.prof t) :=
  ⟨fun v => (S.prof_le_iff (d := S.verb v) (Or.inl ⟨v, rfl⟩)).symm,
    fun r => (S.prof_le_iff (d := S.arg1 r) (Or.inr (Or.inl ⟨r, rfl⟩))).symm,
    fun r => (S.prof_le_iff (d := S.arg2 r) (Or.inr (Or.inr ⟨r, rfl⟩))).symm⟩

/-- **Sorted predicates suffice.** A lexicon and its many-sorted
counterpart, whose sorts are profiles, make the same formulas well
formed. -/
theorem wt_sorts_iff (S : Sig Noun Verb Rel Name) (Γ : List S.Ty)
    (φ : Form Noun Verb Rel Name) : WT S Γ φ ↔ WT S.sorts (Γ.map S.prof) φ :=
  wt_iff_of_sameFit (fun n => S.sameFit_prof (S.noun n)) (fun c => S.sameFit_prof (S.name c))
    (forall₂_map S.prof S.sameFit_prof Γ) φ

/-! ## Typing and truth: verbs outside their domains do not matter -/

section
variable {A : Type}

/-- A model respects a lexicon's types, read as sets of individuals
`ext`: subtypes are subsets, each noun's members are of its type, and
each name is of its type. -/
structure Fits (S : Sig Noun Verb Rel Name) (I : Interp Noun Verb Rel Name A)
    (ext : S.Ty → A → Prop) : Prop where
  mono : ∀ a b x, S.le a b → ext a x → ext b x
  noun : ∀ n x, I.isA n x → ext (S.noun n) x
  name : ∀ c, ext (S.name c) (I.name c)

/-- Quantifiers over `n` look only at the `n`s. -/
def Conservative (I : Interp Noun Verb Rel Name A) : Prop :=
  (∀ d n (C Q C' Q' : A → Prop), (∀ x, I.isA n x → (C x ↔ C' x)) →
    (∀ x, I.isA n x → (Q x ↔ Q' x)) → (I.q d n C Q ↔ I.q d n C' Q')) ∧
  (∀ n (C Q R C' Q' R' : A → Prop), (∀ x, I.isA n x → (C x ↔ C' x)) →
    (∀ x, I.isA n x → (Q x ↔ Q' x)) → (∀ x, I.isA n x → (R x ↔ R' x)) →
    (I.more n C Q R ↔ I.more n C' Q' R'))

/-- An assignment gives each variable an individual of its type. -/
def Respects (S : Sig Noun Verb Rel Name) (ext : S.Ty → A → Prop) (Γ : List S.Ty)
    (ρ : Nat → A) : Prop :=
  ∀ k τ, Γ[k]? = some τ → ext τ (ρ k)

theorem respects_push {S : Sig Noun Verb Rel Name} {ext : S.Ty → A → Prop} {Γ : List S.Ty}
    {ρ : Nat → A} {σ : S.Ty} {x : A} (hρ : Respects S ext Γ ρ) (hx : ext σ x) :
    Respects S ext (σ :: Γ) (push x ρ) := by
  intro k τ hk
  cases k with
  | zero =>
    rw [List.getElem?_cons_zero] at hk
    cases hk
    exact hx
  | succ k =>
    rw [List.getElem?_cons_succ] at hk
    exact hρ k τ hk

theorem term_ext {S : Sig Noun Verb Rel Name} {I : Interp Noun Verb Rel Name A}
    {ext : S.Ty → A → Prop} {Γ : List S.Ty} {ρ : Nat → A} {t : Term Name} {τ : S.Ty}
    (hfit : Fits S I ext) (hρ : Respects S ext Γ ρ) (h : HasTy S Γ t τ) :
    ext τ (t.eval I.name ρ) := by
  cases h with
  | var hk => exact hρ _ _ hk
  | name c => exact hfit.name c

/-- The interpretation with the verbs and relations replaced. -/
def Interp.withVerbs (I : Interp Noun Verb Rel Name A) (verb : Verb → A → Prop)
    (rel : Rel → A → A → Prop) : Interp Noun Verb Rel Name A :=
  { I with verb := verb, rel := rel }

/-- **Domain irrelevance.** In a model that respects the types, a
well-typed formula has the same truth value under any two
interpretations of the verbs and relations that agree on their argument
types. -/
theorem domain_irrelevance {S : Sig Noun Verb Rel Name} {I : Interp Noun Verb Rel Name A}
    {ext : S.Ty → A → Prop} (hfit : Fits S I ext) (hcons : Conservative I)
    {verb' : Verb → A → Prop} {rel' : Rel → A → A → Prop}
    (hv : ∀ v x, ext (S.verb v) x → (I.verb v x ↔ verb' v x))
    (hr : ∀ r x y, ext (S.arg1 r) x → ext (S.arg2 r) y → (I.rel r x y ↔ rel' r x y))
    {Γ : List S.Ty} {φ : Form Noun Verb Rel Name} (h : WT S Γ φ) :
    ∀ ρ, Respects S ext Γ ρ → (Form.eval I φ ρ ↔ Form.eval (Interp.withVerbs I verb' rel') φ ρ) := by
  induction h with
  | verb ht hle =>
    intro ρ hρ
    exact hv _ _ (hfit.mono _ _ _ hle (term_ext hfit hρ ht))
  | rel ht hu hle1 hle2 =>
    intro ρ hρ
    exact hr _ _ _ (hfit.mono _ _ _ hle1 (term_ext hfit hρ ht))
      (hfit.mono _ _ _ hle2 (term_ext hfit hρ hu))
  | isA _ => intro _ _; exact Iff.rfl
  | eq _ _ => intro _ _; exact Iff.rfl
  | top => intro _ _; exact Iff.rfl
  | not _ ih => intro ρ hρ; exact not_congr (ih ρ hρ)
  | and _ _ ih1 ih2 => intro ρ hρ; exact and_congr (ih1 ρ hρ) (ih2 ρ hρ)
  | or _ _ ih1 ih2 => intro ρ hρ; exact or_congr (ih1 ρ hρ) (ih2 ρ hρ)
  | imp _ _ ih1 ih2 => intro ρ hρ; exact imp_congr (ih1 ρ hρ) (ih2 ρ hρ)
  | @quant _ d n _ _ _ _ ihC ihQ =>
    intro ρ hρ
    exact hcons.1 d n _ _ _ _
      (fun x hx => ihC (push x ρ) (respects_push hρ (hfit.noun n x hx)))
      (fun x hx => ihQ (push x ρ) (respects_push hρ (hfit.noun n x hx)))
  | @more _ n _ _ _ _ _ _ ihC ihQ ihR =>
    intro ρ hρ
    exact hcons.2 n _ _ _ _ _ _
      (fun x hx => ihC (push x ρ) (respects_push hρ (hfit.noun n x hx)))
      (fun x hx => ihQ (push x ρ) (respects_push hρ (hfit.noun n x hx)))
      (fun x hx => ihR (push x ρ) (respects_push hρ (hfit.noun n x hx)))

/-- Conservativity passes along agreement. -/
theorem Conservative.of_agree {I J : Interp Noun Verb Rel Name A} (h : I.Agree J)
    (hJ : Conservative J) : Conservative I :=
  ⟨fun d n C Q C' Q' hC hQ =>
    (h.q d n C Q).trans ((hJ.1 d n C Q C' Q' (fun x hx => hC x ((h.isA n x).mpr hx))
      (fun x hx => hQ x ((h.isA n x).mpr hx))).trans (h.q d n C' Q').symm),
   fun n C Q R C' Q' R' hC hQ hR =>
    (h.more n C Q R).trans ((hJ.2 n C Q R C' Q' R' (fun x hx => hC x ((h.isA n x).mpr hx))
      (fun x hx => hQ x ((h.isA n x).mpr hx)) (fun x hx => hR x ((h.isA n x).mpr hx))).trans
      (h.more n C' Q' R').symm)⟩

end

/-! ## Typed quantifiers are conservative -/

theorem countBy_congr {N B : Type} [Fintype N] {f : N → B} {P P' : N → Prop}
    {_ : DecidableEq B} {_ : DecidablePred P} {_ : DecidablePred P'} (h : ∀ x, P x ↔ P' x) :
    countBy f P = countBy f P' := by
  unfold countBy
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h x

theorem countI_congr {N A : Type} [Fintype N] (e : N → A) {P P' : A → Prop}
    (h : ∀ y, P (e y) ↔ P' (e y)) : countI e P = countI e P' := by
  unfold countI
  exact countBy_congr h

theorem detI_congr {N A : Type} [Fintype N] (e : N → A) (d : Det) {C Q C' Q' : A → Prop}
    (hC : ∀ y, C (e y) ↔ C' (e y)) (hQ : ∀ y, Q (e y) ↔ Q' (e y)) :
    detI e d C Q ↔ detI e d C' Q' := by
  have c1 : countI e (fun x => C x ∧ Q x) = countI e (fun x => C' x ∧ Q' x) :=
    countI_congr e (P := fun x => C x ∧ Q x) (P' := fun x => C' x ∧ Q' x)
      fun y => and_congr (hC y) (hQ y)
  have c2 : countI e C = countI e C' := countI_congr e hC
  have hE : EveryT e C Q ↔ EveryT e C' Q' := forall_congr' fun y => imp_congr (hC y) (hQ y)
  have hN : NoT e C Q ↔ NoT e C' Q' :=
    forall_congr' fun y => imp_congr (hC y) (not_congr (hQ y))
  cases d with
  | every => exact hE
  | some => exact exists_congr fun y => and_congr (hC y) (hQ y)
  | no => exact hN
  | most =>
    show MostI e C Q ↔ MostI e C' Q'
    unfold MostI
    rw [c1, c2]
  | both =>
    show BothI e C Q ↔ BothI e C' Q'
    unfold BothI
    rw [c2]
    exact and_congr Iff.rfl hE
  | neither =>
    show NeitherI e C Q ↔ NeitherI e C' Q'
    unfold NeitherI
    rw [c2]
    exact and_congr Iff.rfl hN
  | atLeast k =>
    show AtLeastI k e C Q ↔ AtLeastI k e C' Q'
    unfold AtLeastI
    rw [c1]
  | atMost k =>
    show AtMostI k e C Q ↔ AtMostI k e C' Q'
    unfold AtMostI
    rw [c1]
  | exactly k =>
    show ExactlyI k e C Q ↔ ExactlyI k e C' Q'
    unfold ExactlyI
    rw [c1]

theorem moreI_congr {N A : Type} [Fintype N] (e : N → A) {C Q R C' Q' R' : A → Prop}
    (hC : ∀ y, C (e y) ↔ C' (e y)) (hQ : ∀ y, Q (e y) ↔ Q' (e y))
    (hR : ∀ y, R (e y) ↔ R' (e y)) : MoreI e C Q R ↔ MoreI e C' Q' R' := by
  have c1 : countI e (fun x => C x ∧ Q x) = countI e (fun x => C' x ∧ Q' x) :=
    countI_congr e (P := fun x => C x ∧ Q x) (P' := fun x => C' x ∧ Q' x)
      fun y => and_congr (hC y) (hQ y)
  have c2 : countI e (fun x => C x ∧ R x) = countI e (fun x => C' x ∧ R' x) :=
    countI_congr e (P := fun x => C x ∧ R x) (P' := fun x => C' x ∧ R' x)
      fun y => and_congr (hC y) (hR y)
  unfold MoreI
  rw [c1, c2]

/-- Quantifiers over a noun's type see only the noun's elements. -/
theorem tII_conservative (M : TModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) :
    Conservative (tII M rel) :=
  ⟨fun d n _ _ _ _ hC hQ =>
    detI_congr (M.emb n) d (fun y => hC _ ⟨y, rfl⟩) (fun y => hQ _ ⟨y, rfl⟩),
   fun n _ _ _ _ _ _ hC hQ hR =>
    moreI_congr (M.emb n) (fun y => hC _ ⟨y, rfl⟩) (fun y => hQ _ ⟨y, rfl⟩)
      (fun y => hR _ ⟨y, rfl⟩)⟩

/-- The corpus's determiners are conservative too, by the equivalence
with typed quantifiers. -/
theorem pI_conservative (M : PModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) :
    Conservative (pI M rel) :=
  Conservative.of_agree ((pI_agree_lift_shadow M rel).trans (tII_agree_shadow M.lift rel).symm)
    (tII_conservative M.lift rel)

/-! ## An example: "some table talks"

Two sorts: humans, and physical objects, with every type a subtype of
the physical objects. "Talk" takes a human, "fall" a physical object. -/

inductive ENoun | man | table
inductive EVerb | talk | fall
inductive ETy | human | phys

/-- The example lexicon. -/
def eSig : Sig ENoun EVerb Empty Empty where
  Ty := ETy
  le a b := a = b ∨ b = .phys
  le_refl _ := Or.inl rfl
  le_trans _ _ _ h1 h2 := by
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp
  noun | .man => .human | .table => .phys
  verb | .talk => .human | .fall => .phys
  arg1 r := r.elim
  arg2 r := r.elim
  name c := c.elim

/-- "Some table talks". -/
def tableTalks : Form ENoun EVerb Empty Empty := .quant .some .table .top (.verb .talk (.var 0))

/-- "Some man falls". -/
def manFalls : Form ENoun EVerb Empty Empty := .quant .some .man .top (.verb .fall (.var 0))

theorem wt_man_falls : WT eSig [] manFalls :=
  .quant .top (.verb (.var List.getElem?_cons_zero) (Or.inr rfl))

theorem not_wt_table_talks : ¬ WT eSig [] tableTalks := by
  intro h
  unfold tableTalks at h
  cases h with
  | quant _ hQ =>
    cases hQ with
    | verb ht hle =>
      cases ht with
      | var hk =>
        rw [List.getElem?_cons_zero] at hk
        cases hk
        rcases hle with h | h <;> cases h

theorem not_wt_sorts_table_talks : ¬ WT eSig.sorts [] tableTalks :=
  fun h => not_wt_table_talks ((wt_sorts_iff eSig [] tableTalks).mpr h)

/-- With nouns as predicates over one domain, "some table talks" is well
formed and contingent: true or false depending on what `talk` does to
tables. -/
theorem table_talks_contingent :
    (∃ (M : PModel ENoun EVerb Empty) (rel : Empty → M.A → M.A → Prop) (ρ : Nat → M.A),
      Form.eval (pI M rel) tableTalks ρ) ∧
    (∃ (M : PModel ENoun EVerb Empty) (rel : Empty → M.A → M.A → Prop) (ρ : Nat → M.A),
      ¬ Form.eval (pI M rel) tableTalks ρ) := by
  refine ⟨⟨⟨Unit, inferInstance, fun _ _ => True, fun _ _ => True, fun c => c.elim⟩,
      fun r => r.elim, fun _ => (), ?_⟩,
    ⟨⟨Unit, inferInstance, fun _ _ => True, fun _ _ => False, fun c => c.elim⟩,
      fun r => r.elim, fun _ => (), ?_⟩⟩
  · exact ⟨(), ⟨trivial, trivial⟩, trivial⟩
  · rintro ⟨_, _, h⟩
    exact h

end FraCaS.Encodings.Selection
