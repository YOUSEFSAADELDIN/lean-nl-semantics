import EndToEnd.Encodings.Relational

/-!
# The equivalence, proof-theoretically

Every theorem comparing the encodings so far is about validity over
finite models, with classical logic for counting. For Modern Type
Theories entailment is derivability in an intuitionistic type theory
(Luo; Chatzikyriakidis & Luo's Coq formalizations). This file compares
the two encodings on that ground.

- **Contexts, not models.** A typed context (`TCtx`) is any type of
  individuals, any type for each noun with an embedding, and any
  predicates and relations: no finiteness, no decidability. A predicate
  context (`PCtx`) likewise. An entailment is provable when it holds in
  every context (`ProvT`, `ProvP`). A proof of that is a derivation from
  the context's variables.
- **Counting without decidability.** "At least `k` `N`s are `P`" says
  there is a list of `k` elements of `N`'s type, each `P`, whose
  individuals are pairwise distinct (`AtLeastE`). "At most" and
  "exactly" are its negation and conjunction. This counts individuals,
  as `validI_iff` does. "Most" and "more ... than" compare two counts
  and are left to the classical, finite setting.
- **`provT_iff`.** The fragment (every, some, no, at least, at most and
  exactly `k`; one- and two-place verbs; identity; connectives; nested
  quantifiers) derives the same entailments with nouns as types and
  with nouns as predicates. Each typed context agrees with its
  predicate reading (`TCtx.shadow_eval`) and each predicate context with
  its typed reading (`PCtx.lift_eval`), formula by formula.
- **Without classical axioms.** The proofs avoid `simp` and classical
  lemmas. Lean's `#print axioms` at the end of the file lists the
  axioms `provT_iff` depends on; `Classical.choice` is not among them,
  so the equivalence holds intuitionistically.
-/

namespace FraCaS.Encodings.Constructive
open FraCaS.Encodings.Relational

variable {Noun Verb Rel Name : Type}

/-! ## The fragment -/

inductive CDet where
  | every | some | no
  | atLeast (k : Nat) | atMost (k : Nat) | exactly (k : Nat)

inductive CForm (Noun Verb Rel Name : Type) where
  | verb : Verb → Term Name → CForm Noun Verb Rel Name
  | rel : Rel → Term Name → Term Name → CForm Noun Verb Rel Name
  | isA : Noun → Term Name → CForm Noun Verb Rel Name
  | eq : Term Name → Term Name → CForm Noun Verb Rel Name
  | top : CForm Noun Verb Rel Name
  | not : CForm Noun Verb Rel Name → CForm Noun Verb Rel Name
  | and : CForm Noun Verb Rel Name → CForm Noun Verb Rel Name → CForm Noun Verb Rel Name
  | or : CForm Noun Verb Rel Name → CForm Noun Verb Rel Name → CForm Noun Verb Rel Name
  | imp : CForm Noun Verb Rel Name → CForm Noun Verb Rel Name → CForm Noun Verb Rel Name
  /-- `d` noun `n` that `C` are `Q`: binds `var 0` in `C` and `Q` -/
  | quant : CDet → Noun → CForm Noun Verb Rel Name → CForm Noun Verb Rel Name →
      CForm Noun Verb Rel Name

/-! ## Lists, by hand -/

section
variable {α β : Type}

theorem length_map' (f : α → β) : ∀ l : List α, (l.map f).length = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (length_map' f l)

theorem mem_map_of_mem' (f : α → β) {a : α} {l : List α} (h : a ∈ l) : f a ∈ l.map f := by
  induction h with
  | head as => exact .head _
  | tail b _ ih => exact .tail _ ih

theorem exists_of_mem_map' (f : α → β) {b : β} :
    ∀ (l : List α), b ∈ l.map f → ∃ a, a ∈ l ∧ f a = b
  | [], h => by cases h
  | x :: l, h => by
    cases h with
    | head => exact ⟨x, .head _, rfl⟩
    | tail _ h' =>
      obtain ⟨a, ha, hfa⟩ := exists_of_mem_map' f l h'
      exact ⟨a, .tail _ ha, hfa⟩

/-- A list of individuals each in the image of `e` is the image of a
list of elements. -/
theorem lift_list (e : α → β) : ∀ l : List β, (∀ x, x ∈ l → ∃ y, e y = x) →
    ∃ l' : List α, l'.map e = l
  | [], _ => ⟨[], rfl⟩
  | x :: l, h =>
    let ⟨y, hy⟩ := h x (.head _)
    let ⟨l', hl'⟩ := lift_list e l (fun z hz => h z (.tail _ hz))
    ⟨y :: l', by rw [List.map_cons, hy, hl']⟩

end

/-! ## Counting without decidability -/

/-- At least `k` individuals are `P`: a list of `k` distinct ones. -/
def AtLeastL {A : Type} (k : Nat) (P : A → Prop) : Prop :=
  ∃ l : List A, l.length = k ∧ (∀ x, x ∈ l → P x) ∧ l.Nodup

/-- At least `k` elements of a type, with pairwise distinct individuals,
are `P`. -/
def AtLeastE {T A : Type} (e : T → A) (k : Nat) (P : A → Prop) : Prop :=
  ∃ l : List T, l.length = k ∧ (∀ y, y ∈ l → P (e y)) ∧ (l.map e).Nodup

theorem atLeastL_congr {A : Type} {k : Nat} {P P' : A → Prop} (h : ∀ x, P x ↔ P' x) :
    AtLeastL k P ↔ AtLeastL k P' :=
  ⟨fun ⟨l, hl, hP, hn⟩ => ⟨l, hl, fun x hx => (h x).mp (hP x hx), hn⟩,
   fun ⟨l, hl, hP, hn⟩ => ⟨l, hl, fun x hx => (h x).mpr (hP x hx), hn⟩⟩

/-- Counting a type's elements by their individuals is counting the
individuals in its image. -/
theorem atLeastE_iff {T A : Type} (e : T → A) (k : Nat) (P : A → Prop) :
    AtLeastE e k P ↔ AtLeastL k (fun x => (∃ y, e y = x) ∧ P x) := by
  constructor
  · intro ⟨l, hl, hP, hn⟩
    refine ⟨l.map e, (length_map' e l).trans hl, ?_, hn⟩
    intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_of_mem_map' e l hx
    exact ⟨⟨y, hyx⟩, hyx ▸ hP y hy⟩
  · intro ⟨l, hl, hP, hn⟩
    obtain ⟨l', hl'⟩ := lift_list e l (fun x hx => (hP x hx).1)
    refine ⟨l', ?_, ?_, ?_⟩
    · rw [← length_map' e l', hl']
      exact hl
    · intro y hy
      have hm : e y ∈ l := by
        rw [← hl']
        exact mem_map_of_mem' e hy
      exact (hP (e y) hm).2
    · rw [hl']
      exact hn

/-! ## The two meanings of a determiner -/

/-- Over a noun's type, counting individuals. -/
def detTy {T A : Type} (e : T → A) : CDet → (A → Prop) → (A → Prop) → Prop
  | .every, C, Q => ∀ y, C (e y) → Q (e y)
  | .some, C, Q => ∃ y, C (e y) ∧ Q (e y)
  | .no, C, Q => ∀ y, C (e y) → ¬ Q (e y)
  | .atLeast k, C, Q => AtLeastE e k (fun x => C x ∧ Q x)
  | .atMost k, C, Q => ¬ AtLeastE e (k + 1) (fun x => C x ∧ Q x)
  | .exactly k, C, Q => AtLeastE e k (fun x => C x ∧ Q x) ∧ ¬ AtLeastE e (k + 1) (fun x => C x ∧ Q x)

/-- Over the individuals that are `D`. -/
def detPr {A : Type} (D : A → Prop) : CDet → (A → Prop) → (A → Prop) → Prop
  | .every, C, Q => ∀ x, D x ∧ C x → Q x
  | .some, C, Q => ∃ x, (D x ∧ C x) ∧ Q x
  | .no, C, Q => ∀ x, D x ∧ C x → ¬ Q x
  | .atLeast k, C, Q => AtLeastL k (fun x => (D x ∧ C x) ∧ Q x)
  | .atMost k, C, Q => ¬ AtLeastL (k + 1) (fun x => (D x ∧ C x) ∧ Q x)
  | .exactly k, C, Q =>
    AtLeastL k (fun x => (D x ∧ C x) ∧ Q x) ∧ ¬ AtLeastL (k + 1) (fun x => (D x ∧ C x) ∧ Q x)

/-- A determiner over a noun's type says what it says over the
individuals in the type's image. -/
theorem det_bridge {T A : Type} (e : T → A) (d : CDet) {C Q C' Q' : A → Prop}
    (hC : ∀ x, C x ↔ C' x) (hQ : ∀ x, Q x ↔ Q' x) :
    detTy e d C Q ↔ detPr (fun x => ∃ y, e y = x) d C' Q' := by
  have hAL : ∀ k, AtLeastE e k (fun x => C x ∧ Q x) ↔
      AtLeastL k (fun x => ((∃ y, e y = x) ∧ C' x) ∧ Q' x) := fun k =>
    (atLeastE_iff e k _).trans (atLeastL_congr fun x =>
      ⟨fun ⟨hd, hc, hq⟩ => ⟨⟨hd, (hC x).mp hc⟩, (hQ x).mp hq⟩,
       fun ⟨⟨hd, hc⟩, hq⟩ => ⟨hd, (hC x).mpr hc, (hQ x).mpr hq⟩⟩)
  cases d with
  | every =>
    show (∀ y, C (e y) → Q (e y)) ↔ ∀ x, (∃ y, e y = x) ∧ C' x → Q' x
    constructor
    · intro h x ⟨⟨y, hy⟩, hc⟩
      subst hy
      exact (hQ _).mp (h y ((hC _).mpr hc))
    · intro h y hc
      exact (hQ _).mpr (h (e y) ⟨⟨y, rfl⟩, (hC _).mp hc⟩)
  | some =>
    show (∃ y, C (e y) ∧ Q (e y)) ↔ ∃ x, ((∃ y, e y = x) ∧ C' x) ∧ Q' x
    constructor
    · intro ⟨y, hc, hq⟩
      exact ⟨e y, ⟨⟨y, rfl⟩, (hC _).mp hc⟩, (hQ _).mp hq⟩
    · intro ⟨x, ⟨⟨y, hy⟩, hc⟩, hq⟩
      subst hy
      exact ⟨y, (hC _).mpr hc, (hQ _).mpr hq⟩
  | no =>
    show (∀ y, C (e y) → ¬ Q (e y)) ↔ ∀ x, (∃ y, e y = x) ∧ C' x → ¬ Q' x
    constructor
    · intro h x ⟨⟨y, hy⟩, hc⟩ hq
      subst hy
      exact h y ((hC _).mpr hc) ((hQ _).mpr hq)
    · intro h y hc hq
      exact h (e y) ⟨⟨y, rfl⟩, (hC _).mp hc⟩ ((hQ _).mp hq)
  | atLeast k => exact hAL k
  | atMost k => exact not_congr (hAL (k + 1))
  | exactly k => exact and_congr (hAL k) (not_congr (hAL (k + 1)))

theorem detPr_congr {A : Type} (d : CDet) {D D' C Q C' Q' : A → Prop} (hD : ∀ x, D x ↔ D' x)
    (hC : ∀ x, C x ↔ C' x) (hQ : ∀ x, Q x ↔ Q' x) : detPr D d C Q ↔ detPr D' d C' Q' := by
  have hR : ∀ x, ((D x ∧ C x) ∧ Q x) ↔ ((D' x ∧ C' x) ∧ Q' x) := fun x =>
    and_congr (and_congr (hD x) (hC x)) (hQ x)
  cases d with
  | every =>
    show (∀ x, D x ∧ C x → Q x) ↔ ∀ x, D' x ∧ C' x → Q' x
    exact ⟨fun h x hx => (hQ x).mp (h x ⟨(hD x).mpr hx.1, (hC x).mpr hx.2⟩),
      fun h x hx => (hQ x).mpr (h x ⟨(hD x).mp hx.1, (hC x).mp hx.2⟩)⟩
  | some =>
    show (∃ x, (D x ∧ C x) ∧ Q x) ↔ ∃ x, (D' x ∧ C' x) ∧ Q' x
    exact ⟨fun ⟨x, hx⟩ => ⟨x, (hR x).mp hx⟩, fun ⟨x, hx⟩ => ⟨x, (hR x).mpr hx⟩⟩
  | no =>
    show (∀ x, D x ∧ C x → ¬ Q x) ↔ ∀ x, D' x ∧ C' x → ¬ Q' x
    exact ⟨fun h x hx hq => h x ⟨(hD x).mpr hx.1, (hC x).mpr hx.2⟩ ((hQ x).mpr hq),
      fun h x hx hq => h x ⟨(hD x).mp hx.1, (hC x).mp hx.2⟩ ((hQ x).mp hq)⟩
  | atLeast k => exact atLeastL_congr hR
  | atMost k => exact not_congr (atLeastL_congr hR)
  | exactly k => exact and_congr (atLeastL_congr hR) (not_congr (atLeastL_congr hR))

/-! ## Contexts and derivability -/

/-- A typed context: a type of individuals, a type for each noun with an
embedding, predicates, relations and names. Nothing finite, nothing
decidable. -/
structure TCtx (Noun Verb Rel Name : Type) where
  A : Type
  T : Noun → Type
  emb : ∀ n, T n → A
  verb : Verb → A → Prop
  rel : Rel → A → A → Prop
  name : Name → A

/-- A predicate context: nouns are predicates of the individuals. -/
structure PCtx (Noun Verb Rel Name : Type) where
  A : Type
  noun : Noun → A → Prop
  verb : Verb → A → Prop
  rel : Rel → A → A → Prop
  name : Name → A

def TCtx.eval (M : TCtx Noun Verb Rel Name) : CForm Noun Verb Rel Name → (Nat → M.A) → Prop
  | .verb v t, ρ => M.verb v (t.eval M.name ρ)
  | .rel r t u, ρ => M.rel r (t.eval M.name ρ) (u.eval M.name ρ)
  | .isA n t, ρ => ∃ y, M.emb n y = t.eval M.name ρ
  | .eq t u, ρ => t.eval M.name ρ = u.eval M.name ρ
  | .top, _ => True
  | .not φ, ρ => ¬ M.eval φ ρ
  | .and φ ψ, ρ => M.eval φ ρ ∧ M.eval ψ ρ
  | .or φ ψ, ρ => M.eval φ ρ ∨ M.eval ψ ρ
  | .imp φ ψ, ρ => M.eval φ ρ → M.eval ψ ρ
  | .quant d n C Q, ρ =>
    detTy (M.emb n) d (fun x => M.eval C (push x ρ)) (fun x => M.eval Q (push x ρ))

def PCtx.eval (M : PCtx Noun Verb Rel Name) : CForm Noun Verb Rel Name → (Nat → M.A) → Prop
  | .verb v t, ρ => M.verb v (t.eval M.name ρ)
  | .rel r t u, ρ => M.rel r (t.eval M.name ρ) (u.eval M.name ρ)
  | .isA n t, ρ => M.noun n (t.eval M.name ρ)
  | .eq t u, ρ => t.eval M.name ρ = u.eval M.name ρ
  | .top, _ => True
  | .not φ, ρ => ¬ M.eval φ ρ
  | .and φ ψ, ρ => M.eval φ ρ ∧ M.eval ψ ρ
  | .or φ ψ, ρ => M.eval φ ρ ∨ M.eval ψ ρ
  | .imp φ ψ, ρ => M.eval φ ρ → M.eval ψ ρ
  | .quant d n C Q, ρ =>
    detPr (M.noun n) d (fun x => M.eval C (push x ρ)) (fun x => M.eval Q (push x ρ))

/-- A typed context read with nouns as predicates: being an `n` is being
in the image of `n`'s type. -/
def TCtx.shadow (M : TCtx Noun Verb Rel Name) : PCtx Noun Verb Rel Name :=
  { A := M.A, noun := fun n x => ∃ y, M.emb n y = x, verb := M.verb, rel := M.rel,
    name := M.name }

/-- A predicate context read with nouns as types: each noun's type is its
members. -/
def PCtx.lift (M : PCtx Noun Verb Rel Name) : TCtx Noun Verb Rel Name :=
  { A := M.A, T := fun n => {x // M.noun n x}, emb := fun _ y => y.val, verb := M.verb,
    rel := M.rel, name := M.name }

theorem TCtx.shadow_eval (M : TCtx Noun Verb Rel Name) :
    ∀ (φ : CForm Noun Verb Rel Name) (ρ : Nat → M.A), M.eval φ ρ ↔ M.shadow.eval φ ρ
  | .verb _ _, _ => Iff.rfl
  | .rel _ _ _, _ => Iff.rfl
  | .isA _ _, _ => Iff.rfl
  | .eq _ _, _ => Iff.rfl
  | .top, _ => Iff.rfl
  | .not φ, ρ => not_congr (M.shadow_eval φ ρ)
  | .and φ ψ, ρ => and_congr (M.shadow_eval φ ρ) (M.shadow_eval ψ ρ)
  | .or φ ψ, ρ => or_congr (M.shadow_eval φ ρ) (M.shadow_eval ψ ρ)
  | .imp φ ψ, ρ => imp_congr (M.shadow_eval φ ρ) (M.shadow_eval ψ ρ)
  | .quant d n C Q, ρ =>
    det_bridge (M.emb n) d (fun x => M.shadow_eval C (push x ρ)) (fun x => M.shadow_eval Q (push x ρ))

theorem PCtx.lift_eval (M : PCtx Noun Verb Rel Name) :
    ∀ (φ : CForm Noun Verb Rel Name) (ρ : Nat → M.A), M.lift.eval φ ρ ↔ M.eval φ ρ
  | .verb _ _, _ => Iff.rfl
  | .rel _ _ _, _ => Iff.rfl
  | .isA n t, ρ =>
    show (∃ y : {x // M.noun n x}, y.val = t.eval M.name ρ) ↔ M.noun n (t.eval M.name ρ) from
      ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  | .eq _ _, _ => Iff.rfl
  | .top, _ => Iff.rfl
  | .not φ, ρ => not_congr (M.lift_eval φ ρ)
  | .and φ ψ, ρ => and_congr (M.lift_eval φ ρ) (M.lift_eval ψ ρ)
  | .or φ ψ, ρ => or_congr (M.lift_eval φ ρ) (M.lift_eval ψ ρ)
  | .imp φ ψ, ρ => imp_congr (M.lift_eval φ ρ) (M.lift_eval ψ ρ)
  | .quant d n C Q, ρ =>
    (det_bridge (fun y : {x // M.noun n x} => y.val) d (fun x => M.lift_eval C (push x ρ))
      (fun x => M.lift_eval Q (push x ρ))).trans
    (detPr_congr d (fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩)
      (fun _ => Iff.rfl) (fun _ => Iff.rfl))

/-- `Γ` derives `φ` with nouns as types: in every typed context. -/
def ProvT (Γ : List (CForm Noun Verb Rel Name)) (φ : CForm Noun Verb Rel Name) : Prop :=
  ∀ (M : TCtx Noun Verb Rel Name) (ρ : Nat → M.A), (∀ ψ, ψ ∈ Γ → M.eval ψ ρ) → M.eval φ ρ

/-- `Γ` derives `φ` with nouns as predicates: in every predicate context. -/
def ProvP (Γ : List (CForm Noun Verb Rel Name)) (φ : CForm Noun Verb Rel Name) : Prop :=
  ∀ (M : PCtx Noun Verb Rel Name) (ρ : Nat → M.A), (∀ ψ, ψ ∈ Γ → M.eval ψ ρ) → M.eval φ ρ

/-- **The equivalence, intuitionistically.** Nouns as types and nouns as
predicates derive the same entailments of the fragment, over arbitrary
contexts, with no classical reasoning. -/
theorem provT_iff (Γ : List (CForm Noun Verb Rel Name)) (φ : CForm Noun Verb Rel Name) :
    ProvT Γ φ ↔ ProvP Γ φ :=
  ⟨fun h M ρ hΓ =>
    (M.lift_eval φ ρ).mp (h M.lift ρ fun ψ hψ => (M.lift_eval ψ ρ).mpr (hΓ ψ hψ)),
   fun h M ρ hΓ =>
    (M.shadow_eval φ ρ).mpr (h M.shadow ρ fun ψ hψ => (M.shadow_eval ψ ρ).mp (hΓ ψ hψ))⟩

end FraCaS.Encodings.Constructive

#print axioms FraCaS.Encodings.Constructive.provT_iff
