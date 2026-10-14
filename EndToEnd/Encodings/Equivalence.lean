import EndToEnd.Encodings.Typed

/-!
# Nouns as types and nouns as predicates validate the same entailments

`Typed.lean` shows determiner by determiner that a quantifier over a
noun's type says what the same quantifier says over the individuals that
are of that noun, when the noun's embedding is injective. This file
states the consequence for whole entailments, over a fragment closed
under the connectives:

- **predicates** (`Pred`): verbs and adjectives of individuals, "is an
  N", and their Boolean combinations;
- **formulas** (`Formula`): a determiner (`Det`) over a noun, a
  restrictor and a scope; "more N that R are Q than are S"; a predicate
  of a named individual; and the connectives. A lexical fact relating
  two nouns, "every N is an M", is the formula `every N ⊤ (isA M)`, so
  premises and lexical facts are treated alike.

A formula has two meanings:

- **nouns as predicates** (`PModel`, the corpus's and the pipeline's
  encoding): a noun is a predicate of individuals, and a determiner is
  the corpus's own (`Every`, `AtLeast`, ...), over the noun and the
  restrictor;
- **nouns as types** (`TModel`, the MTT encoding): a noun is a finite
  type with an embedding into the individuals, a determiner ranges over
  the type (`EveryT`, `AtLeastT`, ...), and "is an N" is being the image
  of an element of that type (`IsA`).

`valid_iff`: with injective embeddings, an entailment is valid with
nouns as types exactly when it is valid with nouns as predicates. One
direction reads each typed model as the predicate model of its images
(`TModel.shadow`); the other reads each predicate as the type of its
members (`PModel.lift`).

`not_valid_without_injectivity`: without injectivity the equivalence
fails. An entailment valid with nouns as predicates has a typed
countermodel, in which two elements of a noun's type are one
individual: the individuation question of MTT's counting determiners.

The fragment leaves out the opaque `Many` and `Few` (stated at every
type with nouns as types), anaphora across sentences (stated with
Σ-types in `Section3.lean`), and noun-dependent adjectives
(`Section5.lean`, `MTT/Intensionality.lean`), where the encodings do
differ.
-/

namespace FraCaS.Encodings.Equivalence
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed

/-! ## The fragment -/

/-- What is said of an individual. -/
inductive Pred (Noun Verb : Type) where
  | verb : Verb → Pred Noun Verb
  | isA : Noun → Pred Noun Verb
  | top : Pred Noun Verb
  | and : Pred Noun Verb → Pred Noun Verb → Pred Noun Verb
  | or : Pred Noun Verb → Pred Noun Verb → Pred Noun Verb
  | not : Pred Noun Verb → Pred Noun Verb

/-- The determiners both encodings define. -/
inductive Det where
  | every | some | no | most | both | neither
  | atLeast (k : Nat) | atMost (k : Nat) | exactly (k : Nat)

inductive Formula (Noun Verb Name : Type) where
  /-- `d` noun `n` that `C` are `Q` -/
  | quant : Det → Noun → Pred Noun Verb → Pred Noun Verb → Formula Noun Verb Name
  /-- more noun `n` that `C` are `Q` than are `S` -/
  | more : Noun → Pred Noun Verb → Pred Noun Verb → Pred Noun Verb → Formula Noun Verb Name
  /-- the named individual `c` is `P` -/
  | holds : Pred Noun Verb → Name → Formula Noun Verb Name
  | not : Formula Noun Verb Name → Formula Noun Verb Name
  | and : Formula Noun Verb Name → Formula Noun Verb Name → Formula Noun Verb Name
  | or : Formula Noun Verb Name → Formula Noun Verb Name → Formula Noun Verb Name
  | imp : Formula Noun Verb Name → Formula Noun Verb Name → Formula Noun Verb Name

variable {Noun Verb Name : Type}

/-- A predicate's meaning over individuals `A`, given what each noun and
each verb means there. -/
def Pred.eval {A : Type} (noun : Noun → A → Prop) (verb : Verb → A → Prop) :
    Pred Noun Verb → A → Prop
  | .verb v => verb v
  | .isA n => noun n
  | .top => fun _ => True
  | .and p q => fun x => p.eval noun verb x ∧ q.eval noun verb x
  | .or p q => fun x => p.eval noun verb x ∨ q.eval noun verb x
  | .not p => fun x => ¬ p.eval noun verb x

/-! ## The two encodings of a determiner -/

open Classical in
/-- A determiner over a restrictor `R` and a scope `Q`, as the corpus
states it. -/
noncomputable def detP {A : Type} [Fintype A] : Det → (A → Prop) → (A → Prop) → Prop
  | .every, R, Q => Every R Q
  | .some, R, Q => Some R Q
  | .no, R, Q => No R Q
  | .most, R, Q => Most R Q
  | .both, R, Q => Both R Q
  | .neither, R, Q => Neither R Q
  | .atLeast k, R, Q => AtLeast k R Q
  | .atMost k, R, Q => AtMost k R Q
  | .exactly k, R, Q => Exactly k R Q

open Classical in
/-- "More `R` are `Q` than are `S`", as the pipeline states it. -/
noncomputable def moreP {A : Type} [Fintype A] (R Q S : A → Prop) : Prop := More R Q S

/-- A determiner over the type `N`, embedded by `e`: `C` restricts it
further, `Q` is its scope. -/
noncomputable def detT {N A : Type} [Fintype N] (e : N → A) :
    Det → (A → Prop) → (A → Prop) → Prop
  | .every, C, Q => EveryT e C Q
  | .some, C, Q => SomeT e C Q
  | .no, C, Q => NoT e C Q
  | .most, C, Q => MostT e C Q
  | .both, C, Q => BothT e C Q
  | .neither, C, Q => NeitherT e C Q
  | .atLeast k, C, Q => AtLeastT k e C Q
  | .atMost k, C, Q => AtMostT k e C Q
  | .exactly k, C, Q => ExactlyT k e C Q

/-- Every determiner transfers through an injective embedding:
`Typed.lean`'s lemmas, one per determiner. -/
theorem det_transfer {N A : Type} [Fintype N] [Fintype A] (e : N → A)
    (he : Function.Injective e) (d : Det) (C Q : A → Prop) :
    detT e d C Q ↔ detP d (fun x => IsA e x ∧ C x) Q := by
  cases d with
  | every => simp only [detT, detP]; exact every_t e C Q
  | some => simp only [detT, detP]; exact some_t e C Q
  | no => simp only [detT, detP]; exact no_t e C Q
  | most =>
    simp only [detT, detP]
    convert most_t e he C Q
    all_goals exact Subsingleton.elim _ _
  | both =>
    simp only [detT, detP]
    convert both_t e he C Q
    all_goals exact Subsingleton.elim _ _
  | neither =>
    simp only [detT, detP]
    convert neither_t e he C Q
    all_goals exact Subsingleton.elim _ _
  | atLeast k =>
    simp only [detT, detP]
    convert atLeast_t e he k C Q
    all_goals exact Subsingleton.elim _ _
  | atMost k =>
    simp only [detT, detP]
    convert atMost_t e he k C Q
    all_goals exact Subsingleton.elim _ _
  | exactly k =>
    simp only [detT, detP]
    convert exactly_t e he k C Q
    all_goals exact Subsingleton.elim _ _

theorem more_transfer {N A : Type} [Fintype N] [Fintype A] (e : N → A)
    (he : Function.Injective e) (C Q S : A → Prop) :
    MoreT e C Q S ↔ moreP (fun x => IsA e x ∧ C x) Q S := by
  simp only [moreP]
  convert more_t e he C Q S
  all_goals exact Subsingleton.elim _ _

/-! ## Models -/

/-- Nouns as predicates: a finite domain of individuals, and each noun,
verb and name interpreted there. -/
structure PModel (Noun Verb Name : Type) where
  A : Type
  fin : Fintype A
  noun : Noun → A → Prop
  verb : Verb → A → Prop
  name : Name → A

/-- Nouns as types: each noun is a finite type with an embedding into
the individuals; verbs and names are as before. -/
structure TModel (Noun Verb Name : Type) where
  A : Type
  fin : Fintype A
  T : Noun → Type
  finT : ∀ n, Fintype (T n)
  emb : ∀ n, T n → A
  verb : Verb → A → Prop
  name : Name → A

instance (M : PModel Noun Verb Name) : Fintype M.A := M.fin
instance (M : TModel Noun Verb Name) : Fintype M.A := M.fin
instance (M : TModel Noun Verb Name) (n : Noun) : Fintype (M.T n) := M.finT n

/-- "Is an `n`" in a typed model: the image of an element of `n`'s type. -/
def TModel.isA (M : TModel Noun Verb Name) (n : Noun) : M.A → Prop := IsA (M.emb n)

noncomputable def PModel.sat (M : PModel Noun Verb Name) : Formula Noun Verb Name → Prop
  | .quant d n C Q =>
    detP d (fun x => M.noun n x ∧ C.eval M.noun M.verb x) (Q.eval M.noun M.verb)
  | .more n C Q S =>
    moreP (fun x => M.noun n x ∧ C.eval M.noun M.verb x) (Q.eval M.noun M.verb)
      (S.eval M.noun M.verb)
  | .holds P c => P.eval M.noun M.verb (M.name c)
  | .not φ => ¬ M.sat φ
  | .and φ ψ => M.sat φ ∧ M.sat ψ
  | .or φ ψ => M.sat φ ∨ M.sat ψ
  | .imp φ ψ => M.sat φ → M.sat ψ

noncomputable def TModel.sat (M : TModel Noun Verb Name) : Formula Noun Verb Name → Prop
  | .quant d n C Q => detT (M.emb n) d (C.eval M.isA M.verb) (Q.eval M.isA M.verb)
  | .more n C Q S =>
    MoreT (M.emb n) (C.eval M.isA M.verb) (Q.eval M.isA M.verb) (S.eval M.isA M.verb)
  | .holds P c => P.eval M.isA M.verb (M.name c)
  | .not φ => ¬ M.sat φ
  | .and φ ψ => M.sat φ ∧ M.sat ψ
  | .or φ ψ => M.sat φ ∨ M.sat ψ
  | .imp φ ψ => M.sat φ → M.sat ψ

/-! ## From types to predicates, and back -/

/-- A typed model read with nouns as predicates: each noun is the
predicate of being an image of its type. -/
def TModel.shadow (M : TModel Noun Verb Name) : PModel Noun Verb Name :=
  { A := M.A, fin := M.fin, noun := M.isA, verb := M.verb, name := M.name }

/-- A typed model with injective embeddings and its shadow make the same
formulas true. -/
theorem TModel.sat_iff_shadow (M : TModel Noun Verb Name)
    (hinj : ∀ n, Function.Injective (M.emb n)) :
    ∀ φ : Formula Noun Verb Name, M.sat φ ↔ M.shadow.sat φ
  | .quant d n C Q =>
    det_transfer (M.emb n) (hinj n) d (C.eval M.isA M.verb) (Q.eval M.isA M.verb)
  | .more n C Q S =>
    more_transfer (M.emb n) (hinj n) (C.eval M.isA M.verb) (Q.eval M.isA M.verb)
      (S.eval M.isA M.verb)
  | .holds _ _ => Iff.rfl
  | .not φ => not_congr (M.sat_iff_shadow hinj φ)
  | .and φ ψ => and_congr (M.sat_iff_shadow hinj φ) (M.sat_iff_shadow hinj ψ)
  | .or φ ψ => or_congr (M.sat_iff_shadow hinj φ) (M.sat_iff_shadow hinj ψ)
  | .imp φ ψ => imp_congr (M.sat_iff_shadow hinj φ) (M.sat_iff_shadow hinj ψ)

/-- A predicate model read with nouns as types: each noun is the type of
its members, embedded by inclusion. -/
noncomputable def PModel.lift (M : PModel Noun Verb Name) : TModel Noun Verb Name where
  A := M.A
  fin := M.fin
  T n := {x : M.A // M.noun n x}
  finT n := by classical exact Subtype.fintype _
  emb _ := Subtype.val
  verb := M.verb
  name := M.name

theorem PModel.lift_injective (M : PModel Noun Verb Name) :
    ∀ n, Function.Injective (M.lift.emb n) :=
  fun _ => Subtype.val_injective

/-- Lifting a predicate model and reading it back gives the model again:
being an image of the inclusion of `n`'s members is being an `n`. -/
theorem PModel.lift_shadow (M : PModel Noun Verb Name) : M.lift.shadow = M := by
  obtain ⟨A, fin, noun, verb, name⟩ := M
  show PModel.mk A fin (fun n => IsA (fun y : {x : A // noun n x} => y.val)) verb name =
    PModel.mk A fin noun verb name
  congr 1
  funext n x
  exact propext ⟨fun ⟨y, hy⟩ => by subst hy; exact y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-! ## Validity -/

/-- `Γ` entails `φ` with nouns as predicates: every model of `Γ` is a
model of `φ`. -/
def PValid (Γ : List (Formula Noun Verb Name)) (φ : Formula Noun Verb Name) : Prop :=
  ∀ M : PModel Noun Verb Name, (∀ ψ ∈ Γ, M.sat ψ) → M.sat φ

/-- `Γ` entails `φ` with nouns as types, in every model whose embeddings
are injective (the MInj variant of the comparison). -/
def TValid (Γ : List (Formula Noun Verb Name)) (φ : Formula Noun Verb Name) : Prop :=
  ∀ M : TModel Noun Verb Name, (∀ n, Function.Injective (M.emb n)) →
    (∀ ψ ∈ Γ, M.sat ψ) → M.sat φ

/-- `Γ` entails `φ` with nouns as types, in every model (the M variant). -/
def TValidAny (Γ : List (Formula Noun Verb Name)) (φ : Formula Noun Verb Name) : Prop :=
  ∀ M : TModel Noun Verb Name, (∀ ψ ∈ Γ, M.sat ψ) → M.sat φ

/-- **The equivalence.** With injective embeddings, nouns as types and
nouns as predicates validate exactly the same entailments of the
fragment, lexical facts between nouns included. -/
theorem valid_iff (Γ : List (Formula Noun Verb Name)) (φ : Formula Noun Verb Name) :
    TValid Γ φ ↔ PValid Γ φ := by
  constructor
  · intro h M hΓ
    have key := M.lift.sat_iff_shadow M.lift_injective
    rw [PModel.lift_shadow] at key
    exact (key φ).mp (h M.lift M.lift_injective fun ψ hψ => (key ψ).mpr (hΓ ψ hψ))
  · intro h M hinj hΓ
    have key := M.sat_iff_shadow hinj
    exact (key φ).mpr (h M.shadow fun ψ hψ => (key ψ).mp (hΓ ψ hψ))

/-- Typed validity over all models implies it over injective ones, so by
`valid_iff` it implies validity with nouns as predicates. -/
theorem pvalid_of_validAny {Γ : List (Formula Noun Verb Name)} {φ : Formula Noun Verb Name}
    (h : TValidAny Γ φ) : PValid Γ φ :=
  (valid_iff Γ φ).mp fun M _ hΓ => h M hΓ

/-! ## Without injectivity

Two nouns, `n` (`true`) and `m` (`false`), and one verb `v`: "at least
two n; every n is an m; every n is v; at most one m is v". With nouns as
predicates these are inconsistent, since the two n are two individuals
that are m and v, so they entail anything, here "some n is nothing".
With nouns as types they hold together when the two elements of `n`'s
type are one individual. -/

/-- The premises. -/
def premisesNI : List (Formula Bool Unit Empty) :=
  [.quant (.atLeast 2) true .top .top,
   .quant .every true .top (.isA false),
   .quant .every true .top (.verb ()),
   .quant (.atMost 1) false (.verb ()) .top]

/-- The conclusion: "some n is nothing". -/
def conclusionNI : Formula Bool Unit Empty := .quant .some true .top (.not .top)

theorem pvalid_NI : PValid premisesNI conclusionNI := by
  intro M hΓ
  have h1 := hΓ (.quant (.atLeast 2) true .top .top) (by simp [premisesNI])
  have h2 := hΓ (.quant .every true .top (.isA false)) (by simp [premisesNI])
  have h3 := hΓ (.quant .every true .top (.verb ())) (by simp [premisesNI])
  have h4 := hΓ (.quant (.atMost 1) false (.verb ()) .top) (by simp [premisesNI])
  simp only [PModel.sat, detP, Pred.eval, AtLeast, AtMost, Every, card] at h1 h2 h3 h4
  exfalso
  refine absurd (le_trans h1 (le_trans (Finset.card_le_card fun x hx => ?_) h4)) (by decide)
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, ⟨h2 x hx.2.1, h3 x hx.2.1⟩, trivial⟩

/-- So, by `valid_iff`, the entailment holds with nouns as types too,
in every model whose embeddings are injective. -/
theorem tvalid_NI : TValid premisesNI conclusionNI := (valid_iff _ _).mpr pvalid_NI

/-- The countermodel: the individuals are `true` and `false`; `n`'s type
is `Bool` with both elements the individual `true`; `m`'s type is `Bool`
with each element itself; `v` holds of `true` only. -/
def counterModel : TModel Bool Unit Empty where
  A := Bool
  fin := inferInstance
  T _ := Bool
  finT _ := inferInstance
  emb n y := cond n true y
  verb _ x := x = true
  name c := c.elim

theorem counterModel_not_injective : ¬ Function.Injective (counterModel.emb true) := by
  intro h
  exact absurd (h (a₁ := true) (a₂ := false) rfl) (by decide)

/-- **Without injectivity the equivalence fails.** The entailment is valid
with nouns as predicates, and with nouns as types over injective
embeddings (`tvalid_NI`), but not over all typed models. -/
theorem not_valid_without_injectivity :
    PValid premisesNI conclusionNI ∧ ¬ TValidAny premisesNI conclusionNI := by
  refine ⟨pvalid_NI, fun h => ?_⟩
  have h1 : counterModel.sat (.quant (.atLeast 2) true .top .top) := by
    show cardT (fun _ : Bool => true) (fun _ : Bool => True ∧ True) ≥ 2
    unfold cardT
    exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr ⟨true, by simp, false, by simp, by decide⟩)
  have h2 : counterModel.sat (.quant .every true .top (.isA false)) := by
    show ∀ y : Bool, True → IsA (fun y : Bool => y) true
    exact fun _ _ => ⟨true, rfl⟩
  have h3 : counterModel.sat (.quant .every true .top (.verb ())) := by
    show ∀ y : Bool, True → true = true
    exact fun _ _ => rfl
  have h4 : counterModel.sat (.quant (.atMost 1) false (.verb ()) .top) := by
    show cardT (fun y : Bool => y) (fun x : Bool => x = true ∧ True) ≤ 1
    unfold cardT
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter] at ha hb
    exact ha.2.1.trans hb.2.1.symm
  have hφ : ¬ counterModel.sat conclusionNI := by
    show ¬ ∃ y : Bool, True ∧ ¬ True
    rintro ⟨_, _, h⟩
    exact h trivial
  apply hφ
  apply h counterModel
  intro ψ hψ
  simp only [premisesNI, List.mem_cons, List.mem_nil_iff, or_false] at hψ
  rcases hψ with rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4]

end FraCaS.Encodings.Equivalence
