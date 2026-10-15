import EndToEnd.Encodings.Characterization

/-!
# The equivalence and the characterization, with two-place verbs

`Equivalence.lean`'s fragment has one-place verbs only: a quantifier's
restrictor and scope are predicates of individuals, so "every student
read some book" is not in it. This file extends the fragment with
variables, two-place verbs (relations), identity, and quantifiers that
bind a variable in a restrictor and a scope that are themselves
formulas. Quantifiers nest, so "every student read some book" and "some
book was read by every student" are two formulas.

All of the earlier results carry over:

- `validR_iff`: with injective embeddings, nouns as types and nouns as
  predicates validate the same entailments (as `valid_iff`).
- `validRI_iff`: counting individuals, they validate the same
  entailments with no condition (as `validI_iff`).
- `agreeR_iff_kernel`: nouns counting by identity criteria agree with
  nouns as predicates, under every interpretation of the verbs and
  relations, exactly when each criterion is the individuals' identity
  (as `CModel.agree_iff_kernel`).
- `Formula.toForm`: the old fragment is a part of the new one, with the
  same truth values in every encoding (`Formula.toForm_eval`).

The proofs need nothing beyond the determiner transfer lemmas, because
a quantifier over a noun's type binds its variable to an individual
(the element's image), and the transfer lemmas hold for any restrictor
and scope over the individuals. Each encoding is an interpretation
(`Interp`) of the quantifiers, nouns, verbs, relations and names, and
one evaluation function (`Form.eval`) serves them all. Two
interpretations that agree pointwise give every formula the same truth
value (`Interp.Agree.eval`).

Variables are de Bruijn indices: `var 0` is the variable of the nearest
enclosing quantifier.
-/

namespace FraCaS.Encodings.Relational
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed
open FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence

/-! ## The fragment -/

/-- A variable or a name. -/
inductive Term (Name : Type) where
  | var : Nat → Term Name
  | name : Name → Term Name

inductive Form (Noun Verb Rel Name : Type) where
  /-- a one-place verb or adjective -/
  | verb : Verb → Term Name → Form Noun Verb Rel Name
  /-- a two-place verb: `rel r t u` is "`t` `r`s `u`" -/
  | rel : Rel → Term Name → Term Name → Form Noun Verb Rel Name
  /-- "`t` is an `n`" -/
  | isA : Noun → Term Name → Form Noun Verb Rel Name
  /-- "`t` is `u`": one individual -/
  | eq : Term Name → Term Name → Form Noun Verb Rel Name
  | top : Form Noun Verb Rel Name
  | not : Form Noun Verb Rel Name → Form Noun Verb Rel Name
  | and : Form Noun Verb Rel Name → Form Noun Verb Rel Name → Form Noun Verb Rel Name
  | or : Form Noun Verb Rel Name → Form Noun Verb Rel Name → Form Noun Verb Rel Name
  | imp : Form Noun Verb Rel Name → Form Noun Verb Rel Name → Form Noun Verb Rel Name
  /-- `d` noun `n` that `C` are `Q`: binds `var 0` in `C` and `Q` -/
  | quant : Det → Noun → Form Noun Verb Rel Name → Form Noun Verb Rel Name →
      Form Noun Verb Rel Name
  /-- more noun `n` that `C` are `Q` than are `S`: binds `var 0` in each -/
  | more : Noun → Form Noun Verb Rel Name → Form Noun Verb Rel Name →
      Form Noun Verb Rel Name → Form Noun Verb Rel Name

variable {Noun Verb Rel Name : Type}

/-! ## Interpretations and evaluation -/

/-- What an encoding gives the fragment over individuals `A`: a meaning
for each determiner over each noun (applied to a restrictor and a
scope), for "more", and for the nouns, verbs, relations and names. -/
structure Interp (Noun Verb Rel Name A : Type) where
  q : Det → Noun → (A → Prop) → (A → Prop) → Prop
  more : Noun → (A → Prop) → (A → Prop) → (A → Prop) → Prop
  isA : Noun → A → Prop
  verb : Verb → A → Prop
  rel : Rel → A → A → Prop
  name : Name → A

/-- An assignment with `x` bound to the newest variable. -/
def push {A : Type} (x : A) (ρ : Nat → A) : Nat → A
  | 0 => x
  | k + 1 => ρ k

def Term.eval {A : Type} (name : Name → A) (ρ : Nat → A) : Term Name → A
  | .var k => ρ k
  | .name c => name c

def Form.eval {A : Type} (I : Interp Noun Verb Rel Name A) :
    Form Noun Verb Rel Name → (Nat → A) → Prop
  | .verb v t, ρ => I.verb v (t.eval I.name ρ)
  | .rel r t u, ρ => I.rel r (t.eval I.name ρ) (u.eval I.name ρ)
  | .isA n t, ρ => I.isA n (t.eval I.name ρ)
  | .eq t u, ρ => t.eval I.name ρ = u.eval I.name ρ
  | .top, _ => True
  | .not φ, ρ => ¬ Form.eval I φ ρ
  | .and φ ψ, ρ => Form.eval I φ ρ ∧ Form.eval I ψ ρ
  | .or φ ψ, ρ => Form.eval I φ ρ ∨ Form.eval I ψ ρ
  | .imp φ ψ, ρ => Form.eval I φ ρ → Form.eval I ψ ρ
  | .quant d n C Q, ρ =>
    I.q d n (fun x => Form.eval I C (push x ρ)) (fun x => Form.eval I Q (push x ρ))
  | .more n C Q S, ρ =>
    I.more n (fun x => Form.eval I C (push x ρ)) (fun x => Form.eval I Q (push x ρ))
      (fun x => Form.eval I S (push x ρ))

/-- Two interpretations over the same individuals that agree pointwise. -/
structure Interp.Agree {A : Type} (I J : Interp Noun Verb Rel Name A) : Prop where
  q : ∀ d n C Q, I.q d n C Q ↔ J.q d n C Q
  more : ∀ n C Q S, I.more n C Q S ↔ J.more n C Q S
  isA : ∀ n x, I.isA n x ↔ J.isA n x
  verb : ∀ v x, I.verb v x ↔ J.verb v x
  rel : ∀ r x y, I.rel r x y ↔ J.rel r x y
  name : ∀ c, I.name c = J.name c

section
variable {A : Type} {I J K : Interp Noun Verb Rel Name A}

theorem Interp.Agree.symm (h : I.Agree J) : J.Agree I where
  q d n C Q := (h.q d n C Q).symm
  more n C Q S := (h.more n C Q S).symm
  isA n x := (h.isA n x).symm
  verb v x := (h.verb v x).symm
  rel r x y := (h.rel r x y).symm
  name c := (h.name c).symm

theorem Interp.Agree.trans (h : I.Agree J) (h' : J.Agree K) : I.Agree K where
  q d n C Q := (h.q d n C Q).trans (h'.q d n C Q)
  more n C Q S := (h.more n C Q S).trans (h'.more n C Q S)
  isA n x := (h.isA n x).trans (h'.isA n x)
  verb v x := (h.verb v x).trans (h'.verb v x)
  rel r x y := (h.rel r x y).trans (h'.rel r x y)
  name c := (h.name c).trans (h'.name c)

theorem Interp.Agree.term (h : I.Agree J) (ρ : Nat → A) :
    ∀ t : Term Name, t.eval I.name ρ = t.eval J.name ρ
  | .var _ => rfl
  | .name c => h.name c

/-- Interpretations that agree pointwise give every formula the same
truth value, under every assignment. -/
theorem Interp.Agree.eval (h : I.Agree J) :
    ∀ (φ : Form Noun Verb Rel Name) (ρ : Nat → A), Form.eval I φ ρ ↔ Form.eval J φ ρ
  | .verb v t, ρ => by
    show I.verb v (t.eval I.name ρ) ↔ J.verb v (t.eval J.name ρ)
    rw [h.term ρ t]
    exact h.verb _ _
  | .rel r t u, ρ => by
    show I.rel r (t.eval I.name ρ) (u.eval I.name ρ) ↔ J.rel r (t.eval J.name ρ) (u.eval J.name ρ)
    rw [h.term ρ t, h.term ρ u]
    exact h.rel _ _ _
  | .isA n t, ρ => by
    show I.isA n (t.eval I.name ρ) ↔ J.isA n (t.eval J.name ρ)
    rw [h.term ρ t]
    exact h.isA _ _
  | .eq t u, ρ => by
    show t.eval I.name ρ = u.eval I.name ρ ↔ t.eval J.name ρ = u.eval J.name ρ
    rw [h.term ρ t, h.term ρ u]
  | .top, _ => Iff.rfl
  | .not φ, ρ => not_congr (h.eval φ ρ)
  | .and φ ψ, ρ => and_congr (h.eval φ ρ) (h.eval ψ ρ)
  | .or φ ψ, ρ => or_congr (h.eval φ ρ) (h.eval ψ ρ)
  | .imp φ ψ, ρ => imp_congr (h.eval φ ρ) (h.eval ψ ρ)
  | .quant d n C Q, ρ => by
    show I.q d n (fun x => Form.eval I C (push x ρ)) (fun x => Form.eval I Q (push x ρ)) ↔
      J.q d n (fun x => Form.eval J C (push x ρ)) (fun x => Form.eval J Q (push x ρ))
    have hC : (fun x => Form.eval I C (push x ρ)) = (fun x => Form.eval J C (push x ρ)) :=
      funext fun x => propext (h.eval C (push x ρ))
    have hQ : (fun x => Form.eval I Q (push x ρ)) = (fun x => Form.eval J Q (push x ρ)) :=
      funext fun x => propext (h.eval Q (push x ρ))
    rw [hC, hQ]
    exact h.q _ _ _ _
  | .more n C Q S, ρ => by
    show I.more n (fun x => Form.eval I C (push x ρ)) (fun x => Form.eval I Q (push x ρ))
        (fun x => Form.eval I S (push x ρ)) ↔
      J.more n (fun x => Form.eval J C (push x ρ)) (fun x => Form.eval J Q (push x ρ))
        (fun x => Form.eval J S (push x ρ))
    have hC : (fun x => Form.eval I C (push x ρ)) = (fun x => Form.eval J C (push x ρ)) :=
      funext fun x => propext (h.eval C (push x ρ))
    have hQ : (fun x => Form.eval I Q (push x ρ)) = (fun x => Form.eval J Q (push x ρ)) :=
      funext fun x => propext (h.eval Q (push x ρ))
    have hS : (fun x => Form.eval I S (push x ρ)) = (fun x => Form.eval J S (push x ρ)) :=
      funext fun x => propext (h.eval S (push x ρ))
    rw [hC, hQ, hS]
    exact h.more _ _ _ _

end

/-! ## The encodings

The models are `Equivalence.lean`'s, with the relations interpreted
separately, so `shadow` and `lift` are reused unchanged. -/

/-- Nouns as predicates. -/
noncomputable def pI (M : PModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) :
    Interp Noun Verb Rel Name M.A where
  q d n C Q := detP d (fun x => M.noun n x ∧ C x) Q
  more n C Q S := moreP (fun x => M.noun n x ∧ C x) Q S
  isA := M.noun
  verb := M.verb
  rel := rel
  name := M.name

/-- Nouns as types, counting the elements of a noun's type. -/
noncomputable def tI (M : TModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) :
    Interp Noun Verb Rel Name M.A where
  q d n C Q := detT (M.emb n) d C Q
  more n C Q S := MoreT (M.emb n) C Q S
  isA := M.isA
  verb := M.verb
  rel := rel
  name := M.name

/-- Nouns as types, counting individuals (`Counting.lean`). -/
noncomputable def tII (M : TModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) :
    Interp Noun Verb Rel Name M.A where
  q d n C Q := detI (M.emb n) d C Q
  more n C Q S := MoreI (M.emb n) C Q S
  isA := M.isA
  verb := M.verb
  rel := rel
  name := M.name

/-- Nouns as types, each counting by its identity criterion
(`Characterization.lean`). -/
noncomputable def cI (M : CModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) :
    Interp Noun Verb Rel Name M.A where
  q d n C Q := detBy (M.countC n) (M.emb n) d C Q
  more n C Q S := M.countC n (fun x => C x ∧ Q x) > M.countC n (fun x => C x ∧ S x)
  isA := M.toTModel.isA
  verb := M.verb
  rel := rel
  name := M.name

/-! ## Agreement between the encodings -/

/-- Counting individuals, a typed model agrees with its predicate
reading: no injectivity needed. -/
theorem tII_agree_shadow (M : TModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) :
    (tII M rel).Agree (pI M.shadow rel) where
  q d n C Q := det_transferI (M.emb n) d C Q
  more n C Q S := more_transferI (M.emb n) C Q S
  isA _ _ := Iff.rfl
  verb _ _ := Iff.rfl
  rel _ _ _ := Iff.rfl
  name _ := rfl

/-- Counting elements, a typed model with injective embeddings agrees
with its predicate reading. -/
theorem tI_agree_shadow (M : TModel Noun Verb Name) (hinj : ∀ n, Function.Injective (M.emb n))
    (rel : Rel → M.A → M.A → Prop) : (tI M rel).Agree (pI M.shadow rel) where
  q d n C Q := det_transfer (M.emb n) (hinj n) d C Q
  more n C Q S := more_transfer (M.emb n) (hinj n) C Q S
  isA _ _ := Iff.rfl
  verb _ _ := Iff.rfl
  rel _ _ _ := Iff.rfl
  name _ := rfl

/-- Being the image of an element of a noun's subtype is being of the
noun. -/
theorem lift_isA (M : PModel Noun Verb Name) (n : Noun) (x : M.A) :
    M.lift.isA n x ↔ M.noun n x :=
  ⟨by rintro ⟨y, rfl⟩; exact y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- A predicate model agrees with the predicate reading of its lift. -/
theorem pI_agree_lift_shadow (M : PModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) :
    (pI M rel).Agree (pI M.lift.shadow rel) where
  q d n C Q := by
    have e : (fun x => M.lift.isA n x ∧ C x) = (fun x => M.noun n x ∧ C x) :=
      funext fun x => propext (and_congr (lift_isA M n x) Iff.rfl)
    exact iff_of_eq (congrArg (fun R => detP d R Q) e.symm)
  more n C Q S := by
    have e : (fun x => M.lift.isA n x ∧ C x) = (fun x => M.noun n x ∧ C x) :=
      funext fun x => propext (and_congr (lift_isA M n x) Iff.rfl)
    exact iff_of_eq (congrArg (fun R => moreP R Q S) e.symm)
  isA n x := (lift_isA M n x).symm
  verb _ _ := Iff.rfl
  rel _ _ _ := Iff.rfl
  name _ := rfl

/-! ## Validity -/

/-- `Γ` entails `φ` with nouns as predicates: in every model, under every
interpretation of the relations and every assignment. -/
def PValidR (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) : Prop :=
  ∀ (M : PModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) (ρ : Nat → M.A),
    (∀ ψ ∈ Γ, Form.eval (pI M rel) ψ ρ) → Form.eval (pI M rel) φ ρ

/-- `Γ` entails `φ` with nouns as types, counting elements, over
injective embeddings. -/
def TValidR (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) : Prop :=
  ∀ (M : TModel Noun Verb Name), (∀ n, Function.Injective (M.emb n)) →
    ∀ (rel : Rel → M.A → M.A → Prop) (ρ : Nat → M.A),
    (∀ ψ ∈ Γ, Form.eval (tI M rel) ψ ρ) → Form.eval (tI M rel) φ ρ

/-- `Γ` entails `φ` with nouns as types, counting individuals, over all
typed models. -/
def TValidRI (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) : Prop :=
  ∀ (M : TModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) (ρ : Nat → M.A),
    (∀ ψ ∈ Γ, Form.eval (tII M rel) ψ ρ) → Form.eval (tII M rel) φ ρ

/-- **The equivalence with two-place verbs, counting individuals.** -/
theorem validRI_iff (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) :
    TValidRI Γ φ ↔ PValidR Γ φ := by
  constructor
  · intro h M rel ρ hΓ
    have key := ((pI_agree_lift_shadow M rel).trans (tII_agree_shadow M.lift rel).symm).eval
    exact (key φ ρ).mpr (h M.lift rel ρ fun ψ hψ => (key ψ ρ).mp (hΓ ψ hψ))
  · intro h M rel ρ hΓ
    have key := (tII_agree_shadow M rel).eval
    exact (key φ ρ).mpr (h M.shadow rel ρ fun ψ hψ => (key ψ ρ).mp (hΓ ψ hψ))

/-- **The equivalence with two-place verbs, injective embeddings.** -/
theorem validR_iff (Γ : List (Form Noun Verb Rel Name)) (φ : Form Noun Verb Rel Name) :
    TValidR Γ φ ↔ PValidR Γ φ := by
  constructor
  · intro h M rel ρ hΓ
    have key := ((pI_agree_lift_shadow M rel).trans
      (tI_agree_shadow M.lift M.lift_injective rel).symm).eval
    exact (key φ ρ).mpr (h M.lift M.lift_injective rel ρ fun ψ hψ => (key ψ ρ).mp (hΓ ψ hψ))
  · intro h M hinj rel ρ hΓ
    have key := (tI_agree_shadow M hinj rel).eval
    exact (key φ ρ).mpr (h M.shadow rel ρ fun ψ hψ => (key ψ ρ).mp (hΓ ψ hψ))

/-! ## The old fragment inside the new one -/

/-- A predicate, said of a term. -/
def Pred.toForm : Pred Noun Verb → Term Name → Form Noun Verb Rel Name
  | .verb v, t => .verb v t
  | .isA n, t => .isA n t
  | .top, _ => .top
  | .and p q, t => .and (Pred.toForm p t) (Pred.toForm q t)
  | .or p q, t => .or (Pred.toForm p t) (Pred.toForm q t)
  | .not p, t => .not (Pred.toForm p t)

def Formula.toForm : Formula Noun Verb Name → Form Noun Verb Rel Name
  | .quant d n C Q => .quant d n (Pred.toForm C (.var 0)) (Pred.toForm Q (.var 0))
  | .more n C Q S =>
    .more n (Pred.toForm C (.var 0)) (Pred.toForm Q (.var 0)) (Pred.toForm S (.var 0))
  | .holds P c => Pred.toForm P (.name c)
  | .not φ => .not (Formula.toForm φ)
  | .and φ ψ => .and (Formula.toForm φ) (Formula.toForm ψ)
  | .or φ ψ => .or (Formula.toForm φ) (Formula.toForm ψ)
  | .imp φ ψ => .imp (Formula.toForm φ) (Formula.toForm ψ)

/-- The old fragment's formulas, read through an interpretation. -/
def Interp.satF {A : Type} (I : Interp Noun Verb Rel Name A) : Formula Noun Verb Name → Prop
  | .quant d n C Q => I.q d n (C.eval I.isA I.verb) (Q.eval I.isA I.verb)
  | .more n C Q S => I.more n (C.eval I.isA I.verb) (Q.eval I.isA I.verb) (S.eval I.isA I.verb)
  | .holds P c => P.eval I.isA I.verb (I.name c)
  | .not φ => ¬ I.satF φ
  | .and φ ψ => I.satF φ ∧ I.satF ψ
  | .or φ ψ => I.satF φ ∨ I.satF ψ
  | .imp φ ψ => I.satF φ → I.satF ψ

theorem Pred.toForm_eval {A : Type} (I : Interp Noun Verb Rel Name A) (ρ : Nat → A) :
    ∀ (P : Pred Noun Verb) (t : Term Name),
      Form.eval I (Pred.toForm P t) ρ ↔ P.eval I.isA I.verb (t.eval I.name ρ)
  | .verb _, _ => Iff.rfl
  | .isA _, _ => Iff.rfl
  | .top, _ => Iff.rfl
  | .and p q, t => and_congr (Pred.toForm_eval I ρ p t) (Pred.toForm_eval I ρ q t)
  | .or p q, t => or_congr (Pred.toForm_eval I ρ p t) (Pred.toForm_eval I ρ q t)
  | .not p, t => not_congr (Pred.toForm_eval I ρ p t)

/-- The old fragment's formulas mean in the new fragment what they meant
in the old, in every encoding. -/
theorem Formula.toForm_eval {A : Type} (I : Interp Noun Verb Rel Name A) (ρ : Nat → A) :
    ∀ φ : Formula Noun Verb Name, Form.eval I (Formula.toForm φ) ρ ↔ I.satF φ
  | .quant d n C Q => by
    show I.q d n (fun x => Form.eval I (Pred.toForm C (.var 0)) (push x ρ))
        (fun x => Form.eval I (Pred.toForm Q (.var 0)) (push x ρ)) ↔
      I.q d n (C.eval I.isA I.verb) (Q.eval I.isA I.verb)
    have hC : (fun x => Form.eval I (Pred.toForm C (.var 0)) (push x ρ)) = C.eval I.isA I.verb :=
      funext fun x => propext (Pred.toForm_eval I (push x ρ) C (.var 0))
    have hQ : (fun x => Form.eval I (Pred.toForm Q (.var 0)) (push x ρ)) = Q.eval I.isA I.verb :=
      funext fun x => propext (Pred.toForm_eval I (push x ρ) Q (.var 0))
    rw [hC, hQ]
  | .more n C Q S => by
    show I.more n (fun x => Form.eval I (Pred.toForm C (.var 0)) (push x ρ))
        (fun x => Form.eval I (Pred.toForm Q (.var 0)) (push x ρ))
        (fun x => Form.eval I (Pred.toForm S (.var 0)) (push x ρ)) ↔
      I.more n (C.eval I.isA I.verb) (Q.eval I.isA I.verb) (S.eval I.isA I.verb)
    have hC : (fun x => Form.eval I (Pred.toForm C (.var 0)) (push x ρ)) = C.eval I.isA I.verb :=
      funext fun x => propext (Pred.toForm_eval I (push x ρ) C (.var 0))
    have hQ : (fun x => Form.eval I (Pred.toForm Q (.var 0)) (push x ρ)) = Q.eval I.isA I.verb :=
      funext fun x => propext (Pred.toForm_eval I (push x ρ) Q (.var 0))
    have hS : (fun x => Form.eval I (Pred.toForm S (.var 0)) (push x ρ)) = S.eval I.isA I.verb :=
      funext fun x => propext (Pred.toForm_eval I (push x ρ) S (.var 0))
    rw [hC, hQ, hS]
  | .holds P c => Pred.toForm_eval I ρ P (.name c)
  | .not φ => not_congr (Formula.toForm_eval I ρ φ)
  | .and φ ψ => and_congr (Formula.toForm_eval I ρ φ) (Formula.toForm_eval I ρ ψ)
  | .or φ ψ => or_congr (Formula.toForm_eval I ρ φ) (Formula.toForm_eval I ρ ψ)
  | .imp φ ψ => imp_congr (Formula.toForm_eval I ρ φ) (Formula.toForm_eval I ρ ψ)

theorem pI_satF (M : PModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) :
    ∀ φ : Formula Noun Verb Name, (pI M rel).satF φ ↔ M.sat φ
  | .quant _ _ _ _ => Iff.rfl
  | .more _ _ _ _ => Iff.rfl
  | .holds _ _ => Iff.rfl
  | .not φ => not_congr (pI_satF M rel φ)
  | .and φ ψ => and_congr (pI_satF M rel φ) (pI_satF M rel ψ)
  | .or φ ψ => or_congr (pI_satF M rel φ) (pI_satF M rel ψ)
  | .imp φ ψ => imp_congr (pI_satF M rel φ) (pI_satF M rel ψ)

theorem cI_satF (M : CModel Noun Verb Name) (rel : Rel → M.A → M.A → Prop) :
    ∀ φ : Formula Noun Verb Name, (cI M rel).satF φ ↔ M.satC φ
  | .quant _ _ _ _ => Iff.rfl
  | .more _ _ _ _ => Iff.rfl
  | .holds _ _ => Iff.rfl
  | .not φ => not_congr (cI_satF M rel φ)
  | .and φ ψ => and_congr (cI_satF M rel φ) (cI_satF M rel ψ)
  | .or φ ψ => or_congr (cI_satF M rel φ) (cI_satF M rel ψ)
  | .imp φ ψ => imp_congr (cI_satF M rel φ) (cI_satF M rel ψ)

/-! ## The characterization with two-place verbs -/

/-- A criterion that identifies exactly the elements that are one
individual makes the criterion encoding agree with counting
individuals. -/
theorem cI_agree_of_kernel (M : CModel Noun Verb Name)
    (hk : ∀ n (y y' : M.T n), M.crit n y = M.crit n y' ↔ M.emb n y = M.emb n y')
    (rel : Rel → M.A → M.A → Prop) : (cI M rel).Agree (tII M.toTModel rel) where
  q d n C Q := by
    have hc : M.countC n = countI (M.emb n) := funext (M.counts_eq_of_kernel hk n)
    show detBy (M.countC n) (M.emb n) d C Q ↔ detI (M.emb n) d C Q
    rw [hc]
    exact (detI_iff_detBy _ _ _ _).symm
  more n C Q S := by
    show M.countC n _ > M.countC n _ ↔ MoreI (M.emb n) C Q S
    rw [M.counts_eq_of_kernel hk n, M.counts_eq_of_kernel hk n]
    exact Iff.rfl
  isA _ _ := Iff.rfl
  verb _ _ := Iff.rfl
  rel _ _ _ := Iff.rfl
  name _ := rfl

/-- **The characterization, with two-place verbs.** For fixed nouns,
types, embeddings and criteria, the criterion encoding and nouns as
predicates agree on every formula, under every interpretation of the
verbs and relations and every assignment, exactly when each noun's
criterion is the individuals' identity. Necessity reduces to the
one-place case through `Formula.toForm`. -/
theorem agreeR_iff_kernel (M : CModel Noun Verb Name) (v : Verb) :
    (∀ (verb : Verb → M.A → Prop) (rel : Rel → M.A → M.A → Prop)
      (φ : Form Noun Verb Rel Name) (ρ : Nat → M.A),
      Form.eval (cI (M.withVerb verb) rel) φ ρ ↔
        Form.eval (pI (M.withVerb verb).toTModel.shadow rel) φ ρ) ↔
    ∀ n (y y' : M.T n), M.crit n y = M.crit n y' ↔ M.emb n y = M.emb n y' := by
  constructor
  · intro h n y y'
    refine M.kernel_of_agree v (fun verb φ => ?_) n y y'
    have key := h verb (fun _ _ _ => False) (Formula.toForm φ) (fun _ => M.emb n y)
    have e1 := (Formula.toForm_eval (cI (M.withVerb verb) (fun _ _ _ => False))
      (fun _ => M.emb n y) φ).trans (cI_satF (M.withVerb verb) (fun _ _ _ => False) φ)
    have e2 := (Formula.toForm_eval (pI (M.withVerb verb).toTModel.shadow (fun _ _ _ => False))
      (fun _ => M.emb n y) φ).trans (pI_satF (M.withVerb verb).toTModel.shadow (fun _ _ _ => False) φ)
    exact e1.symm.trans (key.trans e2)
  · intro hk verb rel φ ρ
    exact ((cI_agree_of_kernel (M.withVerb verb) hk rel).trans
      (tII_agree_shadow (M.withVerb verb).toTModel rel)).eval φ ρ

/-! ## An example: scope

"Some book was read by every student" entails "every student read some
book", and not conversely. The entailment is proved with nouns as
predicates and transferred to nouns as types by `validRI_iff`. -/

/-- "Every student read some book" (the object taking narrow scope). -/
def everyReadSome (student book : Noun) (read : Rel) : Form Noun Verb Rel Name :=
  .quant .every student .top (.quant .some book .top (.rel read (.var 1) (.var 0)))

/-- "Some book was read by every student" (the object taking wide scope). -/
def someReadByEvery (student book : Noun) (read : Rel) : Form Noun Verb Rel Name :=
  .quant .some book .top (.quant .every student .top (.rel read (.var 0) (.var 1)))

theorem pvalid_scope (student book : Noun) (read : Rel) :
    PValidR (Verb := Verb) (Name := Name) [someReadByEvery student book read]
      (everyReadSome student book read) := by
  intro M rel ρ hΓ
  have h := hΓ _ (List.mem_singleton_self _)
  obtain ⟨y, ⟨hb, -⟩, hy⟩ := h
  intro x hx
  exact Exists.intro y ⟨⟨hb, trivial⟩, hy x hx⟩

theorem tvalid_scope (student book : Noun) (read : Rel) :
    TValidRI (Verb := Verb) (Name := Name) [someReadByEvery student book read]
      (everyReadSome student book read) :=
  (validRI_iff _ _).mpr (pvalid_scope student book read)

end FraCaS.Encodings.Relational
