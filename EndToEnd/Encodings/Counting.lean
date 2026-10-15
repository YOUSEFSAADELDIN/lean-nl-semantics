import EndToEnd.Encodings.Copredication

/-!
# Counting by an identity criterion, for any number

Phase 4 (`Copredication.lean`) states its problems with "two" only. This
file states them for every `n`, and uses the same counting to generalize
the equivalence theorem (`Equivalence.lean`).

1. **Counting by a criterion** (`countBy f P`): how many distinct
   `f`-values the things that are `P` have. Two things count as one when
   `f` does not tell them apart. With an injective `f` it is the corpus's
   `card` (`countBy_of_injective`); at two it is Phase 4's `TwoBy`
   (`countBy_two_iff`); counting the elements of a noun's type by their
   individuals is counting the individuals that are of that noun
   (`countBy_emb`).
2. **I1 and I2 for every `n ≥ 2`.** With nouns as predicates over one
   domain both are valid (`P_I1_valid`, `P_I2_valid`). With dot types
   neither is (`M_I1_not_valid`, `M_I2_not_valid`: `n` copies of one
   text, one volume with `n` texts), and each becomes valid once one
   aspect determines the other (`M_I1_valid_of`, `M_I2_valid_of`). A
   predicate encoding with a stipulated function to a sort of texts
   leaves I1 open too (`P2_I1_not_valid`).
3. **The equivalence without injectivity.** `Equivalence.lean`'s typed
   models count the elements of a noun's type, and match nouns as
   predicates only when each embedding is injective. Here the typed
   models count by the individuals' own identity instead (`countI`):
   two elements of a noun's type that are one individual count once.
   Then nouns as types and nouns as predicates validate exactly the same
   entailments of the fragment, with no condition on the embeddings
   (`validI_iff`). With injective embeddings the two ways of counting
   agree (`TModel.satI_iff_sat`), so `valid_iff` is the special case.

So what separates the encodings in counting is not types as such but
the identity criterion a noun counts by. Counting by the individuals'
own identity, nouns as types say what predicates say. Counting by
another criterion, as "mastered two books" counts texts, they say
something a predicate over one domain of individuals cannot.
-/

namespace FraCaS.Encodings.Counting
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed
open FraCaS.Encodings.Equivalence (card_filter_mono)
open FraCaS.Encodings.Copredication (TwoBy)

/-! ## Counting by a criterion -/

/-- How many distinct `f`-values the `N`s that are `P` have: the number
of `P`s, counted by the identity criterion "same `f`-value". -/
def countBy {N B : Type} [Fintype N] [DecidableEq B] (f : N → B) (P : N → Prop)
    [DecidablePred P] : Nat :=
  ((Finset.univ.filter P).image f).card

section
variable {N B C : Type} [Fintype N] [DecidableEq B]

theorem countBy_mono (f : N → B) {P Q : N → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x → Q x) : countBy f P ≤ countBy f Q := by
  unfold countBy
  exact Finset.card_le_card (Finset.image_subset_image fun x hx =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩)

/-- A coarser criterion counts no more. -/
theorem countBy_comp_le [DecidableEq C] (g : N → B) (h : B → C) (P : N → Prop)
    [DecidablePred P] : countBy (h ∘ g) P ≤ countBy g P := by
  unfold countBy
  rw [← Finset.image_image]
  exact Finset.card_image_le

/-- If `f` factors through `g`, counting by `f` counts no more than
counting by `g`. -/
theorem countBy_le_of_factor [DecidableEq C] (f : N → C) (g : N → B) (h : B → C)
    (hfg : ∀ x, f x = h (g x)) (P : N → Prop) [DecidablePred P] :
    countBy f P ≤ countBy g P := by
  have : f = h ∘ g := funext hfg
  subst this
  exact countBy_comp_le g h P

/-- Counting by an injective criterion is counting elements: the
corpus's `card`. -/
theorem countBy_of_injective (f : N → B) (hf : Function.Injective f) (P : N → Prop)
    [DecidablePred P] : countBy f P = card P := by
  unfold countBy card
  exact Finset.card_image_of_injective _ hf

/-- At two, `countBy` is Phase 4's `TwoBy` (and so `MTT.v`'s `countGe2`). -/
theorem countBy_two_iff (f : N → B) (P : N → Prop) [DecidablePred P] :
    countBy f P ≥ 2 ↔ TwoBy f P := by
  unfold countBy
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨x, y, (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2, hab⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact Finset.one_lt_card.mpr
      ⟨f x, Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩),
        f y, Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩), hxy⟩

/-- Counting the elements of a noun's type by their individuals is
counting the individuals that are of that noun; no injectivity needed. -/
theorem countBy_emb {A : Type} [Fintype A] [DecidableEq A] (e : N → A) (P : A → Prop)
    [DecidablePred fun y => P (e y)] [DecidablePred fun x => IsA e x ∧ P x] :
    countBy e (fun y => P (e y)) = card (fun x => IsA e x ∧ P x) := by
  unfold countBy card
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, hy⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, hy, rfl⟩

end

/-! ## I1 and I2 for every number

"John picked up `n` books. John mastered every book he picked up."
⇒ "John mastered `n` books." (I1), and its mirror image (I2); see
`Copredication.lean`. -/

def P_I1 (n : Nat) : Prop :=
  ∀ {A : Type} [Fintype A] (book pickedUp mastered : A → Prop)
    [DecidablePred fun x => book x ∧ pickedUp x] [DecidablePred fun x => book x ∧ mastered x],
    AtLeast n book pickedUp → (∀ x, book x → pickedUp x → mastered x) → AtLeast n book mastered

def P_I2 (n : Nat) : Prop :=
  ∀ {A : Type} [Fintype A] (book pickedUp mastered : A → Prop)
    [DecidablePred fun x => book x ∧ mastered x] [DecidablePred fun x => book x ∧ pickedUp x],
    AtLeast n book mastered → (∀ x, book x → mastered x → pickedUp x) → AtLeast n book pickedUp

theorem P_I1_valid (n : Nat) : P_I1 n := by
  unfold P_I1
  intro A _ book pickedUp mastered _ _ h1 h2
  exact le_trans h1 (card_filter_mono (by intro x hx; exact ⟨hx.1, h2 x hx.1 hx.2⟩))

theorem P_I2_valid (n : Nat) : P_I2 n := by
  unfold P_I2
  intro A _ book pickedUp mastered _ _ h1 h2
  exact le_trans h1 (card_filter_mono (by intro x hx; exact ⟨hx.1, h2 x hx.1 hx.2⟩))

/-- P with a stipulated function from individuals to a sort of texts,
and "mastered `n` books" counted through it. -/
def P2_I1 (n : Nat) : Prop :=
  ∀ {A : Type} [Fintype A] (Text : Type) [DecidableEq Text] (book pickedUp mastered : A → Prop)
    (textOf : A → Text)
    [DecidablePred fun x => book x ∧ pickedUp x] [DecidablePred fun x => book x ∧ mastered x],
    AtLeast n book pickedUp → (∀ x, book x → pickedUp x → mastered x) →
    countBy textOf (fun x => book x ∧ mastered x) ≥ n

def M_I1 (n : Nat) : Prop :=
  ∀ (Phy Info Book : Type) [Fintype Book] [DecidableEq Phy] [DecidableEq Info]
    (bk : Book → MTT.DotType Phy Info) (pickedUp : Phy → Prop) (mastered : Info → Prop)
    [DecidablePred fun b => pickedUp (bk b).phy] [DecidablePred fun b => mastered (bk b).info],
    countBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy) ≥ n →
    (∀ b, pickedUp (bk b).phy → mastered (bk b).info) →
    countBy (fun b => (bk b).info) (fun b => mastered (bk b).info) ≥ n

def M_I2 (n : Nat) : Prop :=
  ∀ (Phy Info Book : Type) [Fintype Book] [DecidableEq Phy] [DecidableEq Info]
    (bk : Book → MTT.DotType Phy Info) (pickedUp : Phy → Prop) (mastered : Info → Prop)
    [DecidablePred fun b => pickedUp (bk b).phy] [DecidablePred fun b => mastered (bk b).info],
    countBy (fun b => (bk b).info) (fun b => mastered (bk b).info) ≥ n →
    (∀ b, mastered (bk b).info → pickedUp (bk b).phy) →
    countBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy) ≥ n

/-- `n` copies of one text, for any `n ≥ 2`. -/
theorem P2_I1_not_valid (n : Nat) (hn : 2 ≤ n) : ¬ P2_I1 n := by
  intro h
  unfold P2_I1 at h
  have h1 : AtLeast n (fun _ : Fin n => True) (fun _ => True) := by simp [AtLeast, card]
  have h2 := @h (Fin n) _ Unit _ (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => ())
    _ _ h1 (fun _ _ _ => trivial)
  have h3 : countBy (fun _ : Fin n => ())
      (fun x => (fun _ : Fin n => True) x ∧ (fun _ : Fin n => True) x) ≤ 1 := by
    unfold countBy
    exact (Finset.card_le_univ _).trans (by simp)
  exact absurd (le_trans h2 h3) (by omega)

/-- `n` copies of one text, for any `n ≥ 2`. -/
theorem M_I1_not_valid (n : Nat) (hn : 2 ≤ n) : ¬ M_I1 n := by
  intro h
  unfold M_I1 at h
  have h1 : countBy (fun b : Fin n => b) (fun _ => True) ≥ n := by
    rw [countBy_of_injective (fun b : Fin n => b) (fun _ _ hab => hab)]
    simp [card]
  have h2 := h (Fin n) Unit (Fin n) (fun b => ⟨b, ()⟩) (fun _ => True) (fun _ => True)
    h1 (fun _ _ => trivial)
  have h3 : countBy (fun _ : Fin n => ()) (fun _ => True) ≤ 1 := by
    unfold countBy
    exact (Finset.card_le_univ _).trans (by simp)
  exact absurd (le_trans h2 h3) (by omega)

/-- One volume holding `n` texts, for any `n ≥ 2`. -/
theorem M_I2_not_valid (n : Nat) (hn : 2 ≤ n) : ¬ M_I2 n := by
  intro h
  unfold M_I2 at h
  have h1 : countBy (fun b : Fin n => b) (fun _ => True) ≥ n := by
    rw [countBy_of_injective (fun b : Fin n => b) (fun _ _ hab => hab)]
    simp [card]
  have h2 := h Unit (Fin n) (Fin n) (fun b => ⟨(), b⟩) (fun _ => True) (fun _ => True)
    h1 (fun _ _ => trivial)
  have h3 : countBy (fun _ : Fin n => ()) (fun _ => True) ≤ 1 := by
    unfold countBy
    exact (Finset.card_le_univ _).trans (by simp)
  exact absurd (le_trans h2 h3) (by omega)

/-- I1 holds in M, for every `n`, once a book's text determines its
volume. -/
theorem M_I1_valid_of (n : Nat) {Phy Info Book : Type} [Fintype Book] [DecidableEq Phy]
    [DecidableEq Info] (bk : Book → MTT.DotType Phy Info) (volumeOf : Info → Phy)
    (hvol : ∀ b, (bk b).phy = volumeOf (bk b).info) (pickedUp : Phy → Prop)
    (mastered : Info → Prop)
    [DecidablePred fun b => pickedUp (bk b).phy] [DecidablePred fun b => mastered (bk b).info] :
    countBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy) ≥ n →
    (∀ b, pickedUp (bk b).phy → mastered (bk b).info) →
    countBy (fun b => (bk b).info) (fun b => mastered (bk b).info) ≥ n := by
  intro h1 h2
  exact le_trans h1
    ((countBy_le_of_factor (fun b => (bk b).phy) (fun b => (bk b).info) volumeOf hvol
      (fun b => pickedUp (bk b).phy)).trans (countBy_mono _ h2))

/-- I2 holds in M, for every `n`, once a book's volume determines its
text. -/
theorem M_I2_valid_of (n : Nat) {Phy Info Book : Type} [Fintype Book] [DecidableEq Phy]
    [DecidableEq Info] (bk : Book → MTT.DotType Phy Info) (textOf : Phy → Info)
    (htext : ∀ b, (bk b).info = textOf (bk b).phy) (pickedUp : Phy → Prop)
    (mastered : Info → Prop)
    [DecidablePred fun b => pickedUp (bk b).phy] [DecidablePred fun b => mastered (bk b).info] :
    countBy (fun b => (bk b).info) (fun b => mastered (bk b).info) ≥ n →
    (∀ b, mastered (bk b).info → pickedUp (bk b).phy) →
    countBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy) ≥ n := by
  intro h1 h2
  exact le_trans h1
    ((countBy_le_of_factor (fun b => (bk b).info) (fun b => (bk b).phy) textOf htext
      (fun b => mastered (bk b).info)).trans (countBy_mono _ h2))

end FraCaS.Encodings.Counting

/-! ## The equivalence, counting by the individuals -/

namespace FraCaS.Encodings.Equivalence
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed
open FraCaS.Encodings.Counting

section
variable {N A : Type}

open Classical in
/-- How many individuals the elements of `N` that are `P` amount to:
counting by the individuals' own identity. -/
noncomputable def countI [Fintype N] (e : N → A) (P : A → Prop) : Nat :=
  countBy e (fun y => P (e y))

open Classical in
theorem countI_eq [Fintype N] [Fintype A] (e : N → A) (P : A → Prop)
    [DecidablePred fun x => IsA e x ∧ P x] :
    countI e P = card (fun x => IsA e x ∧ P x) :=
  countBy_emb e P

open Classical in
theorem countI_and [Fintype N] [Fintype A] (e : N → A) (C Q : A → Prop) :
    countI e (fun x => C x ∧ Q x) = card (fun x => (IsA e x ∧ C x) ∧ Q x) := by
  rw [countI_eq]
  exact card_iff fun _ => and_assoc.symm

/-! The counting determiners over a noun's type, counting individuals. -/

noncomputable def MostI [Fintype N] (e : N → A) (C Q : A → Prop) : Prop :=
  2 * countI e (fun x => C x ∧ Q x) > countI e C
noncomputable def AtLeastI [Fintype N] (n : Nat) (e : N → A) (C Q : A → Prop) : Prop :=
  countI e (fun x => C x ∧ Q x) ≥ n
noncomputable def AtMostI [Fintype N] (n : Nat) (e : N → A) (C Q : A → Prop) : Prop :=
  countI e (fun x => C x ∧ Q x) ≤ n
noncomputable def ExactlyI [Fintype N] (n : Nat) (e : N → A) (C Q : A → Prop) : Prop :=
  countI e (fun x => C x ∧ Q x) = n
noncomputable def BothI [Fintype N] (e : N → A) (C Q : A → Prop) : Prop :=
  countI e C = 2 ∧ EveryT e C Q
noncomputable def NeitherI [Fintype N] (e : N → A) (C Q : A → Prop) : Prop :=
  countI e C = 2 ∧ NoT e C Q
noncomputable def MoreI [Fintype N] (e : N → A) (C Q R : A → Prop) : Prop :=
  countI e (fun x => C x ∧ Q x) > countI e (fun x => C x ∧ R x)

/-! Each transfers to the corpus's determiner with no condition on `e`. -/

open Classical in
theorem atLeast_i [Fintype N] [Fintype A] (e : N → A) (n : Nat) (C Q : A → Prop) :
    AtLeastI n e C Q ↔ AtLeast n (fun x => IsA e x ∧ C x) Q := by
  have h := countI_and e C Q
  simp only [AtLeastI, AtLeast]
  constructor <;> intro <;> omega

open Classical in
theorem atMost_i [Fintype N] [Fintype A] (e : N → A) (n : Nat) (C Q : A → Prop) :
    AtMostI n e C Q ↔ AtMost n (fun x => IsA e x ∧ C x) Q := by
  have h := countI_and e C Q
  simp only [AtMostI, AtMost]
  constructor <;> intro <;> omega

open Classical in
theorem exactly_i [Fintype N] [Fintype A] (e : N → A) (n : Nat) (C Q : A → Prop) :
    ExactlyI n e C Q ↔ Exactly n (fun x => IsA e x ∧ C x) Q := by
  have h := countI_and e C Q
  simp only [ExactlyI, Exactly]
  constructor <;> intro <;> omega

open Classical in
theorem most_i [Fintype N] [Fintype A] (e : N → A) (C Q : A → Prop) :
    MostI e C Q ↔ Most (fun x => IsA e x ∧ C x) Q := by
  have h := countI_and e C Q
  have h' := countI_eq e C
  simp only [MostI, Most]
  constructor <;> intro <;> omega

open Classical in
theorem more_i [Fintype N] [Fintype A] (e : N → A) (C Q R : A → Prop) :
    MoreI e C Q R ↔ More (fun x => IsA e x ∧ C x) Q R := by
  have h := countI_and e C Q
  have h' := countI_and e C R
  simp only [MoreI, More]
  constructor <;> intro <;> omega

open Classical in
theorem both_i [Fintype N] [Fintype A] (e : N → A) (C Q : A → Prop) :
    BothI e C Q ↔ Both (fun x => IsA e x ∧ C x) Q := by
  have h := countI_eq e C
  simp only [BothI, Both, every_t]
  rw [h]

open Classical in
theorem neither_i [Fintype N] [Fintype A] (e : N → A) (C Q : A → Prop) :
    NeitherI e C Q ↔ Neither (fun x => IsA e x ∧ C x) Q := by
  have h := countI_eq e C
  simp only [NeitherI, Neither, no_t]
  rw [h]

noncomputable def detI [Fintype N] (e : N → A) : Det → (A → Prop) → (A → Prop) → Prop
  | .every, C, Q => EveryT e C Q
  | .some, C, Q => SomeT e C Q
  | .no, C, Q => NoT e C Q
  | .most, C, Q => MostI e C Q
  | .both, C, Q => BothI e C Q
  | .neither, C, Q => NeitherI e C Q
  | .atLeast k, C, Q => AtLeastI k e C Q
  | .atMost k, C, Q => AtMostI k e C Q
  | .exactly k, C, Q => ExactlyI k e C Q

theorem det_transferI [Fintype N] [Fintype A] (e : N → A) (d : Det) (C Q : A → Prop) :
    detI e d C Q ↔ detP d (fun x => IsA e x ∧ C x) Q := by
  cases d with
  | every => simp only [detI, detP]; exact every_t e C Q
  | some => simp only [detI, detP]; exact some_t e C Q
  | no => simp only [detI, detP]; exact no_t e C Q
  | most =>
    simp only [detI, detP]
    convert most_i e C Q
  | both =>
    simp only [detI, detP]
    convert both_i e C Q
  | neither =>
    simp only [detI, detP]
    convert neither_i e C Q
  | atLeast k =>
    simp only [detI, detP]
    convert atLeast_i e k C Q
  | atMost k =>
    simp only [detI, detP]
    convert atMost_i e k C Q
  | exactly k =>
    simp only [detI, detP]
    convert exactly_i e k C Q

theorem more_transferI [Fintype N] [Fintype A] (e : N → A) (C Q S : A → Prop) :
    MoreI e C Q S ↔ moreP (fun x => IsA e x ∧ C x) Q S := by
  simp only [moreP]
  convert more_i e C Q S

end

variable {Noun Verb Name : Type}

/-- A typed model's formulas, with every counting determiner counting
individuals rather than elements of the noun's type. -/
noncomputable def TModel.satI (M : TModel Noun Verb Name) : Formula Noun Verb Name → Prop
  | .quant d n C Q => detI (M.emb n) d (C.eval M.isA M.verb) (Q.eval M.isA M.verb)
  | .more n C Q S =>
    MoreI (M.emb n) (C.eval M.isA M.verb) (Q.eval M.isA M.verb) (S.eval M.isA M.verb)
  | .holds P c => P.eval M.isA M.verb (M.name c)
  | .not φ => ¬ M.satI φ
  | .and φ ψ => M.satI φ ∧ M.satI ψ
  | .or φ ψ => M.satI φ ∨ M.satI ψ
  | .imp φ ψ => M.satI φ → M.satI ψ

/-- Counting individuals, any typed model and its shadow make the same
formulas true: no injectivity needed. -/
theorem TModel.sat_iff_shadowI (M : TModel Noun Verb Name) :
    ∀ φ : Formula Noun Verb Name, M.satI φ ↔ M.shadow.sat φ
  | .quant d n C Q => det_transferI (M.emb n) d (C.eval M.isA M.verb) (Q.eval M.isA M.verb)
  | .more n C Q S =>
    more_transferI (M.emb n) (C.eval M.isA M.verb) (Q.eval M.isA M.verb) (S.eval M.isA M.verb)
  | .holds _ _ => Iff.rfl
  | .not φ => not_congr (M.sat_iff_shadowI φ)
  | .and φ ψ => and_congr (M.sat_iff_shadowI φ) (M.sat_iff_shadowI ψ)
  | .or φ ψ => or_congr (M.sat_iff_shadowI φ) (M.sat_iff_shadowI ψ)
  | .imp φ ψ => imp_congr (M.sat_iff_shadowI φ) (M.sat_iff_shadowI ψ)

/-- With injective embeddings, counting elements and counting
individuals agree. -/
theorem TModel.satI_iff_sat (M : TModel Noun Verb Name)
    (hinj : ∀ n, Function.Injective (M.emb n)) (φ : Formula Noun Verb Name) :
    M.satI φ ↔ M.sat φ :=
  (M.sat_iff_shadowI φ).trans (M.sat_iff_shadow hinj φ).symm

/-- `Γ` entails `φ` with nouns as types, counting individuals, in every
typed model. -/
def TValidI (Γ : List (Formula Noun Verb Name)) (φ : Formula Noun Verb Name) : Prop :=
  ∀ M : TModel Noun Verb Name, (∀ ψ ∈ Γ, M.satI ψ) → M.satI φ

/-- **The equivalence, without injectivity.** Counting by the
individuals' own identity, nouns as types and nouns as predicates
validate exactly the same entailments of the fragment. -/
theorem validI_iff (Γ : List (Formula Noun Verb Name)) (φ : Formula Noun Verb Name) :
    TValidI Γ φ ↔ PValid Γ φ := by
  constructor
  · intro h M hΓ
    have key := M.lift.sat_iff_shadowI
    rw [PModel.lift_shadow] at key
    exact (key φ).mp (h M.lift fun ψ hψ => (key ψ).mpr (hΓ ψ hψ))
  · intro h M hΓ
    have key := M.sat_iff_shadowI
    exact (key φ).mpr (h M.shadow fun ψ hψ => (key ψ).mp (hΓ ψ hψ))

/-- `Equivalence.lean`'s example that fails without injectivity holds
again when the typed models count individuals. -/
theorem tvalidI_NI : TValidI premisesNI conclusionNI := (validI_iff _ _).mpr pvalid_NI

end FraCaS.Encodings.Equivalence
