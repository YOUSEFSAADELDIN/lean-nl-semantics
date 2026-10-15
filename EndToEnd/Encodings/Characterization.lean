import EndToEnd.Encodings.Counting

/-!
# When do nouns as types say what nouns as predicates say? Exactly when they count by individuals

`validI_iff` (`Counting.lean`) shows that typed models whose counting
determiners count individuals validate exactly what predicate models
validate. This file proves the converse. Let each noun count by its own
identity criterion: two elements of its type count as one when the
criterion does not tell them apart. Then the typed semantics agrees
with the predicate semantics under every interpretation of the verbs
**if and only if** each noun's criterion is the individuals' own
identity: two elements count as one exactly when they are one
individual (`CModel.agree_iff_kernel`).

So the two readings of a noun come apart precisely where its identity
criterion differs from individual identity. That happens in two ways,
and one counting sentence detects each:

- **The criterion splits an individual** (Luo's passengers: one person
  on two journeys is two passengers). Then "at most one N is v", with
  `v` true of that individual only, is true with predicates and false
  by the criterion.
- **The criterion merges individuals** (Gotham's books: two copies of
  one text are one book informationally). Then "at least two N are v",
  with `v` true of the two individuals only, is true with predicates
  and false by the criterion.

Injectivity, the condition of `valid_iff`, is the special case where a
noun counts its type's own elements (`injective_iff_kernel_id`).

The language needs one verb (`v`) to state the distinguishing sentences.
The characterization is for one frame (the nouns, their types,
embeddings and criteria) under all interpretations of the verbs.
-/

namespace FraCaS.Encodings.Equivalence
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed
open FraCaS.Encodings.Counting

/-! ## Counting lemmas

Decidability instances are implicit arguments, not instance-implicit, so
the lemmas apply to counts whatever instances they were built with. -/

section
variable {N B C : Type} [Fintype N]

theorem countBy_le_one_of {f : N → B} {P : N → Prop} {_ : DecidableEq B} {_ : DecidablePred P}
    (h : ∀ x y, P x → P y → f x = f y) : countBy f P ≤ 1 := by
  unfold countBy
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  exact h x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

theorem one_lt_countBy_of {f : N → B} {P : N → Prop} {_ : DecidableEq B} {_ : DecidablePred P}
    {x y : N} (hx : P x) (hy : P y) (hxy : f x ≠ f y) : 1 < countBy f P := by
  unfold countBy
  exact Finset.one_lt_card.mpr
    ⟨f x, Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩),
      f y, Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩), hxy⟩

/-- Two functions that identify the same elements of `S` have images of
the same size. -/
theorem card_image_eq_of_kernel {f : N → B} {g : N → C} [DecidableEq B] [DecidableEq C]
    (S : Finset N) (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y ↔ g x = g y) :
    (S.image f).card = (S.image g).card := by
  have hfst : Set.InjOn Prod.fst ↑(S.image fun x => (f x, g x)) := by
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    exact Prod.ext hab ((h x hx y hy).mp hab)
  have hsnd : Set.InjOn Prod.snd ↑(S.image fun x => (f x, g x)) := by
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    exact Prod.ext ((h x hx y hy).mpr hab) hab
  have e1 := Finset.card_image_of_injOn hfst
  have e2 := Finset.card_image_of_injOn hsnd
  rw [Finset.image_image] at e1 e2
  have e1' : (S.image f).card = (S.image fun x => (f x, g x)).card := e1
  have e2' : (S.image g).card = (S.image fun x => (f x, g x)).card := e2
  rw [e1', e2']

theorem countBy_eq_of_kernel {f : N → B} {g : N → C} {P : N → Prop} {_ : DecidableEq B}
    {_ : DecidableEq C} {_ : DecidablePred P} (h : ∀ x y, P x → P y → (f x = f y ↔ g x = g y)) :
    countBy f P = countBy g P := by
  unfold countBy
  exact card_image_eq_of_kernel _ fun x hx y hy =>
    h x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

end

/-! ## Typed models whose nouns count by a criterion -/

variable {Noun Verb Name : Type}

/-- A typed model in which each noun counts by an identity criterion:
two elements of its type count as one when `crit` gives them the same
value. -/
structure CModel (Noun Verb Name : Type) extends TModel Noun Verb Name where
  K : Noun → Type
  crit : ∀ n, T n → K n

open Classical in
/-- How many `n`s are `P`, counted by `n`'s criterion. -/
noncomputable def CModel.countC (M : CModel Noun Verb Name) (n : Noun) (P : M.A → Prop) : Nat :=
  countBy (M.crit n) (fun y => P (M.emb n y))

/-- A determiner over a noun's type, with its counting done by `cnt`. -/
def detBy {N A : Type} (cnt : (A → Prop) → Nat) (e : N → A) :
    Det → (A → Prop) → (A → Prop) → Prop
  | .every, C, Q => EveryT e C Q
  | .some, C, Q => SomeT e C Q
  | .no, C, Q => NoT e C Q
  | .most, C, Q => 2 * cnt (fun x => C x ∧ Q x) > cnt C
  | .both, C, Q => cnt C = 2 ∧ EveryT e C Q
  | .neither, C, Q => cnt C = 2 ∧ NoT e C Q
  | .atLeast k, C, Q => cnt (fun x => C x ∧ Q x) ≥ k
  | .atMost k, C, Q => cnt (fun x => C x ∧ Q x) ≤ k
  | .exactly k, C, Q => cnt (fun x => C x ∧ Q x) = k

theorem detI_iff_detBy {N A : Type} [Fintype N] (e : N → A) (d : Det) (C Q : A → Prop) :
    detI e d C Q ↔ detBy (countI e) e d C Q := by
  cases d <;> exact Iff.rfl

noncomputable def CModel.satC (M : CModel Noun Verb Name) : Formula Noun Verb Name → Prop
  | .quant d n C Q =>
    detBy (M.countC n) (M.emb n) d (C.eval M.toTModel.isA M.verb) (Q.eval M.toTModel.isA M.verb)
  | .more n C Q S =>
    M.countC n (fun x => C.eval M.toTModel.isA M.verb x ∧ Q.eval M.toTModel.isA M.verb x) >
      M.countC n (fun x => C.eval M.toTModel.isA M.verb x ∧ S.eval M.toTModel.isA M.verb x)
  | .holds P c => P.eval M.toTModel.isA M.verb (M.name c)
  | .not φ => ¬ M.satC φ
  | .and φ ψ => M.satC φ ∧ M.satC ψ
  | .or φ ψ => M.satC φ ∨ M.satC ψ
  | .imp φ ψ => M.satC φ → M.satC ψ

/-- If every noun's criterion counts what counting individuals counts,
the criterion semantics is the individual-counting one. -/
theorem CModel.satC_iff_satI (M : CModel Noun Verb Name)
    (h : ∀ n (P : M.A → Prop), M.countC n P = countI (M.emb n) P) :
    ∀ φ : Formula Noun Verb Name, M.satC φ ↔ M.toTModel.satI φ
  | .quant d n C Q => by
    have hc : M.countC n = countI (M.emb n) := funext (h n)
    show detBy (M.countC n) (M.emb n) d _ _ ↔ detI (M.emb n) d _ _
    rw [hc]
    exact (detI_iff_detBy _ _ _ _).symm
  | .more n C Q S => by
    show M.countC n _ > M.countC n _ ↔ MoreI (M.emb n) _ _ _
    rw [h n, h n]
    exact Iff.rfl
  | .holds _ _ => Iff.rfl
  | .not φ => not_congr (M.satC_iff_satI h φ)
  | .and φ ψ => and_congr (M.satC_iff_satI h φ) (M.satC_iff_satI h ψ)
  | .or φ ψ => or_congr (M.satC_iff_satI h φ) (M.satC_iff_satI h ψ)
  | .imp φ ψ => imp_congr (M.satC_iff_satI h φ) (M.satC_iff_satI h ψ)

/-- A criterion that identifies exactly the elements that are one
individual counts what counting individuals counts. -/
theorem CModel.counts_eq_of_kernel (M : CModel Noun Verb Name)
    (hk : ∀ n (y y' : M.T n), M.crit n y = M.crit n y' ↔ M.emb n y = M.emb n y') :
    ∀ n (P : M.A → Prop), M.countC n P = countI (M.emb n) P := by
  intro n P
  unfold CModel.countC countI
  exact countBy_eq_of_kernel fun y y' _ _ => hk n y y'

/-- **Sufficiency.** With such criteria, the typed model and its predicate
reading make the same formulas true. -/
theorem CModel.satC_iff_shadow_of_kernel (M : CModel Noun Verb Name)
    (hk : ∀ n (y y' : M.T n), M.crit n y = M.crit n y' ↔ M.emb n y = M.emb n y')
    (φ : Formula Noun Verb Name) : M.satC φ ↔ M.toTModel.shadow.sat φ :=
  (M.satC_iff_satI (M.counts_eq_of_kernel hk) φ).trans (M.toTModel.sat_iff_shadowI φ)

/-- The same nouns, types, embeddings and criteria, with the verbs
interpreted by `verb`. -/
def CModel.withVerb (M : CModel Noun Verb Name) (verb : Verb → M.A → Prop) :
    CModel Noun Verb Name :=
  { M with verb := verb }

/-- **Necessity.** If the criterion semantics agrees with the predicate
reading under every interpretation of the verbs, each noun's criterion
is the individuals' identity. -/
theorem CModel.kernel_of_agree (M : CModel Noun Verb Name) (v : Verb)
    (h : ∀ (verb : Verb → M.A → Prop) (φ : Formula Noun Verb Name),
      (M.withVerb verb).satC φ ↔ (M.withVerb verb).toTModel.shadow.sat φ)
    (n : Noun) (y y' : M.T n) : M.crit n y = M.crit n y' ↔ M.emb n y = M.emb n y' := by
  have h' : ∀ (verb : Verb → M.A → Prop) (φ : Formula Noun Verb Name),
      (M.withVerb verb).satC φ ↔ (M.withVerb verb).toTModel.satI φ :=
    fun verb φ => (h verb φ).trans ((M.withVerb verb).toTModel.sat_iff_shadowI φ).symm
  -- An individual's elements are one by the criterion: otherwise "at most
  -- one n is v", with v true of that individual only, tells them apart.
  have fiber : ∀ z z' : M.T n, M.emb n z = M.emb n z' → M.crit n z = M.crit n z' := by
    intro z z' hzz'
    by_contra hne
    let verb : Verb → M.A → Prop := fun _ x => x = M.emb n z
    have hI : (M.withVerb verb).toTModel.satI (.quant (.atMost 1) n (.verb v) .top) := by
      show countI (M.emb n) (fun x => x = M.emb n z ∧ True) ≤ 1
      apply countBy_le_one_of
      intro a b ha hb
      exact ha.1.trans hb.1.symm
    have hC : (M.withVerb verb).countC n (fun x => x = M.emb n z ∧ True) ≤ 1 :=
      (h' verb (.quant (.atMost 1) n (.verb v) .top)).mpr hI
    have h2 : 1 < (M.withVerb verb).countC n (fun x => x = M.emb n z ∧ True) :=
      one_lt_countBy_of (x := z) (y := z') ⟨rfl, trivial⟩ ⟨hzz'.symm, trivial⟩ hne
    omega
  constructor
  · -- Elements one by the criterion are one individual: otherwise "at
    -- least two n are v", with v true of the two individuals only, tells
    -- them apart.
    intro hc
    by_contra hne
    let verb : Verb → M.A → Prop := fun _ x => x = M.emb n y ∨ x = M.emb n y'
    have hI : (M.withVerb verb).toTModel.satI (.quant (.atLeast 2) n (.verb v) .top) := by
      show 1 < countI (M.emb n) (fun x => (x = M.emb n y ∨ x = M.emb n y') ∧ True)
      exact one_lt_countBy_of (x := y) (y := y') ⟨Or.inl rfl, trivial⟩ ⟨Or.inr rfl, trivial⟩ hne
    have hC : (M.withVerb verb).countC n (fun x => (x = M.emb n y ∨ x = M.emb n y') ∧ True) ≥ 2 :=
      (h' verb (.quant (.atLeast 2) n (.verb v) .top)).mpr hI
    have h1 : (M.withVerb verb).countC n (fun x => (x = M.emb n y ∨ x = M.emb n y') ∧ True) ≤ 1 := by
      apply countBy_le_one_of
      intro a b ha hb
      have key : ∀ w : M.T n, (M.emb n w = M.emb n y ∨ M.emb n w = M.emb n y') →
          M.crit n w = M.crit n y := by
        rintro w (hw | hw)
        · exact fiber w y hw
        · exact (fiber w y' hw).trans hc.symm
      exact (key a ha.1).trans (key b hb.1).symm
    omega
  · exact fiber y y'

/-- **The characterization.** For fixed nouns, types, embeddings and
criteria, the criterion semantics and the predicate semantics agree on
every formula under every interpretation of the verbs exactly when each
noun's criterion is the individuals' identity. -/
theorem CModel.agree_iff_kernel (M : CModel Noun Verb Name) (v : Verb) :
    (∀ (verb : Verb → M.A → Prop) (φ : Formula Noun Verb Name),
      (M.withVerb verb).satC φ ↔ (M.withVerb verb).toTModel.shadow.sat φ) ↔
    ∀ n (y y' : M.T n), M.crit n y = M.crit n y' ↔ M.emb n y = M.emb n y' := by
  constructor
  · exact fun h n y y' => M.kernel_of_agree v h n y y'
  · intro hk verb φ
    exact (M.withVerb verb).satC_iff_shadow_of_kernel hk φ

/-- Injectivity, `valid_iff`'s condition, is the case where a noun
counts its type's own elements: the criterion `id` is the individuals'
identity exactly when the embedding is injective. -/
theorem injective_iff_kernel_id {T A : Type} (e : T → A) :
    Function.Injective e ↔ ∀ y y' : T, id y = id y' ↔ e y = e y' :=
  ⟨fun hinj y y' => ⟨fun h => congrArg e h, fun h => hinj h⟩,
    fun h y y' hy => (h y y').mpr hy⟩

end FraCaS.Encodings.Equivalence
