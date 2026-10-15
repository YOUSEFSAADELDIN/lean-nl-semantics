import EndToEnd.Encodings.FullAbstraction
import EndToEnd.Encodings.TranslationMulti

/-!
# What a noun with several criteria means, as far as inference can tell

`FullAbstraction.lean` shows that what the fragment's sentences see of a
noun with one identity criterion is its counting units. This file does
the same for nouns that count by a family of criteria, as copredicated
nouns do in `TranslationMulti.lean`: the `P`s are as many as the largest
set of `P`s pairwise distinct under every criterion. With two criteria
(volumes and texts) that is a largest matching, each book an edge
between its volume and its text.

**`obsEqM_iff` (full abstraction).** Two interpretations of such a noun
are indistinguishable by every formula of the fragment, in every context,
exactly when they give the same count for every set of individuals: for
each `P`, the size of a largest set of `P`s distinct under every
criterion. The extension is among what the counts fix. One verb in the
vocabulary is enough.

So, with several criteria, a noun means its counting function and
nothing more. Two further results say what that function is and is not.

- **The counts are not those of any one criterion (`not_single`).** Take
  three books: `b0` and `b1` are two copies of one text, and `b1` and
  `b2` are two texts bound in one volume. Counted by volume and by text
  at once, `b0` and `b1` are one book, `b1` and `b2` are one book, and
  all three are two (`b0` and `b2`). No interpretation with one
  criterion, whatever its type, embedding and criterion, is
  indistinguishable from this one. With one criterion, counts obey
  `count (P ∪ Q) + count (P ∩ Q) ≤ count P + count Q`
  (`count_toM_submod`), and here `2 + 1 > 1 + 1`. This strengthens
  `DotSetoid.lean`, which rules out an equivalence relation on the
  books' own type: no single criterion of any kind gives these counts.
- **The counts do not fix what each criterion does alone
  (`criteria_hidden`).** Two things at one individual, alike by one
  criterion and told apart by the other, are indistinguishable from one
  thing there. In this fragment every quantifier over the noun counts by
  the whole family, so no sentence counts by one criterion alone. (In
  `VerbCriteria.lean` the verb chooses the criteria, and then they are
  seen by construction.)

The one-criterion result does not follow from this one by itself: there
the counts were shown to determine a structure, the multiset of units.
Here the counts are the invariant, and no simpler structure is claimed.
-/

namespace FraCaS.Encodings.FullAbstractionMulti
open FraCaS.Encodings.Typed FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence
open FraCaS.Encodings.Relational
open FraCaS.Encodings.TranslationMulti (countF le_countF_iff)
open FraCaS.Encodings.FullAbstraction (NounI detBy_obs)
open Classical

variable {Noun Verb Rel Name A : Type}

/-! ## Nouns with families of criteria, and contexts -/

/-- An interpretation of a noun: a finite type, its embedding into the
individuals, and a family of identity criteria. -/
structure NounM (A : Type) where
  T : Type
  fin : Fintype T
  emb : T → A
  ι : Type
  K : ι → Type
  crit : ∀ i, T → K i

instance (I : NounM A) : Fintype I.T := I.fin

/-- How many of the noun's things are `P`: the largest set of them
pairwise distinct under every criterion. -/
noncomputable def NounM.count (I : NounM A) (P : A → Prop) : Nat :=
  countF I.crit (fun y => P (I.emb y))

/-- Being one of the noun's individuals. -/
def NounM.ext (I : NounM A) (x : A) : Prop := ∃ y, I.emb y = x

structure Ctx (Noun Verb Rel Name A : Type) where
  noun : Noun → NounM A
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

noncomputable def Ctx.set (M : Ctx Noun Verb Rel Name A) (n0 : Noun) (I : NounM A) :
    Ctx Noun Verb Rel Name A :=
  { M with noun := fun n => if n = n0 then I else M.noun n }

theorem Ctx.set_self (M : Ctx Noun Verb Rel Name A) (n0 : Noun) (I : NounM A) :
    (M.set n0 I).noun n0 = I := if_pos rfl

theorem Ctx.set_ne (M : Ctx Noun Verb Rel Name A) {n n0 : Noun} (I : NounM A) (h : n ≠ n0) :
    (M.set n0 I).noun n = M.noun n := if_neg h

/-- Two interpretations of `n0` are indistinguishable: no formula, in no
context, tells them apart. -/
def ObsEqM (n0 : Noun) (I I' : NounM A) : Prop :=
  ∀ (M : Ctx Noun Verb Rel Name A) (φ : Form Noun Verb Rel Name) (ρ : Nat → A),
    Form.eval (M.set n0 I).interp φ ρ ↔ Form.eval (M.set n0 I').interp φ ρ

/-! ## Counting facts -/

theorem count_congr (I : NounM A) {P P' : A → Prop} (h : ∀ x, P x ↔ P' x) :
    I.count P = I.count P' := by
  have e : P = P' := funext fun x => propext (h x)
  rw [e]

/-- At least one `P`, counted any way, is some thing that is `P`. -/
theorem one_le_count_iff (I : NounM A) (P : A → Prop) :
    1 ≤ I.count P ↔ ∃ y, P (I.emb y) := by
  unfold NounM.count
  rw [le_countF_iff]
  constructor
  · rintro ⟨S, h1, hP, -⟩
    obtain ⟨y, hy⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨y, hP y hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨{y}, (Finset.card_singleton y).symm.le, fun z hz => ?_, fun i => ?_⟩
    · rw [Finset.mem_singleton.mp hz]
      exact hy
    · rw [Finset.coe_singleton]
      exact Set.injOn_singleton _ _

theorem ext_iff_one_le (I : NounM A) (x : A) : I.ext x ↔ 1 ≤ I.count (fun z => z = x) :=
  (one_le_count_iff I (fun z => z = x)).symm

theorem count_empty (I : NounM A) (hA : IsEmpty A) (P : A → Prop) : I.count P = 0 := by
  by_contra h
  obtain ⟨y, -⟩ := (one_le_count_iff I P).mp (Nat.one_le_iff_ne_zero.mpr h)
  exact hA.false (I.emb y)

/-- If one criterion gives all the `P`s one value, there is at most one. -/
theorem count_le_one_of (I : NounM A) (P : A → Prop) (i : I.ι)
    (h : ∀ a b, P (I.emb a) → P (I.emb b) → I.crit i a = I.crit i b) : I.count P ≤ 1 := by
  unfold NounM.count
  by_contra hlt
  obtain ⟨S, h2, hP, hinj⟩ := (le_countF_iff I.crit (fun y => P (I.emb y)) 2).mp (by omega)
  have : S.card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => hinj i ha hb (h a b (hP a ha) (hP b hb))
  omega

/-! ## Full abstraction -/

theorem agree_of (M : Ctx Noun Verb Rel Name A) (n0 : Noun) {I I' : NounM A}
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

/-- Indistinguishable interpretations have the same counts: "exactly `j`
`n0`s are `v`", with `v` true of `P`. -/
theorem count_of_obs (v : Verb) {n0 : Noun} {I I' : NounM A}
    (h : ObsEqM (Verb := Verb) (Rel := Rel) (Name := Name) n0 I I') (P : A → Prop) :
    I.count P = I'.count P := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a⟩⟩
  · rw [count_empty I hA, count_empty I' hA]
  · let M : Ctx Noun Verb Rel Name A := ⟨fun _ => I, fun _ => P, fun _ _ _ => False, fun _ => a⟩
    have key : ∀ (J : NounM A) (j : Nat),
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

/-- **Full abstraction, several criteria.** Two interpretations of a noun
are indistinguishable by every formula in every context exactly when
they give every set of individuals the same count. -/
theorem obsEqM_iff (v : Verb) (n0 : Noun) (I I' : NounM A) :
    ObsEqM (Verb := Verb) (Rel := Rel) (Name := Name) n0 I I' ↔
      ∀ P, I.count P = I'.count P := by
  constructor
  · intro h
    exact count_of_obs v h
  · intro hc M φ ρ
    have hE : ∀ x, I.ext x ↔ I'.ext x := fun x => by
      rw [ext_iff_one_le, ext_iff_one_le, hc]
    exact (agree_of M n0 hE hc).eval φ ρ

/-! ## One criterion: counts are submodular -/

/-- A noun with one criterion, as a noun with a family of one. -/
def _root_.FraCaS.Encodings.FullAbstraction.NounI.toM (J : NounI A) : NounM A := ⟨J.T, J.fin, J.emb, Unit, fun _ => J.K, fun _ => J.crit⟩

/-- The values the criterion takes on the `R`s. -/
noncomputable def _root_.FraCaS.Encodings.FullAbstraction.NounI.img (J : NounI A) (R : A → Prop) : Finset J.K :=
  (Finset.univ.filter (fun y => R (J.emb y))).image J.crit

/-- With one criterion, the largest set of `P`s distinct under it is as
large as the criterion's values on the `P`s. -/
theorem countF_unit {N K : Type} [Fintype N] (c : N → K) (P : N → Prop) :
    countF (fun _ : Unit => c) P = ((Finset.univ.filter P).image c).card := by
  apply le_antisymm
  · obtain ⟨S, hn, hP, hinj⟩ := (le_countF_iff (fun _ : Unit => c) P _).mp le_rfl
    calc countF (fun _ : Unit => c) P ≤ S.card := hn
      _ = (S.image c).card := (Finset.card_image_of_injOn (hinj ())).symm
      _ ≤ ((Finset.univ.filter P).image c).card :=
          Finset.card_le_card (Finset.image_subset_image fun y hy =>
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP y hy⟩)
  · let s := (Finset.univ.filter P).image c
    let g : {k // k ∈ s} → N := fun k => (Finset.mem_image.mp k.2).choose
    have hg : ∀ k, g k ∈ Finset.univ.filter P ∧ c (g k) = k.val := fun k =>
      (Finset.mem_image.mp k.2).choose_spec
    have hgi : Function.Injective g := by
      intro k1 k2 h
      apply Subtype.ext
      calc k1.val = c (g k1) := (hg k1).2.symm
        _ = c (g k2) := congrArg c h
        _ = k2.val := (hg k2).2
    refine (le_countF_iff (fun _ : Unit => c) P _).mpr ⟨s.attach.image g, ?_, ?_, ?_⟩
    · exact ((Finset.card_image_of_injective _ hgi).trans Finset.card_attach).symm.le
    · intro y hy
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp (hg k).1).2
    · intro _ a ha b hb hab
      obtain ⟨k1, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
      obtain ⟨k2, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
      refine congrArg g (Subtype.ext ?_)
      calc k1.val = c (g k1) := (hg k1).2.symm
        _ = c (g k2) := hab
        _ = k2.val := (hg k2).2

theorem mem_img (J : NounI A) (R : A → Prop) (k : J.K) :
    k ∈ J.img R ↔ ∃ y, R (J.emb y) ∧ J.crit y = k := by
  unfold NounI.img
  constructor
  · intro hk
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨y, (Finset.mem_filter.mp hy).2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩

theorem count_toM (J : NounI A) (R : A → Prop) : J.toM.count R = (J.img R).card :=
  countF_unit J.crit (fun y => R (J.emb y))

/-- **With one criterion, counts are submodular.** -/
theorem count_toM_submod (J : NounI A) (P Q : A → Prop) :
    J.toM.count (fun z => P z ∨ Q z) + J.toM.count (fun z => P z ∧ Q z) ≤
      J.toM.count P + J.toM.count Q := by
  rw [count_toM, count_toM, count_toM, count_toM]
  have hU : J.img (fun z => P z ∨ Q z) = J.img P ∪ J.img Q := by
    ext k
    rw [mem_img, Finset.mem_union, mem_img, mem_img]
    constructor
    · rintro ⟨y, h | h, rfl⟩
      · exact Or.inl ⟨y, h, rfl⟩
      · exact Or.inr ⟨y, h, rfl⟩
    · rintro (⟨y, h, rfl⟩ | ⟨y, h, rfl⟩)
      · exact ⟨y, Or.inl h, rfl⟩
      · exact ⟨y, Or.inr h, rfl⟩
  have hI : J.img (fun z => P z ∧ Q z) ⊆ J.img P ∩ J.img Q := by
    intro k hk
    obtain ⟨y, ⟨h1, h2⟩, rfl⟩ := (mem_img J _ k).mp hk
    exact Finset.mem_inter.mpr ⟨(mem_img J P _).mpr ⟨y, h1, rfl⟩, (mem_img J Q _).mpr ⟨y, h2, rfl⟩⟩
  rw [hU]
  have e := Finset.card_union_add_card_inter (J.img P) (J.img Q)
  have l := Finset.card_le_card hI
  omega

/-! ## Three books that no single criterion counts -/

/-- `b0`, `b1`, `b2` by volume (`true`) and by text (`false`): `b1` and
`b2` share a volume, `b0` and `b1` share a text. -/
def bcrit : Bool → Fin 3 → Fin 2
  | true, y => if y = 0 then 0 else 1
  | false, y => if y = 2 then 1 else 0

/-- `b0` and `b2`. -/
def S02 : Finset (Fin 3) := {0, 2}

theorem S02_card : 2 ≤ S02.card := by decide

theorem mem_S02 : ∀ y, y ∈ S02 → y = 0 ∨ y = 2 := by decide

theorem bcrit_02 : ∀ i, ∀ a ∈ S02, ∀ b ∈ S02, bcrit i a = bcrit i b → a = b := by decide

theorem bcrit_01 : ∀ a b : Fin 3, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
    bcrit false a = bcrit false b := by decide

theorem bcrit_12 : ∀ a b : Fin 3, (a = 1 ∨ a = 2) → (b = 1 ∨ b = 2) →
    bcrit true a = bcrit true b := by decide

/-- The three books, as three individuals. -/
def books (x : Fin 3 → A) : NounM A := ⟨Fin 3, inferInstance, x, Bool, fun _ => Fin 2, bcrit⟩

def P01 (x : Fin 3 → A) (z : A) : Prop := z = x 0 ∨ z = x 1
def P12 (x : Fin 3 → A) (z : A) : Prop := z = x 1 ∨ z = x 2

theorem books_01 (x : Fin 3 → A) (hx : Function.Injective x) : (books x).count (P01 x) ≤ 1 :=
  count_le_one_of (books x) (P01 x) (false : Bool) fun a b ha hb =>
    bcrit_01 a b (Or.imp (fun h => hx h) (fun h => hx h) ha)
      (Or.imp (fun h => hx h) (fun h => hx h) hb)

theorem books_12 (x : Fin 3 → A) (hx : Function.Injective x) : (books x).count (P12 x) ≤ 1 :=
  count_le_one_of (books x) (P12 x) (true : Bool) fun a b ha hb =>
    bcrit_12 a b (Or.imp (fun h => hx h) (fun h => hx h) ha)
      (Or.imp (fun h => hx h) (fun h => hx h) hb)

theorem books_union (x : Fin 3 → A) : 2 ≤ (books x).count (fun z => P01 x z ∨ P12 x z) := by
  unfold NounM.count
  refine (le_countF_iff _ _ 2).mpr ⟨S02, S02_card, fun y hy => ?_,
    fun i a ha b hb => bcrit_02 i a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb)⟩
  rcases mem_S02 y hy with rfl | rfl
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem books_inter (x : Fin 3 → A) : 1 ≤ (books x).count (fun z => P01 x z ∧ P12 x z) :=
  (one_le_count_iff _ _).mpr ⟨(1 : Fin 3), Or.inr rfl, Or.inl rfl⟩

/-- **No single criterion counts the three books.** No interpretation
with one criterion is indistinguishable from them. -/
theorem not_single (v : Verb) (n0 : Noun) (x : Fin 3 → A) (hx : Function.Injective x)
    (J : NounI A) : ¬ ObsEqM (Verb := Verb) (Rel := Rel) (Name := Name) n0 (books x) J.toM := by
  intro h
  have hc := (obsEqM_iff v n0 _ _).mp h
  have s := count_toM_submod J (P01 x) (P12 x)
  have e1 := hc (fun z => P01 x z ∨ P12 x z)
  have e2 := hc (fun z => P01 x z ∧ P12 x z)
  have e3 := hc (P01 x)
  have e4 := hc (P12 x)
  have b1 := books_union x
  have b2 := books_inter x
  have b3 := books_01 x hx
  have b4 := books_12 x hx
  omega

/-! ## The counts do not fix each criterion -/

/-- Two things at one individual, alike by criterion `true`, told apart
by criterion `false`. -/
def twoAt (a : A) : NounM A :=
  ⟨Bool, inferInstance, fun _ => a, Bool, fun _ => Bool, fun i y => if i then false else y⟩

/-- One thing at that individual. -/
def oneAt (a : A) : NounM A :=
  ⟨Unit, inferInstance, fun _ => a, Bool, fun _ => Bool, fun _ _ => false⟩

/-- The noun counted by criterion `i` alone. -/
def NounM.only (I : NounM A) (i : I.ι) : NounM A :=
  ⟨I.T, I.fin, I.emb, Unit, fun _ => I.K i, fun _ => I.crit i⟩

/-- **What each criterion does alone is not seen.** The two
interpretations are indistinguishable, yet counted by criterion `false`
alone one has two things and the other one. -/
theorem criteria_hidden (v : Verb) (n0 : Noun) (a : A) :
    ObsEqM (Verb := Verb) (Rel := Rel) (Name := Name) n0 (twoAt a) (oneAt a) ∧
      2 ≤ ((twoAt a).only (false : Bool)).count (fun _ => True) ∧
      ((oneAt a).only (false : Bool)).count (fun _ => True) ≤ 1 := by
  refine ⟨(obsEqM_iff v n0 _ _).mpr fun P => ?_, ?_,
    count_le_one_of _ _ () fun _ _ _ _ => rfl⟩
  · have h1 := count_le_one_of (twoAt a) P (true : Bool) fun _ _ _ _ => rfl
    have h2 := count_le_one_of (oneAt a) P (true : Bool) fun _ _ _ _ => rfl
    have e : 1 ≤ (twoAt a).count P ↔ 1 ≤ (oneAt a).count P := by
      rw [one_le_count_iff, one_le_count_iff]
      exact ⟨fun ⟨_, h⟩ => ⟨(), h⟩, fun ⟨_, h⟩ => ⟨true, h⟩⟩
    by_cases hp : 1 ≤ (twoAt a).count P
    · have := e.mp hp
      omega
    · have := mt e.mpr hp
      omega
  · unfold NounM.count
    refine (le_countF_iff _ _ 2).mpr ⟨Finset.univ, ?_, fun _ _ => trivial, fun _ y _ z _ h => h⟩
    show 2 ≤ (Finset.univ : Finset Bool).card
    decide

end FraCaS.Encodings.FullAbstractionMulti
