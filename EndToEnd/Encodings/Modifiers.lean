import EndToEnd.Encodings.Selection

/-!
# Two arguments about adjectives: "heavy book" and subsectivity

## 1. "Heavy book" (Chatzikyriakidis & Luo 2017, pp. 47-48)

Their argument against nouns as predicates once sorts such as `Phy` and
`Info` are introduced: with `book : Phy • Info → t` and
`heavy : (Phy → t) → (Phy → t)`, typing `heavy(book)` needs
`Phy • Info → t ≤ Phy → t`, so by contravariance `Phy ≤ Phy • Info`,
"the wrong direction". They conclude that nouns as predicates are
"incompatible with the introduction of subtypes such as Phy and Info"
(p. 48), and say the same of Dependent Type Semantics (p. 51).

The argument applies the adjective to the noun *predicate*. A sorted
predicate encoding can instead apply it to the noun's *variable*: "every
heavy book" binds a variable of the noun's sort and says `heavy` of it,
as MTT's own `Σx : Book. heavy(x)` does. Then what is needed is
`Phy • Info ≤ Phy`, the right direction, which MTT assumes too.

- `wt_heavy_book`: in the MTT lexicon (`hbSig`: `Book ≤ Phy • Info`,
  `Phy • Info ≤ Phy`, `Phy • Info ≤ Info`), "John picked up and mastered
  every heavy book" is well typed.
- `wt_sorts_heavy_book`: so it is in the many-sorted predicate lexicon
  `hbSig.sorts` (`Selection.wt_sorts_iff`), where `book` is a predicate
  over a sort, not a type of its own.
- `not_phy_le_dot`, `not_sorts_phy_le_dot`: `Phy ≤ Phy • Info` fails in
  both lexicons, and neither needs it.

So the argument holds against an encoding that types adjectives as
modifiers of `Phy`-predicates, not against sorted predicates as such.

## 2. Subsectivity (FraCaS 29)

FraCaS 29 needs "every leading businessman is a businessman". Phase 3
found that nouns as types supply it (the type of leading businessmen is
`Σx : Businessman. leading(x)`), while nouns as predicates need a
postulate. This section shows the two are the same stipulation in two
places.

The vocabulary has base nouns `n` and modified nouns `(a, n)`.

- **Typed side (`Coercive`).** Each modified noun's type has a coercion
  into its noun's type that commutes with the embeddings: MTT's first
  projection out of `Σx : N. a(x)`.
- **Predicate side (`Subsective`).** A modified noun applies only to
  what its noun applies to: the subsectivity postulate.

**`validSub_iff`**: counting individuals, an entailment is valid over
coercive typed models exactly when it is valid over subsective predicate
models. And each side needs its stipulation. FraCaS 29's entailment is
valid on both sides with it (`fracas29_P`, `fracas29_T`), fails over all
predicate models (`fracas29_not_P`), and fails over all typed models
too (`fracas29_not_T`). Types get subsectivity from choosing the
Σ-type for "leading businessman", which is the same lexical decision as
the predicate side's postulate that "leading" is subsective.

The modified noun here is its own word, so the predicate side's
`leading businessman` need not be a function of `businessman`'s
extension. With an extensional modifier, coextensive nouns would get
coextensive modified nouns, which is Phase 1a's problem 215 and is not
claimed here.
-/

namespace FraCaS.Encodings.Modifiers
open FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed
open FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence FraCaS.Encodings.Relational
open FraCaS.Encodings.Selection

/-! ## 1. "Heavy book" -/

inductive HTy | human | phy | info | dot | book
  deriving DecidableEq

/-- Subtyping: the dot type below both its constituents (Luo's rule for
dot types), books below the dot type, and so below both. -/
def leB : HTy → HTy → Bool
  | .human, .human => true
  | .phy, .phy => true
  | .info, .info => true
  | .dot, .dot => true
  | .dot, .phy => true
  | .dot, .info => true
  | .book, .book => true
  | .book, .dot => true
  | .book, .phy => true
  | .book, .info => true
  | _, _ => false

inductive HNoun | book
inductive HVerb | heavy
inductive HRel | pickUp | master
inductive HName | john

/-- The MTT lexicon of the argument. -/
def hbSig : Sig HNoun HVerb HRel HName where
  Ty := HTy
  le a b := leB a b = true
  le_refl t := by cases t <;> rfl
  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> decide
  noun _ := .book
  verb _ := .phy
  arg1 _ := .human
  arg2
    | .pickUp => .phy
    | .master => .info
  name _ := .human

/-- "John picked up and mastered every heavy book." -/
def heavyBook : Form HNoun HVerb HRel HName :=
  .quant .every .book (.verb .heavy (.var 0))
    (.and (.rel .pickUp (.name .john) (.var 0)) (.rel .master (.name .john) (.var 0)))

theorem wt_heavy_book : WT hbSig [] heavyBook :=
  .quant (.verb (.var List.getElem?_cons_zero) rfl)
    (.and (.rel (.name .john) (.var List.getElem?_cons_zero) rfl rfl)
      (.rel (.name .john) (.var List.getElem?_cons_zero) rfl rfl))

/-- The same sentence is well typed with nouns as predicates over sorts. -/
theorem wt_sorts_heavy_book : WT hbSig.sorts [] heavyBook :=
  (wt_sorts_iff hbSig [] heavyBook).mp wt_heavy_book

/-- The direction the argument says predicates need fails in MTT's own
lexicon. -/
theorem not_phy_le_dot : ¬ hbSig.le HTy.phy HTy.dot :=
  fun h => absurd (h : leB HTy.phy HTy.dot = true) (by decide)

/-- ... and in the sorted lexicon: the sort of physical objects is not
below the sort of the dot type, since only the latter fits `master`'s
object. -/
theorem not_sorts_phy_le_dot :
    ¬ hbSig.sorts.le (hbSig.prof HTy.phy) (hbSig.prof HTy.dot) := by
  intro h
  have := h HTy.info ⟨Or.inr (Or.inr ⟨HRel.master, rfl⟩), rfl⟩
  exact absurd (this.2 : leB HTy.phy HTy.info = true) (by decide)

/-- The direction that is used holds in the sorted lexicon: the dot sort
is below the sort of physical objects. -/
theorem sorts_dot_le_phy : hbSig.sorts.le (hbSig.prof HTy.dot) (hbSig.prof HTy.phy) := by
  rintro d ⟨hd, hle⟩
  exact ⟨hd, hbSig.le_trans HTy.dot HTy.phy d (rfl : leB HTy.dot HTy.phy = true) hle⟩

/-! ## 2. Subsectivity -/

section
variable {N Adj Verb Rel Name : Type}

/-- Each modified noun's type has a coercion into its noun's type that
commutes with the embeddings, as the first projection of
`Σx : N. a(x)` does. -/
def Coercive (M : TModel (N ⊕ (Adj × N)) Verb Name) : Prop :=
  ∀ a n, ∃ π : M.T (.inr (a, n)) → M.T (.inl n),
    ∀ y, M.emb (.inr (a, n)) y = M.emb (.inl n) (π y)

/-- A modified noun applies only to what its noun applies to. -/
def Subsective (M : PModel (N ⊕ (Adj × N)) Verb Name) : Prop :=
  ∀ a n x, M.noun (.inr (a, n)) x → M.noun (.inl n) x

def TValidSub (Γ : List (Form (N ⊕ (Adj × N)) Verb Rel Name))
    (φ : Form (N ⊕ (Adj × N)) Verb Rel Name) : Prop :=
  ∀ M : TModel (N ⊕ (Adj × N)) Verb Name, Coercive M →
    ∀ (rel : Rel → M.A → M.A → Prop) (ρ : Nat → M.A),
      (∀ ψ ∈ Γ, Form.eval (tII M rel) ψ ρ) → Form.eval (tII M rel) φ ρ

def PValidSub (Γ : List (Form (N ⊕ (Adj × N)) Verb Rel Name))
    (φ : Form (N ⊕ (Adj × N)) Verb Rel Name) : Prop :=
  ∀ M : PModel (N ⊕ (Adj × N)) Verb Name, Subsective M →
    ∀ (rel : Rel → M.A → M.A → Prop) (ρ : Nat → M.A),
      (∀ ψ ∈ Γ, Form.eval (pI M rel) ψ ρ) → Form.eval (pI M rel) φ ρ

theorem shadow_subsective (M : TModel (N ⊕ (Adj × N)) Verb Name) (h : Coercive M) :
    Subsective M.shadow := by
  intro a n x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨π, hπ⟩ := h a n
  exact ⟨π y, (hπ y).symm⟩

theorem lift_coercive (M : PModel (N ⊕ (Adj × N)) Verb Name) (h : Subsective M) :
    Coercive M.lift :=
  fun a n => ⟨fun y => ⟨y.val, h a n y.val y.2⟩, fun _ => rfl⟩

/-- **Subsectivity in types and in predicates.** Counting individuals,
an entailment is valid over typed models whose modified nouns coerce
into their nouns exactly when it is valid over predicate models with the
subsectivity postulate. -/
theorem validSub_iff (Γ : List (Form (N ⊕ (Adj × N)) Verb Rel Name))
    (φ : Form (N ⊕ (Adj × N)) Verb Rel Name) : TValidSub Γ φ ↔ PValidSub Γ φ := by
  constructor
  · intro h M hM rel ρ hΓ
    have key := ((pI_agree_lift_shadow M rel).trans (tII_agree_shadow M.lift rel).symm).eval
    exact (key φ ρ).mpr (h M.lift (lift_coercive M hM) rel ρ fun ψ hψ => (key ψ ρ).mp (hΓ ψ hψ))
  · intro h M hM rel ρ hΓ
    have key := (tII_agree_shadow M rel).eval
    exact (key φ ρ).mpr
      (h M.shadow (shadow_subsective M hM) rel ρ fun ψ hψ => (key ψ ρ).mp (hΓ ψ hψ))

end

/-! ### FraCaS 29 -/

inductive N29 | commissioner | businessman
  deriving DecidableEq
inductive A29 | leading
  deriving DecidableEq

/-- "Every commissioner is a leading businessman." -/
def p29 : Form (N29 ⊕ (A29 × N29)) Empty Empty Empty :=
  .quant .every (.inl .commissioner) .top (.isA (.inr (.leading, .businessman)) (.var 0))

/-- "Every commissioner is a businessman." -/
def h29 : Form (N29 ⊕ (A29 × N29)) Empty Empty Empty :=
  .quant .every (.inl .commissioner) .top (.isA (.inl .businessman) (.var 0))

theorem fracas29_P : PValidSub [p29] h29 := by
  intro M hM rel ρ hΓ
  have h := hΓ p29 (List.mem_singleton_self _)
  intro x hx
  exact hM _ _ x (h x hx)

theorem fracas29_T : TValidSub [p29] h29 := (validSub_iff _ _).mpr fracas29_P

/-- Without the postulate, predicates do not give 29. -/
theorem fracas29_not_P : ¬ PValidR [p29] h29 := by
  intro h
  let M : PModel (N29 ⊕ (A29 × N29)) Empty Empty :=
    ⟨Unit, inferInstance, fun n _ => n ≠ .inl .businessman, fun v => v.elim, fun c => c.elim⟩
  have := h M (fun r => r.elim) (fun _ => ()) (by
    intro ψ hψ
    rw [List.mem_singleton] at hψ
    subst hψ
    intro _ _
    show (Sum.inr (A29.leading, N29.businessman) : N29 ⊕ (A29 × N29)) ≠ .inl .businessman
    exact Sum.inr_ne_inl)
  exact this () ⟨Sum.inl_injective.ne (by decide), trivial⟩ rfl

/-- Without the coercion, types do not give 29 either. -/
theorem fracas29_not_T : ¬ TValidRI [p29] h29 := by
  intro h
  let M : TModel (N29 ⊕ (A29 × N29)) Empty Empty :=
    ⟨Bool, inferInstance, fun _ => Unit, fun _ => inferInstance,
      fun n _ => decide (n ≠ .inl .businessman), fun v => v.elim, fun c => c.elim⟩
  have := h M (fun r => r.elim) (fun _ => true) (by
    intro ψ hψ
    rw [List.mem_singleton] at hψ
    subst hψ
    intro _ _
    exact ⟨(), rfl⟩)
  obtain ⟨_, hy⟩ := this () trivial
  exact absurd hy (by decide)

end FraCaS.Encodings.Modifiers
