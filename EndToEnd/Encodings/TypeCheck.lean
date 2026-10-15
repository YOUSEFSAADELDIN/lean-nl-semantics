import EndToEnd.Encodings.Modifiers

/-!
# Type checking stays decidable: the "both" view without (*)

Chatzikyriakidis & Luo (2017, p. 51) object to interpreting a noun both
as a type and as a predicate (Retoré 2013; Asher et al. 2016): it needs

  (*) for any x : e, x : Man if and only if man(x) is true,

"for this to work", and (*) "cannot simply [be] stipulate[d]": as a rule
of the type theory it would make typing depend on the truth of
propositions, and type checking undecidable.

The correspondences in this project never put (*) into a type theory.

- **Type checking is decidable (`check`, `check_iff`, `wtDecidable`).**
  Well-typedness in the fragment (`Selection.WT`) is decided by a
  program that reads only the formula, the context and the lexicon's
  types and subtyping. It is proved to agree with `WT`. The same
  program decides well-typedness in the sorted predicate lexicon
  (`wtSortsDecidable`, through `wt_sorts_iff`). No model, and no truth
  of any proposition, is consulted.
- **(*) holds between models, as a theorem.** For a typed model and its
  predicate reading, being an `n` is being in the image of `n`'s type
  (`both_shadow`, by definition). For a predicate model and its typed
  reading, being in the image of `n`'s type is being an `n`
  (`both_lift`). The validity theorems (`validI_iff`, `validRI_iff`,
  `validC_iff`, ...) are proved from these, in the metatheory.

So the objection, which is right about (*) as a typing rule, does not
reach this kind of "both": two encodings with decidable typing, related
by theorems about their models.

What is not done here: the undecidability itself. That (*) as a typing
rule makes type checking as hard as validity is the objection's claim,
not checked here.
-/

namespace FraCaS.Encodings.TypeCheck
open FraCaS.Encodings.Equivalence FraCaS.Encodings.Relational FraCaS.Encodings.Selection

variable {Noun Verb Rel Name : Type}

/-! ## A type checker -/

/-- A term's type, if it has one. -/
def typeOf (S : Sig Noun Verb Rel Name) (Γ : List S.Ty) : Term Name → Option S.Ty
  | .var k => Γ[k]?
  | .name c => some (S.name c)

theorem hasTy_iff (S : Sig Noun Verb Rel Name) (Γ : List S.Ty) (t : Term Name) (τ : S.Ty) :
    HasTy S Γ t τ ↔ typeOf S Γ t = some τ := by
  constructor
  · intro h
    cases h with
    | var hk => exact hk
    | name c => rfl
  · intro h
    cases t with
    | var k => exact .var h
    | name c =>
      obtain rfl := Option.some.inj h
      exact .name c

section
variable (S : Sig Noun Verb Rel Name) (dle : ∀ a b, Decidable (S.le a b))

/-- Does the term have a type below `d`? -/
def fits (Γ : List S.Ty) (t : Term Name) (d : S.Ty) : Bool :=
  match typeOf S Γ t with
  | some τ => @decide (S.le τ d) (dle τ d)
  | none => false

theorem fits_iff (Γ : List S.Ty) (t : Term Name) (d : S.Ty) :
    fits S dle Γ t d = true ↔ ∃ τ, HasTy S Γ t τ ∧ S.le τ d := by
  unfold fits
  constructor
  · intro h
    cases e : typeOf S Γ t with
    | none =>
      rw [e] at h
      exact absurd h Bool.false_ne_true
    | some τ =>
      rw [e] at h
      exact ⟨τ, (hasTy_iff S Γ t τ).mpr e, @of_decide_eq_true _ (dle τ d) h⟩
  · rintro ⟨τ, ht, hle⟩
    rw [(hasTy_iff S Γ t τ).mp ht]
    exact @decide_eq_true _ (dle τ d) hle

theorem scoped_iff (Γ : List S.Ty) (t : Term Name) :
    (typeOf S Γ t).isSome = true ↔ ∃ τ, HasTy S Γ t τ := by
  constructor
  · intro h
    cases e : typeOf S Γ t with
    | none =>
      rw [e] at h
      exact absurd h Bool.false_ne_true
    | some τ => exact ⟨τ, (hasTy_iff S Γ t τ).mpr e⟩
  · rintro ⟨τ, ht⟩
    rw [(hasTy_iff S Γ t τ).mp ht]
    rfl

/-- The checker: it reads the formula, the context and the lexicon. -/
def check : List S.Ty → Form Noun Verb Rel Name → Bool
  | Γ, .verb v t => fits S dle Γ t (S.verb v)
  | Γ, .rel r t u => fits S dle Γ t (S.arg1 r) && fits S dle Γ u (S.arg2 r)
  | Γ, .isA _ t => (typeOf S Γ t).isSome
  | Γ, .eq t u => (typeOf S Γ t).isSome && (typeOf S Γ u).isSome
  | _, .top => true
  | Γ, .not φ => check Γ φ
  | Γ, .and φ ψ => check Γ φ && check Γ ψ
  | Γ, .or φ ψ => check Γ φ && check Γ ψ
  | Γ, .imp φ ψ => check Γ φ && check Γ ψ
  | Γ, .quant _ n C Q => check (S.noun n :: Γ) C && check (S.noun n :: Γ) Q
  | Γ, .more n C Q R =>
    check (S.noun n :: Γ) C && check (S.noun n :: Γ) Q && check (S.noun n :: Γ) R

/-- **The checker decides well-typedness.** -/
theorem check_iff : ∀ (φ : Form Noun Verb Rel Name) (Γ : List S.Ty),
    check S dle Γ φ = true ↔ WT S Γ φ
  | .verb v t, Γ => by
    rw [show check S dle Γ (.verb v t) = fits S dle Γ t (S.verb v) from rfl, fits_iff]
    constructor
    · rintro ⟨τ, ht, hle⟩
      exact .verb ht hle
    · intro h
      cases h with
      | verb ht hle => exact ⟨_, ht, hle⟩
  | .rel r t u, Γ => by
    rw [show check S dle Γ (.rel r t u) =
      (fits S dle Γ t (S.arg1 r) && fits S dle Γ u (S.arg2 r)) from rfl,
      Bool.and_eq_true, fits_iff, fits_iff]
    constructor
    · rintro ⟨⟨τ, ht, h1⟩, ⟨σ, hu, h2⟩⟩
      exact .rel ht hu h1 h2
    · intro h
      cases h with
      | rel ht hu h1 h2 => exact ⟨⟨_, ht, h1⟩, ⟨_, hu, h2⟩⟩
  | .isA n t, Γ => by
    rw [show check S dle Γ (.isA n t) = (typeOf S Γ t).isSome from rfl, scoped_iff]
    constructor
    · rintro ⟨τ, ht⟩
      exact .isA ht
    · intro h
      cases h with
      | isA ht => exact ⟨_, ht⟩
  | .eq t u, Γ => by
    rw [show check S dle Γ (.eq t u) = ((typeOf S Γ t).isSome && (typeOf S Γ u).isSome) from rfl,
      Bool.and_eq_true, scoped_iff, scoped_iff]
    constructor
    · rintro ⟨⟨τ, ht⟩, ⟨σ, hu⟩⟩
      exact .eq ht hu
    · intro h
      cases h with
      | eq ht hu => exact ⟨⟨_, ht⟩, ⟨_, hu⟩⟩
  | .top, _ => ⟨fun _ => .top, fun _ => rfl⟩
  | .not φ, Γ => by
    rw [show check S dle Γ (.not φ) = check S dle Γ φ from rfl, check_iff φ Γ]
    exact ⟨fun h => .not h, fun h => by cases h with | not h => exact h⟩
  | .and φ ψ, Γ => by
    rw [show check S dle Γ (.and φ ψ) = (check S dle Γ φ && check S dle Γ ψ) from rfl,
      Bool.and_eq_true, check_iff φ Γ, check_iff ψ Γ]
    exact ⟨fun ⟨a, b⟩ => .and a b, fun h => by cases h with | and a b => exact ⟨a, b⟩⟩
  | .or φ ψ, Γ => by
    rw [show check S dle Γ (.or φ ψ) = (check S dle Γ φ && check S dle Γ ψ) from rfl,
      Bool.and_eq_true, check_iff φ Γ, check_iff ψ Γ]
    exact ⟨fun ⟨a, b⟩ => .or a b, fun h => by cases h with | or a b => exact ⟨a, b⟩⟩
  | .imp φ ψ, Γ => by
    rw [show check S dle Γ (.imp φ ψ) = (check S dle Γ φ && check S dle Γ ψ) from rfl,
      Bool.and_eq_true, check_iff φ Γ, check_iff ψ Γ]
    exact ⟨fun ⟨a, b⟩ => .imp a b, fun h => by cases h with | imp a b => exact ⟨a, b⟩⟩
  | .quant d n C Q, Γ => by
    rw [show check S dle Γ (.quant d n C Q) =
      (check S dle (S.noun n :: Γ) C && check S dle (S.noun n :: Γ) Q) from rfl,
      Bool.and_eq_true, check_iff C, check_iff Q]
    exact ⟨fun ⟨a, b⟩ => .quant a b, fun h => by cases h with | quant a b => exact ⟨a, b⟩⟩
  | .more n C Q R, Γ => by
    rw [show check S dle Γ (.more n C Q R) = (check S dle (S.noun n :: Γ) C &&
      check S dle (S.noun n :: Γ) Q && check S dle (S.noun n :: Γ) R) from rfl,
      Bool.and_eq_true, Bool.and_eq_true, check_iff C, check_iff Q, check_iff R]
    exact ⟨fun ⟨⟨a, b⟩, c⟩ => .more a b c,
      fun h => by cases h with | more a b c => exact ⟨⟨a, b⟩, c⟩⟩

/-- **Type checking is decidable** in any lexicon with decidable
subtyping. -/
def wtDecidable (Γ : List S.Ty) (φ : Form Noun Verb Rel Name) : Decidable (WT S Γ φ) :=
  decidable_of_iff _ (check_iff S dle φ Γ)

/-- ... and so is it with nouns as predicates over sorts. -/
def wtSortsDecidable (Γ : List S.Ty) (φ : Form Noun Verb Rel Name) :
    Decidable (WT S.sorts (Γ.map S.prof) φ) :=
  decidable_of_iff _ ((check_iff S dle φ Γ).trans (wt_sorts_iff S Γ φ))

end

/-! ## (*) as a theorem about models -/

/-- In a typed model's predicate reading, being an `n` is being in the
image of `n`'s type. -/
theorem both_shadow (M : TModel Noun Verb Name) (n : Noun) (x : M.A) :
    M.shadow.noun n x ↔ ∃ y, M.emb n y = x :=
  Iff.rfl

/-- In a predicate model's typed reading, being in the image of `n`'s
type is being an `n`. -/
theorem both_lift (M : PModel Noun Verb Name) (n : Noun) (x : M.A) :
    (∃ y, M.lift.emb n y = x) ↔ M.noun n x :=
  lift_isA M n x

/-! ## The checker at work: "heavy book" -/

/-- Subtyping in `Modifiers.lean`'s lexicon is decidable. -/
def hbDec : ∀ a b, Decidable (Modifiers.hbSig.le a b) :=
  fun a b => inferInstanceAs (Decidable (Modifiers.leB a b = true))

/-- The checker accepts "John picked up and mastered every heavy book",
by computation. -/
theorem heavy_book_checked : check Modifiers.hbSig hbDec [] Modifiers.heavyBook = true := by
  decide

end FraCaS.Encodings.TypeCheck
