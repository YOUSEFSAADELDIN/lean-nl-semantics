import LeanNLSemantics.MTT.Individuation
import EndToEnd.Encodings.Equivalence

/-!
# Phase 4: individuation and copredication

FraCaS does not test the cases Chatzikyriakidis & Luo use to argue for
nouns as types. This file states three small problems in their style, in
three encodings, and settles each claim in Lean. It reads the MTT core
(`LeanNLSemantics/MTT/Individuation.lean`, `DotTypes.lean`) and changes
nothing there.

The problems, about a shelf of books:

- **I1** "John picked up two books. John mastered every book he picked
  up." ⇒ "John mastered two books." Not entailed: the two books he
  picked up may be two copies of one text. This is the contrast `MTT.v`
  Part 7 states (CL20 §5.3.1, ported as `MTT.two_books_phy` and
  `MTT.not_two_books_info`): "picked up two books" counts physical
  objects, "mastered two books" counts texts.
- **I2** "John mastered two books. John picked up every book he
  mastered." ⇒ "John picked up two books." The mirror image: not
  entailed if one volume can hold two texts (an anthology).
- **C1** "John picked up and mastered some book." ⇒ "John mastered some
  book." Copredication without counting, as a control.

The encodings:

- **P**: nouns as predicates over one domain of individuals, counted by
  `AtLeast`, as in the FraCaS corpus and the pipeline. "Picked up" and
  "mastered" are predicates of the same individuals.
- **P+**: P with a stipulated function `textOf` and a determiner that
  counts through it, so "mastered two books" counts texts.
- **M**: nouns as types with dot types (`MTT.DotType`, as in
  `DotTypes.lean`): a book has a physical and an informational aspect,
  "picked up" is a predicate of the first, "mastered" of the second, and
  each counts by its own aspect's identity (`TwoBy`, `MTT.v`'s
  `countGe2` restricted to a predicate).

Results:

- P makes I1 and I2 valid (`P_I1_valid`, `P_I2_valid`). With one domain
  and one count, it cannot tell "picked up two books" from "mastered two
  books" when the same books are picked up and mastered. So on I1 it
  commits to "yes", the wrong answer.
- M leaves both open (`M_I1_not_valid`, `M_I2_not_valid`; I1's
  countermodel is `MTT.v`'s own two copies of one text). Each becomes
  valid under one stated lexical postulate: I1 if each text has one
  volume, I2 if each volume has one text (`M_I1_valid_of`,
  `M_I2_valid_of`). P assumes both without saying so.
- P+ also leaves I1 open (`P2_I1_not_valid`). Predicates can match M,
  but only by adding an identity function to the lexicon and a
  determiner that counts through it: MTT's identity criterion,
  restated.
- Copredication alone changes nothing: C1 is valid in P and in M
  (`P_C1_valid`, `M_C1_valid`). The encodings part only when
  copredication meets counting.
-/

namespace FraCaS.Encodings.Copredication
open FraCaS.Section1
open FraCaS.Encodings.Equivalence (card_filter_mono)

/-! ## Counting by an identity criterion -/

/-- "At least two of the `N`s that are `P`", where two count as two when
`f` tells them apart: counting by the identity criterion "same `f`-value". -/
def TwoBy {N B : Type} (f : N → B) (P : N → Prop) : Prop :=
  ∃ x y, P x ∧ P y ∧ f x ≠ f y

/-- Unrestricted, `TwoBy` is `MTT.v`'s `countGe2` for the criterion
"same `f`-value". -/
theorem twoBy_iff_countGe2 {N B : Type} (f : N → B) :
    TwoBy f (fun _ => True) ↔ MTT.countGe2 N (fun a b => f a = f b) :=
  ⟨fun ⟨x, y, _, _, h⟩ => ⟨x, y, h⟩, fun ⟨x, y, h⟩ => ⟨x, y, trivial, trivial, h⟩⟩

/-- With the individuals' own identity as the criterion, `TwoBy` is the
corpus's `AtLeast 2`. -/
theorem atLeast_two_iff {A : Type} [Fintype A] (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] :
    AtLeast 2 P Q ↔ TwoBy id (fun x => P x ∧ Q x) := by
  unfold AtLeast card
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
    exact ⟨a, b, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hab⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    exact Finset.one_lt_card.mpr
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩,
        b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, hab⟩

/-! ## P: one domain, one count -/

def P_I1 : Prop :=
  ∀ {A : Type} [Fintype A] (book pickedUp mastered : A → Prop)
    [DecidablePred fun x => book x ∧ pickedUp x] [DecidablePred fun x => book x ∧ mastered x],
    AtLeast 2 book pickedUp → (∀ x, book x → pickedUp x → mastered x) → AtLeast 2 book mastered

def P_I2 : Prop :=
  ∀ {A : Type} [Fintype A] (book pickedUp mastered : A → Prop)
    [DecidablePred fun x => book x ∧ mastered x] [DecidablePred fun x => book x ∧ pickedUp x],
    AtLeast 2 book mastered → (∀ x, book x → mastered x → pickedUp x) → AtLeast 2 book pickedUp

def P_C1 : Prop :=
  ∀ {A : Type} (book pickedUp mastered : A → Prop),
    Some book (fun x => pickedUp x ∧ mastered x) → Some book mastered

theorem P_I1_valid : P_I1 := by
  unfold P_I1
  intro A _ book pickedUp mastered _ _ h1 h2
  exact le_trans h1 (card_filter_mono (by intro x hx; exact ⟨hx.1, h2 x hx.1 hx.2⟩))

theorem P_I2_valid : P_I2 := by
  unfold P_I2
  intro A _ book pickedUp mastered _ _ h1 h2
  exact le_trans h1 (card_filter_mono (by intro x hx; exact ⟨hx.1, h2 x hx.1 hx.2⟩))

theorem P_C1_valid : P_C1 := by
  unfold P_C1
  rintro _ book _ _ ⟨x, hb, -, h⟩
  exact ⟨x, hb, h⟩

/-! ## P+: predicates with a stipulated identity function -/

def P2_I1 : Prop :=
  ∀ {A : Type} [Fintype A] (book pickedUp mastered : A → Prop) (textOf : A → A)
    [DecidablePred fun x => book x ∧ pickedUp x],
    AtLeast 2 book pickedUp → (∀ x, book x → pickedUp x → mastered x) →
    TwoBy textOf (fun x => book x ∧ mastered x)

/-- Two copies, one text. -/
theorem P2_I1_not_valid : ¬ P2_I1 := by
  intro h
  unfold P2_I1 at h
  obtain ⟨x, y, -, -, hxy⟩ := @h Bool _ (fun _ => True) (fun _ => True) (fun _ => True)
    (fun _ => false) _
    ((atLeast_two_iff _ _).mpr
      ⟨true, false, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, (by decide : true ≠ false)⟩)
    (fun _ _ _ => trivial)
  exact hxy rfl

/-! ## M: dot types, each verb counting by its own aspect -/

def M_I1 : Prop :=
  ∀ (Phy Info Book : Type) (bk : Book → MTT.DotType Phy Info)
    (pickedUp : Phy → Prop) (mastered : Info → Prop),
    TwoBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy) →
    (∀ b, pickedUp (bk b).phy → mastered (bk b).info) →
    TwoBy (fun b => (bk b).info) (fun b => mastered (bk b).info)

def M_I2 : Prop :=
  ∀ (Phy Info Book : Type) (bk : Book → MTT.DotType Phy Info)
    (pickedUp : Phy → Prop) (mastered : Info → Prop),
    TwoBy (fun b => (bk b).info) (fun b => mastered (bk b).info) →
    (∀ b, mastered (bk b).info → pickedUp (bk b).phy) →
    TwoBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy)

def M_C1 : Prop :=
  ∀ (Phy Info Book : Type) (bk : Book → MTT.DotType Phy Info)
    (pickedUp : Phy → Prop) (mastered : Info → Prop),
    (∃ b, pickedUp (bk b).phy ∧ mastered (bk b).info) → ∃ b, mastered (bk b).info

/-- I1's countermodel is `MTT.v`'s own: two physical copies of one text
(`MTT.Book0`), told apart physically (`MTT.two_books_phy`) and not
informationally (`MTT.not_two_books_info`). -/
theorem M_I1_not_valid : ¬ M_I1 := by
  intro h
  unfold M_I1 at h
  have two_phy : TwoBy (fun b => (MTT.bk0 b).phy) (fun _ => True) :=
    (twoBy_iff_countGe2 _).mpr MTT.two_books_phy
  have := h MTT.Phy0 MTT.Info0 MTT.Book0 MTT.bk0 (fun _ => True) (fun _ => True)
    two_phy (fun _ _ => trivial)
  exact MTT.not_two_books_info ((twoBy_iff_countGe2 _).mp this)

/-- I2's countermodel: one volume holding two texts. -/
theorem M_I2_not_valid : ¬ M_I2 := by
  intro h
  unfold M_I2 at h
  obtain ⟨x, y, -, -, hxy⟩ := h Unit Bool Bool (fun b => ⟨(), b⟩) (fun _ => True) (fun _ => True)
    ⟨true, false, trivial, trivial, (by decide : true ≠ false)⟩ (fun _ _ => trivial)
  exact hxy rfl

/-- Each text has one volume: books that agree informationally agree
physically. -/
def OneVolumePerText {Phy Info Book : Type} (bk : Book → MTT.DotType Phy Info) : Prop :=
  ∀ b b', (bk b).info = (bk b').info → (bk b).phy = (bk b').phy

/-- Each volume has one text: books that agree physically agree
informationally. -/
def OneTextPerVolume {Phy Info Book : Type} (bk : Book → MTT.DotType Phy Info) : Prop :=
  ∀ b b', (bk b).phy = (bk b').phy → (bk b).info = (bk b').info

/-- I1 holds in M once each text has one volume. -/
theorem M_I1_valid_of {Phy Info Book : Type} (bk : Book → MTT.DotType Phy Info)
    (hvol : OneVolumePerText bk) (pickedUp : Phy → Prop) (mastered : Info → Prop) :
    TwoBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy) →
    (∀ b, pickedUp (bk b).phy → mastered (bk b).info) →
    TwoBy (fun b => (bk b).info) (fun b => mastered (bk b).info) := by
  rintro ⟨x, y, hx, hy, hxy⟩ hm
  exact ⟨x, y, hm x hx, hm y hy, fun h => hxy (hvol x y h)⟩

/-- I2 holds in M once each volume has one text. -/
theorem M_I2_valid_of {Phy Info Book : Type} (bk : Book → MTT.DotType Phy Info)
    (htext : OneTextPerVolume bk) (pickedUp : Phy → Prop) (mastered : Info → Prop) :
    TwoBy (fun b => (bk b).info) (fun b => mastered (bk b).info) →
    (∀ b, mastered (bk b).info → pickedUp (bk b).phy) →
    TwoBy (fun b => (bk b).phy) (fun b => pickedUp (bk b).phy) := by
  rintro ⟨x, y, hx, hy, hxy⟩ hp
  exact ⟨x, y, hp x hx, hp y hy, fun h => hxy (htext x y h)⟩

theorem M_C1_valid : M_C1 := by
  unfold M_C1
  rintro _ _ _ bk _ _ ⟨b, -, h⟩
  exact ⟨b, h⟩

/-! The MTT core declares `Physical` and `Informational` as axioms
(`DotTypes.lean`); nothing here uses them. Expected for each: no axioms
beyond Lean's standard three. -/
#print axioms M_I1_not_valid
#print axioms M_I2_not_valid
#print axioms P_I1_valid
#print axioms P2_I1_not_valid

end FraCaS.Encodings.Copredication
