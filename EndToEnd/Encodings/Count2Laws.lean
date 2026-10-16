import EndToEnd.Encodings.ForbiddenLaws
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Laws that characterize counting by two criteria

`ForbiddenLaws.lean` proves laws that every counting function of a noun
with two criteria obeys. This file proves the converse when each
individual is one thing, and shows that the claw law is not implied by
the others.

**The class.** `IsCount2Self f`: `f` counts individuals by two criteria,
`f P = count2 c1 c2 P` for some `c1`, `c2` on the individuals. Write
`pairLe f x y` for `f {x, y} ≤ 1`: `x` and `y` count at most one
together.

**The laws** (`Singles`, `PairDet`, `ClawLaw`, `DiamondLaw`,
`OddCycleLaw`):

- each individual counts one;
- `f` is determined by pairs: `f P` is the size of a largest set of `P`s
  no two of which count at most one together (`pairCount`);
- the claw law, for individuals;
- the diamond law: if `x`, `y` count at most one together, and so do
  each of `z`, `w` with each of `x`, `y`, but `z`, `w` count two, then
  `x` and `y` are twins (everyone counts at most one with `x` exactly when
  with `y`);
- the odd-cycle laws of every length, for individuals.

**`isCount2Self_iff`.** `f` counts individuals by two criteria exactly
when it obeys these laws.

How the converse goes (`union_of_two_general`). Write `S` for
`pairLe f`. Merge twins (`twinSetoid`). Then the diamond law says the
common `S`-neighbours of two related individuals are pairwise related, a
*line* (`IsLine`). Each individual lies on at most two lines, by the
claw law (`three_lines`). Two lines are adjacent when they share an
individual (`lineAdj`). An odd closed walk of lines gives an odd cycle
of individuals. The odd-cycle law then finds a backtrack, which
shortens the walk by two (`shorten`), or a contradiction (`no_odd`). So
the lines can be coloured with two colours (Mathlib's
`two_colorable_iff_forall_loop_even`), and "together on a line of
colour `b`" is an equivalence relation for each `b`. Those two
equivalence relations are the two criteria (`union_of_two`).

**`claw_independent`.** Counting the largest set of non-neighbours in a
star with three leaves (`fStar`) obeys every law except the claw law,
so it is not counting by two criteria, with one thing per individual or
with several (`fStar_not_isCount2`).
-/

namespace FraCaS.Encodings.Count2Laws
open FraCaS.Encodings.TwoCriteria
open FraCaS.Encodings.MinCoverage (IsCount2)
open FraCaS.Encodings.OddCycle (le_one_iff_pairwise one_le_count2_iff)
open FraCaS.Encodings.ForbiddenLaws
open Classical

/-! ## A relation that is the union of two equivalence relations -/

section Core
variable {Q : Type}

/-- The laws, for a relation `S` (twins already merged into `clique`). -/
structure Hyp (S : Q → Q → Prop) : Prop where
  refl : ∀ x, S x x
  symm : ∀ x y, S x y → S y x
  claw : ∀ x y z w, S x y → S x z → S x w → S y z ∨ S y w ∨ S z w
  clique : ∀ x y z w, S x y → x ≠ y → S z x → S z y → S w x → S w y → S z w
  odd : ∀ (m : ℕ) (v : ZMod (2 * m + 1) → Q), (∀ i, S (v i) (v (i + 1))) →
    ∃ i, S (v i) (v (i + 2))

/-- The common neighbours of `x` and `y`. -/
abbrev common (S : Q → Q → Prop) (x y : Q) : Q → Prop := fun u => S u x ∧ S u y

/-- A line: the common neighbours of two distinct related individuals. -/
abbrev IsLine (S : Q → Q → Prop) (s : Q → Prop) : Prop :=
  ∃ x y, x ≠ y ∧ S x y ∧ s = common S x y

variable {S : Q → Q → Prop}

theorem line_S (H : Hyp S) {s : Q → Prop} (hs : IsLine S s) {u u' : Q} (hu : s u)
    (hu' : s u') : S u u' := by
  obtain ⟨x, y, hne, hxy, rfl⟩ := hs
  obtain ⟨h1, h2⟩ := hu
  obtain ⟨h3, h4⟩ := hu'
  exact H.clique x y u u' hxy hne h1 h2 h3 h4

/-- A line is the line of any two of its distinct individuals. -/
theorem line_common (H : Hyp S) {s : Q → Prop} (hs : IsLine S s) {a b : Q} (hab : a ≠ b)
    (ha : s a) (hb : s b) : s = common S a b := by
  have hSab : S a b := line_S H hs ha hb
  obtain ⟨x, y, hne, hxy, rfl⟩ := hs
  obtain ⟨hax, hay⟩ := ha
  obtain ⟨hbx, hby⟩ := hb
  funext u
  apply propext
  constructor
  · rintro ⟨hux, huy⟩
    exact ⟨H.clique x y u a hxy hne hux huy hax hay, H.clique x y u b hxy hne hux huy hbx hby⟩
  · rintro ⟨hua, hub⟩
    exact ⟨H.clique a b u x hSab hab hua hub (H.symm a x hax) (H.symm b x hbx),
      H.clique a b u y hSab hab hua hub (H.symm a y hay) (H.symm b y hby)⟩

/-- Two lines sharing two distinct individuals are equal. -/
theorem line_eq (H : Hyp S) {s t : Q → Prop} (hs : IsLine S s) (ht : IsLine S t) {a b : Q}
    (hab : a ≠ b) (hsa : s a) (hsb : s b) (hta : t a) (htb : t b) : s = t :=
  (line_common H hs hab hsa hsb).trans (line_common H ht hab hta htb).symm

/-- A line has an individual other than any given one. -/
theorem line_other (H : Hyp S) {s : Q → Prop} (hs : IsLine S s) (x : Q) :
    ∃ a, s a ∧ a ≠ x := by
  obtain ⟨x0, y0, hne, hxy, rfl⟩ := hs
  by_cases h : x0 = x
  · exact ⟨y0, ⟨H.symm x0 y0 hxy, H.refl y0⟩, fun e => hne (h.trans e.symm)⟩
  · exact ⟨x0, ⟨H.refl x0, hxy⟩, h⟩

/-- Two lines through `x`, containing related individuals `a`, `b` other
than `x`, are equal. -/
theorem line_merge (H : Hyp S) {s t : Q → Prop} (hs : IsLine S s) (ht : IsLine S t)
    {x a b : Q} (hsx : s x) (hsa : s a) (htx : t x) (htb : t b) (hax : a ≠ x) (hbx : b ≠ x)
    (hab : S a b) : s = t := by
  have hK : s = common S x a := line_common H hs (Ne.symm hax) hsx hsa
  have hsb : s b := by
    rw [hK]
    exact ⟨H.symm x b (line_S H ht htx htb), H.symm a b hab⟩
  exact line_eq H hs ht (Ne.symm hbx) hsx hsb htx htb

/-- **At most two lines through an individual** (the claw law). -/
theorem three_lines (H : Hyp S) {s1 s2 s3 : Q → Prop} (h1 : IsLine S s1) (h2 : IsLine S s2)
    (h3 : IsLine S s3) {x : Q} (hx1 : s1 x) (hx2 : s2 x) (hx3 : s3 x) :
    s1 = s2 ∨ s1 = s3 ∨ s2 = s3 := by
  obtain ⟨a1, ha1, hn1⟩ := line_other H h1 x
  obtain ⟨a2, ha2, hn2⟩ := line_other H h2 x
  obtain ⟨a3, ha3, hn3⟩ := line_other H h3 x
  rcases H.claw x a1 a2 a3 (line_S H h1 hx1 ha1) (line_S H h2 hx2 ha2) (line_S H h3 hx3 ha3)
    with h | h | h
  · exact Or.inl (line_merge H h1 h2 hx1 ha1 hx2 ha2 hn1 hn2 h)
  · exact Or.inr (Or.inl (line_merge H h1 h3 hx1 ha1 hx3 ha3 hn1 hn3 h))
  · exact Or.inr (Or.inr (line_merge H h2 h3 hx2 ha2 hx3 ha3 hn2 hn3 h))

variable (S) in
/-- The lines, as a type. -/
abbrev LineT := {s : Q → Prop // IsLine S s}

variable (S) in
/-- Two lines are adjacent when they are distinct and share an individual. -/
def lineAdj : SimpleGraph (LineT S) where
  Adj L M := L ≠ M ∧ ∃ x, L.1 x ∧ M.1 x
  symm := ⟨fun L M h => by
    obtain ⟨hne, x, h1, h2⟩ := h
    exact ⟨Ne.symm hne, x, h2, h1⟩⟩
  loopless := ⟨fun L h => by
    obtain ⟨hne, -⟩ := h
    exact hne rfl⟩

theorem lineAdj_iff {L M : LineT S} : (lineAdj S).Adj L M ↔ L ≠ M ∧ ∃ x, L.1 x ∧ M.1 x :=
  Iff.rfl

/-- **Shortening a closed walk at a backtrack.** A closed walk of length
`2m + 3` that returns to a vertex two steps later gives a closed walk of
length `2m + 1`. -/
theorem shorten {α : Type} (R : α → α → Prop) (m : ℕ) (L : ZMod (2 * (m + 1) + 1) → α)
    (hL : ∀ i, R (L i) (L (i + 1))) (r : ZMod (2 * (m + 1) + 1)) (hr : L r = L (r + 2)) :
    ∃ L' : ZMod (2 * m + 1) → α, ∀ i, R (L' i) (L' (i + 1)) := by
  refine ⟨fun k => L (r + ((k.val + 2 : ℕ) : ZMod (2 * (m + 1) + 1))), fun k => ?_⟩
  have hk : k.val < 2 * m + 1 := ZMod.val_lt k
  have hk1 : (k + 1).val = (k.val + 1) % (2 * m + 1) := by
    have e : k + 1 = ((k.val + 1 : ℕ) : ZMod (2 * m + 1)) := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    rw [e, ZMod.val_natCast]
  show R (L (r + ((k.val + 2 : ℕ) : ZMod _))) (L (r + (((k + 1).val + 2 : ℕ) : ZMod _)))
  by_cases hlt : k.val + 1 < 2 * m + 1
  · rw [hk1, Nat.mod_eq_of_lt hlt]
    have e : r + ((k.val + 1 + 2 : ℕ) : ZMod (2 * (m + 1) + 1)) =
        r + ((k.val + 2 : ℕ) : ZMod (2 * (m + 1) + 1)) + 1 := by
      (try push_cast) <;> ring
    rw [e]
    exact hL _
  · have hkv : k.val = 2 * m := by omega
    have h0 : (k + 1).val = 0 := by
      rw [hk1, show k.val + 1 = 2 * m + 1 by omega, Nat.mod_self]
    rw [h0, hkv]
    have e0 : ((2 * m + 2 : ℕ) : ZMod (2 * (m + 1) + 1)) + 1 = 0 := by
      rw [← ZMod.natCast_self (2 * (m + 1) + 1)]
      (try push_cast) <;> ring
    have e1 : r + ((0 + 2 : ℕ) : ZMod (2 * (m + 1) + 1)) = r + 2 := by
      (try push_cast) <;> ring
    have e2 : r + ((2 * m + 2 : ℕ) : ZMod (2 * (m + 1) + 1)) + 1 = r := by
      rw [add_assoc, e0, add_zero]
    rw [e1, ← hr]
    have := hL (r + ((2 * m + 2 : ℕ) : ZMod (2 * (m + 1) + 1)))
    rwa [e2] at this

/-- **No odd closed walk of lines.** -/
theorem no_odd (H : Hyp S) : ∀ (m : ℕ) (L : ZMod (2 * m + 1) → LineT S),
    (∀ i, (lineAdj S).Adj (L i) (L (i + 1))) → False := by
  intro m
  induction m with
  | zero =>
    intro L hL
    have h1 : (1 : ZMod (2 * 0 + 1)) = 0 := by
      have e := ZMod.natCast_self (2 * 0 + 1)
      change ((0 + 1 : ℕ) : ZMod (2 * 0 + 1)) = 0 at e
      rwa [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] at e
    obtain ⟨hne, -⟩ := lineAdj_iff.mp (hL 0)
    exact hne (by rw [h1, add_zero])
  | succ m ih =>
    intro L hL
    -- an individual shared by each pair of consecutive lines
    have hp : ∀ i, ∃ x, (L i).1 x ∧ (L (i + 1)).1 x := fun i => (lineAdj_iff.mp (hL i)).2
    choose p hp using hp
    have hS : ∀ i, S (p i) (p (i + 1)) := fun i =>
      line_S H (L (i + 1)).2 (hp i).2 (hp (i + 1)).1
    obtain ⟨i, hi⟩ := H.odd (m + 1) p hS
    have e2 : i + 1 + 1 = i + 2 := by ring
    have e3 : i + 2 + 1 = i + 3 := by ring
    have e4 : i + 1 + 2 = i + 3 := by ring
    have ha0 : (L i).1 (p i) := (hp i).1
    have ha1 : (L (i + 1)).1 (p i) := (hp i).2
    have hb1 : (L (i + 1)).1 (p (i + 1)) := (hp (i + 1)).1
    have hb2 : (L (i + 2)).1 (p (i + 1)) := by
      rw [← e2]
      exact (hp (i + 1)).2
    have hc2 : (L (i + 2)).1 (p (i + 2)) := (hp (i + 2)).1
    have hc3 : (L (i + 3)).1 (p (i + 2)) := by
      rw [← e3]
      exact (hp (i + 2)).2
    have n01 : L i ≠ L (i + 1) := (lineAdj_iff.mp (hL i)).1
    have n12 : L (i + 1) ≠ L (i + 2) := by
      rw [← e2]
      exact (lineAdj_iff.mp (hL (i + 1))).1
    have n23 : L (i + 2) ≠ L (i + 3) := by
      rw [← e3]
      exact (lineAdj_iff.mp (hL (i + 2))).1
    -- the odd-cycle law gives a backtrack, or a contradiction
    have hback : ∃ r, L r = L (r + 2) := by
      by_cases hab : p i = p (i + 1)
      · have ha2 : (L (i + 2)).1 (p i) := by
          rw [hab]
          exact hb2
        rcases three_lines H (L i).2 (L (i + 1)).2 (L (i + 2)).2 ha0 ha1 ha2 with h | h | h
        · exact absurd (Subtype.ext h) n01
        · exact ⟨i, Subtype.ext h⟩
        · exact absurd (Subtype.ext h) n12
      by_cases hbc : p (i + 1) = p (i + 2)
      · have hb3 : (L (i + 3)).1 (p (i + 1)) := by
          rw [hbc]
          exact hc3
        rcases three_lines H (L (i + 1)).2 (L (i + 2)).2 (L (i + 3)).2 hb1 hb2 hb3
          with h | h | h
        · exact absurd (Subtype.ext h) n12
        · refine ⟨i + 1, ?_⟩
          rw [e4]
          exact Subtype.ext h
        · exact absurd (Subtype.ext h) n23
      by_cases hac : p i = p (i + 2)
      · have ha2 : (L (i + 2)).1 (p i) := by
          rw [hac]
          exact hc2
        rcases three_lines H (L i).2 (L (i + 1)).2 (L (i + 2)).2 ha0 ha1 ha2 with h | h | h
        · exact absurd (Subtype.ext h) n01
        · exact ⟨i, Subtype.ext h⟩
        · exact absurd (Subtype.ext h) n12
      -- three distinct individuals, pairwise related: one line holds them all
      exfalso
      have hSbc : S (p (i + 1)) (p (i + 2)) := by
        rw [← e2]
        exact hS (i + 1)
      have hK : (L (i + 1)).1 = common S (p i) (p (i + 1)) :=
        line_common H (L (i + 1)).2 hab ha1 hb1
      have hc1 : (L (i + 1)).1 (p (i + 2)) := by
        rw [hK]
        exact ⟨H.symm _ _ hi, H.symm _ _ hSbc⟩
      exact n12 (Subtype.ext (line_eq H (L (i + 1)).2 (L (i + 2)).2 hbc hb1 hc1 hb2 hc2))
    obtain ⟨r, hr⟩ := hback
    obtain ⟨L', hL'⟩ := shorten (lineAdj S).Adj m L hL r hr
    exact ih L' hL'

/-- **The lines can be coloured with two colours.** -/
theorem lines_colorable (H : Hyp S) : (lineAdj S).Colorable 2 := by
  rw [SimpleGraph.two_colorable_iff_forall_loop_even]
  intro u w
  by_contra hev
  obtain ⟨m, hm⟩ : Odd w.length := Nat.not_even_iff_odd.mp hev
  refine no_odd H m (fun i => w.getVert i.val) (fun i => ?_)
  have hi : i.val < 2 * m + 1 := ZMod.val_lt i
  have hi1 : (i + 1).val = (i.val + 1) % (2 * m + 1) := by
    have e : i + 1 = ((i.val + 1 : ℕ) : ZMod (2 * m + 1)) := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    rw [e, ZMod.val_natCast]
  show (lineAdj S).Adj (w.getVert i.val) (w.getVert (i + 1).val)
  have hadj := w.adj_getVert_succ (show i.val < w.length by omega)
  by_cases hlt : i.val + 1 < 2 * m + 1
  · rw [hi1, Nat.mod_eq_of_lt hlt]
    exact hadj
  · rw [hi1, show i.val + 1 = 2 * m + 1 by omega, Nat.mod_self, SimpleGraph.Walk.getVert_zero]
    rwa [show i.val + 1 = w.length by omega, SimpleGraph.Walk.getVert_length] at hadj

variable (S) in
/-- Equal, or together on a line of colour `b`. -/
abbrev SameCol (col : LineT S → Fin 2) (b : Fin 2) (x y : Q) : Prop :=
  x = y ∨ ∃ L : LineT S, col L = b ∧ L.1 x ∧ L.1 y

/-- **The relation is the union of two equivalence relations.** -/
theorem union_of_two (H : Hyp S) :
    ∃ (K1 K2 : Type) (c1 : Q → K1) (c2 : Q → K2),
      ∀ x y, S x y ↔ c1 x = c1 y ∨ c2 x = c2 y := by
  obtain ⟨col⟩ := lines_colorable H
  have hRsymm : ∀ b x y, SameCol S col b x y → SameCol S col b y x := by
    intro b x y h
    rcases h with h | ⟨L, hL, hLx, hLy⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨L, hL, hLy, hLx⟩
  have hRtrans : ∀ b x y z, SameCol S col b x y → SameCol S col b y z →
      SameCol S col b x z := by
    intro b x y z hxy hyz
    rcases hxy with hxy | ⟨L, hL, hLx, hLy⟩
    · subst hxy
      exact hyz
    rcases hyz with hyz | ⟨M, hM, hMy, hMz⟩
    · subst hyz
      exact Or.inr ⟨L, hL, hLx, hLy⟩
    by_cases hLM : L = M
    · subst hLM
      exact Or.inr ⟨L, hL, hLx, hMz⟩
    · exact absurd (hL.trans hM.symm) (col.valid (lineAdj_iff.mpr ⟨hLM, y, hLy, hMy⟩))
  have key : ∀ b x y, (SameCol S col b x = SameCol S col b y) ↔ SameCol S col b x y := by
    intro b x y
    constructor
    · intro h
      have hy := congrFun h y
      rw [hy]
      exact Or.inl rfl
    · intro h
      funext z
      exact propext ⟨fun hz => hRtrans b y x z (hRsymm b x y h) hz,
        fun hz => hRtrans b x y z h hz⟩
  refine ⟨Q → Prop, Q → Prop, SameCol S col 0, SameCol S col 1, fun x y => ?_⟩
  have main : S x y ↔ SameCol S col 0 x y ∨ SameCol S col 1 x y := by
    constructor
    · intro hS
      by_cases hxy : x = y
      · exact Or.inl (Or.inl hxy)
      · have hl : IsLine S (common S x y) := ⟨x, y, hxy, hS, rfl⟩
        have hx : common S x y x := ⟨H.refl x, hS⟩
        have hy : common S x y y := ⟨H.symm x y hS, H.refl y⟩
        have h2 : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
        rcases h2 (col ⟨common S x y, hl⟩) with h | h
        · exact Or.inl (Or.inr ⟨⟨common S x y, hl⟩, h, hx, hy⟩)
        · exact Or.inr (Or.inr ⟨⟨common S x y, hl⟩, h, hx, hy⟩)
    · rintro (h | h) <;> rcases h with h | ⟨L, -, hLx, hLy⟩
      all_goals first
        | (subst h; exact H.refl _)
        | exact line_S H L.2 hLx hLy
  exact main.trans (or_congr (key 0 x y).symm (key 1 x y).symm)

end Core

/-! ## With twins -/

/-- Twins: related to the same individuals. -/
def twinSetoid {A : Type} (S : A → A → Prop) : Setoid A where
  r a b := ∀ u, S u a ↔ S u b
  iseqv := ⟨fun _ _ => Iff.rfl, fun h u => (h u).symm, fun h h' u => (h u).trans (h' u)⟩

theorem twin_S {A : Type} {S : A → A → Prop} (hsymm : ∀ x y, S x y → S y x) {a a' b b' : A}
    (ha : ∀ u, S u a ↔ S u a') (hb : ∀ u, S u b ↔ S u b') : S a b ↔ S a' b' := by
  constructor
  · intro h
    exact (hb a').mp (hsymm _ _ ((ha b).mp (hsymm _ _ h)))
  · intro h
    exact hsymm _ _ ((ha b).mpr (hsymm _ _ ((hb a').mpr h)))

/-- **A reflexive, symmetric relation obeying the claw, diamond and
odd-cycle laws is the union of two equivalence relations.** -/
theorem union_of_two_general {A : Type} (S : A → A → Prop) (hrefl : ∀ x, S x x)
    (hsymm : ∀ x y, S x y → S y x)
    (hclaw : ∀ x y z w, S x y → S x z → S x w → S y z ∨ S y w ∨ S z w)
    (hdiam : ∀ x y z w, S x y → S z x → S z y → S w x → S w y → ¬ S z w →
      ∀ u, S u x ↔ S u y)
    (hodd : ∀ (m : ℕ) (v : ZMod (2 * m + 1) → A), (∀ i, S (v i) (v (i + 1))) →
      ∃ i, S (v i) (v (i + 2))) :
    ∃ (K1 K2 : Type) (c1 : A → K1) (c2 : A → K2),
      ∀ x y, S x y ↔ c1 x = c1 y ∨ c2 x = c2 y := by
  have H : Hyp (fun q r : Quotient (twinSetoid S) => S q.out r.out) :=
    { refl := fun q => hrefl q.out
      symm := fun q r h => hsymm _ _ h
      claw := fun x y z w h1 h2 h3 => hclaw _ _ _ _ h1 h2 h3
      clique := fun x y z w hxy hne hzx hzy hwx hwy => by
        by_contra hzw
        apply hne
        have ht := hdiam _ _ _ _ hxy hzx hzy hwx hwy hzw
        have e : Quotient.mk (twinSetoid S) x.out = Quotient.mk (twinSetoid S) y.out :=
          Quotient.sound ht
        rwa [Quotient.out_eq, Quotient.out_eq] at e
      odd := fun m v hv => hodd m (fun i => (v i).out) hv }
  have hout : ∀ a u, S u (Quotient.mk (twinSetoid S) a).out ↔ S u a := fun a =>
    Quotient.exact (Quotient.out_eq (Quotient.mk (twinSetoid S) a))
  obtain ⟨K1, K2, c1, c2, hc⟩ := union_of_two H
  exact ⟨K1, K2, fun a => c1 (Quotient.mk (twinSetoid S) a),
    fun a => c2 (Quotient.mk (twinSetoid S) a), fun x y =>
      (twin_S hsymm (fun u => (hout x u).symm) (fun u => (hout y u).symm)).trans (hc _ _)⟩

/-! ## Counting functions -/

section Counting
variable {A : Type} [Fintype A]

/-- The size of a largest set of `P`s no two of which are `R`-related. -/
noncomputable def pairCount (R : A → A → Prop) (P : A → Prop) : ℕ :=
  ((Finset.univ.filter P).powerset.filter
    (fun s : Finset A => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ R x y)).sup Finset.card

theorem le_pairCount_iff (R : A → A → Prop) (P : A → Prop) (n : ℕ) :
    n ≤ pairCount R P ↔ ∃ s : Finset A, n ≤ s.card ∧ (∀ x ∈ s, P x) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ R x y := by
  unfold pairCount
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨∅, Nat.zero_le _, by simp, by simp⟩
    · obtain ⟨s, hs, hle⟩ := (Finset.le_sup_iff hn).mp h
      rw [Finset.mem_filter, Finset.mem_powerset] at hs
      exact ⟨s, hle, fun x hx => (Finset.mem_filter.mp (hs.1 hx)).2, hs.2⟩
  · rintro ⟨s, hn, hP, hR⟩
    refine le_trans hn (Finset.le_sup (f := Finset.card) ?_)
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP x hx⟩, hR⟩

/-- Counting by two criteria is counting by "same in one of them". -/
theorem count2_eq_pairCount {K1 K2 : Type} (c1 : A → K1) (c2 : A → K2) (P : A → Prop) :
    count2 c1 c2 P = pairCount (fun x y => c1 x = c1 y ∨ c2 x = c2 y) P := by
  have key : ∀ s : Finset A, (Set.InjOn c1 ↑s ∧ Set.InjOn c2 ↑s) ↔
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ (c1 x = c1 y ∨ c2 x = c2 y) := by
    intro s
    constructor
    · rintro ⟨h1, h2⟩ x hx y hy hne (e | e)
      · exact hne (h1 hx hy e)
      · exact hne (h2 hx hy e)
    · intro h
      refine ⟨?_, ?_⟩
      · intro x hx y hy e
        by_contra hne
        exact h x hx y hy hne (Or.inl e)
      · intro x hx y hy e
        by_contra hne
        exact h x hx y hy hne (Or.inr e)
  apply le_antisymm
  · obtain ⟨s, h1, h2, h3, h4⟩ := (le_count2_iff c1 c2 P _).mp le_rfl
    exact (le_pairCount_iff _ P _).mpr ⟨s, h1, h2, (key s).mp ⟨h3, h4⟩⟩
  · obtain ⟨s, h1, h2, h3⟩ := (le_pairCount_iff (fun x y => c1 x = c1 y ∨ c2 x = c2 y) P _).mp
      le_rfl
    obtain ⟨h4, h5⟩ := (key s).mpr h3
    exact (le_count2_iff c1 c2 P _).mpr ⟨s, h1, h2, h4, h5⟩

theorem pairCount_single (R : A → A → Prop) (x : A) : pairCount R (fun a => a = x) = 1 := by
  apply le_antisymm
  · by_contra h
    obtain ⟨s, hs, hP, -⟩ := (le_pairCount_iff R (fun a => a = x) 2).mp (by omega)
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    exact hab ((show a = x from hP a ha).trans (show b = x from hP b hb).symm)
  · exact (le_pairCount_iff R _ 1).mpr ⟨{x}, by simp, fun a ha => Finset.mem_singleton.mp ha,
      fun a ha b hb hab =>
        absurd ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm) hab⟩

theorem pairCount_pair_le_one {R : A → A → Prop} (hrefl : ∀ x, R x x)
    (hsymm : ∀ x y, R x y → R y x) (x y : A) :
    pairCount R (fun a => a = x ∨ a = y) ≤ 1 ↔ R x y := by
  have hmem : ∀ a, a ∈ ({x, y} : Finset A) → a = x ∨ a = y := fun a ha => by
    rcases Finset.mem_insert.mp ha with e | e
    · exact Or.inl e
    · exact Or.inr (Finset.mem_singleton.mp e)
  constructor
  · intro h
    by_contra hxy
    have hne : x ≠ y := fun e => hxy (by rw [← e]; exact hrefl x)
    have h2 : 2 ≤ pairCount R (fun a => a = x ∨ a = y) := by
      refine (le_pairCount_iff R _ 2).mpr ⟨{x, y}, (Finset.card_pair hne).ge, hmem, ?_⟩
      intro a ha b hb hab
      rcases hmem a ha with e1 | e1 <;> rcases hmem b hb with e2 | e2
      · exact absurd (e1.trans e2.symm) hab
      · rw [e1, e2]
        exact hxy
      · rw [e1, e2]
        exact fun h => hxy (hsymm _ _ h)
      · exact absurd (e1.trans e2.symm) hab
    omega
  · intro hxy
    by_contra h
    obtain ⟨s, hs, hP, hR⟩ := (le_pairCount_iff R (fun a => a = x ∨ a = y) 2).mp (by omega)
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    apply hR a ha b hb hab
    rcases (show a = x ∨ a = y from hP a ha) with e1 | e1 <;>
      rcases (show b = x ∨ b = y from hP b hb) with e2 | e2
    · exact absurd (e1.trans e2.symm) hab
    · rw [e1, e2]
      exact hxy
    · rw [e1, e2]
      exact hsymm _ _ hxy
    · exact absurd (e1.trans e2.symm) hab

/-- `x` and `y` count at most one together. -/
abbrev pairLe (f : (A → Prop) → ℕ) (x y : A) : Prop := f (fun a => a = x ∨ a = y) ≤ 1

/-- Each individual counts one. -/
abbrev Singles (f : (A → Prop) → ℕ) : Prop := ∀ x, f (fun a => a = x) = 1

/-- `f` is determined by which pairs count at most one together. -/
abbrev PairDet (f : (A → Prop) → ℕ) : Prop := ∀ P, f P = pairCount (pairLe f) P

/-- The claw law, for individuals. -/
abbrev ClawLaw (f : (A → Prop) → ℕ) : Prop :=
  ∀ x y z w, pairLe f x y → pairLe f x z → pairLe f x w →
    pairLe f y z ∨ pairLe f y w ∨ pairLe f z w

/-- The diamond law: the two middle individuals of a diamond are twins. -/
abbrev DiamondLaw (f : (A → Prop) → ℕ) : Prop :=
  ∀ x y z w, pairLe f x y → pairLe f z x → pairLe f z y → pairLe f w x → pairLe f w y →
    ¬ pairLe f z w → ∀ u, pairLe f u x ↔ pairLe f u y

/-- The odd-cycle laws of every length, for individuals. -/
abbrev OddCycleLaw (f : (A → Prop) → ℕ) : Prop :=
  ∀ (m : ℕ) (v : ZMod (2 * m + 1) → A), (∀ i, pairLe f (v i) (v (i + 1))) →
    ∃ i, pairLe f (v i) (v (i + 2))

/-- `f` counts individuals, each one thing, by two criteria. -/
def IsCount2Self (f : (A → Prop) → ℕ) : Prop :=
  ∃ (K1 K2 : Type) (c1 : A → K1) (c2 : A → K2), ∀ P, count2 c1 c2 P = f P

theorem pr_count2 {K1 K2 : Type} (c1 : A → K1) (c2 : A → K2) (x y : A) :
    count2 c1 c2 (fun a => a = x ∨ a = y) ≤ 1 ↔ c1 x = c1 y ∨ c2 x = c2 y := by
  rw [le_one_iff_pairwise]
  constructor
  · intro h
    exact h x y (Or.inl rfl) (Or.inr rfl)
  · intro h a b ha hb
    rcases (show a = x ∨ a = y from ha) with e1 | e1 <;>
      rcases (show b = x ∨ b = y from hb) with e2 | e2
    · exact Or.inl (by rw [e1, e2])
    · rw [e1, e2]
      exact h
    · rw [e1, e2]
      rcases h with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm
    · exact Or.inl (by rw [e1, e2])

theorem c_claw {K1 K2 : Type} (c1 : A → K1) (c2 : A → K2) {x y z w : A}
    (h1 : c1 x = c1 y ∨ c2 x = c2 y) (h2 : c1 x = c1 z ∨ c2 x = c2 z)
    (h3 : c1 x = c1 w ∨ c2 x = c2 w) :
    (c1 y = c1 z ∨ c2 y = c2 z) ∨ (c1 y = c1 w ∨ c2 y = c2 w) ∨
      (c1 z = c1 w ∨ c2 z = c2 w) := by
  rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;> rcases h3 with e3 | e3 <;>
    first
    | exact Or.inl (Or.inl (e1.symm.trans e2))
    | exact Or.inl (Or.inr (e1.symm.trans e2))
    | exact Or.inr (Or.inl (Or.inl (e1.symm.trans e3)))
    | exact Or.inr (Or.inl (Or.inr (e1.symm.trans e3)))
    | exact Or.inr (Or.inr (Or.inl (e2.symm.trans e3)))
    | exact Or.inr (Or.inr (Or.inr (e2.symm.trans e3)))

theorem c_diamond {K1 K2 : Type} (c1 : A → K1) (c2 : A → K2) {x y z w : A}
    (hxy : c1 x = c1 y ∨ c2 x = c2 y) (hzx : c1 z = c1 x ∨ c2 z = c2 x)
    (hzy : c1 z = c1 y ∨ c2 z = c2 y) (hwx : c1 w = c1 x ∨ c2 w = c2 x)
    (hwy : c1 w = c1 y ∨ c2 w = c2 y) (hzw : ¬ (c1 z = c1 w ∨ c2 z = c2 w)) (u : A) :
    (c1 u = c1 x ∨ c2 u = c2 x) ↔ (c1 u = c1 y ∨ c2 u = c2 y) := by
  by_cases h1 : c1 x = c1 y
  · by_cases h2 : c2 x = c2 y
    · rw [h1, h2]
    · exfalso
      have hz : c1 z = c1 x := by
        rcases hzx with e | e
        · exact e
        · rcases hzy with e' | e'
          · exact e'.trans h1.symm
          · exact absurd (e.symm.trans e') h2
      have hw : c1 w = c1 x := by
        rcases hwx with e | e
        · exact e
        · rcases hwy with e' | e'
          · exact e'.trans h1.symm
          · exact absurd (e.symm.trans e') h2
      exact hzw (Or.inl (hz.trans hw.symm))
  · have h2 : c2 x = c2 y := hxy.resolve_left h1
    exfalso
    have hz : c2 z = c2 x := by
      rcases hzx with e | e
      · rcases hzy with e' | e'
        · exact absurd (e.symm.trans e') h1
        · exact e'.trans h2.symm
      · exact e
    have hw : c2 w = c2 x := by
      rcases hwx with e | e
      · rcases hwy with e' | e'
        · exact absurd (e.symm.trans e') h1
        · exact e'.trans h2.symm
      · exact e
    exact hzw (Or.inr (hz.trans hw.symm))

theorem c_odd {K1 K2 : Type} (c1 : A → K1) (c2 : A → K2) (m : ℕ) (v : ZMod (2 * m + 1) → A)
    (hv : ∀ i, c1 (v i) = c1 (v (i + 1)) ∨ c2 (v i) = c2 (v (i + 1))) :
    ∃ i, c1 (v i) = c1 (v (i + 2)) ∨ c2 (v i) = c2 (v (i + 2)) := by
  obtain ⟨i, hi⟩ := count2_oddCycle c1 c2 m (fun i a => a = v i)
    (fun i => (one_le_count2_iff c1 c2 _).mpr ⟨v i, rfl⟩)
    (fun i => (pr_count2 c1 c2 (v i) (v (i + 1))).mpr (hv i))
  exact ⟨i, (pr_count2 c1 c2 (v i) (v (i + 2))).mp hi⟩

/-- **The laws characterize counting individuals by two criteria.** -/
theorem isCount2Self_iff (f : (A → Prop) → ℕ) :
    IsCount2Self f ↔ Singles f ∧ PairDet f ∧ ClawLaw f ∧ DiamondLaw f ∧ OddCycleLaw f := by
  constructor
  · rintro ⟨K1, K2, c1, c2, hf⟩
    have hpr : ∀ x y, pairLe f x y ↔ c1 x = c1 y ∨ c2 x = c2 y := fun x y => by
      show f (fun a => a = x ∨ a = y) ≤ 1 ↔ _
      rw [← hf]
      exact pr_count2 c1 c2 x y
    refine ⟨fun x => ?_, fun P => ?_, ?_, ?_, ?_⟩
    · rw [← hf]
      apply le_antisymm
      · exact (le_one_iff_pairwise c1 c2 _).mpr fun a b ha hb =>
          Or.inl (congrArg c1 ((show a = x from ha).trans (show b = x from hb).symm))
      · exact (one_le_count2_iff c1 c2 _).mpr ⟨x, rfl⟩
    · rw [← hf, count2_eq_pairCount]
      have hC : (fun x y => c1 x = c1 y ∨ c2 x = c2 y) = pairLe f :=
        funext fun x => funext fun y => propext (hpr x y).symm
      rw [hC]
    · intro x y z w h1 h2 h3
      have := c_claw c1 c2 ((hpr _ _).mp h1) ((hpr _ _).mp h2) ((hpr _ _).mp h3)
      exact this.imp (hpr _ _).mpr (Or.imp (hpr _ _).mpr (hpr _ _).mpr)
    · intro x y z w h1 h2 h3 h4 h5 h6 u
      exact (hpr u x).trans ((c_diamond c1 c2 ((hpr _ _).mp h1) ((hpr _ _).mp h2)
        ((hpr _ _).mp h3) ((hpr _ _).mp h4) ((hpr _ _).mp h5)
        (fun h => h6 ((hpr _ _).mpr h)) u).trans (hpr u y).symm)
    · intro m v hv
      obtain ⟨i, hi⟩ := c_odd c1 c2 m v (fun i => (hpr _ _).mp (hv i))
      exact ⟨i, (hpr _ _).mpr hi⟩
  · rintro ⟨hsing, hdet, hclaw, hdiam, hodd⟩
    have hrefl : ∀ x, pairLe f x x := fun x => by
      show f (fun a => a = x ∨ a = x) ≤ 1
      have e : (fun a => a = x ∨ a = x) = (fun a : A => a = x) :=
        funext fun a => propext or_self_iff
      rw [e]
      exact (hsing x).le
    have hsymm : ∀ x y, pairLe f x y → pairLe f y x := fun x y h => by
      show f (fun a => a = y ∨ a = x) ≤ 1
      have e : (fun a => a = y ∨ a = x) = (fun a : A => a = x ∨ a = y) :=
        funext fun a => propext or_comm
      rw [e]
      exact h
    obtain ⟨K1, K2, c1, c2, hc⟩ := union_of_two_general (pairLe f) hrefl hsymm hclaw hdiam hodd
    refine ⟨K1, K2, c1, c2, fun P => ?_⟩
    rw [hdet P, count2_eq_pairCount]
    have hC : (fun x y => c1 x = c1 y ∨ c2 x = c2 y) = pairLe f :=
      funext fun x => funext fun y => propext (hc x y).symm
    rw [hC]

end Counting

/-! ## The claw law is independent of the others -/

/-- A star with centre `0` and three leaves, with each individual related
to itself. -/
abbrev starRel (x y : Fin 4) : Prop := x = y ∨ x = 0 ∨ y = 0

/-- The largest set of non-neighbours in the star. -/
noncomputable def fStar : (Fin 4 → Prop) → ℕ := pairCount starRel

theorem starRel_refl : ∀ x, starRel x x := fun _ => Or.inl rfl

theorem starRel_symm : ∀ x y, starRel x y → starRel y x := by decide

theorem starRel_diamond : ∀ x y z w : Fin 4, starRel x y → starRel z x → starRel z y →
    starRel w x → starRel w y → ¬ starRel z w → ∀ u, starRel u x ↔ starRel u y := by
  decide

theorem pairLe_fStar (x y : Fin 4) : pairLe fStar x y ↔ starRel x y :=
  pairCount_pair_le_one starRel_refl starRel_symm x y

theorem singles_fStar (x : Fin 4) : fStar (fun a => a = x) = 1 := pairCount_single starRel x

theorem starRel_odd (m : ℕ) (v : ZMod (2 * m + 1) → Fin 4)
    (hv : ∀ i, starRel (v i) (v (i + 1))) : ∃ i, starRel (v i) (v (i + 2)) := by
  by_cases h0 : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := h0
    exact ⟨i, Or.inr (Or.inl hi)⟩
  · have hnz : ∀ i, v i ≠ 0 := fun i hi => h0 ⟨i, hi⟩
    have hstep : ∀ i, v i = v (i + 1) := fun i => by
      rcases hv i with e | e | e
      · exact e
      · exact absurd e (hnz i)
      · exact absurd e (hnz (i + 1))
    exact ⟨0, Or.inl ((hstep 0).trans ((hstep (0 + 1)).trans (congrArg v (by ring))))⟩

/-- **The claw law is not implied by the others.** `fStar` counts each
individual one, is determined by pairs, and obeys the diamond law and
the odd-cycle laws of every length, but breaks the claw law, so it does
not count individuals by two criteria. -/
theorem claw_independent :
    Singles fStar ∧ PairDet fStar ∧ DiamondLaw fStar ∧ OddCycleLaw fStar ∧
      ¬ ClawLaw fStar ∧ ¬ IsCount2Self fStar := by
  have hpd : PairDet fStar := fun P => by
    show pairCount starRel P = pairCount (pairLe fStar) P
    have e : pairLe fStar = starRel :=
      funext fun x => funext fun y => propext (pairLe_fStar x y)
    rw [e]
  have hnc : ¬ ClawLaw fStar := fun h => by
    rcases h 0 1 2 3 ((pairLe_fStar 0 1).mpr (by decide)) ((pairLe_fStar 0 2).mpr (by decide))
      ((pairLe_fStar 0 3).mpr (by decide)) with e | e | e
    · exact absurd ((pairLe_fStar 1 2).mp e) (by decide)
    · exact absurd ((pairLe_fStar 1 3).mp e) (by decide)
    · exact absurd ((pairLe_fStar 2 3).mp e) (by decide)
  refine ⟨singles_fStar, hpd, ?_, ?_, hnc, fun h => hnc ((isCount2Self_iff fStar).mp h).2.2.1⟩
  · intro x y z w h1 h2 h3 h4 h5 h6 u
    exact (pairLe_fStar u x).trans ((starRel_diamond x y z w ((pairLe_fStar _ _).mp h1)
      ((pairLe_fStar _ _).mp h2) ((pairLe_fStar _ _).mp h3) ((pairLe_fStar _ _).mp h4)
      ((pairLe_fStar _ _).mp h5) (fun h => h6 ((pairLe_fStar _ _).mpr h)) u).trans
      (pairLe_fStar u y).symm)
  · intro m v hv
    obtain ⟨i, hi⟩ := starRel_odd m v (fun i => (pairLe_fStar _ _).mp (hv i))
    exact ⟨i, (pairLe_fStar _ _).mpr hi⟩

/-- Nor is it counting by two criteria with several things per individual:
the claw law for sets (`ForbiddenLaws.IsCount2.claw`) fails too. -/
theorem fStar_not_isCount2 : ¬ IsCount2 fStar := by
  intro hf
  rcases IsCount2.claw hf (fun a => a = 0) (fun a => a = 1) (fun a => a = 2) (fun a => a = 3)
      (singles_fStar 0).ge ((pairLe_fStar 0 1).mpr (by decide))
      ((pairLe_fStar 0 2).mpr (by decide)) ((pairLe_fStar 0 3).mpr (by decide)) with e | e | e
  · exact absurd ((pairLe_fStar 1 2).mp e) (by decide)
  · exact absurd ((pairLe_fStar 1 3).mp e) (by decide)
  · exact absurd ((pairLe_fStar 2 3).mp e) (by decide)

end FraCaS.Encodings.Count2Laws

/-- info: 'FraCaS.Encodings.Count2Laws.isCount2Self_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.Count2Laws.isCount2Self_iff

/-- info: 'FraCaS.Encodings.Count2Laws.claw_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.Count2Laws.claw_independent
