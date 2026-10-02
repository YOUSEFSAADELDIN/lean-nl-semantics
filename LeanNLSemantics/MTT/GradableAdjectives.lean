import LeanNLSemantics.FraCaS.Section5.Batch1
import LeanNLSemantics.FraCaS.Section5.Batch2
import LeanNLSemantics.FraCaS.Section6.Batch1

/-!
# A measure/threshold model for gradable adjectives (degree-semantics pilot)

This is a **port**, not novel theory. The idea — model a gradable
adjective pair (`small`/`large`, `fast`/`slow`, ...) as a single
degree-scale-valued *measure* plus two *thresholds*, with "small" below
the low threshold and "large" above the high one, leaving a gap in
between for the middle ground — is exactly the device used by:

- Chatzikyriakidis, `CoqLACL` (github.com/StergiosCha/CoqLACL),
  `Adjectives.v`/`FracasCoq.v`: contrary adjectives built from one
  underlying comparison rather than two independent axioms.
- Chatzikyriakidis & Luo, "Adjectival and adverbial modification: The
  view from modern type theories" (JoLLI 2017), and their forthcoming
  monograph *Formal Semantics in Modern Type Theories*
  (github.com/StergiosCha/MTT-semantics_book, `Book_gradable.v`).
- Bernardy & Chatzikyriakidis, "A Wide-Coverage Symbolic Natural
  Language Inference System" (NAACL 2019, W19-6131): one uniform
  measure+threshold-in-ℤ representation, closed automatically by linear
  arithmetic (there, Coq's `omega`/`lia`).

## Generalized over the degree scale

Bernardy & Chatzikyriakidis's own representation (and this file's own
first version) fixed the measure's codomain at `ℤ`, closed by `omega`.
Real degree semantics in the literature is usually understood as
real-valued, not integer, so `Gradable` here is instead parametrized by
an arbitrary degree scale `D` with just `[LinearOrder D]` — no
arithmetic structure at all. That turned out to matter: every proof
below only ever chains `<`/`≤` facts by transitivity (`LT.lt.trans`,
`LT.lt.trans_le`, `not_lt`), so `omega`/`linarith` were never actually
load-bearing — the device is a genuine order-theoretic fact, provable
for *any* linearly ordered degree scale (`ℤ`, `ℚ`, `ℝ`, or anything
else), not an artifact of integer arithmetic. The concrete worked
example near the end instantiates `D := ℚ` rather than `ℤ`, precisely
to demonstrate the generalization is exercised, not just available.

## What this buys the existing port

This project's own Section 5/6 FraCaS theorems (`fracas_204`, `205`,
`208`, `209`, `210`, `211`, `212`, `220`, `223`, `224`, `227`, `229`)
each had to take, as an extra hypothesis, an assumed "connecting fact"
relating a pair of gradable adjectives or comparatives — e.g. `204`'s
`∀ x, small x → ¬ large x`, or `208`'s
`∀ x y, small x → large y → smallerThan x y`. FraCaS's own `<why>` notes
for these problems call such facts genuinely assumed world knowledge,
not derivable from the sentences alone — and that remains true in
general (nothing here changes how those 12 theorems are stated or
proved). What this file adds is a *concrete model* in which all of
those assumed facts turn out to be theorems: give `small`/`large` (or
`fast`/`slow`, `asFastAs`, ...) a shared `measure` into any linearly
ordered scale and a threshold gap, and each fact is a direct consequence
of that gap. The corollaries below apply the real, already-proved
`fracas_NNN` theorems to these derived facts, rather than re-proving or
modifying them — this file is purely additive. `210`/`211`/`212` reuse
the exact same `small`/`large` contrariety facts as `204`/`205`/`208` —
they only differ from 204/205/208 in bundling in an extra, genuinely
lexical (non-gradable) "mice/elephants are animals" premise that stays
an ordinary hypothesis, not something the degree model derives.
-/

namespace MTT

open FraCaS.Section5 FraCaS.Section6

/-- A gradable adjective pair over `A`, with degrees drawn from an
arbitrary linearly ordered scale `D` (ℤ, ℚ, ℝ, ... — anything with
`[LinearOrder D]`): a `measure`, and two thresholds with a gap between
them (`small_lt_large`) for the "neither small nor large" middle ground
that FraCaS's own 206/207 rely on. -/
structure Gradable (D : Type*) [LinearOrder D] (A : Type*) where
  measure : A → D
  smallThreshold : D
  largeThreshold : D
  small_lt_large : smallThreshold < largeThreshold

variable {D : Type*} [LinearOrder D] {A : Type*}

/-- Below the low threshold. -/
def small (G : Gradable D A) (x : A) : Prop := G.measure x < G.smallThreshold

/-- Above the high threshold. -/
def large (G : Gradable D A) (x : A) : Prop := G.largeThreshold < G.measure x

/-- The comparative read off the same measure (strict). -/
def smallerThan (G : Gradable D A) (x y : A) : Prop := G.measure x < G.measure y

/-- The reverse comparative. -/
def largerThan (G : Gradable D A) (x y : A) : Prop := G.measure y < G.measure x

/-- "Faster than" (or any strict comparative): greater measure. -/
def fasterThan (G : Gradable D A) (x y : A) : Prop := G.measure y < G.measure x

/-- "At least as fast as" — the "at least as", not "exactly as", reading
`Section6.Batch1`'s own 224/225/226/227/228 comment already calls for. -/
def asFastAs (G : Gradable D A) (x y : A) : Prop := G.measure y ≤ G.measure x

/-- "Slower than": the reverse strict comparative. -/
def slowerThan (G : Gradable D A) (x y : A) : Prop := G.measure x < G.measure y

/-! ## The derived "connecting facts"

Every proof here is a direct chain of `<`/`≤` facts via transitivity —
`LT.lt.trans`, `LT.lt.trans_le`, `not_lt` — available for any
`LinearOrder`, with no arithmetic involved. -/

/-- Feeds `fracas_204`: small and large can't both hold, via the gap. -/
theorem small_not_large (G : Gradable D A) : ∀ x, small G x → ¬ large G x := by
  intro x hs hl
  have hgap := G.small_lt_large
  unfold small at hs
  unfold large at hl
  exact absurd ((hs.trans hgap).trans hl) (lt_irrefl _)

/-- Feeds `fracas_205`, the mirror image of `small_not_large`. -/
theorem large_not_small (G : Gradable D A) : ∀ x, large G x → ¬ small G x := by
  intro x hl hs
  have hgap := G.small_lt_large
  unfold small at hs
  unfold large at hl
  exact absurd ((hl.trans hs).trans hgap) (lt_irrefl _)

/-- Feeds `fracas_208`: anything small measures below anything large. -/
theorem small_lt_large_measure (G : Gradable D A) :
    ∀ x y, small G x → large G y → smallerThan G x y := by
  intro x y hs hl
  have hgap := G.small_lt_large
  unfold small at hs
  unfold large at hl
  unfold smallerThan
  exact (hs.trans hgap).trans hl

/-- Feeds `fracas_209`, the `largerThan`-flavored mirror of the above. -/
theorem not_larger_of_small_large (G : Gradable D A) :
    ∀ x y, small G x → large G y → ¬ largerThan G x y := by
  intro x y hs hl hcontra
  have hgap := G.small_lt_large
  unfold small at hs
  unfold large at hl
  unfold largerThan at hcontra
  exact absurd (((hl.trans hcontra).trans hs).trans hgap) (lt_irrefl _)

/-- Feeds `fracas_220`: faster than something large is itself large. -/
theorem large_of_fasterThan_large (G : Gradable D A) :
    ∀ x y, fasterThan G x y → large G y → large G x := by
  intro x y hf hy
  unfold fasterThan at hf
  unfold large at hy ⊢
  exact hy.trans hf

/-- Feeds `fracas_223`: faster than something small rules out the
*other* one being large (the faster one is already small, so the
slower one is even smaller). -/
theorem not_large_of_fasterThan_small (G : Gradable D A) :
    ∀ x y, fasterThan G x y → small G x → ¬ large G y := by
  intro x y hf hx hy
  have hgap := G.small_lt_large
  unfold fasterThan at hf
  unfold small at hx
  unfold large at hy
  exact absurd (((hy.trans hf).trans hx).trans hgap) (lt_irrefl _)

/-- Feeds `fracas_224`: at-least-as-fast-as something large is itself
large. -/
theorem large_of_asFastAs_large (G : Gradable D A) :
    ∀ x y, asFastAs G x y → large G y → large G x := by
  intro x y ha hy
  unfold asFastAs at ha
  unfold large at hy ⊢
  exact hy.trans_le ha

/-- Feeds `fracas_227`, the `asFastAs`-flavored mirror of
`not_large_of_fasterThan_small`. -/
theorem not_large_of_asFastAs_small (G : Gradable D A) :
    ∀ x y, asFastAs G x y → small G x → ¬ large G y := by
  intro x y ha hx hy
  have hgap := G.small_lt_large
  unfold asFastAs at ha
  unfold small at hx
  unfold large at hy
  exact absurd (((hy.trans_le ha).trans hx).trans hgap) (lt_irrefl _)

/-- Feeds `fracas_229`: at-least-as-fast-as directly refutes
slower-than, by pure order reasoning (no threshold gap needed). -/
theorem not_slowerThan_of_asFastAs (G : Gradable D A) :
    ∀ x y, asFastAs G x y → ¬ slowerThan G x y := by
  intro x y ha
  unfold asFastAs at ha
  unfold slowerThan
  exact not_lt.mpr ha

/-- Feeds `fracas_212`: same fact as `small_lt_large_measure`, but in
the large-object-first argument order 212's own hypothesis happens to
use (`largerThan y x` where `y` is the large one, `x` the small one). -/
theorem large_gt_small_measure (G : Gradable D A) :
    ∀ x y, small G x → large G y → largerThan G y x := by
  intro x y hs hl
  have hgap := G.small_lt_large
  unfold small at hs
  unfold large at hl
  unfold largerThan
  exact (hs.trans hgap).trans hl

/-! ## The corollaries: the real FraCaS theorems, discharged -/

theorem fracas_204_degree_based (G : Gradable D A) (mickey : A) :
    small G mickey → ¬ large G mickey :=
  fracas_204 (small G) (large G) mickey (small_not_large G)

theorem fracas_205_degree_based (G : Gradable D A) (dumbo : A) :
    large G dumbo → ¬ small G dumbo :=
  fracas_205 (small G) (large G) dumbo (large_not_small G)

theorem fracas_208_degree_based (G : Gradable D A) (mickey dumbo : A) :
    small G mickey → large G dumbo → smallerThan G mickey dumbo :=
  fracas_208 (small G) (large G) (smallerThan G) mickey dumbo (small_lt_large_measure G)

theorem fracas_209_degree_based (G : Gradable D A) (mickey dumbo : A) :
    small G mickey → large G dumbo → ¬ largerThan G mickey dumbo :=
  fracas_209 (small G) (large G) (largerThan G) mickey dumbo (not_larger_of_small_large G)

theorem fracas_210_degree_based (G : Gradable D A) (mouse animal largeMouse : A → Prop)
    (mickey : A) :
    (∀ x, mouse x → animal x ∧ small G x) → mouse mickey ∧ largeMouse mickey →
      ¬ large G mickey :=
  fun h1 h2 => fracas_210 mouse animal (small G) largeMouse (large G) mickey h1
    (small_not_large G) h2

theorem fracas_211_degree_based (G : Gradable D A) (elephant animal smallElephant : A → Prop)
    (dumbo : A) :
    (∀ x, elephant x → animal x ∧ large G x) → elephant dumbo ∧ smallElephant dumbo →
      ¬ small G dumbo :=
  fun h1 h2 => fracas_211 elephant animal (large G) smallElephant (small G) dumbo h1
    (large_not_small G) h2

theorem fracas_212_degree_based (G : Gradable D A)
    (mouse elephant animal largeMouse smallElephant : A → Prop) (mickey dumbo : A) :
    (∀ x, mouse x → animal x ∧ small G x) → (∀ x, elephant x → animal x ∧ large G x) →
      mouse mickey ∧ largeMouse mickey → elephant dumbo ∧ smallElephant dumbo →
        largerThan G dumbo mickey :=
  fun h1 h2 h3 h4 =>
    fracas_212 mouse elephant animal (small G) (large G) largeMouse smallElephant (largerThan G)
      mickey dumbo h1 h2 h3 h4 (large_gt_small_measure G)

theorem fracas_220_degree_based (G : Gradable D A) (pc itel : A) :
    fasterThan G pc itel → large G itel → large G pc :=
  fracas_220 (fasterThan G) (large G) pc itel (large_of_fasterThan_large G)

theorem fracas_223_degree_based (G : Gradable D A) (pc itel : A) :
    fasterThan G pc itel → small G pc → ¬ large G itel :=
  fracas_223 (fasterThan G) (large G) (small G) pc itel (not_large_of_fasterThan_small G)

theorem fracas_224_degree_based (G : Gradable D A) (pc itel : A) :
    asFastAs G pc itel → large G itel → large G pc :=
  fracas_224 (asFastAs G) (large G) pc itel (large_of_asFastAs_large G)

theorem fracas_227_degree_based (G : Gradable D A) (pc itel : A) :
    asFastAs G pc itel → small G pc → ¬ large G itel :=
  fracas_227 (asFastAs G) (large G) (small G) pc itel (not_large_of_asFastAs_small G)

theorem fracas_229_degree_based (G : Gradable D A) (pc itel : A) :
    asFastAs G pc itel → ¬ slowerThan G pc itel :=
  fracas_229 (asFastAs G) (slowerThan G) pc itel (not_slowerThan_of_asFastAs G)

/-! ## A concrete, non-vacuous instance

Everything above is stated for an arbitrary `G : Gradable D A` — worth
checking it isn't vacuous, i.e. that `Gradable` actually has an
inhabitant and the corollaries fire on real data, the same way
`CN.lean`'s `john`/`johnI` and `LinglibBridge.lean`'s `toyLexicon` give
their own abstract structures a concrete witness. This instance uses
`D := ℚ` rather than `ℤ`, to exercise the generalization rather than
just type-check it against the one scale the original version used. -/

/-- Three animals distinguished only by measure: Mickey (a mouse) is
small, Dumbo (an elephant) is large, and a third, `medium`, sits in the
gap between them — neither small nor large. -/
inductive ToyAnimal where
  | mickey
  | medium
  | dumbo

/-- Mickey measures `1`, Dumbo measures `100`, and `medium` measures
`25` — strictly inside the gap `(10, 50)`, below neither threshold's
wrong side and above neither's right one. All four values are rational
(not integer) literals, over the degree scale `ℚ`. -/
def toyGradable : Gradable ℚ ToyAnimal where
  measure := fun
    | .mickey => 1
    | .medium => 25
    | .dumbo => 100
  smallThreshold := 10
  largeThreshold := 50
  small_lt_large := by norm_num

theorem toy_mickey_small : small toyGradable .mickey := by show (1:ℚ) < 10; norm_num

theorem toy_dumbo_large : large toyGradable .dumbo := by show (50:ℚ) < 100; norm_num

/-- The fully concrete form of `fracas_204_degree_based`: Mickey really
is not large. -/
theorem toy_fracas_204_not_large : ¬ large toyGradable .mickey :=
  fracas_204_degree_based toyGradable .mickey (by show (1:ℚ) < 10; norm_num)

/-- The fully concrete form of `fracas_208_degree_based`: Mickey really
does measure below Dumbo. -/
theorem toy_fracas_208_smallerThan : smallerThan toyGradable .mickey .dumbo :=
  fracas_208_degree_based toyGradable .mickey .dumbo
    (by show (1:ℚ) < 10; norm_num) (by show (50:ℚ) < 100; norm_num)

/-- `.medium` sits strictly inside the threshold gap — this is the
concrete form of FraCaS's own 206/207 independence ("not small" doesn't
give "large", and vice versa). The gap in `Gradable` isn't a loose end
in the model; it's exactly the middle ground 206/207 rely on, and this
is a genuine witness of it, not just an assertion in prose. -/
theorem fracas_206_207_gap_witness :
    ¬ small toyGradable .medium ∧ ¬ large toyGradable .medium := by
  refine ⟨?_, ?_⟩
  · show ¬ (25:ℚ) < 10; norm_num
  · show ¬ (50:ℚ) < 25; norm_num

/-! ## Axiom audit

Same discipline as `AssumptionAudit.lean`'s port of `MTT.v` Part 9,
applied to this file's own theorems: `#print axioms` on everything
proved above, to check rather than assume that this pilot's proofs
don't quietly depend on anything beyond what the originals need. The
abstract lemmas and corollaries (parametrized by an arbitrary
`G : Gradable D A`) never needed `omega`/`decide`/`norm_num` at all —
pure order-lemma composition closes them, so there is no concrete
numeral reduction for anything to go wrong on. The one place the
earlier `ℤ`-only version of this file *did* pick up a stray
`Classical.choice` dependency was in the concrete `toyGradable`
instance's own `small_lt_large` field proof (there, `by norm_num`
proving `(10:ℤ) < 50`) — not in any of the downstream goals that
mention it, which was the wrong place three separate debugging attempts
looked first. Worth re-checking here since the scale changed to `ℚ`
and the field proof is `norm_num` again (rationals' order is decidable
and `norm_num`'s numeral-comparison certificates are ordinarily
constructive, but "ordinarily" is exactly the kind of claim this file's
own history says to verify, not assume). -/

#print axioms small_not_large
#print axioms large_not_small
#print axioms small_lt_large_measure
#print axioms not_larger_of_small_large
#print axioms large_of_fasterThan_large
#print axioms not_large_of_fasterThan_small
#print axioms large_of_asFastAs_large
#print axioms not_large_of_asFastAs_small
#print axioms not_slowerThan_of_asFastAs
#print axioms large_gt_small_measure
#print axioms fracas_204_degree_based
#print axioms fracas_205_degree_based
#print axioms fracas_208_degree_based
#print axioms fracas_209_degree_based
#print axioms fracas_210_degree_based
#print axioms fracas_211_degree_based
#print axioms fracas_212_degree_based
#print axioms fracas_220_degree_based
#print axioms fracas_223_degree_based
#print axioms fracas_224_degree_based
#print axioms fracas_227_degree_based
#print axioms fracas_229_degree_based
#print axioms toy_mickey_small
#print axioms toy_dumbo_large
#print axioms toy_fracas_204_not_large
#print axioms toy_fracas_208_smallerThan
#print axioms fracas_206_207_gap_witness

end MTT
