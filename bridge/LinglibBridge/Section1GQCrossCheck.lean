import LeanNLSemantics.FraCaS.Section1.GQ
import LeanNLSemantics.FraCaS.Section2.Plurals
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Quantification.Counting

/-!
# Section 1's own GQ layer against linglib's independently-built one

`FraCaS.Section1.GQ` (`LeanNLSemantics/FraCaS/Section1/GQ.lean`) was built
self-contained, on purpose — that file's own header explains the main
package deliberately does *not* reuse `MTT`'s `Every`/`Some'`/`No'`, since
Section 1's two-predicate `Det(A)(restrictor)(scope)` shape doesn't match
`MTT`'s CN-typed one. That choice was about keeping the main,
Mathlib-unpinned 342-theorem package free of the bridge's own optional,
pinned dependency — not a judgment that nothing else already existed:
linglib ships its own independent formalization of exactly this theory
(`Linglib.Semantics.Quantification.{Defs,Basic,Properties,Counting}`),
Barwise & Cooper's `GQ α := (α → Prop) → (α → Prop) → Prop` and its
`every`/`GQ.some`/`no`, already used for real in `Linglib.Studies.
Ladusaw1979` (determiner monotonicity and polarity licensing).

So the duplication here is real — the same mathematics, authored twice,
independently — but it was never a wasted step: the main package's
Section 1 work had to stand on its own regardless of what any one
pinned, fast-moving external dependency happened to ship, the same
reason `bridge/lakefile.toml`'s own header gives for keeping this
package separate at all. What the bridge adds now is exactly what
wasn't possible before linglib was actually pulled in and read: showing
the two formalizations *agree*, and that Section 1's own hand-proved
monotonicity lemmas are literal instances of linglib's general,
already-proven theory — the same kind of confirmation
`LinglibBridge.lean`'s `KindedLexicon`/`CN'.intersective_widen`
generalization gave Section 5, now given to Section 1.
-/

namespace MTT.LinglibBridge

/-! ## The determiner denotations coincide

Not approximately — `FraCaS.Section1.Every`/`Some`/`No` and linglib's
`Quantifier.GQ.every`/`.some`/`.no` both reduce to the exact same
`∀ x, P x → Q x` / `∃ x, P x ∧ Q x` / `∀ x, P x → ¬ Q x`, so `Iff.rfl`
closes all three: no proof beyond unfolding both sides. -/

theorem every_eq_gq_every {A : Type} (P Q : A → Prop) :
    FraCaS.Section1.Every P Q ↔ Quantifier.GQ.every P Q := Iff.rfl

theorem some_eq_gq_some {A : Type} (P Q : A → Prop) :
    FraCaS.Section1.Some P Q ↔ Quantifier.GQ.some P Q := Iff.rfl

theorem no_eq_gq_no {A : Type} (P Q : A → Prop) :
    FraCaS.Section1.No P Q ↔ Quantifier.GQ.no P Q := Iff.rfl

/-! ## The counting primitive coincides

`FraCaS.Section1.card` and linglib's `Quantifier.GQ.count` are both,
after unfolding `count`'s own `countOn Finset.univ`, literally
`(Finset.univ.filter P).card` — `rfl`, not just propositionally equal. -/

theorem card_eq_count {A : Type} [Fintype A] (P : A → Prop) [DecidablePred P] :
    FraCaS.Section1.card P = Quantifier.GQ.count P := rfl

/-! ## Section 1's own monotonicity theorems are instances of linglib's general theory

`every_mono_scope`/`every_restrict` were proved directly, by hand, in
`FraCaS/Section1/GQ.lean` — reasonably so, since that file owes nothing
to this bridge or to linglib. But linglib's own `Quantifier.GQ.
scopeMonotone_every`/`restrictorAntitone_every` (used for real in
`Linglib.Studies.Ladusaw1979`'s `determiner_monotonicity`, to locate
where *every* licenses negative polarity items) are the fully general
versions of exactly these two facts, proved once for *any* type, not
redone here: both of Section 1's lemmas below are recovered as direct
applications of linglib's theorems, term-for-term, with no new
reasoning of their own. -/

/-- `every_mono_scope`, rederived: `scopeMonotone_every P` is
`Monotone (every P)`, i.e. exactly "`Q ≤ R` gives `every P Q ≤ every P
R`" under the pointwise/implication order on `α → Prop` — applying it to
`hqr : ∀ x, Q x → R x` and then to the `Every P Q` premise is the whole
proof, matching how `Properties.lean` itself invokes these combinators
(e.g. `ScopeMonotone.compl`'s `h R hSS' hQS`). -/
theorem every_mono_scope_is_scopeMonotone_every {A : Type} (P Q R : A → Prop) :
    FraCaS.Section1.Every P Q → (∀ x, Q x → R x) → FraCaS.Section1.Every P R :=
  fun h hqr => Quantifier.GQ.scopeMonotone_every P hqr h

/-- `every_restrict`, rederived: `restrictorAntitone_every Q` is
`Antitone (fun R => every R Q)`, i.e. "`P ≤ R` gives `every R Q ≤ every P
Q`" (shrinking the restrictor preserves a universal) — applying it to
`hpr : ∀ x, P x → R x` and then to the `Every R Q` premise is the whole
proof, the same instantiation pattern as `every_mono_scope_is_
scopeMonotone_every` above, for the other of the two Barwise-Cooper
monotonicities instead of the first. -/
theorem every_restrict_is_restrictorAntitone_every {A : Type} (P Q R : A → Prop) :
    FraCaS.Section1.Every R Q → FraCaS.Section1.Every P R → FraCaS.Section1.Every P Q :=
  fun h hpr => Quantifier.GQ.restrictorAntitone_every Q hpr h

/-! ## Section 2's `Exactly` coincides with linglib's `exactly`, too

`FraCaS.Section2.Exactly n P Q := card (fun x => P x ∧ Q x) = n`, the
only piece Section 2 adds beyond reusing Section 1's own machinery
wholesale (`FraCaS/Section2/Plurals.lean`'s own header). linglib's
`Quantifier.GQ.exactly n R S := count (fun x => R x ∧ S x) = n` matches
it exactly in content — but unlike `every`/`some`/`no`/`count`, it isn't
a free `Iff.rfl`/`rfl`: `exactly` is declared `noncomputable`, built
under `open Classical in` so it can supply `count`'s `[DecidablePred
...]` argument itself via `Classical.propDecidable`, rather than taking
one as a parameter from the caller the way `Exactly`/`card`/`count` all
do. So the two sides use *different* `Decidable` instances for the same
predicate, and those aren't defeq to each other in general — only
provably equal, via `Prop`'s own definitional proof irrelevance (any
two `Decidable p` witnesses for one true-or-false `p` must already
agree). -/

/-- Two `Decidable p` witnesses for the *same* proposition are equal —
proved directly from first principles rather than reached for a named
mathlib lemma of this shape, since getting a recalled lemma name wrong
is exactly the kind of mistake that has already cost real CI
round-trips elsewhere in this bridge. The matching-constructor cases
are `rfl` outright, since `Prop` has definitional proof irrelevance
(any two proofs of `p`, or of `¬p`, are already defeq); the
mismatched cases are vacuous, since `h : p` and `h' : ¬p` can't both
hold, and `absurd` turns that contradiction into a proof of anything,
this equality included. -/
theorem decidable_subsingleton {p : Prop} (d₁ d₂ : Decidable p) : d₁ = d₂ := by
  cases d₁ <;> cases d₂ <;> first | rfl | exact absurd ‹p› ‹¬p›

/-- The same fact, pointwise over a predicate: two `DecidablePred p`
witnesses are equal as functions, since they agree (by
`decidable_subsingleton`) at every point. -/
theorem decidablePred_subsingleton {A : Type*} {p : A → Prop}
    (inst₁ inst₂ : DecidablePred p) : inst₁ = inst₂ :=
  funext fun x => decidable_subsingleton (inst₁ x) (inst₂ x)

/-- `Exactly` and `exactly` agree, despite using different `Decidable`
instances internally (`exactly` is `noncomputable`, supplying `count`'s
instance itself via `Classical.propDecidable` rather than taking one
from the caller the way `Exactly`/`card`/`count` all do): both unfold to
`(Finset.univ.filter (fun x => P x ∧ Q x) _).card = n`, and
`decidablePred_subsingleton` erases the only difference between the two
sides, since `Finset.filter` applied to equal instances gives equal
results (`congr!`'s own subsingleton-closing step, backed by the lemma
above rather than left to guesswork about what it already knows). -/
theorem exactly_eq_gq_exactly {A : Type} [Fintype A] (n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] :
    FraCaS.Section2.Exactly n P Q ↔ Quantifier.GQ.exactly n P Q := by
  simp only [FraCaS.Section2.Exactly, FraCaS.Section1.card, Quantifier.GQ.exactly,
    Quantifier.GQ.count, Quantifier.GQ.countOn]
  congr! 1 <;> exact decidablePred_subsingleton _ _

end MTT.LinglibBridge
