import LeanNLSemantics.FraCaS.Section1.GQ
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Polarity

/-!
# Quantifier monotonicity signatures - the exact Phase-1 fragment

Two layers, kept deliberately separate:

1. **The entailment relation.** `FraCaS.Section1.Every P Q` (`∀ x, P x →
   Q x`), already defined in `GQ.lean`, is the one and only "P entails Q"
   relation this reasoner consumes - it is read here under the name
   `Entails` would suggest, but reusing `Every` directly rather than
   introducing a second name for the identical relation. A fact of this
   shape can come from an explicit FraCaS premise, a hand-asserted lexical
   fact, or (optionally, later) an adapter lemma from the MTT `CN`/`CNTag`
   subtyping lattice in `MTT/CN.lean` - the reasoner in `Tactic.lean` does
   not care which, and does not import `MTT.CN` at all. That lattice is a
   possible future *source* of such facts, never a dependency of the core
   reasoner - `GQ.lean`'s own header already documents that the 342-problem
   suite runs on this flat predicate layer, not on CN-as-type subtyping.

2. **Polarity signatures**, below: which argument position of which
   quantifier is upward- or downward-entailing. This is the new,
   reusable part - previously reproven per-lemma in `GQ.lean`
   (`every_restrict`, `some_mono_scope`, etc.), now stated once as data.

## The exact fragment

Quantifiers: `Every`, `Some`, `AtLeast n`, `AtMost n`.

**`No` is excluded.** Its signature is knowable in principle (`down`/
`down`, dual of `Every`, since `No P Q := ∀ x, P x → ¬ Q x`), but `GQ.lean`
has no `no_restrict`/`no_mono_scope` lemma to ground it in - nothing here
invents a rule with no already-proved lemma behind it.

**`Most` is excluded.** Unlike the other four, `Most P Q := 2 * card (P ∧
Q) > card P` is not a pure substitution in either argument: narrowing or
widening the restrictor changes the denominator `card P` itself, so
`most_trans` (`GQ.lean`) needs a genuinely different, non-monotonicity
argument (an auxiliary `Every`/`Every` structure), not a substitution
along a single `Entails` fact. Treating it as `down`/`down` or `up`/`up`
here would be silently unsound, not just incomplete.

**Positions**: exactly `restrictor` and `scope` - a single atomic
argument differs between a known fact and the goal, never a compound
expression. The conjunctive shape `every_trans`/`most_trans`/
`atMost_trans` use (`fun x => S x ∧ R x`) is still out of scope for
*this file's table*: `every_trans`'s own shape is instead reached via
`Tactic.lean`'s Phase 2 (combining two flat facts, still consumed by this
table's own `everyMonoScope`), and `atMost_trans`'s via Phase 5 (a
`(AtMost, scope)`-specific *conditioned* counterpart, registered outside
this table entirely rather than added to it - see `Trace.lean`'s
`atMostMonoScopeConditioned`). Neither widens this table itself; both
widen what feeds or consumes it. `most_trans` remains genuinely
unreachable (`Most` is excluded above). `Polarity.compose` in
`Polarity.lean` is what a future extension into nested positions would
use, not something this file's table attempts to cover already.

Every one of the eight `(quantifier, position)` cells below is grounded in
an already-proved `GQ.lean` lemma (`MonoRule` in `Trace.lean` names all
eight, `Tactic.lean` cites each by name): `every_mono_scope`,
`every_restrict`, `some_mono_scope`, `some_restrict`, `atLeast_mono_scope`,
`atLeast_restrict`, `atMost_mono_scope`, `atMost_restrict`. This is a
complete table over the four supported quantifiers × two positions, not
a subset hand-picked to match any particular problem: `some_mono_scope`
in particular is not needed by any of the fourteen problems (29, 31, 48,
49, 55, 57, 59, 63, 66-69, 76, 77) that motivated this fragment, but it is
exactly as real and exactly as grounded as `every_mono_scope`, so it is
included on the same footing rather than left out for having no example
yet - a fragment defined by which lemmas exist, not by which problems were
looked at first.
-/
namespace FraCaS.Section1.Monotonicity

/-- The four quantifiers the Phase-1 fragment supports. `No`/`Most` are
deliberately not constructors here - see this file's header. -/
inductive Quantifier where
  | every
  | some
  | atLeast
  | atMost
  deriving DecidableEq, Repr, Inhabited

/-- One quantifier's polarity in each of its two substitutable positions. -/
structure QuantifierSig where
  quantifier : Quantifier
  restrictor : Polarity
  scope : Polarity
  deriving Repr

/-- The fragment's whole semantic content, as data - each row cross-checked
against the real lemma directions in `GQ.lean` in this file's header. -/
def QuantifierSig.table : Quantifier → QuantifierSig
  | .every   => { quantifier := .every,   restrictor := .down, scope := .up }
  | .some    => { quantifier := .some,    restrictor := .up,   scope := .up }
  | .atLeast => { quantifier := .atLeast, restrictor := .up,   scope := .up }
  | .atMost  => { quantifier := .atMost,  restrictor := .down, scope := .down }

end FraCaS.Section1.Monotonicity
