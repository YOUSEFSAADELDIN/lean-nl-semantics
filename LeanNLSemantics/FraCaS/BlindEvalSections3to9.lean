import LeanNLSemantics.FraCaS.Section1.Monotonicity.BlindEvalCore
import LeanNLSemantics

/-!
# Blind evaluation (Sections 3-9)

An earlier version of `BlindEval.lean` (Sections 1-2) restricted its
scan to theorems whose conclusion is headed by one of the fixed
generalized-quantifier names (`Every`/`Some`/`Most`/...), on the theory
that Section 1/2's own `Signature.lean` table and certified monotonicity
fragment are built around exactly that closed vocabulary.

Sections 3-9 have no such shared vocabulary to restrict to in the
first place: each section's own "approach" header (`Section3/Anaphora
.lean`, `Section6/Comparatives.lean`, `Section9/Attitudes.lean`, ...)
describes bespoke, per-problem hypotheses over free predicate/individual
variables - possessive-pronoun bundles, Skolem-function donkey readings,
cardinal `Nat` comparisons, assumed factivity-connecting facts - with no
small fixed head-symbol algebra the way Section 1's GQ layer has. Most of
these sections' own headers say outright that **no new lemmas are
needed**: the "semantic" step was already folded into each problem's own
premises (an assumed connecting fact, a Skolem function, a literal `Nat`
inequality), leaving genuinely generic first-order/propositional
reasoning - or `Section1.Every`/`Some` reused unchanged, wherever a
problem's standard is itself quantified (`Comparatives.lean`'s header) -
to get from premises to hypothesis. So this scan attempts every bare
`fracas_NNN` theorem in Sections 3-9,
regardless of its conclusion's head, via `BlindEvalCore.lean`'s shared
`runBlindEvalGeneric` (`attemptClose` plus the polarity-aware
`flipConclusion` - many of these sections' bare theorems state a `.no`
gold answer as a literal `¬ hypothesis` or `a ≠ b` conclusion). That
generic scan was first built here; Sections 1-2 (`BlindEval.lean`) now
use the very same implementation, their own earlier shape restriction
having turned out not to be load-bearing.

Suffixed names (`_dir1`/`_dir2`/...) are skipped here; these sections'
`.unknown`/`.undef` countermodel pairs are evaluated separately, via the
generalized claims in `BlindEvalUnknown3to9.lean`
(`BlindEvalUnknown3to9Scan.lean`).

Deliberately not imported by anything (imports the root `LeanNLSemantics`
umbrella to see every already-proved theorem, so importing it back would
be circular) - run directly, the same way `BlindEval.lean`/`Coverage.lean`
already are.
-/
open Lean Lean.Elab.Command
open FraCaS.Section1.Monotonicity.BlindEval (runBlindEvalGeneric)

elab "#blind_eval_section3" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section3 "blind_eval_section3"

elab "#blind_eval_section4" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section4 "blind_eval_section4"

elab "#blind_eval_section5" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section5 "blind_eval_section5"

elab "#blind_eval_section6" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section6 "blind_eval_section6"

elab "#blind_eval_section7" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section7 "blind_eval_section7"

elab "#blind_eval_section8" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section8 "blind_eval_section8"

elab "#blind_eval_section9" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section9 "blind_eval_section9"

#blind_eval_section3
#blind_eval_section4
#blind_eval_section5
#blind_eval_section6
#blind_eval_section7
#blind_eval_section8
#blind_eval_section9
