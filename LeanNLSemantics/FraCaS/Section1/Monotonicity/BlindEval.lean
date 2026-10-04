import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Scan
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Existential
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Compose
import LeanNLSemantics.FraCaS.Section1.Monotonicity.BlindEvalCore
import LeanNLSemantics.FraCaS.Data.Problems
import LeanNLSemantics

/-!
# Blind evaluation (Sections 1-2)

Every `fracas_NNN` theorem so far (`Batch1.lean`-`Batch5.lean`) is
*hand-proved*: whoever wrote `theorem fracas_002 : Every P Q → Some P R
→ Some P Q := every_some ...` already knew, from FraCaS's own gold
answer, that this direction is the one that holds - the theorem's own
statement bakes in a decision no automated procedure made. That's the
concern the "self-serving?" review of the axiom audit (`AssumptionAudit
.lean`) raised for axioms; the equivalent concern here is whether the
338/342 headline figure reflects real automated entailment-checking or
just a human confirming, problem by problem, a proof they already knew
existed.

This file is a first, honest attempt at closing that gap for Sections
1-2 (`BlindEvalSections3to9.lean` covers the rest). For every **bare**
`fracas_NNN` theorem in `FraCaS.Section1` or `FraCaS.Section2` (no
`_dir1`/`_via_mono_nl`/`_from_gf`/... suffix - countermodel pairs are
evaluated separately, via `BlindEvalUnknown.lean`'s generalized claims,
and the rest are re-derivations, not distinct problems), this file:

1. Takes the theorem's own **type** only, never its hand-written proof
   term - the type is the translated Prop (premises and hypothesis, both
   necessarily a human translation choice, same as any NLI system's
   parsing step), but which *direction* of it is provable is then
   decided by automated tactics alone, not by the proof that already sits
   there.
2. Attempts to automatically close "premises → hypothesis" and,
   separately, "premises → ¬hypothesis", via `BlindEvalCore.lean`'s fixed
   `attemptClose` chain both times (see that file for the chain itself,
   and for the history of its `aesop` step, which silently never ran
   before CI run 37168342088 exposed it).
3. Turns (pos succeeds, neg fails) into **yes**, (neg succeeds, pos
   fails) into **no**, (neither succeeds) into **unknown**, and (both
   succeed) into a flagged **contradiction** - that last case would mean
   the premises are jointly unsatisfiable under this translation, or one
   of these tactics unsoundly closed a goal it shouldn't have; either way
   it is reported, never silently absorbed into "yes" or "no".
4. Compares that automated decision against `FraCaS.problems`' own gold
   `Answer` (`.unknown` and `.undef` both compared against automated
   `unknown` - see `answerMatches`).

**Every bare theorem is attempted, whatever its conclusion's shape.** An
earlier version of this file skipped any theorem whose conclusion wasn't
headed by a generalized quantifier (`Every`/`Some`/`Most`/...), 20 bare
theorems in all. The Sections 3-9 scan (`BlindEvalSections3to9.lean`)
showed that restriction wasn't load-bearing - those sections have no
quantifier vocabulary to restrict to, and the same chain handled them
anyway - so both scans now share one shape-unrestricted implementation,
`BlindEvalCore.lean`'s `runBlindEvalGeneric`, including its polarity-aware
`flipConclusion` (several of those 20 state a `.no` answer as a literal
`¬ hypothesis` conclusion, e.g. `fracas_006`).

The current CI-confirmed counts live in exactly one place, `BLIND_EVAL.md`,
read off this file's own `#blind_eval_section1`/`#blind_eval_section2`
log lines - not restated here, where they would go stale.

Deliberately not imported by anything (imports the root `LeanNLSemantics`
umbrella to see every already-proved theorem, so importing it back would
be circular) - run directly, the same way `Coverage.lean` already is.
-/
open Lean Lean.Elab.Command
open FraCaS.Section1.Monotonicity.BlindEval (runBlindEvalGeneric)

elab "#blind_eval_section1" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section1 "blind_eval_section1"

elab "#blind_eval_section2" : command => liftTermElabM do
  runBlindEvalGeneric `FraCaS.Section2 "blind_eval_section2"

#blind_eval_section1
#blind_eval_section2
