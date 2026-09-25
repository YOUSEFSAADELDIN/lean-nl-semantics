import LeanNLSemantics.MTT.Subtyping
import LeanNLSemantics.MTT.Judgments
import LeanNLSemantics.MTT.Adjectives
import LeanNLSemantics.MTT.Adverbs
import LeanNLSemantics.MTT.DotTypes
import LeanNLSemantics.MTT.Individuation
import LeanNLSemantics.MTT.NLIExamples

/-!
# Assumption audit

Faithful port of `atlas/mtt_ranta/MTT.v` Part 9 — not theorems but a
diagnostic. Coq's `Print Assumptions` becomes Lean's `#print axioms`, run
over the same 14 theorems `MTT.v` audits, to see what each one actually
depends on. `MTT.v`'s own comment: "every theorem below prints 'Closed
under the global context' — zero axioms, zero Parameters" — every
predicate/individual it needs (`walk`, `john`, ...) is a Coq `Section`
`Variable`, universally quantified away at the end of the section, never
a free top-level `Parameter`.

This repo isn't guaranteed clean the same way, and this file is where
that gets checked rather than assumed: `CN.lean` declares
`axiom walk : CN .animal → Prop` and `Adjectives.lean` declares
`axiom Tall`, genuine top-level Lean `axiom`s (not `variable`s scoped to
a section), specifically so those two files' own worked examples have a
concrete predicate to apply to a concrete model. Nothing audited below
touches either — the 14 theorems here are all built from
`variable`/`section`, matching `MTT.v`'s approach throughout
`Subtyping.lean`, `Judgments.lean`, `Adjectives.lean`, `Adverbs.lean`,
`DotTypes.lean`, `Individuation.lean`, `NLIExamples.lean` — so the CI log
for this file is the actual evidence for that, not a repeated claim.
-/

#print axioms MTT.every_anti
#print axioms MTT.some_mono
#print axioms MTT.judgment_to_prop
#print axioms MTT.intersective_iff
#print axioms MTT.intersective_every_iff
#print axioms MTT.subsective_not_transferable
#print axioms MTT.fake_not_real
#print axioms MTT.gun_partition
#print axioms MTT.noncommittal_witness
#print axioms MTT.adv_veridical
#print axioms MTT.copred_some
#print axioms MTT.two_books_phy
#print axioms MTT.not_two_books_info
#print axioms MTT.nli_black_man_walks
