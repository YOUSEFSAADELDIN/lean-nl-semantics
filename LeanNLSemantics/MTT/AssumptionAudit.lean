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
that gets checked rather than assumed — and the check found something an
earlier version of this comment got wrong: this repo has *three* genuine
top-level `axiom`s outside any `section` (`CN.lean`'s `walk`,
`Adjectives.lean`'s `Tall`, and `DotTypes.lean`'s `Physical`/
`Informational`, kept as uninterpreted types for `Book`), not the two
originally flagged here. CI's actual result, from `#print axioms` on each
of the 14: 13 come back "does not depend on any axioms" — but
`copred_some` (`DotTypes.lean`, Part 6) depends on `[MTT.Informational,
MTT.Physical]`. Not because it's any less general than its neighbours —
`copred_left`/`copred_right`/`copred_some` are all stated over a fully
abstract `{A : Type} (bk : A → DotType Physical Informational)`, same
shape as `Subtyping.lean`'s theorems — but because `Physical`/
`Informational` are themselves free top-level axioms, not section
variables, so any statement mentioning `DotType Physical Informational`
at all carries that dependency regardless of how abstract everything
else in it is. Turning them into ordinary `variable`s the way the rest of this repo
does would mean `Book`, its two `Coe` instances, and every theorem in
this file all take an explicit `Physical`/`Informational` pair — since
`Book`'s own definition already fixes a specific choice — a bigger
design change than fixing this one dependency is worth right now, not
something ruled out in principle.
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
