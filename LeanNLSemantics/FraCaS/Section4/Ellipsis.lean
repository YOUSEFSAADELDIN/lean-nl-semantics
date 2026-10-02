import LeanNLSemantics.FraCaS.Section3.Anaphora

/-!
# FraCaS Section 4 (Ellipsis) — approach

Section 4 tests VP-ellipsis, gapping, "one"-anaphora, NP-ellipsis, and
sloppy/strict identity — all instances of the same move: an elided or
anaphoric constituent is resolved to a specific reading, and the
question is whether *that resolved reading* entails the hypothesis.
Consistent with Section 3's treatment of pronouns, this project does not
model the ellipsis-resolution mechanism itself (parallelism constraints,
sloppy/strict identity as a formal operation, etc.) — each problem's
ellipsis site is hand-resolved directly into the Lean formalization, the
resolved premise stated as a bundled fact.

This makes almost every problem one of two shapes:

- **The resolved premise directly contains (or trivially implies) the
  hypothesis** — `.yes`/`.no`, proved by projection, instantiation, or
  direct negation, no new machinery needed.
- **Two different resolutions are both grammatically available and
  FraCaS asks about each separately** (169/170's "before" scope
  ambiguity; 175/176/182/183/185–187/189/190's sloppy-vs-strict
  identity; 191/193/195's parallel plural-pronoun resolution) — each
  reading gets its own theorem stating what *that* reading gives,
  matching FraCaS's own per-reading gold answers, rather than one
  theorem trying to cover an ambiguous sentence.
- **The hypothesis asks about a detail the resolved premise is silent
  on** (143/158/174/177/181/184/188/192/194's `.unknown` cases, and
  156's "not necessarily the same witness" case) — genuine independence,
  shown the same way as Sections 1–3's countermodels: either two
  unconnected concrete facts, or (156) two existentials that need not
  share a witness.

No new lemmas are needed beyond what Sections 1–3 already built
(`Every`/`Some`/`No`/`Exactly`/`exactly_ne` from `GQ.lean`/`Plurals.lean`),
so this file exists only to record the approach; the four `Batch*.lean`
files do the actual per-problem work.

One caveat, specific to the GF cross-check tooling rather than the Lean
formalization above (which stays entirely hand-written either way):
`gf/translate.py`'s `_try_translate_gapped_travel_fact` and
`_try_translate_existential_universal_object` reproduce five of this
section's ids directly from their own raw GF trees. The first handles
150–153's own shared gapping pattern ("John went to Paris by car"), an
intransitive verb with two PP adjuncts, continued either by a second
named individual (150–152) or a definite-plural distributive universal
over a trivial whole-domain restrictor (153) — confirmed to need a
genuinely three-sorted Lean domain (`{A B C : Type*}`), the same
finding Section 3's own 134/135 established for two sorts: nothing in
the cross-check generator's own dispatch mechanism required a single
domain, every prior id there simply hadn't needed more than one. The
second handles 196's own wide-scope "so did" reading ("one lawyer
signed all the reports"), an existential subject taking scope over an
inner universal object — `translate_cl`'s own general path parses the
identical tree shape without erroring but commits to the wrong,
cardinal-quantified reading for it, confirmed by direct comparison, not
assumed. None of these five ids were previously cross-checked at all
(not a refactor of existing hand-built code).

A second round added six more: 169/170 (a top-level `AdvS (SubjS
before_Subj ...) ...` "before"-conditional, the stipulated reading of a
genuinely ambiguous sentence, `:= id` trivially) and 179 (an
`if`-conditional, modus ponens over two bare atoms, split via a new
`_split_advs_conditional` helper into its antecedent/consequent) reuse
trees that were ALREADY confirmed via `gf`'s own linearize check but
had never been wired into the cross-check generator at all. 175/176
("Bill/John said that Mary/Bill wrote a report", `:= id` trivially) and
180's own premise 1 ("John wanted to buy a car", a `want_VV`+`ComplVV`
control-verb construction) are genuinely NEW trees, confirmed directly
by actually invoking this project's own local `gf` toolchain this
round — it's available and fast enough to confirm brand-new sentences
directly, not just reuse already-confirmed ones, each built from
constructs (`say_VS`/`ComplVS`, `want_VV`/`ComplVV`) already proven
elsewhere in this corpus.

The remaining 12 ids in this section are either bare-`Prop`-atom
restatements (via `gen_gf_cross_check.py`'s own `_atomic_name` helper,
which fuses an entire resolved sentence into one nullary fact, not a
domain-quantified predicate, so there is no positional structure to
extract in the first place) or still out of reach for reasons that
don't shrink with more GF-construction effort: genuine grammar gaps the
GF grammar itself has no combinator for (163/171–174/191–195); 168
("forty-five women work part time"), a REAL, independently-
reconfirmed gf-rgl TOOLCHAIN bug at the current pinned tag (`pot1plus`,
the tens-plus-ones numeral combinator any two-digit number with a
nonzero ones digit needs, renders its own bind tokens literally instead
of collapsing them — confirmed directly via `gf`'s own linearize output
this round, not merely re-read from a pre-existing comment), not
fixable at the Python/`translate.py` level; or countermodel-only ids
with no bare theorem to cross-check at all
(143/156/158/161/174/177/181/184/188/192/194).
-/
