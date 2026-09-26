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
-/
