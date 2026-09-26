import Mathlib

/-!
# FraCaS Section 9 (Attitudes) — approach

Section 9 (the final section, 13 problems, 334–346) tests which
attitude, control, and perception verbs are **factive**/**implicative**
(entail the truth of their complement) versus which are not, plus the
extensional character of direct-perception reports:

- **Factive vs. non-factive attitude verbs**: "knew" is factive
  (334 — an assumed connecting fact plus modus ponens, the same
  "assumed relation" style as Sections 5/6/8's comparatives and
  perfective verbs), "believed" is not (335, `.unknown`).
- **Implicative vs. non-implicative control verbs**: "managed to" is
  implicative (336 — succeeding is part of its meaning), "tried to" is
  not (337, `.unknown` — trying doesn't entail succeeding, the control-
  verb analogue of Section 8's imperfective paradox).
- **Literal truth-functional embedding**: "it is true that P" simply
  *is* `P` (338), "it is false that P" simply *is* `¬P` (339) — no
  separate factivity axiom is needed here, unlike a genuine attitude or
  perception verb, since these are transparent truth-conditional
  operators, not opaque predicates about a subject's mental state.
- **Perception-verb ("see") factivity and extensionality**: "saw X do
  Y" is factive about `Y` (342, another assumed-connecting-fact
  pattern) and licenses substituting a co-referential description for
  the individual inside its complement (343 — unlike a genuine opaque
  attitude context, "see" is about the real event, so `jones =
  chairman` lets the conclusion swap one name for the other),
  existential generalization over that individual (344), and
  distributing over a conjunction (345) or disjunction (346) in its
  complement.
- **Perception-verb opacity to *inferred* material** (340/341):
  although "saw Jones sign the contract" entails "Jones signed the
  contract" (342), it does **not** entail "saw Jones' heart beat" even
  given a background conditional or simultaneity fact connecting
  signing to heartbeat — direct perception is about what was actually
  witnessed, not what can be *inferred* from it, so both stay
  `.unknown`.

No new lemmas are needed; this file records the approach only.
-/
