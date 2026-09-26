import Mathlib

/-!
# FraCaS Section 5 (Adjectives) — approach

Section 5 tests exactly the intersective/subsective/privative adjective
distinctions `MTT/Adjectives.lean` already formalizes as Part 4 of the
`MTT.v` port (`Intersective`, `SubsCN`, the `Gun`/`fake`/`real` privative
pattern) — but as *individual* predications about named entities (John,
Dumbo, Mickey) rather than `Some'`/`Every`-quantified claims, so this
section works directly with adjective/noun predicates over a domain
rather than re-wrapping every problem in `Intersective`/`SubsCN`'s
subtype machinery. The recurring shapes:

- **Affirmative adjectives** ("genuine", "four-legged") license noun-
  drop and adjective-drop (`inter_noun_drop`/`inter_adj_drop`'s content,
  restated directly): `Adj x ∧ N x` entails either conjunct.
- **Privative adjectives** ("former") are the *opposite* of affirmative:
  `former N x` entails `¬ N x`, an explicit assumed fact playing the
  role `Gun.lean`'s `fake_not_real` plays for "fake" — this project
  follows FraCaS's own chosen `.no` reading, not the "opinions differ"
  alternative it also flags.
- **Adjective ordering** (199–201) matters for privative+affirmative
  stacks: an affirmative adjective *outermost* in the construction
  ("successful former N") still predicates of the present-tense
  subject, but one embedded *under* a privative ("former successful N")
  does not project past the "former".
- **Comparison-class-relative (subsective) adjectives** ("small",
  "large", "clever", "competent") are contrary, not contradictory
  (`small → ¬large` but `¬small ⇏ large`), and only transfer across a
  bare/general predication when the comparison class is *extensional*
  (214/216) — an *intensional* one (215/217/219) doesn't transfer, shown
  the same way as Sections 1–4's independence cases.
- **Comparatives** ("smaller than") are given via an explicit assumed
  relation between the base gradable adjectives, per FraCaS's own
  `<why>` ("assume comparative relations exemplified in (208)/(209)").

No new lemmas are needed; this file records the approach only.
-/
