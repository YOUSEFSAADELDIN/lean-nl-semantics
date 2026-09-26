import Mathlib

/-!
# FraCaS Section 6 (Comparatives) — approach

Section 6 continues Section 5's comparative machinery (208/209/212's
"assume the comparative relation between the base gradable adjectives"
pattern) and adds genuine cardinal comparatives ("won more orders
than"), which this project formalizes directly as `Nat` counts so the
arithmetic is real (`omega`), not another assumed relation. Recurring
shapes:

- **"Adj-er than" / "as Adj as"** license or refute a bare "Adj"
  predication via an explicit assumed connecting fact (the same move as
  Section 5's 208/209), including the "as...as" case's asymmetric
  ("at least as", not "exactly as") reading that makes some of these
  `.unknown` rather than `.yes`/`.no`.
- **Cardinal comparatives** ("won more orders than APCOM did/lost")
  are literal `Nat` inequalities between counts, so "won some" (`>0`)
  and "won at least eleven" (given the standard's own count) are
  `omega`-checkable facts, not assumed ones.
- **Quantified comparative standards** ("faster than every/some/any
  ITEL computer", "... than X and Y") reuse `Every`/`Some` from
  `FraCaS.Section1.GQ` exactly as Sections 1–5 do throughout — a
  universal standard licenses instantiation, an existential one doesn't
  (independence, the same shape as Section 1's problem 33).
- A handful of genuinely ambiguous/nonstandard comparative-ellipsis
  readings (236/237, 244/245, 250) are each given their own stipulated
  reading directly, the same way Section 4 handles ellipsis ambiguity.

No new lemmas are needed; this file records the approach only.
-/
