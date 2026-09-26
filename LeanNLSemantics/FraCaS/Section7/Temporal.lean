import Mathlib

/-!
# FraCaS Section 7 (Temporal Reference) — approach

Section 7 is the largest FraCaS section (75 problems, four of which —
276, 305, 309, 310 — are degenerate FraCaS problems with no question or
hypothesis transcribed, so they are skipped exactly as
`FraCaS/Types.lean` already documents). Its inferences turn on
Aktionsart (lexical aspect): whether a predicate is a **state**,
**activity**, **accomplishment**, or **achievement** in Vendler's
classification governs which temporal adverbials and tense
constructions license which inferences. Recurring shapes:

- **Continuous "since"** ("has been P since Y, it is now Y'") licenses
  the state `P` at every intervening time only when `P` is genuinely
  stative (255) or paired with an explicit continuity premise
  (252). Applied to a non-stative predicate coerced into "since" (253,
  254 — developing an editor, expanding), it only asserts *some*
  occurrence in the interval, not truth throughout it, so the
  inference is `.unknown`. Problems 256/257 are FraCaS's own
  acknowledged case of the same sentence receiving two different gold
  answers across the corpus (the note on 257 says so explicitly) — the
  continuous reading is `.yes`, the "at least once since" reading is
  `.unknown`; this project gives each its own theorem rather than
  picking one silently.
- **Bare past-tense state without "since"** (277) does *not* project to
  an adjacent year on its own — continuity needs to be given, not
  assumed.
- **Repeatable vs. unrepeatable events** (278/279 vs. 280; 282 vs. 283):
  an *unrepeatable* accomplishment/achievement ("wrote *his first*
  novel", "discovered *a* new species" referred back to with "it")
  happens at one time only, so a different year is refuted (`.no`); a
  *repeatable* one (a novel, a species, not tied to a unique referent)
  merely leaves the second year open (`.unknown`).
- **"In N hours" vs. "for N hours"**: for an accomplishment, "in N
  hours" bounds *completion* (285/287 leave the exact duration
  `.unknown`, but 284's explicit start time lets completion-by a clock
  time be computed, and 288/290/297/300 all get the bare existential
  "did happen at all" for free). "For N hours" applied to an
  accomplishment (303/304) is different again: it coerces the
  accomplishment into a bounded activity reading, which does *not*
  entail that the accomplishment culminated (304's `.unknown`, "he may
  not have finished it") — the key contrast with "in N hours"'s
  completion entailment. For an achievement, "in N hours" bounds when
  the (near-instantaneous) event happened but never means "spent N
  hours doing it" (289's `.no`), unless it's explicitly *repeated*
  (many species) over the window (291's `.yes`).
- **Downward-entailing durative "for"**: "P for N years/hours" entails
  "P for M years/hours" whenever `M ≤ N`, for states (298) and
  activities (301) and even accomplishments under the durative "for"
  coercion (303) alike — this is real `Nat` arithmetic (`omega`), not
  an assumed relation. The same "for N" does *not* entail "for exactly
  N" (299) or "for more than N" (286/293/296 — several of these stay
  `.unknown` rather than `.no`, since unlike an accomplishment's tight
  "in N hours" bound, a state/activity's "for N" doesn't fix an upper
  bound either).
- **Event-ordering chains** ("left before/after", "revised … before/
  after") are transitive and their `before`/`after` are exact converses
  for telic, punctual-enough predicates (261/262/264–268/270), modeled
  as real `Nat` timestamps closed by `omega`. The same chains over a
  bare *activity* or *state* repeated across sentences (269, 271–274)
  are `.unknown`: a second bare mention of "Smith swam"/"was present"/
  "was writing a report" need not pick out the same occasion as the
  first, so the timestamp identification the telic cases get for free
  cannot be assumed.
- **"Before" is non-factive, "after" is factive** about their embedded
  clause throughout this section (275's `.unknown` for "lost his
  temper", following only from a `before`-clause) — the semantic
  contrast this project's Section 7 design leans on hardest.
- **Interval-continuity word problems** (307, 314–317, 319, 321) are
  genuine arithmetic (day/step counting, or an explicit continuity
  hypothesis instantiated at a point within its range), closed with
  `omega` or by direct instantiation of a universal premise (307
  reuses `Every` from `FraCaS.Section1.GQ`).
- **A real scope ambiguity, not a degenerate problem** (308): FraCaS's
  own gold answer is "yes on one scoping, unknown on another" — this
  project gives the distributive (narrow-scope) and specific
  (wide-scope) readings their own theorems, per the established
  ambiguous-sentence pattern.
- **Factive attitude verbs** ("knew", 320/322) entail their
  complement directly; "discover"/"know after the fact" (325) is
  likewise treated as factive, licensing existential transfer from a
  premise already stated in "discover" terms.

No new lemmas are needed; this file records the approach only.
-/
