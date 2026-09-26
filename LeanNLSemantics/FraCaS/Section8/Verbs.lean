import Mathlib

/-!
# FraCaS Section 8 (Verbs) — approach

Section 8 (8 problems, 326–333) is short and tests aspect/telicity
distinctions already familiar from Section 7's Aktionsart work, plus
two plural-subject inferences:

- **Perfective vs. imperfective (the "imperfective paradox")**: a
  perfective accomplishment/achievement verb ("built", "won") entails
  its culmination ("finished", an actual win) via an assumed connecting
  fact (326, 328 — the same "assumed relation" style as Sections 5/6's
  comparatives), but the *progressive* ("was building", "was winning")
  does not — an in-progress accomplishment/achievement may never
  culminate, so 327/329 are `.unknown`.
- **Interval containment** (330): a state holding "from Y1 to Y2"
  entails holding at any year in between — the same `omega`-closed
  pattern as Section 7's continuous-"since" problems (252/255/314).
- **Plural-subject conjunction** (331/332): "Smith and Jones VP-ed"
  distributes to each named conjunct.
- **Collective-predicate existential closure** (333): "Smith, Anderson
  and Jones met" (a predicate that requires a plural/collective
  subject) trivially gives "there is a group that met".

No new lemmas are needed; this file records the approach only.
-/
