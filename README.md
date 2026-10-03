# lean-nl-semantics

A Lean 4 library for natural language semantics based on Modern Type
Theory (MTT) — Chatzikyriakidis & Luo's account of common nouns as
types (rather than as predicates), with subtyping via coercions. It
includes a full mechanization of the FraCaS test suite for natural
language inference, and a bridge to `linglib`, a Montagovian (predicate
semantics) library, for comparing the two approaches.

**[Try the Semantics Lab](https://yousefsaadeldin.github.io/lean-nl-semantics/lab.html)**
— build a controlled-English sentence, watch its real GF syntax tree,
and check whether a conclusion is licensed by a Lean-verified rule, all
live in the browser. Also live: the [full corpus
reference](https://yousefsaadeldin.github.io/lean-nl-semantics/index.html),
the [reasoner trace explorer](https://yousefsaadeldin.github.io/lean-nl-semantics/trace.html),
and a [plain-language entailment walkthrough](https://yousefsaadeldin.github.io/lean-nl-semantics/entailment.html).

## Status

- **MTT core** (`LeanNLSemantics/MTT/`): a Lean 4 port of the MTT
  semantics described in Chatzikyriakidis & Luo's papers (see
  `CREDITS.md`), covering common nouns as types, coercive subtyping,
  quantifiers, adjectives, adverbs, copredication/dot-types, and
  individuation.
- **FraCaS suite** (`LeanNLSemantics/FraCaS/`): all 342 formalizable
  problems from the FraCaS test suite (Cooper et al. 1996; 4 of the
  original 346 have no question/hypothesis in the source and are
  skipped) are formalized as Lean theorems, one per problem, each
  proved against its recorded gold answer. See "The FraCaS suite"
  below for details.
- **linglib bridge** (`bridge/`): a bridge connecting this project's
  CN-as-type semantics to `linglib`'s CN-as-predicate semantics over a
  shared entity domain, built as its own separate Lake package so it
  can't affect the main library's build. Beyond the shared-domain
  connection itself: two general theorems (`CN'.intersective_widen`,
  `KindedLexicon`) generalizing fragment-specific Section 5 results into
  reusable bridge-level lemmas; a real linglib fragment wired in
  (`Linglib.Fragments.English.Toy`'s own four-entity model, not an
  invented domain) as a genuine instance of the general theorems rather
  than only this project's own constructions; and a cross-validation of
  Section 1/2's independently-built GQ layer (`Every`/`Some`/`No`/`card`/
  `Exactly`) against linglib's own `Quantifier.GQ` theory, confirming the
  two agree and that this project's hand-proved monotonicity lemmas are
  literal instances of linglib's general, already-proven ones.
- **GF integration** (`gf/`, scope intentionally bounded — see below): a
  Grammatical Framework grammar and a Python translator producing Lean
  terms from a hand-built (not freely parsed) English sentence tree,
  used to cross-check the FraCaS formalizations above against real
  English via `linearize`. Every one of the 342 problems' sentences
  that this grammar can build at all now has a real, independently-
  confirmed GF tree — 803 `linearize` checks across all nine FraCaS
  sections (`gf/run_gf_tests.py`), validated against a real local
  GF/RGL toolchain (not just parsed as text) before ever being pushed.
  `gf/translate.py` additionally cross-checks a subset of Sections 1-2
  by translating a GF tree straight into the same Lean `Prop` shape
  the hand-written proof already uses — a genuine mechanical
  cross-check, not a similarity check
  (`LeanNLSemantics/FraCaS/Section1/GFCrossCheck.lean` wires one such
  tree, problem 2's first premise, directly into its real proved
  theorem). Later sections (5 onward) deliberately don't extend
  `translate.py` — each one's whole point is a distinction (privative
  adjectives, assumed comparative relations, factivity) that
  `translate.py`'s own generic predicate-fusion would silently collapse
  rather than translate faithfully — but still get real GF sentences.
  A handful of problems per section are skipped for GF purposes with a
  documented reason (a construction this grammar has no combinator for,
  e.g. embedded questions, or specific calendar-date arithmetic) — see
  `gf/FraCaSLogicEng.gf`'s own per-section comments and `gf/NOTES.md`
  for the full setup and every gotcha hit along the way.

  This is deliberately not aimed at general English coverage — FraCaS
  is a small, closed vocabulary and sentence set, and covering it was
  always the actual scope. "General natural-language inference" (open
  vocabulary, world knowledge like car ⊆ vehicle, automated entailment
  over arbitrary sentences, further languages) is a substantially
  larger, separate undertaking this project's foundations could
  eventually feed into, not something the phases below complete.

## Layout

```
lean-toolchain              -- pinned Lean release
lakefile.toml                -- Lake package definition (depends on Mathlib)
LeanNLSemantics.lean          -- umbrella import
LeanNLSemantics/
  MTT/
    CN.lean                  -- the CN lattice and CN-as-type encoding
    Quantifiers.lean          -- Some/Every/No over CN-typed domains
    Adjectives.lean           -- intersective/subsective/privative adjectives
    Adverbs.lean              -- veridical adverbs
    DotTypes.lean             -- copredication (Pustejovsky dot-types)
    Individuation.lean        -- identity criteria
  FraCaS/
    Types.lean                -- Problem/Answer representation
    Data/                     -- fracas.xml + the 342 parsed Problem records
    Section1/ .. Section9/    -- all 342 problems, formalized
bridge/                      -- the linglib bridge, a separate Lake package
  lakefile.toml
  LinglibBridge.lean
gf/                           -- Grammatical Framework grammar + cross-checks
scripts/                      -- generators for the files gf/ and FraCaS/ commit
viz/                          -- data exports + the three live visualizer pages
lake-manifest.json            -- pinned Mathlib commit
LICENSE
CREDITS.md                   -- sources and licensing
```

## Building

```sh
curl --proto '=https' --tlsv1.2 -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
lake update        # resolves a Mathlib commit matching lean-toolchain
lake exe cache get # fetch prebuilt Mathlib .olean files
lake build
```

The linglib bridge is a separate package and isn't built by the above;
build it explicitly with:

```sh
cd bridge
lake update
lake exe cache get
lake build
```

CI (`.github/workflows/build.yml`) runs three jobs on every push: `build`
(the main package, must stay green), `build-linglib-bridge`
(informational, won't fail the workflow if it breaks), and `build-gf`
(the GF/RGL toolchain plus all 803 `linearize` checks, must stay green).

## The FraCaS suite

Each of the 342 problems is its own Lean theorem. `.yes` problems prove
`premises → hypothesis`; `.no` problems prove `premises → ¬hypothesis`;
`.unknown`/`.undef` problems get a concrete two-direction countermodel
(one model where the premises hold and the hypothesis does, another
where they hold and it doesn't) — Lean has no general decision procedure
for natural language entailment, so this is the constructive stand-in
for "neither direction is a validity."

A handful of problems have a documented, deliberate divergence from
FraCaS's own gold answer, flagged in the relevant theorem's doc comment
rather than silently mismatched — mostly from this project's simplified
treatment of "many"/"several"/"a few" as a plain existential and of
"both"/"neither" as a plain universal/negation, without a proportional
or exactly-two-elements reading. Every theorem's proof shape has been
checked by hand against its recorded gold answer across all 342
problems; as of the last audit, 338/342 match exactly, the remaining 4
are the documented divergences above, and there are no unexplained
mismatches. (This is a manual audit, not a reproducible script — nothing
in this repo automates it yet.)

This isn't directly comparable to prior published accuracy numbers
(e.g. FraCoq's 83%/81%): those come from a pipeline that predicts an
answer automatically and compares it to gold; here, the gold answer was
an input to each formalization, so the check above is an internal
consistency check, not a blind-prediction accuracy score.

## Roadmap

- **MTT core** — done. Ported from `formal_atlas_of_semantics`'s
  `MTT.v` (see `CREDITS.md`), covering all nine parts of that
  formalization.
- **FraCaS suite** — done. All 342 formalizable problems, all nine
  sections.
- **linglib bridge** — done, and still exploratory by design (Phase 2b,
  its own pinned dependency, isolated so it can't affect the main
  library). A separate Lake package connecting this project's CN-as-type
  semantics to linglib's CN-as-predicate semantics, now including a real
  linglib fragment (not just this project's own invented domains), two
  general bridge-level theorems, and a confirmed correspondence between
  Sections 1/2's own GQ layer and linglib's independent one — see
  "Status" above.
- **GF integration** (`gf/`) — done, for the scope it set out to cover.
  A Grammatical Framework grammar producing real, `linearize`-confirmed
  English for every FraCaS sentence this grammar can build (803 checks
  across all nine sections), rather than each sentence being hand-
  formalized with no independent check on its own English gloss.
  `gf/translate.py` additionally cross-checks a subset of Sections 1-2
  by translating a GF tree straight into the same Lean `Prop` shape the
  hand-written proof uses, with one such tree wired directly into its
  real proved theorem as a genuine mechanical cross-check (not just a
  standalone proposition) — see `gf/NOTES.md`/`gf/translate.py` and
  `LeanNLSemantics/FraCaS/Section1/GFCrossCheck.lean`. Free parsing
  against GF's own full English grammar turned out not to be usable for
  this — it's built to be maximally permissive and produces an
  effectively unbounded number of alternate readings for even a simple
  sentence — so sentences are hand-built as GF abstract trees and
  checked against the target English via `linearize`, the same way
  FraCoq's own FraCaS-treebank was built. This phase's scope was always
  FraCaS's own closed sentence/vocabulary set, not general English —
  see the GF integration note above for why. GF's resource grammar
  library covers many languages under one abstract syntax, so the
  abstract syntax and translator are language-agnostic already, but
  further languages aren't a near-term goal.
- **Certified monotonicity/natural-logic reasoner** (`LeanNLSemantics/
  FraCaS/Section1/Monotonicity/`) — done, through Phase 5, CI-confirmed.
  A Lean tactic (`mono_nl`) that closes a scoped fragment of FraCaS
  Section 1/2 goals automatically, by computing which argument position
  of `Every`/`Some`/`AtLeast`/`AtMost` a substitution needs and applying
  the one already-proved `GQ.lean` lemma that direction licenses —
  replacing bespoke per-problem proof terms with one general, sound (by
  construction, not by a separate reflected interpreter) search
  procedure, widened over five phases (substitution, existential
  transfer, composition, and conditioned narrowing — see `Tactic.lean`,
  `Existential.lean`, `Compose.lean` for each phase's own grounding) to
  close every eligible problem, not just the ones it started with.
  Deliberately not an LLM-based path — every rule is grounded in an
  already-proved lemma, the same "prove it, don't assume it" standard
  the rest of this project holds to, not a probabilistic fallback.
  `Coverage.lean`'s own header tracks the one current, authoritative
  corpus-wide count (not duplicated here, so it can't go stale in two
  places — see that file for the current scanned/proved/eligible-failed
  numbers and, as of the corpus's growth past Phase 5, a breakdown of
  what the remaining eligible-but-failed cases actually are). A separate
  blind evaluation
  (`BlindEval.lean`) addresses the obvious follow-up question — whether
  that count reflects real automated entailment-checking or just a
  human confirming a proof they already knew existed — by taking each
  bare Section 1/2 theorem's *type* only (never its hand-written proof)
  and letting the tactics alone decide yes/no/unknown: **47/47 (100%)**
  automated verdicts matched FraCaS's own gold answer, CI-confirmed.
  That scope is still Sections 1–2 only, and even there it skips the
  countermodel-pair (`.unknown`/`.undef`) problems a binary yes/no/
  unknown procedure has no single entailment-shaped question to ask
  about — extending past that (more of Sections 1–2's own skipped
  problems, or into Sections 3–9) is the most direct next step toward a
  blind accuracy figure actually comparable to prior published ones
  (e.g. FraCoq's 83%/81%), per the note under "The FraCaS suite" above.
- **General natural-language inference** — a substantially larger,
  separate undertaking (open-vocabulary parsing, world/taxonomic
  knowledge, automated entailment over arbitrary sentences, more
  languages) this project's foundations could feed into, not something
  the phases above complete on their own.

## License

MIT — see `LICENSE`. See `CREDITS.md` for what this project depends on
or was ported from, and their licenses.
