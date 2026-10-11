# lean-nl-semantics

A Lean 4 library for natural language semantics. Its core is a port of
Modern Type Theory (MTT) semantics — Chatzikyriakidis & Luo's account of
common nouns as types (rather than as predicates), with subtyping via
coercions. It also includes a full mechanization of the FraCaS test
suite for natural language inference, an end-to-end pipeline that
translates FraCaS from its English automatically, and a bridge to
`linglib`, a Montagovian (predicate semantics) library, for comparing
the two approaches.

It has four parts, each self-contained, with its own code, checks and
results:

1. **MTT core** (`LeanNLSemantics/MTT/`): the semantics itself.
2. **The FraCaS corpus** (`LeanNLSemantics/FraCaS/`): all 342 problems as
   hand-written Lean theorems, with a certified monotonicity reasoner, a
   GF cross-check of their English, and an evaluation of whether a fixed
   prover recovers each gold answer (`BLIND_EVAL.md`).
3. **The linglib bridge** (`bridge/`): MTT's nouns-as-types against
   linglib's nouns-as-predicates, as a separate Lake package.
4. **The end-to-end pipeline** (`EndToEnd/`): FraCaS translated
   automatically from its original English and scored by its own prover
   (`EndToEnd/README.md`).

**Which parts are MTT.** Only parts 1 and 3 use nouns as types. Parts 2
and 4 state every problem with nouns as *predicates* over one domain of
individuals (`commissioner : A → Prop`, `Every commissioner
spendTimeAtHome`), the encoding of Montague semantics. Where they use an
MTT idea - adjective classes, subtyping between nouns, a possessive as a
function of its possessor - it is restated as a predicate fact or a
function on that domain, not as a type. (One file, `FraCaS/Section1/
Monotonicity/CNAdapter.lean`, derives two such facts from part 1's noun
lattice.) So the FraCaS results in parts 2 and 4 are results about that
encoding and about the methods around it - parsing, reading ambiguity,
the prover - and do not by themselves show anything for or against
MTT. Comparing the two encodings on the same problems, with everything
else held fixed, is future work.

The browser lab (below) is meant to end up demoing all four.

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
- **FraCaS suite** (`LeanNLSemantics/FraCaS/`; nouns as predicates,
  see "Which parts are MTT" above): all 342 formalizable
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
- **GF cross-check** (part of the FraCaS corpus; `gf/`, scope
  intentionally bounded — see below): a Grammatical Framework grammar
  and a Python translator producing Lean terms from a hand-built (not
  freely parsed) English sentence tree, used to cross-check the FraCaS
  formalizations above against real English via `linearize`. (The
  end-to-end pipeline, part 4, reuses this grammar for *parsing*, with
  its own restricted parse grammar; that is its own scope, below.)
  Every one of the 342 problems' sentences that this grammar can build
  at all now has a real, independently-
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
  `translate.py`'s default mode, which this cross-check uses — each one's whole point is a distinction (privative
  adjectives, assumed comparative relations, factivity) that
  `translate.py`'s own generic predicate-fusion would silently collapse
  rather than translate faithfully — but still get real GF sentences.
  A handful of problems per section are skipped for GF purposes with a
  documented reason (a construction this grammar has no combinator for,
  e.g. embedded questions, or specific calendar-date arithmetic) — see
  `gf/FraCaSLogicEng.gf`'s own per-section comments and `gf/NOTES.md`
  for the full setup and every gotcha hit along the way.

- **End-to-end pipeline** (`EndToEnd/`, part 4; nouns as predicates,
  like part 2): FraCaS's original
  English parsed with a restricted GF grammar, the top reading chosen by
  a generic ranker and translated by `gf/translate.py` under the
  pipeline's own readings of ambiguous English (`EndToEnd/readings.py`),
  scored by its own prover. It reaches 260 of 342 problems and matches
  gold on 181 of them as translated (240 with problem-independent
  background knowledge), with no wrong answers. These are
  **development-set** figures: the pipeline was extended by looking at
  which of these same problems failed. Full write-up:
  `EndToEnd/README.md`.

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
EndToEnd/                    -- part 4: the end-to-end pipeline (its own Lake library)
gf/                           -- Grammatical Framework grammar + cross-checks (the
                                 end-to-end pipeline extends this grammar in EndToEnd/)
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
(the GF/RGL toolchain, the 810 `linearize` checks of `gf/`'s grammar
and the end-to-end pipeline's own 46, must stay green).

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
  sentence — so for this cross-check sentences are hand-built as GF
  abstract trees and checked against the target English via
  `linearize`, the same way FraCoq's own FraCaS-treebank was built. (The
  end-to-end pipeline later made parsing usable with a grammar
  restricted to FraCaS's vocabulary; see `EndToEnd/README.md`.) This phase's scope was always
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
  blind evaluation addresses the obvious follow-up question — whether
  that count reflects real automated entailment-checking or just a
  human confirming a proof they already knew existed — by taking each
  bare theorem's *type* only (never its hand-written proof) and letting
  a fixed tactic chain alone decide yes/no/unknown (`BlindEval.lean`,
  `BlindEvalSections3to9.lean`); each `.unknown`/`.undef` problem, which
  the corpus represents as a `_dir1`/`_dir2` countermodel pair rather
  than a single statement, is evaluated through a generalized,
  deliberately unprovable claim instead, where the correct outcome is
  that *neither* direction closes (`BlindEvalUnknownScan.lean`,
  `BlindEvalUnknown3to9Scan.lean`). CI-confirmed: **336/342 (98.2%)**
  automated verdicts match FraCaS's gold answer, with every problem in
  the corpus attempted, against a 31.0% always-"unknown" baseline; the 6
  misses are proofs the chain fails to find, never wrong ones. (An
  earlier round's 314/322 was produced while the chain's `aesop` step
  was silently failing on every goal — see `BLIND_EVAL.md`.) That score
  covers inference over *hand-translated* `Prop`s, so it is not
  comparable to FraCoq's 83%/81%, whose pipeline translates English
  automatically. The end-to-end pipeline (part 4, `EndToEnd/README.md`)
  is the comparable kind of measurement. **`BLIND_EVAL.md`** is the full
  writeup of this one: methodology, exact per-scan results, every
  remaining miss and why, and its limitations. Its prover is frozen, so
  work on the end-to-end pipeline cannot move this number.
- **End-to-end pipeline** (part 4) — ongoing; see `EndToEnd/README.md`.
- **General natural-language inference** — a substantially larger,
  separate undertaking (open-vocabulary parsing, world/taxonomic
  knowledge, automated entailment over arbitrary sentences, more
  languages) this project's foundations could feed into, not something
  the phases above complete on their own.

## License

MIT — see `LICENSE`. See `CREDITS.md` for what this project depends on
or was ported from, and their licenses.
