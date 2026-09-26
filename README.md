# lean-nl-semantics

A Lean 4 library for natural language semantics based on Modern Type
Theory (MTT) — Chatzikyriakidis & Luo's account of common nouns as
types (rather than as predicates), with subtyping via coercions. It
includes a full mechanization of the FraCaS test suite for natural
language inference, and a bridge to `linglib`, a Montagovian (predicate
semantics) library, for comparing the two approaches.

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
- **linglib bridge** (`bridge/`): a small bridge connecting this
  project's CN-as-type semantics to `linglib`'s CN-as-predicate
  semantics over a shared entity domain, built as its own separate Lake
  package so it can't affect the main library's build.
- **Not yet started**: a Grammatical Framework (GF) grammar to parse
  English (and eventually other languages GF supports) directly into
  these Lean terms, rather than each sentence being hand-formalized.

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
    Tense.lean                -- event/time skeleton
  Tactic/
    NLI.lean                  -- proof automation helpers
  FraCaS/
    Types.lean                -- Problem/Answer representation
    Data/                     -- fracas.xml + the 342 parsed Problem records
    Section1/ .. Section9/    -- all 342 problems, formalized
bridge/                      -- the linglib bridge, a separate Lake package
  lakefile.toml
  LinglibBridge.lean
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

CI (`.github/workflows/build.yml`) builds both on every push — the main
build must stay green; the bridge build is informational and won't fail
the workflow if it breaks.

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
or exactly-two-elements reading. A script cross-checks every theorem's
proof shape against its recorded gold answer across all 342 problems;
as of the last run, 338/342 match exactly, the remaining 4 are the
documented divergences above, and there are no unexplained mismatches.

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
- **linglib bridge** — done. A separate Lake package connecting this
  project's CN-as-type semantics to linglib's CN-as-predicate semantics.
- **GF integration** (next up) — a Grammatical Framework grammar that
  parses natural language sentences directly into the Lean terms this
  project already proves things about, rather than each sentence being
  hand-formalized. GF's resource grammar library covers many languages
  under one abstract syntax, so the intent is for this to not be
  English-only over time: a language-agnostic abstract syntax plus a
  translator into Lean, with per-language concrete syntax added
  incrementally.
- **LLM-assisted fallback** — for sentences outside the grammar's
  coverage, an LLM-based formalization path checked against the
  grammar's own output where both exist.

## License

MIT — see `LICENSE`. See `CREDITS.md` for what this project depends on
or was ported from, and their licenses.
