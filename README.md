# lean-nl-semantics

A Lean 4 port of Chatzikyriakidis & Luo's Modern Type Theory (MTT)
semantics — common nouns as types, subtyping via coercions, FraCaS-style
inference as theorem proving — with a planned GF-based autoformalization
pipeline. See `CREDITS.md` for sources and licensing.

No public Lean 4 port of this line of work exists yet (checked September
2026): CoqLACL (the original Coq implementation) has no Lean counterpart,
no FraCaS suite has been mechanized in Lean, and the closest existing Lean
linguistics library (`hawkrobe/linglib`) uses Montagovian predicate
semantics (nouns as `E → Prop`), not CNs-as-types.

## What this buys you that isn't out there already

1. The first Lean 4 library for MTT-semantics with CNs-as-types and
   coercive subtyping.
2. The first FraCaS benchmark mechanized in Lean 4.
3. A GF grammar/translator whose formal target is **NL semantics** in
   Lean, not mathematics (existing GF→proof-assistant tools — Informath,
   GFLean — only handle math).
4. A bridge comparing MTT and Montagovian (linglib) interpretations.
5. A hybrid GF-plus-LLM autoformalizer for NLI, checked against the
   grammar's own output.

## Layout

```
lean-toolchain              -- pinned Lean release channel
lakefile.toml                -- Lake package; depends on Mathlib
LeanNLSemantics.lean          -- umbrella import
LeanNLSemantics/
  MTT/
    CN.lean                  -- CN universe + subtyping (Coe instances)
    Quantifiers.lean          -- Some/Every/No over CN-typed domains
    Adjectives.lean           -- intersective adjectives via Subtype
    DotTypes.lean             -- copredication (Pustejovsky dot-types)
    Tense.lean                -- event/time skeleton
  Tactic/
    NLI.lean                  -- FraCaS proof automation (skeleton)
  FraCaS/
    Types.lean                -- Problem/Answer representation
    Data/                     -- (not yet populated -- see below)
CREDITS.md                   -- sources, licenses, what may/may not be copied
```

## Status and network limitations (read this before trusting a green check)

This scaffold was written in a sandboxed session whose network policy
allows `raw.githubusercontent.com` but blocks `github.com`,
`api.github.com`, `release.lean-lang.org`, and `nlp.stanford.edu`. Two
consequences:

- **The Lean/Mathlib toolchain has not been downloaded, and none of this
  code has been compiled.** `elan` is installed, but `elan default stable`
  and `lake build` both fail with 403s from the egress proxy on
  `release.lean-lang.org` / `github.com`. Every Lean snippet here is
  written to the best of current knowledge of Lean 4 + Mathlib syntax, but
  is unverified. In particular, check on first build whether `@[coe]` can
  be attached directly to an `axiom` (`MTT/CN.lean`) — if not, wrap the
  axiom in a `def` instead.
- **No FraCaS data is vendored.** MacCartney's `fracas.xml` lives on
  `nlp.stanford.edu`, which this session cannot reach. `FraCaS/Types.lean`
  defines the target shape (`Problem`, `Answer`); fetch the XML from an
  environment with access and transcribe it into `FraCaS/Data/*.lean`.

To fix the network restriction itself: broaden this environment's network
access (or add the specific hosts above to its allowed domains) from the
environment's settings, then re-run the build steps below.

### Building (once network access allows it)

```sh
curl --proto '=https' --tlsv1.2 -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
lake update        # resolves a Mathlib commit matching lean-toolchain
lake exe cache get # fetch prebuilt Mathlib .olean files (much faster than building)
lake build
```

## Licensing decision

MIT (see `LICENSE`). This project reimplements the papers directly rather
than porting CoqLACL's code (which carries no license file — treat as
all-rights-reserved) or FraCoq / the FraCaS-treebank (GPL-3.0). See
`CREDITS.md` for the full source list and what may or may not be copied
from each. `formal_atlas_of_semantics` (MIT, same lead author as CoqLACL,
active as of September 2026) is a plausible collaborator to reach out to
regarding a CoqLACL license, since it shows the author is still working in
this space with tooling similar to this one.

## Roadmap

- **Phase 0 — done here:** licensing decision, Lake scaffold, directory
  layout.
- **Phase 1 — core MTT library** (`MTT/*.lean`, started here): finish
  porting `MainCoq.v` and `Adjectives.v` (multidimensional adjectives,
  comparatives), then `CN_predhyp.v` and `Individuation.v`. Acceptance
  test: every example in `FracasCoq.v` restated and proved in Lean with
  the `nli` tactic.
- **Phase 2 — FraCaS harness:** vendor `fracas.xml` (see limitation
  above), parse it into `FraCaS/Data/SectionN.lean`, emit one
  `fracas_NNN` theorem per problem, and report YES/NO/UNK accuracy
  per-section against FraCoq's published numbers (83% on its 5 sections;
  81% overall including temporal reference) as a sanity baseline — not a
  target to match exactly, since the semantics differ (types vs.
  predicates).
- **Phase 3 — GF integration:** either a GF concrete syntax linearizing
  directly to Lean source (GFLean's approach) or a Haskell/Python
  PGF-AST-to-Lean translator (FraCoq's `FraToCoq.hs` approach, recommended
  for handling variable binding and eta-expansion correctly — see the
  `Quantifiers.lean` gotcha about coercions not passing through function
  types).
- **Phase 4 — LLM fallback:** for sentences outside the grammar's
  coverage, borrow ProofBridge's/Mathesis's compile-then-prove-equivalence
  loop, checked against the Lean REPL, to verify LLM-produced formulas
  against the GF-produced ones where both exist.

## Lean 4 encoding notes (see file-level doc comments for detail)

- Subtyping is `Coe` instances between CN-universe `axiom`s, chained via
  `CoeTC`. Declare only covering edges of the hierarchy; Lean does not
  check coercion-path coherence the way Coq warns about ambiguous paths,
  so add explicit `rfl` checks wherever two paths are relied on to agree.
- Coercions do not propagate through function types: a quantifier's
  predicate argument must be eta-expanded (`fun x => walk x`, never bare
  `walk`) for the per-argument coercion to fire. This is the emitter's
  job in Phase 3, not something to special-case with a generic
  `Coe (B → Prop) (A → Prop)` instance (that shape of instance is a known
  source of elaboration loops).
- Intersective/subsective adjectives are `Subtype`s (Lean's Σ-types);
  identity-criteria work (`Individuation.v`) will need re-checking against
  Lean's definitional proof irrelevance for `Prop`, which behaves
  differently from Coq's here.
