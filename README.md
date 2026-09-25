# lean-nl-semantics

A Lean 4 port of Chatzikyriakidis & Luo's Modern Type Theory (MTT)
semantics — common nouns as types, subtyping via coercions, FraCaS-style
inference as theorem proving — with a planned GF-based autoformalization
pipeline. See `CREDITS.md` for sources and licensing.

No public Lean 4 port of this line of work exists yet (checked September
2026, by reading the sources directly — see `CREDITS.md`): CoqLACL (the
original Coq implementation) has no Lean counterpart, no FraCaS suite has
been mechanized in Lean, and the closest existing Lean linguistics library
(`hawkrobe/linglib`) uses Montagovian predicate semantics (nouns as
`E → Prop`), not CNs-as-types.

**Goal:** primarily a novel research contribution — first FraCaS-in-Lean,
first MTT-in-Lean, something citable. If at some point that stops being
the more useful thing (Lean/Mathlib toolchain access turns out to be a
dead end here, or the community is clearly better served by a practical
NLI tool or a direct contribution to linglib instead), the project can
pivot to either of those without throwing away the core MTT library —
that's why the architecture below keeps linglib optional rather than
load-bearing.

**Architecture:** hybrid (see "Architecture decision" below) — a
standalone MTT core with no dependency on linglib, plus an optional,
not-built-by-default bridge module for interop.

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

## Architecture decision

Three shapes were on the table; picked **hybrid** (D):

- **A. Faithful CoqLACL port** — one `axiom` per CN, one hand-declared
  `Coe` per subtyping edge, mirroring `MainCoq.v`'s `Parameter`/`Axiom
  …Coercion…` almost line for line (confirmed by reading `MainCoq.v`
  directly — this really is the pattern it uses). Fastest to a working
  FraCaS harness, but doesn't use anything Lean can do that Coq couldn't:
  every CN is opaque, nothing is checkable by `decide`, and coercion-path
  coherence is asserted in a comment rather than proven.
- **B. Lean-idiomatic standalone** — what's actually in `MTT/CN.lean` now:
  the CN lattice is a `Fintype`/`DecidableEq` `inductive` with an
  `ancestors` list and a `PartialOrder` instance whose laws are `by
  decide`, adapted directly from a pattern already proven out in
  linglib's own `Studies/Pustejovsky1995.lean` (read from the source, not
  the earlier secondhand research summary). Coercion-path coherence is
  then a consequence of Lean's definitional proof irrelevance for `Prop`,
  not an assumption — see the `rfl`-checked example at the bottom of that
  file. CNs have a concrete, computable, `Subtype`-based interpretation
  (`CN.lean`'s toy `Individual` domain) instead of resting entirely on
  axioms.
- **C. linglib-integrated** — CNs as `Subtype`s cutting linglib's own
  entity domain (confirmed viable by reading `Composition/Ty.lean`:
  `Ty.Domain E W .e = E`, `.et = E → Prop`, generic in `E`, so this really
  does slot in cleanly). Maximal reuse, but makes this project's
  correctness and pace depend on a single-maintainer repo that was
  mid-rewrite of its own type system in September 2026, and arguably
  weakens the type-theoretic claim MTT is actually making (a CN that's
  still fundamentally "a flat domain cut by a predicate" is closer to
  Montague than to Luo).

**Chosen: standalone core (B's rigor) + optional bridge (C's interop),
never both by default.** `MTT/CN.lean` has zero dependency on linglib —
the library is a complete, citable artifact on its own. `MTT/LinglibBridge.lean`
sketches the connection over linglib's actual `E`/`Ty.Domain` (not a
guess) but isn't in `lakefile.toml` or the umbrella import, so building
the core never touches linglib. If the project's goal later shifts toward
"practical tool" or "contribute to linglib" (see the goal note above), the
bridge file is exactly the seam to build out from — including, per
linglib's own convention, potentially upstreaming a `Studies/`-style entry
into linglib itself rather than maintaining a separate dependency.

## Layout

```
lean-toolchain              -- pinned Lean release channel
lakefile.toml                -- Lake package; depends on Mathlib
LeanNLSemantics.lean          -- umbrella import
LeanNLSemantics/
  MTT/
    CN.lean                  -- CN lattice (CNTag) + CN-as-Subtype + coherence
    Quantifiers.lean          -- Some/Every/No over CN-typed domains
    Adjectives.lean           -- intersective adjectives via Subtype
    DotTypes.lean             -- copredication (Pustejovsky dot-types)
    Tense.lean                -- event/time skeleton
    LinglibBridge.lean        -- optional linglib interop; NOT built by default
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
  `release.lean-lang.org` / `github.com`. `MTT/CN.lean`'s lattice pattern
  (`inductive` + `ancestors` + `PartialOrder` + `by decide`) is adapted
  from `hawkrobe/linglib`'s `Studies/Pustejovsky1995.lean`, read directly
  from that repo rather than reconstructed from memory, which raises
  confidence but doesn't substitute for actually building it here — check
  `lake build` catches nothing on first run. `Quantifiers.lean`,
  `Adjectives.lean`, `Tactic/NLI.lean`, `DotTypes.lean`, `Tense.lean` are
  still closer to best-effort-from-known-syntax than confirmed-compiling.
- **FraCaS data is now vendored** (`FraCaS/Data/fracas.xml`, all 346
  problems) — `nlp.stanford.edu` itself stayed unreachable, but a
  byte-identical mirror on GitHub wasn't; see `FraCaS/Data/SOURCE.md` for
  exact provenance. Still needs transcribing into `Problem` values
  (`FraCaS/Types.lean` defines the target shape) — that's a parsing step,
  not a network problem, from here.

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
**Decision (this conversation, after reading `atlas/mtt_ranta/MTT.v`
directly)**: that file already solves Phase 1 cleanly, in Coq, current
and MIT. Redoing that design work from scratch in Lean is a weak novelty
claim once a better reference exists; porting it fast and putting the
real effort into the two things nothing does yet (the full FraCaS suite,
and a linglib bridge) is the better use of time. `CoqLACL` stays cited
for history; `MTT.v` is now the thing to actually port from.

- **Phase 1 — core MTT library, reframed as a port of `atlas/mtt_ranta/MTT.v`**
  (`MTT/*.lean`, `CNTag`/`CN`/`Quantifiers.lean` started here, predating
  this decision): translate its Parts 1–9 faithfully, crediting it
  explicitly in each file's header (see `CREDITS.md`) rather than
  re-deriving the design: Part 1–2 (CNs as types, subtyping, quantifier
  monotonicity) → `CN.lean`/`Quantifiers.lean`, already close, needs the
  monotonicity theorems (T-SUB1–3) added; Part 3 (judgmental
  interpretations) → new `MTT/Judgments.lean`; Part 4 (adjectives) →
  extend `Adjectives.lean`; Part 5 (veridical adverbs) → new
  `MTT/Adverbs.lean`; Part 6 (copredication/dot-types) → extend
  `DotTypes.lean`; Part 7 (individuation) → new `MTT/Individuation.lean`
  (watch the `Prop`-irrelevance caveat below); Part 8 (NLI mini-suite) →
  a handful of worked examples, distinct from the real Phase 2 suite;
  Part 9 (assumption audit) → adopt the practice, not just the port —
  keep a running list of what's still axiomatized.
- **Phase 2 — the actual novel contribution: the full FraCaS suite.**
  `fracas.xml` is vendored (`FraCaS/Data/fracas.xml`, all 346 problems —
  see `FraCaS/Data/SOURCE.md`). The data layer is done:
  `scripts/gen_fracas_problems.py` parses it into
  `FraCaS/Data/Problems.lean`, 342 `Problem` records (4 of 346 have an
  empty hypothesis in the source and are skipped), CI-checked
  (`problems.length = 342 := by decide`). Turning each `Problem`'s
  `premises`/`hypothesis` English strings into real formalized terms and
  proving or refuting each one is a per-sentence formalization effort,
  not a mechanical step.

  **Section 1 (Generalized Quantifiers, all 80 problems) is done** —
  `FraCaS/Section1/GQ.lean` (a two-predicate restrictor/scope quantifier
  encoding, `Every`/`Some`/`No`/`Most`/`AtLeast`/`AtMost`, distinct from
  `MTT/Quantifiers.lean`'s CN-typed quantifiers since Section 1 tests
  determiner inference patterns, not CN subtyping) plus five
  `Batch*.lean` files (`fracas_001`–`fracas_080`, one theorem/countermodel
  pair per problem, proved against `Problem.answer`). `.yes` problems
  prove `premises → hypothesis`; `.no` problems prove `premises →
  ¬hypothesis`; `.unknown`/`.undef` problems get a concrete two-direction
  countermodel (a model where the premises hold and the hypothesis does,
  another where they hold and it doesn't) — the constructive form of
  "attempt both directions, neither succeeds" this project settled on,
  since Lean has no general decision procedure for natural-language
  entailment to actually run in both directions. Two documented,
  deliberate divergences from FraCaS's own gold answers (problem 56, and
  61/62/77/78): this project's simplified treatment of "many"/"several"/
  "a few" as a plain `Some` and of "both"/"neither" as a plain
  `Every`/`No` (no proportional or exactly-two-elements reading) proves
  things FraCaS's own answer hedges or reads differently — flagged in
  each theorem's doc comment rather than silently mismatched. What's
  next: Sections 2–9 (plurals, anaphora, ellipsis, adjectives,
  comparatives, temporal, verbs, attitudes) need substantially more of
  `MTT.v`'s machinery (and new machinery `MTT.v` doesn't have at all —
  plurals/anaphora/ellipsis aren't in Chatzikyriakidis & Luo's own scope)
  before they're tractable the same way. Report YES/NO/UNK accuracy
  per-section as sections complete. Nobody has done this for all 346 in
  any proof assistant — FraCoq's published 83%/81% (5 sections, then a
  temporal subset) is the closest prior result and a sanity baseline, not
  a target to match exactly, since the underlying semantics differ
  (types vs. predicates).
- **Phase 2b — the other actual novel contribution: a linglib bridge.**
  `MTT/LinglibBridge.lean` already sketches the connection; atlas has no
  equivalent of linglib (an independent, large, actively-maintained
  predicate-semantics library) to bridge into, so this is Lean-specific
  territory regardless of what happens with the FraCaS suite.
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

- The CN universe is a `Fintype` `inductive` (`CNTag`) with an `ancestors`
  list and a `PartialOrder` instance proven `by decide`; `CN t` is a
  `Subtype` of a concrete individual domain cut by `x.kind ≤ t`.
  Coercion-path coherence — two routes through the lattice giving the same
  result — follows from Lean's definitional proof irrelevance for `Prop`
  rather than needing a separate check, though `CN.lean` still includes
  one concrete `rfl`-checked example. Named `Coe` instances are declared
  only for covering edges (for `↑` ergonomics); `CN.widen (by decide)`
  is the general-purpose fallback for any pair not covered.
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
