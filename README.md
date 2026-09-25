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
- **Phase 1 — core MTT library** (`MTT/*.lean`, started here): the
  `CNTag` lattice foundation is in place; next is growing `CNTag` to
  cover `MainCoq.v`'s actual CN set (confirmed by reading it: `bank`,
  `manager`, `car`, `delegate`, `student`, `swede`, `scandinavian`, ~30
  more), porting multidimensional adjectives and comparatives from
  `Adjectives.v`, then `CN_predhyp.v` and `Individuation.v` — the latter
  needs care around Lean's definitional proof irrelevance for `Prop`
  (see encoding notes below). Acceptance test: every example in
  `FracasCoq.v` restated and proved in Lean with the `nli` tactic — note
  `FracasCoq.v` itself mostly uses hand-written `cbv; intro; exists x;
  assumption`-style scripts rather than one robust automation tactic
  (confirmed by reading it), so matching or beating that bar is a
  realistic goal for `nli`, not a given.
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
