# Credits and licensing

This project is MIT licensed (see `LICENSE`). Nothing in this codebase
is copied from a copyleft (GPL) or all-rights-reserved source — where
those were consulted, it was for architecture or ideas, never for code
or data. The rest of this file explains what's actually a dependency or
a direct port, and what was only ever read for reference.

## Direct ports and dependencies

- **`formal_atlas_of_semantics`** —
  `github.com/StergiosCha/formal_atlas_of_semantics`, MIT. The MTT core
  in `LeanNLSemantics/MTT/` is a Lean port of `atlas/mtt_ranta/MTT.v`
  from this repo, a Coq formalization of Chatzikyriakidis & Luo's MTT
  semantics (common nouns as types, subtyping, quantifiers, adjectives,
  adverbs, copredication, individuation). Being MIT, this needed no
  special permission to port from, and it's credited in each ported
  file's header alongside the original theorem names.
- **`linglib`** — `github.com/hawkrobe/linglib`, Apache-2.0. Two uses:
  the `CNTag`/`ancestors`/`PartialOrder` lattice pattern in `MTT/CN.lean`
  is adapted from this library's `Studies/Pustejovsky1995.lean`, and
  `bridge/LinglibBridge.lean` is a genuine dependency on linglib's
  `Semantics.Composition.Ty` module, built as a separate Lake package
  (see that file and `bridge/lakefile.toml`).
- **FraCaS test data** — Cooper et al. 1996 (LRE 62-051r), via Bill
  MacCartney's machine-readable `fracas.xml`. Public domain, credit
  requested. Vendored at `LeanNLSemantics/FraCaS/Data/fracas.xml`; see
  `FraCaS/Data/SOURCE.md` for exact provenance.

- **MED** (Monotonicity Entailment Dataset) — Yanaka, Mineshima, Bekki,
  Inui, Sekine, Abzianidze and Bos 2019, `github.com/verypluming/MED`,
  commit `860ba36`, **CC BY-SA 4.0**. Vendored unmodified at
  `EndToEnd/HeldOut/MED.tsv` as the end-to-end pipeline's held-out test
  (see `EndToEnd/HeldOut/README.md`). That file, and anything derived
  from its sentences (`EndToEnd/HeldOut/Claims.lean`), stays under CC
  BY-SA 4.0, not MIT. Part of MED is itself drawn from FraCaS and the GLUE
  diagnostics; the FraCaS part is excluded from the test.
- **SICK** (Sentences Involving Compositional Knowledge) — Marelli,
  Menini, Baroni, Bentivogli, Bernardi and Zamparelli, LREC 2014,
  University of Trento, **CC BY-NC-SA 3.0**. Its SemEval 2014 test split
  is vendored, rows and columns unaltered, at
  `EndToEnd/HeldOut/SICK/SICK_test.tsv` as the pipeline's second held-out
  test (see `EndToEnd/HeldOut/SICK/README.md`). That file, and anything
  derived from its sentences (`EndToEnd/HeldOut/SICK/Claims.lean`,
  `SickNames*.gf`, `sick.json`), stays under CC BY-NC-SA 3.0, not MIT:
  attribution, non-commercial use only, and the same licence for
  derivatives.

## Read for reference only, not used

These were looked at for architecture or ideas during design, but
nothing from them — no code, no grammar files, no data — is in this
repository, so their licenses don't affect this project's own:

- **CoqLACL** (`github.com/StergiosCha/CoqLACL`) — an earlier Coq
  implementation of the same MTT semantics, and the original reference
  point before `formal_atlas_of_semantics` was found and used instead.
  Has no LICENSE file (default all-rights-reserved); nothing from it
  ended up in this codebase.
- **FraCoq** (`github.com/GU-CLASP/FraCoq`, GPL-3.0) and the
  **FraCaS-treebank** (`github.com/heatherleaf/FraCaS-treebank`,
  GPL-3.0) — a prior Coq mechanization of the FraCaS suite and its
  companion GF treebank. Consulted for how a GF-to-proof-assistant
  pipeline can be structured (relevant to the GF integration work
  ahead); no `.v`, `.hs`, `.gf`, or `.pl` files from either were copied.
  `gf-rgl`'s own bundled copy of this same treebank data
  (`src/english/treebank.txt`, not part of this repo) is used the same
  reference-only way during Phase 3 grammar work: it's read to identify
  which RGL functions a target sentence needs and to cross-check a
  design, but every tree actually committed to `gf/FraCaSLogic*.gf` is
  independently written using the RGL's own LGPL/BSD public API, never
  copied from it verbatim.
- Grammatical Framework itself (`www.grammaticalframework.org`,
  `gf-core`, `gf-rgl`) and related tooling (Informath, GFLean,
  ProofBridge, Mathesis) — background reading for the GF integration
  and LLM-fallback roadmap items. Each has its own license; anything
  actually vendored from them later (e.g. resource grammar sources)
  needs its own license check at that point.

## Background reading

The MTT semantics this project implements (via `formal_atlas_of_semantics`)
comes from this line of papers by Chatzikyriakidis & Luo and
collaborators:

- "Natural Language Inference in Coq," *JoLLI* 23(4):441–480, 2014.
- "Proof Assistants for Natural Language Semantics," LACL 2016.
- "Adjectival and adverbial modification: The view from modern type
  theories," *JoLLI* 26(1):45–88, 2017.
- "On the interpretation of common nouns: Types versus predicates," 2017.
- "Identity Criteria of Common Nouns and dot-types for Copredication," 2018.
- *Formal Semantics in Modern Type Theories*, Wiley/ISTE, 2020.
- Luo, "Formal semantics in modern type theories with coercive
  subtyping," *Linguistics and Philosophy* 35(6), 2012.
- Bernardy & Chatzikyriakidis, "A Type-Theoretical system for the
  FraCaS test suite: Grammatical Framework meets Coq," IWCS 2017.
- Chatzikyriakidis & Bernardy, "A Wide-Coverage Symbolic Natural
  Language Inference System," NODALIDA 2019.
- Bernardy & Chatzikyriakidis, "Applied Temporal Analysis: A Complete
  Run of the FraCaS Test Suite," Proc. 14th IWCS 2021, pp. 11–20.

These describe the ideas this project implements; the actual Lean code
was ported from `formal_atlas_of_semantics`'s Coq implementation, not
written from these papers directly.
