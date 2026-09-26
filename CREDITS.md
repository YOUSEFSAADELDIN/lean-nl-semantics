# Credits and licensing notes

This project is a from-scratch Lean 4 implementation of ideas published in
the papers below. It follows the **permissive route**: no code has been
copied from CoqLACL or FraCoq, and no data has been copied from the FraCaS
treebank. Contributors should keep it that way unless the licensing notes
below change.

## Primary sources (papers — reimplemented from published descriptions)

- Chatzikyriakidis & Luo, "Natural Language Inference in Coq," *Journal of
  Logic, Language and Information* 23(4):441–480, 2014.
  DOI: 10.1007/s10849-014-9208-x.
- Chatzikyriakidis & Luo, "Proof Assistants for Natural Language
  Semantics," LACL 2016.
- Chatzikyriakidis & Luo, "Adjectival and adverbial modification: The view
  from modern type theories," JoLLI 26(1):45–88, 2017.
- Chatzikyriakidis & Luo, "On the interpretation of common nouns: Types
  versus predicates," 2017.
- Chatzikyriakidis & Luo, "Identity Criteria of Common Nouns and dot-types
  for Copredication," 2018.
- Chatzikyriakidis & Luo, *Formal Semantics in Modern Type Theories*,
  Wiley/ISTE, 2020.
- Luo, "Formal semantics in modern type theories with coercive
  subtyping," *Linguistics and Philosophy* 35(6), 2012.
- Bernardy & Chatzikyriakidis, "A Type-Theoretical system for the FraCaS
  test suite: Grammatical Framework meets Coq," IWCS 2017.
- Chatzikyriakidis & Bernardy, "A Wide-Coverage Symbolic Natural Language
  Inference System," NODALIDA 2019.
- Bernardy & Chatzikyriakidis, "Applied Temporal Analysis: A Complete Run
  of the FraCaS Test Suite," Proc. 14th IWCS 2021, pp. 11–20.

## Reference implementations (consulted for architecture, not copied)

- **CoqLACL** — `github.com/StergiosCha/CoqLACL`. No LICENSE file as of
  this writing (default all-rights-reserved). Do not copy its `.v` files
  into this repository without the author's explicit permission. Contact
  the author before doing so.
- **FraCoq** — `github.com/GU-CLASP/FraCoq`. GPL-3.0. Its `.v`/`.hs` files
  are a derivative-work trigger under GPL-3.0: translating them directly
  into this repo would require relicensing this project GPL-3.0. Its
  architecture (GF abstract syntax tree → Haskell translation → target
  logic → proof) is the model for this project's planned GF pipeline; only
  that architectural pattern, not its code, has been reused here.
- **FraCaS-treebank** (Ljunglöf & Siverbo) —
  `github.com/heatherleaf/FraCaS-treebank`. GPL-3.0, v0.2 (2012). Same
  caveat as FraCoq: usable as a reference for GF abstract syntax trees, but
  copying its `.gf`/`.xml`/`.pl` files in verbatim makes this repo
  GPL-3.0 for the parts that include them.
- **formal_atlas_of_semantics** — `github.com/StergiosCha/formal_atlas_of_semantics`.
  MIT. Newer, active, much larger project by the same lead author: a
  230-source survey connected to Coq mechanizations, live-deployed at
  https://orange-beach-0c447e210.5.azurestaticapps.net. **This is now
  this project's primary Coq reference, superseding CoqLACL**:
  `atlas/mtt_ranta/MTT.v` (read directly, 541 lines, MIT) is a current,
  axiom-free, CI-verified formalization of exactly Chatzikyriakidis &
  Luo's MTT semantics — CNs as types, subtyping, judgmental
  interpretations, adjectives, veridical adverbs, copredication/dot-types,
  individuation, an NLI mini-suite, and an assumption audit (Parts 1-9;
  its own header cites CL14/CL20/L12, the same three papers this project
  is based on). It is cleaner and more current than CoqLACL and, being
  MIT, needs no permission to port from. **All nine parts are now
  ported** (`MTT/Quantifiers.lean`, `MTT/Subtyping.lean`,
  `MTT/Judgments.lean`, `MTT/Adjectives.lean`, `MTT/Adverbs.lean`,
  `MTT/DotTypes.lean`, `MTT/Individuation.lean`, `MTT/NLIExamples.lean`,
  `MTT/AssumptionAudit.lean`) — faithfully, theorem names and CL20
  section references kept alongside the Lean names so the correspondence
  stays checkable (Part 6's T-DOT3 excepted — Coq-section-local-coercion
  trick, doesn't generalise, see `DotTypes.lean`). Part 7 turned out not
  to need the `Prop`-irrelevance caveat noted throughout this repo — it
  compares plain equality on a concrete model, not which proof a Σ-type
  carries; see `Individuation.lean`. Part 8 is eight small worked
  entailments, not the full FraCaS suite — don't confuse it with the
  real Phase 2 work in `FraCaS/Data/Problems.lean`. Part 9 (`#print
  axioms` over the same 14 theorems `MTT.v` audits) is a genuine check,
  not a repeated claim, and it found something worth knowing: this repo
  has three real top-level `axiom`s (`CN.lean`'s `walk`,
  `Adjectives.lean`'s `Tall`, `DotTypes.lean`'s `Physical`/
  `Informational`) that `MTT.v`'s section-variable style avoids. 13 of
  the 14 audited theorems come back clean, but `copred_some`
  (`DotTypes.lean`) depends on `Physical`/`Informational` — not because
  it's less general than its neighbours, but because those two are free
  axioms rather than section variables, so anything mentioning
  `DotType Physical Informational` carries the dependency regardless.
  See `AssumptionAudit.lean` for the full accounting. It does *not*
  cover the full
  346-problem FraCaS suite (only a curated illustrative subset) and is
  Coq, not Lean, so a faithful Lean port plus the full FraCaS suite are
  both still open — see the README's roadmap. `atlas/mtt_ranta/Ranta.v`,
  `DTS.v`/`DTS_Resolution.v`, `MTT_vs_Ranta.v` and `atlas/ttr/TTR_vs_MTT.v`
  compare it against Ranta's/Bekki's DTS and Cooper's TTR — reference
  material for a future bridge/comparison file, not yet ported.
- **linglib** — `github.com/hawkrobe/linglib`. Apache-2.0. A large, active
  Lean 4 linguistics library. Confirmed by reading `Composition/Ty.lean`
  directly: its composition engine is Montagovian (a CN denotes at type
  `Ty.et`, i.e. `E → Prop` for a fragment-chosen entity type `E`), not MTT
  (CNs as types with their own elements) — the two are complementary, not
  overlapping. `MTT/CN.lean`'s `CNTag`/`ancestors`/`PartialOrder`/`by
  decide` pattern for the CN lattice is adapted directly from
  `Studies/Pustejovsky1995.lean`'s `SemType` (same file also formalizes
  Pustejovsky's *argument-selection* type coercion — a different problem
  from this project's dot-types/copredication, and not duplicated here;
  see `MTT/DotTypes.lean`). `MTT/LinglibBridge.lean` sketches connecting
  the two semantics over a shared entity domain; it is optional and not
  built by default (see that file for why).

## Data

- **FraCaS** (Cooper et al. 1996, LRE 62-051r). Machine-readable version:
  Bill MacCartney's `fracas.xml`, 346 problems, public domain with credit
  requested ("If you benefit from my work, please give me appropriate
  credit"). **Vendored** at `LeanNLSemantics/FraCaS/Data/fracas.xml`,
  fetched from a byte-identical GitHub mirror since the canonical
  `nlp.stanford.edu` host is unreachable from this project's sandbox; full
  provenance in `FraCaS/Data/SOURCE.md`. Transcribed into `Problem` values
  (`FraCaS/Types.lean`, `FraCaS/Data/Problems.lean`) — 342 of 346 (4 have
  an empty hypothesis in the source and are skipped). **All nine
  sections (all 342 formalizable problems) are formalized and proved**:
  `FraCaS/Section1/` (`GQ.lean` + `Batch1.lean`–`Batch5.lean`, 80
  problems) through `FraCaS/Section9/` (`Attitudes.lean` + `Batch1.lean`,
  13 problems, the final section), each theorem proved against its
  `Problem.answer`; see the README's Phase 2 section for the per-section
  breakdown and the documented divergences from FraCaS's own gold
  answers (Section 1's problems 56/61/62/77/78, Section 7's 256/257).

## GF and autoformalization tooling (background, not yet integrated)

- Grammatical Framework (`www.grammaticalframework.org`), `gf-core`,
  `gf-rgl`. GPL/BSD-family per component; check each before vendoring RGL
  sources.
- Informath (Ranta) and GFLean (Pathak): GF-to-proof-assistant tooling,
  math-only today. Architectural templates for the GF→Lean bridge in
  Phase 3 of the README's roadmap.
- ProofBridge (ICLR 2026) and Mathesis (Huawei): borrow the
  compile-then-semantic-equivalence verification loop for the LLM-fallback
  path in Phase 4, not any specific code.
