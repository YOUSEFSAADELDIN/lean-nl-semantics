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
  MIT. Newer, active Coq work by the same lead author, revisiting formal
  semantics in proof assistants (TTR/MTT/Ranta/DTS comparisons). Worth
  watching as a potential collaboration rather than a code source, since it
  targets Coq, not Lean.
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
  Bill MacCartney's `fracas.xml`
  (`nlp.stanford.edu/~wcmac/downloads/fracas.xml`), 346 problems, stated as
  public domain with credit requested. **Not yet vendored** — this
  session's network policy blocks `nlp.stanford.edu`; fetch it and drop it
  under `LeanNLSemantics/FraCaS/Data/` (with the source URL and date noted
  in a comment) from an environment that can reach it, then transcribe
  into `Problem` values per `FraCaS/Types.lean`.

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
