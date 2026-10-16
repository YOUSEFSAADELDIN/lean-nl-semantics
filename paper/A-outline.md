# Paper A: outline

Full drafts now exist: `A1-draft.md` (equivalence, translation, full
abstraction, setoids, FraCaS) and `A2-draft.md` (laws of counting, two
criteria, graph theory, the debate, the test). Together they cover every
result below; A1 §20 says how they would merge into one paper.

For you to react to before any prose is written. Every result named is a
Lean theorem in `EndToEnd/Encodings/` checked by CI (run numbers in that
directory's `README.md`), or a statement from a paper we have read
(`A-literature.md`). Status markers: **[have]** done and confirmed,
**[gap]** not done, **[decide]** needs your decision.

## Working titles [decide]

- One paper: **What a noun can mean, as far as sentences can tell: types,
  predicates and the laws of counting.**
- Or two papers (see "One paper or two?" below):
  - A1: **Nouns as types, nouns as predicates: an exact equivalence and
    where it ends.**
  - A2: **The laws of counting: one criterion, two criteria, and a
    test.**

## Thesis

Whether common nouns are types or predicates makes no difference to what
a fragment of English can say, with one exception: identity criteria.
The difference that remains can be stated exactly. What sentences can
observe of a noun is its counting units. Nouns that count by one
criterion obey laws that copredicated nouns, as Gotham and Chatzikyriakidis
& Luo describe them, can break. So the debate about copredication and
counting has a decidable empirical core: a law that one speaker's
answers either obey or break.

## Contributions

1. **Equivalence.** In a fragment with numerals, quantifiers, relative
   clauses, adjectives and two-place verbs, nouns as types (MTT, with
   coercions) and nouns as predicates validate the same entailments iff
   the coercions are injective (`valid_iff`, `validI_iff`,
   `not_valid_without_injectivity`; `Relational.lean`). [have]
2. **Characterization.** For nouns counting by an identity criterion,
   the two encodings agree under all verb interpretations iff each
   criterion is the individuals' identity. They fail in exactly two
   ways: splitting an individual (Luo's passengers) and merging
   individuals (Gotham's books) (`CModel.agree_iff_kernel`, `Characterization.lean`).
   [have]
3. **Translation.** Nouns as types with identity criteria (C&L 2018)
   are a word-by-word notational variant of predicates with criteria
   (Gotham 2017, Asher 2011), with one criterion per noun or several
   (`validC_iff`, `validM_iff`), and with the verb choosing
   (`validV_iff`). The same holds for selection (`wt_iff_of_sameFit`)
   and proof-theoretically (`Constructive.provT_iff`). Type checking
   stays decidable (`TypeCheck.check_iff`). [have]
4. **Full abstraction.** Two interpretations of a noun are
   indistinguishable by every sentence in every context iff they have
   the same counting units with the same multiplicities (`obsEq_iff`).
   This also holds with several criteria (`obsEqM_iff`), with plurals
   (`obsEqP_iff`), and in intensional contexts (`obsEqW_iff`; a
   hyperintensional attitude separates only by symbol,
   `thinks_distinguishes`). [have]
5. **Laws of counting.** One-criterion counts are exactly the integer
   coverage functions (`representation`, `units_unique`; the
   representation is Chakrabarty & Huang's). The typology: additive iff
   never merges, single iff never splits, both iff Montague
   (`additive_iff`, `single_iff`, `montague_iff`). Never splitting is
   Rothstein's and Landman's disjointness (`noSplit_iff_disjoint`).
   Every cell is inhabited (`cells_inhabited`). All one-criterion
   counts are submodular (`count_submod`). [have]
6. **Copredication.** Counting by two criteria is the least of the
   mixed one-criterion counts (`count2_eq_min`, by König's theorem via
   Hall), and no single criterion can stand in for it (`not_single`).
   The hierarchy is strict: coverage ⊊ two criteria ⊊ minima of
   coverage (`not_pairwise_example`). Two-criteria counts obey
   subadditivity, a pairwise law and an odd-cycle law. The first two do
   not characterize them (`two_laws_not_sufficient`). [have] An exact
   characterization via line graphs of bipartite multigraphs, for one
   thing per individual, depends on an unchecked graph-theory statement
   (`A-literature.md`, graph theory entry). [gap]
7. **Two findings about published papers.** C&L's (2015) injectivity
   axiom is exactly the equivalence condition. No equivalence relation
   gives C&L's (2018) dot-setoid counting in libraries their n. 4 accepts
   (`dotSame_not_transitive`, `exists_setoid_iff`, `no_setoid`). [have]
   Expert check before contacting the authors. [gap]
8. **A prediction and a protocol** that separate double distinctness,
   Property Versatility and Sutton's QUD account by the law
   (`A-prediction.md`). [have, not run; running it is your decision]
9. **FraCaS-scale comparison** (Phases 1-3): on FraCaS, the encodings
   differ almost nowhere. [have] **[decide]** whether this belongs in
   Paper A or in Paper B.

## Sections

### 1. Introduction

The types-versus-predicates debate (Ranta 1994; Luo 2012; C&L 2017;
Retoré 2013). The claim that types buy something, and the counter-claim
that they are notational. Our answer: notational, except for identity
criteria, and there the difference is exactly the counting units. Then
counting becomes the topic: copredication as the test case (Gotham 2017;
C&L 2015, 2018; Liebesman & Magidor 2017, 2026; Sutton 2024).
Contributions list.

### 2. The fragment and the two encodings

The grammar, the P and M encodings, models, and what "validate the same
entailments" means. Kept short, with the Lean development as the
reference.

### 3. Equivalence and where it ends

Contributions 1-2. Intuition first: coercions that merge individuals.
Passengers and books as the two failure modes. Answers Retoré's open
question for the fragment.

### 4. Criteria are notation

Contribution 3: the translation theorems. Positioning: C&L 2018
(setoids) vs Gotham 2017, Asher 2011 (predicates with criteria).
Neither side states a correspondence; both compare examples.

### 5. What sentences observe: full abstraction

Contribution 4. The four versions. The main point: the counting units
with multiplicities are everything a noun contributes. That
motivates studying counting functions directly.

### 6. The laws of counting

Contribution 5. The representation theorem. The typology table, with an
example per cell (passengers, copies, anthologies). Link to Rothstein's
contextual disjointness (2017, pp. 107-112) and Landman's disjoint base
(2020, §5.2, p. 144; §6.1.2, pp. 165-167) as the never-splits column.
Landman's neat mass nouns as a family of disjoint choices (p. 209).
Landman's indexing (§11.3) as the repair that allows double counting.

### 7. Copredication: two criteria

Contribution 6. The minimum-of-mixtures theorem, then
non-submodularity. The strict hierarchy and the laws. Graph-theory
reading: matchings in a bipartite multigraph of volumes and texts. Open
question: the exact class.

### 8. The setoid problem

Contribution 7. Kept factual and short. Bahramian et al. (2017) and
Gotham use no single identity relation, so the result bears on C&L 2018
only.

### 9. A test

Contribution 8. The law as a prediction that is independent of which
one-criterion account is right. Three hypotheses (DD, PV, QUD). Why the
law must be tested per speaker in a fixed context (Liebesman & Magidor's
reading switches). Why the anthology is unavoidable, and that it is the
contested reading (Sutton n. 1; C&L 2018 n. 4). Liebesman & Magidor's
counterexample (37) and Sutton's modifier pairs as further items.
Landman's processing cost as a second measure.

### 10. Limits

- A fragment, not English. No mass nouns, measure phrases or classifiers
  (Landman chs. 8-10). No context change within a sentence (Sutton's
  word-order effects).
- The criterion is held fixed. Rothstein's and Landman's main concern,
  how context sets it, is not modelled, except that a family of
  criteria can be.
- `count2` is a hypothesis about meaning, contested (Liebesman &
  Magidor). The theorems say what it implies, not that it is right.
- No experimental data.
- Machine-checked statements are only as good as their definitions. The
  definitions are given in the paper so readers can check them.

### 11. Related work

Gotham 2017, 2022; C&L 2015, 2017, 2018; Asher 2011; Luo 2012; Retoré
2013; Mery & Retoré 2013; Mery, Moot & Retoré 2019 (not read); Bekki
2014 and DTS; Bahramian et al. 2017; Liebesman & Magidor 2017, 2019,
2023, 2025, 2026; Sutton 2024; Rothstein 2017; Landman 2020; Barner &
Snedeker 2005 (via Rothstein and Landman); Chakrabarty & Huang 2012;
König, Hall; Harary & Holzmann 1974; Trotter 1977.

## One paper or two? [decide]

- **One paper.** The full story, from notation to laws to test. It
  would be long (sections 2-9 each carry a theorem family), and two
  audiences have to read all of it. Formal semantics readers want 3-5;
  readers of the copredication debate want 6-9.
- **Two papers.**
  - A1, "Equivalence": sections 2-5 and 8, for formal semantics and type
    theory venues.
  - A2, "Laws of counting": section 5 as background, then 6, 7 and 9,
    for semantics and philosophy of language venues, or as the
    theoretical half of an experimental paper once the test is run.

  A2 stands on its own: it needs only the definition of a noun with
  counting units and full abstraction as motivation.
- My recommendation: two papers. A2's results do not depend on the
  types-versus-predicates question, and the copredication debate is
  their natural audience. A1 is complete now, and A2 gains most from
  the experiment, which may take longer.

## Before drafting

- [gap] Check the Harary & Holzmann statement (or send the paper). If
  it holds, the exact characterization in contribution 6 is a short
  formalization away: the claw law and all odd-hole laws, plus the
  reduction.
- [gap] Read Gotham (2022) and Liebesman & Magidor (2019, 2023), the
  rest of the exchange, before section 9 is written.
- [gap] Expert check of contribution 7.
- [decide] Venue(s), and whether the FraCaS comparison stays here.
- [decide] Whether to run the experiment, and with whom.
