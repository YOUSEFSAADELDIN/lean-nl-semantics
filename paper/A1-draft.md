# Nouns as types, nouns as predicates: an exact comparison

*Draft A1, October 2026. Not for circulation. Every theorem cited is
proved in Lean 4 in `EndToEnd/Encodings/` of this repository and checked
by continuous integration (CI); the run numbers are in Appendix A. Every
literature claim is from a source read for this project
(`paper/A-literature.md`), unless marked "not read".*

*This is one of two drafts. A2 (`paper/A2-draft.md`) develops the laws
of counting that §12 here introduces. Read together, the two are the
whole of Paper A; §20 of this draft says how they would merge into one
paper.*

---

## Abstract

Should a common noun be interpreted as a predicate of individuals, as in
Montague semantics, or as a type, as in Modern Type Theories (MTTs)?
Proponents of nouns as types argue that the choice matters for
inference, above all for counting, through the identity criteria that
nouns carry. We settle the question for a fragment of English, with
proofs checked in Lean.

1. **Equivalence.** In a fragment with nine determiners, "more ... than",
   one- and two-place verbs, identity, nested quantifiers and the
   connectives, nouns as types and nouns as predicates validate exactly
   the same entailments when each noun's embedding into the individuals
   is injective. Without injectivity they part.
2. **Counting individuals.** If typed counting counts individuals, the
   condition disappears.
3. **Characterization.** For nouns that count by arbitrary identity
   criteria, the encodings agree under all interpretations of the verbs
   exactly when every criterion is the individuals' own identity. They
   can fail in only two ways: splitting an individual (Luo's
   passengers) or merging individuals (Gotham's books).
4. **Translation.** Even then the difference is notational. Nouns as
   types with identity criteria translate word by word into nouns as
   predicates over a richer domain with criteria. This holds with one
   criterion per noun, with several (copredication), and with the verb
   choosing the criterion. It also holds proof-theoretically, with no
   axioms.
5. **Full abstraction.** What every sentence of the fragment, in every
   context, can observe of a noun is exactly its multiset of counting
   units. For nouns that count individuals it is exactly the extension.
   This holds with plurals and in intensional contexts.
6. **Ruled out.** Selectional restrictions, the "heavy book" argument,
   subsectivity, the "competent" problem and decidability of type
   checking each turn out to be owed to something other than nouns
   being types.
7. **Two published claims.** The injectivity axiom of Chatzikyriakidis
   & Luo (2015) is exactly the equivalence condition. No equivalence
   relation (setoid) yields the copredication counting proposed by
   Chatzikyriakidis & Luo (2018) in libraries they accept.
8. **FraCaS.** Over the problems an end-to-end pipeline reaches,
   nouns as types change no answer, cost proof automation, and save
   stipulations. The saving is owed to dependent types, not to nouns
   being types.

---

## 1. Introduction

### 1.1 The question

In Montague semantics a common noun is a predicate: "every man walks"
is ∀x (man(x) → walk(x)), with x ranging over one domain of
individuals. In the type-theoretical semantics of Ranta (1994) and Luo
(2010, 2012), developed by Chatzikyriakidis & Luo (2017, 2018, 2020), a
common noun is a type: "every man walks" is ∀x : Man. walk(x), with x
ranging over the type Man.

The two views are usually compared by example. Luo (2012) and
Chatzikyriakidis & Luo (2017) argue for nouns as types on four grounds:

- **Identity criteria.** A noun says how its things are counted: one
  person on three flights is three passengers. Types are said to be the
  natural home for this.
- **Selectional restrictions.** "The television ate the cake" is a type
  error rather than a falsehood.
- **Subsectivity.** "A leading businessman is a businessman" holds by
  typing.
- **Anaphora.** Dependent types (Σ-types) express it directly.

Gotham (2017) and Asher (2011) give predicate accounts of identity
criteria and copredication. FraCoq (Bernardy & Chatzikyriakidis 2017),
written by authors who also develop nouns as types, states nouns as
predicates and leaves the comparison open: "Working on the common
nouns as Types approach is left for future work, and we hope that
results will shed light on the theoretical advantages of the two
approaches" (n. 2).

This paper replaces comparison by example with theorems. For a fragment
of English, we prove when the two encodings validate the same
entailments, what a noun contributes to the truth of sentences at all,
and where each argued advantage of types really comes from.

### 1.2 Summary of results

| question | answer | where |
|---|---|---|
| Do types and predicates validate the same entailments? | Yes, iff the embeddings are injective | §4, `valid_iff`, `not_valid_without_injectivity` |
| ...if typed counting counts individuals? | Yes, unconditionally | §5, `validI_iff` |
| ...with identity criteria? | Iff each criterion is individual identity; two failure modes | §6, `CModel.agree_iff_kernel` |
| ...with two-place verbs and nested quantifiers? | The same three results | §7, `validR_iff`, `validRI_iff`, `agreeR_iff_kernel` |
| Are criteria a reason for types? | No: word-by-word translation into predicates with criteria | §8, `validC_iff`, `validM_iff`, `validV_iff` |
| Does this depend on classical model theory? | No: derivability, with no axioms | §9, `provT_iff` |
| What does a noun mean, for inference? | Its multiset of counting units | §11, `obsEq_iff`, and the plural and intensional versions |
| Is copredication one criterion in disguise? | No | §12, `not_single` |
| Can a setoid do copredicated counting? | Not in libraries C&L (2018) accept | §13, `exists_setoid_iff`, `no_setoid` |
| Do selectional restrictions need types? | No: sorts suffice | §10, `wt_iff_of_sameFit`, `wt_sorts_iff` |
| Does using both types and predicates make type checking undecidable? | Not in this encoding | §10, `check_iff` |
| Do types decide FraCaS 215 ("competent")? | No: extensionality does | §14, `fracas215_*` |
| Does anything change on FraCaS? | No answer; automation cost; fewer stipulations, owed to dependent types | §15 |

### 1.3 What is and is not claimed

**Claimed.** The theorems, for the fragment defined in §3 and its
extensions. Every one is a Lean theorem. The main ones carry
machine-checked records of the axioms they use (`#guard_msgs` on
`#print axioms`): `propext`, `Classical.choice` and `Quot.sound` for the
model-theoretic results, and none at all for the proof-theoretic
equivalence (§9).

**Not claimed.**

- That the fragment is English. Mass nouns, measure phrases, generics,
  tense, intensional verbs ("seek"), and noun-dependent intensional
  adjectives ("alleged") are outside it. These are discussed where
  relevant.
- That the encodings are equally convenient. They are not; nouns as
  types cost generic proof automation (§15).
- That identity criteria are unimportant. Chatzikyriakidis & Luo (2018)
  argue they are essential to counting, and our results agree. What we
  show is that they do not require types.
- Novelty for the individual examples (passengers, copies, anthologies),
  which are the literature's. What is new is the exactness: the
  conditions, their necessity, and the observational semantics.

### 1.4 How the results were checked

All proofs are in Lean 4 with Mathlib (version pinned in
`lake-manifest.json`). CI builds every file on every push; Appendix A
lists the run in which each file first passed. A theorem that builds is
proved. A reader must still check that its *statement* says what the
paper says it does. For that reason §3 gives the definitions in full,
and Appendix B lists the Lean names of every definition used.

---

## 2. Background

### 2.1 Nouns as predicates

A model has a domain A of individuals. A noun n denotes a subset
⟦n⟧ ⊆ A, and so do verbs. Determiners are relations between sets: "at
least k N are V" is |⟦N⟧ ∩ ⟦V⟧| ≥ k. This is the encoding of the FraCaS
corpus formalization in this repository and of the end-to-end pipeline
(Paper B).

### 2.2 Nouns as types

A noun n denotes a type T_n. Verbs remain predicates of individuals, so
each noun's type comes with a map into the individuals: in Luo's MTT, a
coercion, here written emb_n : T_n → A. "Every N is V" is
∀y : T_N. V(emb_N(y)). "At least k N are V" counts elements of T_N:
|{y : T_N | V(emb_N(y))}| ≥ k. "x is an N" is the proposition
∃y : T_N. emb_N(y) = x, written IsA.

### 2.3 Identity criteria

Geach's (1962) and Gupta's (1980, not read) idea, taken up by Luo
(2012), is that a count noun supplies a criterion of identity for
counting. The standard examples:

- **Passengers** (Luo 2012). "EasyJet transported 1 million passengers"
  does not entail "...1 million persons": one person on three journeys
  is three passengers.
- **Books** (Gotham 2017; Asher 2011). "John picked up three books"
  counts physical volumes; "John mastered three books" counts texts.
  Two copies of one novel are two books physically and one
  informationally. An anthology (one volume, two novels) is one book
  physically and two informationally.

Chatzikyriakidis & Luo (2018) model a noun as a *setoid*: a type with an
equivalence relation, its identity criterion, which counting respects.
The verb's domain chooses which criterion applies ((39)-(45)).

### 2.4 Copredication and double distinctness

"John picked up and mastered three books" applies a physical and an
informational predicate to one noun phrase. Gotham (2017) and
Chatzikyriakidis & Luo (2015, 2018) take it to require three books that
are pairwise distinct both physically and informationally: *double
distinctness*. Liebesman & Magidor (2017, 2019, 2026) dispute that the
sentence has this reading at all, and Sutton (2024) argues that it
depends on the context (Paper A2, §10). This paper treats double
distinctness as the proposed meaning and asks what it implies.

### 2.5 FraCaS and the pipeline

FraCaS (Cooper et al. 1996) is a suite of 346 inference problems; the
repository formalizes 342. Paper B builds an end-to-end pipeline from
FraCaS's English to Lean, in which every verdict is a machine-checked
proof. §15 uses that pipeline's parses to compare noun encodings on the
same sentences.

---

## 3. The fragment and its two semantics

### 3.1 Syntax

Fix finite sets of nouns, verbs and names.

**Predicates of individuals** (`Equivalence.Pred`):

> P ::= v | isA n | ⊤ | P ∧ P | P ∨ P | ¬P

where v is a verb and n a noun.

**Determiners** (`Det`): every, some, no, most, both, neither, at least
k, at most k, exactly k, for each natural number k.

**Formulas** (`Formula`):

> φ ::= D n C Q (D n that C are Q)
>   | more n C Q S (more n that C are Q than are S)
>   | P(c) (the named individual c is P)
>   | ¬φ | φ ∧ φ | φ ∨ φ | φ → φ

"Every N is an M" is the formula every N ⊤ (isA M), so lexical facts
relating nouns are premises like any other.

### 3.2 Nouns as predicates

A predicate model (`PModel`) has a finite domain A and interprets each
noun and verb as a predicate of A and each name as an element of A. "D
n that C are Q" is the corpus's own determiner (`Every`, `AtLeast`,
...) applied to the restrictor "n and C" and the scope Q. For example,
at least k is |{x ∈ A | n(x) ∧ C(x) ∧ Q(x)}| ≥ k. "Most" is the
corpus's: more than half. "Both" and "neither" presuppose exactly two.

### 3.3 Nouns as types

A typed model (`TModel`) has a finite domain A, and for each noun n a
finite type T_n with an embedding emb_n : T_n → A. Verbs and names are
as before. "isA n" is IsA(emb_n). The determiners range over the type:
"at least k n that C are Q" is |{y : T_n | C(emb_n y) ∧ Q(emb_n y)}| ≥
k, and so on (`EveryT`, `AtLeastT`, `MostT`, ...; `Typed.lean`).

### 3.4 Validity

An entailment from a list of premises Γ to φ is *P-valid* (`PValid`) if
every predicate model satisfying Γ satisfies φ. It is *T-valid*
(`TValid`) if every typed model with injective embeddings does, and
*T-valid without restriction* (`TValidAny`) if every typed model does.

### 3.5 Extensions used later

- **Relational fragment** (`Relational.lean`, §7): variables, two-place
  verbs, identity, and quantifiers whose restrictor and scope are
  formulas binding a variable, so quantifiers nest.
- **Identity criteria** (§6): each noun's type also has a criterion
  crit_n : T_n → K_n, and counting counts distinct values.
- **Plurals** (§11.3), **worlds and attitudes** (§11.4).

### 3.6 What the fragment leaves out

It leaves out the opaque determiners "many" and "few", anaphora across
sentences (§15.2), and adjectives that take the noun as an argument
(§14). Those are where the encodings were found to differ on FraCaS.

---

## 4. The equivalence theorem

**Theorem 4.1 (`valid_iff`).** For every list of premises Γ and formula
φ of the fragment, Γ ⇒ φ is T-valid (over typed models with injective
embeddings) iff it is P-valid.

*Proof.*

- *Types to predicates.* A typed model M is read as the predicate model
  of its images (`TModel.shadow`): the noun n becomes "is the image of
  an element of T_n". Each typed determiner, through an injective
  embedding, says what the corresponding predicate determiner says of
  the images (`det_transfer`, `more_transfer`, from `Typed.lean`'s
  lemmas `every_t`, `atLeast_t`, ..., `more_t`, via `cardT_eq`). So M
  and its shadow satisfy the same formulas (`TModel.sat_iff_shadow`).
- *Predicates to types.* A predicate model is read as the typed model
  of its subtypes (`PModel.lift`): T_n is {x ∈ A | n(x)}, embedded by
  inclusion. This lift is injective (`PModel.lift_injective`), and its
  shadow is the model itself (`PModel.lift_shadow`). ∎

**Every, some and no need nothing.** The quantifiers every, some and no
transfer through any embedding (`every_t`, `some_t`, `no_t`). Only
counting needs injectivity (`counting_needs_injectivity`, `Typed.lean`).

**Theorem 4.2 (`not_valid_without_injectivity`).** Some entailment is
P-valid but not valid over all typed models.

*The counterexample.* The premises are:

1. at least two n;
2. every n is an m;
3. every n is v;
4. at most one m is v.

The conclusion is "some n is nothing".

- With predicates the premises are inconsistent: the two n are two
  individuals that are m and v. So the entailment is valid
  (`pvalid_NI`).
- In the typed model `counterModel`, T_n has two elements, both
  embedded to one individual. All four premises hold and the conclusion
  fails. ∎

**Remark 4.3 (the 2015 axiom).** To derive "John picked up three
physical objects and mastered three informational objects" from
"John picked up and mastered three books" in Coq, Chatzikyriakidis &
Luo (2015, Appendix A) add, for Book ≤ Phy and Book ≤ Info, the axioms

> ∀x y : Book, ¬(x = y :> Book) → ¬(x = y :> Phy)

and likewise for Info. Their n. 9 notes that x ≠ y does not imply
c(x) ≠ c(y) "unless c is injective", and justifies the axiom by saying
that "for the atomic types like Book and PHY, the equality on a subtype
coincides with that of the supertype".

That axiom is the injectivity of the coercions. By Theorem 4.1 it is
exactly the condition under which their account validates what the
predicate account does. This explains Gotham's (2017, §4.3, n. 34)
objection that their 2015 system validates his argument (100), which
should be invalid (§13.1). Asserting injectivity for Phy and for Info
together says that two distinct books are never two copies of one text
and never two texts in one volume. Those are exactly the scenarios that
separate the criteria.

---

## 5. Counting individuals removes the condition

Let the typed determiners count *individuals*: two elements of T_n that
embed to the same individual count once (`countI`; the determiners
`AtLeastI`, `MostI`, `MoreI`, ...; `Counting.lean`).

**Theorem 5.1 (`validI_iff`).** With typed counting by individuals, Γ ⇒
φ is valid over *all* typed models iff it is P-valid.

*Proof.* Counting a noun's elements by their images is counting the
individuals of the noun (`countBy_emb`). So each determiner transfers
with no condition (`det_transferI`, `more_transferI`), and the typed
model and its shadow agree (`TModel.sat_iff_shadowI`). With injective
embeddings the two typed countings agree (`TModel.satI_iff_sat`), so
Theorem 4.1 is the special case. The entailment of Theorem 4.2 holds
again (`tvalidI_NI`). ∎

So the gap in Theorem 4.2 is not about types. It is about what typed
counting counts.

---

## 6. Identity criteria: the characterization

Let each noun count by an arbitrary identity criterion (`CModel`). A
noun n has a type T_n, an embedding emb_n : T_n → A and a criterion
crit_n : T_n → K_n. Two elements count as one when the criterion gives
them the same value (`countBy`, `CModel.satC`). Fix the nouns, their
types, embeddings and criteria (the *frame*), and let the verbs vary.

**Theorem 6.1 (`CModel.agree_iff_kernel`).** The typed semantics with
criteria and the predicate semantics agree on every formula of the
fragment, under every interpretation of the verbs, iff each criterion
identifies two elements exactly when they are one individual:
crit_n(y) = crit_n(y') ↔ emb_n(y) = emb_n(y').

*Proof.*

- *Sufficiency* (`CModel.satC_iff_shadow_of_kernel`). Such a criterion
  counts what counting individuals counts (`countBy_eq_of_kernel`), so
  §5 applies.
- *Necessity* (`CModel.kernel_of_agree`). A criterion can differ from
  individual identity in only two ways, and one sentence detects each.
  - **It splits an individual**: two elements with one image count
    twice. These are Luo's passengers, one person on two journeys. Let v
    be true of that individual only. Then "at most one n is v" is true
    with predicates and false by the criterion.
  - **It merges individuals**: two elements with different images
    count once. These are Gotham's books counted as texts, two copies
    of one novel. Let v be true of exactly those two individuals. Then
    "at least two n are v" is true with predicates and false by the
    criterion. ∎

Theorem 4.1's injectivity is the case crit_n = id
(`injective_iff_kernel_id`).

**Scope of the statement.** It is per frame and quantifies over all
interpretations of the verbs, so it needs one verb in the vocabulary.
It does not say which entailments separate the encodings for a given
frame with fixed verbs.

**Reading.** Separating nouns as types from nouns as predicates is the
same as a noun not counting by its individuals' identity. The two ways
that can happen, splitting and merging, are exactly the literature's
two standard examples. Paper A2 turns this into laws of counting.

---

## 7. Two-place verbs and nested quantifiers

`Relational.lean` extends the fragment with variables, two-place verbs
(rel), identity (eq), and quantifiers whose restrictor and scope are
formulas binding a variable. Both scopings of "every student read some
book" are then formulas. All three results extend:

- `validR_iff`: with injective embeddings, the same valid entailments;
- `validRI_iff`: counting individuals, with no condition;
- `agreeR_iff_kernel`: with criteria, agreement under all
  interpretations of verbs and relations iff each criterion is
  individual identity.

The old fragment embeds in the new one with the same truth values
(`Formula.toForm_eval`). The worked example is that "some book was read
by every student" entails "every student read some book", with
predicates (`pvalid_scope`) and, by `validRI_iff`, with types
(`tvalid_scope`).

*Proof idea.* Each encoding is an interpretation (`Interp`) of
quantifiers, nouns, verbs, relations and names under one evaluation
function. Interpretations that agree pointwise make every formula true
together (`Interp.Agree.eval`). A quantifier over a noun's type binds
its variable to the image of the element, so one agreement lemma per
determiner suffices.

---

## 8. Criteria are notation: the translation theorems

Theorem 6.1 shows that nouns with non-trivial criteria differ from
nouns as predicates *over the same individuals*. The predicate accounts
of criteria (Gotham 2017; Asher 2011) do not keep the same individuals.
They enrich the domain with the things counted (journeys, composite
books) and add relations of individuation. This section shows that this
enrichment is always available and loses nothing.

### 8.1 One criterion per noun

- **Source.** Nouns as types with identity criteria (`CModel`, `cI`),
  over the relational fragment.
- **Target.** Nouns as predicates with criteria (`PCModel`, `pcI`).
  There is one finite domain, with nouns, verbs and relations as
  predicates of it. A relation *same* says when two objects are one
  individual, and verbs respect it. Each noun has a criterion its
  determiners count by.
- **The translation `tr`** is word by word: every word and construction
  goes to itself, except identity ("t is u"), which goes to *same*.

**Theorem 8.1 (`validC_iff`).** An entailment is valid in the source
iff its translation is valid in the target.

*Proof.*

- A typed model becomes a predicate model (`toPC`, `toPC_eval`). Its
  domain is the individuals, plus one object for each element of each
  noun's type, each object standing for its individual.
- A predicate model becomes a typed model (`PCModel.quotC`,
  `quot_eval`). Its individuals are the *same*-classes, and its types
  are the nouns' members. ∎

So nouns as types with identity criteria are, inferentially, a
notational variant of nouns as predicates over a domain containing
what is counted, with an identity relation. What the predicate side
needs is ontology, not types. A reader who objects to that ontology
(objects for journeys, or composite books) objects to the predicate
accounts themselves, not to this construction.

The source lexicon must be finite (`Fintype Noun`) for the target
domain to be finite.

### 8.2 Several criteria per noun

Copredication counts by two criteria at once (§12, §13). Let each noun
have a nonempty family of criteria (`MCModel`, `MPCModel`;
`TranslationMulti.lean`).

**Counting (`countF`).** The P's are as many as the largest set of P's
pairwise distinct under *every* criterion. With two criteria (volume,
text), each book is an edge between its volume and its text, and the
count is the size of a largest matching.

- "At least n" is then double distinctness (`le_countF_bool_iff`). That
  is Gotham's non-compressibility by PHYS and by INFO, and
  Chatzikyriakidis & Luo's `Three` over a dot-setoid (§13).
- "At most", "exactly", "most", "both" and "neither" count by the same
  function. The literature settles only the numerals, so this is our
  extension.

**Theorem 8.2 (`validM_iff`).** With families of criteria, nouns as
types and the word-by-word translation into nouns as predicates
validate the same entailments.

The constructions are those of §8.1 (`toPCM`, `MPCModel.quotM`). Each
noun needs at least one criterion: with none, a count would count a
type's elements, which the target domain does not preserve.

### 8.3 The verb chooses the criterion

In §§8.1-8.2 "book counted physically" and "book counted
informationally" are separate noun senses, as Chatzikyriakidis & Luo's
(41)-(42) are two setoids. Their account has one lexical entry: "the
identity criterion of the object CN ... is determined by the domain of
the predicate" ((43)-(45)), and adjectives have a say too ((48)-(54)).
`VerbCriteria.lean` formalizes this.

- **The lexicon** (`AspLex`) gives each argument of each verb and
  relation an *aspect* (Phy, Info, ...): the domain of the predicate.
- **Labelling** (`labelQ`) marks each quantifier with the aspects at
  which its variable is used, in the restrictor or the scope.
  Chatzikyriakidis & Luo give no general rule ("how the identity
  criteria are decided are a little bit more complicated", p. 136).
  The rule is our reconstruction. It gives each of their examples (36),
  (37), (38), (48) and (55).
- **Models.**
  - A typed model (`VModel`) has one type per noun and one criterion
    per aspect.
  - A predicate model (`VPModel`) has one predicate per noun and one
    criterion per aspect, like Gotham's PHYS and INFO.
  - A quantifier counts by the criteria of its label's aspects
    (`countV`), or by the noun's default criterion if it has none.

**Theorem 8.3 (`validV_iff`).** With the verb choosing the criterion, an
entailment is valid with nouns as types iff its word-by-word
translation is valid with nouns as predicates.

**Gotham's (122)** (`gotham122_V`, `gotham122_VP`). "John picked up and
mastered three books ⇒ John picked up three books" is valid.
`labelQ_p122` and `labelQ_h122` show that the premise counts both ways
and the conclusion physically. With one lexical entry, both quantifiers
count the same books, and more criteria count fewer
(`VModel.countV_anti`). With two unrelated noun senses, as in §8.2, the
entailment would not hold. So the one-entry design matters for
validity, but it is available to both encodings alike.

---

## 9. The equivalence, proof-theoretically

All results so far are about validity over finite models, with
classical counting. In MTTs, entailment is derivability in an
intuitionistic type theory. `Constructive.lean` compares the encodings
on that ground.

- **Contexts, not models.** A typed context (`TCtx`) has any type of
  individuals, any type for each noun with an embedding, and any
  predicates and relations. A predicate context (`PCtx`) likewise.
  Nothing is finite or decidable. An entailment is derivable (`ProvT`,
  `ProvP`) when it holds in every context. A proof of that is a
  derivation from the context's variables.
- **Counting without decidability.** "At least k N are P" is a list of
  k elements of N's type, each P, with pairwise distinct individuals
  (`AtLeastE`). "At most" and "exactly" are built from it. "Most" and
  "more ... than" compare two counts and are not included.

**Theorem 9.1 (`provT_iff`).** For every, some, no, at least, at most
and exactly k, with one- and two-place verbs, identity, the connectives
and nested quantifiers, an entailment is derivable with nouns as types
iff it is derivable with nouns as predicates.

`#print axioms provT_iff` reports no axioms: not classical choice, not
propositional or function extensionality. A `#guard_msgs` check fails
the build if that changes. The equivalence is therefore a theorem of
the bare type theory, so it holds by MTT's own notion of entailment, not
only by classical model theory.

*Proof idea.* A typed context is shadowed by a predicate context
(`TCtx.shadow_eval`) and a predicate context lifted to a typed one
(`PCtx.lift_eval`). Bounded counting transfers through lists
(`atLeastE_iff`, `det_bridge`, `lift_list`).

---

## 10. Well-formedness: selection, sorts and type checking

### 10.1 Selectional restrictions

Chatzikyriakidis & Luo (2017: 49) count selectional restrictions as an
advantage of nouns as types: "#the television ate the cake" is a type
error. That is a claim about which sentences are well formed, not which
entailments are valid. A lexicon (`Sig`) gives each noun, verb argument
and name a type, with subtyping. `WT` is well-typedness: each verb and
relation is applied to terms whose types are subtypes of its argument
types.

- **Theorem 10.1 (`wt_iff_of_sameFit`).** Two lexicons whose nouns' and
  names' types fit the same argument positions make exactly the same
  sentences well formed. Well-formedness never sees a noun's type, only
  its *profile*: which argument types it falls under.
- **Theorem 10.2 (`wt_sorts_iff`).** For any lexicon S, the many-sorted
  lexicon `S.sorts` accepts exactly the sentences S accepts. It has one
  sort per profile, and nouns in it are predicates over their sort,
  not types. This is Retoré's (2013) option of "a small ontology" of
  sorts (Asher's position), against a type per noun (Luo's). For
  well-formedness the two coincide, given the right sorts.
- **Theorem 10.3 (`domain_irrelevance`).** In a model that respects the
  types, a well-typed formula has the same truth value whatever the
  verbs and relations do outside their argument types. So MTT's verbs,
  typed on their domains, and predicates of all individuals that
  extend them make the same well-typed sentences true. The proof needs
  conservative quantifiers. Typed quantifiers are conservative by
  construction (`tII_conservative`), and the corpus's determiners are
  too, by the equivalence (`pI_conservative`).
- **The difference is the ill-typed sentences.** In the example lexicon
  (`eSig`), "some table talks" is ill typed (`not_wt_table_talks`), and
  so it is in the sorted lexicon (`not_wt_sorts_table_talks`). With
  nouns as predicates over one domain, it is well formed and
  contingent (`table_talks_contingent`). "Some man falls" is well typed
  by subtyping (`wt_man_falls`).

So selectional restrictions separate MTT from one-domain predicates, not
from many-sorted predicates. The number of sorts needed is the number
of distinct profiles; nothing here bounds it for a real lexicon. "t is
an n" and identity are checked for scope only, as Retoré's recognising
predicates are defined on the top sort. Coercions are not modelled, so
copredication is well typed only through dot types (§13), which are
stated by hand.

### 10.2 "Heavy book"

Chatzikyriakidis & Luo (2017, pp. 47-48; extended to DTS at p. 51)
argue against nouns as predicates once sorts like Phy and Info exist.
Take book : Phy • Info → t and heavy : (Phy → t) → (Phy → t). Then
heavy(book) needs Phy ≤ Phy • Info by contravariance, "the wrong
direction".

The argument applies the adjective to the noun *predicate*. A sorted
encoding can instead apply it to the noun's *variable*: "every heavy
book" binds a variable of the noun's sort and says heavy of it, as
MTT's own Σx : Book. heavy(x) does. That needs Phy • Info ≤ Phy, the
right direction, which MTT assumes too.

- `wt_heavy_book`: in their lexicon (Book ≤ Phy • Info, Phy • Info ≤
  Phy, Phy • Info ≤ Info), "John picked up and mastered every heavy
  book" is well typed;
- `wt_sorts_heavy_book`: so it is with nouns as predicates over sorts;
- `not_phy_le_dot`, `not_sorts_phy_le_dot`: Phy ≤ Phy • Info fails in
  both lexicons, and neither needs it;
- `sorts_dot_le_phy`: the direction that is used holds.

So the argument holds against one design, adjectives typed as modifiers
of Phy-predicates. It does not hold against sorted predicates as such.

### 10.3 Type checking stays decidable

Chatzikyriakidis & Luo (2017, p. 51) object to using a noun both as a
type and as a predicate (Retoré 2013). It would need the rule (*) "x :
Man if and only if man(x) is true", which "cannot simply [be]
stipulate[d]": as a rule of the type theory, it would make typing
depend on the truth of propositions.

- **`check`, `check_iff`, `wtDecidable`.** Well-typedness in the
  fragment is decided by a program that reads only the formula, the
  context, and the lexicon's types and subtyping, and the program is
  proved to agree with `WT`. No model and no truth of any proposition
  is consulted.
- **`wtSortsDecidable`.** The same program decides well-typedness in the
  sorted lexicon, through `wt_sorts_iff`.
- **`both_shadow`, `both_lift`.** (*) holds *between models*, as a
  theorem. In a typed model's predicate reading, being an n is being in
  the image of n's type. In a predicate model's typed reading, being in
  the image of n's type is being an n. The validity theorems are proved
  from these, in the metatheory.
- **`heavy_book_checked`.** The checker accepts "John picked up and
  mastered every heavy book" by computation.

So the objection is right about (*) as a typing rule. It does not reach
this kind of "both": two encodings with decidable typing, related by
theorems about their models. We have not checked C&L's claim that (*)
as a typing rule makes type checking as hard as validity.

---

## 11. What sentences observe: full abstraction

The equivalence and translation theorems compare two encodings. Both
point to a further question: which part of a noun's interpretation do
the fragment's sentences see at all? In programming-language semantics,
a semantics is *fully abstract* when two things get the same meaning
exactly when no context tells them apart. We characterize that
indistinguishability for nouns.

### 11.1 Nouns with one criterion

A noun is interpreted by a finite type T, an embedding emb : T → A and
an identity criterion crit : T → K (`NounI`). Its **counting units** are
the criterion's values. Each unit k *covers* the individuals its
elements embed to: unit(k) = {emb(y) | crit(y) = k} (`NounI.unit`). The
noun's *units* are the function u(S) = the number of units covering
exactly S, for each set S of individuals (`NounI.units`).

Two interpretations I, I' of a noun n₀ are *indistinguishable*
(`ObsEq`) if no formula of the relational fragment tells them apart,
in any context. A context interprets the other nouns, the verbs,
relations and names, and the variables.

**Theorem 11.1 (`obsEq_iff`).** I and I' are indistinguishable iff
they have the same counting units with the same multiplicities:
u_I = u_I'. One verb in the vocabulary suffices.

**Theorem 11.2 (`obsEq_byInd_iff`).** For nouns that count individuals
(crit = emb), two interpretations are indistinguishable iff their
extensions agree.

*Proof of 11.1.*

- "Every", "some", "no" and "is an N" see only the extension, the union
  of the units.
- "Exactly j N are v", with v free to mean any set P, sees how many
  units meet P (`count_meets`): count(P) = Σ_S u(S)·[S ∩ P ≠ ∅].
- Those counts determine u (`eq_of_meets`). The units inside a set S
  are all the units less those meeting its complement. The units equal
  to S then follow by strong induction on S.
- Conversely, equal units give equal counts and equal extensions, and
  every determiner depends only on those (`detBy_obs`, `agree_of`). ∎

So, as far as the fragment's inferences go, a count noun means a
*multiset of nonempty sets of individuals*. One person on three
journeys is three passenger units covering that person. Two copies of
one novel, counted as texts, are one unit covering both copies. Nouns
as types with criteria and nouns as predicates with criteria are two
ways of writing such a multiset down, which is why Theorem 8.1 holds.
For nouns that count individuals, the multiset is the extension, one
singleton per member: Montague's predicates, recovered.

### 11.2 Nouns with several criteria

With a family of criteria (§8.2), counting is by largest sets pairwise
distinct under every criterion (`NounM`, `NounM.count`).

**Theorem 11.3 (`obsEqM_iff`).** Two such interpretations are
indistinguishable iff they give every set of individuals the same
count. The counts fix the extension too.

**Theorem 11.4 (`criteria_hidden`).** The counts do not fix what each
criterion does alone. Two things at one individual, alike by one
criterion and distinct by the other, are indistinguishable from one
thing there. Every quantifier in this fragment counts by the whole
family. With the verb choosing (§8.3), the separate criteria are
visible by construction.

**Theorem 11.5 (`not_single`).** Some copredicated noun is
indistinguishable from no noun with one criterion. Take three books:
b0 and b1 are two copies of one text, and b1 and b2 are two texts in
one volume. Counted by volume and by text at once:

- b0 and b1 together count as one (`books_01`);
- b1 and b2 together count as one (`books_12`);
- all three count as two (`books_union`);
- b1 alone counts as one (`books_inter`).

Every noun with one criterion obeys

> count(P ∪ Q) + count(P ∩ Q) ≤ count(P) + count(Q)

(`count_toM_submod`, and in A2 `count_submod`), and here 2 + 1 > 1 + 1.

`DotSetoid.lean` (§13.3) rules out an equivalence relation on the books'
own type. Theorem 11.5 is stronger: it rules out every single
criterion, over any type and embedding, judged by sentences alone. With
one criterion a noun means a multiset of units; with several it means
its counting function, which no single criterion need produce. Paper
A2 characterizes these counting functions.

### 11.3 Plurals

`PForm` adds plural variables, bound separately from individual ones,
and:

- "exactly k / at least k N together are such that φ" (`coll`);
- "the N are such that φ" (`the`);
- collective verbs of a plurality ("gathered", "lifted the piano";
  `pverb`);
- "t is one of them" (`among`), which with the singular quantifiers
  gives distributive readings.

**A plurality of N is a set of the noun's own things**, not of
individuals. A collective verb is true or false of the individuals
they embed to. The plurality counts as as many N as the criterion has
values on it (`NounI.pl`). This is the reading closest to nouns as
types. Three journeys by one person are a plurality of three
passengers, of two, or of one, all covering that one person. So plural
sentences could in principle see more than singular ones: which sets
of individuals the units can jointly cover, and with how many units.

**Theorem 11.6 (`obsEqP_iff`).** They do not. Two interpretations are
indistinguishable by the plural fragment iff they have the same
counting units, with the same multiplicities.

*Proof.* A plurality of k things covering exactly X exists iff some k
units each meet X and together cover it (`pl_iff_keys`). That is a fact
about the units as a multiset (`pl_iff_m`), so equal units give equal
pluralities. The converse needs only singular sentences. ∎

Not covered: cumulative and other polyadic plural readings beyond what
nesting `coll`, `among` and the singular quantifiers expresses; mass
nouns; several criteria in the plural fragment.

### 11.4 Intensional contexts

`IForm` adds possible worlds:

- "necessarily φ" (`nec`), over an accessibility relation;
- "t believes that φ" (`believes`), over each individual's belief
  worlds, where t may be a bound variable, so de re and de dicto
  readings come from scope;
- "t thinks that φ" (`thinks`), a hyperintensional attitude: a relation
  to the sentence itself, not to the set of worlds where it is true.

A context gives each noun an interpretation at each world (type,
embedding and criterion may all vary), verbs and relations at each
world, rigid names, and the accessibility relations. Worlds can be any
type.

- **Theorem 11.7 (`obsEqW_iff`).** Two world-indexed interpretations are
  indistinguishable by every formula, in every context, at every world,
  iff at every world they have the same counting units. A count noun
  means a function from worlds to multisets of units.
- **Theorem 11.8 (`obsEqW_byInd_iff`).** For nouns that count
  individuals, indistinguishable iff the extensions agree at every
  world: the noun means its Montague intension.
- **Theorem 11.9 (`believes_same`, `thinks_distinguishes`).**
  Possible-worlds belief cannot tell apart two nouns with the same
  interpretation at every world. The hyperintensional attitude can,
  but only by the noun *symbol*: it separates two nouns with literally
  the same interpretation. So finer distinctions come from the
  attitude, whatever nouns denote. Since the attitude does not look at
  interpretations, full abstraction is unchanged.

Not covered: intensional transitive verbs ("seek a unicorn") and
adjectives that take a noun's intension as an argument ("alleged").
These need a decision about what such an operator may see of a noun.
Also not covered: varying domains, and plurals or several criteria
together with worlds. The proof follows §11.1 world by world.

---

## 12. From observation to laws

Theorem 11.1 says that a noun with one criterion contributes a multiset
of units, so its counting function

> count(P) = Σ_S u(S)·[S meets P]

is everything sentences see. Paper A2 takes that function as the object
of study. In brief:

- The counting functions of nouns with one criterion are exactly the
  *integer coverage functions* (`representation`, `units_unique`). The
  representation is the one Chakrabarty & Huang (2012) characterize.
- Two laws stated only in terms of counts sort nouns into four kinds.
  *Additive* holds iff the noun never merges individuals
  (`additive_iff`). *Single* holds iff it never splits one
  (`single_iff`). Nouns obeying both are exactly the Montague nouns
  (`montague_iff`, `montague_obsEq`).
- Never splitting is Rothstein's (2017) and Landman's (2020)
  disjointness (`noSplit_iff_disjoint`).
- Every one-criterion noun is submodular (`count_submod`), and
  copredication can break that (Theorem 11.5). That gives an empirical
  test.
- Counting by two criteria is the least of a family of mixed
  single-criterion counts (`count2_eq_min`, by König's theorem).

Theorem 6.1, restated in A2's terms: the encodings agree over the same
individuals iff every noun obeys both laws.

---

## 13. Copredication and the setoid problem

### 13.1 Problems from the literature (`Copredication.lean`, `Counting.lean`)

FraCaS does not test the cases used to argue for nouns as types. We
state three problems, each for every number n ≥ 2:

- **I1** (Gotham 2017, §3.3.2, ex. (100), with "every book he picked up"
  for "every book"): "John picked up n books. John mastered every book
  he picked up." ⇒ "John mastered n books." Not entailed: the books may
  be n copies of one text.
- **I2** (the mirror image, from Asher's anthology case): "John mastered
  n books. John picked up every book he mastered." ⇒ "John picked up n
  books." Not entailed if one volume holds n texts.
- **C1** (control): "John picked up and mastered some book." ⇒ "John
  mastered some book."

Three encodings:

- **P**: one domain, counted by the corpus's `AtLeast`.
- **P+**: P with a stipulated function textOf and a determiner that
  counts through it.
- **M**: dot types (`MTT/DotTypes.lean`). "Picked up" is a predicate of
  a book's physical aspect and "mastered" of its informational aspect;
  each counts by its own aspect (`TwoBy`, `countBy`).

| | I1 (copies) | I2 (anthology) | C1 |
|---|---|---|---|
| P | **valid: commits to "yes"** (`P_I1_valid`) | valid (`P_I2_valid`) | valid (`P_C1_valid`) |
| P+ | open (`P2_I1_not_valid`) | - | - |
| M | open (`M_I1_not_valid`); valid if a book's text determines its volume (`M_I1_valid_of`) | open (`M_I2_not_valid`); valid if its volume determines its text (`M_I2_valid_of`) | valid (`M_C1_valid`) |

- **P answers I1 wrongly**, and the claim is valid in P. Nouns as types
  *without* identity criteria do the same: this is Gotham's point about
  Chatzikyriakidis & Luo (2015), and Theorem 5.1 explains why for the
  whole fragment. The difference is the criteria, as Chatzikyriakidis &
  Luo (2018) argue, not the types.
- **M leaves I1 and I2 open and states each one's assumption.** P assumes
  both without saying so.
- **Predicates can match M at a price.** P+ needs a stipulated identity
  function and a determiner that counts through it. That is MTT's
  identity criterion restated inside the predicate encoding, and
  Theorem 8.1 shows it is always available.
- **Copredication alone changes nothing** (C1). The encodings part only
  when copredication meets counting.

### 13.2 Four checks of published claims (`Criteria.lean`)

- **Gotham's (100) and (103), in his wording, for every n.** (100)
  ("...mastered every book ⇒ mastered n books") is invalid with dot
  types for n ≥ 2 and valid with one-domain predicates. (103)
  ("...defaced every book ⇒ defaced n books") is valid in both, since
  both verbs count physical objects.
- **Luo's passengers.** "EasyJet transported n passengers ⇒ n persons"
  is invalid with a passenger type embedded in the persons (one person
  on n journeys), and its converse is valid. With one-domain predicates
  it is valid.
- **Double distinctness is the dot-setoid's count.** "John picked up and
  mastered n books", stated as n books pairwise distinct physically and
  informationally (`AtLeastBoth`), entails "picked up n books" and
  "mastered n books": Gotham's (122)-(123). It is exactly
  Chatzikyriakidis & Luo's (2018) `Three` over their dot-setoid
  (`atLeastDot_iff`), so the two accounts agree on it.
- **The dot-setoid's relation is not transitive** (`dotSame_not_transitive`).
  Chatzikyriakidis & Luo (2018, §4.2, p. 134) define ⟨a1, b1⟩ =
  ⟨a2, b2⟩ iff a1 =_A a2 ∨ b1 =_B b2. They say (p. 135) "Our definition
  does result in an equivalence relation". Counterexample: x =
  (volume 1, *Crime and Punishment*), y = (volume 2, *Crime and
  Punishment*), z = (volume 2, *Notes from Underground*). x and y agree
  informationally, y and z physically, x and z in neither. The relation
  is transitive when each volume has one text (`dotSame_trans_of`), the
  view their n. 4 says they "incline to believe". Their `Three` uses
  only pairwise distinctness, so their *predictions* are those of
  double distinctness and survive.

### 13.3 No setoid does it (`DotSetoid.lean`)

The failure is not in the choice of relation.

**Theorem 13.1 (`exists_setoid_iff`).** For any books, volumes and
texts, the following are equivalent:

- some equivalence relation's pairwise-distinctness numerals agree with
  double distinctness, for every number and every predicate;
- "same volume or same text" is transitive on those books.

The only candidate relation is "same volume or same text" itself.

**Corollary 13.2 (`no_setoid`, `library_counts`).** Take the library of
§13.2: two copies of *Crime and Punishment*, one bound with *Notes
from Underground*. No setoid gives double distinctness there. Every
equivalence relation on those three books miscounts "picked up and
mastered two books" for some choice of what John picked up and
mastered.

Chatzikyriakidis & Luo's n. 4 adopts Asher's and Gotham's view that
physically identical books can be informationally different, so it
accepts such libraries. Under that view, their remark (p. 135) that "as
long as it is an equivalence relation, it would do" cannot be met, and
the counting in their (47) cannot come from a setoid. Gotham (2017:
338-339, (11), (14)) states the reading with two relations, PHYS and
INFO, each "transitive and symmetric", and never makes their union an
equivalence. Theorem 13.1 says the two cannot be traded for one, and
Theorem 11.5 extends this to any single criterion at all.

Bahramian, Nematollahi & Sabry (2017) model nouns in homotopy type
theory as identifications of aspect "prototypes" and also predict
double distinctness ((24c), p. 17). They use no single identity
relation on Book, so Theorem 13.1 does not bear on them, though
Theorem 11.5 does.

**These findings concern published work.** They should be checked by an
expert in MTT before the authors are contacted. A draft issue to
Chatzikyriakidis exists in the repository and has not been sent.

---

## 14. Adjectives

### 14.1 Subsectivity (FraCaS 29)

FraCaS 29: "every commissioner is a leading businessman ⇒ every
commissioner is a businessman". It is the one modified-noun problem
where nouns as types supply the needed fact and predicates need a
postulate (§15.4).

- **Theorem 14.1 (`validSub_iff`).** Counting individuals, an
  entailment is valid over typed models whose modified nouns have a
  coercion into their nouns (`Coercive`, MTT's first projection out of
  Σx : N. a(x)) iff it is valid over predicate models with the
  subsectivity postulate (`Subsective`).
- 29 is valid on both sides with the stipulation (`fracas29_P`,
  `fracas29_T`).
- It fails on both sides without it (`fracas29_not_P`,
  `fracas29_not_T`).

So types get subsectivity by choosing the Σ-type for "leading
businessman". That is the same lexical decision as the postulate that
"leading" is subsective, stated in a different place.

### 14.2 "Competent" (FraCaS 215)

FraCaS 215: "All legal authorities are law lecturers. All law lecturers
are legal authorities. ⇒ All competent legal authorities are competent
law lecturers?" The gold answer is unknown. On FraCaS (§15.1),
extensional predicates prove it, wrongly, and types do not. Four
encodings separate the two questions. An adjective is *extensional* if
coextensive nouns give coextensive modified nouns (`ExtP`, `ExtT`).

| | extensional adjectives | noun-relative adjectives |
|---|---|---|
| nouns as types | valid, wrong (`fracas215_ext_T`) | not valid, right (`fracas215_not_T`) |
| nouns as predicates | valid, wrong (`fracas215_ext_P`) | not valid, right (`fracas215_not_P`) |

With extensional adjectives, types and predicates validate the same
entailments (`validSubExt_iff`), as they do without (`validSub_iff`).
So 215's verdict tracks extensionality, not types. MTT gets it right
because its adjectives are noun-relative (competent : LegalAuthority →
Prop) and nothing forces them to be extensional. Intensional predicates
(Montague's adjectives as functions of properties) get it right for the
same reason.

---

## 15. FraCaS: the empirical comparison

§§4-14 are about a fragment. This section asks what changes on a real
benchmark. The end-to-end pipeline of Paper B parses FraCaS's English
with a restricted Grammatical Framework grammar, ranks parses, resolves
discourse, enumerates readings, and translates to Lean. We hold all of
that fixed and vary only the statement of nouns. All FraCaS figures are
development-set figures: the pipeline was built while looking at these
problems.

### 15.1 Four encodings; Section 5 (adjectives)

| | nouns | adjectives |
|---|---|---|
| **F** (the pipeline) | an opaque predicate per noun phrase (`competentLegalAuthority`) | part of the name; background knowledge adds entailments |
| **P** (extensional Montague) | N : E → Prop | intersective E → Prop; others (E → Prop) → E → Prop |
| **W** (intensional Montague) | N : W → E → Prop, premises at w₀ | intersective W → E → Prop; others (W → E → Prop) → W → E → Prop |
| **M** (MTT) | codes N : CN, carriers El N, emb N : El N → E | intersective E → Prop; others (n : CN) → El n → Prop |

All four use the same lexical classes (intersective, extensionally
subsective, privative; every other adjective subsective). Each states
what its encoding does not supply as counted postulates:

- **subsectivity**: a postulate per adjective in P and W; built in in M;
- **privativity**: a postulate in all four;
- **extensional subsectivity**: free in P (and so, wrongly, for every
  adjective); a postulate in W and M;
- **the degree lexicon**: the same postulates in all four.

Predictions were stated before the results (`EndToEnd/Encodings/README.md`):

- P answers 215 wrongly; the others answer 214 and 215 right.
- M needs no subsectivity postulates.
- Otherwise the four agree.

**Results on all 23 Section 5 problems.** "Generic prover" is `aesop`
then `grind`. "Valid" adds what is settled by hand in `Commitments.lean`.

| | generic: matched | wrong | valid: matched | wrong | postulates |
|---|---|---|---|---|---|
| F | 21/23 | 0 | 21/23 | 0 | 38 background facts |
| P | 21/23 | 0 | **20/23** | **1** (215) | 53 |
| W | 21/23 | 0 | 21/23 | 0 | 65 |
| M | 16/23 | 0 | 21/23 | 0 | **35** |

- **P commits to the wrong answer on 215, as predicted.** The prover
  does not find it, so P scores the same, but the claim is valid
  (`p_215_valid`; `extensional_forces_215` in `MTT/Intensionality.lean`).
  With nouns as extensions, "competent" cannot tell coextensive nouns
  apart. §14.2 shows the cause is extensionality.
- **W and M leave 215 open**, each with a countermodel (`m_215_not_valid`).
- **M needs the fewest postulates**: 35 against 53 (P) and 65 (W).
  Subsectivity is built into M's types; W also needs the extensionality
  of dimensional adjectives, which P gets free.
- **Not predicted: M is harder for a generic prover.** Its premises
  relate nouns through their embeddings (`eAnimal a = eMouse m`), so a
  proof needs identity reasoning that `aesop` and `grind` did not find
  on 202, 210, 211, 212 and 214. All five are valid in M, proved by
  hand. A version with modified nouns as subtypes did no better.
- All encodings miss 199 and 218, which need a default comparison class
  for "successful" and "clever".

### 15.2 Section 3 (anaphora), and the role of dependent types

The 11 Section 3 problems the pipeline reaches through possessives,
dependencies and pronouns (114-120, 131-133, 138). Both encodings follow
the pipeline's resolution decisions.

| | generic: matched | wrong | valid: matched | stipulated functions | background facts |
|---|---|---|---|---|---|
| F (predicates, simple types) | 10/11 | 0 | 10/11 | 7 | 3 |
| M (nouns as types, dependent types) | 7/11 | 0 | 10/11 | **0** | **0** |
| D (nouns as predicates, dependent types) | **9/11** | 0 | 10/11 | **0** | **0** |

- F states "her workstation" and "the cover page of R-95-103" with
  functions on every individual (workstationOf, coverPageOf : A → A). M
  states them as projections of Σ-typed proof objects: the premise
  "every report has a cover page", as (x : Report) → Σ' c : CoverPage,
  …, applied to the proof that R-95-103 is a report.
- F needs one background fact for each of 120, 131 and 132. In M the
  first is a projection and the others are subsectivity.
- Both accommodate the same presuppositions (6 each): F as side
  premises, M as Σ-hypotheses.
- All three miss 119, where she may have used someone else's
  workstation.
- 133 does not test maximality: the pipeline resolves "them" to the
  E-type description first. A projection alone would miss it
  (`projection_misses_133`).
- **D** is nouns as predicates over one type of entities, with M's
  Σ-typed premises kept, as in Dependent Type Semantics (Bekki 2014;
  Tanaka, Mineshima & Bekki 2015). "Every report has a cover page" is
  (x : E) → report x → Σ' y : E, coverPage y ∧ have x y (`Section3D.lean`).
  D also needs no stipulated function, and the generic prover finds
  more of its answers (9 against M's 7).

**So the Section 3 saving is owed to dependent types, not to nouns as
types.** Phase 1b's automation cost comes from M's embeddings, not
from the projections. Classically the claims are equivalent: a
stipulated function exists by choice whenever the Σ-premise holds. So
the difference is in what is assumed, not in what follows.

### 15.3 Every problem the pipeline reaches

All 259 reached problems, restated with each quantified noun as a type
(`gen_lifted.py`, `Lifted.lean`, `Typed.lean`). Parse, readings,
background knowledge and fused names stay F's. "Every Italian man
wants..." becomes EveryT eItalianMan (fun _ => True) wantGreatTenor.

- **Where the encoding can matter at all: 137 problems.** The other 122
  never quantify over a noun; their lifted claim is F's token for token,
  which the generator checks. That covers most of Sections 4 and 7-9.
- On the 137, with background knowledge (0 wrong answers in every row;
  every proof kernel-checked):

| | pipeline's prover | generic prover |
|---|---|---|
| F | **123** | 104 |
| M | 65 | 97 |
| M, rewritten into F's form first | 95 | - |
| M with injective embeddings, rewritten first | 95 | - |

| problems | F, generic | M, generic | F, pipeline | M, best |
|---|---|---|---|---|
| only every / some / no (63) | 60 | **60** | 60 | 60 |
| a counting determiner, "many" or "few" (74) | 44 | 37 | 63 | 37 |

1. **No accuracy edge for M, and no loss outside counting.** Every
   problem F gets and M misses involves "at least", "exactly", "most",
   "both"/"neither", "more" or "many" over a typed noun.
2. **Counting is where nouns as types make a choice.** "Two N" counts
   elements of N, which need not be two individuals. `Typed.lean`
   proves that every, some and no transfer unconditionally, that the
   counting determiners transfer with injectivity, and that without it
   they need not (`counting_needs_injectivity`). This is the FraCaS-level
   shadow of Theorem 4.1.
3. **The gap is the prover's.** Rewriting M's claims into F's form by
   the transfer lemmas recovers nothing beyond the generic prover: 95,
   with or without injectivity, against F's 123. After the rewrite the
   restrictor is a term (IsA eN), not a predicate variable, and the
   pipeline's monotonicity and counting tactics look for variables.
   This explanation is likely but has not been checked tactic by
   tactic.

The tie on every/some/no holds by construction. The genuinely different
comparison is §§15.1-15.2. Injectivity changed no FraCaS result.

### 15.4 The modified nouns of Section 1

A lexical-premise audit of all 342 hand-written problems
(`LeanNLSemantics/FraCaS/LEXICAL_AUDIT.md`, checked in CI against the
corpus) found:

- 46 added premises in 46 problems;
- 27 noun-to-noun premises that FraCaS itself states;
- 90 of the 236 yes/no theorems concluded in translation rather than by
  proof.

Eight added premises say a modified noun is a kind of the noun ("an
Irish delegate is a delegate"; problems 29, 55, 57, 59, 63, 70, 76, 80).

| | pipeline's prover | generic | valid | stipulated facts |
|---|---|---|---|---|
| F, no background knowledge | 0/8 | 0/8 | 0/8 (argued) | 0 |
| F, background knowledge | **7/8** | 2/8 | 7/8 | 8 |
| P | 2/8 | 2/8 | 7/8 | 2 (29: subsectivity, "used to") |
| W | 2/8 | 2/8 | 7/8 | 2 |
| M | 1/8 | 1/8 | 7/8 | **1** (29: "used to") |

1. **Seven of the eight premises come from fused names, not from nouns
   as predicates.** In 55, 57, 59, 63, 70, 76 and 80 the adjective is
   intersective, so any compositional encoding has the premise free. P
   and W have it as much as M. This corrects an earlier version of the
   audit, which credited all eight to nouns as types.
2. **Only 29 tells M apart** (subsective "leading"): §14.1 shows it is
   the same stipulation in a different place.
3. **M's counting needs no injectivity here.** In each counting problem
   the premise and hypothesis count the same noun's type, so `cardT_mono`
   settles them.
4. **The cost is automation**, for all three decomposed encodings.
5. 76 is missed by all: its second reading treats "few" as opaque.

Of the rest of the audit, the 27 stated noun relations become declared
coercions in M (the same knowledge, restated). The 13 adjective
premises are needed in every encoding, but M can state them per noun.
22 premises (verb phrases, verbs, time, antonyms, existence) are
untouched by the noun encoding. Of the 90 steps taken in translation,
only 4 (adjective classes and comparison classes) bear on nouns.

### 15.5 Summary of the FraCaS comparison

| | Section 5 valid | Section 3 valid | wrong (valid) | stipulations |
|---|---|---|---|---|
| F | 21/23 | 10/11 | 0 | 38 facts (S5); 7 functions, 3 facts (S3) |
| P | 20/23 | - | **1** (215) | 53 postulates (S5) |
| W | 21/23 | - | 0 | 65 postulates (S5) |
| M | 21/23 | 10/11 | 0 | **35** postulates (S5); none (S3) |

On FraCaS, nouns as types change no answer relative to intensional
Montague semantics. They have a validity edge over extensional
predicates (215), which is owed to extensionality. They need fewer
stipulations, owed to dependent types and to stating subsectivity in
the types. They cost generic proof automation. Development-set
problems, small sections.

---

## 16. The arguments for nouns as types, checked

| argument | holds against | fails against | where |
|---|---|---|---|
| identity criteria in counting (Luo 2012; passengers) | one-domain predicates counting individuals | predicates over a richer domain with criteria | Thm 6.1, 8.1 |
| copredicated counting (C&L 2015, 2018) | one-domain predicates | predicates with two criteria (Gotham); and C&L's own single setoid fails | Thm 8.2, 13.1 |
| the verb chooses the criterion (C&L 2018) | nothing | | Thm 8.3 |
| selectional restrictions (C&L 2017, p. 49) | one-domain predicates | sorted predicates | Thm 10.2 |
| "heavy book" (C&L 2017, pp. 47-48, 51) | adjectives as modifiers of Phy-predicates | sorted predicates, adjective said of the variable | §10.2 |
| "both" needs undecidable type checking (C&L 2017, p. 51) | the rule (*) as a typing rule | two encodings related by theorems about models | §10.3 |
| subsective adjectives (FraCaS 29) | predicates without a postulate | predicates with the postulate | Thm 14.1 |
| "competent" (FraCaS 215) | extensional adjectives, types or predicates alike | noun-relative adjectives, types or predicates alike | §14.2 |
| anaphora (Section 3) | predicates without dependent types | predicates with dependent types (DTS) | §15.2 |
| quantifiers and counting individuals | nothing | | Thm 5.1, 7, 9.1 |

Every argument either fails against some predicate encoding or holds
equally against the corresponding type encoding. In each case what
does the work is a piece of structure around the nouns: criteria over a
richer ontology, sorts, dependent types, noun-relative adjectives, or a
lexical choice. It is never nouns being types.

---

## 17. Related work

- **Nouns as types.** Ranta (1994); Luo (2010, 2012a, 2012b);
  Chatzikyriakidis & Luo (2017, 2018, 2020). Luo (2012) argues from
  identity criteria and passengers; C&L (2017) from selection, "heavy
  book" and decidability; C&L (2018) introduce setoids and the verb
  choosing the criterion. We give the exact conditions and the
  translations.
- **Predicate accounts with criteria.** Gotham (2017): individuation
  relations contributed by predicates, non-compressibility (Definition
  1, p. 339), PHYS not an equivalence relation, only transitive and symmetric (n. 7).
  Asher (2011, ch. 5, pp. 146-159 read): dot objects counted relative
  to one constituent type. Theorem 8.1 shows such accounts are a
  notational variant of nouns as types with criteria, given their
  ontology.
- **Montagovian Generative Lexicon.** Retoré (2013, 2014) and Mery &
  Retoré (2013): sorts and recognising predicates. Retoré leaves open
  how type judgements x : T relate to recognising predicates T̂(x)
  (§5.3). Theorems 4.1 and 8.1 answer it for this fragment, and
  §10.1's sorts theorem is his "small ontology" option. Retoré calls
  the logical forms of Asher, Luo and himself "quite similar" (§5.2);
  §10.1 makes that exact for selection. Mery, Moot & Retoré (2019) on
  individuation and counting have not been read.
- **Dependent Type Semantics.** Bekki (2014); Tanaka, Mineshima & Bekki
  (2015). §15.2's D encoding is theirs in spirit: the anaphora saving
  of MTT is owed to dependent types.
- **Copredication.** Gotham (2017, 2022 [not read]); Liebesman &
  Magidor (2017, 2019 [not read], 2023 [not read], 2025 [not read],
  2026); Sutton (2024); Bahramian, Nematollahi & Sabry (2017). The
  debate over whether double distinctness is the right meaning is taken
  up in A2. Our setoid result concerns C&L (2018) only.
- **FraCoq.** Bernardy & Chatzikyriakidis (2017) state FraCaS with
  nouns as predicates and leave the comparison open (n. 2); §15 is
  that comparison over the problems our pipeline reaches.
- **Full abstraction** is a notion from programming-language semantics
  (Milner 1977; Plotkin 1977). We use it in its plain sense: meanings
  equal iff no context tells them apart.
- **Counting.** Rothstein (2010, 2017) and Landman (2020): A2.

---

## 18. Limits

1. **A fragment, not English.** The fragment has no mass nouns, measure
   phrases, classifiers, generics, tense, intensional verbs or
   noun-dependent intensional adjectives. Its plural fragment lacks
   cumulative readings; its intensional fragment has fixed domains.
2. **Finite models.** The model-theoretic results assume finite domains;
   the proof-theoretic one (§9) does not, but covers fewer determiners.
3. **Per-frame characterization.** Theorem 6.1 quantifies over all verb
   interpretations; it does not say which entailments separate the
   encodings for fixed verbs.
4. **Our reconstruction.** The labelling rule of §8.3 and the
   determiners other than numerals under two criteria (§8.2) are our
   extensions, not the literature's.
5. **Coercion systems** (Asher 2011; Retoré 2013; Luo's coercive
   subtyping) are not compared. Copredication is stated by hand with
   dot types.
6. **FraCaS figures are development-set figures** and the relevant
   sections are small (23 and 11 problems). Phase 2's tie on
   every/some/no holds by construction. The automation explanation in
   §15.3 is likely but unchecked tactic by tactic.
7. **Definitions.** Machine-checked statements are only as good as
   their definitions. Appendix B lists them so readers can check.
8. **The undecidability claim** for (*) as a typing rule is C&L's and is
   not checked here.
9. **Not read:** Gupta (1980); Cooper (2011); most of Asher (2011);
   Gotham (2022); Liebesman & Magidor (2019, 2023, 2025); Mery, Moot &
   Retoré (2019).

---

## 19. Conclusion

For the fragment studied, nouns as types and nouns as predicates differ
in what they validate exactly when a noun does not count by its
individuals' identity. The two ways that can happen are splitting and
merging individuals. Even then the difference disappears once the
predicate side has the ontology of the things counted. Inferentially, a
count noun is a multiset of counting units, and both encodings are ways
of writing one down. Every argued advantage of types that we could
check is owed to some other structure: criteria with an ontology,
sorts, dependent types, a lexical choice about subsectivity, or
noun-relative adjectives.

The one place where the comparison leaves something new is counting
itself. If a noun's meaning, for inference, is its counting function,
then the laws that function obeys are the empirical content of theories
of individuation. That is the subject of Paper A2.

---

## 20. If A1 and A2 become one paper

A single paper would keep §§1-11 and §§13-19 of A1 and replace §12 with
A2's §§3-12, retitled "What a noun means, as far as sentences can tell:
types, predicates and the laws of counting". The overlap to cut is A2's
§2 (a restatement of §11.1 here) and A2's §7.4 (a restatement of
Theorem 11.5). The merged paper would run to roughly the length of both
drafts less those sections.

---

## References

Items marked [not read] are cited from secondary sources and must be
checked.

- Asher, N. (2011). *Lexical Meaning in Context: A Web of Words*.
  Cambridge University Press. (Ch. 5, pp. 146-159 read.)
- Bahramian, H., Nematollahi, N. & Sabry, A. (2017). Copredication in
  homotopy type theory. Manuscript (PDF dated 7 November 2017).
- Bekki, D. (2014). Representing anaphora with dependent types. LACL
  2014, LNCS 8535: 14-29.
- Bernardy, J.-P. & Chatzikyriakidis, S. (2017). A type-theoretical
  system for the FraCaS test suite: grammatical framework meets Coq.
  IWCS 2017. [Title and venue to check; the quotation of n. 2 is from
  the paper.]
- Chakrabarty, D. & Huang, Z. (2012). Testing coverage functions. ICALP
  2012 (arXiv:1205.1587); journal version: Recognizing coverage
  functions, SIAM J. Discrete Math. 29(3), 2015. [Abstract only.]
- Chatzikyriakidis, S. & Luo, Z. (2015). Individuation criteria,
  dot-types and copredication: a view from modern type theories.
  Proceedings of MoL 14: 39-50.
- Chatzikyriakidis, S. & Luo, Z. (2017). On the interpretation of
  common nouns: types versus predicates. In *Modern Perspectives in
  Type-Theoretical Semantics*, Springer SLAP 98: 43-70.
- Chatzikyriakidis, S. & Luo, Z. (2018). Identity criteria of common
  nouns and dot-types for copredication. *Oslo Studies in Language*
  10(2): 121-141.
- Chatzikyriakidis, S. & Luo, Z. (2020). *Formal Semantics in Modern
  Type Theories*. ISTE/Wiley. [not read]
- Cooper, R. (2011). Copredication, quantification and frames. LACL
  2011, LNCS 6736: 64-79. [not read]
- Cooper, R. et al. (1996). Using the framework. FraCaS deliverable D16.
- Geach, P. T. (1962). *Reference and Generality*. Cornell University
  Press. [not read; cited for the notion]
- Gotham, M. (2014). Copredication, quantification and individuation.
  PhD thesis, UCL. [not read]
- Gotham, M. (2017). Composing criteria of individuation in
  copredication. *Journal of Semantics* 34: 333-371.
- Gotham, M. (2022). Property inheritance, deferred reference and
  copredication. *Journal of Semantics* 39: 87-116. [not read]
- Gupta, A. (1980). *The Logic of Common Nouns*. Yale University Press.
  [not read]
- Landman, F. (2020). *Iceberg Semantics for Mass Nouns and Count
  Nouns*. Springer, SLAP 105.
- Liebesman, D. & Magidor, O. (2017). Copredication and property
  inheritance. [Venue to check: *Philosophical Issues* 27?]
- Liebesman, D. & Magidor, O. (2019). Copredication, counting, and
  criteria of individuation: a response to Gotham. *Journal of
  Semantics* 36(3): 549-561. [not read]
- Liebesman, D. & Magidor, O. (2026). What copredication can(not) teach
  us. *Theoretical Linguistics*, advance online,
  doi:10.1515/tl-2026-2002.
- Luo, Z. (2010). Type-theoretical semantics with coercive subtyping.
  SALT 20: 38-56. [not read]
- Luo, Z. (2012a). Common nouns as types. LACL 2012, LNCS 7351: 173-185.
- Luo, Z. (2012b). Formal semantics in modern type theories with
  coercive subtyping. *Linguistics and Philosophy* 35(6): 491-513.
  [not read]
- Mery, B., Moot, R. & Retoré, C. (2019). Solving the individuation and
  counting puzzle with λ-DRT and MGL. In *New Frontiers in Artificial
  Intelligence*. [not read]
- Mery, B. & Retoré, C. (2013). Semantic types, lexical sorts and
  classifiers. arXiv:1312.3168.
- Milner, R. (1977). Fully abstract models of typed λ-calculi.
  *Theoretical Computer Science* 4: 1-22. [cited for the notion]
- Montague, R. (1973). The proper treatment of quantification in
  ordinary English. [cited for the notion]
- Plotkin, G. (1977). LCF considered as a programming language.
  *Theoretical Computer Science* 5: 223-255. [cited for the notion]
- Ranta, A. (1994). *Type-Theoretical Grammar*. Oxford University Press.
  [cited for the notion]
- Retoré, C. (2013). A type theoretical framework for natural language
  semantics: the Montagovian generative lexicon. HAL hal-00779214v2;
  published as The Montagovian generative lexicon ΛTyn, TYPES 2013,
  LIPIcs 26 (2014).
- Rothstein, S. (2017). *Semantics for Counting and Measuring*.
  Cambridge University Press.
- Sutton, P. R. (2024). Individuation criteria and copredication:
  modification in context. *Proceedings of Sinn und Bedeutung* 28:
  876-894.
- Tanaka, R., Mineshima, K. & Bekki, D. (2015). Resolving modal
  anaphora in Dependent Type Semantics. JSAI-isAI 2014 Workshops, LNAI
  9067: 83-98.

---

## Appendix A. Theorems, files and CI runs

Each file was first built by the CI run listed. All later pushes
rebuild every file.

| result | Lean name | file | CI run |
|---|---|---|---|
| Thm 4.1 | `valid_iff` | `Equivalence.lean` | [to fill] |
| Thm 4.2 | `not_valid_without_injectivity` | `Equivalence.lean` | [to fill] |
| determiner transfer | `every_t`, `atLeast_t`, ..., `counting_needs_injectivity` | `Typed.lean` | 38176812855 |
| Thm 5.1 | `validI_iff` | `Counting.lean` | 38666051248 |
| Thm 6.1 | `CModel.agree_iff_kernel` | `Characterization.lean` | [to fill] |
| §7 | `validR_iff`, `validRI_iff`, `agreeR_iff_kernel` | `Relational.lean` | 38693145097 |
| Thm 8.1 | `validC_iff` | `Translation.lean` | 38703463185 |
| Thm 8.2 | `validM_iff` | `TranslationMulti.lean` | 38776792804 |
| Thm 8.3 | `validV_iff`, `gotham122_V` | `VerbCriteria.lean` | 38798780646 |
| Thm 9.1 | `provT_iff` | `Constructive.lean` | 38804770603 |
| §10.1 | `wt_iff_of_sameFit`, `wt_sorts_iff`, `domain_irrelevance` | `Selection.lean` | 38693145097 |
| §10.2, §14 | `wt_heavy_book`, `validSub_iff`, `fracas215_*` | `Modifiers.lean` | 38790801238, 38802195701 |
| §10.3 | `check_iff`, `both_shadow`, `both_lift` | `TypeCheck.lean` | 38802195701 |
| Thm 11.1, 11.2 | `obsEq_iff`, `obsEq_byInd_iff` | `FullAbstraction.lean` | 38809883869 |
| Thm 11.3-11.5 | `obsEqM_iff`, `criteria_hidden`, `not_single` | `FullAbstractionMulti.lean` | 38814363115 |
| Thm 11.6 | `obsEqP_iff` | `FullAbstractionPlural.lean` | 38818866053 |
| Thm 11.7-11.9 | `obsEqW_iff`, `obsEqW_byInd_iff`, `thinks_distinguishes` | `FullAbstractionIntensional.lean` | 38827684833 |
| §13.1 | `P_I1_valid`, `M_I1_not_valid`, ... | `Copredication.lean`, `Counting.lean` | 38659837431, 38666051248 |
| §13.2 | `dotSame_not_transitive`, `atLeastDot_iff` | `Criteria.lean` | 38671403438 |
| Thm 13.1 | `exists_setoid_iff`, `no_setoid` | `DotSetoid.lean` | 38697690966 |
| §15.1 | `p_215_valid`, `m_215_not_valid` | `Commitments.lean` | 38113017348 |
| §15.2 | Section 3 and D | `Section3*.lean` | 38120599283, 38683409778 |
| §15.3 | lifted claims | `Lifted.lean` | 38176812855; kernel check 38523449354 |
| §15.4 | modified nouns | `Modified*.lean`, `Pullback.lean` | 38622015149, 38625945101 |

[To do before submission: fill the "[to fill]" rows. The runs on the
commits that added `Equivalence.lean` (38539046834) and
`Characterization.lean` (38688353931) failed, so the first passing
run for each must be found in the repository's Actions history. Both
files build in every later run listed here.]

## Appendix B. Definitions to check

The statements above depend on these definitions; a reviewer should read
them in the Lean source.

- `Equivalence`: `Pred`, `Det`, `Formula`, `PModel`, `TModel`,
  `PModel.sat`, `TModel.sat`, `PValid`, `TValid`, `TValidAny`.
- `Typed`: `EveryT`, `AtLeastT`, `MostT`, `IsA`, `cardT`.
- `Counting`: `countBy`, `countI`, `TModel.satI`.
- `Characterization`: `CModel`, `CModel.satC`.
- `Relational`: `Form`, `Interp`, `Form.eval`.
- `Translation`, `TranslationMulti`: `PCModel`, `tr`, `countF`, `MCModel`.
- `VerbCriteria`: `AspLex`, `labelQ`, `countV`, `VModel`, `VPModel`.
- `Constructive`: `TCtx`, `PCtx`, `AtLeastE`, `ProvT`, `ProvP`.
- `Selection`, `TypeCheck`: `Sig`, `WT`, `Sig.sorts`, `check`.
- `FullAbstraction*`: `NounI`, `NounI.unit`, `NounI.units`, `ObsEq`,
  `NounM`, `ObsEqM`, `PForm`, `NounI.pl`, `IForm`.
- `Criteria`, `DotSetoid`: `DotSame`, `AtLeastBoth`, `Same`, `AtLeastBy`.
