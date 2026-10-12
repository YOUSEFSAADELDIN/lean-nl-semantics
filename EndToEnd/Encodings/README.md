# Noun encodings compared: does nouns-as-types buy anything?

The end-to-end pipeline states every claim with nouns as predicates over
one domain, under opaque fused names (`competentLegalAuthority`). This
directory asks whether stating the *same* parsed sentences with nouns as
types (MTT) changes what follows. Everything before the semantic target is
held fixed: the parser, the ranker, discourse resolution, the readings,
the lexical classes, and the prover.

FraCoq, whose authors also develop nouns as types, states nouns as
predicates and leaves the comparison open: "Working on the common nouns
as Types approach is left for future work, and we hope that results will
shed light on the theoretical advantages of the two approaches"
(Bernardy & Chatzikyriakidis, IWCS 2017, n. 2). The reason they give is
that testing whether an object belongs to a noun "as a proposition" is
tricky to encode compositionally with nouns as types; here that is
`IsA` (the propositional form of a judgement, `MTT/Judgments.lean`).

## The encodings

Each is produced from the pipeline's resolved trees by its own renderer:

| | nouns | adjectives | prior work |
|---|---|---|---|
| **F** fused (the pipeline today) | opaque predicate per noun phrase (`competentLegalAuthority : A → Prop`) | part of the name; `background.py` adds the entailments | this repo |
| **P** extensional Montague | `N : E → Prop` | intersective `E → Prop`; others predicate modifiers `(E → Prop) → E → Prop` | Montague; linglib |
| **W** intensional Montague | `N : W → E → Prop`, premises at `w₀` | intersective `W → E → Prop`; others `(W → E → Prop) → W → E → Prop` | Montague (PTQ) |
| **M** MTT | codes `N : CN` with carriers `El N` and `emb N : El N → E` | intersective `E → Prop`; others indexed by the noun, `(n : CN) → El n → Prop` | Luo; Chatzikyriakidis & Luo |

All four use the same lexical classes (`background.py`'s `INTERSECTIVE`,
`EXTENSIONAL_SUBSECTIVE`, `PRIVATIVE`; every other adjective subsective),
and each states the facts its encoding does not supply as explicit,
counted postulates:

- **subsectivity** ("a competent N is an N"): a postulate in P and W, one
  per adjective; *built in* in M (an element of `El N` is an N).
- **privativity** ("a former N is not an N"): a postulate in all four.
- **extensional subsectivity** ("fat" depends only on the noun's members,
  FraCoq's `ExtensionalSubsectiveA`): free in P (and so, wrongly, for
  every adjective); a postulate in W and M.
- the **degree lexicon** (contraries, comparatives): the same postulates
  in all four.

## What is measured

1. Matched and wrong answers per section, with one generic prover for all
   encodings (the pipeline's specialised tactics are built for F's shape;
   F is also reported with them, separately).
2. **Commitments**: whether an encoding makes a wrong answer *valid*, not
   just whether the prover finds it. `MTT/Intensionality.lean` proves P
   forces FraCaS 215 to "yes" (`extensional_forces_215`); the comparison
   checks that against the generated claims.
3. **Postulates**: how many stipulated facts each encoding needs for the
   answers it gets.
4. **What each can state at all** (Phase 1b): dependent anaphora as
   Σ-types (`MTT/DependentAnaphora.lean`) against F's stipulated
   functions.

## Predictions, stated before the results

- Section 5: P answers 215 wrongly (it is valid in P); F, W and M get
  214 and 215 right. M needs no subsectivity postulates; W and P need one
  per subsective adjective. Otherwise the four agree.
- Section 3: F, P and W need a stipulated function per possessive or
  dependency ("her workstation"); M states the same problems with Σ-types
  and no stipulation. Classically the claims are equivalent, so accuracy
  should not differ; what differs is what is assumed. M misses 133
  (maximality), which F gets through its E-type description.
- Overall: no accuracy edge for M over W, a validity edge over P, and
  fewer postulates than either.

## Phase 1a results: Section 5 (CI run 38113017348)

All 23 problems, from the pipeline's own parses. "Matched" is with one
generic prover (`aesop`, then `grind`). "Valid" adds what
`Commitments.lean` settles by hand: a claim proved valid, or refuted by a
countermodel.

| | generic prover: matched | wrong | valid answers: matched | wrong | postulates |
|---|---|---|---|---|---|
| F (pipeline, background knowledge) | 21/23 | 0 | 21/23 | 0 | 38 background facts |
| P (extensional Montague) | 21/23 | 0 | **20/23** | **1** (215: "yes" is valid) | 53 |
| W (intensional Montague) | 21/23 | 0 | 21/23 | 0 | 65 |
| M (MTT) | 16/23 | 0 | 21/23 | 0 | **35** |

Every encoding misses 199 and 218 (gold yes). They need a default
comparison class for "successful" and "clever", which the shared lexicon
deliberately lacks.

What the predictions got right, and what they missed:
- **P commits to the wrong answer on 215, as predicted.** The prover does
  not find it, so P scores the same as the others. Its claim is valid,
  though (`p_215_valid`): with nouns as extensions, "competent" cannot
  tell coextensive nouns apart. A stronger prover would make P answer
  215 wrongly.
- **W and M leave 215 open, as predicted**, each with a countermodel.
- **M needs the fewest postulates**: 35, against 53 for P and 65 for W.
  Subsectivity ("a competent N is an N") is built into M's types, and is
  a postulate per adjective in P and W. W also needs the extensionality
  of dimensional adjectives as a postulate, which P gets as a theorem
  (for every adjective, which is the problem).
- **Not predicted: M is harder for a generic prover.** Its premises
  relate nouns only through their embeddings into individuals
  (`eAnimal a = eMouse m`), so a proof needs identity reasoning that
  `aesop` and `grind` did not find on five problems (202, 210, 211, 212,
  214). All five are valid in M (proved in `Commitments.lean`). This is
  a real cost of the encoding, but to automation, not to what it
  entails. A first version stated M's modified nouns as subtypes and
  did no better (CI run 38109159944); currying them changed nothing.

So on Section 5: no accuracy edge for M over intensional Montague; an
edge in validity over extensional Montague (215); the fewest postulates;
and a cost in proof automation. These are development-set problems,
and Section 5 is small.

## Phase 1b results: Section 3 (CI run 38120599283)

The 11 Section 3 problems the pipeline reaches through possessives,
dependencies and pronouns (114-120, 131-133, 138). Both encodings follow
the pipeline's own resolution decisions; they differ only in how a
dependency is stated.

| | generic prover: matched | wrong | valid answers: matched | stipulated functions | background facts | accommodated presuppositions |
|---|---|---|---|---|---|---|
| F (pipeline) | 10/11 | 0 | 10/11 | 7 | 3 | 6 (side premises) |
| M (dependent types) | 7/11 | 0 | 10/11 | **0** | **0** | 6 (Σ-hypotheses) |

Both miss 119 ("No student used her workstation" ⇒ not "Mary used a
workstation", gold no): she may have used someone else's.

- **No stipulated functions.** F states "her workstation" and "the cover
  page of R-95-103" with functions on every individual (`workstationOf,
  coverPageOf : A → A`). M states them as projections of Σ-typed proof
  objects: the premise "every report has a cover page" itself, as
  `(x : Report) → Σ' c : CoverPage, …`, applied to the proof that
  R-95-103 is a report.
- **No background facts.** F needs one for each of 120, 131 and 132
  ("chaired the meeting Smith attended" ⊑ "chaired a meeting", "rents a
  dedicated line" ⊑ "rents a line"). In M the first is a projection
  (`ev.1` is a meeting) and the second is subsectivity, built into the
  types.
- **The same presuppositions.** Where the context has no antecedent
  ("Mary used her workstation", with nothing about Mary before it),
  both accommodate the presupposition that she has one. F does it as a
  side premise about a stipulated function; M as a Σ-hypothesis
  restricted to the possessor.
- **The same accuracy, and the same automation cost as in Section 5.**
  The generic prover misses three M claims (118, 131, 132) that are
  valid (`Commitments.lean`): they need a proof object in the context
  projected, or a conjunction taken apart under one.
- **133 is not a test of maximality here.** The pipeline resolves "them"
  to the E-type description "all the computers GFI owns" before either
  encoding sees it, so both get 133. A projection alone would not
  (`MTT/DependentAnaphora.lean`'s `projection_misses_133`).

So on Section 3, as predicted: equal accuracy, and M states the same
problems without the stipulated functions and background facts F
needs. Classically the two are equivalent (a stipulated function exists
by choice whenever the Σ-premise holds), so this is a difference in what
is assumed, not in what follows.

## Findings so far (Phases 1a and 1b)

Across the 34 problems of Sections 5 and 3 the pipeline reaches, with the
parser, readings and lexicon held fixed:

| | Section 5: valid answers matched | Section 3: valid answers matched | wrong (valid) | stipulations |
|---|---|---|---|---|
| F (pipeline) | 21/23 | 10/11 | 0 | 38 background facts (S5); 7 functions and 3 background facts (S3) |
| P (extensional Montague) | 20/23 | - | **1** (215) | 53 postulates (S5) |
| W (intensional Montague) | 21/23 | - | 0 | 65 postulates (S5) |
| M (MTT) | 21/23 | 10/11 | 0 | **35** postulates (S5); **none** (S3) |

1. **No accuracy edge for M.** It matches intensional Montague semantics
   and the pipeline on every problem.
2. **A validity edge over extensional Montague.** Stating nouns as
   extensions makes the wrong answer to 215 valid (`p_215_valid`); M,
   like W, leaves it open (`m_215_not_valid`).
3. **The fewest stipulations.** In Section 5, subsectivity is built into
   M's types (35 postulates against 53 and 65). In Section 3, M states
   possessives and dependencies as projections of the premises' own
   proof objects, where F stipulates a function per possessive and
   background facts linking fused names.
4. **A cost in proof automation.** One generic prover finds 16/23 (S5)
   and 7/11 (S3) of M's answers against 21/23 and 10/11 of F's. Every
   miss is valid and proved by hand in `Commitments.lean`: M's premises
   relate nouns through their embeddings into individuals and through
   projections, which `aesop` and `grind` do not search well.

These are development-set problems, and both sections are small. The
differences in (3) are differences in what is assumed, not in what
follows: classically, a stipulated function exists by choice wherever
the Σ-premise holds.

## Phase 2 results: every problem the pipeline reaches (CI run 38176812855)

Phase 2 restates the pipeline's own claims, all 259 problems, with each
quantified noun as a type (`gen_lifted.py`, `Lifted.lean`, `Typed.lean`).
Nothing else changes: parse, readings, background knowledge and fused
names are F's. "Every Italian man wants..." becomes `EveryT eItalianMan
(fun _ => True) wantGreatTenor`, a quantifier over the type `ItalianMan`.
Verbs and adjectives stay predicates of individuals. Elsewhere, "x is an N"
is `IsA eN x`, meaning x is the individual of some element of `N`.

**Where the encoding can matter at all: 137 of the 259 problems.** The
other 122 never quantify over a noun. They only talk about named
individuals through fused names (`haveGenuineDiamond smith`), so their
lifted claim is F's, token for token (the generator checks). That covers
most of Sections 4 and 7-9: at the granularity the pipeline translates
to, there is no noun there to make a type of.

On the 137 (with background knowledge; 0 wrong answers in every row).
The first run (38125879289) also had 119, since refused by the
pipeline's name check; it was unmatched in every row, and no other
verdict changed:

| | pipeline's prover | generic prover (`aesop`, `grind`) |
|---|---|---|
| F (pipeline) | **125** | 104 |
| M (nouns as types) | 65 | 97 |
| M, rewritten into F's form first (`*_transfer`) | 95 | - |
| MInj (injective embeddings), rewritten first | 95 | - |

| problems | F, generic | M, generic | F, pipeline's prover | M, best |
|---|---|---|---|---|
| only every / some / no (63) | 60 | **60** | 60 | 60 |
| a counting determiner, `Many` or `Few` (74) | 44 | 37 | 65 | 37 |

1. **No accuracy edge for M, and no loss outside counting.** On the 63
   problems quantified only by every, some and no, M and F match the same
   60 problems under the generic prover. Every problem F gets and M
   misses has "at least", "exactly", "most", "both"/"neither", "more" or
   "many" over a typed noun.
2. **Counting is where nouns as types make a choice.** With nouns as
   types, "two Ns" counts elements of the type `N`. Two elements may
   be one individual, so this need not be two individuals: MTT's
   individuation question. `Typed.lean` proves:
   - every, some and no transfer to F's quantifiers unconditionally
     (`every_t`, `some_t`, `no_t`);
   - the counting determiners transfer when the embedding is injective
     (`atLeast_t`, ..., `more_t`, from `cardT_eq`);
   - without injectivity they need not (`counting_needs_injectivity`, a
     countermodel). Injectivity is sufficient, not shown necessary.

   So M with injective embeddings (MInj) states each problem as F does,
   with "n" read as `IsA eN`. Each predicate is `IsA` of its subtype's
   inclusion, so the two have the same valid claims. The exceptions are
   the opaque `Many` and `Few`, stated at every type in M. That last
   step is an argument from the per-determiner lemmas; it is not
   mechanized claim by claim. F counts individuals without saying so;
   M has to state it, one postulate per counted noun.
3. **The gap is the prover's.** The pipeline's prover is built for F's
   syntax. Rewriting M's claims into F's quantifiers by the transfer
   lemmas recovers nothing beyond what the generic prover finds: 95
   with injectivity or without, against F's 125. The likely reason is
   that after the rewrite the restrictor is a term (`IsA eN`), not a
   predicate variable, and the pipeline's monotonicity and counting
   tactics look for variables. That has not been checked tactic by
   tactic. The generic prover, which
   neither encoding was tuned for, puts them closer: 104 against 97, the
   7-problem difference being counting problems.

So on the rest of FraCaS, as predicted, a tie on what follows. There is
no accuracy edge, and with injective embeddings no logical difference.
The one substantive difference is that nouns as types make the
individuation of counted nouns an explicit assumption. As in Phases
1a/1b, there is a real cost in automation that was built for predicates.

What this phase does not show:
- **The tie on every, some and no holds by construction.** M is F with
  each quantified noun lifted to a type, and the transfer lemmas prove
  the lift preserves those quantifiers; the experiment measures only
  how well each form is proved. The comparison of genuinely different
  noun encodings is Phase 1 (34 problems).
- **Injectivity changed no result on FraCaS**: 95 with it or without.
  The individuation point itself is not new: Chatzikyriakidis & Luo
  (2018) argue that common nouns need identity criteria precisely for
  counting. This phase mechanizes it; it does not discover it.
- **M here keeps F's fused names**: "Italian man" is one type, not an
  adjective applied to a noun, so MTT's treatment of modification is
  not tested (Phase 1a tests it on Section 5).

## Phases

- **1a**: Section 5 (adjectives), all four encodings.
- **1b**: Section 3 (anaphora): F against M.
- **2**: every problem the pipeline reaches, its own claims with nouns as types.

These are development-set problems, as everywhere in this project.
