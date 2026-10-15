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
verdict changed. With every proof kernel-checked (CI run 38523449354), F
with the pipeline's prover matches 123, not 125: the proofs of 9 and 11
came from `exist_nl` and are rejected by the kernel (`EndToEnd/README.md`,
"The kernel check"). No other row changes:

| | pipeline's prover | generic prover (`aesop`, `grind`) |
|---|---|---|
| F (pipeline) | **123** | 104 |
| M (nouns as types) | 65 | 97 |
| M, rewritten into F's form first (`*_transfer`) | 95 | - |
| MInj (injective embeddings), rewritten first | 95 | - |

| problems | F, generic | M, generic | F, pipeline's prover | M, best |
|---|---|---|---|---|
| only every / some / no (63) | 60 | **60** | 60 | 60 |
| a counting determiner, `Many` or `Few` (74) | 44 | 37 | 63 | 37 |

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
   the opaque `Many` and `Few`, stated at every type in M. That step is
   now a theorem over a fragment (`Equivalence.lean`, below), not a
   check of each claim. F counts individuals without saying so; M has
   to state it, one postulate per counted noun.
3. **The gap is the prover's.** The pipeline's prover is built for F's
   syntax. Rewriting M's claims into F's quantifiers by the transfer
   lemmas recovers nothing beyond what the generic prover finds: 95
   with injectivity or without, against F's 123. The likely reason is
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

## The equivalence theorem (`Equivalence.lean`)

Phase 2's argument that M with injective embeddings and F validate the
same claims went determiner by determiner. `Equivalence.lean` proves it
for whole entailments, over a fragment closed under the connectives:

- predicates of individuals: verbs, "is an N", `⊤`, and their `∧`, `∨`
  and `¬`;
- formulas: every, some, no, most, both, neither, at least k, at most k
  and exactly k over a noun, with a restrictor and a scope; "more N
  that R are Q than are S"; a predicate of a named individual; and
  `¬`, `∧`, `∨`, `→`.

"Every N is an M" is a formula of the fragment, so lexical facts about
nouns are premises like any other.

Each formula has two meanings. In a predicate model (`PModel`), a noun is
a predicate of a finite domain and each determiner is the corpus's own
(`Every`, `AtLeast`, ...). In a typed model (`TModel`), a noun is a finite
type with an embedding into the domain. There each determiner is the
typed one (`EveryT`, `AtLeastT`, ...) and "is an N" is `IsA`.

- **`valid_iff`**: an entailment from a list of premises is valid over
  all typed models with injective embeddings exactly when it is valid
  over all predicate models. A typed model is read as the predicate
  model of its images (`TModel.shadow`), and the two satisfy the same
  formulas (`TModel.sat_iff_shadow`, by `det_transfer` and
  `more_transfer`). A predicate model is read as the typed model of its
  subtypes (`PModel.lift`), whose shadow is the model itself
  (`PModel.lift_shadow`). That reading of a predicate as a type is the
  linglib bridge's `CN'` (`bridge/LinglibBridge.lean`), whose
  `CN'.intersective_widen` is also the general form of Phase 3's result
  on intersective adjectives.
- **`not_valid_without_injectivity`**: dropping injectivity breaks the
  equivalence, when the typed models count elements of a noun's type.
  Counting individuals instead removes the condition altogether
  (`validI_iff`, Phase 4). Injectivity is the axiom Chatzikyriakidis &
  Luo (2015, n. 9 and Appendix A) add to their Coq development to count
  books as physical and as informational objects. By `valid_iff`, it is
  exactly the condition under which their account validates what the
  predicate account does (`paper/A-literature.md`). The premises are "at least two n", "every n is an m",
  "every n is v" and "at most one m is v". With predicates they are
  inconsistent, so they entail "some n is nothing" (`pvalid_NI`). A
  typed model whose two elements of `n` are one individual satisfies
  them and not the conclusion.

What it does not cover:

- It is about the fragment, not the corpus or the pipeline's claims. No
  claim is translated into `Formula`, so it does not certify any Phase 2
  verdict. It says what Phase 2's MInj row should find: the same valid
  claims as F, where the claims fall in the fragment.
- It leaves out `Many` and `Few` (opaque, and stated at every type in
  M), anaphora (Phase 1b), and adjectives that take the noun as an
  argument (Phase 1a). Those are where the encodings were found to
  differ, and none is in the fragment.
- Verbs are one-place predicates of individuals, and individuals are
  named directly. Relations and quantified objects are not in it.
- Injectivity is shown sufficient, and its absence is shown to break
  the equivalence on one entailment. Weaker conditions that would also
  suffice are not explored.

## Phase 3 results: the modified nouns of Section 1 (CI run 38622015149)

The lexical-premise audit found 8 problems whose hand-written proof needs
an added premise that a modified noun is a kind of the noun: 29, 55, 57,
59, 63, 70, 76 and 80 ("an Irish delegate is a delegate"). The pipeline
reaches all 8 and supplies the same fact as background knowledge,
because it states "Irish delegate" as one fused name, `irishDelegate`.
Phase 3 asks which encodings supply the fact themselves.

`gen_modified.py` starts from F's own claims without background
knowledge, so the parse, the readings, the determiners and the verb
phrases are F's. It restates only the fused names that the pipeline's
trees build from an adjective and a noun (and, in 29, from "used to be"
and such a noun). It uses the adjective classes of `background.py`, as
Phase 1a does:

- **P**: "Irish delegate" is `fun x => delegate x ∧ irish x`. "Leading
  businessman" is `leading businessman`, with subsectivity a postulate.
- **W**: as P, with the decomposed nouns and adjectives as intensions at
  `w₀`; "leading" takes the noun's intension.
- **M**: P's claim lifted as in Phase 2, so "some Irish delegate" is
  `SomeT eDelegate (fun x => irish x) …`. "Leading" is indexed by the
  type `Businessman`, as in Phase 1a, so subsectivity is built in.

"Used to" is an opaque operator in all three, with one counted postulate:
it is upward monotone.

| | pipeline's prover | generic prover | valid answers | stipulated facts |
|---|---|---|---|---|
| F, no background knowledge | 0/8 | 0/8 | 0/8 (argued) | 0 |
| F, background knowledge | **7/8** | 2/8 | 7/8 | 8 background facts |
| P (extensional Montague) | 2/8 | 2/8 | 7/8 | 2 (29: subsectivity, "used to") |
| W (intensional Montague) | 2/8 | 2/8 | 7/8 | 2 (29: subsectivity, "used to") |
| M (MTT) | 1/8 (after `Pullback.lean`) | 1/8 | 7/8 | **1** (29: "used to") |

No row gives a wrong answer. "Valid answers" adds the claims proved by
hand in `ModifiedCommitments.lean` (built in CI run 38625945101). F
without background knowledge is not valid on any of the 8, since nothing
relates its fused names (`irishDelegate`, `delegate`). That is argued,
not shown by countermodels. None of the encodings gets 76:
its second reading treats "few" as the opaque `Few`, whose one postulate
lets the scope shrink but not the restrictor. F with background knowledge
misses it for the same reason.

1. **7 of the 8 premises come from fused names, not from nouns as
   predicates.** In 55, 57, 59, 63, 70, 76 and 80 the adjective is
   intersective (Irish, Portuguese, Scandinavian, female). Any encoding
   that builds "Irish delegate" from "Irish" and "delegate" has "an
   Irish delegate is a delegate" for free, P and W as much as M. Only F
   needs it stated, because `irishDelegate` and `delegate` are
   unrelated names. This corrects the audit, which credited all 8 to
   nouns as types.
2. **Only 29 tells M apart.** "Leading" is subsective. P and W need a
   postulate that a leading businessman is a businessman; M has it in
   the types. That is Phase 1a's subsectivity result again, on one
   Section 1 problem.
3. **M's counting needs no injectivity here.** In each counting problem
   the premise and the hypothesis count the same noun's type ("at least
   three female commissioners", "at least three commissioners"), so
   `cardT_mono` settles them with no condition on the embedding. The
   individuation question of Phase 2 arises only when two different
   nouns are counted against each other.
4. **The cost is automation, for all three decomposed encodings.** The
   pipeline's prover gets 7 of F's claims with background knowledge but
   only 2 of P's and W's and 1 of M's, the same claims stated
   compositionally. Every miss is a counting claim or M's 29, and all are
   valid. The prover's monotonicity tactics expect a plain predicate as
   the restrictor, and here the restrictor is `fun x => delegate x ∧
   irish x`, or a typed count. The pipeline's prover is built for F's
   fused names. Reading M's counts on the noun's own type
   (`Pullback.lean`) did not help.

What this phase does not show:
- 8 problems is a small set, and all are development problems.
- The verb phrases stay fused, as F has them: "won the contract from
  APCOM" is still one name. So the audit's 3 object-noun premises (17,
  24, 328) are not tested.

## Phase 4 results: individuation and copredication (`Copredication.lean`, CI run 38659837431)

FraCaS does not test the cases Chatzikyriakidis & Luo use to argue for
nouns as types. Phase 4 states three small problems from that
literature and settles each claim in Lean in three encodings. The phase
reads the MTT core's `Individuation.lean` and `DotTypes.lean` without
changing them.

Sources. I1 is Gotham's (2017, §3.3.2, ex. 100) argument "John picked
up three books. John mastered every book. ⇒ John mastered three books",
which he judges invalid (three copies of one text), with "every book he
picked up" for "every book". Gotham (§4.3, n. 34) also shows that
Chatzikyriakidis & Luo's (2015) nouns-as-types account, which counts
elements of the type `Book`, makes that argument valid. Chatzikyriakidis
& Luo (2018) answer with common nouns as setoids: a noun comes with an
identity criterion, set by the domain of the predicate applied to it
("pick up" counts by physical sameness, "master" by informational
sameness; their (39)-(43)). M below is that account for these
sentences. The anthology case behind I2 (one volume, several texts) is
Asher's (2011), discussed by Gotham (2017, Figs. 3 and 5) and by
Chatzikyriakidis & Luo (2018, n. 4), who adopt it while saying they
incline to think a physically identical book cannot be informationally
different.

- **I1** "John picked up two books. John mastered every book he picked
  up." ⇒ "John mastered two books." Not entailed: the two books may be
  two copies of one text. This is the contrast `MTT.v` Part 7 states
  (CL20 §5.3.1): "picked up two books" counts physical objects,
  "mastered two books" counts texts.
- **I2** "John mastered two books. John picked up every book he
  mastered." ⇒ "John picked up two books." The mirror image: not
  entailed if one volume can hold two texts (an anthology).
- **C1** "John picked up and mastered some book." ⇒ "John mastered some
  book." Copredication without counting, as a control.

The encodings:
- **P**: one domain of individuals, counted by the corpus's `AtLeast`;
  "picked up" and "mastered" are predicates of the same individuals.
- **P+**: P with a stipulated function `textOf` and a determiner that
  counts through it.
- **M**: dot types, as in `DotTypes.lean`. "Picked up" is a predicate of
  a book's physical aspect, "mastered" of its informational aspect, and
  each counts by its own aspect's identity (`TwoBy`, which is `MTT.v`'s
  `countGe2` restricted to a predicate).

| | I1 (two copies, one text) | I2 (one volume, two texts) | C1 (copredication only) |
|---|---|---|---|
| P (one domain) | **valid: commits to "yes"** | valid | valid |
| P+ (stipulated `textOf`) | open | - | - |
| M (dot types) | open; valid if each text has one volume | open; valid if each volume has one text | valid |

1. **P answers I1 wrongly, and the claim is valid in P**
   (`P_I1_valid`). With one domain and one count, "picked up two books"
   and "mastered two books" count the same individuals whenever the
   same books are picked up and mastered. Nouns as types without
   identity criteria do the same (Gotham's point about Chatzikyriakidis
   & Luo 2015; `validI_iff` below shows why, for a whole fragment). The
   difference is the identity criteria, as Chatzikyriakidis & Luo
   (2018) argue, not the types.
2. **M leaves I1 and I2 open, and makes each one's assumption
   explicit.** I1's countermodel is `MTT.v`'s own two copies of one text
   (`M_I1_not_valid`, from `MTT.two_books_phy` and
   `MTT.not_two_books_info`). I2's is one volume holding two texts. I1
   becomes valid once each text has one volume, and I2 once each volume
   has one text (`M_I1_valid_of`, `M_I2_valid_of`). P assumes both
   without saying so.
3. **Predicates can match M, at a price.** P+ leaves I1 open too
   (`P2_I1_not_valid`), but it needs a stipulated identity function and
   a determiner that counts through it. That is MTT's identity
   criterion restated inside the predicate encoding, the same pattern
   as Phase 1b's stipulated functions.
4. **Copredication alone changes nothing.** C1 is valid in P and in M
   (`P_C1_valid`, `M_C1_valid`). The encodings part only when
   copredication meets counting.

This also changes how the equivalence theorem's limit should be read.
`not_valid_without_injectivity` shows the encodings part when two
elements of a noun's type are one individual. Phase 4 shows that this is
what individuation needs: two copies are two books physically and one
book informationally. Injectivity is the assumption that a noun counts
by the individuals' own identity, which P makes for every noun and every
verb.

**For every number (`Counting.lean`, CI run 38666051248).** `countBy f P`
counts the things that are `P` by the criterion "same `f`-value". With
the individuals' own identity it is the corpus's `card`, and at two it is
`TwoBy` (`countBy_of_injective`, `countBy_two_iff`). The results above
hold for every `n ≥ 2`. P makes I1 and I2 valid for every `n`
(`P_I1_valid`, `P_I2_valid`). M leaves both open for every `n ≥ 2`, with
`n` copies of one text and one volume holding `n` texts as
countermodels (`M_I1_not_valid`, `M_I2_not_valid`). I1 becomes valid
once a book's text determines its volume, and I2 once its volume
determines its text (`M_I1_valid_of`, `M_I2_valid_of`). P+ with a
stipulated function to a sort of texts leaves I1 open for every
`n ≥ 2` (`P2_I1_not_valid`).

**The equivalence without injectivity (`Counting.lean`).** The same
counting removes the equivalence theorem's condition. Let the typed
models' counting determiners count individuals: two elements of a
noun's type that are one individual count once (`countI`). Then nouns as
types and nouns as predicates validate exactly the same entailments of
the fragment, with no condition on the embeddings (`validI_iff`). The
key step is that counting a noun's elements by their individuals is
counting the individuals of that noun (`countBy_emb`). With injective
embeddings the two ways of counting agree (`TModel.satI_iff_sat`), so
`valid_iff` is the special case. The example that fails without
injectivity holds again (`tvalidI_NI`).

So what separates the encodings in counting is the identity criterion a
noun counts by, not types as such. Counting by the individuals' own
identity, nouns as types say what predicates say, in the whole fragment.
Counting by another criterion, as "mastered three books" counts texts,
they say what one-domain predicates cannot.

What this phase does not show:
- Three constructed problems. It shows the encodings can differ, and
  where. It does not measure how often this happens in text.
- Only P, P+ and M are stated. W is P here: nothing in these problems is
  intensional.
- The problems are stated by hand, not produced by the pipeline, which
  has no dot types.
- Counting under both criteria at once ("John picked up and mastered two
  books") is not stated. How that sentence counts is itself debated.

## Phases

- **1a**: Section 5 (adjectives), all four encodings.
- **1b**: Section 3 (anaphora): F against M.
- **2**: every problem the pipeline reaches, its own claims with nouns as types.
- **Equivalence theorem**: over a fragment, nouns as types with injective embeddings and nouns as predicates validate the same entailments; without injectivity they do not (`Equivalence.lean`).
- **3**: the 8 modified-noun problems the audit found, in F, P, W and M (`gen_modified.py`, `Modified.lean`, `ModifiedCommitments.lean`).
- **4**: individuation and copredication, beyond FraCaS: three constructed problems in P, P+ and M, for every number, and the equivalence theorem without injectivity (`Copredication.lean`, `Counting.lean`).
- **Lexical-premise audit** of the hand-written corpus, all 342 problems: which premises the formalization supplies, and which of them nouns-as-types would supply instead (`LeanNLSemantics/FraCaS/LEXICAL_AUDIT.md`).

These are development-set problems, as everywhere in this project.
