# A testable prediction: one criterion versus copredication

Draft protocol. Nothing here has been run. Running it needs human
participants, which is your decision. Revised in October 2026 after
reading Liebesman & Magidor (2026), Sutton (2024) and Landman (2020)
(`A-literature.md`).

## The law

Count a noun's things that have some property. For every noun with one
identity criterion, whatever encodes it, counts obey

> count(P or Q) + count(P and Q) ≤ count(P) + count(Q)

(`CountingLaws.count_submod`). "Whatever encodes it" covers a type with
a criterion, a predicate with a criterion, a setoid, a counting context
in Rothstein's sense, or a disjoint base in Landman's sense.

Counting by two criteria at once can break it
(`FullAbstractionMulti.not_single`). Gotham (2017), Chatzikyriakidis &
Luo (2015, 2018) and Bahramian, Nematollahi & Sabry (2017) propose two
criteria for "picked up and mastered three books". So the law separates
*every* one-criterion account from double distinctness at once, without
choosing among the one-criterion accounts. It is a law about the
pattern of one speaker's answers in one context, not about any single
answer.

## Three hypotheses

| | source | "picked up and mastered" counts by | law |
|---|---|---|---|
| DD (double distinctness) | Gotham 2017; C&L 2015, 2018; Bahramian et al. 2017 | both criteria (`count2`) | can fail |
| PV (Property Versatility) | Liebesman & Magidor 2017, 2026 | one criterion per context: 'book' ranges over volumes or over texts | holds |
| QUD | Sutton 2024 | both criteria in a neutral context; one criterion when a prominent QUD makes a word restrict the domain | fails only in the neutral context |

Landman (2020, §11.3) adds a fourth expectation, which can hold
alongside any of the three. Where counting does need overlapping items,
speakers manage it by "indexing", which "comes with a processing cost"
(p. 360). So answers that break the law should be slower or rated
harder.

## The scenario

Three books on a desk, as in `FullAbstractionMulti.books`:

- volume 1: a copy of *Emma*. Call this book A.
- volume 2: a two-novel omnibus edition holding *Emma* and *Persuasion*.
  Call its two books B (*Emma*) and C (*Persuasion*).

John picked up every volume and read every text. Two overlapping groups
of books:

- P = "the copies of *Emma*": A and B;
- Q = "the books in the omnibus": B and C.

So "P and Q" is B alone, and "P or Q" is all three.

**Why the omnibus is unavoidable.** If every volume holds one text, then
"same volume" implies "same text", so "same volume or same text" is
transitive (`Criteria.dotSame_trans_of`). Double distinctness is then
counting by one equivalence relation (`DotSetoid.exists_setoid_iff`),
which obeys the law. If every text has one copy, the symmetric argument
gives the same (not formalized). So no scenario can separate DD from one criterion
without both a text with two copies and a volume with two texts.

The second is the reading that Sutton (2024, p. 877, n. 1) and
Chatzikyriakidis & Luo (2018, n. 4) find marginal. The protocol must
make it salient (an omnibus with two title pages, described as "two
novels in one binding"). It must also check that participants count B
and C as two books (manipulation check below).

## The questions and the predicted answers

| books asked about | "picked up" (by volume) | "mastered" (by text) | "picked up and mastered" (both) |
|---|---|---|---|
| A, B (P) | 2 | 1 | 1 |
| B, C (Q) | 1 | 2 | 1 |
| A, B, C (P or Q) | 2 | 2 | 2 |
| B (P and Q) | 1 | 1 | 1 |
| law: (P or Q) + (P and Q) ≤ P + Q | 3 ≤ 3, holds | 3 ≤ 3, holds | 3 ≤ 2, **fails** |

The last column is double distinctness, checked in Lean: at least 2 for
all three (`books_union`), at least 1 for B (`books_inter`), at most 1
for P (`books_01`) and for Q (`books_12`). The first two columns count
by one criterion, so they obey the law (`count_submod`).

Predicted answers to the conjoined question:

- DD: the "both" column.
- PV: the volume column or the text column, whichever reading the
  context gives. Never the "both" column.
- QUD: the "both" column in the neutral context, and a single column in
  the QUD context.

## Reading switches: what the design must control

Liebesman & Magidor (2026, pp. 19-20) show that "Alice picked up three
books" can count texts, and "Three books are by Tolstoy" can count
volumes, given the right context. So a speaker's criterion can change
from one sentence to the next. That has two consequences.

1. **Never pool across speakers or questions.** Suppose the modal
   answer to the P question comes from text-readers (1), the modal
   answer to the Q question from volume-readers (1), and both groups
   answer 2 and 1 to the other two questions. Then the modal answers
   are 1, 1, 2, 1, which break the law. Yet every speaker counted by
   one criterion. So the law must be tested **per participant**: each
   participant answers all four group questions for one verb, in one
   context. The analysis counts participants whose own four answers
   break it.
2. **Fix the context across the four questions.** Present one scenario
   and one framing for all four questions, and ask after each answer
   "which books did you count?", with the books pictured. A participant
   who switches criterion between questions, by their own report, is
   analysed separately.

## Conditions

- **Verb** (between participants): "picked up", "mastered", "picked up
  and mastered". The single verbs are controls: every account predicts
  that they obey the law.
- **Context** (between participants), from Sutton (2024):
  - *neutral*: the scenario only, with no salient grouping;
  - *QUD*: a prior question that makes one criterion the point, for
    instance "John is weighing his luggage allowance: how many books
    did he pick up and master?" (volumes), or "John is preparing for a
    literature exam on separate novels" (texts).
- **Order of the four questions**, counterbalanced.

## Further items (separate from the law test)

- **Liebesman & Magidor's counterexample** (2026, p. 21, ex. (37)): ten
  wrinkled copies of *War and Peace*, two of *Wuthering Heights*. Ask
  for a true/false judgment on "Exactly one wrinkled book is by
  Tolstoy". DD (Gotham's version) predicts true; PV predicts false.
  `count2` gives 1 here (all ten copies share a text).
- **Sutton's modifier pair** (2024, exx. (10)-(11)): "I memorised the
  first page of three damaged, insightful books" against "I tore out the
  first page of three ..." in her display-pile context. Ask whether the
  sentence can be true when two of the books are copies of one text.
  Her account predicts no for *memorised* and yes for *tore out*.
- **Gotham's Granger item** (Gotham 2022, via L&M 2026, p. 34, ex. (68)):
  "Granger memorized three yellow books", with three yellow copies of
  one text. DD predicts false. Liebesman & Magidor (n. 38) doubt that
  judgment.

## What each outcome would show

- **Participants' own four answers to the conjoined question break the
  law**, with a stable criterion by their own report. Then no account
  with one criterion can model these speakers, whatever it takes a book
  to be. PV is refuted for this construction, and DD is supported. If
  this happens only in the neutral context, Sutton's QUD account is
  supported over DD as stated.
- **Answers obey the law** (for instance the volume or the text column
  throughout). Then double distinctness is wrong for these speakers in
  this context, and a one-criterion account suffices, as PV says.
- **A second, weaker prediction** holds on every account considered
  here. The conjoined answer never exceeds either single answer
  (`TwoCriteria.count2_le_mix`, with the mixture that counts everything
  by text and the one that counts everything by volume). Answers above
  either would show a reading this project does not model.
- **Difficulty.** If law-breaking answers are slower or rated harder
  than law-obeying ones, that fits Landman's indexing cost. If they are
  not, it counts against treating double counting as a repair.

## Method notes

- Rothstein (2017, ch. 5, pp. 117-121) and Landman (2020, pp. 197, 214)
  report Barner & Snedeker's (2005) "Who has more N?" comparisons, a
  well-tried way of eliciting counting judgments without asking for a
  number. A comparative version would test the same law ("Who picked up
  and mastered more books, John or Mary?", with two scenarios differing
  in one group). Here too, each participant must see all the
  comparisons the law needs.
- **Manipulation check**: before the test questions, ask how many books
  (not volumes) the omnibus contains. Participants who answer one
  reject the composite-book ontology (Gotham's; Asher's anthology).
  For them the scenario has only two books, and the law test is
  vacuous. Analyse them separately.
- **Matching across conditions.** Keep word order and structure the
  same across conditions. Sutton (2024, p. 878) shows that "three
  damaged, insightful books" and "three insightful, damaged books"
  differ.
- **Measures**: the number, the "which books did you count?" report, a
  difficulty rating, and response time if run online.
- The design needs a power analysis and ethics approval before running;
  neither is attempted here.
