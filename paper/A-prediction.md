# A testable prediction: one criterion versus copredication

Draft protocol. Nothing here has been run. Running it needs human
participants, which is your decision.

## The law

Count a noun's things that have some property. For every noun with one
identity criterion, whatever encodes it (a type with a criterion, a
predicate with a criterion, a setoid, a counting context in Rothstein's
sense, a base in Landman's sense), counts obey

> count(P or Q) + count(P and Q) ≤ count(P) + count(Q)

(`CountingLaws.count_submod`). Counting by two criteria at once, as
Gotham (2017) and Chatzikyriakidis & Luo (2018) propose for "picked up
and mastered three books", can break it
(`FullAbstractionMulti.not_single`). So the law separates *every*
one-criterion account from double distinctness at once, without
choosing among the one-criterion accounts. It is a law about the
pattern of answers, not about any single answer.

## The scenario

Three books on a desk, as in `FullAbstractionMulti.books`:

- volume 1: a copy of *Emma*. Call this book A.
- volume 2: an anthology holding *Emma* and *Persuasion*. Call its two
  books B (*Emma*) and C (*Persuasion*).

John picked up every volume and read every text. Two overlapping groups
of books:

- P = "the copies of *Emma*": A and B;
- Q = "the books in the anthology": B and C.

So "P and Q" is B alone, and "P or Q" is all three.

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

## What each outcome would show

- **Answers to the conjoined question break the law** (as tabulated):
  no account with one criterion can model these speakers, whatever it
  takes a book to be. Copredication needs two criteria, as Gotham
  argues, now on the basis of a law rather than one example.
- **Answers obey the law** (for instance 1 throughout, as a single
  "same volume or same text" equivalence would give): double
  distinctness is wrong for these speakers, and a one-criterion account
  suffices.
- **A second, weaker prediction** holds on every account considered
  here: the conjoined answer never exceeds either single answer
  (`TwoCriteria.count2_le_mix`, with the mixture that counts everything
  by text, and the one that counts everything by volume). Answers above
  either would show a reading this project does not model.

## Method notes

- Rothstein (2017, ch. 5, pp. 117-121) reports Barner & Snedeker's
  (2005) "Who has more N?" comparisons, a well-tried way of eliciting
  counting judgments without asking for a number. A comparative version
  ("Who picked up and mastered more books, John or Mary?") with two
  scenarios differing in one group would test the same law.
- Each participant should see one of the three verbs, so that answers to
  "picked up" do not prime the conjoined question.
- The scenario's appeal to composite books (B and C are two books in one
  volume) is Gotham's ontology. Participants who reject it (one
  anthology is one book) give a different count, and the protocol
  should record which reading they report.
