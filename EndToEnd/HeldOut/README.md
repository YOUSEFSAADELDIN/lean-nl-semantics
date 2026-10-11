# The held-out test: MED through the frozen pipeline

Every end-to-end figure on FraCaS is a development-set figure: the
grammar, readings, background knowledge and prover were extended by
looking at which FraCaS problems failed. This directory tests the
pipeline on problems it was never developed on.

## The data

**MED**, the Monotonicity Entailment Dataset (Yanaka, Mineshima, Bekki,
Inui, Sekine, Abzianidze and Bos 2019; `github.com/verypluming/MED`,
commit `860ba36`, CC BY-SA 4.0): 5,382 single-premise problems.
Most were collected by crowdsourcing; the rest come from linguistics
publications. `MED.tsv` is the file as published. It and the claims
generated from it (`Claims.lean`) are under CC BY-SA 4.0 (see
`CREDITS.md`).

- **Excluded**: the 37 problems MED marks as taken from FraCaS, and any
  problem with a FraCaS sentence verbatim (none beyond those 37).
  5,345 remain.
- **Labels** are two-way: entailment, or neutral (which includes
  contradiction).

## What is frozen, and the one thing added

Everything that decides an answer is the pipeline's own, as it stood
before this test was run:
- the constructions the parse grammar admits;
- the ranker and discourse resolution;
- the readings and the every-reading rule;
- the translator and the background knowledge;
- the assembly and the prover.

FraCaS's vocabulary is about 1,300 words, and only 5 MED problems use
nothing else. So the parse grammar's vocabulary is extended by one rule,
applied mechanically (`gen_heldout.py`):

- a word the FraCaS grammar does not know gets every open-class entry
  (noun, verb, adjective, adverb, proper noun) that the RGL's general
  English dictionary (DictEng) gives it: 6,441 entries;
- a capitalized word with no such entry is a proper noun: 45 names.

Closed classes are never extended: pronouns ("I", "you", "we"),
determiners, prepositions, conjunctions. Nor is any construction, and
no lexical knowledge is added ("dog" ⊑ "animal"): MED's lexical problems
can only come out unknown. Adjectives the lexicon does not classify are
treated as plainly subsective, the pipeline's default.

**The rule for this test**: the pipeline is not changed in response to
what it shows. The claims were generated once, at the commit that added
them, and are scored as they are.

## Reach

| | problems |
|---|---|
| MED, minus FraCaS | 5,345 |
| a word outside the frozen closed classes | 1,891 |
| does not parse with the frozen constructions | 1,807 |
| parses, but does not translate | 658 |
| **reached** | **989** (477 entailment, 512 neutral) |

## Scoring

The pipeline's verdicts are yes, no and unknown. Against MED's labels:
- **matched**: "yes" on entailment, or "no"/"unknown" on neutral;
- **wrong**: "yes" on neutral, or "no" on entailment (a reading
  assignment proving both counts as wrong);
- **missed**: "unknown" on entailment, which is neither.

"Unknown" on neutral counts as matched, which makes neutral problems
easy. The figures to read are the wrong answers and how many entailment
problems are proved.

## Results (CI run 38138826755)

On the 989 reached problems (477 entailment, 512 neutral):

| | entailment proved | matched | wrong answers |
|---|---|---|---|
| as translated | 1 / 477 | 512 / 989 | **1** (2504) |
| with background knowledge | 137 / 477 | 646 / 989 | **3** (536, 2504, 2718) |

The pipeline never answered "no": MED's neutral problems are not
contradictions, and none was refuted. Background knowledge is what
proves things here: 136 of the 137 entailments come from its
problem-independent structural entailments, mostly a modifier deleted
in an upward-monotone position, which is what MED's upward problems
test. Without lexical knowledge ("dog" ⊑ "animal"), MED's lexical and
most of its downward problems stay unknown.

**The three wrong answers**, each "yes" on a problem labelled neutral:

- **2718** is a **pipeline error**. "Tom said he didn't drink black
  coffee" ⊢ "Tom said he didn't drink coffee" became `drinkBlackCoffee
  tom → drinkCoffee tom`: both "said" and "didn't" vanished. The
  translator names a verb phrase after the words in it, and keeps only
  words whose category it lists (`translate.py`'s `_LEXICAL_SUFFIXES`).
  A sentence-complement verb (`say_VS`) is not listed, and nor is the
  negation of an embedded clause. On FraCaS every "say/know/believe"
  sentence was caught first by the attitude reading (`readings.py`'s
  `_attitude`), which declines when the complement is negated or its
  subject is a pronoun, so the gap never showed. It is a soundness bug:
  the claim says something the English does not.
- **2504** has the same sentence as premise and hypothesis ("You can't
  live on a desolate island"), labelled neutral. Any sound system says
  yes; the label looks like an annotation error.
- **536**, "A cold bubbly bath refreshed him" ⊢ "A cold bath refreshed
  him", labelled neutral. "Bubbly" is intersective here, and deleting it
  under "a" is upward monotone, which is what MED's own tag
  (`upward_monotone`) says; the label looks like an error too.

Counted as the protocol says, that is 3 wrong answers in 140 decided
(yes) answers with background knowledge, and 1 of 2 without. Against
labels corrected for 2504 and 536 it would be 1 of 140: the one real
error, 2718. Either way, "zero wrong answers" does not survive the
held-out test as a property of the pipeline.

## What this does and does not show

- It is a test of soundness more than accuracy. MED is about monotonicity
  and lexical knowledge; the pipeline has the first only as structural
  modifier deletion and none of the second. 137 of 477 entailments is
  the honest accuracy figure.
- It found a real failure the FraCaS development set could not, of the
  kind the project's design is meant to exclude.
- The pipeline is unchanged by it. A fix for 2718's cause belongs in a
  separate change, and once made, a re-run on MED is no longer held out.
