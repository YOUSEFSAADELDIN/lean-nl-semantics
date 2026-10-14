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
  yes.
- **536**, "A cold bubbly bath refreshed him" ⊢ "A cold bath refreshed
  him", labelled neutral. "Bubbly" is intersective here, and deleting it
  under "a" is upward monotone, which is what MED's own tag
  (`upward_monotone`) says. The pipeline answers its reverse, 535 ("a
  cold bath" ⊢ "a cold bubbly bath"), "unknown".

Both are defects of how MED's crowdsourced pairs were built (Yanaka et
al. 2019, §3.1.3). A pair's gold label was set by its direction (a
downward pair entailment, an upward one non-entailment) and kept when
three workers agreed; then, "to make the distribution of gold labels
symmetric", each pair was swapped, premise for hypothesis, and its label
reversed. The swapped pairs follow their originals (`pairID` n+1):
- 536 is 535 swapped, with the label not reversed: by the procedure it
  is entailment. MED has 8 such pairs (535/536, 570/571, 618/619,
  683/684, 1995/1996, 2010/2011, 2066/2067, 2093/2094).
- 2504 should be 2503 ("You can't live on an island" ⊢ "... a desolate
  island", entailment) swapped, and has the swapped label, but its
  hypothesis repeats its premise. MED has 6 pairs with the same sentence
  twice (1612, 1613, 2455, 2504, 3876, 3907), and one pair given both
  labels (2048, 2049).

Counted as the protocol says, that is 3 wrong answers in 140 decided
(yes) answers with background knowledge, and 1 of 2 without. Against
labels corrected for 2504 and 536 it would be 1 of 140: the one real
error, 2718. Either way, "zero wrong answers" does not survive the
held-out test as a property of the pipeline.

**How far the same gap reaches.** The mechanism behind 2718: the
translator names a phrase after the words of the categories it lists,
and a name that leaves words out is harmless by itself (every name is
a bound variable of its claim), but wrong when it is also the name of a
different phrase in the same problem, so that what holds of one is
applied to the other. Measured on the 989 reached problems, after the
run and without changing it (`names.py`'s check applied to the frozen
pipeline's translations): **28 problems** have a name standing for two
phrases that differ in what it leaves out.

| what the name leaves out | problems | example |
|---|---|---|
| the negation of a relative clause | 18 | "every alien who did **not** throw balls" named like "throw balls" |
| "said" and the negation of its complement | 3 | 2718; 2717, 3675 |
| "believes" | 4 | "Pete **believes** he is a spider" named like "is a spider" (5067-5070) |
| "even" | 2 | 4023, 4024 |
| "no longer" | 1 | "Tom is **no longer** a kid" named like "is a kid" (1355) |

Only 2718 turned into a wrong answer. The other 27 came out "unknown":
12 entailments missed, and 15 neutral problems "matched". Those 15 are
right only while nothing is known about the colliding names. Lexical
knowledge, which MED's other problems need ("a quarter is a coin"),
would turn some into wrong answers: 4897's claim, `Every (fun x =>
alienFem x ∧ useCoin x) hairy → Every (fun x => alienFem x ∧ useQuarter
x) hairy`, follows from
"quarter ⊑ coin", but its English ("every alien who did not use coins
is hairy" ⇒ "... did not use quarters ...") does not. An earlier count
here (33 problems, by open-class words the naming drops) missed the
negated relative clauses entirely and counted words that cause no
collision; this table replaces it.

**Against the closest logic-based system.** Haruta, Mineshima and Bekki
(ACL SRW 2020) score MED on "a subset (498 problems) of MED that does not
require world knowledge and commonsense reasoning; these problems were
collected from various linguistics papers". MED's genre tags give
exactly 498 such problems: `paper:` problems with no `lexical_knowledge`
tag, not from FraCaS or GLUE. Their labels split 215/283 (yes/unknown);
this file's split 207/291, so MED's labels have changed since, and the
figures below are close to theirs but not identical. Scoring the frozen
run on them, with unreached problems as "unknown", as their accuracy
counts every problem:

| | reached | accuracy | majority ("unknown") | entailments proved | wrong |
|---|---|---|---|---|---|
| this pipeline (frozen run) | 90 / 498 | .600 | .584 | 8 / 207 | 0 |
| Haruta et al. 2020 | all | .84 | .60 | - | not reported |

So on that subset the pipeline is no better than answering "unknown"
throughout: it makes no wrong answer, and proves almost nothing.

## After the test: the name check (post-hoc)

The fix is the name check (`EndToEnd/names.py`, run by `gen_claims.py`
on every problem): a problem is not translated when one of its names
would stand for two different phrases. It was written after this test,
in response to 2718, so **what follows is not a held-out result**. The
claims above are the frozen pipeline's and are not regenerated; the
check only removes problems, so each remaining problem's verdict is the
frozen run's.

| | reached | entailment proved | decided | wrong answers |
|---|---|---|---|---|
| the frozen run (held out) | 989 | 137 / 477 | 140 | 3 (536, 2504, 2718) |
| with the name check (post-hoc) | 961 | 137 / 465 | 139 | 2 (536, 2504) |

The check refuses the 28 problems in the table above and nothing else.
The two wrong answers left are the two labels that look wrong (536,
2504); neither involves naming. On FraCaS the check refuses one problem
(119, "unknown" before) and changes no verdict; it also subsumes two
of the pipeline's earlier safeguards (`EndToEnd/README.md`, "The name
check").

## Reproducing these figures

Every figure above is recomputed by `report.py` from recorded inputs:
`verdicts.txt` (the verdict lines of CI run 38138826755), `heldout.json`
(the frozen run's reach), `MED.tsv`, and `namecheck.json` (the post-hoc
name check's 28 refusals, written by `posthoc_namecheck.py`). With the
name check, precision of "yes" is 137/139 (98.6%).

## Re-run with every proof kernel-checked

CI run 38523449354 scored the same frozen claims with every proof
checked by Lean's kernel before it counts (`EndToEnd/README.md`, "The
kernel check"). All 989 verdicts are unchanged in both variants, so
every figure above stands.

## What this does and does not show

- It is a test of soundness more than accuracy. MED is about monotonicity
  and lexical knowledge; the pipeline has the first only as structural
  modifier deletion and none of the second. 137 of 477 entailments is
  the honest accuracy figure.
- It found a real failure the FraCaS development set could not, of the
  kind the project's design is meant to exclude.
- The pipeline was not changed during it. The fix for 2718's cause, the
  name check, came after, and its MED figures above are post-hoc: a
  clean test of the fixed pipeline needs problems it has not seen.
