# The second held-out test: SICK through the frozen pipeline

MED (`../README.md`) was the pipeline's first held-out test, and the name
check (`EndToEnd/names.py`) was written in response to it, so MED cannot
test the pipeline as it now is. This directory tests it on problems it
was never developed on and that nothing in it responds to.

**This file was written, and committed with the data, the generator and
the scorer, before any claims were generated.** What follows the
"Results" heading was added after the run.

## The data

**SICK** (Marelli, Menini, Baroni, Bentivogli, Bernardi and Zamparelli,
LREC 2014), the file `SICK.txt` of the official release, released under
CC BY-NC-SA 3.0 (see `CREDITS.md`). `SICK_test.tsv` is its SemEval 2014
test split (`SemEval_set` = `TEST`), unaltered, every column kept: 4,906
pairs (sha256 `2e18975b79a9511c05260ac3582c63bef6417631685783cedfc024406d3234e6`).
Published results often cite 4,927 test pairs; this release's split has
4,906.

- **Premise and hypothesis**: sentence A and sentence B.
- **Gold label**: `entailment_label`, three-way: ENTAILMENT (1,404),
  CONTRADICTION (712), NEUTRAL (2,790). This is the label the systems
  compared below are scored on. (SICK also gives `entailment_AB` and
  `entailment_BA`, which sometimes disagree with it; they are not used.)
- **Excluded**: nothing. SICK's sentences come from image and video
  captions, not from FraCaS or MED.

## What is frozen, and the one thing added

The pipeline as it stood at commit `ac92c4e`: the parse grammar's
constructions, the ranker and discourse resolution, the readings and the
every-reading rule, the translator, the name check, the background
knowledge, the assembly and the prover. The vocabulary is extended by the
same fixed rule as for MED (`gen_heldout.lexicon`): every open-class
DictEng entry of a word the FraCaS grammar does not know, and a proper
noun for a capitalized word with none. No closed-class word, construction
or lexical knowledge is added.

**The rule for this test**: the pipeline is not changed in response to
what it shows. The claims are generated once, by `gen_sick.py` at the
commit after this one, and scored as they are.

## Scoring

Verdicts are yes, no and unknown (`EndToEnd/SickScan.lean`, the same
prover and every-reading rule as FraCaS and MED), with and without
background knowledge:
- **matched**: yes on ENTAILMENT, no on CONTRADICTION, unknown on NEUTRAL;
- **wrong**: yes on a pair that is not ENTAILMENT, no on one that is not
  CONTRADICTION, or both proved;
- **missed**: unknown on ENTAILMENT or CONTRADICTION.

Reported figures, fixed now:
1. reach: pairs translated, of 4,906;
2. **wrong answers**, each listed and inspected;
3. **precision**: correct yes/no answers ÷ all yes/no answers;
4. **recall**: correct yes/no answers ÷ (ENTAILMENT + CONTRADICTION
   pairs), over the whole test split, unreached pairs counting as
   "unknown" - the definition behind the precision/recall figures of
   LangPro (98.0 / 58.1) and Martínez-Gómez et al. (97.0 / 63.6) on SICK
   (as tabulated by Chen, Gao & Moss 2021, Table 3);
5. accuracy over the whole split, unreached pairs as "unknown", for
   context only.

Every wrong answer is counted as wrong whatever its cause; a label that
looks mistaken is reported as such beside the count, never instead of it.

## Results (CI run 38227786430)

*Added after the run. Nothing in the pipeline has been changed since
`ac92c4e`.*

**Reach** (`sick.json`): 1,416 of 4,906 pairs (28.9%): 592 ENTAILMENT,
762 NEUTRAL, 62 CONTRADICTION. 2,714 do not parse with the frozen
constructions, 454 parse but do not translate, 322 need a closed-class word the grammar lacks.

| | decided | correct | **wrong** | precision | recall (whole split) | accuracy (whole split) |
|---|---|---|---|---|---|---|
| as translated | 19 | 19 | **0** | 100% | 0.9% | .573 |
| with background knowledge | 52 | 52 | **0** | 100% | 2.5% | .579 |

All-"unknown" baseline accuracy: .569. Recall is over all 2,116
ENTAILMENT and CONTRADICTION pairs, unreached ones counting as
"unknown", as defined above.

- **No wrong answer.** With 52 of 52 correct, a 95% (Clopper-Pearson)
  lower bound on precision is 93.2%: the sample is too small to tell
  this precision from LangPro's 98.0 or Martínez-Gómez et al.'s 97.0.
- **What it proves**: 49 entailments, nearly all by deleting a modifier
  in an upward position ("A wild deer is jumping a fence" ⇒ "A deer is
  jumping a fence"; "A man is playing a piano at a concert" ⇒ "A man is
  playing a piano"), plus "one N" ⇒ "a N" and a definite agent made
  indefinite ("by the man" ⇒ "by a man"); and 3 contradictions of the
  form "A N is V-ing" / "No N is V-ing".
- **What it misses**: 543 of the 592 reached entailments and 59 of the
  62 reached contradictions stay unknown. These were not analysed
  pair by pair; SICK's entailments typically need lexical knowledge
  ("man" ⊑ "person") or paraphrase, which the pipeline does not have.
- **Recall is the cost of the design**: 2.5% against LangPro's 58.1%.
  The pipeline reaches 29% of SICK and decides 4% of what it reaches.

So on problems nothing in the pipeline was developed on or changed for,
it gave no wrong answer, and almost no answers.

Every figure here is recomputed by `report.py` from `verdicts.txt` (the
verdict lines of CI run 38227786430), `SICK_test.tsv` and `sick.json`.
