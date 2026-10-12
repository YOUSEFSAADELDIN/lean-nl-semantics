# Paper B: outline

Working title: **Every "yes" is a proof: where a logic-based NLI pipeline
goes wrong, and how it can refuse instead.**

Every figure below is from a CI run named next to it, or from a paper we
have read; nothing here is new evidence. Status markers: **[have]** done
and confirmed, **[gap]** not done, **[decide]** needs a decision.

## Thesis

When a pipeline's verdicts are machine-checked proofs, the prover cannot
be the source of a wrong answer: every error is a translation error. So
the pipeline should be judged by its wrong answers, and designed to
refuse a problem rather than guess. We build one (FraCaS's English to
Lean, end to end), measure what each of its safeguards prevents, find
the one mechanism behind every naming error it has made, close it with
one check, and test it on problems it was never developed on.

## Contributions

1. **An end-to-end pipeline whose every verdict is a Lean proof**: GF
   parse with a restricted grammar, generic ranker, readings of ambiguous
   English, translation, a fixed prover. [have]
2. **The every-reading rule**: "yes" only if every reading of the
   ambiguous English proves it. Measured against committing to one
   reading and against FraCoq's "any reading" rule. [have]
3. **Safeguard ablations**: each safeguard switched off in turn, and the
   wrong answers it lets through. [have]
4. **The name check**: fused predicate names are bound variables, so a
   name that drops a word is harmless unless it also names a different
   phrase. Every naming error the pipeline has made is that collision;
   one check refuses it, and subsumes two earlier safeguards. [have]
5. **A held-out test on MED**, with a frozen pipeline and a stated
   protocol, reported as precision and coverage. [have]

## Results

### FraCaS (development set; CI run 38176812855)

| | matched | wrong |
|---|---|---|
| reached | 259 / 342 | |
| always "unknown" | 90 / 259 | |
| as translated | 181 / 259 | 0 |
| with background knowledge | 240 / 259 | 0 |

### Against systems that parse FraCaS's English

Same 181 problems and labels as ccg2lambda (Mineshima et al. 2015,
Table 3, checked against the paper); this pipeline's figures from CI run
38101249418 (no problem in these sections changed since):

| | quantifiers | plurals | adjectives | comparatives | verbs | attitudes | total |
|---|---|---|---|---|---|---|---|
| ccg2lambda | .77 | .67 | .68 | .48 | .62 | .77 | .69 |
| Haruta et al. 2020 (73 / 22 / 31 problems) | .92 | - | .86 | .77 | - | - | - |
| this pipeline, background knowledge | .96 | .70 | .91 | .65 | .88 | .77 | .834 |

FraCoq, under its own labels and rules (`compare_fracoq.py`): 81.9% on
its 2017 subset (FraCoq .83), 74.1% on its 2019 set (.89), 73.9% on its
2021 set (.81). Below FraCoq everywhere; FraCoq uses a hand-built
treebank and partly hand-made proofs.

### Ablations (CI run 38273607580)

| switched off | wrong, as translated | wrong, background |
|---|---|---|
| nothing | 0 | 0 |
| every reading → weak only | 1 | 2 |
| every reading → strong only | 4 | 4 |
| every reading → any reading (FraCoq's rule) | 5 | 6 |
| presupposition in "no" claims | 0 | 1 |
| determiners, numerals, progressive mark in names (name check on) | 0 | 0 |
| telicity | 0 | 2 |
| non-subsective / non-veridical exclusions | 0 | 2 |
| the name check (alone; reaches 119 again) | 0 | 0 |

Without the name check, the names row was 3 and 5 (CI run 38105846712).

### Held-out: MED (CI run 38138826755, frozen)

| | reached | entailments proved | decided | wrong |
|---|---|---|---|---|
| frozen run | 989 / 5,345 | 137 / 477 | 140 | 3 |
| with the name check (post-hoc) | 961 | 137 / 465 | 139 | 2 |

- Precision of "yes": 137/140 (97.9%) frozen. For scale, on SICK (a
  different dataset): LangPro 98.0 precision / 58.1 recall, Martínez-Gómez
  et al. 97.0 / 63.6 (as tabulated by Chen et al. 2021, Table 3).
- Whole-MED accuracy, for context only: NeuralLog 93.4 (Chen et al. 2021,
  Table 4). This pipeline reaches 18.5% of MED and is not comparable on
  accuracy.
- The 3 wrong: 2718, a real translation error (the name collision);
  536 and 2504, defects of MED's pair construction (Yanaka et al. 2019,
  3.1.3: swapped pairs get the reversed label; 536 is a swap whose label
  was not reversed, 2504 a swap whose hypothesis repeats its premise; 15
  such pairs in MED).
- Haruta et al.'s 498-problem subset: .600 against a .584 all-"unknown"
  baseline (Haruta et al. .84); 8/207 entailments proved; 0 wrong.
- The name check refuses 28 reached problems. 27 of them were answered
  "unknown" anyway, but some would turn wrong once lexical knowledge is
  added (`HeldOut/README.md`, 4897).

### Held-out: SICK, the fixed pipeline (CI run 38227786430)

Pre-registered (`HeldOut/SICK/README.md`, committed before the claims);
pipeline frozen at ac92c4e, name check included.

| | reached | decided | wrong | precision | recall (whole split) |
|---|---|---|---|---|---|
| as translated | 1,416 / 4,906 | 19 | 0 | 100% | 0.9% |
| background knowledge | 1,416 / 4,906 | 52 | 0 | 100% (95% lower bound 93.2%) | 2.5% |
| LangPro (Chen et al. 2021, Table 3) | | | | 98.0 | 58.1 |
| Martínez-Gómez et al. 2017 (same) | | | | 97.0 | 63.6 |

## Limitations to state up front

- The grammar is restricted to FraCaS's constructions: 18.5% of MED is
  reached, and on Haruta's subset the pipeline is at the "unknown"
  baseline. This is a precision paper, not a coverage paper.
- Every FraCaS safeguard was added after a wrong answer on FraCaS; the
  name check after one on MED. The held-out runs are MED (before the
  name check) and SICK (after it, pre-registered).
- The name check covers naming only. Constructions with no word of
  their own are covered only when listed (the progressive and the
  passive are); a false background fact is not caught (the telicity
  ablation's 2 wrong).
- No lexical knowledge: MED's lexical problems can only be "unknown".

## Gaps

1. **[have] A held-out test of the fixed pipeline**: SICK, above. Its
   precision sample is small (52 answers); a larger one needs more reach,
   not more tuning.
2. **[gap] Related work**, all read: Bernardy & Chatzikyriakidis
   2017/2019/2021, Mineshima et al. 2015, Haruta et al. 2020, Abzianidze
   2015, Ljunglöf & Siverbo 2012, Yanaka et al. 2019, Chen et al. 2021.

## Out of scope for this paper

The MTT core, the nouns-as-types comparison (Paper A), the linglib
bridge, the hand-written FraCaS corpus except as the source of the
parse grammar, the GF cross-check, and the browser lab.
