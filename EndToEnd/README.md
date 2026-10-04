# The end-to-end pipeline: FraCaS from its own English

This directory is the project's fourth part, alongside the MTT core, the
hand-written FraCaS corpus, and the linglib bridge. It translates FraCaS
problems into Lean **automatically, from their original English**, and
scores the result with a fixed prover.

| file | what it is |
|---|---|
| `gen_claims.py` | the generator: English → parse → rank → resolve → translate → assemble (needs the `gf` binary) |
| `Claims.lean` | its output, committed; CI regenerates it and fails on any difference |
| `Quantifiers.lean` | `More` and the lemmas only these claims use |
| `Prover.lean` | the tactic chain that scores the claims (`attemptCloseEndToEnd`) |
| `Scan.lean` | the evaluation itself, run by its own CI job |
| `readings.py` | how ambiguous English is read (weak/strong readings, counted objects, …) |
| `parse_rank.py` | parsing and generic ranking |
| `gen_parse_grammar.py`, `FraCaSParse*.gf` | the restricted parse grammar (generated) |
| `parse_eval.py` | parser quality on the confirmed sentences |
| `background.py` | problem-independent background knowledge |

**What it shares with the rest of the project.** Two things in `gf/`:
the FraCaSLogic grammar, which the parse grammar restricts, and
`translate.py`, the tree-to-`Prop` translator. `translate.py` reads each
construction one way, the way the hand-written corpus's GF cross-check
needs; `readings.py` plugs into its one extension point (the `Readings`
class) and holds every reading the pipeline adds. CI snapshots every
default translation (`gf/default_translations.tsv`) and regenerates the
cross-check theorems, failing if either changes, so work here cannot
silently change the cross-check.

**These are development-set figures, not blind ones.** The grammar
constructions, translator rules, ambiguity readings and prover steps were
each added after seeing which of these same FraCaS problems failed. There
is no held-out FraCaS; a reader should weigh the numbers below
accordingly. The prover here extends the hand-written corpus's evaluation
chain (`attemptClose`, frozen) in its own file, so none of this tuning
can move that evaluation's number.

## How it works


The hand-written corpus's evaluation (`BLIND_EVAL.md`) scores inference
over a `Prop` a human wrote. This part of the project removes the human
from the translation step as well, for every problem the automated
pipeline can carry all the way through (`EndToEnd/gen_claims.py`):

1. **English**: each premise and hypothesis exactly as FraCaS states it,
   through one generic lexer step (`EndToEnd/parse_rank.py`'s `tokenize`: final
   punctuation dropped, commas split off, each token looked up in the
   grammar's own vocabulary case-insensitively) — never the project's own
   confirmed rewordings in `gf/run_gf_tests.py`.
2. **Parse** with a restricted GF grammar (`EndToEnd/gen_parse_grammar.py`).
   Parsing with the full FraCaSLogic grammar is unusable — 69,115
   readings in five minutes for one Section 1 sentence, none free of junk
   constructions — so the parse grammar inherits only the functions and
   words the CI-confirmed trees use. That makes it a controlled-language
   grammar fit to FraCaS's vocabulary (the same kind of artifact FraCoq's
   FraCaS-specific grammar is); it does not tell the parser which tree
   goes with which sentence. FraCaS's own wording needed four
   constructions the hand-built trees (written for the project's
   rewordings) never used: the "who" relative pronoun, the "there
   are/was X who…" existential that most Section 1 hypotheses use, the
   frozen "used to", and "just one"; each has one confirmed linearize
   check (`_FRACAS_ENGLISH_CHECKS`). A later round added Section 4's VP
   ellipsis ("so did Bill", "Bill didn't", "the students have too"),
   one-anaphora ("a blue one", "owns one too") and uncontracted negation
   ("is not") the same way; readings that use anaphoric "one" as anything
   but the head of a noun phrase are discarded as ill-formed.
3. **Rank** the readings generically (`EndToEnd/parse_rank.py`): fewest nodes,
   ties broken by right association (attach adverbials as low as
   possible).
4. **Resolve** ellipsis and one-anaphora by copying the antecedent
   clause's verb phrase or noun (the standard copy treatment; "a blue
   one" after "a red car" contrasts with the antecedent's outermost
   adjective), then **translate** with `gf/translate.py` and **assemble**
   by one generic rule — bind every free predicate/individual, chain
   premises into the hypothesis — with no per-problem cases. Sentential
   negation is translated only with a proper-name subject, where its
   scope is unambiguous. A proper-name subject's counted object ("APCOM
   won ten orders", "ITEL won some orders") keeps its verb as a binary
   predicate and its determiner as a quantifier over it, rather than
   being fused into one predicate name. Quantity comparatives ("ITEL won
   more orders than APCOM did / than APCOM / than APCOM lost") translate
   to `More order (win itel) (win apcom)`, a comparison of two counts
   (`GQ.lean`), with an elided verb resolved to the main clause's. Fused
   names keep an object's numeral: they used to drop it, which made "won
   ten orders" and "won eleven orders" the same predicate.
   A coordinated subject ("Smith, Jones and Anderson signed the
   contract", "either Smith, Jones or Anderson …") distributes over its
   conjuncts or disjuncts, except where its collective reading is live:
   with a collective verb ("Smith, Anderson and Jones met") or a counted
   object ("Smith and Jones signed two contracts", whose cumulative
   reading 111–113 test) it is left untranslated. "It is true/false that
   S" is S / ¬S; "everyone (at the meeting)" is every person (at the
   meeting); "one of the Ns" is a counted partitive, ambiguous like a
   bare numeral; and a fronted adverbial ("In 1993 ITEL won …") modifies
   the VP, with a proper-name subject and no negation, where its scope
   is the same as in final position.
5. **Never commit to one reading of ambiguous English.** Six kinds of
   ambiguity are translated in a weak and a strong reading: a definite
   plural subject ("the inhabitants voted" — collective/generic `Some`,
   or distributive `Every` plus the definite's existence presupposition);
   a bare plural with a relative clause (existential or generic); "many"
   (cardinal, read as `Some`, or proportional — an opaque relation stated
   only with properties every reading shares: it entails "some" and is
   upward monotone in its scope, but not in its restrictor); plural
   "some Xs" (number-neutral, or at least two); a bare numeral ("ten
   orders": at least ten, or exactly ten); and "few" (a small number —
   `AtMost` an unknown threshold — or a small proportion, an opaque
   relation stated only with the property both readings share: narrowing
   its scope within its restrictor preserves it). "A few"/"at least a
   few" are vague rather than ambiguous: `AtLeast` an unknown threshold
   of at least one, not plain `Some` (which would make "some X are Y"
   entail "a few X are Y"); "several" likewise, with a threshold of at
   least two. "Both"/"neither" use the
   corpus's own `Both`/`Neither`, which keep the exactly-two
   presupposition. Each problem is translated under every *consistent*
   assignment of readings — the same word read the same way in each of
   its sentences — and the scan answers "yes"/"no" only if the
   corresponding claim is proved under **every** assignment.
6. Each problem is scored twice: as translated, and with **background
   knowledge** from `EndToEnd/background.py` added as premises. That knowledge
   is problem-independent: entailments derived from the parse trees
   themselves (deleting an intersective modifier in an upward-monotone
   position — "win the Nobel prize *for literature*" ⊑ "win a Nobel
   prize" — never for non-subsective adjectives like "former", never
   under `every`/`no` objects or VP-complement verbs, never for a
   durative "for two hours"), plus a small closed degree-semantics
   lexicon (antonym contraries such as small/large over the *same* noun,
   a comparative's standard transferring upward, comparative asymmetry,
   antonym converses). Nothing in it is keyed by problem or gold answer,
   but the lists were written with this corpus in view, so it is not a
   held-out resource.

The `build-gf` CI job regenerates the claims file from the English and
fails if it differs from the committed copy, so the scored claims are
reproducible.

**Parser quality, on the 456 distinct CI-confirmed sentences**
(`EndToEnd/parse_eval.py`; 449 before `main`'s anaphora and degree-
adjective work was merged in): all 456 parse; the hand-built tree is
among the readings for all 456; median 4 readings (max 3,600); and the
top-ranked reading translates to the same `Prop` as the hand tree for 388
of the 389 sentences `translate.py` covers. The one exception (136) is a garden-path
compound ("[executive that had a laptop] computer") tied in size with the
correct reading. The right-association tie-breaker was added after
inspecting misses of the size rule alone on these same sentences, so this
is not a held-out figure.

**Coverage, on FraCaS's original English**: 219 of 342 problems go all
the way through (64.0%). 103 stop at a sentence the restricted grammar
doesn't parse, 13 at a reading the translation doesn't cover, 6 at a
translation needing non-generic assembly, and 1 (104) at a predicate
named after a Lean keyword (`have`). Of the 103, the remaining parse
failures are mostly hard phenomena rather than missing glue: tense and
aspect (41 problems, Section 7), ellipsis forms such as gapping and
fragments ("Bill by train.", 39, Section 4), cross-sentence anaphora,
attitude reports, and numbers written as digits. The last cheap round
added the remaining small constructions: perception reports ("Smith saw
Jones sign the contract"), "every X and every Y was", a floated "all"
before the verb, "if S, S", "more than n", and comparatives inside a
noun phrase ("a fatter politician than Bill"), each with one linearize
check of FraCaS's own sentence. The quantity comparatives that census
also found ("ITEL won more orders than APCOM did") are now covered (step
4 above). Giving the parse grammar the full
dictionary entries for every word FraCaS uses was tried and rejected: it
unlocked only 25 sentences (nearly all untranslatable) at up to 34,902
readings per sentence.

**Result** (CI run 37240689801), on those 219 problems:

| | matched | wrong answers |
|---|---|---|
| always "unknown" (baseline) | 80/219 (36.5%) | — |
| as translated | **136/219 (62.1%)** | **0** |
| with background knowledge | **158/219 (72.1%)** | **0** |

Counting the 123 problems the pipeline cannot yet reach as "unknown",
corpus-wide that is 162/342 (47.4%) as translated and 184/342 (53.8%)
with background knowledge, against a 31.0% baseline ("unknown" also
counts as matching FraCaS's "undef").

The cheap-construction round (CI run 37240689801) lost no previously
matched problem and gained 84, 89, 93, 217 and 342; 216 ("John is a
fatter politician than Bill" ⇒ "John is fatter than Bill", gold yes) is
"unknown" by design, since "fatter as a politician" coincides with
"fatter" only for some adjectives (not "clever", 217), which the
pipeline has no lexicon for. Before that, CI run 37205860267 gave
131/213 and 153/213.

Before the round before that (coordinated subjects, "several", "it is
true/false that", "everyone", counted partitives, fronted adverbials;
CI run 37199853258, reproduced after `readings.py` was split out of
`translate.py` in run 37205385335) the figures were 118/195 and
139/195, also with no wrong answers; that round lost no previously
matched problem and gained 62, 78, 81, 82, 83, 85, 91, 92, 295, 331,
332, 338, 339, and 297 with background knowledge. Of the problems it
newly reaches, 46 and 86 (gold "no") stay "unknown" because refuting
them needs the exactly-two of "neither" or an "exactly" read as
distributing over both conjuncts of "exactly two lawyers and three
accountants"; 133 needs e-type anaphora ("ITEL maintains them"); and
258 and 307 need temporal reasoning. (The previous
version of this file gave one corpus-wide figure, 164/342; that was the
with-background-knowledge number, and it was not labelled as such.) 0
contradictions and 0 errored attempts in either variant.

**Every mismatch is fail-safe**: "unknown" where gold says yes or no,
never a wrong answer. The previous version of this pipeline gave 5 wrong
answers (56, 77, 94, 95, 109), all from translation shortcuts that
committed to one reading — "the inhabitants voted" read distributively,
"many" read as "some", "both" read as "every", plural "some accountants"
read as "at least one". Step 5 above removes all five without per-
problem cases. Its cost is that a genuinely ambiguous problem now gets
"unknown", and some FraCaS gold answers do pick one reading:

- **107 and 109 are the same English with opposite gold answers** ("Just
  one accountant attended the meeting" ⇒ "Some accountants attended the
  meeting": yes in 107, no in 109) — FraCaS encodes the number-neutral vs
  at-least-two ambiguity as a pair. No consistent system can get both;
  "unknown" on both is the principled outcome.
- **230, 233, 239** ("ITEL won more orders than APCOM [did / lost]" ⇒
  "ITEL won some orders", gold yes) follow on the number-neutral reading
  of "some orders" but not on the at-least-two reading, the same
  ambiguity as 107/109, so the pipeline says "unknown". The other six
  problems in the group (231, 232, 234, 235, 240, 241) match.
- **76** ("Few committee members are from southern Europe" ⇒ "Few
  female committee members are", gold yes) holds on the small-number
  reading of "few" but not the proportional one (if the only southern
  European member is one of two female members, few members but half the
  female members are from southern Europe), so the pipeline says
  "unknown". The rest of the "few"/"a few" group matches: 11, 12, 27, 28,
  43, 44, 60 and 75, and 59 with background knowledge.
- **13** ("Leading tenors who are excellent are indispensable" read
  generically) and **160** ("a fast one" after "a red car" read as "a
  fast red car") are FraCaS committing to one reading of a genuinely
  ambiguous sentence; the pipeline says "unknown".

How the remaining "unknown"s split: most need knowledge neither the
translation nor `EndToEnd/background.py` supplies (comparisons across noun
classes, 208; former-student inferences, 198-199), counting arguments the
generic prover doesn't find (105, 106), or temporal reasoning that the
fused predicate names cannot express (Section 7, 261-306).

One background-knowledge rule *was* unsound and has been fixed, a fix
found from its observed failure: the first version deleted durative
"for two hours" like any other modifier, so "Smith wrote a report for
two hours" ⇒ "Smith wrote a report" (304, gold unknown — an
accomplishment need not culminate). Durative "for"-phrases are no longer
deletable. That also removes the fact for 306 ("discovered a new species
for two years" ⇒ "discovered a new species", gold yes, valid for an
iterated achievement); telling those apart needs lexical aspect classes,
which this pipeline does not have, so it takes the conservative side.

How the translator was improved for this, beyond the grammar additions:
`translate.py` keeps prepositions and determiners in verb-phrase
predicate names ("resident **in**" vs "resident **outside** Europe",
FraCaS 74; "spend **a lot of** time" vs "spend time", 30–32/47), reads a
definite plural object universally (the convention it already used for
subjects), translates comparatives and equatives as binary relations
(`fastThan`, `fastAs`) instead of fusing the standard into a unary name
("as fast as" and "faster than" had coincided, 228), reads "there are X
who VP" as `Some X VP`, "only/just one" as `Exactly 1`, a floated "all"
("the Ancient Greeks were all noted philosophers") as universal, and
translates the two attachments of an adjective-plus-relative-clause noun
phrase identically. Its default reading — the one the cross-check
theorems are proved against — is unchanged throughout.

## Limitations

- Everything in `BLIND_EVAL.md`'s limitations about the prover applies
  here too, and more strongly: `Prover.lean`'s additions were each made
  to win a specific problem (named in that file).
- The parse grammar's vocabulary and constructions are read off this
  corpus's confirmed trees, and its new constructions (ellipsis, quantity
  comparatives, ...) were added for FraCaS's own sentences.
- The ranker's tie-breaker and one background-knowledge rule were chosen
  after observing failures on this same corpus, and the background
  lexicon was written with FraCaS in view. Both the with- and
  without-knowledge scores are reported, so the knowledge module's
  contribution can be read off directly.
- Comparing with FraCoq: this is the comparable *kind* of measurement
  (automatic translation from English), but it reaches only part of the
  corpus and is not competitive with FraCoq's reported 83%/81% on what it
  does reach. Its distinguishing property is that it gives no wrong
  answers on what it reaches, with every verdict machine-checked.
