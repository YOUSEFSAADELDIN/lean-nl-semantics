# The end-to-end pipeline: FraCaS from its own English

This directory is the project's fourth part, alongside the MTT core, the
hand-written FraCaS corpus, and the linglib bridge. It translates FraCaS
problems into Lean **automatically, from their original English**, and
scores the result with a fixed prover.

It does not use the MTT core. Like the hand-written corpus, its claims
state nouns as predicates over one domain of individuals (`commissioner
: A → Prop`); where it borrows an idea from dependent type semantics (a
possessive as a function of its possessor, `workstationOf`), it encodes
it as a function on that domain, not as a Σ-type. Its figures are
therefore evidence about the pipeline's methods - parsing, ranking,
reading ambiguous English, background knowledge, the prover - under the
predicate encoding, and not about MTT.

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
| `FraCaSEndToEnd*.gf`, `english_checks.py` | the pipeline's extension of `gf/`'s grammar, and its linearize checks |
| `background.py` | problem-independent background knowledge |
| `Encodings/` | the same parsed problems restated with nouns as types (MTT) and in two Montague encodings, and the comparison's results (`Encodings/README.md`) |

**What it shares with the rest of the project.** Two things in `gf/`,
both used without editing them:
- the FraCaSLogic grammar, which `FraCaSEndToEnd.gf` extends with every
  construction only the pipeline needs (FraCaS's own wording: "who",
  "there are", ellipsis, gapping, the progressive, ...), each confirmed by
  one linearize check in `english_checks.py`. The parse grammar
  restricts that extension.
- `translate.py`, the tree-to-`Prop` translator. It reads each
  construction one way, the way the hand-written corpus's GF cross-check
  needs; `readings.py` plugs into its extension points (the `Readings`
  class, the relative pronouns, the name markers) and holds every reading
  the pipeline adds, including its translation of "there are NP".

CI snapshots every default translation of the corpus's trees
(`gf/default_translations.tsv`) and regenerates the cross-check theorems,
failing if either changes, so work here cannot silently change the
cross-check.

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
   check (`english_checks.py`). A later round added Section 4's VP
   ellipsis ("so did Bill", "Bill didn't", "the students have too"),
   one-anaphora ("a blue one", "owns one too") and uncontracted negation
   ("is not") the same way; readings that use anaphoric "one" as anything
   but the head of a noun phrase are discarded as ill-formed. The
   ellipsis round added gapping ("John went to Paris by car, and Bill by
   train"), fragments ("On Friday.", "And to Sue.", "But only one
   woman."), VP ellipsis with a new adverbial ("And Bill did at five
   o'clock"), "S, and S", "if S, then S", "is going to" as an elided
   auxiliary, and "said S" without "that"; readings that put a fragment
   anywhere but at sentence level are discarded.
3. **Rank** the readings generically (`EndToEnd/parse_rank.py`): fewest nodes,
   ties broken by right association (attach adverbials as low as
   possible).
4. **Resolve** ellipsis and one-anaphora by copying the antecedent
   clause's verb phrase or noun (the standard copy treatment; "a blue
   one" after "a red car" contrasts with the antecedent's outermost
   adjective). A coordinated premise asserts each conjunct in turn; a
   gapped clause or fragment copies the antecedent clause with each
   remnant replacing its parallel adverbial (the same preposition, or a
   time adverbial of the same kind) or added to it ("John went to Paris
   by car, and Bill to Berlin": Bill went to Berlin by car). Ellipsis
   whose antecedent embeds another verb phrase ("John said Mary wrote a
   report, and Bill did too": Bill said so, or John said Bill wrote one)
   is ambiguous and left untranslated. Time adverbials the parser
   attached to a noun phrase ("won [the contract in 1993]") are moved to
   the verb phrase. Then **translate** with `gf/translate.py` and **assemble**
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
   is the same as in final position. An attitude report with a named
   complement subject ("Bill said Peter wrote a report") is a relation
   named after the verb and the complement's verb phrase, voice included
   (`sayWriteReport bill peter`), so "said", "believed" and "knew" never
   share a predicate; a factive ("knew that S") also asserts S. Object
   "it" in a premise, after a sentence with a quantified subject ("each
   department has a dedicated line"), is read as "a [dedicated line]",
   which only weakens the premise.
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
   antonym converses), plus three adjective classes: intersective ("a
   four-legged animal" is four-legged and an animal), privative ("a
   former student" is not a student), and dimensional (a threshold set by
   the comparison class's members, a comparative independent of the
   noun, and contraries ordered within one class); every other adjective
   ("competent", "clever") is plainly subsective and licenses nothing
   beyond the noun. It also relates time adverbials on the same verb
   phrase ("for two years" ⇒ "for a year"; a state "from 1988 to 1992"
   ⇒ "in 1990"; "in July 1994" ⇒ "in 1994"; "every month" in 1994 ⇒ "in
   July 1994"; "for two years" excludes "for exactly a year"; one
   culminating event on one object per year), deletes a durative and the
   progressive only from a verb phrase that does not culminate, has a
   creation verb's object not exist before the event and "finish NP"
   finish the one event the problem mentions on it, deletes "a lot of"
   and a PP on a non-quantified object,
   weakens the complements of "can", "must" and "used to", and makes "as
   fast as" exclude "slower than". Nothing in it is keyed by problem or gold answer,
   but the lists were written with this corpus in view, so it is not a
   held-out resource.

The `build-gf` CI job regenerates the claims file from the English and
fails if it differs from the committed copy, so the scored claims are
reproducible.

**Parser quality, on the CI-confirmed sentences**
(`EndToEnd/parse_eval.py`, which grows as each round adds its
confirmation checks): all parse; the hand-built tree is among the
readings for all; median 4 readings (max 3,600); and the top-ranked
reading translates to the same `Prop` as the hand tree for all but one
of the sentences `translate.py` covers (405 of 406 after the
progressive round). The one exception (136) is a garden-path
compound ("[executive that had a laptop] computer") tied in size with the
correct reading. The right-association tie-breaker was added after
inspecting misses of the size rule alone on these same sentences, so this
is not a held-out figure.

**Coverage, on FraCaS's original English**: 259 of 342 problems go all
the way through (75.7%). 65 stop at a sentence the restricted grammar
doesn't parse, 16 at a reading the translation doesn't cover, 1 (104) at
a predicate named after a Lean keyword (`have`), and 1 (119) at the name
check (below): "used her workstation" and "used a workstation" would both
be `useWorkstation`. The remaining parse failures are
mostly hard phenomena rather than missing glue: tense and aspect
(Section 7), embedded questions, antecedent-contained and parallel-scope
ellipsis (Section 4's 163, 171-173, 191-196), cross-sentence anaphora,
and numbers written as digits. The last cheap round
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

**Result** (CI run 38523449354, every proof checked by the kernel), on
those 259 problems:

| | matched | wrong answers |
|---|---|---|
| always "unknown" (baseline) | 90/259 (34.7%) | — |
| as translated | **179/259 (69.1%)** | **0** |
| with background knowledge | **238/259 (91.9%)** | **0** |

(Before the name check the pipeline also reached 119, answered
"unknown" against gold "no"; no other verdict changed.)

Counting the 83 problems the pipeline cannot yet reach as "unknown",
corpus-wide that is 195/342 (57.0%) as translated and 254/342 (74.3%)
with background knowledge, against a 31.0% baseline ("unknown" also
counts as matching FraCaS's "undef").

**The kernel check.** Until CI run 38523449354 the prover accepted a
claim when a tactic left no goal open, without giving the proof to
Lean's kernel. Every proof is now kernel-checked before it counts
(`Prover.lean`'s `runTacticChecked`): it must contain no `sorry` or
metavariable, the kernel must accept it as a theorem of the claim, and
it may use no axiom beyond `propext`, `Classical.choice` and
`Quot.sound`. The check rejected the proofs of two answers, 9 ("Several
great tenors are British" ⇒ "There are great tenors who are British")
and 11 ("A few great tenors sing popular music" ⇒ ...), both correct
"yes" answers: the earlier figures, 181/259 and 240/259 (CI run
38176812855), counted them. The cause is `exist_nl`
(`Section1/Monotonicity/Existential.lean`): it proves that a count is
positive with `mkDecideProof`, which builds `of_decide_eq_true rfl`
without evaluating `decide`. For a numeral the term is correct; for a
count that is a variable, as "several" and "a few" are here, it is
ill-typed, and only the kernel notices. No other verdict changed, and
no answer became wrong.

**Anaphora** (CI run 38087617550) reached 114-120, matched 114-118 in
both variants and 120 with background knowledge, matched 131 and 133
(reached before), and lost nothing. A possessive bound to the subject
("every student used her workstation") is a function of its possessor,
`workstationOf x` - the first projection of the dependent pair reading
Π x : student. Σ w : workstation. has x w that dependent type semantics
gives possessives and donkey sentences (Ranta 1994; Bekki 2014), and
that `LeanNLSemantics/MTT/DependentAnaphora.lean` on the
`mtt-intensional-adjectives` branch states with Σ itself. Its
presuppositions are premises for every possessor and project out of the
hypothesis. A pronoun after "NAME V-ed a/several N" is the E-type
description of its antecedent (Evans; Cooper; Heim): "GFI owns several
computers. ITEL maintains them" is "ITEL maintains all the computers
that GFI owns" (133, maximality), and "Smith attended a meeting. She
chaired it" is "Smith chaired the meeting that Smith attended" (120).
Still "unknown": 119 ("no student used her workstation" ⇒ not "Mary
used a workstation", gold no) does not follow - she may have used
someone else's; 124-126 would need the exactly-two reading of "two
machines" settled; 129 and 130 are the same problem with opposite gold
answers; and 127, 128, 134-138 need plural or donkey anaphora over
conjunctions and relative clauses. Before this round, CI run
38041260727 gave 160/229 and 203/229.

A follow-up (CI run 38089191811) matched 128, 130 and 138, reached 129,
and lost nothing. **Bridging**: "every report has a cover page" makes
each report's cover page a function of the report, stated as such
(`coverPageOf`) when a later definite depends on it; "the cover page of
R-95-103" is then `coverPageOf r95103`, and in a premise a bare "the
cover page" is the cover page of the one report the discourse names
(138). **Plural "they" after a coordination**: "John and his colleagues
went to a meeting. They hated it" - "they" may be all of them or just
the colleagues, so only what holds on both is used: the colleagues
hated the meeting (128). Whether John did depends on that reading, and
FraCaS's 129 (yes) and 130 (unknown) are the same problem with both
answers; the pipeline says "unknown" to both. 134/135 (donkey
sentences) are not attempted: "MFI has a service contract for all its
computers" needs "its" read as ownership and a uniqueness argument from
"exactly one computer", and 135 holds only on the strong donkey reading.
Before, CI run 38087617550 gave 166/237 and 211/237.

**Diagnosing reached problems** (CI runs 38093927327 and 38100351678)
took the reached problems answered "unknown" against a yes/no label one
by one. Matched with background knowledge: 46, 258, 279, 282, 307 and
326.
- **Discourse referents.** "Smith wrote a novel in 1991 ⊢ Smith wrote
  it in 1992": when the hypothesis's object "it" has exactly one
  possible antecedent, a premise's "NAME V-ed a CN", the indefinite
  introduces a referent (`theNovel`) that "it" names. This is dynamic
  entailment (Kamp; Groenendijk and Stokhof); the claim's universal
  binding makes the premise exactly as strong as before. The
  one-time-per-event rule then gives "no" (279, 282).
- **A silent bug, now refused.** That diagnosis found that an object
  pronoun nothing resolves dropped out of the predicate's name ("Smith
  wrote it" was named like "Smith wrote"). An unresolved object pronoun
  is now refused instead. Of the reached problems this affected only
  279/282 and the donkey pronoun of 134/135 ("has a service contract for
  it"). 134/135 are therefore no longer reached; they were "unknown"
  before, on a translation that had lost the pronoun.
- **Background knowledge.** "Every month" within a year gives each month
  of it (307). A creation verb's object did not exist before the event
  (258). "Finish NP" is the one other kind of event the problem mentions
  on that same thing, finished when it culminates: "ITEL built MTALK" ⇒
  "ITEL finished MTALK" (326; logical metonymy, Pustejovsky 1995).
- **Prover.** A positive count is refuted on its exact reading too (46).
- **Presupposition.** That change at first also proved 78's "no" (gold
  undefined). "One of the female commissioners spends a lot of time at
  home" is vacuously untrue when there are no female commissioners, but
  it is not false then: "the female commissioners" presupposes them. A
  hypothesis's partitive now records that presupposition, and a "no"
  claim must establish it as well as the negation (Strawson). 78 and 62
  stay "unknown"; 46 still follows, since "neither commissioner"
  presupposes two.
- **Left "unknown".** 140 ("John said Bill had hurt himself" ⇒ "John
  said Bill had been hurt") would need what is said to be closed under
  entailment, which saying is not. The step inside the report, from
  "hurt himself" to "been hurt", would be fine on its own.

That run gave 173/250 and 230/250, with no wrong answers.

**Progressive and other constructions** (CI run 38101249418) reached
141, 153, 273, 274, 281, 294, 296, 299, 327, 329 and 343, matched all of
them, and lost 308.
- **The progressive** ("was writing a report") is marked in predicate
  names (`progWriteReport`), so it is never the simple past. Background
  knowledge gives "was running his own business" ⇒ "ran his own
  business" (294) only for a VP that does not culminate. "Was building
  MTALK" need not have built it, and "was winning the contract" need not
  have won it (327, 329, gold unknown: the imperfective paradox).
- **Gapping** now copies into a progressive: "John is going to Paris by
  car, and the students by train" (153).
- **Durations.** "For two years" excludes "for exactly a year" (299).
- **Perception** is transparent in its agent, so "Smith saw Jones sign
  the contract" and "Jones is the chairman of ITEL" give "Smith saw the
  chairman of ITEL sign the contract" (343).
- **Attitudes.** "Someone said ..." is an attitude report (141, gold
  unknown).
- **Ranking.** A reading with a noun phrase that has no words (the bare
  plural indefinite article) is not a reading of the sentence. A parse
  category whose parses are all of that kind no longer hides the next
  one: "Bill is going to." keeps its elliptical reading. 308 is no longer
  reached because every parse of its hypothesis ("There is a
  representative that Smith wrote to every week") had such an empty noun
  phrase; it was reached before only through one. `parse_eval.py` uses
  the same category choice.

Before, CI run 38100351678 gave 173/250 and 230/250.

**Tense and aspect** (CI run 38091759266) reached 251-257, 301, 302 and
311-313, matched 251, 252, 301, 302, 311, 312 and 313 with background
knowledge (251 also as translated) and 253, 254 and 256 (gold unknown),
and lost nothing. "Currently" adds nothing to a translation that reads
the present tense as the present (251). "It is now 1996" makes the
perfect's "since 1992" a span up to 1996, and a *state* that has held
since then held in 1993 (252); for any other verb phrase the perfect
says only that the event happened at some time since, so "ITEL has
expanded since 1992" says nothing about 1993 (254, gold unknown). 255
("Since 1992 ITEL has made a loss", gold yes) and 257 (the same as 256,
gold unknown, but labelled yes) would need the fronted "since" to force
the continuous reading on a non-state; they stay "unknown". "Ran his own
business for two years" gives "for a year" and, since running a
business does not culminate, "ran his own business" (301, 302). A
separate "Then S." puts S's event after the previous premise's, which
the event-time encoding of "before"/"after" then orders (311). "Always"
and "never" quantify over occasions: "ITEL always delivers reports late"
and "ITEL delivered reports in 1993" give "delivered reports late in
1993", and "never" excludes it (312, 313); the end-to-end namer now keeps
the adverb in the predicate's name, which `translate.py`'s default namer
drops (so its default mode still names "never delivers reports late"
like "delivers reports late" - not a problem for the hand-written
cross-check, which never uses either). Section 7's remaining parse
failures are calendar arithmetic (259, 260, 284, 314), "spent N hours
V-ing" (285-291), and the long multi-clause problems 315-325. Before,
CI run 38089191811 gave 169/240 and 214/240.

**Ellipsis** (CI run 38041260727) reached 145, 146, 154, 164-167, 178
and 179 and matched all of them, matched 150-152 (reached before, but
parsed into one fused predicate), and lost nothing. 140 is newly
reached and "unknown": "John said Bill had hurt himself" ⇒ "John said
Bill had been hurt" needs reflexive-to-passive inside a report, and the
two reports are kept distinct. Left untranslated on purpose: 175, 176
and 180, whose ellipsis has two antecedents (above), and 169/170 ("John
found Mary before Bill"), where FraCaS reads the same sentence both ways.
The strict/sloppy problems (182-190: "Smith represents his company and
so does Jones" ⇒ both "Jones' company" and "Smith's company", gold yes)
would also need committing to one reading; they do not parse yet.
Before this round, CI run 38040036163 gave 148/219 and 191/219.

**Fixing reached problems** (CI run 38040036163) took 15 problems the
pipeline already reached from "unknown" to gold, losing none: 105 and
106 (the prover now uses that a nonzero exact count refutes "no"); 298,
300, 303, 306, 328, 330 and 278 (time adverbials, step 6); 25, 29, 31 and
48 (weakenings, step 6); 229 ("as fast as"); and 132 (object "it").
Of the problems still "unknown" against a yes/no gold label, most are
FraCaS picking one reading of ambiguous English (13, 76, 86, 87, 100,
107, 109, 160, 230, 233, 239, 250); 69 is a slip in FraCaS itself (its
premise says "can travel freely", its hypothesis asks about "the right
to live"); and the rest need anaphora with identity (133-135, 138, 279,
282), calendar or lexical knowledge (258, 307, 326), or adjective
knowledge the lexicon deliberately lacks (199, 218). Before this round,
CI run 38036552953 gave 146/219 and 176/219.

**Adjectives and attitudes** (CI run 38036552953) gained 198, 202, 203,
208, 209, 212, 214 and 216 with background knowledge, and 334 and 336 in
both variants, and lost nothing. Background knowledge now sorts
adjectives into the classes of Kamp & Partee (1995) (step 6): 216's
"a fatter politician than Bill" ⇒ "fatter than Bill" follows for a
dimensional adjective like "fat" and not for "clever" (217, still
correctly unknown), and 214's "all fat legal authorities are fat law
lecturers" follows from the two nouns having the same members, which
does not carry over to "competent" (215, still correctly unknown).
Readings now commit to the complement of a factive ("Smith knew that
S" ⇒ S, 334) and of a positive implicative ("ITEL managed to win" ⇒
ITEL won, 336), and not of "believe" or "try" (335, 337, correctly
unknown). Left as they are: 199 ("a successful former university
student" ⇒ "successful") would need "successful" to be intersective,
which it is not in general (successful as what?), and 218 ("a clever
person" ⇒ "clever") needs a default comparison class. The adjective
lists were written with Section 5 in view, so this round's gains are
development-set gains like every other. Before this round, CI run
38028878624 gave 144/219 and 166/219.

**Temporal order** (CI run 38028878624) gained 261, 262, 264-268 and
270 and lost nothing: "Smith left before/after Jones left" now places
each named individual's culminating event at one time (`leaveTime :
A → ℕ`). "After" is factive in its clause and "before" is not (275,
"left the meeting before he lost his temper", stays unknown). Only
between two culminating (telic) events, judged by the standard telicity
tests: for states and activities ("was present", "swam") "before" and
"after" are not converses, and FraCaS's gold answers differ exactly
there (264/270 yes vs 269/272 unknown, same logical shape), so those
keep an opaque translation and stay correctly unknown. A first version
assumed every event has one time regardless of aspect; checking the
whole group before building it showed that would have answered 269 and
272 wrongly. Before this round, CI run 37240689801 gave 136/219 and
158/219.

The cheap-construction round (CI run 37240689801) lost no previously
matched problem and gained 84, 89, 93, 217 and 342; 216 ("John is a
fatter politician than Bill" ⇒ "John is fatter than Bill", gold yes) is
"unknown" by design, since "fatter as a politician" coincides with
"fatter" only for some adjectives (not "clever", 217), which the
pipeline then had no lexicon for (it does now, see above). Before that, CI run 37205860267 gave
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

How the remaining "unknown"s split: see "Fixing reached problems"
above.

One background-knowledge rule *was* unsound and has been fixed, a fix
found from its observed failure: the first version deleted durative
"for two hours" like any other modifier, so "Smith wrote a report for
two hours" ⇒ "Smith wrote a report" (304, gold unknown — an
accomplishment need not culminate). Durative "for"-phrases were then
made non-deletable everywhere, which also lost 306 ("discovered new
species for two years" ⇒ "discovered new species", gold yes, valid for
an iterated achievement). They now delete only from a verb phrase that
does not culminate, by the same telicity test `readings.py` uses for
"before"/"after": 304 stays unknown and 306 is matched again.

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

## The name check

Every fused name is a free variable of its claim, bound universally, so
a name that leaves a word out of its phrase is harmless by itself:
`throwBall` may as well mean "did not throw balls" if nothing else is
said about it. It is wrong when the same name is also the name of a
different phrase, because whatever holds of one is then applied to the
other. That one mechanism is behind every wrong answer the pipeline has
given from naming: "spend a lot of time" and "spend time" (FraCaS 30,
32, 47, before determiners were kept in names), and, on the held-out
test, "said he didn't drink black coffee" named like the "drink black
coffee" inside it (MED 2718, `HeldOut/README.md`).

`names.py` refuses a problem when a name its claims use is the name of
two of its phrases that differ in what the name leaves out. What a name
may leave out without that counting is a short explicit list, each entry
with its reason (articles and number, tense, positive polarity, relative
pronouns, a floated "all"); a negation, a verb taking a clause, an
adverb, a pronoun or a conjunction counts. It reads the naming code in
use, so it also guards any later change to it.

It compares the phrases of the sentences and also the phrases
background knowledge states facts about without their being in any
sentence (a weakening; the event "finish" stands for). A construction
with no word of its own counts as left out when its mark is missing
from a name: the progressive, which names mark, and the passive, which
they do not, so "(be) impressed" and "impress" never pass as one phrase
(no FraCaS or MED result changes).

On FraCaS it refuses one problem, 119, which was "unknown" before; no
verdict changes. The ablations below show what it covers: with
determiners, numerals and the progressive's mark dropped from names, it
refuses all 13 problems whose names collide instead of answering any of
them wrongly. It covers naming only: a false background fact (the
telicity ablation) still gives wrong answers.

## Soundness ablations

Which of the pipeline's safeguards prevent wrong answers? Each ablation
switches one off and re-scores (`ablations.py`, `AblationScan.lean`,
`ablation_report.py`; CI run 38523449354, with the name check and the
kernel check in place). The reading-rule rows reuse the baseline's claims, scored one
reading at a time. The others regenerate the claims with one safeguard
patched out, and score the problems whose claims change. Recomputing
the every-reading rule from the per-claim results reproduces the main
scan exactly (179 and 238), so the two scans agree.

| switched off | as translated: matched | wrong | with background knowledge: matched | wrong | wrong answers it lets through |
|---|---|---|---|---|---|
| nothing (the pipeline) | 179/259 | 0 | 238/259 | 0 | |
| every reading → weak readings only | 180/259 | 1 | 239/259 | 2 | 56, 109 |
| every reading → strong readings only | 179/259 | 4 | 238/259 | 4 | 91, 94, 95, 107 |
| every reading → any reading (FraCoq's rule) | 178/259 | 5 | 237/259 | 6 | 56, 91, 94, 95, 107, 109 |
| presupposition in "no" claims | 179/259 | 0 | 237/259 | 1 | 78 |
| determiners, numerals and the progressive in names | 177/259 | 0 | 232/259 | 0 | |
| telicity | 179/259 | 0 | 232/259 | 2 | 304, 329 |
| non-subsective/non-veridical exclusions | 179/259 | 0 | 236/259 | 2 | 198, 201 |
| parse-ranking filters | 171/262 | 0 | 228/262 | 0 | |
| unresolved-pronoun guard | 179/259 | 0 | 238/259 | 0 | |
| the name check | 179/260 | 0 | 238/260 | 0 | |

What this shows:
- **Committing to one reading buys almost nothing and costs wrong
  answers.** The weak readings alone match one more problem and answer
  one or two wrongly; the strong readings alone match none more and
  answer four wrongly; "yes if any reading proves it" answers five or six
  wrongly (counting two contradictions). The every-reading rule's price
  is one problem.
- **Each semantic safeguard prevents specific wrong answers:**
  - the imperfective paradox (telicity): 2;
  - non-subsective adjectives and non-veridical adverbs: 2;
  - the presupposition in "no" claims: 1.
- **The name check subsumes two safeguards.** Before it, dropping
  determiners, numerals and the progressive's mark from names gave 3
  wrong answers as translated and 5 with background knowledge (30, 32,
  47, 327, 329); with it, all 13 problems whose names collide are
  refused (30-32, 46-48, 90, 153, 273, 274, 294, 327, 329), and none is
  answered wrongly. Without the unresolved-pronoun guard, it refuses 134
  and 135 itself.
- **The name check alone prevents nothing on FraCaS**: switched off, it
  lets 119 through again, still "unknown". Its effect shows when another
  safeguard is gone (above) and on held-out data (MED 2718).
- **The parse-ranking filters** change accuracy (10 matches), not
  soundness.

Caveat: every one of these safeguards, the name check included, was
added after the pipeline gave one of these wrong answers, on these same
problems or (the name check) on the held-out test. So the table shows
what each safeguard does on FraCaS. It does not show that it would be
needed, or enough, on unseen problems.

## Comparison with systems that parse FraCaS's English

The like-for-like comparison is with systems that, like this pipeline,
parse FraCaS's English automatically and prove automatically.
**ccg2lambda** (Mineshima, Martínez-Gómez, Miyao & Bekki, EMNLP 2015)
uses the C&C CCG parser and Coq "fully automated" with a 30-second
timeout, on FraCaS sections 1, 2, 5, 6, 8 and 9, "excluding seven
problems that lack a well-defined answer": exactly this project's `undef`
problems there (12, 16, 61, 62, 77, 78, 213), so the same 181 problems and
the same labels. With CI run 38523449354's kernel-checked verdicts
(`compare_fracoq.py`):

| section (problems) | this pipeline, as translated | with background knowledge | ccg2lambda |
|---|---|---|---|
| quantifiers (74) | .73 | **.93** | .77 |
| plurals (33) | .70 | **.70** | .67 |
| adjectives (22) | .32 | **.91** | .68 |
| comparatives (31) | .48 | **.65** | .48 |
| verbs (8) | .50 | **.88** | .62 |
| attitudes (13) | .77 | .77 | .77 |
| **total (181)** | **.624** | **.823** | **.69** |

No wrong answers in either variant. Haruta, Mineshima & Bekki (ACL SRW
2020), ccg2lambda's successor for these phenomena (two CCG parsers,
Vampire), report quantifiers .92, adjectives .86, comparatives .77 (.95,
.95, .84 with hand-coded tagging rules, two of them for FraCaS 214/215).

What these numbers do and do not show:

- **The grammar is the largest difference.** ccg2lambda parses with a
  general statistical parser trained on newswire (CCGbank) and a lexicon
  its authors describe as "not specific with respect to the FraCaS test
  suite". This pipeline parses with a grammar restricted to the functions
  and words of FraCaS-derived trees (step 2 above): a controlled language
  for FraCaS. Its parses are more reliable on FraCaS and it parses almost
  nothing else.
- **Both are development-set figures.** ccg2lambda's authors say the same
  of theirs ("do not constitute an evaluation on real texts nor on unseen
  test data"). Haruta et al. add held-out sets (MED, 498 monotonicity
  problems: .84; CAD, 105 comparatives: .77), which is the evaluation this
  pipeline cannot yet attempt: its grammar would not parse them.
- **Background knowledge is comparable in kind.** ccg2lambda takes
  antonymy from WordNet; this pipeline's `background.py` derives
  entailments from the parse trees and a small degree lexicon, written with
  FraCaS in view.
- **Wrong answers are not reported** for ccg2lambda. LangPro (Abzianidze,
  EMNLP 2015) reports precision, about 98%, but on SICK, not FraCaS; its
  FraCaS figures in other papers' tables come from a later paper of
  Abzianidze's, not compared here.

## Comparison with FraCoq

FraCoq (Bernardy & Chatzikyriakidis: IWCS 2017, 0.83 on five sections;
NoDaLiDa 2019, 0.89 on all but section 7; IWCS 2021, 0.81 on all
sections) is the strongest published logic-based FraCaS system. Its
setting differs from this pipeline's in three ways, each stated in its
papers:

- **Input.** FraCoq "skip[s] the parsing phase and use[s] the parse trees
  constructed by Ljunglöf and Siverbo (2011)": one tree per sentence from
  a treebank, with ellipsis marked explicitly in the trees. This pipeline
  parses FraCaS's English and ranks the readings automatically.
- **Proofs.** FraCoq's proofs were not automated in 2017, and in 2021
  "the construction of such proofs has demanded human intervention"; an
  "unknown" there means no proof was found with reasonable effort. Here a
  fixed prover runs unattended, and "unknown" means it failed.
- **Labels.** FraCoq scores an amended FraCaS (its `AnswerTypes.hs`): six
  labels overruled, ambiguous problems counted "yes" if *one* reading
  entails the hypothesis, and problems without a plain label dropped. This
  pipeline uses the original labels and answers "yes" only if *every*
  reading entails it.

The papers themselves warn against reading the number alone: "(At the
limit, one can construct a tool with 100% success rate by simply using a
lookup table.)" (2017); "the value of the present work lies not in the bare
accuracy numbers which we are able to achieve, but in the details of how we
do so" (2021).

`compare_fracoq.py` aligns problems and labels: it reads FraCoq's labels
from a FraCoq checkout (master, commit 3d86cc1, which reproduces the 2019
paper's 259 problems exactly) and scores this pipeline's verdicts by
FraCoq's own rules (only clearly labelled problems; an `Undef` label
accepts any answer). With the kernel-checked verdicts of CI run
38523449354:

| FraCoq problem set | problems | this pipeline, as translated | with background knowledge | FraCoq (paper) |
|---|---|---|---|---|
| 2017: sections 1, 2, 5, 6, 9 | 171 | 62.0% | 80.7% | 0.83 (on 174) |
| 2019: all but section 7 | 259 | 58.7% | 73.4% | 0.89 |
| 2021: all sections | 326 | 55.5% | 73.3% | 0.81 (on 329) |

On the 2017 sections, per section with background knowledge: quantifiers
68/74 (FraCoq .96), plurals 22/33 (.76), adjectives 19/20 (.95),
comparatives 19/31 (.56), attitudes 10/13 (.85). Under FraCoq's labels one
answer counts as wrong: 5, whose label FraCoq overrules from yes to
unknown ("missing hypothesis: there are italian tenors"); under the
original labels it is correct. The 2017 subset comes out at 171 problems
rather than 174 with the current label file, which has since marked
further problems (such as 199) as unclear.

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
  corpus and is still below FraCoq's reported 83%/81% on what it
  does reach. Its distinguishing property is that it gives no wrong
  answers on what it reaches, with every verdict machine-checked. That
  property is measured on the development set only. On held-out
  problems (MED, `HeldOut/README.md`) it gives 3 wrong answers in 140
  decided. One is a real translation error: a fused name that silently
  drops a verb taking a clause, and that verb's negated complement, so
  that it names the phrase inside it too. The name check now refuses
  every problem where a name would stand for two phrases (28 of the 989
  on MED, 1 on FraCaS); it was added after the held-out test, so its
  MED figures are post-hoc. The pipeline with it was then tested on
  SICK's test split, pre-registered (`HeldOut/SICK/README.md`): 1,416 of
  4,906 pairs reached, 52 answered, none wrong; recall 2.5%. With every
  proof kernel-checked (CI run 38523449354), 51 answers, none wrong;
  recall 2.4%.
