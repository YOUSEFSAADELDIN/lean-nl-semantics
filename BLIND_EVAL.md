# Blind evaluation: methodology, current coverage, and limitations

This records what "blind evaluation" actually tests in this project, the
exact current coverage and result (CI-confirmed, not estimated), what it
deliberately excludes and why, and how the resulting number does and does
not compare to prior published FraCaS accuracy figures (e.g. FraCoq's
83%/81%). It exists as its own document rather than another paragraph in
`README.md` because the real content here is the reasoning and the exact
breakdown, not just a headline number — the number alone, without this,
invites exactly the "comparable to FraCoq?" question this document
answers directly.

## The concern this addresses

Every one of the 342 formalized FraCaS problems in this corpus is proved
by a human who already knew, from FraCaS's own gold answer, which
direction to prove: `theorem fracas_002 : Every P Q → Some P R → Some P Q
:= every_some ...` bakes in a decision no automated procedure made. The
338/342 "self-consistency" figure this project otherwise reports is a
check that each hand-written proof's *shape* matches its recorded gold
answer — a manual audit, not a blind prediction. It says the
formalizations are internally consistent, not that an automated system
correctly inferred each one's answer from the premises and hypothesis
alone.

Blind evaluation is the attempt to close that specific gap: take a
problem's translated premises/hypothesis (the `Prop` the human wrote,
unavoidably a translation choice, same as any NLI system's parsing step)
and let fixed, general-purpose tactics — not the human's proof — decide
which direction holds, then compare that automated decision against gold.

## Methodology

### Bare theorems (`BlindEval.lean`, `BlindEvalSections3to9.lean`)

For every `fracas_NNN` theorem (no suffix — see "What's still excluded"
below for what a suffix excludes), whatever the shape of its conclusion:

1. Take the theorem's own type only, never its proof term.
2. Attempt to close "premises → hypothesis" and, separately, "premises →
   ¬hypothesis", via the identical fixed tactic chain both times
   (`attemptClose` in `BlindEvalCore.lean`): this corpus's certified
   monotonicity fragment (`mono_nl`, `exist_nl`, `mono_nl_compose` — see
   `Tactic.lean`/`Existential.lean`/`Compose.lean`), two small targeted
   searches for `Most`-headed goals (`most_nl`, `every_most_nl`), an
   `aesop` call that unfolds `Every`/`Some`/`No` and is armed with every
   general (not problem-specific) `GQ.lean`/`Plurals.lean` lemma
   (`blind_aesop`) plus an unarmed fallback, `grind` with and without
   those unfoldings, and `intros; omega` last (Section 6's cardinal
   comparatives are literal `Nat` inequalities). Which of the two queries
   is the hypothesis and which its negation is decided polarity-aware
   (`flipConclusion`/`isNegHead`): many bare theorems state a `.no` answer
   by writing `¬hypothesis` or `a ≠ b` as the literal conclusion, and
   naively wrapping a second `¬` around that asks a different question.
3. (hypothesis closes, negation fails) → **yes**; the reverse → **no**;
   neither → **unknown**; both → a flagged **contradiction**, never
   silently folded into yes or no.
4. Compare against FraCaS's own gold `Answer`, collapsing `.unknown` and
   `.undef` both onto automated `"unknown"` (a binary yes/no/unknown
   procedure has no way to tell "genuinely undecided" apart from "the
   source's answer wasn't a literal yes/no/don't-know").

Both files call the same `runBlindEvalGeneric`. An earlier Sections 1–2
version only attempted theorems whose conclusion was headed by a
generalized quantifier (`Every`/`Some`/`Most`/...), skipping 20; that
restriction turned out not to be load-bearing and has been dropped.

**The `aesop` step silently never ran until this round — stated plainly
because it changes what earlier published numbers meant.** It was
written with `unfold FraCaS.Section1.Every` and no phase; Aesop requires
`norm unfold`, so every invocation failed while building its rule set,
before searching at all (`phase (safe/unsafe/norm) not specified.`, found
by a temporary per-tactic diagnostic in CI run 37168342088). Since a
failed attempt and an erroring one look identical to the scan, this was
invisible: every blind-evaluation result published before the fix came
from the chain's other steps alone. `BlindEvalCore.lean` now defines the
call as a `blind_aesop` macro followed by `example`s it must prove, so a
broken rule set fails `lake build` instead of quietly failing every goal.
Turning `aesop` on also surfaced a resource issue: the scans' heartbeat
budget was shared across a whole section, so a working search eventually
exhausted it and aborted the rest of the section; each attempt and each
bookkeeping step now runs in its own budget, and a budget failure is
reported as "errored", never as a verdict.

### Countermodel-pair `.unknown`/`.undef` problems (`BlindEvalUnknownScan.lean`, `BlindEvalUnknown3to9Scan.lean`)

Every genuine `.unknown`/`.undef` problem in this corpus is represented
not as a single theorem but as a `_dir1`/`_dir2` pair: two concrete
models (over `Bool`, `Fin n`) jointly witnessing that neither direction
is a validity. That pair has no single entailment-shaped `Prop` the
procedure above could even pose a yes/no question about, so the bare-
theorem scans skip every one of them by construction.

The fix is not to force them into that shape but to recognize what a
genuine independence claim actually is: by construction, not a valid
universal statement in either direction, so there is no theorem to write
down and prove — and no proof burden to invent one. Each of the 46
`.unknown`/`.undef` problems in Sections 1–2 (and, by the same method,
all 60 in Sections 3–9) instead gets a bare, deliberately **unprovable**
`Prop`-valued `def` (`BlindEvalUnknown.lean`/`BlindEvalUnknown3to9.lean`,
generated by `scripts/gen_blind_eval_unknown.py`/`gen_blind_eval_unknown_
3to9.py`): the generic, schematic form of exactly what that problem's
own, already-proved `dir1`/`dir2` pair demonstrates concretely, with the
quantifier structure put inside the `Prop` itself (`∀ {A}[Fintype A]
(P Q)[...], AtMost 2 P Q → Some P Q`, for instance) so the existing
`attemptClose`/`negateConclusion`/`introAll` machinery can consume it
exactly like a bare theorem's type, with no new extraction logic. Each
generic claim is a mechanical generalization of its own dir1/dir2 pair —
every concrete predicate or individual promoted to a free schematic
variable, the same variable reused wherever the identical concrete term
recurs across both models — not a fresh translation from the English,
though cross-checked against the English directly wherever position-
sharing alone was ambiguous or no doc comment explained the intended
content (Sections 1–2 ids 28, 34–37, 42, 43, 65; Section 7's 271–274
among the Sections 3–9 set).

Sections 3–9 turned up one complication Sections 1–2 never did: 53 of
their 60 dir1/dir2 pairs turned out to be *vacuous* `True ∧ ¬False`/
`True ∧ True` stubs (the same bug class as Sections 1–2's own
fracas_91/94/95/102/104, just far more common, since ellipsis ambiguity
and tense/aspect independence are inherently "two unconnected facts"
phenomena). Every one was fixed in place — named, real content, reusing
sibling theorems' own vocabulary wherever it already existed in the file
— before being generalized the same mechanical way; see each theorem's
own doc comment in the corpus for the fix, and `BlindEvalUnknown3to9
.lean`'s own header for the one further wrinkle this surfaced: a few
state/achievement temporal-composition claims (263, 269, 271–274)
deliberately use opaque `Prop`s instead of real `Nat` timestamps, since
real `<`/`>` would make the composition trivially (and wrongly) provable
by plain transitivity, silently turning a genuine `.unknown` into a
false "yes".

The scan then runs the exact same `attemptClose`/`negateConclusion`
pipeline (factored into `BlindEvalCore.lean` so every scan shares it)
against each claim, in both directions, and the correct automated
outcome is **failure on both** — that failure, not a yes/no verdict, is
what a genuine independence claim should produce, and is compared
against the gold `.unknown`/`.undef` answer the same way the bare-
theorem scans' own `answerMatches` already does.

## Current result (CI-confirmed)

CI run 37170606363:

| | problems | attempted | matched |
|---|---|---|---|
| Bare yes/no, Sections 1–2 | 67 | 67 | 64/67 |
| `.unknown`/`.undef` pairs, Sections 1–2 | 46 | 46 | 46/46 |
| Bare yes/no, Sections 3–9 | 169 | 169 | 166/169 |
| `.unknown`/`.undef` pairs, Sections 3–9 | 60 | 60 | 60/60 |
| **Total** | **342** | **342** | **336/342 (98.2%)** |

Every problem in the corpus is now attempted. 0 contradictions, 0
errored attempts, 0 missing claims. For scale, answering "unknown" to
everything would score 106/342 (31.0%).

The 6 mismatches are all `(gold yes/no, automated unknown)` — the chain
fails to find a proof; it never finds a wrong one. Each needs something a
generic search over these lemmas doesn't do, and none has been patched
with a problem-shaped rule:

- **105, 106** (`Exactly 1 P Q → ¬ No P Q`): cardinality reasoning — a
  count of 1 implies a witness.
- **111, 127**: two *distinct* existential witnesses (`∃ c₁ c₂, c₁ ≠ c₂ ∧
  ...`).
- **123** (`Most R S → (∀x, S x → D x) → Some S D`): forward reasoning
  from `Most` to a witness, then chaining.
- **126**: `Fintype.card` arithmetic.

Repairing `aesop` is what closed the earlier gaps 129, 173, 246, 248 and
307 (`Every P Q → P x → Q x` and similar instantiations — plain `grind`
cannot see inside the `Every` definition), and dropping Sections 1–2's
shape restriction brought in 17 more correct verdicts among the 20
previously excluded problems.

(Exact CI output: the `blind_eval_section1` … `blind_eval_section9`,
`blind_eval_unknown` and `blind_eval_unknown_3to9` commands, run on
every push.)

## End-to-end: translating from FraCaS's English automatically (`BlindEvalParsedScan.lean`)

Every result above scores inference over a `Prop` a human wrote. This
scan removes the human from the translation step as well, for every
problem the automated pipeline can carry all the way through
(`scripts/gen_blind_eval_parsed.py`):

1. **English**: each premise and hypothesis exactly as FraCaS states it,
   normalized only mechanically (final period dropped; first letter
   lowercased if the sentence doesn't parse as written) — not the
   project's own confirmed rewordings in `gf/run_gf_tests.py`.
2. **Parse** with a restricted GF grammar (`gf/gen_parse_grammar.py`).
   Parsing with the full FraCaSLogic grammar is unusable — 69,115
   readings in five minutes for one Section 1 sentence, none free of junk
   constructions — so the parse grammar inherits only the functions and
   words the CI-confirmed trees use. That makes it a controlled-language
   grammar fit to FraCaS's vocabulary (the same kind of artifact FraCoq's
   FraCaS-specific grammar is); it does not tell the parser which tree
   goes with which sentence.
3. **Rank** the readings generically (`gf/parse_rank.py`): fewest nodes,
   ties broken by right association (attach adverbials as low as
   possible).
4. **Translate** the top reading with `gf/translate.py`, and **assemble**
   by one generic rule — bind every free predicate/individual, chain
   premises into the hypothesis — with no per-problem cases and no
   background-knowledge premise ever supplied.

The `build-gf` CI job regenerates the claims file from the English and
fails if it differs from the committed copy, so the scored claims are
reproducible.

**Parser quality, on the 437 distinct CI-confirmed sentences**
(`gf/parse_eval.py`): all 437 parse; the hand-built tree is among the
readings for all 437; median 4 readings (max 3,600); and the top-ranked
reading translates to the same `Prop` as the hand tree for 371 of the 373
sentences `translate.py` covers. The two exceptions are a genuine
ambiguity (13: bare plural "leading tenors that are excellent" — generic
or existential) and one remaining relative-clause attachment (136). The
right-association tie-breaker was added after inspecting misses of the
size rule alone on these same sentences, so this is not a held-out
figure.

**Coverage, on FraCaS's original English**: 111 of 342 problems go all
the way through. 188 stop at a sentence the restricted grammar doesn't
parse (FraCaS's hypotheses are often "There are X who…" existentials,
which no confirmed tree uses), 30 at a reading `translate.py` doesn't
cover, 13 at a translation needing non-generic assembly.

**Result: 48/111 (43.2%) — against an always-"unknown" baseline of
45/111 (40.5%) on the same problems.** End-to-end, the pipeline is barely
better than the trivial baseline, and that is the honest headline. 40 of
the 48 matches are "unknown" verdicts. The 63 mismatches break down as:

- **58 `(gold yes/no, automated unknown)`**, overwhelmingly missing
  knowledge the hand-written theorems supply as an explicit premise and
  this pipeline deliberately never does ("winning the Nobel prize for
  literature" ⇒ "winning a Nobel prize", 17; "small animal" vs "large
  animal" being contraries, 204/205) or comparatives flattened into
  unrelated unary predicates (220–229).
- **5 wrong "yes"** (30, 32, 47, 94, 228), all translation conflations:
  `translate.py` drops object determiners from predicate names, so
  "spend **a lot of** time at home" and "spend time at home" become the
  same predicate (30, 32, 47); it drops comparative morphology, so "**as**
  fast as" and "fast**er** than" coincide (228); and it reads "the
  inhabitants … voted" distributively, where FraCaS's "unknown" turns on
  the collective reading (94).

Some of the 8 "yes" matches are also right partly for the wrong reason
(31 and 48 involve the same determiner collision, in a direction where it
happens not to matter). Building this pipeline also found and fixed three
`translate.py` fidelity bugs that were silently conflating distinct
meanings: prepositions were dropped from predicate names (FraCaS 74's
"resident **in** Europe" vs "resident **outside** Europe" both became
`residentEurope`), GF word-sense tags leaked into names (`by8agent` vs
`by8means`), and a relative clause was translated differently depending
on whether a parse attached the article via `CompCN` or `CompNP`.

## What's still excluded, and why

Nothing in the hand-translated evaluation: all 342 problems are attempted.
Suffixed names (`_dir1`/`_dir2`, `_from_gf`, `_via_mono_nl`, ...) are
skipped by the bare-theorem scans by design — countermodel pairs are
evaluated through their generalized claims instead, and the rest are
re-derivations of problems already counted, not distinct problems.

## Comparison to FraCoq (83%/81%)

The 336/342 figure is a genuine blind-prediction score in one narrow
sense: the automated decision used only the translated `Prop`, never the
human's proof direction. It covers the whole corpus. But it is **not
comparable** to FraCoq's 83%/81%, because FraCoq's pipeline includes
automated translation from English and its score absorbs that step's
mistakes, while the 336/342 premises/hypotheses were translated by hand.
It isolates and scores the inference step only.

The end-to-end scan above is the comparable kind of measurement, and it
says the translation step is where nearly all of the difficulty lives:
48/111 (43.2%) on the problems the pipeline reaches at all, barely above
a 40.5% always-"unknown" baseline, covering only a third of the corpus.
Closing that gap is a translation problem — grammar coverage of FraCaS's
own hypothesis constructions, determiner- and comparative-preserving
translation, and some account of background knowledge — not an
inference problem.

## Other limitations worth stating plainly

- The tactic chain (`mono_nl`/`exist_nl`/`mono_nl_compose`/`most_nl`/
  `every_most_nl`/`aesop`/`grind`/`omega`) was built and iterated against
  this exact corpus. A high match rate on problems the chain was tuned
  against is a weaker claim than the same rate on a held-out set the
  chain never influenced — there is no such held-out set here, because
  there is only one FraCaS to evaluate against. This is a structural
  limitation of blind-evaluating a fixed, closed benchmark with a hand-
  built reasoner rather than a learned one; it does not mean the 336/342
  result is invalid, only that it should not be read as evidence the
  chain generalizes to sentences outside this corpus's vocabulary and
  structure.
- The same applies to the end-to-end pipeline: its parse grammar's
  vocabulary and constructions are read off this corpus's own confirmed
  trees, and its ranking tie-breaker was chosen after looking at its
  misses here.
- `aesop`'s lemma list in `attemptClose` is general (not problem-
  specific) `GQ.lean`/`Plurals.lean` content, but it is still a list
  curated by a human who had already seen the whole corpus — the same
  "self-serving?" concern the axiom audit (`MTT/AssumptionAudit.lean`)
  raises for axioms applies here in a milder form. The genuinely
  independent part of this evaluation is which *direction* closes, not
  whether some member of a hand-picked general lemma set exists at all.
- A `.yes`/`.no` match only confirms the tactic chain picked the
  direction FraCaS also picked; it does not independently confirm that
  direction is linguistically correct (the hand-proof already is that
  confirmation, via the separate 338/342 manual consistency audit in
  `README.md`).
- A 98.2% match is partly a statement about how much of each problem's
  difficulty the hand translation already absorbed (an explicit
  background-knowledge premise, a pre-resolved ellipsis, a literal `Nat`
  comparison). The end-to-end scan's 43.2% is the counterweight to read
  next to it.
