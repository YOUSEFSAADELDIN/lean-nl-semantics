# GF setup and debugging notes (Phase 3)

This records how the GF toolchain was actually gotten working, and every
real gotcha hit along the way, so the next round of grammar-writing
doesn't have to rediscover any of it. Everything through the first five
confirmed sentence shapes was originally done by hand on a separate
machine (Windows 11 via WSL2) and relayed back, because this project's
usual day-to-day development environment was originally believed to
have no viable path to a Haskell toolchain (`grammaticalframework.org`,
`get.haskellstack.org`, Hackage's mirror fallback domains all appeared
blocked) — see below for how that was diagnosed.

**That turned out to be wrong**: the real blocker was never a full
network block, just `cabal`'s own TUF secure-repo signature check
failing through this environment's egress proxy - fixed once and for
all by setting `~/.cabal/config`'s `hackage.haskell.org` repository to
`secure: False`. Once that was found, the entire toolchain (`gf-core`
via `cabal install` at the pinned commit below, `gf-rgl`'s `Setup.sh`
at the pinned tag below, plus `DictEngAbs.gf`/`DictEng.gf` compiled
separately the same way CI does it) builds and runs directly in this
same sandbox - no relay to a separate machine needed for any of the
work after that point. If a future development environment starts
from scratch, the same steps below (`cabal install` at the pinned
commit, `gf-rgl`'s `Setup.sh` at the pinned tag, the `secure: False`
fix above) reproduce it; nothing here depends on a specific tool or
session mechanism to rebuild it automatically.

**GitHub Actions CI is a still separate, still-necessary check**: its
runners have normal, unrestricted internet access, so
`.github/workflows/build.yml`'s `build-gf` job builds the same pinned
toolchain from source (independently of whatever's cached in this
sandbox) and runs `gf/run_gf_tests.py`'s automated `linearize` checks
on every push. All 342 FraCaS problems' worth of sentence shapes across
all nine FraCaS sections (803 `linearize` checks in total, as the suite
has grown since this note was first written) are built and validated
against the local toolchain described above before ever being pushed.
This has been proven green on real GitHub Actions across multiple runs
(PR #13 first confirmed it, continue-on-error removed from `build-gf`
since), confirming the local and CI environments agree — the "prove
it, don't assume it" bar the rest of this project holds to. If this
count or that status claim drifts again, re-run `gf/run_gf_tests.py`
and update this paragraph by hand, the same discipline the top-level
README's own Roadmap section now holds to after being caught stale.
See `gf/FraCaSLogic.gf`/`gf/FraCaSLogicEng.gf` for
the grammar itself and each file's own per-section comments for what
each FraCaS section needed and what it deliberately skipped.

## Toolchain install (Windows 11 / WSL2)

1. **WSL2 + Ubuntu**: `wsl --install` from an admin PowerShell, then use
   the Ubuntu terminal for everything below.
2. **GF itself is not packaged for apt** (`apt install gf` fails —
   there's no such package). It also can't be installed via
   `cabal install gf` from Hackage on a stock modern GHC: the published
   `gf` package (3.12) needs `ghc-prim <= 0.10.0`, and a default
   `ghcup`-installed GHC ships something newer — a real, currently
   unresolved version mismatch, not a local mistake. The reliable path
   is building `gf-core` from source with **Stack**, which pins its own
   known-good GHC version instead of using whatever's already installed:
   ```
   curl -sSL https://get.haskellstack.org/ | sh
   git clone https://github.com/GrammaticalFramework/gf-core.git
   cd gf-core
   stack --stack-yaml stack-ghc8.10.7.yaml setup
   stack --stack-yaml stack-ghc8.10.7.yaml build
   stack --stack-yaml stack-ghc8.10.7.yaml install   # copies `gf` to ~/.local/bin
   ```
   Expect 20–60+ minutes and a few GB of disk for the `build` step.
3. **PATH**: `~/.local/bin` (where `stack install` puts the binary) is
   not on PATH by default. Add it in `~/.bashrc`. Careful: if you
   `echo '...' >> ~/.bashrc` right after another tool's installer (e.g.
   ghcup) already appended a line with no trailing newline, your new
   line lands *after that line's `#` comment* and is silently inert.
   Use `printf '\n...\n' >> ~/.bashrc` (forces its own line) and always
   sanity-check with `tail -3 ~/.bashrc` after any append — don't just
   assume it worked.
4. **The RGL (resource grammar library)**: a separate repo,
   `github.com/GrammaticalFramework/gf-rgl`. Its `main` branch is an
   unpinned, continuously-changing development snapshot, not
   necessarily compatible with a given released `gf` version — prefer
   a dated tagged release (e.g. `20260403`) over `main`. Build with:
   ```
   git clone https://github.com/GrammaticalFramework/gf-rgl.git
   cd gf-rgl && git checkout 20260403
   ./Setup.sh --dest=$HOME/gf-libs -v
   ```
   `Setup.sh` (the no-Haskell-needed shell build script) has **no
   `--langs` flag** — that only exists on the Haskell `Setup.hs` build
   script — so a plain `Setup.sh` run always builds every language RGL
   knows, not just English. That's fine for this project's eventual
   goal of not being English-only anyway; it does mean the build takes
   a while.
5. **`GF_LIB_PATH`**: set it in `~/.bashrc`
   (`export GF_LIB_PATH="$HOME/gf-libs"`) — same append-newline caveat
   as above.

## The `~/gf-libs` layout, and a real foot-gun

`Setup.sh`'s `--dest` is **not** a flat directory — it's organized into
subfolders by build phase: `prelude/`, `present/`, `alltenses/`,
`morphodict/`. `present` and `alltenses` are two *separate, mutually
incompatible* compiled variants of the same modules (present-tense-only
vs. full tense coverage) — pointing `-path` at both at once (e.g. a
bare `-path=$HOME/gf-libs` that reaches into both subfolders) makes GF
silently mix pieces from each tier, which surfaces later as a
baffling `Internal error in GeneratePMCFG: unknown identifier ...`
during linking, not as an import error up front. **Always point `-path`
at exactly one tier plus `prelude`** — for this project, that's:
```
-path=.:$HOME/gf-libs/alltenses:$HOME/gf-libs/prelude
```
(`alltenses`, not `present`, since full tense coverage is what a
NL-semantics project actually wants.)

## A real GF 3.12.0 compiler bug: avoid `Syntax`/`SyntaxEng`

The RGL ships a convenience interface, `Syntax` (bundling
`Constructors + Cat + Structural + Combinators` into one thing an
application grammar can extend in one go), with a per-language instance
(`SyntaxEng`, etc.). **Using it (`= SyntaxEng ** open ...`) triggers a
genuine compiler crash** — `Internal error in GeneratePMCFG: unknown
identifier above_Prep` — even though `above_Prep` is a perfectly
ordinary, correctly-defined word in `StructuralEng`. This reproduced
identically across two different RGL versions (`main` HEAD and the
`20260403` tag), so it's not a version-skew issue; it's specific to how
GF 3.12.0's linker resolves the `interface ... = A, B, C, D` bundling
mechanism.

**Fix: never go through `Syntax`/`SyntaxEng`. Extend the underlying
modules directly instead** — `CatEng`, `ConstructorsEng`,
`StructuralEng`, `ParadigmsEng`, etc., named individually. Every
grammar in this project does this from the start; if a future one is
tempted to write `= SyntaxEng ** ...` for convenience, don't — it will
compile far enough to look fine and then crash at the very last step
(linking), which wastes a full rebuild cycle to rediscover.

## RGL's abstract syntax is scattered across many small modules

There's no one module that has "the" abstract functions for building
sentences — `Cat.gf` only declares *categories* (`S`, `NP`, `CN`, ...),
not the functions that build them. The functions actually needed for a
simple quantified sentence are spread across separate abstract modules,
each needing its own `extends` on both the abstract and concrete side
(`Foo` in the abstract module's `**`-list, `FooEng` in the concrete
module's):

| Function(s)                                            | Abstract module | Concrete module |
|----------------------------------------------------------|-----------------|------------------|
| `every_Det`, `someSg_Det`/`somePl_Det`, `no_Quant`        | `Structural`    | `StructuralEng`  |
| `most_Det`                                                | (`DictEngAbs` — heavier, a ~30k-line general dictionary; avoided so far, see below) | `DictEng` |
| `UseCl`                                                   | `Sentence`      | `SentenceEng`    |
| `PredVP`                                                  | `Sentence`      | `SentenceEng`    |
| `TTAnt`, `TPres`, `ASimul`, `PPos`                        | `Tense`         | (bundled into `SentenceEng`, no separate `TenseEng` file exists) |
| `DetCN`, `AdjCN`, `UseN`                                  | `Noun`          | `NounEng`        |
| `PositA`                                                  | `Adjective`     | `AdjectiveEng`   |
| `ComplVV`, `UseComp`, `CompCN`, `CompAP`                  | `Verb`          | `VerbEng`        |

The working recipe: `abstract X = Cat, Structural, Sentence, Tense,
Noun, Adjective, Verb ** { ...our own lexical fun declarations... }`,
concrete `X`Eng `= CatEng, StructuralEng, SentenceEng, NounEng,
AdjectiveEng, VerbEng ** open ParadigmsEng in { ...our own lexical
`lin` rules, via `mkA`/`mkN`/`mkV`/`mkVV`... }`. `most_Det` (the only
determiner needed so far that lives in the big `DictEng`/`DictEngAbs`
dictionary rather than `Structural`) hasn't been pulled in yet — when
it's needed, extend with `DictEngAbs`/`DictEng` the same way.

**Don't redeclare a word that's already a Structural constant.**
`want_VV` is already declared in `Structural` (it's common enough to be
a built-in structural word) — declaring our own `want_VV : VV` in our
own abstract module collides with it (`cannot unify ... in module
Structural with ... in module <ours>`). Reuse the existing one; only
declare genuinely new content words (`italian_A`, `tenor_N`, etc.).

## Not every RGL module Setup.sh's build is missing is *just* the dictionary

`Backward.gf`/`BackwardEng.gf` (the module with `ComplV2`, the plain
transitive-verb VP constructor) hit the exact same "File X.gf does not
exist" error `DictEngAbs` did, confirming this isn't a one-off special
case about the dictionary specifically - `Setup.sh`'s build output is
missing more than one module the gf-rgl *source* tree has. **When a
needed function's home module fails to load with "File X.gf does not
exist," don't assume it's unbuildable - just self-declare that function
too**, the same recipe as below: find its real linearization in the
source clone (`grep` the function name in the relevant `src/english/*.gf`
file), and copy the right-hand side directly, opening whatever resource
module(s) that recipe itself depends on (same as `mkDeterminer` below).
`ComplV2`'s real recipe (from `BackwardEng.gf`) is
`insertObj (\\_ => v.c2 ++ np.s ! NPAcc) (predV v)`, needing `insertObj`
and `predV` from `ResEng` (a resource module, `open`ed directly - same
"open it yourself, don't rely on inheriting it" situation as
`mkDeterminer`/`MorphoEng` below).

**But don't trust an "obsolete" module's recipe verbatim either.**
`BackwardEng.gf` literally opens with the comment "a repository of
obsolete constructs, needed for backward compatibility" (dated
2008-04-19) - and it's not just old, it's actually stale against the
*current* RGL API: its own source writes `np.s ! Acc`, but `ResEng.gf`'s
real `NPCase` type (`NCase Case | NPAcc | NPNomPoss`) has no bare `Acc`
constructor at all, only `NPAcc` - the accusative case constructor was
evidently renamed at some point since 2008 and `Backward.gf` was never
updated to match. `gf -make` catches this immediately and clearly
("constant not found: Acc"), which is plausibly *why* it's excluded
from `Setup.sh`'s build output in the first place, not an arbitrary
omission like `DictEngAbs`. Moral: when copying a recipe out of a
module the RGL itself flags as obsolete, expect it may not compile
verbatim against the current API - check any param/constructor names it
uses (`grep` their real current definition, as always) rather than
assuming a same-repo cross-reference is automatically still accurate.

## `DictEngAbs`/`DictEng` (the general dictionary) aren't in `Setup.sh`'s build output

`Setup.sh`'s default build (see above) does **not** produce
`DictEngAbs.gfo`/`DictEng.gfo` anywhere under `--dest` - confirmed with
`find ~/gf-libs -iname 'DictEngAbs*'` returning nothing, even though the
module exists in the `gf-rgl` *source* tree (`src/english/DictEngAbs.gf`,
`src/english/DictEng.gf`). It's the RGL's ~30k-line general dictionary
and is a separate, heavier build step Setup.sh doesn't run by default.

**Superseded** (was originally: "don't extend `DictEngAbs`/`DictEng` at
all, declare every content word directly instead"). That held only
while every word this project needed was hand-declared one at a time;
once the word count grew past Section 1, compiling `DictEngAbs.gf`/
`DictEng.gf` directly (as its own extra step, straight into the same
`~/gf-libs/alltenses` `Setup.sh` already populated - see
`.github/workflows/build.yml`'s own "Build DictEng" step) and
extending `FraCaSLogic`/`FraCaSLogicEng` with it turned out to work
fine and cut the amount of hand-declared vocabulary dramatically -
each grammar file's own extends line now reads `DictEngAbs - [...]`
(excluding only the handful of names that collide with something
already free via `Structural`, or whose real dictionary recipe doesn't
match what a specific FraCaS sentence needs - see either grammar
file's own comment on its exclusion list for the full account). The
"copy the word's own `lin` rule instead of the whole module" move
below is still the right one for a word that's excluded for either of
those reasons, or that genuinely isn't in `DictEngAbs` at all (a
FraCaS-specific proper noun, an invented product name, a compound this
project needs fused as one lexical item).

**Watch out: a module using an oper internally doesn't re-export it.**
`someSg_Det`/`somePl_Det` in `StructuralEng.gf` are themselves built from
`mkDeterminer`, but that's `StructuralEng`'s own private
`open MorphoEng in {...}` at work - a module that merely `extends`
`StructuralEng` (as this project's own concrete syntax does) does NOT
inherit that opening. Confirmed by a real compile error: `constant not
found: mkDeterminer` even with `StructuralEng` (and `ParadigmsEng`,
which provides the *other* smart constructors this grammar uses - `mkA`,
`mkN`, `mkAdA` - fine) already in scope. `mkDeterminer` is declared in
`MorphoEng` specifically (`grep -rn "mkDeterminer :" ~/gf-rgl/src/english/`
finds it there, not in `Constructors.gf` or `ParadigmsEng.gf`), so the
fix is to `open` `MorphoEng` directly ourselves alongside `ParadigmsEng`,
not to rely on it being pulled in transitively through `StructuralEng`.

## Two different lambda syntaxes: `\x -> e` vs `\\x => e`

Copying a recipe out of RGL source verbatim and dropping a backslash
produces a real, confusing compile error: `Unexpected token '=>'.
Expected one of: '->'`. GF has two lambda forms, not one - `\x -> e`
builds a plain function (arrow type `A -> B`), while `\\x => e` (double
backslash) builds a *table* (finite function over a param type, e.g.
`Agr => Str`). `ComplV2`'s recipe (`insertObj (\\_ => v.c2 ++ np.s !
Acc) (predV v)`) needs the double-backslash form because `insertObj`'s
first argument is table-typed (`(Agr => Str) -> VP -> VP`) - `insertObj`
itself is defined with the plain single-backslash form (`\obj,vp -> ...`)
since it's an ordinary two-argument function. When copying a recipe,
match the backslash count exactly as printed - it's not a stylistic
choice or a typo in the source, it's meaningful syntax.

## `mk*` sugar only works inside compiled source files

The `mk*` "smart constructor" family (`mkS`, `mkCl`, `mkNP`, `mkCN`,
`mkAP`, `mkVP`, ...) from `Constructors.gf`/`ParadigmsEng.gf` are
**opers** — a source-level convenience that gets fully expanded/inlined
at compile time. They are **not** part of the compiled grammar's
abstract syntax and are **not usable at the interactive `gf` shell
prompt** (`linearize mkS (mkCl ...)` doesn't work there — only real,
already-declared `fun`s do). Two consequences:
- Inside a `.gf` source file, they're fine and convenient for writing a
  lexical item's own linearization (`lin italian_A = mkA "Italian" ;`).
- For building a **sentence's own tree** so that it stays inspectable
  (rather than opaque), don't wrap it in a named nullary abstract
  constant either (`fun P002 : S ; lin P002 = mkS (mkCl ...) ;` looks
  tempting, but a concrete `lin` rule can only build a *string/record*
  value — it can't invoke other abstract functions, so `P002` stays a
  completely opaque atom to anything reading the compiled grammar, with
  zero visible internal structure). Instead, declare the *lexical
  items* (adjectives, nouns) as their own abstract `fun`s with simple
  `mk*`-based `lin` rules, and build the **whole sentence** as a bare,
  unnamed tree expression using RGL's *real*, non-sugared function
  names (`PredVP`, `DetCN`, `AdjCN`, `PositA`, `UseN`, `ComplVV`,
  `UseComp`, `CompCN`, `CompAP`, ...) applied directly to those lexical
  funs. That tree is real, traversable data — exactly what a downstream
  translator needs — and it's still typed and linearizable the same
  way.

To find the real, desugared name behind a given `mk*` overload,
`grep` the specific overload's definition directly out of
`gf-rgl/src/api/Constructors.gf` (each overload's `=` right-hand side
*is* the real function) rather than guessing from the sugar's name.

## `parse` against the full grammar is not usable for controlled input

Loading the RGL's own full, maximally-permissive English grammar
(`AllEngAbs`/`AllEng` — what `Setup.sh` already compiles) and running
`parse "..."` on an ordinary sentence produces an enormous, effectively
unbounded number of alternate readings (possessives, apposition,
dropped-pronoun placeholders like `?4`/`?15` all being tried), not a
short, clean list — it can run for minutes without terminating even on
a short sentence. This is inherent to how permissive the full grammar
is, not a bug to route around. **For controlled/known input, don't
parse — hand-build the tree directly** (as above) and use `linearize`
to confirm it round-trips to the exact right English string. Free
parsing only becomes viable with either a much more restricted grammar
or serious ambiguity-ranking/pruning.

**Update — both now exist, and parsing works.** Measured first against
this project's own FraCaSLogic grammar (smaller than `AllEng`, but still
all of the RGL's Noun/Verb/Sentence/... modules plus DictEng): 69,115
readings for "every Italian man wants to be a great tenor" before a
5-minute timeout, none free of `ProDrop`/`ApposCN`/`GenNP` junk.
`gen_parse_grammar.py` builds `FraCaSParse.gf`/`FraCaSParseEng.gf` by GF
*restricted inheritance* (`FraCaSLogic [f, g, ...]`), keeping only the
functions and words the CI-confirmed trees in `run_gf_tests.py` use (plus
the non-`Cat` categories - `ListCN`/`ListNP`/numeral sub-categories -
that linking otherwise reports missing). The same sentence then has 4
readings in well under a second. `parse_rank.py` ranks readings
generically (fewest nodes, ties broken by right association), and
`parse_eval.py` (run by the `build-gf` CI job) measures it over all 437
distinct confirmed sentences: all parse, the hand tree is among the
readings for every one, and the top reading translates like the hand tree
for 371/373 of those `translate.py` covers. This restricted grammar is
fit to FraCaS's own vocabulary and constructions - a controlled-language
grammar, not open-domain parsing - and `scripts/gen_blind_eval_parsed.py`
uses it to translate FraCaS's original English end to end; see
`BLIND_EVAL.md` for what that achieves (and doesn't).

Building that pipeline exposed three `translate.py` bugs, now fixed:
prepositions were dropped from predicate names (FraCaS 74's "resident
**in** Europe" and "resident **outside** Europe" both became
`residentEurope`), GF word-sense tags leaked into names (`by8agent` vs
`by8means` for the same "by"), and a relative clause translated to a
conjunction under `CompNP (DetCN ...)` but to one fused name under the
equivalent `CompCN` derivation. One known collision remains: object
determiners are still dropped ("spend **a lot of** time at home" and
"spend time at home" share a name). Keeping all determiners was tried
and reverted - it leaks subject determiners into the cross-check
generator's restrictor names (`everyCommittee`) and breaks the
`fracas_090` cross-check - so it needs a targeted fix, not a blanket one.

**Later round - FraCaS's own wording, and the fixes it needed.** Parsing
FraCaS's original English (not the confirmed rewordings) surfaced four
constructions no hand-built tree used, each now added to FraCaSLogic with
one confirmed linearize check (`run_gf_tests.py`'s
`_FRACAS_ENGLISH_CHECKS`, labelled `english_*` so `gen_gf_cross_check.py`
ignores them): `who_RP` (`IdRP` realizes "that" by design), a
self-declared `ExistNP` ("there are/was NP" - IdiomEng's own lin, since
extending `Idiom` fails at this gf-rgl tag), a frozen `usedTo_VV` (DictEng's
`use_VV` is the freely conjugated verb), and DictEng's own `just_Predet`.
`parse_rank.tokenize` is a single generic lexer step (final punctuation
dropped, commas split off, tokens looked up case-insensitively in the
grammar's own `pg -words` vocabulary). The targeted determiner fix this
note asked for is in: `_scope_name` now keeps lexical `_Det` words inside
a VP ("spend a lot of time" vs "spend time") and reads a definite plural
object universally - the convention already used for subjects - so
`fracas_090`'s "the items"/"every item" still name one predicate.
Comparatives and equatives now translate as binary relations
(`fastThan`/`fastAs`, the naming the cross-check builders already used).

**Ellipsis, one-anaphora, negation.** A census of every FraCaS sentence
the parser still rejected showed half contain no unknown word at all -
they are construction gaps, dominated by Section 4's VP ellipsis ("So
did Bill", "Bill didn't", "the students have too") and one-anaphora
("Bill owns a blue one"). FraCaSLogic now has an `EllAux` category with
`ElliptS`/`SoS`/`TooS` for the elliptical clauses, `anaphOne_N`/
`anaphOne_NP` for anaphoric "one", and `UncNeg` for uncontracted "is not"
(this grammar's `PNeg` realizes "isn't"), each with a confirmed check.
The grammar deliberately does not represent the elided material:
`scripts/gen_blind_eval_parsed.py` resolves it by copying the antecedent
clause's VP or noun (the standard copy treatment). `EllAux` had to be
added to `gen_parse_grammar.py`'s `EXTRA_CATS` for the same reason as the
list categories.

One trap worth recording: the single-node `anaphOne_NP`/`anaphOne_N`
immediately outranked the multi-node numeral "one" under the
fewest-nodes rule ("Smith signed [one] contract" as a compound noun, "just
[one] accountant", "[one] of the leading tenors"), dropping top-reading
agreement from 380/381 to 374/382. `parse_rank.ranked` now discards
readings where anaphoric one is anything but the head of a noun phrase or
a bare argument - a well-formedness condition, not a ranking tweak - and
agreement is back to 381/382.

**Quantity comparatives.** "ITEL won more orders than APCOM did" (and
"... than APCOM", "... than APCOM lost", FraCaS 230-241) gets three
FraCaSLogic functions, `MoreThanAux`/`MoreThanNP`/`MoreThanV2 : CN -> NP
-> ... -> NP`. Each realizes the whole object NP "more CN than NP [did |
V-ed]", with a confirmed check apiece. As with ellipsis, the "than" part
is not a full clause in the grammar: an elided verb is resolved to the
main clause's own verb by `translate.py`, which translates the sentence
as `More order (win itel) (win apcom)`. `More` is the three-place
quantifier `card (P ∧ Q) > card (P ∧ R)` in `GQ.lean`. This needed
object quantifiers, which `translate.py` did not have: it fused the
whole VP into one predicate name. It now keeps the verb as a binary
predicate and the determiner as a quantifier over it, but only for a
proper-name subject (no scope interaction) whose object counts
(numerals, "some/several/a few/many Xs", "more Xs than ..."), and only
in the end-to-end readings. Other objects keep the fused name, so a
problem mixing the two shapes can lose an inference, never gain a wrong
one.

The same work found a soundness bug in the fused names: numerals were
dropped, so "won ten orders" and "won eleven orders" were one predicate.
Fused names now keep the numeral (`win10Order`). A bare numeral is also a
fifth ambiguity kind in the end-to-end readings: "at least n" (weak) or
"exactly n" (strong). "Just/only n" is always exact, and "at least/at
most/exactly n" say which outright.

Free-choice "any" (DictEng's `anySg_Det`, FraCaS 248: "faster than any
ITEL computer") is read universally, but only as a comparative's
standard; everywhere else "any" still does not translate.

**"Few", "a few", "at least a few".** No grammar change: these
already parsed, and `translate.py` had no rule for `few_Det`/
`atLeastAFew_Det`. "Few" is a sixth ambiguity kind, read as cardinal
(`AtMost fewCount`, unknown threshold) or proportional (an opaque `Few`,
bound by the generator with one meaning postulate). "A few"/"at least a
few" are `AtLeast aFewCount` with `aFewCount ≥ 1`. A counting existential
("there are few committee members from southern Europe") takes the NP's
PP or relative clause as its scope. The parse puts the PP inside the
compound ("committee [members from ...]"), so the translator re-brackets
it first. FraCaS 27 then needed the `(AtLeast, scope)` counterpart of
`mono_nl`'s Phase-5 conditioned narrowing (`atLeast_mono_scope_
conditioned`); aesop did not find the equivalent `atLeast_trans`.

**Measured and rejected: a corpus-vocabulary lexicon.** Giving the parse
grammar DictEng's entries for every word FraCaS uses (404 lexical
functions for 94 missing words) let only 25 more of the 230 failing
sentences parse - nearly all ellipsis or aspect sentences translate.py
cannot translate anyway - while one of them reached 34,902 readings. Not
adopted: the remaining failures are constructions, not vocabulary.

## SOLVED: `UseCl`/tense support - the missing piece was `TenseX`, not a real RGL bug

**This was wrong for a long time and is now fixed - full story below,
including two dead ends, because both are instructive.**

`linearize (PredVP np vp)` (category `Cl`) reliably produces the fully
correct, correctly-conjugated English string. Wrapping the exact same
clause with `UseCl (TTAnt TPres ASimul) PPos (...)` to get an `S`
compiled fine but **linearized to an empty string**. This was first
taken as a genuine RGL limitation and worked around by using `Cl`,
never `S`, as this project's target category (tense/aspect being
separate information from the core proposition elsewhere in this
project - the FraCaS Section 7 Lean proofs - made this a defensible
design choice regardless, not just a workaround).

**Dead end 1**: gf-rgl's own treebank always wraps `UseCl`'s result in
`UttS : S -> Utt` before linearizing, never linearizing a bare `S`
directly. Hypothesis: the missing `UttS` wrapping was the actual cause.
Tested via CI (after fixing two real bugs in the *test methodology
itself* - a batched-session check that let one command's output
satisfy a different command's expected string, then a "fix" that ran
each check as its own process and broke *every* check via a
startup/piping race - both documented above under "Automating
`linearize` checks"). Once the test methodology was actually
trustworthy: `linearize UttS (UseCl (TTAnt TPres ASimul) PPos (...))`
still produced blank output. Hypothesis rejected.

**The real fix**: our grammar extends the *abstract* `Tense` module
(giving `TTAnt`/`PPos`/etc. as valid syntax that compiles) but never
extended any *concrete* pairing for it. `TenseX` (`concrete TenseX of
Tense = CommonX ** open (R = ParamX) in {...}`, in `src/common/`) is
that pairing - genuinely cross-language, not English-specific. Traced
through `gf-rgl/src/english/GrammarEng.gf` (the RGL's own full-coverage
aggregate grammar, which every prior working example - including the
treebank and the `vps2.gftest` regression test that first proved
tensed linearization genuinely works in this RGL version at all -
ultimately builds on) to find this. Extending with plain `TenseX`
alone doesn't work either, for a real, separate reason: its own `CAdv`
shape doesn't unify with `CatEng`'s (a genuine conflict) - confirmed
because `GrammarEng.gf` itself works around the exact same conflict,
by extending `TenseX - [Pol, PPos, PNeg, SC, CAdv]` (excluding those
five) and redefining `PPos`/`PNeg` itself:
```
PPos = {s = []; p = CPos} ;
PNeg = {s = []; p = CNeg True} ;
```
Copied that recipe verbatim (it's RGL's own generic conflict-resolution
pattern, not FraCaS-specific content - same non-issue as the numeral
encoding). One more gap: `True`/`False` need `Prelude` opened
(`SentenceEng.gf` itself already does this, we hadn't).

**Result, confirmed via CI with the corrected per-command-isolated test
methodology**: `linearize UttS (UseCl (TTAnt TPres ASimul) PPos (PredVP
... want to be a great tenor ...))` → `"every Italian man wants to be a
great tenor"` - genuine, correct, non-blank output. Tense support is
real. Whether to switch this project's target category from `Cl` to
full `S`/`Utt` (now that it's possible) or keep `Cl` as the default and
use `S` only where a sentence's tense actually matters is a design
choice to make deliberately, not a hard technical wall anymore - the
wall is gone.

## Automating `linearize` checks: a shared session is required, but needs correct per-command splitting

Two real bugs in `gf/run_gf_tests.py`'s test methodology, found in
sequence:

1. **First version**: ran every check's `linearize` command in one
   shared `gf` stdin session, then checked each check's expected string
   against the *whole* session's captured output. This produced a false
   positive: a diagnostic check for whether wrapping `UseCl`'s result in
   `UttS` fixes the blank-output problem below appeared to pass, because
   its expected substring ("wants to be a great tenor") had already
   appeared in an *earlier, unrelated* check's own result further up the
   same transcript - the diagnostic's own command actually still
   produced blank output. A substring check against a shared
   multi-command transcript is not evidence that *that specific
   command* produced the expected output, only that the string appeared
   *somewhere*.
2. **"Fix" that was itself broken**: running each check as its own
   separate, short-lived `gf` process (one `linearize` command, then
   `quit`, per invocation) - the obvious-looking fix for bug 1 - made
   *every single check* produce blank output, not just the diagnostic
   one. This is a startup/piping race specific to that lone-command-
   then-quit pattern (the process exits before `gf`'s own output
   finishes), not a real result; the batched shared-session approach is
   actually the reliable one.

**The real fix**: keep the shared session (proven reliable), but split
its captured output on the `FraCaSLogic> ` prompt marker into one
segment per command, in the order the commands were sent, and check
each expected string only against its own corresponding segment. This
gets correct per-command isolation without the piping race.

## How to debug a "why is this blank / why doesn't this work" problem here

The pattern that actually worked, every time: **linearize the smallest
possible sub-tree first**, then grow it one function application at a
time, rather than debugging a big nested expression all at once. When
a big `linearize` call was silently blank, splitting it into
`linearize (AdjCN ...)`, then `linearize (DetCN ...)`, then
`linearize (PredVP ...)` isolated the exact function application
responsible in a couple of steps, versus staring at one large failing
expression. GF's own error messages are precise about *what's missing*
("Function X is not in scope", "cannot unify ... in module A with ...
in module B") but never *where in a large expression* something is
wrong when the failure is silent (empty output) rather than a compile
error — sub-tree bisection is the fix for that gap.
