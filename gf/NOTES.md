# GF setup and debugging notes (Phase 3)

This records how the GF toolchain was actually gotten working, and every
real gotcha hit along the way, so the next round of grammar-writing
doesn't have to rediscover any of it. GF itself doesn't run in the cloud
sandbox this project's Lean/CI work happens in (no Haskell toolchain,
and `grammaticalframework.org` is blocked by that sandbox's egress
policy), so all of this was done on a separate machine (Windows 11 via
WSL2) and relayed back — see `gf/FraCaSLogic.gf`/`gf/FraCaSLogicEng.gf`
for the actual proven-working grammar this produced.

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
`insertObj (\_ => v.c2 ++ np.s ! Acc) (predV v)`, needing `insertObj`
and `predV` from `ResEng` (a resource module, `open`ed directly - same
"open it yourself, don't rely on inheriting it" situation as
`mkDeterminer`/`MorphoEng` below).

## `DictEngAbs`/`DictEng` (the general dictionary) aren't in `Setup.sh`'s build output

`Setup.sh`'s default build (see above) does **not** produce
`DictEngAbs.gfo`/`DictEng.gfo` anywhere under `--dest` - confirmed with
`find ~/gf-libs -iname 'DictEngAbs*'` returning nothing, even though the
module exists in the `gf-rgl` *source* tree (`src/english/DictEngAbs.gf`,
`src/english/DictEng.gf`). It's the RGL's ~30k-line general dictionary
and is a separate, heavier build step Setup.sh doesn't run by default.
**Don't extend `DictEngAbs`/`DictEng`** - declare every content word and
determiner this project needs directly in `FraCaSLogic.gf`/
`FraCaSLogicEng.gf` instead, the same way `really_AdA` always was. For a
word that DictEng already has a recipe for (e.g. `most_Det`), the fix is
to copy that recipe, not the dependency: `grep` the word's own `lin` rule
directly out of `gf-rgl/src/english/DictEng.gf` (the source clone, not
the built libs) and reuse the same right-hand side. `most_Det`'s real
recipe is `mkDeterminer plural "most"`.

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
or serious ambiguity-ranking/pruning, neither of which this project has
built.

## `UseCl` (bare `Cl` → `S`) silently produces empty output; use `Cl` directly

`linearize (PredVP np vp)` (category `Cl`) reliably produces the fully
correct, correctly-conjugated English string. Wrapping the exact same
clause with `UseCl (TTAnt TPres ASimul) PPos (...)` to get an `S`
compiles and type-checks fine but **linearizes to an empty string**,
for reasons not tracked down further (not worth the time — see below).
**Workaround: use `Cl`, not `S`, as this project's target category.**
This is actually a fine fit, not just a workaround: tense/aspect is
already treated as separate information from the core proposition
elsewhere in this project (see the FraCaS Section 7 Lean proofs), so a
tenseless clause is close to the right semantic unit anyway.

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
