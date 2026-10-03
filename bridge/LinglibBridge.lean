import Linglib.Semantics.Composition.Ty
import LeanNLSemantics.MTT.CN
import LeanNLSemantics.MTT.Adjectives

/-!
# Bridge to linglib (Phase 2b — a separate Lake package, on purpose)

This is a genuinely separate Lake package (`bridge/lakefile.toml`, its
own manifest, its own `lean-toolchain`), not a second target inside the
main `lean_nl_semantics` package. `hawkrobe/linglib` is a second,
fast-moving, single-maintainer project, and this dependency is optional
and exploratory — a version conflict between this bridge's pinned
linglib/Mathlib and the main package's own (unpinned, tracking `main`)
Mathlib requirement must never be able to break the main package's
build. Two separate lakefiles/manifests, built as two separate CI jobs
(`build` and `build-linglib-bridge` in `.github/workflows/build.yml`,
the latter `continue-on-error` at the job level), makes that structurally
impossible rather than merely unlikely. `bridge/lakefile.toml`'s
`MTTCore` target reuses the main package's own `LeanNLSemantics/MTT/*.lean`
files directly (via `srcDir`, not a package dependency) so this file
always tracks the same `CN`/`CNTag`/`Individual` the main package's core
library uses.

## The actual connection point

Read directly from linglib's `Semantics/Composition/Ty.lean` (as of
commit `8cd728c`, 2026-09-26 — linglib's own docs call it fast-moving,
so re-check this file if the bridge stops building): `Ty.Domain E W ty`
is generic in an entity type `E` and index type `W` supplied per
fragment, and (since `Ty.Domain` is `abbrev`, hence reducible)
`Ty.Domain E W .e = E` and `Ty.Domain E W .et = E → Prop` hold
definitionally. So for any linglib fragment's chosen `E`, its
common-noun denotations already live at exactly the type `E → Prop` —
Montague's CNs-as-predicates. The bridge below refines that `E` into
MTT's CNs-as-types on top of the *same* `E`, rather than introducing a
second, disconnected entity domain (contrast `CN.lean`'s toy
`Individual` type, which exists only so the standalone core has a
concrete, computable model — a real fragment would use this bridge's
`E` instead).

(Naming note: this file imports `CN.lean` and friends by their full
`LeanNLSemantics.MTT.*` module names, matching the main package's own
internal imports exactly — `MTTCore`'s `srcDir` below points straight at
the repo root rather than part-way into it, specifically so a reused
file's own `import LeanNLSemantics.MTT.X` lines resolve unchanged. An
earlier version of this bridge pointed `srcDir` one level deeper to get
a shorter `MTT.X` alias; that broke the moment a reused file (`MTT/
Adjectives.lean`, pulled in by `LinglibBridge/Section5Pilot.lean`) had
its own cross-import, since nothing upstream had needed more than
`CN.lean`'s own `import Mathlib` before.)
-/

namespace MTT.LinglibBridge

open Semantics.Composition

/-- A lexicon over linglib's entity type `E` and an arbitrary CN-tag type
`T` carrying its own subtyping order: one `E → Prop` per tag (exactly
linglib's `Ty.Domain E W .et`), required to respect `T`'s order —
`embed_mono` is the proof obligation a fragment author owes: "whatever
satisfies the `man` predicate also satisfies `human`". This is
fragment-specific lexical content, not provable in general.

Generalized over `T` (rather than hardcoded to `MTT.CNTag`, whose five
tags are `CN.lean`'s own toy model) so a real fragment can supply its
own tag lattice instead — see `LinglibBridge/Section5Pilot.lean`. -/
structure Lexicon (T E : Type) [LE T] where
  embed : T → E → Prop
  embed_mono : ∀ {a b : T}, a ≤ b → ∀ x, embed a x → embed b x

/-- MTT's CN-as-type, refining linglib's entity domain instead of
`CN.lean`'s standalone toy model: `CN' L t` is the type of `E`-elements
the lexicon's `t`-predicate accepts. -/
def CN' {T E : Type} [LE T] (L : Lexicon T E) (t : T) : Type :=
  {x : E // L.embed t x}

/-- Widening, same shape as `MTT.CN.widen`, discharged via the lexicon's
monotonicity proof instead of the toy model's `le_trans`. -/
def CN'.widen {T E : Type} [LE T] (L : Lexicon T E) {a b : T} (h : a ≤ b) :
    CN' L a → CN' L b :=
  fun x => ⟨x.1, L.embed_mono h x.1 x.2⟩

/-- An intersective adjective passes through any subtyping edge, for any
lexicon at all — not just `LinglibBridge/Section5Pilot.lean`'s own
`fracas_202`/`fracas_214`, which are exactly this theorem applied at
`L := section5Lexicon`. The only content is `CN'.widen` itself: keep the
`P`-witness, widen the rest. Generalizing it here (rather than leaving
it duplicated once per fragment) is what turns "one worked fragment"
into a small reusable piece of the bridge itself. -/
def CN'.intersective_widen {T E : Type} [LE T] (L : Lexicon T E) {a b : T} (h : a ≤ b)
    (P : E → Prop) :
    MTT.Intersective (CN' L a) (fun z => P z.1) → MTT.Intersective (CN' L b) (fun z => P z.1) :=
  fun ⟨x, hx⟩ => ⟨CN'.widen L h x, hx⟩

/-- The predicate reading is recovered for free — this *is* the bridge:
an MTT quantifier over `CN' L t` and a Montagovian generalized quantifier
over `L.embed t : Ty.Domain E W .et` are talking about the same set. -/
def CN'.toPredicate {T E : Type} [LE T] (L : Lexicon T E) (t : T) : E → Prop :=
  L.embed t

/-- Not just "the same shape" asserted in prose: `CN'.toPredicate`'s
output is *definitionally* a term of linglib's own Montagovian
common-noun type `Ty.Domain E W .et`, for any index type `W` a fragment
chooses — the kernel checks this, `rfl` needs no unfolding lemma. -/
example {T E W : Type} [LE T] (L : Lexicon T E) (t : T) :
    CN'.toPredicate L t = (L.embed t : Ty.Domain E W .et) :=
  rfl

/-- A lexicon that assigns each individual a single most-specific tag and
derives its own membership from that tag alone (`embed t x := kind x ≤
t`) — the pattern `toyLexicon` below and `Section5Pilot.lean`'s own
`section5Lexicon` already use by hand, named once so `embed_mono` comes
free from `le_trans` instead of being reproved per fragment. Needs the
stronger `[Preorder T]` (not just `Lexicon`'s own `[LE T]`) because
`le_trans` is exactly what discharges `embed_mono` here. -/
structure KindedLexicon (T E : Type) [Preorder T] where
  kind : E → T

/-- The `Lexicon` a `KindedLexicon` induces. -/
def KindedLexicon.toLexicon {T E : Type} [Preorder T] (K : KindedLexicon T E) : Lexicon T E where
  embed t x := K.kind x ≤ t
  embed_mono h _ hx := le_trans hx h

/-- Generalizes `Section5Pilot.lean`'s own `fracas_198_bridge`: for any
`KindedLexicon`, if no tag is ever comparable to *both* `a` and `b`
(`hdisjoint`), no individual's membership can witness both at once. This
is `fracas_198_bridge`'s own proof split into its two halves: the
generic half is this theorem; the fragment-specific half —
`hdisjoint` itself, e.g. `Section5Pilot.lean`'s own
`former_univStudent_tags_disjoint`, `decide`-checked by cases over one
concrete finite tag type — cannot be generalized further, since it
depends on that tag type's own shape, not on anything `KindedLexicon`
provides. -/
theorem KindedLexicon.disjoint_of_tags_disjoint {T E : Type} [Preorder T] (K : KindedLexicon T E)
    {a b : T} (hdisjoint : ∀ t, ¬ (t ≤ a ∧ t ≤ b)) (x : E) :
    K.toLexicon.embed a x → ¬ K.toLexicon.embed b x :=
  fun h1 h2 => hdisjoint (K.kind x) ⟨h1, h2⟩

/-- A concrete instantiation, reusing `CN.lean`'s own toy `Individual`
domain and its defining predicate (`x.kind ≤ t`) as the lexicon: not a
second, disconnected model, but literally the one `CN.lean`'s standalone
core already uses, now packaged as a linglib-shaped `Lexicon`.
`embed_mono` is exactly `CN.lean`'s own `le_trans` argument. -/
def toyLexicon : Lexicon MTT.CNTag MTT.Individual where
  embed t x := x.kind ≤ t
  embed_mono h _ hx := le_trans hx h

/-- With that lexicon, the bridge's `CN'` and `CN.lean`'s own `CN` are
the *same type* at every tag, not merely isomorphic — checked by `rfl`,
the same definitional-equality payoff `CN.lean`'s own coherence example
(two coercion routes agreeing) relies on. -/
example (t : MTT.CNTag) : CN' toyLexicon t = MTT.CN t := rfl

/-- `toyLexicon` itself is exactly `KindedLexicon.toLexicon` applied to
`Individual.kind` — confirmed by `rfl`, not merely "the same shape";
`Section5Pilot.lean` checks the identical thing for `section5Lexicon`. -/
example :
    toyLexicon = (KindedLexicon.mk (T := MTT.CNTag) (E := MTT.Individual) MTT.Individual.kind).toLexicon :=
  rfl

end MTT.LinglibBridge

/-!
## What this does and doesn't buy you

Reusing linglib's `E` this way makes every MTT theorem transportable to
linglib's fragments and vice versa — the original research briefing's
goal of "a formal bridge comparing MTT and Montagovian interpretations"
falls out of the definitions instead of needing to be proven separately
per fragment. It does **not** get you linglib's existing per-language
lexica for free: `Lexicon.embed_mono` still has to be discharged by hand
for each predicate a real fragment actually uses, since linglib's own
predicates were never written with the CN lattice's monotonicity in
mind. `toyLexicon` above is a proof that the bridge type-checks and
composes correctly, not a real fragment's lexicon.

`LinglibBridge/Section5Pilot.lean` takes the next step: a real tag
lattice and lexicon over six actual FraCaS Section 5 problems
(`mammal`/`animal`/`mouse`/`elephant`, `univStudent`/`former`,
`legalAuth`/`lawLect`), re-deriving `fracas_202`/`210`/`211`/`212`/`214`
through the bridge's `CN'` and `Adjectives.lean`'s existing generic
machinery, and strengthening `fracas_198`'s privativity ("former
university student") from a `decide`-checked missing edge into a proved
theorem — a third treatment alongside this project's existing two
(`fracas_198`'s own assumed premise, and `Adjectives.lean`'s
`Gun`/`realGun`/`fakeGun` sum-type construction), and the only one of
the three with no proof obligation to discharge at all.

## Generalizing past one fragment

`CN'.intersective_widen` and `KindedLexicon.disjoint_of_tags_disjoint`
above are the two fragment-specific results generalized up from
`Section5Pilot.lean` once that pilot showed what was actually doing the
work: `fracas_202`/`fracas_214`'s own re-derivations turned out to need
nothing beyond `CN'.widen`'s functoriality, true for *any* lexicon, not
just `section5Lexicon` — so `CN'.intersective_widen` states it once, and
`Section5Pilot.lean`'s own instances become one-line corollaries.
`fracas_198_bridge`'s own privativity result does **not** generalize the
same way: it relies specifically on `section5Lexicon`'s "one
most-specific kind per individual" construction, which `Lexicon`'s own
interface doesn't require (`embed` is just `T → E → Prop`, satisfying
monotonicity — nothing says it has to come from a single `kind`
function). `KindedLexicon` names that stronger pattern explicitly, and
`disjoint_of_tags_disjoint` proves the individual-level half generically
for it; the fragment-specific half (that `.former` and `.univStudent`
are never both reachable from any one tag, `Section5Pilot.lean`'s own
`former_univStudent_tags_disjoint`) still has to be `decide`-checked per
concrete tag lattice, and cannot be generalized further — it is a fact
about that one lattice's own shape, not about lexicons in general. That
asymmetry is itself informative: one of this file's two real results
(intersectivity passing through subtyping) is genuinely about the
`CN'`/`Lexicon` bridge machinery itself; the other (privativity as a
missing edge) is about a *particular, common way* of building a lexicon,
not a free consequence of the bridge's own interface.
-/
