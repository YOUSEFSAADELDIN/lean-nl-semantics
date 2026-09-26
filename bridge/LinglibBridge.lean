import Linglib.Semantics.Composition.Ty
import MTT.CN

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
`MTTCore` target reuses `../LeanNLSemantics/MTT/CN.lean` directly (via
`srcDir`, not a package dependency) so this file always tracks the same
`CN`/`CNTag`/`Individual` the main package's core library uses.

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
-/

namespace MTT.LinglibBridge

open Semantics.Composition

/-- A lexicon over linglib's entity type `E`: one `E → Prop` per CN tag
(exactly linglib's `Ty.Domain E W .et`), required to respect the CN
lattice — `embed_mono` is the proof obligation a fragment author owes:
"whatever satisfies the `man` predicate also satisfies `human`". This is
fragment-specific lexical content, not provable in general. -/
structure Lexicon (E : Type) where
  embed : MTT.CNTag → E → Prop
  embed_mono : ∀ {a b}, a ≤ b → ∀ x, embed a x → embed b x

/-- MTT's CN-as-type, refining linglib's entity domain instead of
`CN.lean`'s standalone toy model: `CN' L t` is the type of `E`-elements
the lexicon's `t`-predicate accepts. -/
def CN' {E : Type} (L : Lexicon E) (t : MTT.CNTag) : Type :=
  {x : E // L.embed t x}

/-- Widening, same shape as `MTT.CN.widen`, discharged via the lexicon's
monotonicity proof instead of the toy model's `le_trans`. -/
def CN'.widen {E : Type} (L : Lexicon E) {a b : MTT.CNTag} (h : a ≤ b) :
    CN' L a → CN' L b :=
  fun x => ⟨x.1, L.embed_mono h x.1 x.2⟩

/-- The predicate reading is recovered for free — this *is* the bridge:
an MTT quantifier over `CN' L t` and a Montagovian generalized quantifier
over `L.embed t : Ty.Domain E W .et` are talking about the same set. -/
def CN'.toPredicate {E : Type} (L : Lexicon E) (t : MTT.CNTag) : E → Prop :=
  L.embed t

/-- Not just "the same shape" asserted in prose: `CN'.toPredicate`'s
output is *definitionally* a term of linglib's own Montagovian
common-noun type `Ty.Domain E W .et`, for any index type `W` a fragment
chooses — the kernel checks this, `rfl` needs no unfolding lemma. -/
example {E W : Type} (L : Lexicon E) (t : MTT.CNTag) :
    CN'.toPredicate L t = (L.embed t : Ty.Domain E W .et) :=
  rfl

/-- A concrete instantiation, reusing `CN.lean`'s own toy `Individual`
domain and its defining predicate (`x.kind ≤ t`) as the lexicon: not a
second, disconnected model, but literally the one `CN.lean`'s standalone
core already uses, now packaged as a linglib-shaped `Lexicon`.
`embed_mono` is exactly `CN.lean`'s own `le_trans` argument. -/
def toyLexicon : Lexicon MTT.Individual where
  embed t x := x.kind ≤ t
  embed_mono h _ hx := le_trans hx h

/-- With that lexicon, the bridge's `CN'` and `CN.lean`'s own `CN` are
the *same type* at every tag, not merely isomorphic — checked by `rfl`,
the same definitional-equality payoff `CN.lean`'s own coherence example
(two coercion routes agreeing) relies on. -/
example (t : MTT.CNTag) : CN' toyLexicon t = MTT.CN t := rfl

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
-/
