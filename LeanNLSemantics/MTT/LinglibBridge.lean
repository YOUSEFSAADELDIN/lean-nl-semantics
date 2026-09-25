/-!
# Bridge to linglib (optional, not built by default)

This file is **not** imported by `LeanNLSemantics.lean` and linglib is
**not** listed in `lakefile.toml`. It's a design sketch for connecting
this package's MTT core (`CN.lean`) to `hawkrobe/linglib`'s Montagovian
composition engine, kept out of the default build so the core MTT library
never depends on a second, fast-moving, single-maintainer project. Build
it only when you actually want the bridge: add a second

```toml
[[require]]
name = "linglib"
git = "https://github.com/hawkrobe/linglib.git"
```

to `lakefile.toml`, add this file to a separate `[[lean_lib]]` target (not
the default one), and uncomment the `import` below.

## The actual connection point

Read directly from linglib's `Semantics/Composition/Ty.lean`:
`Ty.Domain E W ty` is generic in an entity type `E` and index type `W`
supplied per fragment, and `Ty.Domain E W .e = E`,
`Ty.Domain E W .et = E → Prop` (definitionally, since `Ty.Domain` is
`abbrev`). So for any linglib fragment's chosen `E`, its common-noun
denotations already live at exactly the type `E → Prop` — Montague's
CNs-as-predicates. The bridge below refines that `E` into MTT's
CNs-as-types on top of the *same* `E`, rather than introducing a second,
disconnected entity domain (contrast `CN.lean`'s toy `Individual` type,
which exists only so the standalone core has a concrete, computable
model — a real fragment would use this bridge's `E` instead).

```
-- import Semantics.Composition.Ty
-- import LeanNLSemantics.MTT.CN

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

end MTT.LinglibBridge
```

## What this does and doesn't buy you

Reusing linglib's `E` this way makes every MTT theorem transportable to
linglib's fragments and vice versa — the item 4 goal from the original
research briefing ("a formal bridge comparing MTT and Montagovian
interpretations") falls out of the definitions instead of needing to be
proven separately. It does **not** get you linglib's existing per-language
lexica for free: `Lexicon.embed_mono` still has to be discharged by hand
for each predicate a fragment actually uses, since linglib's own
predicates were never written with the CN lattice's monotonicity in mind.
-/
