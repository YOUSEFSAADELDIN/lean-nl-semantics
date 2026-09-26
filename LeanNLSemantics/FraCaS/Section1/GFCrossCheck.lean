import LeanNLSemantics.FraCaS.Section1.Batch1

/-!
# GF cross-check: problem 2's first premise

The GF integration in `gf/` (grammar in `gf/FraCaSLogic.gf`/
`gf/FraCaSLogicEng.gf`, translator in `gf/translate.py`) is a second,
independent path from an English sentence to a Lean `Prop`: a hand-built
GF tree that `linearize`s back to the exact target English (confirmed on
the real GF toolchain, not just in this repo), fed through
`translate.py`, which turns it into a Lean proposition using this
project's own `Every`/`Some`/`No`/`Most` vocabulary (`GQ.lean`).

This file is that path's one end-to-end confirmation, for `fracas_002`'s
first premise ("Every Italian man wants to be a great tenor."). The GF
tree
```
PredVP (DetCN every_Det (AdjCN (PositA italian_A) (UseN man_N)))
       (ComplVV want_VV (UseComp (CompCN (AdjCN (PositA great_A) (UseN tenor_N)))))
```
translates (via `python3 gf/translate.py`) to `Every italianMan
wantGreatTenor`. `Batch1.lean`'s own hand-written `fracas_002` uses
differently-named (but semantically identical) predicates -
`italianMan`/`wantsGreatTenor` - chosen independently, by hand, before
any of the GF work existed. The check below is not "these look similar
to a human reader": `fracas_002_from_gf` restates the theorem using
`translate.py`'s own generated names, and its proof is nothing but a
direct application of the real, already-proved `fracas_002` - so this
typechecks only because the GF-generated proposition's shape (which GQ
combinator, applied to which restrictor/scope, in which order) is
*exactly* the one `fracas_002` already proves, not merely similar to it.
A mismatched combinator or swapped argument order here would fail to
typecheck, not just look wrong.

Only the first premise is cross-checked this way - `fracas_002`'s second
premise ("Some Italian men are great tenors") and its conclusion are
still the hand-written formalization as-is; extending the translator to
cover a full multi-premise problem end to end is future work, not
claimed here.
-/

namespace FraCaS.Section1

theorem fracas_002_from_gf {A : Type*}
    (italianMan wantGreatTenor isGreatTenor : A → Prop) :
    Every italianMan wantGreatTenor → Some italianMan isGreatTenor →
      Some italianMan wantGreatTenor :=
  fracas_002 italianMan wantGreatTenor isGreatTenor

end FraCaS.Section1
