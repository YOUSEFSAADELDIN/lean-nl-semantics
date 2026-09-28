/-!
# Polarity

The syntactic/compositional layer of the monotonicity reasoner (see
`Signature.lean`'s file comment for the layer split). `Polarity` says
nothing about *why* one predicate entails another - that's `Entails`
(`FraCaS.Section1.Every`, already used exactly this way throughout
`GQ.lean`'s `_restrict`/`_mono_scope` lemmas). It only says which
*direction* a known `Entails` fact must point for a substitution at a
given argument position to preserve truth - van Benthem's upward/
downward-entailing distinction.
-/
namespace FraCaS.Section1.Monotonicity

/-- `up`: substituting a value the OLD one entails (a "wider" replacement)
preserves truth. `down`: substituting a value that entails the OLD one (a
"narrower" replacement) preserves truth. `non`: neither direction is
licensed in general - not used by any quantifier in the Phase-1 fragment
(see `Signature.lean`), kept only so `Polarity.compose` is total. -/
inductive Polarity where
  | up
  | down
  | non
  deriving DecidableEq, Repr, Inhabited

/-- Negation-shaped positions flip the polarity of everything beneath them
- not exercised by the Phase-1 fragment (no connective nesting is in
scope, see `Signature.lean`), but stated now since it's the general
operation `compose` specializes. -/
def Polarity.flip : Polarity → Polarity
  | .up => .down
  | .down => .up
  | .non => .non

/-- Composing polarity across nested positions (outer ∘ inner): `non`
absorbs, otherwise `up` passes the inner polarity through unchanged and
`down` flips it. Phase 1 never actually nests two positions - every rule
in `Signature.lean`'s table sits directly under one quantifier - so this
is unused by `Tactic.lean` today; it's included because `Position` in
`Trace.lean` is written as a path precisely so a later, deliberate
extension (e.g. substituting inside a conjunction, as `every_trans`'s
shape would need) has this operation ready rather than needing to be
invented under pressure. -/
def Polarity.compose : Polarity → Polarity → Polarity
  | .non, _ => .non
  | _, .non => .non
  | .up, p => p
  | .down, p => p.flip

end FraCaS.Section1.Monotonicity
