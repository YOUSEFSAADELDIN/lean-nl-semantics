/-!
# Common nouns as types

Following Chatzikyriakidis & Luo (JoLLI 2014, "Natural Language Inference
in Coq"; LACL 2016), common nouns (CNs) are interpreted as *types*, not as
predicates over a fixed domain of individuals. Subtyping between CNs
(`Man <: Human <: Animal`) is modelled with Lean's coercion mechanism
instead of Coq's `Coercion` declarations.

Declare only the *covering* edges of the CN hierarchy (a Hasse diagram) and
let `CoeTC` supply the transitive closure — do not also declare shortcut
edges (e.g. both `Man → Human → Animal` and a direct `Man → Animal`),
since Lean does not check that two coercion paths between the same types
agree, unlike Coq's ambiguous-path warning. Any file that relies on two
paths coinciding should add an explicit `rfl` (or `example ... := rfl`)
check for that fact.

Caveat (unverified on a live toolchain, see repo README): whether `@[coe]`
can be attached to an `axiom` constant directly, or needs the axiom
wrapped in a `def`, has not been checked against a running Lean/Mathlib
build in this environment.
-/
namespace MTT

/-- The universe of common nouns for this fragment. Extend per grammar
fragment; keep the hierarchy a DAG (no cycles) so `CoeTC` terminates. -/
axiom Animal : Type
axiom Human : Type
axiom Man : Type
axiom Woman : Type

@[coe] axiom Human.toAnimal : Human → Animal
@[coe] axiom Man.toHuman : Man → Human
@[coe] axiom Woman.toHuman : Woman → Human

instance : Coe Human Animal := ⟨Human.toAnimal⟩
instance : Coe Man Human := ⟨Man.toHuman⟩
instance : Coe Woman Human := ⟨Woman.toHuman⟩

/-- A one-place verb, typed at the widest CN it applies to. Predicates are
declared over the *supertype* precisely so that subtype arguments need a
coercion inserted — that insertion is the test that subtyping actually
works end to end. -/
axiom walk : Animal → Prop

axiom john : Man

/-- `walk john` only elaborates because Lean chains `Man → Human → Animal`
through the two `Coe` instances above (`CoeTC`). This is the smallest
possible regression test for the subtyping setup; keep it passing. -/
example : Prop := walk john

end MTT
