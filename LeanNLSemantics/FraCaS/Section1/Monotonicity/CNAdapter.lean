import LeanNLSemantics.MTT.CN
import LeanNLSemantics.FraCaS.Section1.GQ

/-!
# An adapter lemma from `MTT/CN.lean`'s subtyping lattice

`Signature.lean`'s own header names this exact possibility and leaves it
undone: an `Every`-shaped fact feeding the monotonicity reasoner "can
come from an explicit FraCaS premise, a hand-asserted lexical fact, or
(optionally, later) an adapter lemma from the MTT `CN`/`CNTag` subtyping
lattice in `MTT/CN.lean` ... That lattice is a possible future *source*
of such facts, never a dependency of the core reasoner." This file is
that adapter, exercised on two real Section 1 problems whose own
hand-asserted premise is a CN-subtyping fact in disguise:

- **`fracas_029`** (`Batch2.lean`) assumes `∀ x, leadingBusinessman x →
  businessman x` to run `every_mono_scope`. "Leading businessman" ⊆
  "businessman" is Adj+N ⊆ N — the same shape `bridge/LinglibBridge/
  Section5Pilot.lean`'s own `fracas_202`/`fracas_214` handle, except this
  one is a genuine edge on `CN.lean`'s own `CNTag`, in the main package,
  not a bridge-local tag type.
- **`fracas_044`** (`Batch3.lean`) assumes `Every (fun x => person x ∧
  portugal x) southernEurope` ("Portuguese people are Southern
  Europeans") to run `atMost_trans` — the project's own comment there
  calls this "a real subset argument". Same move: `.portugal ≤
  .southernEurope` is now a `CNTag` edge, not an assumed premise.

Both adapter lemmas are stated generically over any `{A : Type*}` paired
with a tagging function `kind : A → CNTag`, not hardcoded to `CN.lean`'s
own `Individual` — `Individual`'s `name : String` field makes it
genuinely infinite, so it cannot itself instantiate `fracas_044`'s own
`[Fintype A]` requirement (`AtMost`/cardinality need a finite domain);
a real fragment would supply its own finite, `CNTag`-tagged type instead,
the way `bridge/LinglibBridge/Section5Pilot.lean`'s `S5Individual` does
for Section 5. Genericizing over `kind` rather than committing to one
concrete domain is what makes these two lemmas actually reusable by
whatever concrete type a future fragment brings, matching `Signature.lean`'s
own framing of the lattice as a *source*, not a fixed dependency.
-/

namespace MTT

/-- `fracas_029`'s own assumed premise, now a proved fact about
`CN.lean`'s own `CNTag` lattice instead of a hand-asserted hypothesis:
the proof obligation (`.leadingBusinessman ≤ .businessman`) is
`decide`-checked, not assumed. -/
theorem leadingBusinessman_businessman_adapter {A : Type*} (kind : A → CNTag) :
    FraCaS.Section1.Every (fun x => kind x ≤ .leadingBusinessman)
      (fun x => kind x ≤ .businessman) :=
  fun _ hx => le_trans hx (by decide)

/-- `fracas_029`, re-derived: the subtyping premise `Batch2.lean`'s own
proof takes as a hypothesis is no longer a hypothesis at all — it's
`leadingBusinessman_businessman_adapter`, discharged from the lattice,
leaving only the genuinely external fact (who counts as a commissioner)
assumed, exactly as `Batch2.lean`'s own proof does. -/
theorem fracas_029_from_cn {A : Type*} (kind : A → CNTag) (commissioner : A → Prop) :
    FraCaS.Section1.Every commissioner (fun x => kind x ≤ .leadingBusinessman) →
      FraCaS.Section1.Every commissioner (fun x => kind x ≤ .businessman) :=
  fun h => FraCaS.Section1.every_mono_scope commissioner _ _ h
    (leadingBusinessman_businessman_adapter kind)

/-- `fracas_044`'s own "Portuguese people are Southern Europeans"
premise, now a proved fact: `.portugal ≤ .southernEurope` is a `CNTag`
edge. -/
theorem portugal_southernEurope_adapter {A : Type*} (kind : A → CNTag) :
    FraCaS.Section1.Every (fun x => (kind x ≤ .human) ∧ kind x ≤ .portugal)
      (fun x => kind x ≤ .southernEurope) :=
  fun _ h => le_trans h.2 (by decide)

/-- `fracas_044`, re-derived: `Batch3.lean`'s own third premise (the
Portugal/Southern-Europe inclusion) is gone, replaced by
`portugal_southernEurope_adapter`. The other two hypotheses stay exactly
as assumed as they are in `Batch3.lean` — cardinality bound and
committee membership are facts about this scenario, not the tag
lattice, and the lattice was never meant to supply those. -/
theorem fracas_044_from_cn {A : Type*} [Fintype A] (kind : A → CNTag)
    (n : Nat) (committee : A → Prop)
    [DecidablePred fun x => committee x ∧ kind x ≤ CNTag.southernEurope]
    [DecidablePred fun x => committee x ∧ kind x ≤ CNTag.portugal] :
    FraCaS.Section1.AtMost n committee (fun x => kind x ≤ .southernEurope) →
      FraCaS.Section1.Every committee (fun x => kind x ≤ .human) →
        FraCaS.Section1.AtMost n committee (fun x => kind x ≤ .portugal) :=
  fun hAtMost hEveryHuman =>
    FraCaS.Section1.atMost_trans n committee (fun x => kind x ≤ .portugal)
      (fun x => kind x ≤ .human) (fun x => kind x ≤ .southernEurope)
      hAtMost hEveryHuman (portugal_southernEurope_adapter kind)

end MTT
