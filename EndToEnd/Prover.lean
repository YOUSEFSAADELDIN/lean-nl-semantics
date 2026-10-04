import LeanNLSemantics.FraCaS.Section1.Monotonicity.BlindEvalCore
import EndToEnd.Quantifiers

/-!
# The end-to-end pipeline's prover

The tactic chain `EndToEnd/Scan.lean` runs on the end-to-end claims. It
starts from the hand-written corpus's evaluation chain
(`FraCaS/Section1/Monotonicity/BlindEvalCore.lean`'s `attemptClose`) and
adds what was found to be needed for claims translated automatically from
FraCaS's English:

- `mono_nl_upward`: `mono_nl` with its opt-in `(AtLeast, scope)`
  conditioned-narrowing rule switched on (FraCaS 27);
- `blind_aesop_e2e`: `blind_aesop` plus `more_some`, `atLeast_trans` and
  `atLeast_mono_scope_conditioned`;
- `blind_count`: counting arguments over `AtLeast`/`AtMost`/`Exactly`/
  `More`, by unfolding them and calling `omega` (FraCaS 232).

Each was added after seeing a specific end-to-end claim fail, so the
end-to-end scores are development-set figures. Keeping them here, not in
`attemptClose`, means none of it can change the hand-written corpus's
evaluation, which keeps `attemptClose` exactly as it stood before the
end-to-end work began.
-/

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace FraCaS.EndToEnd

/-- `mono_nl` with the `(AtLeast, scope)` conditioned-narrowing fallback
enabled (`searchMonoNl`'s `upwardConditioned`). -/
elab "mono_nl_upward" : tactic => do
  liftMetaTactic1 fun goal => do
    if ← FraCaS.Section1.Monotonicity.searchMonoNl (fun _ => pure #[]) goal
        (upwardConditioned := true) then
      return none
    else
      throwError "mono_nl_upward: goal is outside the monotonicity fragment"

set_option hygiene false in
/-- `blind_aesop` (`BlindEvalCore.lean`) with three more lemmas: see this
file's header. -/
macro "blind_aesop_e2e" : tactic => `(tactic|
  aesop
    (add norm unfold FraCaS.Section1.Every, norm unfold FraCaS.Section1.Some,
      norm unfold FraCaS.Section1.No,
      unsafe 50% apply FraCaS.Section1.entails_and, unsafe 50% apply FraCaS.Section1.entails_refl,
      unsafe 50% apply FraCaS.Section1.some_entails_and,
      unsafe 50% apply FraCaS.Section1.entails_narrow,
      unsafe 50% apply FraCaS.Section1.every_some,
      unsafe 50% apply FraCaS.Section1.some_of_nonempty,
      unsafe 50% apply FraCaS.Section1.every_trans, unsafe 50% apply FraCaS.Section1.every_mp,
      norm simp FraCaS.Section1.no_iff_not_some,
      unsafe 50% apply FraCaS.Section1.atLeast_some, unsafe 50% apply FraCaS.Section1.most_some,
      unsafe 50% apply FraCaS.EndToEnd.more_some,
      unsafe 50% apply FraCaS.Section1.some_mono_scope,
      unsafe 50% apply FraCaS.Section1.every_mono_scope,
      unsafe 50% apply FraCaS.Section1.atLeast_mono_scope,
      unsafe 50% apply FraCaS.Section1.some_trans, unsafe 50% apply FraCaS.Section1.most_trans,
      unsafe 50% apply FraCaS.Section1.atMost_trans,
      unsafe 50% apply FraCaS.EndToEnd.atLeast_trans,
      unsafe 50% apply FraCaS.Section1.atMost_mono_scope,
      unsafe 50% apply FraCaS.Section1.atMost_mono_scope_conditioned,
      unsafe 50% apply FraCaS.Section1.atLeast_mono_scope_conditioned,
      unsafe 50% apply FraCaS.Section1.some_restrict,
      unsafe 50% apply FraCaS.Section1.every_restrict,
      unsafe 50% apply FraCaS.Section1.atLeast_restrict,
      unsafe 50% apply FraCaS.Section1.atMost_restrict,
      unsafe 50% apply FraCaS.Section2.exactly_ne,
      unsafe 50% apply FraCaS.Section2.exactly_pos_not_no,
      unsafe 50% apply FraCaS.Section2.some_of_exactly,
      unsafe 50% apply FraCaS.Section2.exactly_atLeast,
      unsafe 50% apply FraCaS.Section2.exactly_atMost,
      unsafe 50% apply FraCaS.Section2.every_most))


set_option hygiene false in
/-- Counting arguments: unfold the cardinality quantifiers (`AtLeast`/
`AtMost`/`Exactly`/`More`, all `abbrev`s for comparisons of `card`s) and
hand the resulting linear arithmetic over the `card` atoms to `omega` -
FraCaS 232's "ITEL won more orders than APCOM did, APCOM won ten orders
⊢ ITEL won at least eleven orders". -/
macro "blind_count" : tactic => `(tactic|
  (intros; (try simp only [FraCaS.EndToEnd.More, FraCaS.Section1.AtLeast,
    FraCaS.Section1.AtMost, FraCaS.Section2.Exactly] at *); omega))

-- Canaries: each fails the build if its tactic stops closing the exact
-- shape the pipeline generates for the problem named.
example {A : Type} (P Q : A → Prop) (x : A) :
    FraCaS.Section1.Every P Q → P x → Q x := by blind_aesop_e2e
-- FraCaS 232, both readings of "ten"
example {A : Type} [Fintype A] (order : A → Prop) [DecidablePred order]
    (win : A → A → Prop) [DecidableRel win] (itel apcom : A) :
    FraCaS.EndToEnd.More order (win itel) (win apcom) →
    FraCaS.Section1.AtLeast 10 order (win apcom) →
    FraCaS.Section1.AtLeast 11 order (win itel) := by blind_count
example {A : Type} [Fintype A] (order : A → Prop) [DecidablePred order]
    (win : A → A → Prop) [DecidableRel win] (itel apcom : A) :
    FraCaS.EndToEnd.More order (win itel) (win apcom) →
    FraCaS.Section2.Exactly 10 order (win apcom) →
    FraCaS.Section1.AtLeast 11 order (win itel) := by blind_count
-- FraCaS 27
example {A : Type} [Fintype A] (n : Nat) (committee sweden person scandinavia : A → Prop)
    [DecidablePred fun x => committee x ∧ sweden x]
    [DecidablePred fun x => committee x ∧ scandinavia x] :
    FraCaS.Section1.AtLeast n committee sweden → FraCaS.Section1.Every committee person →
      FraCaS.Section1.Every (fun x => person x ∧ sweden x) scandinavia →
        FraCaS.Section1.AtLeast n committee scandinavia := by mono_nl_upward

open FraCaS.Section1.Monotonicity in
/-- The end-to-end chain: the steps of `attemptClose`, in the same order,
with `mono_nl_upward` for `mono_nl` and `blind_aesop_e2e` for
`blind_aesop`, then `blind_count` last. -/
def attemptCloseEndToEnd (ty : Expr) : Lean.Elab.Term.TermElabM Bool := do
  if ← runTacticBool ty (← `(tactic| mono_nl_upward)) then return true
  if ← runTacticBool ty (← `(tactic| exist_nl)) then return true
  if ← runTacticBool ty (← `(tactic| mono_nl_compose)) then return true
  if ← runTacticBool ty (← `(tactic| most_nl)) then return true
  if ← runTacticBool ty (← `(tactic| every_most_nl)) then return true
  if ← runTacticBool ty (← `(tactic| blind_aesop_e2e)) then return true
  if ← runTacticBool ty (← `(tactic| blind_aesop_unfold)) then return true
  if ← runTacticBool ty (← `(tactic| grind)) then return true
  if ← runTacticBool ty (← `(tactic| blind_grind)) then return true
  if ← runTacticBool ty (← `(tactic| (intros; omega))) then return true
  if ← runTacticBool ty (← `(tactic| blind_count)) then return true
  return false

end FraCaS.EndToEnd
