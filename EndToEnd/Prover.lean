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
  `More`, by unfolding them and calling `omega` (FraCaS 232);
- `blind_exactly_no`: a nonzero exact count refutes `No` (FraCaS 105,
  106);
- `blind_refute_count`: refutes a positive count, at least or exactly,
  by refuting `Some` (FraCaS 46).

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

/-- `exactly_pos_not_no` with the nonzero count built into its statement,
so `apply` needs no side goal. -/
theorem exactly_succ_not_no {A : Type*} [Fintype A] (n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] (h : FraCaS.Section2.Exactly (n + 1) P Q) :
    ¬ FraCaS.Section1.No P Q :=
  FraCaS.Section2.exactly_pos_not_no (n + 1) P Q (Nat.succ_ne_zero n) h

/-- A nonzero exact count refutes "no" - FraCaS 105/106's "just one
accountant attended ⊢ not no accountant(s) attended". `blind_aesop_e2e`
has the lemma but unfolds `No` before it can apply it. -/
macro "blind_exactly_no" : tactic => `(tactic|
  (intros; apply FraCaS.EndToEnd.exactly_succ_not_no; assumption))

/-- To refute a positive count, refute `Some`. -/
theorem not_atLeast_succ_of {A : Type*} [Fintype A] (n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] (h : FraCaS.Section1.Some P Q → False) :
    ¬ FraCaS.Section1.AtLeast (n + 1) P Q :=
  fun hc => h (FraCaS.Section1.atLeast_some (n + 1) P Q (Nat.succ_pos n) hc)

/-- The same for an exact positive count ("one of the commissioners" on
its exact reading). -/
theorem not_exactly_succ_of {A : Type*} [Fintype A] (n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] (h : FraCaS.Section1.Some P Q → False) :
    ¬ FraCaS.Section2.Exactly (n + 1) P Q :=
  fun hc => h (FraCaS.Section2.some_of_exactly (n + 1) P Q (Nat.succ_ne_zero n) hc)

/-- "Neither P" presupposes two `P`s, so there is one. -/
theorem exists_of_neither {A : Type*} [Fintype A] (P Q : A → Prop) [DecidablePred P]
    (h : FraCaS.Section1.Neither P Q) : ∃ x, P x := by
  have hpos : 0 < FraCaS.Section1.card P := by have := h.1; omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter] at hx
  exact ⟨x, hx.2⟩

/-- A positive count (at least or exactly) refuted by `No`/`Neither` and
the background facts - FraCaS 46's "neither commissioner spends time at
home ⊢ not one of the commissioners spends a lot of time at home", on both
readings of "one". The hypothesis's partitive presupposes commissioners,
which the "no" claim must establish too (`gen_claims.py`); `Neither`
presupposes them. `Neither` is then unfolded: `blind_aesop_e2e` does not
see through it to its `No`. -/
macro "blind_refute_count" : tactic => `(tactic|
  (intros
   (try refine ⟨FraCaS.EndToEnd.exists_of_neither _ _ (by assumption), ?_⟩)
   (try simp only [FraCaS.Section1.Neither] at *)
   first
     | apply FraCaS.EndToEnd.not_atLeast_succ_of
     | apply FraCaS.EndToEnd.not_exactly_succ_of
   first
     | (intro hs; obtain ⟨x, hx₁, hx₂⟩ := hs; (try simp only [FraCaS.Section1.No] at *); grind)
     | blind_aesop_e2e))

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

-- FraCaS 105, in the exact shape the generator emits
example {A : Type} [Fintype A] (accountant attendMeeting : A → Prop) [DecidablePred accountant]
    [DecidablePred attendMeeting] :
    FraCaS.Section2.Exactly 1 accountant attendMeeting →
      ¬ FraCaS.Section1.No accountant attendMeeting := by blind_exactly_no

-- FraCaS 46, both readings of "one of", in the exact shape the generator emits
example {A : Type} [Fintype A] (commissioner spendTimeAtHome spendALotOfTimeAtHome : A → Prop)
    [DecidablePred commissioner] [DecidablePred spendTimeAtHome] [DecidablePred spendALotOfTimeAtHome] :
    (∀ x, spendALotOfTimeAtHome x → spendTimeAtHome x) → FraCaS.Section1.Neither commissioner spendTimeAtHome →
      (∃ y, commissioner y) ∧ ¬ FraCaS.Section1.AtLeast 1 commissioner spendALotOfTimeAtHome := by
  blind_refute_count
example {A : Type} [Fintype A] (commissioner spendTimeAtHome spendALotOfTimeAtHome : A → Prop)
    [DecidablePred commissioner] [DecidablePred spendTimeAtHome] [DecidablePred spendALotOfTimeAtHome] :
    (∀ x, spendALotOfTimeAtHome x → spendTimeAtHome x) → FraCaS.Section1.Neither commissioner spendTimeAtHome →
      (∃ y, commissioner y) ∧ ¬ FraCaS.Section2.Exactly 1 commissioner spendALotOfTimeAtHome := by
  blind_refute_count

-- Event order (`EndToEnd/readings.py`'s `_ordered`): FraCaS 261's chain
-- of "before"s and 264's "before" ⇒ "after", in the exact shape the
-- generator emits; `grind` (already in the chain) must close both.
example {A : Type} (leave : A → Prop) (leaveTime : A → ℕ) (smith jones anderson : A) :
    (leave smith ∧ leaveTime smith < leaveTime jones) →
    (leave jones ∧ leaveTime jones < leaveTime anderson) →
    (leave smith ∧ leaveTime smith < leaveTime anderson) := by grind
example {A : Type} (leave : A → Prop) (leaveTime : A → ℕ) (smith jones : A) :
    leave smith → leave jones → (leave smith ∧ leaveTime smith < leaveTime jones) →
    (leave jones ∧ leave smith ∧ leaveTime jones > leaveTime smith) := by grind

open FraCaS.Section1.Monotonicity in
/-- The end-to-end chain: the steps of `attemptClose`, in the same order,
with `mono_nl_upward` for `mono_nl` and `blind_aesop_e2e` for
`blind_aesop`, then `blind_count`, `blind_exactly_no` and
`blind_refute_count` last. -/
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
  if ← runTacticBool ty (← `(tactic| blind_exactly_no)) then return true
  if ← runTacticBool ty (← `(tactic| blind_refute_count)) then return true
  return false

end FraCaS.EndToEnd
