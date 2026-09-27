import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Existential
import LeanNLSemantics

/-!
# Corpus-wide coverage scan

**Validation status**: the corrected four-way split (14 trivial / 40
proved / 15 eligible-but-failed / 393 outside-fragment, out of 462) is
CI-confirmed (run 36300667468) for `mono_nl` alone (Phase 1 + 2). This
version adds `exist_nl` (Category B, `Existential.lean`) as a second
tactic tried whenever `mono_nl` fails, before a theorem is counted
eligible-but-failed. One bug found and fixed once the main build finally
went green end-to-end (`Existential.lean`'s own fix took five attempts
first): `runTactic`'s local `Lean.Elab.Tactic.run mvar.mvarId! (evalTactic
...)` call was annotated `MetaM (Except String Unit)`, but
`Lean.Elab.Tactic.run` returns `TermElabM (List MVarId)` - the identical
mismatch `Existential.lean`'s `applyWithDecidableSide` hit originally.
Unlike there, no rewrite was needed: this whole scan already runs inside
`liftTermElabM do ...` (the command elaborator below), so `TermElabM` was
already available - `runTactic` just needed its own annotation corrected
to match, not a different implementation. Re-running the scan against
this corrected build is what will actually confirm the numbers below.

`#mono_nl_coverage` scans every already-proved theorem in the whole
FraCaS suite (`import LeanNLSemantics`, the project's own root umbrella
import, pulls in all nine sections) whose name's last component starts
with `fracas_`. For each, in order:
- **outside the fragment**: the conclusion's head isn't one of
  `Every`/`Some`/`AtLeast`/`AtMost` at all - `mono_nl` is never attempted,
  since `Signature.lean`'s table has nothing to say about these
  regardless of what hypotheses are available. Checked *first*: an
  earlier version of this scan checked `isTrivial` before eligibility and
  found it also caught theorems whose head has nothing to do with this
  fragment at all (an `Iff`/`Eq`/named-individual restatement elsewhere
  in the corpus) - inflating "trivial" well past the standing
  instruction's fourteen cases and understating "outside the fragment"
  to match. `isTrivial` is only meaningful *within* the eligible set, so
  it's only checked there now.
- **trivial**: (checked within what's eligible) the goal is already
  exactly one hypothesis's own type (an `id`-shaped restatement), or one
  conjunct of an `And`-headed hypothesis (a `.1`/`.2`-shaped projection) -
  not a substitution at all, so not attempted by `mono_nl` and not
  counted as a monotonicity miss either way. These are the fourteen cases
  (`fracas_001`, `007`-`009`, `011`, `087`, `090`, `092`, `093`, `096`,
  `097`, `128`, `149`, `153` - identified by inspection, not hard-coded
  here) the standing instruction asked not to count as genuine
  eligible-but-failed monotonicity problems.
- **eligible but failed**: the head matches, `isTrivial` doesn't, and
  neither tactic closes it - `mono_nl` (Phase 1's direct-hypothesis
  match, or Phase 2's combine-then-match) tried first, `exist_nl`
  (Category B's existential-import/quantifier-strength family,
  `Existential.lean`) tried second whenever `mono_nl` fails - grouped by
  whichever tactic's thrown message is actually informative (see
  `reasonBucket`'s own comment for why `exist_nl`'s generic "wrong head"
  rejection never overwrites a real `mono_nl` diagnosis), not a
  re-guessed classification.
- **automatically proved**: either tactic closed it - the report doesn't
  need to distinguish which, since each tactic's own `logInfo` trace
  already does, per-theorem, in the build log.

Per the standing instruction this reasoner was scoped under, nothing
here adds a rule *because* some corpus example needs it - the fragment
scanned is exactly `Signature.lean`/`Trace.lean`'s rule table plus
Phase 2's one combine step, unchanged by what this scan finds.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Command

namespace FraCaS.Section1.Monotonicity

/-- The last component of a (possibly namespaced) declaration name, as a
plain string - e.g. `FraCaS.Section3.fracas_114` ↦ `"fracas_114"`. -/
def lastComponent (n : Lean.Name) : String :=
  (toString n).splitOn "." |>.getLast!

/-- The underlying FraCaS problem number a theorem name names, regardless
of which variant proved it - `"fracas_018"` ↦ `some 18`,
`"fracas_066_via_mono_nl"` ↦ `some 66`, `"fracas_012_dir1"` ↦ `some 12`.
Used only to report *distinct problems* closed, not to drive any
decision `mono_nl` itself makes. -/
def problemId (n : Lean.Name) : Option Nat :=
  let s := lastComponent n
  if "fracas_".isPrefixOf s then
    (s.drop "fracas_".length |>.takeWhile Char.isDigit).toNat?
  else
    none

/-- Whether a theorem's own conclusion, after introducing its
implication chain, is headed by one of the four quantifiers the
fragment covers at all - independent of whether `mono_nl`'s own search
then succeeds. This is the eligible/outside-fragment line; `mono_nl`
itself draws the proved/eligible-but-failed line within it. Reuses
`introAll`/`quantifierHeads` from `Tactic.lean` rather than
re-implementing the same head check a second, possibly-inconsistent
way. -/
def isEligible (ty : Expr) : MetaM Bool := do
  let mvar ← mkFreshExprMVar ty (kind := .synthetic)
  let (_, goal) ← introAll mvar.mvarId!
  goal.withContext do
    match (← goal.getType).getAppFn.constName? with
    | some n => return (quantifierHeads.lookup n).isSome
    | none => return false

/-- Whether a theorem's goal, after introducing its implication chain, is
already exactly one hypothesis's own type (an `id`-shaped restatement),
or one conjunct of an `And`-headed hypothesis (a `.1`/`.2`-shaped
projection) - checked *before* `isEligible`/`mono_nl`, so these count as
their own bucket rather than as a monotonicity miss. Deliberately not a
`mono_nl` concern: neither shape is a position substitution at all
(there's nothing differing to substitute), so it isn't this fragment's
job to close them, and it isn't this fragment's failure that it doesn't. -/
def isTrivial (ty : Expr) : MetaM Bool := do
  let mvar ← mkFreshExprMVar ty (kind := .synthetic)
  let (_, goal) ← introAll mvar.mvarId!
  goal.withContext do
    let goalTy ← goal.getType
    let lctx ← getLCtx
    let hyps := lctx.decls.toList.filterMap id
      |>.filter (fun d => !d.isImplementationDetail)
    for h in hyps do
      if ← isDefEq h.type goalTy then return true
      match h.type with
      | .app (.app (.const ``And _) l) r =>
        if (← isDefEq l goalTy) then return true
        if (← isDefEq r goalTy) then return true
      | _ => pure ()
    return false

/-- The head constant name of an eligible-or-not goal's conclusion, for
the "outside the fragment" breakdown - `none` when it isn't even a named
application (e.g. a bare `∀`/`∃` left over from a definition unfolding,
or a `Prop` variable). -/
def concludingHead (ty : Expr) : MetaM (Option Lean.Name) := do
  let mvar ← mkFreshExprMVar ty (kind := .synthetic)
  let (_, goal) ← introAll mvar.mvarId!
  goal.withContext do
    return (← goal.getType).getAppFn.constName?

/-- Renders a caught tactic exception's message to plain text, for
grouping - falls back to a fixed string rather than propagating a second
failure if formatting itself somehow fails. -/
def renderException (e : Exception) : MetaM String :=
  try
    e.toMessageData.toString
  catch _ =>
    pure "<error message could not be rendered>"

/-- Buckets an eligible failure's raw message into a small number of
named reasons, using `Tactic.lean`'s own fixed error strings (updated for
its Phase-2 wording) rather than inventing a new classification -
anything not matching one of `mono_nl`'s own known failure messages falls
into "other," tagged with its own first line so distinct "other" causes
stay distinguishable without exploding into one bucket per theorem. -/
def reasonBucket (msg : String) : String :=
  if (msg.splitOn "outside the Phase-1/2 monotonicity fragment").length > 1 then
    "no single differing position had a matching (direct or combined) Entails fact"
  else if (msg.splitOn "could not read the restrictor/scope").length > 1 then
    "goal's argument shape not recognized (extractPQ arg-count mismatch)"
  else if (msg.splitOn "outside the Category-B fragment").length > 1 then
    "Some-headed, but no stronger-quantifier or Every-plus-witness match (exist_nl)"
  else if (msg.splitOn "tactic left goals open").length > 1 then
    "tactic closed the goal only partially"
  else
    "other: " ++ (msg.splitOn "\n").head?.getD msg

def addToBucket (buckets : Array (String × Array Lean.Name)) (key : String) (name : Lean.Name) :
    Array (String × Array Lean.Name) :=
  match buckets.findIdx? (·.1 == key) with
  | some idx => buckets.set! idx (key, buckets[idx]!.2.push name)
  | none => buckets.push (key, #[name])

def dedupNats (l : List Nat) : List Nat :=
  l.foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) []

elab "#mono_nl_coverage" : command => liftTermElabM do
  let env ← getEnv
  let mut trivial : Array Lean.Name := #[]
  let mut proved : Array Lean.Name := #[]
  let mut eligibleFailedBuckets : Array (String × Array Lean.Name) := #[]
  let mut outsideFragment : Array Lean.Name := #[]
  let mut outsideHeadBuckets : Array (String × Array Lean.Name) := #[]

  for (name, info) in env.constants.toList do
    unless (lastComponent name).startsWith "fracas_" do continue
    unless info.isTheorem do continue
    let ty := info.type

    -- Eligibility first, `isTrivial` only within it: checking `isTrivial`
    -- unconditionally over the whole corpus (an earlier version of this
    -- scan did) also caught theorems whose head has nothing to do with
    -- the monotonicity fragment at all (an `Iff`/`Eq`/named-individual
    -- restatement in, say, Section 4's ellipsis problems) - diluting
    -- "outside the fragment" and inflating "trivial" well past the
    -- fourteen cases this was meant to carve out of "eligible but
    -- failed." `trivial` is specifically "eligible in principle, but a
    -- restatement/projection rather than a real substitution question,"
    -- not "any theorem anywhere that happens to restate a hypothesis."
    let eligible ← try isEligible ty catch _ => pure false
    unless eligible do
      outsideFragment := outsideFragment.push name
      let headKey ←
        try
          match ← concludingHead ty with
          | some n => pure (toString n)
          | none => pure "<no named head>"
        catch _ =>
          pure "<error while inspecting head>"
      outsideHeadBuckets := addToBucket outsideHeadBuckets headKey name
      continue

    let trivialHere ← try isTrivial ty catch _ => pure false
    if trivialHere then
      trivial := trivial.push name
      continue

    -- Two independent tactics, tried in turn - `mono_nl` (position
    -- substitution, Phase 1/2) and `exist_nl` (existential-import/
    -- quantifier-strength, Category B, `Existential.lean`). Neither
    -- calls the other; a theorem only needs one of the two shapes to
    -- close, and `mono_nl`'s own failure message is discarded (not
    -- reported) whenever `exist_nl` goes on to succeed, so a theorem
    -- closed by either counts as proved with no "which one" ambiguity
    -- left over - Tactic.lean's/Existential.lean's own `logInfo` traces
    -- in the build log already say which.
    let runTactic (tacticStx : Lean.TSyntax `tactic) : TermElabM (Except String Unit) :=
      try
        let mvar ← mkFreshExprMVar ty (kind := .synthetic)
        let remaining ← Lean.Elab.Tactic.run mvar.mvarId! do
          Lean.Elab.Tactic.evalTactic tacticStx
        if remaining.isEmpty then
          pure (.ok ())
        else
          pure (.error "tactic left goals open")
      catch e =>
        let msg ← renderException e
        pure (.error msg)

    let monoOutcome ← runTactic (← `(tactic| mono_nl))
    let outcome : Except String Unit ←
      match monoOutcome with
      | .ok () => pure (.ok ())
      | .error monoMsg =>
        match ← runTactic (← `(tactic| exist_nl)) with
        | .ok () => pure (.ok ())
        | .error existMsg =>
          -- `exist_nl` rejects any non-`Some`-headed goal immediately,
          -- before looking at a single hypothesis - that boilerplate
          -- message would otherwise overwrite `mono_nl`'s own, more
          -- specific reason for every Every/AtLeast/AtMost-headed miss.
          -- Report it only when `exist_nl` actually engaged (the goal
          -- *was* `Some`-headed) and still came up empty.
          if (existMsg.splitOn "exist_nl only closes Some-headed goals").length > 1 then
            pure (.error monoMsg)
          else
            pure (.error existMsg)

    match outcome with
    | .ok () => proved := proved.push name
    | .error msg =>
      eligibleFailedBuckets := addToBucket eligibleFailedBuckets (reasonBucket msg) name

  let eligibleFailedCount := (eligibleFailedBuckets.map (·.2.size)).foldl (· + ·) 0
  let total := trivial.size + proved.size + eligibleFailedCount + outsideFragment.size
  let provedProblems := dedupNats ((proved.toList.map problemId).filterMap id)

  logInfo m!"mono_nl coverage: {trivial.size} trivial (not a monotonicity question), \
    {proved.size} automatically proved ({provedProblems.length} distinct FraCaS problems), \
    {eligibleFailedCount} eligible but failed, {outsideFragment.size} outside the fragment, \
    out of {total} FraCaS theorems scanned"
  logInfo m!"distinct FraCaS problems proved: {provedProblems}"
  logInfo m!"trivial [{trivial.size}]: {trivial.toList}"
  logInfo m!"proved [{proved.size}]: {proved.toList}"
  for (reason, names) in eligibleFailedBuckets do
    logInfo m!"eligible but failed [{names.size}] - {reason}: {names.toList}"
  logInfo m!"outside the fragment, by conclusion head:"
  for (head, names) in outsideHeadBuckets do
    logInfo m!"  {head} [{names.size}]: {names.toList}"

end FraCaS.Section1.Monotonicity

#mono_nl_coverage
