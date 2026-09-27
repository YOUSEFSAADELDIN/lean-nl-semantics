import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics

/-!
# Corpus-wide coverage scan

**Validation status**: the two-way (32/427) and three-way (32/34/393)
splits below have each been confirmed once in CI (runs 36297683676 and
36298768378). This version adds a fourth bucket - `trivial` - carved out
of what was "eligible but failed," and re-targets `reasonBucket` at
`Tactic.lean`'s Phase-2 message text; it also now measures Phase 2's
`entails_and`/`entails_refl` combine step, added at the same time. None
of *this* version's counts are confirmed yet - awaiting the next CI run
before treating them as real, the same discipline every earlier version
of this file held to.

`#mono_nl_coverage` scans every already-proved theorem in the whole
FraCaS suite (`import LeanNLSemantics`, the project's own root umbrella
import, pulls in all nine sections) whose name's last component starts
with `fracas_`. For each, in order:
- **trivial**: the goal is already exactly one hypothesis's own type (an
  `id`-shaped restatement), or one conjunct of an `And`-headed hypothesis
  (a `.1`/`.2`-shaped projection) - not a substitution at all, so not
  attempted by `mono_nl` and not counted as a monotonicity miss either
  way. `isTrivial` draws this line *before* eligibility is even checked,
  per the standing instruction that these fourteen cases (`fracas_001`,
  `007`-`009`, `011`, `087`, `090`, `092`, `093`, `096`, `097`, `128`,
  `149`, `153` - identified by inspection, not hard-coded here) shouldn't
  be counted as genuine eligible-but-failed monotonicity problems.
- **outside the fragment**: (checked on what's left) the conclusion's
  head isn't one of `Every`/`Some`/`AtLeast`/`AtMost` at all - `mono_nl`
  is never attempted, since `Signature.lean`'s table has nothing to say
  about these regardless of what hypotheses are available.
- **eligible but failed**: the head matches, but `mono_nl`'s own search
  (Phase 1's direct-hypothesis match, or Phase 2's combine-then-match)
  didn't find a fact - grouped by `mono_nl`'s own thrown message, not a
  re-guessed classification.
- **automatically proved**: `mono_nl` closed it, whether via a direct
  fact (Phase 1) or a combined one (Phase 2) - the report doesn't need to
  distinguish which, since `Tactic.lean`'s own `logInfo` trace already
  does, per-theorem, in the build log.

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
  else if (msg.splitOn "tactic left goals open").length > 1 then
    "mono_nl closed the goal only partially"
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

    let trivialHere ← try isTrivial ty catch _ => pure false
    if trivialHere then
      trivial := trivial.push name
      continue

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

    let outcome : Except String Unit ←
      try
        let mvar ← mkFreshExprMVar ty (kind := .synthetic)
        let remaining ← Lean.Elab.Tactic.run mvar.mvarId! do
          Lean.Elab.Tactic.evalTactic (← `(tactic| mono_nl))
        if remaining.isEmpty then
          pure (.ok ())
        else
          pure (.error "tactic left goals open")
      catch e =>
        let msg ← renderException e
        pure (.error msg)

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
