import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics

/-!
# Corpus-wide coverage scan

**Validation status**: the first version of this scan ran in CI (run
36297683676) and reported a bare two-way split (32 supported / 427 not,
out of 459 FraCaS theorems - more than 342 since this counts every
`fracas_`-named theorem declaration, including `_dir1`/`_dir2`
countermodel pairs and this file's own `_via_mono_nl` cross-checks, not
one row per FraCaS problem id). That answered "how many," not "why the
rest didn't" - this version adds the three-way split and per-reason
grouping asked for next, on top of the same scan, not a new one:
`isEligible` (below) draws the eligible/outside-fragment line
independently of whether `mono_nl`'s search actually succeeds, and a
failed `mono_nl` call's own thrown message (previously discarded by a
bare `catch _ => pure false`) is now kept and grouped, so an eligible
failure's real cause is visible rather than folded into "unsupported."
Awaiting a CI run of *this* version before treating its three-way counts
as confirmed - the two-way split from the first run is the only number
already kernel-checked as of this writing.

`#mono_nl_coverage` scans every already-proved theorem in the whole
FraCaS suite (`import LeanNLSemantics`, the project's own root umbrella
import, pulls in all nine sections) whose name's last component starts
with `fracas_`. For each:
- **outside the fragment**: after introducing its implication chain, the
  conclusion's head isn't one of `Every`/`Some`/`AtLeast`/`AtMost` at
  all (`No`/`Most`-headed goals, `Iff`/`And`/`Not`/`Eq`-shaped
  statements, countermodel conjunctions, etc.) - `mono_nl` is never even
  attempted, since `Signature.lean`'s table has nothing to say about
  these regardless of what hypotheses are available.
- **eligible but failed**: the head matches, but `mono_nl`'s own search
  didn't find a single differing position with a matching `Entails`
  fact - grouped by *why*, using `mono_nl`'s own thrown message rather
  than a re-guessed classification.
- **automatically proved**: `mono_nl` closed it.

Per the standing instruction this reasoner was scoped under, nothing
here adds a rule *because* some corpus example needs it - the fragment
scanned is exactly `Signature.lean`/`Trace.lean`'s already-fixed
eight-rule table, unchanged by what this scan finds.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Command

namespace FraCaS.Section1.Monotonicity

/-- The last component of a (possibly namespaced) declaration name, as a
plain string - e.g. `FraCaS.Section3.fracas_114` ↦ `"fracas_114"`. -/
def lastComponent (n : Lean.Name) : String :=
  (toString n).splitOn "." |>.getLast!

/-- Whether a theorem's own conclusion, after introducing its
implication chain, is headed by one of the four quantifiers the
Phase-1 fragment covers at all - independent of whether `mono_nl`'s own
search then succeeds. This is the eligible/outside-fragment line;
`mono_nl` itself draws the proved/eligible-but-failed line within it.
Reuses `introAll`/`quantifierHeads` from `Tactic.lean` rather than
re-implementing the same head check a second, possibly-inconsistent
way. -/
def isEligible (ty : Expr) : MetaM Bool := do
  let mvar ← mkFreshExprMVar ty (kind := .synthetic)
  let (_, goal) ← introAll mvar.mvarId!
  goal.withContext do
    match (← goal.getType).getAppFn.constName? with
    | some n => return (quantifierHeads.lookup n).isSome
    | none => return false

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
named reasons, using `Tactic.lean`'s own fixed error strings rather than
inventing a new classification - anything not matching one of
`mono_nl`'s own known failure messages falls into "other," tagged with
its own first line so distinct "other" causes stay distinguishable
without exploding into one bucket per theorem. -/
def reasonBucket (msg : String) : String :=
  if (msg.splitOn "outside the Phase-1 monotonicity fragment").length > 1 then
    "no single differing position had a matching Entails fact"
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

elab "#mono_nl_coverage" : command => liftTermElabM do
  let env ← getEnv
  let mut proved : Array Lean.Name := #[]
  let mut eligibleFailedBuckets : Array (String × Array Lean.Name) := #[]
  let mut outsideFragment : Array Lean.Name := #[]
  let mut outsideHeadBuckets : Array (String × Array Lean.Name) := #[]

  for (name, info) in env.constants.toList do
    unless (lastComponent name).startsWith "fracas_" do continue
    unless info.isTheorem do continue
    let ty := info.type

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
  let total := proved.size + eligibleFailedCount + outsideFragment.size

  logInfo m!"mono_nl coverage: {proved.size} automatically proved, \
    {eligibleFailedCount} eligible but failed, {outsideFragment.size} outside the fragment, \
    out of {total} FraCaS theorems scanned"
  logInfo m!"proved [{proved.size}]: {proved.toList}"
  for (reason, names) in eligibleFailedBuckets do
    logInfo m!"eligible but failed [{names.size}] - {reason}: {names.toList}"
  logInfo m!"outside the fragment, by conclusion head:"
  for (head, names) in outsideHeadBuckets do
    logInfo m!"  {head} [{names.size}]: {names.toList}"

end FraCaS.Section1.Monotonicity

#mono_nl_coverage
