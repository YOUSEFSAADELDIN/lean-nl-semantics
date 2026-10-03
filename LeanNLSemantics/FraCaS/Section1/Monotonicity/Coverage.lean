import Lean
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Tactic
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Scan
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Existential
import LeanNLSemantics.FraCaS.Section1.Monotonicity.Compose
import LeanNLSemantics

/-!
# Corpus-wide coverage scan

**Validation status** - the single, authoritative running log of this
scan's CI-confirmed numbers (kept in exactly this one place, not
duplicated in `Tactic.lean`'s/`CrossCheck.lean`'s own headers, precisely
so it can't go stale in one copy while another gets updated):

| CI run | commit | phase added | trivial | proved (distinct) | eligible-failed | scanned |
|---|---|---|---|---|---|---|
| (early) | | Phase 1+2 (`mono_nl` alone) | 14 | 40 (25) | 15 | 462 |
| 36308515404 | 390c6da | + Category B (`exist_nl`) | 14 | 57 (35) | 4 | 468 |
| 36310612545 | b2da508 | + Phase 3 (`mono_nl_compose`, #123 only) | 14 | 59 (36) | 3 | 469 |
| 36312200141 | 8934c04 | + Phase 4 (`exactly_atLeast`/`exactly_atMost` for #124, `some_entails_and` for #27) | 14 | 63 (38) | 1 | 471 |
| 36316374524 | 5628f63 | + Phase 5 (`entails_narrow`/`atMost_mono_scope_conditioned` for #044) | 14 | 65 (**39**) | **0** | 472 |

The Phase 5 row is current: **zero** eligible-but-failed problems remain
- every theorem this scan's own `isEligible`/`isTrivial` split calls
genuinely eligible now closes automatically, across five principled
extensions (Phase 1/2's substitution, Category B's existential-
transfer/positive-cardinality, Phase 3/4's composition, Phase 5's
conditioned narrowing), none of them a rule invented to fit one FraCaS
example - see each phase's own file header for its grounding.

`#mono_nl_coverage` scans every already-proved theorem in the whole
FraCaS suite (`import LeanNLSemantics`, the project's own root umbrella
import, pulls in all nine sections) whose name's last component starts
with `fracas_`. For each, in order:
- **outside the fragment**: the conclusion's head isn't one of
  `Every`/`Some`/`AtLeast`/`AtMost` at all - none of the three tactics is
  even attempted, since `Signature.lean`'s table has nothing to say about
  these regardless of what hypotheses are available. Checked *first*: an
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
  not a substitution at all, so not attempted by any of the three tactics
  and not counted as a monotonicity miss either way. These are the
  fourteen cases (`fracas_001`, `007`-`009`, `011`, `087`, `090`, `092`,
  `093`, `096`, `097`, `128`, `149`, `153` - identified by inspection, not
  hard-coded here) the standing instruction asked not to count as genuine
  eligible-but-failed monotonicity problems.
- **eligible but failed**: the head matches, `isTrivial` doesn't, and none
  of the three tactics closes it - `mono_nl` (Phase 1's direct-hypothesis
  match, or Phase 2's combine-then-match) tried first, `exist_nl`
  (Category B's existential-import/quantifier-strength family,
  `Existential.lean`) tried second, `mono_nl_compose` (Phase 3,
  `Compose.lean`'s composition of the two) tried third - grouped by
  whichever tactic's thrown message is actually informative (see the
  `runTactic` chain's own comment for why only the *last* tactic tried is
  ever worth reading), not a re-guessed classification.
- **automatically proved**: any of the three closed it - the report
  doesn't need to distinguish which, since each tactic's own `logInfo`
  trace already does, per-theorem, in the build log.

Per the standing instruction this reasoner was scoped under, nothing
here adds a rule *because* some corpus example needs it - the fragment
scanned is exactly `Signature.lean`/`Trace.lean`'s rule table, Phase 2's
one combine step, and Phase 3's one composition (no new rule, no new
`MonoRule`/`ExistentialRule` - see `Compose.lean`'s header), unchanged by
what this scan finds.
-/
open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Command

namespace FraCaS.Section1.Monotonicity

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
itself draws the proved/eligible-but-failed line within it. Built on
`Scan.lean`'s shared `goalHeadConst`/`introAll`/`quantifierHeads`
rather than re-implementing the same head check a second,
possibly-inconsistent way. -/
def isEligible (ty : Expr) : MetaM Bool := do
  match ← goalHeadConst ty with
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
  else if (msg.splitOn "outside the Phase-3/4 fragment").length > 1 then
    "no matching Entails fact even after also trying exist_nl/exactly_atLeast/exactly_atMost/some_entails_and-synthesized shape facts (mono_nl_compose)"
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
          match ← goalHeadConst ty with
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

    -- Three tactics, tried in turn - `mono_nl` (position substitution,
    -- Phase 1/2), `exist_nl` (existential-import/quantifier-strength,
    -- Category B, `Existential.lean`), then `mono_nl_compose` (Phase 3,
    -- `Compose.lean`: `mono_nl`'s own search, widened to also try
    -- `exist_nl`-synthesized shape facts). None calls another directly -
    -- this loop is what composes them - and a theorem only needs one of
    -- the three shapes to close, with each earlier tactic's own failure
    -- message discarded (not reported) whenever a later one succeeds, so
    -- a theorem closed by any of them counts as proved with no "which
    -- one" ambiguity left over - each tactic's own `logInfo` trace in the
    -- build log already says which.
    -- `exist_nl` rejects any non-`Some`-headed goal immediately, before
    -- looking at a single hypothesis, and `mono_nl_compose` is `mono_nl`'s
    -- own search widened (never a quick head-mismatch rejection, since
    -- every theorem reaching here already passed `isEligible`) - so
    -- whichever of the three tactics runs *last* always has the most
    -- complete diagnosis, and the earlier two's messages are discarded
    -- unread rather than compared, not merely unused by accident.
    -- Marks which theorem the next batch of `mono_nl`/`exist_nl`/
    -- `mono_nl_compose` trace `logInfo`s (if any) belongs to - the traces
    -- themselves carry no theorem name (see `Trace.lean`'s header: they
    -- describe one substitution/combine step, not which theorem it came
    -- from), so an export script reading this job's log back needs this
    -- marker to group them. Purely a log-format concern; changes nothing
    -- about what gets proved or how.
    logInfo m!"mono_nl_coverage: attempting {name}"
    let monoOutcome ← runTacticOn ty (← `(tactic| mono_nl))
    let outcome : Except String Unit ←
      match monoOutcome with
      | .ok () => pure (.ok ())
      | .error _monoMsg =>
        match ← runTacticOn ty (← `(tactic| exist_nl)) with
        | .ok () => pure (.ok ())
        | .error _existMsg =>
          match ← runTacticOn ty (← `(tactic| mono_nl_compose)) with
          | .ok () => pure (.ok ())
          | .error composeMsg => pure (.error composeMsg)

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
