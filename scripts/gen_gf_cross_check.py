#!/usr/bin/env python3
"""Generate LeanNLSemantics/FraCaS/Section1/GFCrossCheckBatch.lean.

Extends `GFCrossCheck.lean`'s own single hand-written example (only
`fracas_002`'s first premise, cross-checked via `gf/translate.py`) to
every FraCaS problem whose *entire* set of premises and hypothesis
already has a real, CI-linearize-confirmed GF tree in
`gf/run_gf_tests.py`'s own `BASE_CHECKS` (so no new, unconfirmed GF tree
is introduced here - only trees the real GF toolchain has already
validated as correct English, via the `build-gf` CI job).

For each such problem, every premise/hypothesis tree is fed through
`translate_cl` (imported directly - `translate.py` is pure Python, no
GF toolchain needed at translation time), and a `fracas_NNN_from_gf`
theorem is emitted: same shape as `GFCrossCheck.lean`'s own example,
restating the theorem with `translate.py`'s own generated predicate/
individual names and proving it via `fun h1 h2 ... => fracas_NNN _ _
... h1 h2 ...` (predicate/individual args as `_`, hypotheses supplied
by name, in the real theorem's own declared order) - an earlier
`intros; apply fracas_NNN <;> assumption` version proved unreliable on
3+-premise compositions, where a predicate appearing only in a middle
premise (never the conclusion) was left as an unresolved metavariable
`assumption` could not reliably close in the needed order. Either way,
this only typechecks if the translated proposition's *shape* genuinely
matches the already-proved theorem's, same bar `GFCrossCheck.lean`'s
own single example already holds itself to.

Only problems with EVERY premise and the hypothesis all translating
without a Python-level error are attempted - `translate.py`'s own
already-documented gaps (a handful of determiner shapes, conjoined
subjects, `everyone_NP`) are skipped, not forced. Re-run this script
after `gf/run_gf_tests.py` or `gf/translate.py` change; do not hand-edit
the generated output.
"""
from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GF_DIR = ROOT / "gf"
OUT_PATH = ROOT / "LeanNLSemantics" / "FraCaS" / "Section1" / "GFCrossCheckBatch.lean"

sys.path.insert(0, str(GF_DIR))
from translate import Translation, translate_cl, parse_tree  # noqa: E402

CONFIRMED_STATUS = """\
**Validation status - CI-confirmed** (CI run TBD, commit TBD, branch
blind-eval-section1): all N generated theorems below type-check against
their already-proved fracas_NNN counterparts. See
`scripts/gen_gf_cross_check.py` for how this list was derived. If this
file's own theorem count no longer matches, this status is stale -
re-run the script and update this constant by hand."""


CONJUNCT_IDS = {89: ["_hypothesis_rep", "_hypothesis_client"]}


def _scope_aux(ps, h) -> str:
    """`(forall x, <premise's own scope> x -> <hypothesis's own scope> x)`
    - the "world-knowledge" fact a handful of `..._mono_scope`-proved
    theorems need beyond their one real FraCaS premise (e.g. "finishing
    on time entails finishing"), read directly off each real theorem's
    own stated type, not guessed. `free_predicates` is always
    `[*restrictor_preds, scope_name]` (`translate_cl`'s own uniform
    convention, checked directly against its source), so the scope is
    always the LAST entry. """
    return f"(∀ x, {ps[-1].free_predicates[-1]} x → {h.free_predicates[-1]} x)"


def _restrict_aux(ps, h) -> str:
    """`Every <premise's own restrictor> <hypothesis's own restrictor>`
    - the dual of `_scope_aux`, for theorems whose extra fact instead
    narrows/widens the RESTRICTOR while the scope stays fixed (e.g.
    "Irish delegate" subset of "delegate") - `some_restrict`/
    `every_restrict`/`atLeast_restrict`'s own shape. The restrictor is
    always the FIRST entry of `free_predicates`."""
    return f"Every {ps[-1].free_predicates[0]} {h.free_predicates[0]}"


def _scope_aux_rev(ps, h) -> str:
    """`(forall x, <hypothesis's own scope> x -> <premise's own scope> x)`
    - `_scope_aux` with the two scopes in the OPPOSITE order, for a `.no`
    theorem proved by `no_iff_not_some` + `some_mono_scope` (e.g.
    fracas_038: `No delegate finish -> (forall x, onTime x -> finish x)
    -> not Some delegate onTime`) - here the premise is the NEGATIVE
    ("No ... finish") and the aux fact has to entail the premise's own
    scope FROM the hypothesis's own (stronger) scope, the reverse
    direction of the positive `..._mono_scope` theorems `_scope_aux`
    covers (where the premise is positive and entails the hypothesis).
    Predicate NAMES never have to match the real theorem's own choice
    of variable names for this to typecheck (Lean unifies by position,
    not by spelling) - only this SHARING PATTERN does: whichever
    predicate the real theorem's own aux fact and premise share, or aux
    fact and hypothesis share, has to be the same single translate_cl
    predicate on this side too, confirmed by reading the real theorem's
    stated type directly, not assumed from premise/hypothesis English
    alone (this is exactly what tripped up fracas_069, excluded
    elsewhere in this file: there the real theorem shares ONE variable
    across premise and conclusion with no aux bridging it at all, a
    strictly different, incompatible shape from this one)."""
    return f"(∀ x, {h.free_predicates[-1]} x → {ps[-1].free_predicates[-1]} x)"


def _restrict_aux_rev(ps, h) -> str:
    """`Every <hypothesis's own restrictor> <premise's own restrictor>`
    - `_restrict_aux` with the two restrictors in the OPPOSITE order,
    for a `.no` theorem proved by `no_iff_not_some` + `some_restrict`
    where the PREMISE carries the wide restrictor and the hypothesis
    the narrow one (e.g. fracas_070: `No delegate finishOnTime -> Every
    scandinavianDelegate delegate -> not Some scandinavianDelegate
    finishOnTime`) - the reverse of `_restrict_aux`'s own cases (55/57/
    59/63), where the premise always carries the NARROW restrictor."""
    return f"Every {h.free_predicates[0]} {ps[-1].free_predicates[0]}"


# Ids needing exactly one extra hypothesis beyond their real FraCaS
# premises, and which of the four shapes above it takes - all read off
# each id's own real theorem source directly (see AssumptionAudit-style
# discipline throughout this project: confirmed, not assumed). Inserted
# right before the hypothesis in the arrow chain for every one of these -
# checked directly against each real theorem's own text, not assumed to
# be uniform.
AUX_HYPOTHESIS = {
    17: _scope_aux, 23: _scope_aux, 24: _scope_aux, 25: _scope_aux, 29: _scope_aux,
    55: _restrict_aux, 57: _restrict_aux, 59: _restrict_aux, 63: _restrict_aux,
    38: _scope_aux_rev,
    70: _restrict_aux_rev,
}

# Ids whose own single FraCaS premise translates to a CONJUNCTION (via
# `translate.py`'s `_try_translate_conjnp_subject`, "exactly two lawyers
# and three accountants signed" read distributively) but whose real
# theorem only needs ONE conjunct as its premise - 85 the first
# (lawyer) conjunct, 86 the second (accountant), confirmed by reading
# each real theorem's own stated type directly. Maps an id to (which
# premise position needs projecting, 1-based matching hN; which
# conjunct, 0-based matching `Translation.conjuncts`). The generated
# theorem's own STATED type keeps the full, faithful conjunction as
# that premise's type (only the proof term projects) - and, just as
# importantly, the real theorem's own predicate/individual ARITY is
# narrower than the full conjunction's (e.g. fracas_085 never mentions
# "accountant" in its stated type at all, so Lean's `variable` auto-
# inclusion never adds it as a parameter - confirmed by reading
# Batch1.lean's own `variable` scoping directly, not assumed from the
# conjunction's own merged predicate list), so the underscore count for
# THIS premise position is computed from the projected conjunct's own
# narrower `free_predicates`/`free_individuals`, not the merged ones.
PROJECT_CONJUNCT = {85: (1, 0), 86: (1, 1)}

# Section 3 pilot: ids 114/115/116 all share the single premise "Mary
# used her workstation", translated by `translate.py`'s
# `_try_translate_possessive_presupposition` into a three-way
# presupposition bundle (gender/has/verb). Each id's own real theorem
# is a straight projection out of that SAME bundle (Batch1.lean's own
# comment: "114/115/116 are then just projections out of the same
# bundle") - 114 the verb conjunct, 115 the has conjunct, 116 the
# gender conjunct (0-based, matching `Translation.conjuncts`'s own
# order) - confirmed by reading each real theorem's own stated type
# directly. Unlike PROJECT_CONJUNCT above, no proof-term projection is
# needed here: the real theorems (`fun h => h.2.2` etc.) already
# project internally, so the generated wrapper's own hypothesis is
# simply REPLACED with the matching conjunct (not independently
# re-translated from its own, differently-shaped hypothesis tree -
# "Mary has a workstation" read in isolation would otherwise get
# translate_cl's usual fused-unary-predicate treatment, structurally
# incompatible with the bundle's own binary `has owner possessed`).
BUNDLE_PROJECT = {114: 2, 115: 1, 116: 0}

# fracas_117/118's shared premise 1 ("every student used her
# workstation") and fracas_119's own premise 1 ("no student used her
# workstation") translate (via `translate.py`'s
# `_try_translate_bound_possessive_presupposition`) to a universally-
# quantified bundle whose parts are parameterized by the bound student
# variable, not concrete - exposed via that Translation's own
# `template`. Each id's real theorem instantiates ONE part at the
# SPECIFIC individual introduced by its OTHER premise ("Mary is a
# student") - 117 the verb part, 118 the has part, 119 the (negated)
# verb part again - confirmed by reading each real theorem's own stated
# type directly. Maps an id to (which premise holds the template,
# 1-based; which part: "gender"/"has"/"verb"). Like BUNDLE_PROJECT, the
# generated hypothesis is built directly from the template rather than
# independently re-translating each id's own differently-shaped
# hypothesis sentence ("Mary used her workstation"/"Mary used a
# workstation", both exactly as ambiguous in isolation as fracas_115's
# "Mary has a workstation" was).
SKOLEM_PROJECT = {117: (1, "verb"), 118: (1, "has"), 119: (1, "verb")}


def load_base_checks():
    spec = importlib.util.spec_from_file_location(
        "run_gf_tests", str(GF_DIR / "run_gf_tests.py")
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    # Section 3's own GF trees are written in the past tense (unlike
    # Section 1/2's bare, present-tense ones), so they live in
    # `_SECTION3_TENSED_CHECKS`, a separate module-level list from
    # `BASE_CHECKS` proper (only combined into `CHECKS`, used for the
    # real GF-toolchain verification run, at the bottom of
    # run_gf_tests.py) - not visible to this generator otherwise.
    return mod.BASE_CHECKS + mod._SECTION3_TENSED_CHECKS


def _load_problems_lean_entries():
    text = (ROOT / "LeanNLSemantics/FraCaS/Data/Problems.lean").read_text()
    pat = re.compile(
        r'\{\s*id\s*:=\s*(\d+),\s*premises\s*:=\s*(\[.*?\]),\s*hypothesis\s*:=\s*"[^"]*",'
        r"\s*answer\s*:=\s*\.(\w+)\s*\}",
        re.S,
    )
    return pat.findall(text)


def load_premise_counts():
    counts = {}
    for id_str, premises_text, _answer in _load_problems_lean_entries():
        counts[int(id_str)] = len(re.findall(r'"', premises_text)) // 2
    return counts


def load_answers():
    return {int(id_str): answer for id_str, _premises, answer in _load_problems_lean_entries()}


def load_bare_theorem_ids() -> set:
    """Which fracas_NNN ids have an actual bare (non-suffixed) theorem
    declaration anywhere in Section1/Section2/Section3 - several ids
    with full GF coverage turn out to be countermodel-only
    (`fracas_NNN_dir1`/`_dir2`, from this session's own earlier many/
    both/neither work), and would otherwise generate a reference to a
    theorem that doesn't exist at all, not just a shape mismatch."""
    ids = set()
    for section in ("Section1", "Section2", "Section3"):
        for path in (ROOT / f"LeanNLSemantics/FraCaS/{section}").glob("Batch*.lean"):
            for m in re.finditer(r"theorem fracas_(\d+) ", path.read_text()):
                ids.add(int(m.group(1)))
    return ids


def real_theorem_arrow_count(idn: int) -> "int | None":
    """The number of top-level (paren-depth-0) `->` arrows in fracas_NNN's
    own stated type - its true explicit-hypothesis arity. Several hand
    proofs (`AUX_HYPOTHESIS`'s own keys: 17/23/24/25/29 via
    `some_mono_scope`/`every_mono_scope`-style scope facts, 55/57/59/63
    via `some_restrict`/`every_restrict`/`atLeast_restrict`-style
    restrictor facts, 38/70 via the same two lemma families but with
    the premise/hypothesis roles reversed - a `.no` answer proved by
    `no_iff_not_some` composed with `some_mono_scope`/`some_restrict`)
    take an EXTRA hypothesis beyond one per FraCaS premise - a
    "world-knowledge" fact that isn't itself sourced from any distinct
    FraCaS premise sentence at all, so `len(premises)` (this script's
    default) undercounts them; `31` and `46` need one too but are
    excluded separately (see `AUX_HYPOTHESIS`'s own comment) since each
    one's own two trees collide on the same generated name. Only a real
    match here (not just a plausible-looking premise count) makes a
    problem eligible - confirmed by reading the actual Lean source, not
    assumed from Problems.lean's own premise list length. """
    for section in ("Section1", "Section2", "Section3"):
        for path in (ROOT / f"LeanNLSemantics/FraCaS/{section}").glob("Batch*.lean"):
            text = path.read_text()
            m = re.search(rf"theorem fracas_{idn:03d} :\s*(.*?):=", text, re.S)
            if m:
                depth = 0
                count = 0
                type_text = m.group(1)
                i = 0
                while i < len(type_text):
                    c = type_text[i]
                    if c == "(":
                        depth += 1
                    elif c == ")":
                        depth -= 1
                    elif c == "→" and depth == 0:
                        count += 1
                    i += 1
                return count
    return None


def premise_index(role: str) -> "tuple[int, str] | None":
    """('' or '_premise') -> (1, ''); '_premise2' -> (2, ''); '_premise1a' -> (1, 'a')."""
    if role == "" or role == "_premise":
        return (1, "")
    m = re.match(r"_premise(\d+)([ab]?)$", role)
    if m:
        return (int(m.group(1)), m.group(2))
    return None


def main() -> None:
    base_checks = load_base_checks()
    premise_counts = load_premise_counts()
    answers = load_answers()
    bare_theorem_ids = load_bare_theorem_ids()

    by_id: dict[int, dict[str, str]] = {}
    for label, cmd, _expected in base_checks:
        m = re.match(r"fracas_(\d+)(.*)", label)
        idn = int(m.group(1))
        role = m.group(2)
        assert cmd.startswith("linearize ")
        by_id.setdefault(idn, {})[role] = cmd[len("linearize ") :]

    emitted: list[int] = []
    skipped: dict[int, str] = {}
    lines = [
        "-- Generated by scripts/gen_gf_cross_check.py - do not hand-edit;",
        "-- re-run the script instead.",
        "import LeanNLSemantics.FraCaS.Section1.Batch1",
        "import LeanNLSemantics.FraCaS.Section1.Batch2",
        "import LeanNLSemantics.FraCaS.Section1.Batch3",
        "import LeanNLSemantics.FraCaS.Section1.Batch4",
        "import LeanNLSemantics.FraCaS.Section1.Batch5",
        "import LeanNLSemantics.FraCaS.Section2.Batch1",
        "import LeanNLSemantics.FraCaS.Section2.Batch2",
        "import LeanNLSemantics.FraCaS.Section3.Batch1",
        "import LeanNLSemantics.FraCaS.Section3.Batch2",
        "",
        "/-!",
        "# GF cross-check, batch 2",
        "",
        "Extends `GFCrossCheck.lean`'s own single example (only `fracas_002`'s",
        "first premise) to every problem whose full premise/hypothesis set",
        "already has a real, linearize-confirmed GF tree (`gf/run_gf_tests.py`)",
        "that `gf/translate.py` translates cleanly, where the real theorem's",
        "own top-level arrow count exactly matches (one arrow per premise,",
        "chaining into the hypothesis, plus a \"world-knowledge\" auxiliary",
        "hypothesis for ids in `AUX_HYPOTHESIS`) - now extended into Section 3",
        "as a pilot (ids 114-116 only - see `BUNDLE_PROJECT`): \"Mary used her",
        "workstation\" translates to a three-way presupposition bundle",
        "(`translate.py`'s `_try_translate_possessive_presupposition`),",
        "matching Batch1.lean's own comment that 114/115/116 are \"just",
        "projections out of the same bundle\" - each id's own generated",
        "hypothesis is that SAME bundle's matching conjunct, not an",
        "independent translation of its own (differently-shaped) hypothesis",
        "sentence, since that sentence read in isolation is genuinely",
        "ambiguous between this bundle's own specific reading and this",
        "project's usual fused-unary-predicate one (see `BUNDLE_PROJECT`'s",
        "own comment). Harder Section 3 constructions (Skolem functions,",
        "cross-sentential variable sharing, cardinality anaphora) are not",
        "attempted yet - see",
        "`scripts/gen_gf_cross_check.py` for exactly how, including the",
        "non-obvious exclusions it found and documents rather than silently",
        "omitting: problems 31 and 46 each need an aux hypothesis (like",
        "17/23-25/29, or 38/70's reverse-direction variant) but are excluded",
        "because their own premise and hypothesis trees collide on the same",
        "generated predicate name (`translate.py` doesn't read determiners",
        "like \"a lot of\" when naming a VP's object - \"spends time at home\"",
        "and \"spends a lot of time at home\" both fuse to `spendTimeHome`,",
        "where the real theorems need two DISTINCT predicates); problem 5",
        "needs an extra *nonempty-restrictor* premise (`hNonempty : ∃ x,",
        "ambitious x`) in a binder position this script's arrow-chain model",
        "doesn't cover; problem 69's hand proof uses the SAME bound variable",
        "for premise 1's own scope and the hypothesis's predicate, even",
        "though their surface text differs (\"can travel freely\" vs \"have",
        "the right to live\") and translate_cl correctly gives them different",
        "names - bridging that needs a composed proof, not just an extra",
        "hypothesis; problems 44/81/82/85/86/92 hit real, pre-existing",
        "`gf/translate.py` gaps (`few_Det`, `CountNP` partitives, conjoined",
        "subjects, bare-cardinal determiners, `everyone_NP`) rather than",
        "anything this script can paper over; and problems 101/102 (Section",
        "2's generics) have a hand proof that deliberately names a premise's",
        "own predicate the same as the hypothesis's (\"likelyPoorTrader\" for",
        "both) - a real semantic modeling choice a literal, compositional",
        "translator correctly does not reproduce on its own.",
        "-/",
        "",
        "open FraCaS.Section1 FraCaS.Section2 FraCaS.Section3",
        "",
        "-- Most/AtLeast/AtMost/Exactly need a DecidablePred instance per",
        "-- predicate/conjunction they apply to - a real theorem's own",
        "-- variable block always supplies one concretely (unfold-friendly,",
        "-- so decide can compute), but the actual decision procedure is",
        "-- never exercised on THESE theorems (their proof is just the real",
        "-- theorem re-applied) - classical satisfies the instance search",
        "-- uniformly, for every predicate this file ever binds, without",
        "-- computing which concrete decidability argument each one needs.",
        "attribute [local instance] Classical.propDecidable",
        "",
    ]

    for idn in sorted(by_id):
        # Section 3 scoped to 114-119 so far (the possessive-
        # presupposition bundle, unbound and Skolem-function-bound) -
        # raise this bound again when extending further into Section
        # 3's harder constructions (cross-sentential variable sharing,
        # cardinality anaphora, etc).
        if idn > 119:
            continue
        roles = by_id[idn]
        n = premise_counts.get(idn)
        if n is None:
            skipped[idn] = "no Problems.lean entry"
            continue
        if idn not in bare_theorem_ids:
            skipped[idn] = "no bare fracas_NNN theorem (countermodel-only, e.g. _dir1/_dir2)"
            continue
        if idn in (101, 102):
            # Confirmed locally (not just guessed): these are Section 2's
            # "generics" problems - the hand proof deliberately names
            # premise 1's own scope predicate the SAME as the hypothesis's
            # ("likelyPoorTrader" for both), treating "generic X make Y" as
            # directly equivalent to "likely Y" - a real semantic modeling
            # choice for generics, not a literal reading of premise 1's own
            # surface text (which never says "likely" at all). A literal,
            # compositional translator correctly does NOT reproduce that
            # non-compositional identification on its own, so this is
            # expected to mismatch - excluded here rather than generating
            # a theorem already known to fail, for a reason worth recording
            # rather than silently omitting.
            skipped[idn] = "generics: hand proof's predicate identification is non-compositional (see comment)"
            continue
        if idn == 69:
            # Confirmed via a real CI failure (not just guessed): the hand
            # proof's premise-1 scope variable and the hypothesis's own
            # predicate are the SAME bound variable ("rightToLive"), even
            # though premise 1's surface text ("can travel freely within
            # Europe") and the hypothesis's ("have the right to live in
            # Europe") are different VPs that translate_cl correctly gives
            # different predicate names to (canTravelFreeEurope vs
            # haveRightLiveEurope). Unlike AUX_HYPOTHESIS's cases, bridging
            # this needs an extra lemma application composed around
            # every_restrict, not just one more hypothesis chained into a
            # single application of the real theorem - out of scope for
            # this generator's proof-term shape.
            skipped[idn] = "premise-1 scope and hypothesis predicate are the same bound variable in the hand proof, but distinct translate_cl names - needs a composed proof, not just an extra hypothesis"
            continue
        has_hyp = any(r.startswith("_hypothesis") for r in roles if r != "")
        hyp_variant_roles = [r for r in roles if r.startswith("_hypothesis_")]
        # fracas_089 is the one case where "_hypothesis_X" roles are
        # genuine CONJUNCTS the real theorem needs together ("every rep
        # is at the meeting AND every client is"), not alternate readings
        # of an ambiguous sentence (that pattern - e.g. fracas_109's own
        # "_hypothesis_client"/"_hypothesis_rep"-shaped naming elsewhere
        # in this corpus - was already handled by reformalizing the
        # problem itself in an earlier round, not through this mechanism)
        # - confirmed by reading fracas_089's own real conclusion
        # (`Every rep atMeeting ∧ Every client atMeeting`) directly, not
        # assumed from the role names. Hard-coded to this one id rather
        # than a blanket "any _hypothesis_X set is a conjunction" rule,
        # since that would be guessing at problems this hasn't been
        # checked for.
        if idn in CONJUNCT_IDS:
            if "_hypothesis" in roles or set(hyp_variant_roles) != set(CONJUNCT_IDS[idn]):
                skipped[idn] = f"expected exactly {CONJUNCT_IDS[idn]} as conjuncts, got {sorted(roles)}"
                continue
        elif hyp_variant_roles:
            # Ambiguous-reading variants (fracas_109's own "_hypothesis_
            # client"/"_hypothesis_rep" naming, despite the similar-
            # looking suffix, is exactly this case, not the conjunction
            # one above) - skip, picking one arbitrarily would
            # misrepresent the ambiguity.
            if "_hypothesis" not in roles:
                skipped[idn] = f"only ambiguous hypothesis variant(s): {sorted(roles)}"
                continue

        premise_trees: dict[int, str] = {}
        ok = True
        for role, tree in roles.items():
            idx = premise_index(role)
            if idx is None:
                continue
            i, variant = idx
            if variant:
                ok = False
            premise_trees[i] = tree
        if not ok:
            skipped[idn] = "a/b premise variant present - ambiguous, skipped"
            continue
        if (
            not has_hyp
            and idn not in BUNDLE_PROJECT
            and idn not in SKOLEM_PROJECT
            or (
                idn not in CONJUNCT_IDS
                and idn not in BUNDLE_PROJECT
                and idn not in SKOLEM_PROJECT
                and "_hypothesis" not in roles
            )
        ):
            skipped[idn] = "no hypothesis tree"
            continue
        if sorted(premise_trees) != list(range(1, n + 1)):
            skipped[idn] = f"needs {n} premises, has {sorted(premise_trees)}"
            continue
        real_arrows = real_theorem_arrow_count(idn)
        expected_arrows = n + (1 if idn in AUX_HYPOTHESIS else 0)
        if real_arrows != expected_arrows:
            skipped[idn] = (
                f"real theorem has {real_arrows} top-level arrows, expected {expected_arrows} "
                "(one per premise, chaining into the hypothesis, plus one more if this id "
                "is in AUX_HYPOTHESIS) - likely an extra world-knowledge hypothesis not "
                "sourced from any FraCaS premise and not yet accounted for"
            )
            continue

        try:
            translated_premises = [translate_cl(parse_tree(premise_trees[i])) for i in range(1, n + 1)]
            if idn in CONJUNCT_IDS:
                conjuncts = [translate_cl(parse_tree(roles[r])) for r in CONJUNCT_IDS[idn]]
                conj_preds: list[str] = []
                conj_individuals: list[str] = []
                for c in conjuncts:
                    for p in c.free_predicates:
                        if p not in conj_preds:
                            conj_preds.append(p)
                    for v in c.free_individuals:
                        if v not in conj_individuals:
                            conj_individuals.append(v)
                translated_hyp = Translation(
                    lean_prop=" ∧ ".join(c.lean_prop for c in conjuncts),
                    free_predicates=conj_preds,
                    free_individuals=conj_individuals,
                )
            elif idn in BUNDLE_PROJECT or idn in SKOLEM_PROJECT:
                # Overridden below from the premise's own bundle/template -
                # its hypothesis tree (when one even exists at all - several
                # SKOLEM_PROJECT ids have none) is a differently-shaped
                # sentence (e.g. 114's own passive-possessive "Mary's
                # workstation was used") not meant to be translated
                # independently, and in 114's own case doesn't even
                # translate at all (GenNP subjects aren't handled elsewhere
                # in this translator - no need to extend that just to
                # immediately discard the result).
                translated_hyp = None
            else:
                translated_hyp = translate_cl(parse_tree(roles["_hypothesis"]))
        except Exception as e:
            skipped[idn] = f"translate error: {e}"
            continue

        if idn in BUNDLE_PROJECT:
            bundle = translated_premises[0]
            conjunct_idx = BUNDLE_PROJECT[idn]
            if not bundle.conjuncts or conjunct_idx >= len(bundle.conjuncts):
                skipped[idn] = (
                    f"BUNDLE_PROJECT names conjunct {conjunct_idx}, but premise 1's "
                    "own translation has no such conjunct - tree or mapping is stale"
                )
                continue
            translated_hyp = bundle.conjuncts[conjunct_idx]

        if idn in SKOLEM_PROJECT:
            tmpl_i, part = SKOLEM_PROJECT[idn]
            tmpl_premise = translated_premises[tmpl_i - 1]
            if tmpl_premise.template is None:
                skipped[idn] = (
                    f"SKOLEM_PROJECT names premise {tmpl_i} as holding a template, "
                    "but its own translation has none - tree or mapping is stale"
                )
                continue
            tmpl = tmpl_premise.template
            if part == "gender" and tmpl["negated"]:
                skipped[idn] = "SKOLEM_PROJECT asks for the gender part of a negated template, which has none"
                continue
            individual_candidates = [
                v
                for i, t in enumerate(translated_premises)
                if i != tmpl_i - 1
                for v in t.free_individuals
            ]
            if len(individual_candidates) != 1:
                skipped[idn] = (
                    f"SKOLEM_PROJECT needs exactly one named individual from this id's "
                    f"OTHER premises to instantiate the template at, found {individual_candidates}"
                )
                continue
            individual_name = individual_candidates[0]
            skolem_name = tmpl["skolem"]
            if part == "gender":
                translated_hyp = Translation(
                    lean_prop=f"{tmpl['gender']} {individual_name}",
                    free_predicates=[tmpl["gender"]],
                    free_individuals=[individual_name],
                )
            elif part == "has":
                translated_hyp = Translation(
                    lean_prop=f"has {individual_name} ({skolem_name} {individual_name})",
                    free_predicates=["has"],
                    free_individuals=[individual_name],
                    binary_predicates=["has"],
                )
            else:
                translated_hyp = Translation(
                    lean_prop=f"{tmpl['verb']} {individual_name} ({skolem_name} {individual_name})",
                    free_predicates=[tmpl["verb"]],
                    free_individuals=[individual_name],
                    binary_predicates=[tmpl["verb"]],
                )

        # A `.no` gold answer means the real theorem proves premises ->
        # NOT hypothesis, not premises -> hypothesis (Batch1.lean's own
        # header states this convention directly) - confirmed against the
        # two real cases this hits (6, 14) by reading their actual Lean
        # source, not assumed from the answer alone. Wrapped in parens
        # unconditionally so precedence can't bite (id 14's own hypothesis
        # is already a conjunction: `(fun x => leadingTenor x ∧ cheap x)
        # pavarotti`, needing `¬ (...)`, not `¬ (fun x => ...) pavarotti`).
        answer = answers.get(idn)
        if answer == "no":
            translated_hyp = Translation(
                lean_prop=f"¬ ({translated_hyp.lean_prop})",
                free_predicates=translated_hyp.free_predicates,
                free_individuals=translated_hyp.free_individuals,
            )
        elif answer != "yes":
            skipped[idn] = f"gold answer is .{answer}, not .yes/.no - not attempted"
            continue

        preds: list[str] = []
        individuals: list[str] = []
        binary_preds: list[str] = []
        functions: list[str] = []
        for t in [*translated_premises, translated_hyp]:
            for p in t.free_predicates:
                if p not in preds:
                    preds.append(p)
            for v in t.free_individuals:
                if v not in individuals:
                    individuals.append(v)
            for p in t.binary_predicates:
                if p not in binary_preds:
                    binary_preds.append(p)
            for f in t.free_functions:
                if f not in functions:
                    functions.append(f)
        unary_preds = [p for p in preds if p not in binary_preds]

        if idn in PROJECT_CONJUNCT:
            proj_i, conjunct_idx = PROJECT_CONJUNCT[idn]
            proj_premise = translated_premises[proj_i - 1]
            if not proj_premise.conjuncts or conjunct_idx >= len(proj_premise.conjuncts):
                skipped[idn] = (
                    f"PROJECT_CONJUNCT names premise {proj_i} conjunct {conjunct_idx}, "
                    "but its own translation has no such conjunct - tree or mapping is stale"
                )
                continue

        chain_parts = [p.lean_prop for p in translated_premises]
        if idn in AUX_HYPOTHESIS:
            chain_parts.append(AUX_HYPOTHESIS[idn](translated_premises, translated_hyp))
        chain_parts.append(translated_hyp.lean_prop)
        arrow_chain = " → ".join(chain_parts)

        # Most/AtLeast/AtMost/Exactly need [Fintype A] (a real structural
        # fact - classical logic can't manufacture one for an abstract A)
        # plus a DecidablePred instance per predicate/conjunction they
        # apply to - the latter is uniformly discharged by this file's
        # own `attribute [local instance] Classical.propDecidable"
        # (below), so only Fintype needs adding here, conditionally.
        needs_fintype = any(
            q in arrow_chain for q in ("Most ", "AtLeast ", "AtMost ", "Exactly ")
        )

        binder_parts = ["{A : Type*}"]
        if needs_fintype:
            binder_parts.append("[Fintype A]")
        if unary_preds:
            binder_parts.append(f"({' '.join(unary_preds)} : A → Prop)")
        if binary_preds:
            binder_parts.append(f"({' '.join(binary_preds)} : A → A → Prop)")
        for v in individuals:
            binder_parts.append(f"({v} : A)")
        if functions:
            binder_parts.append(f"({' '.join(functions)} : A → A)")
        binders = " ".join(binder_parts)

        # `apply fracas_NNN <;> assumption` (this generator's first
        # attempt) isn't reliable once a theorem chains 3+ premises where
        # a predicate appears only in a MIDDLE premise, never in the
        # final conclusion (fracas_018/21/26/27's `every_trans`/
        # `most_trans`-style composition: apply leaves that predicate an
        # unresolved metavariable, and `assumption` tried independently
        # per remaining goal via `<;>` doesn't reliably resolve it in the
        # right order) - the same failure mode `most_nl`/`every_most_nl`
        # were built to work around in BlindEval.lean. Supplying every
        # predicate/individual argument as `_` and every hypothesis by
        # name, all in ONE application, lets Lean's own left-to-right
        # elaboration resolve each metavariable from the earliest
        # hypothesis that determines it, before the next one is checked -
        # exactly GFCrossCheck.lean's own original example's shape
        # (predicates supplied), generalized to also thread the
        # hypotheses through the same application instead of applying
        # them after.
        hyp_names = [f"h{i}" for i in range(1, expected_arrows + 1)]

        # A handful of ids (85/86) translate their own single FraCaS
        # premise to a CONJUNCTION (`_try_translate_conjnp_subject`'s own
        # "np1 VP and np2 VP" reading of a conjoined, independently-
        # quantified subject), faithfully restating the real English -
        # but the real theorem itself only needs ONE conjunct as its own
        # premise (confirmed by reading its stated type directly, e.g.
        # fracas_085's own `Exactly 2 lawyer signed -> ...`, not the
        # conjunction), with a correspondingly NARROWER predicate/
        # individual arity than the full conjunction's own merged
        # `preds`/`individuals` (see PROJECT_CONJUNCT's own comment) -
        # so the underscore count for the real theorem's own application
        # is computed from that narrower set for these ids, not `preds`.
        if idn in PROJECT_CONJUNCT:
            proj_i, conjunct_idx = PROJECT_CONJUNCT[idn]
            real_preds: list[str] = []
            real_individuals: list[str] = []
            for i, t in enumerate(translated_premises, start=1):
                source = t.conjuncts[conjunct_idx] if i == proj_i else t
                for p in source.free_predicates:
                    if p not in real_preds:
                        real_preds.append(p)
                for v in source.free_individuals:
                    if v not in real_individuals:
                        real_individuals.append(v)
            for p in translated_hyp.free_predicates:
                if p not in real_preds:
                    real_preds.append(p)
            for v in translated_hyp.free_individuals:
                if v not in real_individuals:
                    real_individuals.append(v)
        else:
            real_preds, real_individuals = preds, individuals

        underscores = " ".join(["_"] * (len(real_preds) + len(real_individuals) + len(functions)))
        proof_hyp_args = list(hyp_names)
        if idn in PROJECT_CONJUNCT:
            proj_i, conjunct_idx = PROJECT_CONJUNCT[idn]
            suffix = ".1" if conjunct_idx == 0 else ".2"
            proof_hyp_args[proj_i - 1] += suffix
        proof_args = " ".join(filter(None, [underscores, " ".join(proof_hyp_args)]))

        lines.append(f"theorem fracas_{idn:03d}_from_gf {binders} :")
        lines.append(f"    {arrow_chain} :=")
        lines.append(f"  fun {' '.join(hyp_names)} => fracas_{idn:03d} {proof_args}")
        lines.append("")
        emitted.append(idn)

    OUT_PATH.write_text("\n".join(lines))
    print(f"wrote {OUT_PATH}: {len(emitted)} theorems: {emitted}", file=sys.stderr)
    print(f"skipped {len(skipped)}:", file=sys.stderr)
    for idn, reason in sorted(skipped.items()):
        print(f"  {idn}: {reason}", file=sys.stderr)


if __name__ == "__main__":
    main()
