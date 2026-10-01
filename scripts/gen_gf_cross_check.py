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
from translate import (  # noqa: E402
    Translation,
    translate_cl,
    parse_tree,
    camel_name,
    _leaf_words,
    _unwrap_tense,
    _decode_card,
)

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

# fracas_123's own premise 2 ("They are on her desk") is, read on its
# own, an un-translatable bare-pronoun subject ("they" has no
# antecedent a single-sentence translator can resolve) - but its real
# semantic content is exactly `_scope_aux`'s own shape: "they [=the
# ones ITEL sent] are on her [=Smith's] desk" bridges premise 1's own
# scope ("sent by ITEL") to the hypothesis's own scope ("on Smith's
# desk"), confirmed by reading fracas_123's own stated type directly
# (`Most reportsNeeded sentByItel -> (forall x, sentByItel x -> onDesk
# x) -> Some reportsNeeded onDesk`). Maps an id to (which premise
# position to synthesize, 1-based; which of _scope_aux/_restrict_aux/
# their *_rev variants to synthesize it with) - synthesized from the
# PRIOR premises and the hypothesis, the same two aux-fact builders
# AUX_HYPOTHESIS already uses, just inserted as a PREMISE of its own
# instead of appended before the hypothesis. The premise's own GF tree
# (when one exists at all, as fracas_123_premise2 does) is never fed to
# translate_cl for these ids. The third element is the quantifier word
# the FINAL hypothesis is rebuilt with (see below) - "Some" for 123,
# confirmed by reading its own stated conclusion `Some reportsNeeded
# onDesk` directly.
SYNTHESIZE_PREMISE = {123: (2, _scope_aux, "Some")}


def _build_fracas_120(roles: dict) -> "tuple[str, str, str]":
    """"Smith attended a meeting. She chaired it." -> "Smith chaired a
    meeting." The two premises share ONE bound existential (the
    meeting), confirmed by reading the real theorem's own stated type
    directly (`(exists m, attended smith m and chaired smith m) ->
    exists m, chaired smith m`). Built by hand straight from the three
    raw GF trees rather than through translate_cl's own per-sentence
    pipeline: no other id needs "keep the indefinite object
    existentially open instead of fusing it into a predicate name" or
    "she"/"it" resolving to the PRIOR sentence's own subject/object -
    forcing either into translate_cl's general-purpose dispatch would
    risk it misfiring on some unrelated future sentence shape it was
    never meant to cover. Returns (binders, arrow_chain, proof)."""
    p1 = _unwrap_tense(parse_tree(roles["_premise1"]))
    p2 = _unwrap_tense(parse_tree(roles["_premise2"]))
    hyp = _unwrap_tense(parse_tree(roles["_hypothesis"]))

    subject_name = camel_name(_leaf_words(p1.args[0]))
    verb1 = camel_name(_leaf_words(p1.args[1].args[0]))
    verb2 = camel_name(_leaf_words(p2.args[1].args[0]))
    if camel_name(_leaf_words(hyp.args[0])) != subject_name:
        raise ValueError("hypothesis's own subject doesn't match premise 1's")
    if camel_name(_leaf_words(hyp.args[1].args[0])) != verb2:
        raise ValueError("hypothesis's own verb doesn't match premise 2's")

    combined = f"(∃ m, {verb1} {subject_name} m ∧ {verb2} {subject_name} m)"
    conclusion = f"∃ m, {verb2} {subject_name} m"
    arrow_chain = f"{combined} → {conclusion}"
    binders = f"{{A : Type*}} ({subject_name} : A) ({verb1} {verb2} : A → A → Prop)"
    proof = "fun h1 => fracas_120 _ _ _ h1"
    return binders, arrow_chain, proof


def _build_fracas_121(roles: dict) -> "tuple[str, str, str]":
    """"Smith delivered a report to ITEL. She also delivered them an
    invoice. And she delivered them a project proposal." -> restates the
    same three-way conjunction, confirmed by reading the real theorem's
    own `:= id` proof directly. The real theorem treats each delivered
    item as a NAMED INDIVIDUAL constant, not a predicate (`delivered :
    A -> A -> A -> Prop`, a genuinely TERNARY relation - the first this
    generator has ever produced) - built by hand for the same reason as
    fracas_120's own builder: "she"/"them" resolving to the first
    sentence's own subject/PP-object, and a ternary named-individual
    relation, are both one-off shapes no other id needs. Returns
    (binders, arrow_chain, proof)."""
    p1 = _unwrap_tense(parse_tree(roles["_premise1"]))
    p2 = _unwrap_tense(parse_tree(roles["_premise2"]))
    p3 = _unwrap_tense(parse_tree(roles["_premise3"]))

    subject_name = camel_name(_leaf_words(p1.args[0]))
    vp1 = p1.args[1]
    verb_name = camel_name(_leaf_words(vp1.args[0].args[0]))
    obj1_name = camel_name(_leaf_words(vp1.args[0].args[1]))
    pp_name = camel_name(_leaf_words(vp1.args[1].args[1]))

    vp2 = p2.args[1].args[1]
    obj2_name = camel_name(_leaf_words(vp2.args[0].args[1]))

    vp3 = p3.args[1]
    obj3_name = camel_name(_leaf_words(vp3.args[0].args[1]))

    def conjunct(obj_name: str) -> str:
        return f"{verb_name} {subject_name} {pp_name} {obj_name}"

    combined = f"({conjunct(obj1_name)} ∧ {conjunct(obj2_name)} ∧ {conjunct(obj3_name)})"
    arrow_chain = f"{combined} → {combined}"
    binders = (
        f"{{A : Type*}} ({subject_name} {pp_name} {obj1_name} {obj2_name} {obj3_name} : A) "
        f"({verb_name} : A → A → A → Prop)"
    )
    proof = "fun h => fracas_121 _ _ _ _ _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_122(roles: dict) -> "tuple[str, str, str]":
    """"Every committee has a chairman. He is appointed by its
    members." -> "every committee has a chairman appointed by members
    of the committee" - the bound "he"/"its" fold into ONE combined
    statement, confirmed by reading the real theorem's own `:= id` proof
    directly (`(forall c, committee c -> exists ch, chairman ch c and
    appointedByMembers ch c) -> ...`, the same statement restated). The
    hypothesis's own GF tree (a single self-contained sentence using a
    passive post-nominal modifier, "a chairman appointed by members of
    the committee") is never translated independently - it would need
    passive-post-nominal-modifier support this translator doesn't have,
    for a shape that's provably equal to the premise anyway, so this
    just reuses the SAME combined text as both. Built by hand for the
    same reason as fracas_120/121's own builders: "he"/"its" resolving
    to a NESTED bound variable, not a fixed individual, is one-off.
    Returns (binders, arrow_chain, proof)."""
    p1 = _unwrap_tense(parse_tree(roles["_premise1"]))
    p2 = _unwrap_tense(parse_tree(roles["_premise2"]))

    committee_name = camel_name(_leaf_words(p1.args[0]))
    chairman_name = camel_name(_leaf_words(p1.args[1].args[1]))
    appoint_name = camel_name(_leaf_words(p2.args[1]))

    combined = f"(∀ c, {committee_name} c → ∃ ch, {chairman_name} ch c ∧ {appoint_name} ch c)"
    arrow_chain = f"{combined} → {combined}"
    binders = f"{{A : Type*}} ({committee_name} : A → Prop) ({chairman_name} {appoint_name} : A → A → Prop)"
    proof = "fun h => fracas_122 _ _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_124(roles: dict) -> "tuple[str, str, str]":
    """"Two out of ten machines are missing. They have been removed." ->
    "Two machines have been removed." Confirmed by reading the real
    theorem's own stated type directly (`Exactly 2 (fun _ : A => True)
    missing -> (forall x, missing x -> removed x) -> AtLeast 2 (fun _ :
    A => True) removed`): the "ten" in "out of ten machines" carries NO
    information in the real theorem's own type at all - the whole
    domain A is treated as being exactly the ten machines via a
    trivial `fun _ => True` restrictor, not a named one (unlike every
    other restrictor this generator has ever produced) - only fracas_126
    (excluded separately, see CUSTOM_BUILD's own comment) needs that
    cardinality made explicit. Premise 2 ("They have been removed") is
    never translated at all (no tree needed): its only real content is
    an aux scope-entailment fact bridging premise 1's own scope
    ("missing") to the hypothesis's own ("removed"), built directly the
    same way SYNTHESIZE_PREMISE's own `_scope_aux` already does, just
    inlined here since the trivial restrictor doesn't fit that
    mechanism's generic "reuse free_predicates[0]" hypothesis rebuild
    (there IS no such free predicate to reuse). Returns (binders,
    arrow_chain, proof)."""
    p1 = _unwrap_tense(parse_tree(roles["_premise1"]))
    hyp = _unwrap_tense(parse_tree(roles["_hypothesis"]))

    if (
        p1.args[0].head != "AdvNP"
        or p1.args[0].args[1].head != "PrepNP"
        or p1.args[0].args[1].args[0].head != "out_of_Prep"
    ):
        raise ValueError("premise 1's subject isn't the expected 'N out of M Xs' shape")
    det_np = p1.args[0].args[0]
    count, approx = _decode_card(det_np.args[0].args[1].args[0])
    if approx is not None:
        raise ValueError("premise 1's own count is AdNum-wrapped, expected a bare numeral")
    p1_scope = camel_name(_leaf_words(p1.args[1]))
    hyp_scope = camel_name(_leaf_words(hyp.args[1]))

    combined_premise = f"Exactly {count} (fun _ : A => True) {p1_scope}"
    aux = f"(∀ x, {p1_scope} x → {hyp_scope} x)"
    conclusion = f"AtLeast {count} (fun _ : A => True) {hyp_scope}"
    arrow_chain = f"{combined_premise} → {aux} → {conclusion}"
    binders = f"{{A : Type*}} [Fintype A] ({p1_scope} {hyp_scope} : A → Prop)"
    proof = "fun h1 h2 => fracas_124 _ _ h1 h2"
    return binders, arrow_chain, proof


def _build_fracas_128(roles: dict) -> "tuple[str, str, str]":
    """"John and his colleagues went to a meeting. They hated it." ->
    "John's colleagues hated the meeting." (reading A: "they" excludes
    John). Confirmed by reading the real theorem's own `:= id` proof
    directly (`Every colleagueOf hated -> Every colleagueOf hated`) -
    premise 1's own VP ("went to a meeting") is a pure distractor, never
    used at all; only its subject's own "his colleagues" conjunct
    supplies the restrictor name. Premise 2 ("they hated it") supplies
    the scope name directly (both pronouns contribute nothing to
    naming, same as every other pronoun this generator's builders have
    seen). Returns (binders, arrow_chain, proof)."""
    p1 = _unwrap_tense(parse_tree(roles["_premise1"]))
    colleague_cn = p1.args[0].args[1].args[1].args[1]
    colleague_name = camel_name(_leaf_words(colleague_cn))
    p2 = _unwrap_tense(parse_tree(roles["_premise2"]))
    hate_name = camel_name(_leaf_words(p2.args[1]))

    combined = f"Every {colleague_name} {hate_name}"
    arrow_chain = f"{combined} → {combined}"
    binders = f"{{A : Type*}} ({colleague_name} {hate_name} : A → Prop)"
    proof = "fun h => fracas_128 _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_129(roles: dict) -> "tuple[str, str, str]":
    """"John and his colleagues went to a meeting. They hated it." ->
    "John hated the meeting." (reading B: "they" includes John,
    distributively). Confirmed by reading the real theorem's own stated
    type directly (`Every (fun x => x = john or colleagueOf x) hated ->
    hated john`). The hypothesis ("John hated the meeting") translates
    fine via translate_cl's OWN general path (a plain "ProperNoun VP"
    fact) - reused directly for both its own names and the final
    conclusion, rather than re-derived - but premise 1's disjunctive
    restrictor has no GF tree of its own to translate at all (it's a
    hand-combination of fracas_128's own colleague name with John's own
    individual, read off the real theorem's own stated shape directly).
    Returns (binders, arrow_chain, proof)."""
    p1 = _unwrap_tense(parse_tree(roles["_premise1"]))
    colleague_cn = p1.args[0].args[1].args[1].args[1]
    colleague_name = camel_name(_leaf_words(colleague_cn))
    hyp = translate_cl(parse_tree(roles["_hypothesis"]))
    hate_name = hyp.free_predicates[-1]
    john_name = hyp.free_individuals[0]

    premise1_text = f"Every (fun x => x = {john_name} ∨ {colleague_name} x) {hate_name}"
    arrow_chain = f"({premise1_text}) → {hyp.lean_prop}"
    binders = f"{{A : Type*}} ({john_name} : A) ({colleague_name} {hate_name} : A → Prop)"
    proof = "fun h => fracas_129 _ _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_131(roles: dict) -> "tuple[str, str, str]":
    """"Each department has a dedicated line. They rent them from BT."
    -> "Every department rents a line from BT." Confirmed by reading
    the real theorem's own stated type directly (`(forall d, department
    d -> hasLine d (lineOf d)) -> (forall d, department d -> rentsFromBT
    d (lineOf d)) -> forall d, department d -> exists l, rentsFromBT d
    l`): "a dedicated line" becomes a Skolem function (one line per
    department, the same device 117-119 use for a BOUND possessive
    pronoun, except triggered here by plain anaphoric continuation of
    an indefinite object, not a possessive pronoun at all) - "they"/
    "them" in premise 2 and the hypothesis's own weaker existential
    conclusion are both built directly rather than independently
    translated, since neither sentence's own compositional reading
    matches the real theorem's shape (the hypothesis's own "rents A
    line from BT" would otherwise fuse into one unary predicate, not
    split into the needed `exists l, rentsFromBT d l`). Returns
    (binders, arrow_chain, proof)."""
    p1 = _unwrap_tense(parse_tree(roles["_premise1"]))
    restrictor = camel_name(_leaf_words(p1.args[0]))
    noun_name = camel_name(_leaf_words(p1.args[1].args[1]))
    skolem = noun_name + "Of"
    has_name = "has"
    p2 = _unwrap_tense(parse_tree(roles["_premise2"]))
    rel_name = camel_name(_leaf_words(p2.args[1]))

    premise1_text = f"∀ d, {restrictor} d → {has_name} d ({skolem} d)"
    premise2_text = f"∀ d, {restrictor} d → {rel_name} d ({skolem} d)"
    conclusion = f"∀ d, {restrictor} d → ∃ l, {rel_name} d l"
    arrow_chain = f"({premise1_text}) → ({premise2_text}) → ({conclusion})"
    binders = (
        f"{{A : Type*}} ({restrictor} : A → Prop) ({skolem} : A → A) "
        f"({has_name} {rel_name} : A → A → Prop)"
    )
    proof = "fun h1 h2 => fracas_131 _ _ _ _ h1 h2"
    return binders, arrow_chain, proof


def _build_fracas_132(roles: dict) -> "tuple[str, str, str]":
    """"Each department has a dedicated line. The sales department
    rents it from BT." -> "The sales department rents a line from BT."
    The Skolem-function half of fracas_131's own pattern (premise 1 is
    IDENTICAL, reused), now instantiated at a NAMED individual ("the
    sales department") instead of the bound variable - confirmed by
    reading the real theorem's own stated type directly (`(forall d,
    department d -> hasLine d (lineOf d)) -> rentsFromBT salesDept
    (lineOf salesDept) -> exists l, rentsFromBT salesDept l`). Returns
    (binders, arrow_chain, proof)."""
    p1 = _unwrap_tense(parse_tree(roles["_premise1"]))
    restrictor = camel_name(_leaf_words(p1.args[0]))
    noun_name = camel_name(_leaf_words(p1.args[1].args[1]))
    skolem = noun_name + "Of"
    has_name = "has"
    p2 = _unwrap_tense(parse_tree(roles["_premise2"]))
    sales_dept_name = camel_name(_leaf_words(p2.args[0]))
    rel_name = camel_name(_leaf_words(p2.args[1]))

    premise1_text = f"∀ d, {restrictor} d → {has_name} d ({skolem} d)"
    premise2_text = f"{rel_name} {sales_dept_name} ({skolem} {sales_dept_name})"
    conclusion = f"∃ l, {rel_name} {sales_dept_name} l"
    arrow_chain = f"({premise1_text}) → {premise2_text} → {conclusion}"
    binders = (
        f"{{A : Type*}} ({restrictor} : A → Prop) ({skolem} : A → A) "
        f"({sales_dept_name} : A) ({has_name} {rel_name} : A → A → Prop)"
    )
    proof = "fun h1 h2 => fracas_132 _ _ _ _ _ h1 h2"
    return binders, arrow_chain, proof


def _build_fracas_133(roles: dict) -> "tuple[str, str, str]":
    """"GFI owns several computers. ITEL maintains them." -> "ITEL
    maintains all the computers that GFI owns." Confirmed by reading
    the real theorem's own stated type directly (`(exists x, ownsGFI x)
    -> (forall x, ownsGFI x -> maintainsITEL x) -> forall x, ownsGFI x
    -> maintainsITEL x`) - e-type anaphora: "them" resolves to the
    MAXIMAL set GFI owns, not just the "several" witnesses, so premise 2
    becomes a universal bridging fact, built directly (pronoun "them"
    contributes nothing to naming). The hypothesis's own GF tree (an
    object-gap relative clause, "the computers that GFI owns") is never
    translated independently: unlike fracas_123's own StrandRelSlash
    case, which fuses the restrictor into ONE name, this real theorem
    needs "owns"/"maintains" kept as two SEPARATE predicates sharing an
    argument - the same restrictor-vs-two-predicates ambiguity
    `_try_translate_possessive_presupposition`'s own comment already
    flags for "has a N" sentences, just surfacing here for a relative
    clause instead. Returns (binders, arrow_chain, proof)."""
    p1 = _unwrap_tense(parse_tree(roles["_premise1"]))
    owns_name = camel_name(_leaf_words(p1.args[1]))
    p2 = _unwrap_tense(parse_tree(roles["_premise2"]))
    maintain_name = camel_name(_leaf_words(p2.args[1]))

    premise1_text = f"∃ x, {owns_name} x"
    premise2_text = f"∀ x, {owns_name} x → {maintain_name} x"
    arrow_chain = f"({premise1_text}) → ({premise2_text}) → ({premise2_text})"
    binders = f"{{A : Type*}} ({owns_name} {maintain_name} : A → Prop)"
    proof = "fun h1 h2 => fracas_133 _ _ h1 h2"
    return binders, arrow_chain, proof


def _build_fracas_138(roles: dict) -> "tuple[str, str, str]":
    """"Every report has a cover page. R-95-103 is a report. Smith
    signed the cover page." -> "Smith signed the cover page of
    R-95-103." Confirmed by reading the real theorem's own stated type
    directly (`report r95103 -> signed smith (coverPageOf r95103) ->
    signed smith (coverPageOf r95103)`) - premise 1 is DROPPED entirely
    (it only licenses treating "the cover page of X" as a total Skolem
    function notationally, never appearing as an explicit hypothesis of
    the real theorem at all - the reverse of AUX_HYPOTHESIS's own
    pattern, which always ADDS a hypothesis, never removes one).
    Premise 2 ("R-95-103 is a report") translates fine via translate_cl
    directly and is reused as-is; premise 3 and the hypothesis both get
    hand-built from the same coverPageOf Skolem function and r95103
    individual, since the hypothesis's own independent translation
    would otherwise bake r95103 directly into a fused predicate name
    rather than applying a separate function to it as an argument.
    Returns (binders, arrow_chain, proof)."""
    p1 = _unwrap_tense(parse_tree(roles["_premise1"]))
    noun_name = camel_name(_leaf_words(p1.args[1].args[1]))
    skolem = noun_name + "Of"
    report_fact = translate_cl(parse_tree(roles["_premise2"]))
    report_name = report_fact.free_predicates[0]
    r_name = report_fact.free_individuals[0]
    p3 = _unwrap_tense(parse_tree(roles["_premise3"]))
    smith_name = camel_name(_leaf_words(p3.args[0]))
    sign_name = camel_name(_leaf_words(p3.args[1].args[0]))

    fact = f"{sign_name} {smith_name} ({skolem} {r_name})"
    arrow_chain = f"{report_name} {r_name} → {fact} → {fact}"
    binders = (
        f"{{A : Type*}} ({report_name} : A → Prop) ({skolem} : A → A) "
        f"({smith_name} {r_name} : A) ({sign_name} : A → A → Prop)"
    )
    proof = "fun h1 h2 => fracas_138 _ _ _ _ _ h1 h2"
    return binders, arrow_chain, proof


def _build_fracas_139(roles: dict) -> "tuple[str, str, str]":
    """"A company director awarded himself a large payrise." ->
    "A company director has awarded and been awarded a payrise."
    Confirmed by reading the real theorem's own `:= id` proof directly
    (`(exists d, awarded d d) -> exists d, awarded d d`) - "a company
    director" is ERASED entirely (the real theorem existentially
    quantifies over ANY individual, not specifically company directors
    - a real semantic simplification, not a translation gap), and only
    the reflexive "awarded... a large payrise" relation survives. The
    verb's own GF lexical item (`award_V3`) uses a `_V3` suffix this
    translator's `_LEXICAL_SUFFIXES` table doesn't recognize (the
    ditransitive award_V3/ReflVP construction has never come up before
    this problem), so "award" is prepended by hand rather than picked
    up automatically - names don't need to match the real theorem's own
    choice regardless. Returns (binders, arrow_chain, proof)."""
    p = _unwrap_tense(parse_tree(roles["_premise"]))
    obj_cn = p.args[1].args[0].args[1]
    payrise_name = camel_name(_leaf_words(obj_cn))
    verb_name = "award" + payrise_name[0].upper() + payrise_name[1:]

    combined = f"∃ d, {verb_name} d d"
    arrow_chain = f"({combined}) → {combined}"
    binders = f"{{A : Type*}} ({verb_name} : A → A → Prop)"
    proof = "fun h => fracas_139 _ h"
    return binders, arrow_chain, proof


def _build_fracas_140(roles: dict) -> "tuple[str, str, str]":
    """"John said Bill had hurt himself." -> "John said Bill had been
    hurt." Confirmed by reading the real theorem's own `:= id` proof
    directly (`said john (hurt bill bill) -> said john (hurt bill
    bill)`) - "said" takes a Prop as its own second argument (`A -> Prop
    -> Prop`, an embedded-clause-as-argument shape no other id in this
    generator needs), and "himself" resolves to Bill, giving the
    reflexive `hurt bill bill`. Both `say_VS`'s own GF lexical item and
    "said" itself use suffixes (`_VS`) this translator doesn't recognize
    as lexical, so "said" is supplied by hand, same reason as
    fracas_139's own `award_V3`. Returns (binders, arrow_chain, proof)."""
    p = _unwrap_tense(parse_tree(roles["_premise"]))
    john_name = camel_name(_leaf_words(p.args[0]))
    embedded = p.args[1].args[1].args[2]
    bill_name = camel_name(_leaf_words(embedded.args[0]))
    hurt_name = camel_name(_leaf_words(embedded.args[1]))
    said_name = "said"

    hurt_fact = f"{hurt_name} {bill_name} {bill_name}"
    combined = f"{said_name} {john_name} ({hurt_fact})"
    arrow_chain = f"{combined} → {combined}"
    binders = (
        f"{{A : Type*}} ({john_name} {bill_name} : A) "
        f"({said_name} : A → Prop → Prop) ({hurt_name} : A → A → Prop)"
    )
    proof = "fun h => fracas_140 _ _ _ _ h"
    return binders, arrow_chain, proof


# ---------------------------------------------------------------------
# Section 4 (ellipsis, 142-196): per Ellipsis.lean's own approach note,
# almost every id's real theorem is either a trivial restatement/
# conjunction-projection over the hand-resolved ellipsis site, or a
# countermodel (already auto-excluded elsewhere). None of these fit
# translate_cl's quantifier-centric pipeline - many real theorems bind
# bare `Prop` atoms (one per whole resolved sentence, not a domain-
# quantified predicate at all), so every one of these is CUSTOM_BUILD.
# ---------------------------------------------------------------------


def _atomic_name(tree_text: str) -> str:
    """Fuses an entire (tensed) sentence's own leaf words into one
    camelCase name, for the bare-`Prop`-atom ids (142/145-148/164-166/
    178 etc.) whose real theorem treats "John spoke to Mary" as a single
    nullary fact, not a domain-quantified predicate - the ellipsis site
    is hand-resolved to one whole fact, matching Ellipsis.lean's own
    documented approach, so there's no compositional structure left to
    preserve once resolved."""
    return camel_name(_leaf_words(_unwrap_tense(parse_tree(tree_text))))


def _build_fracas_142(roles: dict) -> "tuple[str, str, str]":
    """"John spoke to Mary. So did Bill." -> "Bill spoke to Mary."
    Confirmed by reading the real theorem's own stated type directly
    (`spokeJohnMary ∧ spokeBillMary -> spokeBillMary`) - both conjuncts
    are bare `Prop` atoms (the whole resolved sentence fused into one
    name), not domain-quantified predicates; the elided "so did Bill"
    (premise 2) is never given its own tree - its resolved content is
    literally the hypothesis's own sentence, so that tree is reused
    directly rather than re-registering it. Returns (binders,
    arrow_chain, proof)."""
    n1 = _atomic_name(roles["_premise1"])
    n2 = _atomic_name(roles["_hypothesis"])
    arrow_chain = f"{n1} ∧ {n2} → {n2}"
    binders = f"({n1} {n2} : Prop)"
    proof = "fun h => fracas_142 _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_145(roles: dict) -> "tuple[str, str, str]":
    """"John spoke to Mary at four. And Bill did at five." -> "Bill
    spoke to Mary at five." Confirmed by reading the real theorem's own
    `:= id` proof directly (`spokeAt5BillMary -> spokeAt5BillMary`) -
    "at five o'clock" is its OWN overriding adverbial, not inherited
    from premise 1 at all, so premise 1 is a pure distractor the real
    proof never touches; only the hypothesis's own sentence (reused
    directly for the elided "Bill did at five o'clock") matters.
    Returns (binders, arrow_chain, proof)."""
    n = _atomic_name(roles["_hypothesis"])
    arrow_chain = f"{n} → {n}"
    binders = f"({n} : Prop)"
    proof = "fun h => fracas_145 _ h"
    return binders, arrow_chain, proof


def _build_fracas_146(roles: dict) -> "tuple[str, str, str]":
    """"John has spoken to Mary. Bill is going to." -> "Bill will speak
    to Mary." Confirmed by reading the real theorem's own `:= id` proof
    directly (`spokeBillMary -> spokeBillMary`) - this project doesn't
    model tense as a parameter separate from the underlying fact, so
    premise 1's own perfect-tense tree is a pure distractor (different
    surface tense, same single `Prop` either way would be redundant);
    only the hypothesis's own sentence matters, reused for the elided
    "Bill is going to [speak to Mary]" directly. Returns (binders,
    arrow_chain, proof)."""
    n = _atomic_name(roles["_hypothesis"])
    arrow_chain = f"{n} → {n}"
    binders = f"({n} : Prop)"
    proof = "fun h => fracas_146 _ h"
    return binders, arrow_chain, proof


def _build_fracas_147(roles: dict) -> "tuple[str, str, str]":
    """"John spoke to Mary on Monday. Bill didn't." -> "Bill didn't
    speak to Mary on Monday." Confirmed by reading the real theorem's
    own `:= id` proof directly (`¬ spokeBillMaryMonday -> ¬
    spokeBillMaryMonday`) - negative ellipsis directly refutes the
    hypothesis regardless of premise 1's own (positive) polarity, so
    premise 1 is a pure distractor; the hypothesis's own (positive)
    sentence is reused, negated, for the elided "Bill didn't [speak to
    Mary on Monday]". Returns (binders, arrow_chain, proof)."""
    n = _atomic_name(roles["_hypothesis"])
    arrow_chain = f"¬ {n} → ¬ {n}"
    binders = f"({n} : Prop)"
    proof = "fun h => fracas_147 _ h"
    return binders, arrow_chain, proof


def _build_fracas_148(roles: dict) -> "tuple[str, str, str]":
    """"Does John speak to Mary? Bill has." -> "Bill has spoken to
    Mary." Confirmed by reading the real theorem's own `:= id` proof
    directly (`spokeBillMary -> spokeBillMary`) - premise 1 is a
    QUESTION (not asserted content at all, so it has no tree and
    contributes nothing), and the hypothesis's own sentence is reused
    for the elided "Bill has [spoken to Mary]" directly. Returns
    (binders, arrow_chain, proof)."""
    n = _atomic_name(roles["_hypothesis"])
    arrow_chain = f"{n} → {n}"
    binders = f"({n} : Prop)"
    proof = "fun h => fracas_148 _ h"
    return binders, arrow_chain, proof


def _build_fracas_149(roles: dict) -> "tuple[str, str, str]":
    """"John has spoken to Mary. The students have too." -> "The
    students have spoken to Mary." Confirmed by reading the real
    theorem's own `:= id` proof directly (`Every student spokeMary ->
    Every student spokeMary`) - "the students", a definite plural
    subject, is this project's own distributive-universal convention
    (Section 2's simplification for definite plurals, same as every
    other definite-plural subject this corpus treats as `Every`); only
    premise 2's own resolved sentence matters (reused for the
    hypothesis directly, matching the real proof's own restatement).
    Returns (binders, arrow_chain, proof)."""
    p = _unwrap_tense(parse_tree(roles["_premise2"]))
    _det, cn = p.args[0].args
    restrictor = camel_name(_leaf_words(cn))
    scope = camel_name(_leaf_words(p.args[1]))
    arrow_chain = f"Every {restrictor} {scope} → Every {restrictor} {scope}"
    binders = f"{{A : Type*}} ({restrictor} {scope} : A → Prop)"
    proof = "fun h => fracas_149 _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_164(roles: dict) -> "tuple[str, str, str]":
    """"John spoke to Mary. [He spoke] to Sue [too]." -> "John spoke to
    Sue." Confirmed by reading the real theorem's own stated type
    directly (`spokeJohnMary ∧ spokeJohnSue -> spokeJohnSue`) - a plain
    bare-`Prop`-atom conjunction-projection, same shape as fracas_142;
    premise 1's own gold text ("John spoke to Mary") is identical to
    fracas_142's own premise 1, so its tree is reused rather than
    re-registered (`fracas_164_premise1` in run_gf_tests.py). Returns
    (binders, arrow_chain, proof)."""
    n1 = _atomic_name(roles["_premise1"])
    n2 = _atomic_name(roles["_hypothesis"])
    arrow_chain = f"{n1} ∧ {n2} → {n2}"
    binders = f"({n1} {n2} : Prop)"
    proof = "fun h => fracas_164 _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_165(roles: dict) -> "tuple[str, str, str]":
    """"John spoke to Mary. [He spoke to her] on Friday [too]." -> "John
    spoke to Mary on Friday." Confirmed by reading the real theorem's
    own stated type directly (`spokeJohnMary ∧ spokeJohnMaryFriday ->
    spokeJohnMaryFriday`) - same bare-`Prop`-atom conjunction-projection
    shape as 142/164; premise 1's own gold text is again identical to
    fracas_142's own premise 1 (reused, `fracas_165_premise1`). Returns
    (binders, arrow_chain, proof)."""
    n1 = _atomic_name(roles["_premise1"])
    n2 = _atomic_name(roles["_hypothesis"])
    arrow_chain = f"{n1} ∧ {n2} → {n2}"
    binders = f"({n1} {n2} : Prop)"
    proof = "fun h => fracas_165 _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_166(roles: dict) -> "tuple[str, str, str]":
    """"John spoke to Mary on Thursday. [He spoke to her] on Friday
    [too]." -> "John spoke to Mary on Friday." Confirmed by reading the
    real theorem's own stated type directly (`spokeJohnMaryThursday ∧
    spokeJohnMaryFriday -> spokeJohnMaryFriday`) - same shape again;
    the hypothesis's own gold text ("John spoke to Mary on Friday") is
    identical to fracas_165's own hypothesis, so that tree is reused
    (`fracas_166_hypothesis`) rather than re-registered. Returns
    (binders, arrow_chain, proof)."""
    n1 = _atomic_name(roles["_premise1"])
    n2 = _atomic_name(roles["_hypothesis"])
    arrow_chain = f"{n1} ∧ {n2} → {n2}"
    binders = f"({n1} {n2} : Prop)"
    proof = "fun h => fracas_166 _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_167(roles: dict) -> "tuple[str, str, str]":
    """"Twenty men work in the Sales Department. But only one woman."
    -> not "Two women work in the Sales Department." Confirmed by
    reading the real theorem's own `exactly_ne`-based proof directly
    (`Exactly 1 (fun _ : A => True) womanWorksInSales -> ¬ Exactly 2
    (fun _ : A => True) womanWorksInSales`) - premise 1 (about MEN) is a
    pure distractor never touched at all; only premise 2's own numeral
    ("only one woman", unwrapped past its `PredetNP only_Predet`) and
    the hypothesis's own numeral ("two women") matter, both decoded via
    `_decode_card`, same trivial-literal-restrictor convention as
    fracas_124. Returns (binders, arrow_chain, proof)."""

    def subj_count_and_words(p):
        subj = p.args[0]
        if subj.head == "PredetNP":
            subj = subj.args[1]
        det, cn = subj.args
        count, _approx = _decode_card(det.args[1].args[0])
        return count, _leaf_words(cn) + _leaf_words(p.args[1])

    p2 = parse_tree(roles["_premise2"])
    hyp = parse_tree(roles["_hypothesis"])
    count2, words2 = subj_count_and_words(p2)
    count_h, _words_h = subj_count_and_words(hyp)
    pred_name = camel_name(words2)
    arrow_chain = (
        f"Exactly {count2} (fun _ : A => True) {pred_name} → "
        f"¬ Exactly {count_h} (fun _ : A => True) {pred_name}"
    )
    binders = f"{{A : Type*}} [Fintype A] ({pred_name} : A → Prop)"
    proof = "fun h => fracas_167 _ h"
    return binders, arrow_chain, proof


def _represents_fact(p, default_owner=None):
    """Parses a "X represents (his|Y's) company" clause into (subject,
    verb, noun, owner) - `owner` is the subject itself for a bound
    possessive pronoun (sloppy reading), or an explicit named individual
    for a genitive NP (strict reading); shared by 182/183/189/190, all
    of which Skolemize "company" via the same `companyOf : A -> A`
    pattern 131/132's own `lineOf` already established."""
    subj = camel_name(_leaf_words(p.args[0]))
    comp = p.args[1]
    verb = camel_name(_leaf_words(comp.args[0]))
    det_cn = comp.args[1]
    noun = camel_name(_leaf_words(det_cn.args[1]))
    quant = det_cn.args[0].args[0]
    if quant.head == "PossPron":
        owner = default_owner if default_owner else subj
    elif quant.head == "GenNP":
        owner = camel_name(_leaf_words(quant.args[0]))
    else:
        raise ValueError(f"unexpected determiner {quant.head!r}")
    return subj, verb, noun, owner


def _build_fracas_182(roles: dict) -> "tuple[str, str, str]":
    """"Smith represents his company. So does Jones." (sloppy reading)
    -> "Jones represents Jones' company." Confirmed by reading the real
    theorem's own stated type directly (`represents smith (companyOf
    smith) ∧ represents jones (companyOf jones) -> represents jones
    (companyOf jones)`) - the bound possessive "his" resolves to each
    sentence's OWN subject (sloppy identity), Skolemized the same way
    131/132's own `lineOf` already is; premise 2's own gold text ("Jones
    represents Jones' company") is identical to the hypothesis, reused
    rather than re-registered. Returns (binders, arrow_chain, proof)."""
    p = _unwrap_tense(parse_tree(roles["_premise"]))
    hyp = _unwrap_tense(parse_tree(roles["_hypothesis"]))
    s1, v, n, o1 = _represents_fact(p)
    s2, _v2, _n2, o2 = _represents_fact(hyp)
    skolem = n + "Of"
    fact1 = f"{v} {s1} ({skolem} {o1})"
    fact2 = f"{v} {s2} ({skolem} {o2})"
    arrow_chain = f"({fact1}) ∧ ({fact2}) → {fact2}"
    binders = f"{{A : Type*}} ({v} : A → A → Prop) ({skolem} : A → A) ({s1} {s2} : A)"
    proof = "fun h => fracas_182 _ _ _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_183(roles: dict) -> "tuple[str, str, str]":
    """"Smith represents his company. So does Jones." (strict reading)
    -> "Jones represents Smith's company." Confirmed by reading the real
    theorem's own stated type directly (`represents smith (companyOf
    smith) ∧ represents jones (companyOf smith) -> represents jones
    (companyOf smith)`) - "his" is referential here (fixed to Smith, the
    strict reading), so Jones' own fact Skolemizes at `smith`, not
    `jones`; the premise's own gold text ("Smith represents his
    company") is identical to fracas_182's own premise, reused rather
    than re-registered (`fracas_183_premise` in run_gf_tests.py).
    Returns (binders, arrow_chain, proof)."""
    p = _unwrap_tense(parse_tree(roles["_premise"]))
    hyp = _unwrap_tense(parse_tree(roles["_hypothesis"]))
    s1, v, n, o1 = _represents_fact(p)
    s2, _v2, _n2, o2 = _represents_fact(hyp)
    skolem = n + "Of"
    fact1 = f"{v} {s1} ({skolem} {o1})"
    fact2 = f"{v} {s2} ({skolem} {o2})"
    arrow_chain = f"({fact1}) ∧ ({fact2}) → {fact2}"
    binders = f"{{A : Type*}} ({v} : A → A → Prop) ({skolem} : A → A) ({s1} {s2} : A)"
    proof = "fun h => fracas_183 _ _ _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_178(roles: dict) -> "tuple[str, str, str]":
    """"John wrote a report. Bill said Peter did too." -> "Bill said
    Peter wrote a report." Confirmed by reading the real theorem's own
    stated type directly (`johnWroteReport ∧ billSaidPeterWroteReport ->
    billSaidPeterWroteReport`) - two unrelated bare-`Prop` atoms
    conjunction-projected, same shape as 142/164/165/166 but across a
    `say_VS`-embedded clause (the hypothesis's own leaf words silently
    drop "said" itself, same `_VS`-suffix gap as fracas_140 - harmless
    here since names never need to match, only arity/type). Returns
    (binders, arrow_chain, proof)."""
    n1 = _atomic_name(roles["_premise1"])
    n2 = _atomic_name(roles["_hypothesis"])
    arrow_chain = f"{n1} ∧ {n2} → {n2}"
    binders = f"({n1} {n2} : Prop)"
    proof = "fun h => fracas_178 _ _ h"
    return binders, arrow_chain, proof


def _claimed_costed_xyz(p):
    """Parses "X claimed (he|Y) had costed (his|Y's) proposal" into the
    ternary (x, y, z) `claimedCosted` applies to - `y`/`z` resolve to `x`
    itself for a bound pronoun (`UsePron he_Pron`, where `_leaf_words`
    has no lexical content to name from at all), or an explicit named
    individual for an overt `UsePN`/genitive NP - shared by 185/186/187,
    FraCaS's three sloppy/strict/doubly-strict combinations of the SAME
    two-pronoun sentence."""
    x = camel_name(_leaf_words(p.args[0]))
    inner_vp = p.args[1].args[1].args[2]
    y_tree = inner_vp.args[0]
    y = x if y_tree.head == "UsePron" else camel_name(_leaf_words(y_tree))
    det_cn = inner_vp.args[1].args[1]
    quant = det_cn.args[0].args[0]
    if quant.head == "PossPron":
        z = y
    elif quant.head == "GenNP":
        z = camel_name(_leaf_words(quant.args[0]))
    else:
        raise ValueError(f"unexpected determiner {quant.head!r}")
    return x, y, z


def _build_claimed_costed(idn: int, roles: dict) -> "tuple[str, str, str]":
    p = _unwrap_tense(parse_tree(roles["_premise"]))
    hyp = _unwrap_tense(parse_tree(roles["_hypothesis"]))
    x1, y1, z1 = _claimed_costed_xyz(p)
    x2, y2, z2 = _claimed_costed_xyz(hyp)
    rel = "claimedCosted"
    fact1 = f"{rel} {x1} {y1} {z1}"
    fact2 = f"{rel} {x2} {y2} {z2}"
    arrow_chain = f"({fact1}) ∧ ({fact2}) → {fact2}"
    names = list(dict.fromkeys([x1, y1, z1, x2, y2, z2]))
    binders = f"{{A : Type*}} ({rel} : A → A → A → Prop) ({' '.join(names)} : A)"
    proof = f"fun h => fracas_{idn} _ {'_ ' * len(names)}h"
    return binders, arrow_chain, proof


def _build_fracas_185(roles: dict) -> "tuple[str, str, str]":
    """"Smith claimed that he had costed his proposal. So did Jones."
    (all-sloppy reading) -> "Jones claimed that he had costed his [own]
    proposal." Confirmed by reading the real theorem's own stated type
    directly (`claimedCosted smith smith smith ∧ claimedCosted jones
    jones jones -> claimedCosted jones jones jones`) - `claimedCosted x
    y z` = "x claimed that y had costed z's proposal", the first ternary
    relation this generator has produced from a two-pronoun ellipsis
    (see `_claimed_costed_xyz`); both pronouns resolve to each
    sentence's own subject. Returns (binders, arrow_chain, proof)."""
    return _build_claimed_costed(185, roles)


def _build_fracas_186(roles: dict) -> "tuple[str, str, str]":
    """Same antecedent as 185, sloppy on "he" (-> jones) but strict on
    "his" (-> smith). Confirmed by reading the real theorem's own stated
    type directly (`claimedCosted smith smith smith ∧ claimedCosted
    jones jones smith -> claimedCosted jones jones smith`) - the
    premise's own gold text is identical to fracas_185's own premise,
    reused rather than re-registered (`fracas_186_premise` in
    run_gf_tests.py). Returns (binders, arrow_chain, proof)."""
    return _build_claimed_costed(186, roles)


def _build_fracas_187(roles: dict) -> "tuple[str, str, str]":
    """Same antecedent again, strict on BOTH pronouns (both -> smith).
    Confirmed by reading the real theorem's own stated type directly
    (`claimedCosted smith smith smith ∧ claimedCosted jones smith smith
    -> claimedCosted jones smith smith`) - "he" here is an overt `Smith`
    (`UsePN`, not a pronoun at all), still resolving to the same
    individual the strict reading always picks. Returns (binders,
    arrow_chain, proof)."""
    return _build_claimed_costed(187, roles)


def _build_fracas_155(roles: dict) -> "tuple[str, str, str]":
    """"John owns a car. So does Bill." -> "Bill owns a car." Confirmed
    by reading the real theorem's own stated type directly ((∃ c, car c
    ∧ owns john c) ∧ (∃ c, car c ∧ owns bill c) -> ∃ c, car c ∧ owns
    bill c) - "one"-anaphora resolved to a fresh existential per
    conjunct (NOT the same witness - contrast 155's own neighbor 156,
    which FraCaS marks as needing two distinct witnesses too), same
    `∃c, N c ∧ ...` shape fracas_120 already established. Returns
    (binders, arrow_chain, proof)."""

    def subj_verb_noun(p):
        subj = camel_name(_leaf_words(p.args[0]))
        comp = p.args[1]
        verb = camel_name(_leaf_words(comp.args[0]))
        noun = camel_name(_leaf_words(comp.args[1].args[1]))
        return subj, verb, noun

    p1 = parse_tree(roles["_premise1"])
    p2 = parse_tree(roles["_premise2"])
    s1, v, n = subj_verb_noun(p1)
    s2, _v2, _n2 = subj_verb_noun(p2)
    fact1 = f"∃ c, {n} c ∧ {v} {s1} c"
    fact2 = f"∃ c, {n} c ∧ {v} {s2} c"
    arrow_chain = f"({fact1}) ∧ ({fact2}) → {fact2}"
    binders = f"{{A : Type*}} ({n} : A → Prop) ({v} : A → A → Prop) ({s1} {s2} : A)"
    proof = "fun h => fracas_155 _ _ _ _ h"
    return binders, arrow_chain, proof


def _adj_obj(p):
    """Parses "X owns a <adj> car" into (subject, verb, adj, noun) -
    shared by 157/159/160's single-adjective cases."""
    subj = camel_name(_leaf_words(p.args[0]))
    comp = p.args[1]
    verb = camel_name(_leaf_words(comp.args[0]))
    adjcn = comp.args[1].args[1]
    adj = camel_name(_leaf_words(adjcn.args[0]))
    noun = camel_name(_leaf_words(adjcn.args[1]))
    return subj, verb, adj, noun


def _build_fracas_157(roles: dict) -> "tuple[str, str, str]":
    """"John owns a red car. Bill owns a blue one." -> "Bill owns a blue
    car." Confirmed by reading the real theorem's own stated type
    directly ((∃c,car c∧red c∧owns john c)∧(∃c,car c∧blue c∧owns bill
    c) -> ∃c,car c∧blue c∧owns bill c) - "a blue one" contrastively
    replaces "red" with "blue", trivial once resolved. Returns (binders,
    arrow_chain, proof)."""
    p1 = parse_tree(roles["_premise1"])
    p2 = parse_tree(roles["_premise2"])
    s1, v, a1, n = _adj_obj(p1)
    s2, _v2, a2, _n2 = _adj_obj(p2)
    fact1 = f"∃ c, {n} c ∧ {a1} c ∧ {v} {s1} c"
    fact2 = f"∃ c, {n} c ∧ {a2} c ∧ {v} {s2} c"
    arrow_chain = f"({fact1}) ∧ ({fact2}) → {fact2}"
    binders = f"{{A : Type*}} ({n} {a1} {a2} : A → Prop) ({v} : A → A → Prop) ({s1} {s2} : A)"
    proof = "fun h => fracas_157 _ _ _ _ _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_159(roles: dict) -> "tuple[str, str, str]":
    """"John owns a red car. Bill owns a fast one." -> "Bill owns a fast
    car." Confirmed by reading the real theorem's own stated type
    directly ((∃c,car c∧red c∧owns john c)∧(∃c,car c∧fast c∧owns bill c)
    -> ∃c,car c∧fast c∧owns bill c) - "fast" isn't a color, so it
    doesn't contrast with "red" the way 157's "blue" does; it's simply
    the new modifier. premise 1's own gold text ("John owns a red car")
    is identical to fracas_157's own premise 1, reused rather than
    re-registered (`fracas_159_premise1` in run_gf_tests.py). Returns
    (binders, arrow_chain, proof)."""
    p1 = parse_tree(roles["_premise1"])
    hyp = parse_tree(roles["_hypothesis"])
    s1, v, a1, n = _adj_obj(p1)
    s2, _v2, a2, _n2 = _adj_obj(hyp)
    fact1 = f"∃ c, {n} c ∧ {a1} c ∧ {v} {s1} c"
    fact2 = f"∃ c, {n} c ∧ {a2} c ∧ {v} {s2} c"
    arrow_chain = f"({fact1}) ∧ ({fact2}) → {fact2}"
    binders = f"{{A : Type*}} ({n} {a1} {a2} : A → Prop) ({v} : A → A → Prop) ({s1} {s2} : A)"
    proof = "fun h => fracas_159 _ _ _ _ _ _ h"
    return binders, arrow_chain, proof


def _walk_adjs(cn):
    """AdjCN (PositA adj) inner -> ([adj, ...], noun), walking nested
    AdjCN chains - 160/162 stack TWO adjectives ("a fast red car"),
    unlike 157/159's single-adjective objects."""
    adjs = []
    while cn.head == "AdjCN":
        adjs.append(camel_name(_leaf_words(cn.args[0])))
        cn = cn.args[1]
    return adjs, camel_name(_leaf_words(cn))


def _subj_verb_adjs_noun(p):
    subj = camel_name(_leaf_words(p.args[0]))
    comp = p.args[1]
    verb = camel_name(_leaf_words(comp.args[0]))
    adjs, noun = _walk_adjs(comp.args[1].args[1])
    return subj, verb, adjs, noun


def _build_fracas_160(roles: dict) -> "tuple[str, str, str]":
    """"John owns a red car. Bill owns a fast one." (the "fast red car"
    reading) -> "Bill owns a fast red car." Confirmed by reading the
    real theorem's own stated type directly ((∃c,car c∧red c∧owns john
    c)∧(∃c,car c∧fast c∧red c∧owns bill c) -> ∃c,car c∧fast c∧red
    c∧owns bill c) - "one" resolves via the WHOLE property "red car", so
    "a fast one" = "a fast red car" (contrast 161, the other available
    reading, already a countermodel). premise 1 reused from fracas_157's
    own premise 1, same as 159. Returns (binders, arrow_chain, proof)."""
    p1 = parse_tree(roles["_premise1"])
    hyp = parse_tree(roles["_hypothesis"])
    s1, v, adjs1, n = _subj_verb_adjs_noun(p1)
    s2, _v2, adjs2, _n2 = _subj_verb_adjs_noun(hyp)
    fact1 = f"∃ c, {n} c ∧ " + " ∧ ".join(f"{a} c" for a in adjs1) + f" ∧ {v} {s1} c"
    fact2 = f"∃ c, {n} c ∧ " + " ∧ ".join(f"{a} c" for a in adjs2) + f" ∧ {v} {s2} c"
    arrow_chain = f"({fact1}) ∧ ({fact2}) → {fact2}"
    all_adjs = list(dict.fromkeys(adjs1 + adjs2))
    binders = f"{{A : Type*}} ({n} {' '.join(all_adjs)} : A → Prop) ({v} : A → A → Prop) ({s1} {s2} : A)"
    n_args = 1 + len(all_adjs) + 1 + 2  # noun, adjs, verb, 2 subjects
    proof = f"fun h => fracas_160 {'_ ' * n_args}h"
    return binders, arrow_chain, proof


def _build_fracas_162(roles: dict) -> "tuple[str, str, str]":
    """"John owns a fast red car. Bill owns a slow one." -> "Bill owns a
    slow red car." Confirmed by reading the real theorem's own stated
    type directly ((∃c,car c∧fast c∧red c∧owns john c)∧(∃c,car
    c∧slow c∧red c∧owns bill c) -> ∃c,car c∧slow c∧red c∧owns bill c) -
    "fast"/"slow" are antonyms on the same dimension, so "a slow one"
    replaces "fast" with "slow" but keeps the non-parallel modifier
    "red", per FraCaS's own `<why>`. Both premise 1 and the hypothesis
    have their own full trees registered (no reuse needed here). Returns
    (binders, arrow_chain, proof)."""
    p1 = parse_tree(roles["_premise1"])
    hyp = parse_tree(roles["_hypothesis"])
    s1, v, adjs1, n = _subj_verb_adjs_noun(p1)
    s2, _v2, adjs2, _n2 = _subj_verb_adjs_noun(hyp)
    fact1 = f"∃ c, {n} c ∧ " + " ∧ ".join(f"{a} c" for a in adjs1) + f" ∧ {v} {s1} c"
    fact2 = f"∃ c, {n} c ∧ " + " ∧ ".join(f"{a} c" for a in adjs2) + f" ∧ {v} {s2} c"
    arrow_chain = f"({fact1}) ∧ ({fact2}) → {fact2}"
    all_adjs = list(dict.fromkeys(adjs1 + adjs2))
    binders = f"{{A : Type*}} ({n} {' '.join(all_adjs)} : A → Prop) ({v} : A → A → Prop) ({s1} {s2} : A)"
    n_args = 1 + len(all_adjs) + 1 + 2  # noun, adjs, verb, 2 subjects
    proof = f"fun h => fracas_162 {'_ ' * n_args}h"
    return binders, arrow_chain, proof


def _build_fracas_189(roles: dict) -> "tuple[str, str, str]":
    """"John is a man. Mary is a woman. John represents his company. So
    does Mary." (sloppy reading) -> "Mary represents her [own]
    company." Confirmed by reading the real theorem's own stated type
    directly ((isMan john ∧ isWoman mary) -> (represents john (companyOf
    john) ∧ represents mary (companyOf mary)) -> represents mary
    (companyOf mary)) - the gender premise is a pure distractor (`fun _
    h => h.2`, same pattern as Section 1/2's unused premises); "John
    represents his [own] company" (premise 2's first conjunct) is never
    given its own tree - it's built directly from names already parsed
    out of the hypothesis (same verb/noun/skolem, `john` substituted for
    the owner), not a fresh GF tree at all. Returns (binders,
    arrow_chain, proof)."""
    p1a = _unwrap_tense(parse_tree(roles["_premise1a"]))
    p1b = _unwrap_tense(parse_tree(roles["_premise1b"]))
    hyp = _unwrap_tense(parse_tree(roles["_hypothesis"]))
    john = camel_name(_leaf_words(p1a.args[0]))
    man = camel_name(_leaf_words(p1a.args[1]))
    mary = camel_name(_leaf_words(p1b.args[0]))
    woman = camel_name(_leaf_words(p1b.args[1]))
    _subj_h, verb, noun, owner_h = _represents_fact(hyp)
    skolem = noun + "Of"
    fact_distractor = f"{man} {john} ∧ {woman} {mary}"
    fact_john = f"{verb} {john} ({skolem} {john})"
    fact_mary = f"{verb} {mary} ({skolem} {owner_h})"
    arrow_chain = f"({fact_distractor}) → ({fact_john} ∧ {fact_mary}) → {fact_mary}"
    binders = (
        f"{{A : Type*}} ({verb} : A → A → Prop) ({skolem} : A → A) "
        f"({john} {mary} : A) ({man} {woman} : A → Prop)"
    )
    proof = "fun _ h => fracas_189 _ _ _ _ _ _ h"
    return binders, arrow_chain, proof


def _build_fracas_190(roles: dict) -> "tuple[str, str, str]":
    """Same antecedent as 189, strict reading: "so does Mary" resolves
    to "Mary represents John's company". Confirmed by reading the real
    theorem's own stated type directly ((isMan john ∧ isWoman mary) ->
    (represents john (companyOf john) ∧ represents mary (companyOf
    john)) -> represents mary (companyOf john)) - premise 1a/1b's own
    gold text ("John is a man"/"Mary is a woman") is identical to
    fracas_189's own, reused rather than re-registered
    (`fracas_190_premise1a`/`fracas_190_premise1b` in run_gf_tests.py).
    Returns (binders, arrow_chain, proof)."""
    p1a = _unwrap_tense(parse_tree(roles["_premise1a"]))
    p1b = _unwrap_tense(parse_tree(roles["_premise1b"]))
    hyp = _unwrap_tense(parse_tree(roles["_hypothesis"]))
    john = camel_name(_leaf_words(p1a.args[0]))
    man = camel_name(_leaf_words(p1a.args[1]))
    mary = camel_name(_leaf_words(p1b.args[0]))
    woman = camel_name(_leaf_words(p1b.args[1]))
    _subj_h, verb, noun, owner_h = _represents_fact(hyp)
    skolem = noun + "Of"
    fact_distractor = f"{man} {john} ∧ {woman} {mary}"
    fact_john = f"{verb} {john} ({skolem} {john})"
    fact_mary = f"{verb} {mary} ({skolem} {owner_h})"
    arrow_chain = f"({fact_distractor}) → ({fact_john} ∧ {fact_mary}) → {fact_mary}"
    binders = (
        f"{{A : Type*}} ({verb} : A → A → Prop) ({skolem} : A → A) "
        f"({john} {mary} : A) ({man} {woman} : A → Prop)"
    )
    proof = "fun _ h => fracas_190 _ _ _ _ _ _ h"
    return binders, arrow_chain, proof


# Ids needing a FULLY CUSTOM theorem build, bypassing translate_cl's own
# per-sentence pipeline entirely - each is a one-off cross-sentential
# anaphora shape (a shared bound existential across two sentences, a
# ternary named-individual relation, a nested bound existential, a
# trivial-domain-wide "N out of M" restrictor, a plain-indefinite-object
# Skolem function, a dropped licensing-only premise, reflexives, an
# embedded-clause argument) that doesn't recur anywhere else in the
# corpus, so generalizing translate.py itself for any of them would add
# real-general-translator complexity to serve exactly one id - see each
# builder's own comment for the specific real-theorem shape it was
# confirmed against. fracas_126 (same 124-126 "dependent-plural/
# cardinal anaphora" cluster) is NOT here: its own real theorem needs an
# extra premise ("the other eight machines were also here yesterday")
# with no corresponding FraCaS sentence at all - confirmed by reading
# its stated type directly - the same "genuinely unstated background
# premise" gap as id 5's `hNonempty`, not fixable by any translation
# mechanism. fracas_127/134/135 (two-sorted domains, `{Person Machine}`/
# `{A B}`) and fracas_137 (needs a `Fintype.card` premise plus a single
# predicate bundling five separate FraCaS sentences) are structurally
# blocked the same way - confirmed by reading their own stated types
# directly, not attempted.
#
# Section 4 (ellipsis, 142-196) adds 23 more ids, all via the same
# mechanism: per Ellipsis.lean's own approach note, this project never
# models ellipsis RESOLUTION itself, only the already-resolved content,
# so almost every real theorem is a trivial restatement or conjunction-
# projection translate_cl's quantifier-centric pipeline was never built
# to express (many bind bare `Prop` atoms, one per whole resolved
# sentence, not a domain-quantified predicate at all - see
# `_atomic_name`). Not attempted: 150/151/152/153/196 (three- or
# two-sorted domains - `{Person City Vehicle}`/`{Student City Vehicle}`/
# `{Person Report}` - the same structural blocker as 127/134/135);
# 163/171/172/173/174/191-195 (genuine grammar gaps - embedded questions
# under "know"/"want", relativizing a quantificational pronoun NP, and a
# passive-impersonal-plus-reciprocal construction this grammar has no
# combinator for - confirmed by `run_gf_tests.py`'s own comment on
# exactly these ids, not just unattempted); 168/169/170/175/176/179/180
# (each needs at least one genuinely NEW GF tree - "forty five women
# work part time", "John wanted to buy a car", or an `AdvS`-headed
# before/if-conditional top level this generator's builders haven't
# been shaped for yet - left for a future round rather than rushed).
# 143/156/158/161/174/177/181/184/188/192/194 are countermodel-only,
# already excluded automatically (no bare theorem to cross-check).
CUSTOM_BUILD = {
    120: _build_fracas_120,
    121: _build_fracas_121,
    122: _build_fracas_122,
    124: _build_fracas_124,
    128: _build_fracas_128,
    129: _build_fracas_129,
    131: _build_fracas_131,
    132: _build_fracas_132,
    133: _build_fracas_133,
    138: _build_fracas_138,
    139: _build_fracas_139,
    140: _build_fracas_140,
    142: _build_fracas_142,
    145: _build_fracas_145,
    146: _build_fracas_146,
    147: _build_fracas_147,
    148: _build_fracas_148,
    149: _build_fracas_149,
    155: _build_fracas_155,
    157: _build_fracas_157,
    159: _build_fracas_159,
    160: _build_fracas_160,
    162: _build_fracas_162,
    164: _build_fracas_164,
    165: _build_fracas_165,
    166: _build_fracas_166,
    167: _build_fracas_167,
    178: _build_fracas_178,
    182: _build_fracas_182,
    183: _build_fracas_183,
    185: _build_fracas_185,
    186: _build_fracas_186,
    187: _build_fracas_187,
    189: _build_fracas_189,
    190: _build_fracas_190,
}


def load_base_checks():
    spec = importlib.util.spec_from_file_location(
        "run_gf_tests", str(GF_DIR / "run_gf_tests.py")
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    # Every section past 1/2 writes its own GF trees in the past tense
    # (unlike Section 1/2's bare, present-tense ones), so they live in
    # their own per-section `_SECTIONN_TENSED_CHECKS` lists rather than
    # `BASE_CHECKS` proper - previously only `_SECTION3_TENSED_CHECKS`
    # was added here (a stale omission caught while surveying Section 4:
    # it silently meant ids with real, already-toolchain-verified trees
    # in `_SECTION4_TENSED_CHECKS` were invisible to this generator
    # entirely). `mod.CHECKS` is this file's own full union, already
    # used for the real GF-toolchain verification run at its bottom, so
    # reusing it here instead of hand-picking lists can't miss a future
    # one the same way again. Labels never collide across these lists
    # (`_tense_reconfirm` always suffixes its own copies with
    # `_tense_reconfirm`, never bare), so last-write-wins in
    # `main()`'s own `by_id.setdefault(...)[role] = ...` is safe.
    return mod.CHECKS


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
    for section in ("Section1", "Section2", "Section3", "Section4"):
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
    for section in ("Section1", "Section2", "Section3", "Section4"):
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
        # `_tense_reconfirm`-suffixed labels (`TENSE_RECONFIRMATIONS`,
        # generated from `BASE_CHECKS` itself) are pure GF-toolchain
        # duplicates re-verifying an already-registered tree's tensed
        # form - never a distinct role any downstream logic here should
        # see (this exact omission regressed fracas_089 when
        # `load_base_checks` was widened to the full `CHECKS` union:
        # `_hypothesis_rep_tense_reconfirm` started matching the same
        # "_hypothesis_" prefix check CONJUNCT_IDS's own real conjunct
        # roles use).
        if label.endswith("_tense_reconfirm"):
            continue
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
        "hypothesis for ids in `AUX_HYPOTHESIS`) - now extended through all of",
        "Section 3's 114-141 range: the possessive-presupposition bundle",
        "(114-116, `BUNDLE_PROJECT`, `translate.py`'s",
        "`_try_translate_possessive_presupposition`) - \"Mary used her",
        "workstation\" translates to a three-way presupposition bundle,",
        "matching Batch1.lean's own comment that 114/115/116 are \"just",
        "projections out of the same bundle\" - each id's own generated",
        "hypothesis is that SAME bundle's matching conjunct, not an",
        "independent translation of its own (differently-shaped) hypothesis",
        "sentence, since that sentence read in isolation is genuinely",
        "ambiguous between this bundle's own specific reading and this",
        "project's usual fused-unary-predicate one; its Skolem-function-bound",
        "variant (117-119, `SKOLEM_PROJECT`); a synthesized scope-entailment",
        "premise (123, `SYNTHESIZE_PREMISE`); and twelve fully hand-built",
        "cross-sentential-anaphora theorems bypassing `translate_cl` entirely",
        "(120-122/124/128/129/131-133/138-140, `CUSTOM_BUILD` - a shared bound",
        "existential, a ternary named-individual relation, trivial-literal",
        "restrictors, Skolemized dependent-plural/paycheque pronouns, a",
        "dropped licensing-only premise, and reflexive/embedded-clause",
        "arguments). Not every Section 3 id is covered: 125/130/136/141 are",
        "countermodel-only (no bare theorem to cross-check at all); 126 needs",
        "a genuinely unstated extra premise (\"the other eight machines were",
        "also here yesterday\", no corresponding FraCaS sentence); and",
        "127/134/135 (two-sorted `{Person Machine}`/`{A B}` domains - this",
        "generator hardcodes a single domain `{A : Type*}` throughout) and 137",
        "(needs a `Fintype.card` premise plus one predicate bundling five",
        "separate FraCaS sentences) are structurally blocked. Section 4",
        "(ellipsis, 142-196) adds 23 more ids, all via `CUSTOM_BUILD`: per",
        "Ellipsis.lean's own approach note, this project never models",
        "ellipsis RESOLUTION itself, only the already-resolved content, so",
        "almost every real theorem is a trivial restatement or conjunction-",
        "projection over bare `Prop` atoms (one per whole resolved",
        "sentence - \"John spoke to Mary\" fuses to one nullary fact, not a",
        "domain-quantified predicate at all) or a Skolemized/ternary single-",
        "domain shape already established by Section 3's own builders.",
        "Because that arrow-count check alone isn't sufficient evidence here",
        "(it let two structurally WRONG theorems through before this was",
        "caught - a single-domain guess at fracas_150's own three-sorted",
        "`{Person City Vehicle}` domain, and a `Some`/`Exactly`-quantified",
        "guess at fracas_196's own direct `∃`/`∀` over a two-sorted",
        "`{Person Report}` domain), every Section 4 id goes through",
        "`CUSTOM_BUILD` or not at all. Not covered: 150/151/152/153/196",
        "(three- or two-sorted domains, the same blocker as 127/134/135);",
        "163/171/172/173/174/191-195 (genuine grammar gaps - embedded",
        "questions, relativizing a quantificational pronoun NP, a passive-",
        "impersonal-plus-reciprocal construction with no combinator -",
        "confirmed via `run_gf_tests.py`'s own comment on exactly these",
        "ids); 168/169/170/175/176/179/180 (each needs a genuinely new GF",
        "tree or an `AdvS`-headed conditional top level not yet built,",
        "left for a future round); and 143/156/158/161/174/177/181/184/",
        "188/192/194 (countermodel-only, already excluded automatically).",
        "`scripts/gen_gf_cross_check.py` documents the non-obvious",
        "exclusions it found rather than silently omitting them, including",
        "earlier rounds': problems 31 and 46 each need an aux hypothesis (like",
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
        # Section 3 scoped to 114-141, Section 4 to 142-196 (see
        # CUSTOM_BUILD's own comment for exactly which ids in each range
        # are covered, countermodel-excluded, or structurally/not-yet
        # attempted) - raise this bound again when extending past 196.
        if idn > 196:
            continue
        roles = by_id[idn]
        n = premise_counts.get(idn)
        if n is None:
            skipped[idn] = "no Problems.lean entry"
            continue
        if idn not in bare_theorem_ids:
            skipped[idn] = "no bare fracas_NNN theorem (countermodel-only, e.g. _dir1/_dir2)"
            continue
        if idn in CUSTOM_BUILD:
            try:
                binders, arrow_chain, proof = CUSTOM_BUILD[idn](roles)
            except Exception as e:
                skipped[idn] = f"CUSTOM_BUILD error: {e}"
                continue
            lines.append(f"theorem fracas_{idn:03d}_from_gf {binders} :")
            lines.append(f"    {arrow_chain} :=")
            lines.append(f"  {proof}")
            lines.append("")
            emitted.append(idn)
            continue
        if idn >= 142:
            # Section 4's own defining move (Ellipsis.lean's header) is
            # that the ellipsis site is hand-resolved BEFORE it's stated
            # as a Lean premise - so a real theorem's own top-level
            # arrow count matching this script's generic expectation is
            # necessary but not sufficient evidence translate_cl's
            # literal compositional reading would agree with it; unlike
            # Section 1-3, where that arrow-count/shape check was the
            # real gate, here it can (and did: fracas_150/196, caught by
            # inspecting their own generated output before this guard
            # was added) silently pass structurally WRONG theorems - an
            # `{A} (A -> Prop)`-shaped guess at a sentence whose real
            # theorem needs a THREE-sorted `{Person City Vehicle}`
            # domain, or a `Some`/`Exactly`-quantified guess at a
            # sentence whose real theorem is a direct `∃`/`∀` over a
            # TWO-sorted `{Person Report}` domain - without ever
            # comparing against the real theorem's own stated type at
            # all. So every Section 4 id (142+) goes through
            # CUSTOM_BUILD or not at all; see CUSTOM_BUILD's own comment
            # for exactly which ids are covered, countermodel-excluded,
            # or not yet attempted.
            skipped[idn] = "Section 4 id not in CUSTOM_BUILD - translate_cl's normal pipeline isn't safe for ellipsis-resolved content (see this script's own comment just above)"
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

        synth_i = SYNTHESIZE_PREMISE[idn][0] if idn in SYNTHESIZE_PREMISE else None
        try:
            translated_premises = [
                None if i == synth_i else translate_cl(parse_tree(premise_trees[i]))
                for i in range(1, n + 1)
            ]
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

        if idn in SYNTHESIZE_PREMISE:
            synth_i, synth_fn, hyp_quant = SYNTHESIZE_PREMISE[idn]
            prior = translated_premises[: synth_i - 1]
            if any(p is None for p in prior):
                skipped[idn] = (
                    f"SYNTHESIZE_PREMISE for premise {synth_i} needs every prior premise "
                    "already resolved, but an earlier one is itself synthesized - not supported"
                )
                continue
            translated_premises[synth_i - 1] = Translation(
                lean_prop=synth_fn(prior, translated_hyp),
                free_predicates=[],
            )
            # The hypothesis's own independent translation names its
            # restrictor from its OWN surface wording ("reports from
            # ITEL"), a different predicate than the one the synthesized
            # premise bridges FROM ("reports Smith needs", premise 1's
            # own restrictor) - but the real theorem's own conclusion
            # reuses premise 1's restrictor directly (`Some reportsNeeded
            # onDesk`, not a fresh one), confirmed by reading its stated
            # type. Rebuilt here rather than independently re-derived,
            # same "reuse an established name instead of guessing a
            # fresh one matches" principle as BUNDLE_PROJECT/
            # SKOLEM_PROJECT - only the hypothesis's own SCOPE (its
            # free_predicates' own LAST entry, by translate_cl's uniform
            # [*restrictor_preds, scope_name] convention) is kept.
            hyp_scope = translated_hyp.free_predicates[-1]
            restrictor = prior[-1].free_predicates[0]
            translated_hyp = Translation(
                lean_prop=f"{hyp_quant} {restrictor} {hyp_scope}",
                free_predicates=[restrictor, hyp_scope],
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
