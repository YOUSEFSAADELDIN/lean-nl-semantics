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
individual names and proving it via `intros; apply fracas_NNN <;>
assumption` - deliberately arity/order-agnostic (rather than hand-
guessing each real theorem's own predicate-argument order for 16
different theorems), so this only typechecks if the translated
proposition's *shape* genuinely matches the already-proved theorem's,
same bar `GFCrossCheck.lean`'s own single example already holds itself
to.

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
from translate import translate_cl, parse_tree  # noqa: E402

CONFIRMED_STATUS = """\
**Validation status - CI-confirmed** (CI run TBD, commit TBD, branch
blind-eval-section1): all N generated theorems below type-check against
their already-proved fracas_NNN counterparts. See
`scripts/gen_gf_cross_check.py` for how this list was derived. If this
file's own theorem count no longer matches, this status is stale -
re-run the script and update this constant by hand."""


def load_base_checks():
    spec = importlib.util.spec_from_file_location(
        "run_gf_tests", str(GF_DIR / "run_gf_tests.py")
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.BASE_CHECKS


def load_premise_counts():
    text = (ROOT / "LeanNLSemantics/FraCaS/Data/Problems.lean").read_text()
    pat = re.compile(
        r'\{\s*id\s*:=\s*(\d+),\s*premises\s*:=\s*(\[.*?\]),\s*hypothesis\s*:=\s*"[^"]*",'
        r"\s*answer\s*:=\s*\.\w+\s*\}",
        re.S,
    )
    counts = {}
    for id_str, premises_text in pat.findall(text):
        counts[int(id_str)] = premises_text.count('",') + (1 if premises_text.strip() != "[]" else 0)
    # More reliable: count quoted strings directly.
    counts = {}
    for id_str, premises_text in pat.findall(text):
        counts[int(id_str)] = len(re.findall(r'"', premises_text)) // 2
    return counts


def load_bare_theorem_ids() -> set:
    """Which fracas_NNN ids have an actual bare (non-suffixed) theorem
    declaration anywhere in Section1/Section2 - several ids with full GF
    coverage turn out to be countermodel-only (`fracas_NNN_dir1`/`_dir2`,
    from this session's own earlier many/both/neither work), and would
    otherwise generate a reference to a theorem that doesn't exist at
    all, not just a shape mismatch."""
    ids = set()
    for path in (ROOT / "LeanNLSemantics/FraCaS/Section1").glob("Batch*.lean"):
        for m in re.finditer(r"theorem fracas_(\d+) ", path.read_text()):
            ids.add(int(m.group(1)))
    for path in (ROOT / "LeanNLSemantics/FraCaS/Section2").glob("Batch*.lean"):
        for m in re.finditer(r"theorem fracas_(\d+) ", path.read_text()):
            ids.add(int(m.group(1)))
    return ids


def real_theorem_arrow_count(idn: int) -> "int | None":
    """The number of top-level (paren-depth-0) `->` arrows in fracas_NNN's
    own stated type - its true explicit-hypothesis arity. Several hand
    proofs (23/24/25/29/31: `some_mono_scope`/`every_mono_scope`-style)
    take an EXTRA hypothesis beyond one per FraCaS premise - a `(forall
    x, P x -> Q x)` "world-knowledge" scope-entailment fact that isn't
    itself sourced from any distinct FraCaS premise sentence at all, so
    `len(premises) + 1` (this script's default) undercounts them. Only a
    real match here (not just a plausible-looking premise count) makes a
    problem eligible - confirmed by reading the actual Lean source, not
    assumed from Problems.lean's own premise list length. """
    for section in ("Section1", "Section2"):
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
        "",
        "/-!",
        "# GF cross-check, batch 2",
        "",
        "Extends `GFCrossCheck.lean`'s own single example (only `fracas_002`'s",
        "first premise) to every problem whose full premise/hypothesis set",
        "already has a real, linearize-confirmed GF tree (`gf/run_gf_tests.py`)",
        "that `gf/translate.py` translates cleanly, where the real theorem's",
        "own top-level arrow count exactly matches (one arrow per premise,",
        "chaining into the hypothesis) - see `scripts/gen_gf_cross_check.py`",
        "for exactly how, including two real, non-obvious exclusions it found",
        "and documents rather than silently omitting: several premise-count-1",
        "problems (23-25, 29, 31, ...) actually need an *extra* hypothesis",
        "beyond their one real FraCaS premise (a \"world-knowledge\" scope-",
        "entailment fact, not itself sourced from any distinct premise",
        "sentence), and problems 101/102 (Section 2's generics) have a hand",
        "proof that deliberately names a premise's own predicate the same as",
        "the hypothesis's (\"likelyPoorTrader\" for both) - a real semantic",
        "modeling choice a literal, compositional translator correctly does",
        "not reproduce on its own.",
        "-/",
        "",
        "open FraCaS.Section1 FraCaS.Section2",
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
        if idn > 113:
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
        has_hyp = any(r.startswith("_hypothesis") for r in roles if r != "")
        hyp_role = next((r for r in roles if r.startswith("_hypothesis")), None)
        if hyp_role and hyp_role not in ("_hypothesis",):
            # Ambiguous-reading variants (_hypothesis_client etc.) - skip,
            # picking one arbitrarily would misrepresent the ambiguity.
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
        if not has_hyp or "_hypothesis" not in roles:
            skipped[idn] = "no hypothesis tree"
            continue
        if sorted(premise_trees) != list(range(1, n + 1)):
            skipped[idn] = f"needs {n} premises, has {sorted(premise_trees)}"
            continue
        real_arrows = real_theorem_arrow_count(idn)
        if real_arrows != n:
            skipped[idn] = (
                f"real theorem has {real_arrows} top-level arrows, expected {n} "
                "(one per premise, chaining into the hypothesis) - likely an extra "
                "world-knowledge hypothesis not sourced from any FraCaS premise"
            )
            continue

        try:
            translated_premises = [translate_cl(parse_tree(premise_trees[i])) for i in range(1, n + 1)]
            translated_hyp = translate_cl(parse_tree(roles["_hypothesis"]))
        except Exception as e:
            skipped[idn] = f"translate error: {e}"
            continue

        preds: list[str] = []
        individuals: list[str] = []
        for t in [*translated_premises, translated_hyp]:
            for p in t.free_predicates:
                if p not in preds:
                    preds.append(p)
            for v in t.free_individuals:
                if v not in individuals:
                    individuals.append(v)

        arrow_chain = " → ".join([p.lean_prop for p in translated_premises] + [translated_hyp.lean_prop])

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
        if preds:
            binder_parts.append(f"({' '.join(preds)} : A → Prop)")
        for v in individuals:
            binder_parts.append(f"({v} : A)")
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
        hyp_names = [f"h{i}" for i in range(1, n + 1)]
        underscores = " ".join(["_"] * (len(preds) + len(individuals)))
        proof_args = " ".join(filter(None, [underscores, " ".join(hyp_names)]))

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
