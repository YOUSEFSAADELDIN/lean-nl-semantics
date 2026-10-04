#!/usr/bin/env python3
"""Generate LeanNLSemantics/FraCaS/BlindEvalParsed.lean: FraCaS problems
translated into Lean **automatically, from their original English**, for
end-to-end blind evaluation (BlindEvalParsedScan.lean).

Every other blind-evaluation scan in this project scores inference over a
*hand-translated* `Prop`. This one removes the human from the translation
step too, for every problem the pipeline can carry all the way through:

1. **English**: each premise and the hypothesis exactly as FraCaS states
   them (`FraCaS/Data/Problems.lean`), normalized only mechanically - the
   final period dropped, and the first letter lowercased if the sentence
   doesn't parse as written. Never the project's own confirmed rewordings
   in `gf/run_gf_tests.py`.
2. **Parse**: `gf/parse_rank.py`'s `parse_readings` against the restricted
   FraCaSParse grammar (see `gf/gen_parse_grammar.py` for what that
   restriction is and isn't), then its generic ranking picks one reading.
3. **Translate**: `gf/translate.py`'s `translate_cl`, unchanged.
4. **Assemble**, by one generic rule with no per-problem cases: bind every
   free predicate/individual the sentences mention universally, over one
   domain `A`, and chain `premise₁ → ... → premiseₙ → hypothesis`.
   Decidability binders are added for each unary predicate (the counting
   quantifiers `Most`/`AtLeast`/... need them). Unlike the hand-written
   theorems, **no background-knowledge premise** a human would add ("an
   Irishman winning the Nobel prize for literature wins a Nobel prize") is
   ever supplied - a problem needing one should come out "unknown", and
   that is reported as the real end-to-end result, not repaired.

A problem is skipped, with its reason reported, if any sentence fails to
parse, any top-ranked reading fails to translate, or a translation needs
something the generic rule doesn't assemble (Skolem functions, presupposition
bundles, conjunct projections, a name used at two different kinds).

Needs the `gf` binary and a compiled gf/FraCaSParse.pgf (the `build-gf` CI
job has both and regenerates this file to check it is reproducible). Do not
hand-edit the output.
"""
from __future__ import annotations

import collections
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GF_DIR = ROOT / "gf"
OUT_PATH = ROOT / "LeanNLSemantics" / "FraCaS" / "BlindEvalParsed.lean"
PROBLEMS = ROOT / "LeanNLSemantics" / "FraCaS" / "Data" / "Problems.lean"

sys.path.insert(0, str(GF_DIR))
from parse_rank import parse_readings, ranked  # noqa: E402
from translate import parse_tree, translate_cl  # noqa: E402

# Identifiers a generated predicate/individual name must not collide with.
LEAN_RESERVED = {
    "at", "by", "do", "else", "end", "fun", "have", "if", "in", "let", "match",
    "open", "show", "then", "from", "with", "where", "for", "this", "calc",
    "suffices", "obtain", "def", "theorem", "x", "A", "Prop", "Type", "Sort",
}


def load_problems():
    src = PROBLEMS.read_text()
    out = []
    for m in re.finditer(
        r'\{ id := (\d+), premises := \[(.*?)\],\s*hypothesis := "((?:[^"\\]|\\.)*)", answer := \.(\w+) \}',
        src, re.S,
    ):
        premises = re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(2))
        out.append((int(m.group(1)), premises, m.group(3), m.group(4)))
    return out


def variants(sentence: str):
    s = sentence.strip().rstrip(".?!").strip()
    yield s
    if s[:1].isupper():
        yield s[:1].lower() + s[1:]


def to_clause(t):
    if t.head == "UttS" and len(t.args) == 1:
        t = t.args[0]
    if t.head == "UseCl" and len(t.args) == 3 and t.args[1].head == "PPos":
        return t.args[2]
    return t


_parse_cache: dict = {}


def best_reading(sentence: str):
    for v in variants(sentence):
        if v not in _parse_cache:
            _parse_cache[v] = parse_readings(v)
        _cat, trees = _parse_cache[v]
        if trees:
            return ranked(trees)[0], len(trees)
    return None, 0


def assemble(idn, sentences):
    """(claim_text, None) or (None, reason)."""
    translations = []
    for role, s in sentences:
        tree, n = best_reading(s)
        if tree is None:
            return None, f"{role} does not parse: {s!r}"
        try:
            tr = translate_cl(to_clause(parse_tree(tree)))
        except Exception as e:  # translate.py signals unsupported shapes this way
            return None, f"{role} parses ({n} readings) but does not translate: {str(e)[:120]}"
        if tr.conjuncts or tr.free_functions or tr.template:
            return None, f"{role} needs non-generic assembly (conjuncts/Skolem/bundle)"
        translations.append(tr)

    kinds: dict[str, str] = {}
    order: list[str] = []
    for tr in translations:
        for name in tr.free_predicates:
            kind = "binary" if name in tr.binary_predicates else "unary"
            if kinds.setdefault(name, kind) != kind:
                return None, f"name {name} used at two arities"
            if name not in order:
                order.append(name)
        for name in tr.free_individuals:
            if kinds.setdefault(name, "individual") != "individual":
                return None, f"name {name} used as both predicate and individual"
            if name not in order:
                order.append(name)
    bad = [n for n in order if n in LEAN_RESERVED or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", n)]
    if bad:
        return None, f"generated names unusable as Lean binders: {bad}"

    unary = [n for n in order if kinds[n] == "unary"]
    binary = [n for n in order if kinds[n] == "binary"]
    inds = [n for n in order if kinds[n] == "individual"]
    binders = ["{A : Type}", "[Fintype A]"]
    if unary:
        binders.append(f"({' '.join(unary)} : A → Prop)")
        binders += [f"[DecidablePred {n}]" for n in unary]
    if binary:
        binders.append(f"({' '.join(binary)} : A → A → Prop)")
    if inds:
        binders.append(f"({' '.join(inds)} : A)")
    chain = " → ".join(f"({tr.lean_prop})" for tr in translations)
    return f"∀ {' '.join(binders)}, {chain}", None


def main() -> None:
    problems = load_problems()
    emitted: list[tuple[int, str]] = []
    skipped: dict[int, str] = {}
    for idn, premises, hypothesis, answer in problems:
        sentences = [(f"premise {i + 1}", p) for i, p in enumerate(premises)]
        sentences.append(("hypothesis", hypothesis))
        claim, reason = assemble(idn, sentences)
        if claim is None:
            skipped[idn] = reason
        else:
            emitted.append((idn, answer, claim))

    def stage(reason: str) -> str:
        for key, label in (
            ("does not parse", "a sentence does not parse"),
            ("does not translate", "a sentence parses but translate.py does not cover its reading"),
            ("non-generic assembly", "a translation needs non-generic assembly"),
            ("used", "a generated name is used at two different kinds"),
            ("unusable", "a generated name is not a usable Lean binder"),
        ):
            if key in reason:
                return label
        return reason

    reasons = collections.Counter(stage(r) for r in skipped.values())
    lines = [
        "-- Generated by scripts/gen_blind_eval_parsed.py - do not hand-edit;",
        "-- re-run the script instead (needs the gf binary - see its header).",
        "import LeanNLSemantics.FraCaS.Types",
        "import LeanNLSemantics.FraCaS.Section1.GQ",
        "import LeanNLSemantics.FraCaS.Section2.Plurals",
        "",
        "/-!",
        "# End-to-end blind evaluation: claims translated from FraCaS's English",
        "",
        "Each `fracas_NNN_parsed` below was produced with no human in the",
        "translation step: FraCaS's own English, parsed by the restricted GF",
        "grammar, the top-ranked reading translated by `gf/translate.py`, and",
        "assembled by one generic rule. See `scripts/gen_blind_eval_parsed.py`",
        "for the exact pipeline and what it deliberately does not supply (any",
        "background-knowledge premise). Evaluated by",
        "`BlindEvalParsedScan.lean`.",
        "",
        f"{len(emitted)} of {len(problems)} problems carried all the way through;",
        "the rest, by first failing stage:",
    ]
    for r, c in reasons.most_common():
        lines.append(f"- {r}: {c}")
    lines += [
        "",
        "Per-problem skip reasons (first failing sentence/stage):",
        "",
    ]
    for idn in sorted(skipped):
        # Lean block comments nest, so neither delimiter may appear inside.
        lines.append(f"- {idn}: {skipped[idn]}".replace("-/", "- /").replace("/-", "/ -"))
    lines += [
        "-/",
        "",
        "namespace FraCaS",
        "namespace BlindEvalParsedClaims",
        "open FraCaS.Section1 FraCaS.Section2",
        "",
    ]
    for idn, _answer, claim in emitted:
        lines.append(f"def fracas_{idn:03d}_parsed : Prop :=")
        lines.append(f"  {claim}")
        lines.append("")
    lines += [
        "end BlindEvalParsedClaims",
        "",
        "/-- `(problem id, gold answer, claim constant)` for every problem the",
        "pipeline carried through - read by `BlindEvalParsedScan.lean`. -/",
        "def blindEvalParsedRegistry : List (Nat × Answer × Lean.Name) := [",
    ]
    rows = [
        f"  ({idn}, .{answer}, ``BlindEvalParsedClaims.fracas_{idn:03d}_parsed)"
        for idn, answer, _ in emitted
    ]
    lines.append(",\n".join(rows))
    lines += ["]", "", "end FraCaS", ""]
    OUT_PATH.write_text("\n".join(lines))
    print(f"emitted {len(emitted)} / {len(problems)}; skipped: {dict(reasons)}")


if __name__ == "__main__":
    main()
