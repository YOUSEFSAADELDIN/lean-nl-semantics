#!/usr/bin/env python3
"""Measure the restricted-grammar parser against every CI-confirmed
English sentence in run_gf_tests.py's CHECKS.

For each sentence: parse its English (never looking at the hand tree),
then report (a) whether it parses at all, (b) whether the hand-built tree
is among the readings, (c) how many readings there are, and, for
sentences gf/translate.py covers, (d) whether every reading translates to
the same Lean Prop (i.e. the ambiguity is semantically spurious) and (e)
whether the top-ranked reading's translation equals the hand tree's.

Exit status is nonzero only for a *grammar* regression - a confirmed
sentence that no longer parses, or whose hand tree is no longer among its
readings. Ranking agreement is reported, not enforced.
"""
from __future__ import annotations

import collections
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
GF_DIR = HERE.parent / "gf"
sys.path.insert(0, str(GF_DIR))
sys.path.insert(0, str(HERE))
from parse_rank import normalize, parse_readings, ranked  # noqa: E402
from translate import App, parse_tree, translate_cl  # noqa: E402


def to_clause(t):
    """`UttS (UseCl tense PPos cl)` / `UseCl tense PPos cl` -> `cl`;
    anything else unchanged (tense carries no Lean-side content here - see
    translate.py's own `_unwrap_tense`)."""
    if t.head == "UttS" and len(t.args) == 1:
        t = t.args[0]
    if t.head == "UseCl" and len(t.args) == 3 and t.args[1].head == "PPos":
        return t.args[2]
    return t


def _show(t) -> str:
    return t.head if not t.args else "(" + " ".join([t.head] + [_show(a) for a in t.args]) + ")"


def core(tree_text: str) -> str:
    return _show(to_clause(parse_tree(tree_text)))


def translate(tree_text: str):
    try:
        return translate_cl(to_clause(parse_tree(tree_text))).lean_prop
    except Exception:
        return None


def main() -> int:
    spec = importlib.util.spec_from_file_location("run_gf_tests", GF_DIR / "run_gf_tests.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    stats = collections.Counter()
    regressions, rank_misses, readings = [], [], []
    seen = set()
    for label, cmd, english in mod.CHECKS:
        # `_tense_reconfirm` checks re-linearize an already-listed tree
        # under a tense wrapper - the same English, not a new sentence.
        if label.endswith("_tense_reconfirm"):
            continue
        hand = cmd[len("linearize "):]
        if (english, hand) in seen:
            continue
        seen.add((english, hand))
        stats["sentences"] += 1
        cat, trees = parse_readings(english)
        if not trees:
            regressions.append(f"{label}: no parse for {english!r}")
            continue
        stats["parsed"] += 1
        readings.append(len(trees))
        # Compared as bare clauses: a tensed hand tree is wrapped as
        # `UttS (UseCl ...)` while `parse -cat=S` returns `UseCl ...` and a
        # present-tense sentence parses at `Cl` directly - the same
        # clause either way (tense is not translated - see to_clause).
        if core(hand) not in {core(t) for t in trees}:
            regressions.append(f"{label}: hand tree not among {len(trees)} readings of {english!r}")
            continue
        stats["hand tree among readings"] += 1
        stats["unique reading"] += len(trees) == 1
        hand_prop = translate(hand)
        if hand_prop is None:
            continue
        stats["in translate.py coverage"] += 1
        props = {p for p in (translate(t) for t in trees) if p is not None}
        stats["all readings translate identically"] += props == {hand_prop}
        top = translate(ranked(trees)[0])
        if top == hand_prop:
            stats["top-ranked reading translates like hand tree"] += 1
        else:
            rank_misses.append(f"{label}: {english!r}\n    hand: {hand_prop}\n    top:  {top}")
    readings.sort()
    for k, v in stats.items():
        print(f"{k}: {v}")
    if readings:
        print(f"readings per parsed sentence: median {readings[len(readings) // 2]}, max {readings[-1]}")
    print(f"ranking misses [{len(rank_misses)}]:")
    print("\n".join(rank_misses))
    print(f"grammar regressions [{len(regressions)}]:")
    print("\n".join(regressions))
    return 1 if regressions else 0


if __name__ == "__main__":
    sys.exit(main())
