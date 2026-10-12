#!/usr/bin/env python3
"""Every SICK figure in README.md, recomputed from the recorded verdicts.

Inputs, in this directory: `verdicts.txt` (the `sick_verdict` lines of the
scoring CI run; or pass saved CI logs of the `sick` job as arguments),
`SICK_test.tsv` and `sick.json`. The figures are the ones README.md fixed
before the run: reach, wrong answers, precision, recall over the whole
split (unreached pairs as unknown), accuracy over the whole split.
Run: `python3 EndToEnd/HeldOut/SICK/report.py`.
"""
from __future__ import annotations

import csv
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LINE = re.compile(r"sick_verdict (\S+) shard \d+/\d+ (\d+) ([ECN]) (\w+)")
LABELS = {"ENTAILMENT": "E", "CONTRADICTION": "C", "NEUTRAL": "N"}


def lower_bound(n: int, k: int, alpha: float = 0.05) -> float:
    """The two-sided Clopper-Pearson lower bound for k successes in n, by
    bisection on the binomial tail (no SciPy needed)."""
    from math import comb
    if k == 0:
        return 0.0
    tail = lambda p: sum(comb(n, i) * p ** i * (1 - p) ** (n - i) for i in range(k, n + 1))  # noqa: E731
    lo, hi = 0.0, 1.0
    for _ in range(100):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if tail(mid) < alpha / 2 else (lo, mid)
    return lo


def main() -> None:
    gold = {r["pair_ID"]: LABELS[r["entailment_label"]]
            for r in csv.DictReader((HERE / "SICK_test.tsv").open(encoding="utf-8"), delimiter="\t")}
    v: dict = {}
    for p in sys.argv[1:] or [HERE / "verdicts.txt"]:
        for label, pid, g, x in LINE.findall(Path(p).read_text()):
            v.setdefault(label, {})[pid] = (g, x)
    stages = json.loads((HERE / "sick.json").read_text())["stages"]
    decidable = sum(g in "EC" for g in gold.values())
    neutral = sum(g == "N" for g in gold.values())
    print(f"reach: {stages.get('reached', 0)} of {len(gold)} ({stages})\n")
    print("| | decided | correct | wrong | precision (95% lower bound) | recall (whole split) | accuracy (whole split) |")
    print("|---|---|---|---|---|---|---|")
    for label in ("as_translated", "with_background"):
        vs = v[label]
        decided = [(g, x) for g, x in vs.values() if x in ("yes", "no")]
        correct = sum((g, x) in (("E", "yes"), ("C", "no")) for g, x in decided)
        wrong = sorted((p for p, (g, x) in vs.items()
                        if x == "contradiction" or (x == "yes" and g != "E") or (x == "no" and g != "C")), key=int)
        matched = sum((g, x) in (("E", "yes"), ("C", "no"), ("N", "unknown")) for g, x in vs.values())
        accuracy = (matched + sum(g == "N" for p, g in gold.items() if p not in vs)) / len(gold)
        prec = f"{correct}/{len(decided)} ({lower_bound(len(decided), correct):.3f})" if decided else "-"
        print(f"| {label} | {len(decided)} | {correct} | {len(wrong)} {wrong or ''} | {prec} | "
              f"{correct / decidable:.3f} | {accuracy:.3f} |")
    print(f"\nall-unknown baseline accuracy: {neutral / len(gold):.3f}; "
          f"recall denominator: {decidable} ENTAILMENT + CONTRADICTION pairs")


if __name__ == "__main__":
    main()
