#!/usr/bin/env python3
"""Score the end-to-end scan on FraCoq's problem sets, under FraCoq's labels.

FraCoq (Bernardy & Chatzikyriakidis: IWCS 2017, NoDaLiDa 2019, IWCS 2021)
reports accuracy on an amended FraCaS: its `AnswerTypes.hs` overrules six
gold labels, turns several ambiguous problems into "yes" ("because usually
in FraCaS, if one reading entails, then problem marked as Yes"), and drops
every problem whose label is not a plain answer (`Unclear`). Its
`ResultParser.hs` then scores only problems with a clear label, and counts
an `Undef` label as compatible with any answer. This script applies the
same rules to this pipeline's verdicts, so the two systems can be compared
on the same problems and the same labels:

  - the 2017 paper's five sections (FraCaS 1, 2, 5, 6, 9);
  - the 2019 paper's eight (all but 7, temporal reference);
  - the 2021 paper's nine.

FraCoq's labels are read from a FraCoq checkout (GPL-3; nothing of it is
copied here). Verdicts come from a saved log of the `end-to-end` CI job
(`EndToEnd/Scan.lean`'s `matched`/`mismatches` lists); a problem the
pipeline does not reach counts as "unknown".

Usage:
  python3 EndToEnd/compare_fracoq.py FRACOQ_CHECKOUT SCAN_LOG

(SCAN_LOG may be the job log as plain text or as the JSON the GitHub API
returns.) The settings FraCoq and this pipeline differ in - gold trees vs
parsing FraCaS's English, hand-assisted vs automatic proofs - are stated in
EndToEnd/README.md; this script only aligns problems and labels.
"""
from __future__ import annotations

import ast
import json
import re
import sys
from pathlib import Path

SECTIONS = {1: (1, 80), 2: (81, 113), 3: (114, 141), 4: (142, 196), 5: (197, 219),
            6: (220, 250), 7: (251, 325), 8: (326, 333), 9: (334, 346)}
SUBSETS = [
    ("FraCoq 2017: sections 1, 2, 5, 6, 9", [1, 2, 5, 6, 9]),
    ("FraCoq 2019: all but section 7", [1, 2, 3, 4, 5, 6, 8, 9]),
    ("FraCoq 2021: all sections", list(range(1, 10))),
]


def section(i: int) -> int:
    return next(k for k, (a, b) in SECTIONS.items() if a <= i <= b)


def fracoq_labels(checkout: Path) -> dict[int, str]:
    """`answers` from AnswerTypes.hs. Its amendments are listed before the
    scraped labels, and `nubBy` after a stable sort keeps the first entry
    per problem, so the first occurrence of each number wins."""
    src = (checkout / "AnswerTypes.hs").read_text()
    body = src[src.index("answers ="):]
    labels: dict[int, str] = {}
    for m in re.finditer(r"\(\s*0*(\d+)\s*,\s*(Yes|No|Unknown|Undef|Unclear)", body):
        labels.setdefault(int(m.group(1)), m.group(2))
    return labels


def scan_lists(log_text: str) -> list[list]:
    """The `matched`/`mismatches` lists of both scans, in log order:
    as-translated matched, mismatches, then with-background-knowledge."""
    try:
        log_text = json.loads(log_text)["logs_content"]
    except (json.JSONDecodeError, KeyError, TypeError):
        pass
    lines = [re.sub(r"^\S+Z ", "", line) for line in log_text.split("\n")]
    out = []
    for i, line in enumerate(lines):
        if line.startswith("matched [") or line.startswith("mismatches"):
            buf, j = line.split(":", 1)[1], i
            while not buf.rstrip().endswith("]"):
                j += 1
                buf += lines[j]
            out.append(ast.literal_eval(re.sub(r"\b(yes|no|unknown|undef)\b", r"'\1'", buf.strip())))
    return out


def verdicts(matched, mismatches) -> dict[int, str]:
    v = {}
    for p, gold in matched:
        v[p] = "unknown" if gold in ("unknown", "undef") else gold
    for p, (_gold, answer) in mismatches:
        v[p] = answer
    return v


def compatible(label: str, answer: str) -> bool:
    """`ResultParser.hs`'s rule: an Undef label accepts any answer."""
    return label == "Undef" or label.lower() == answer


def main() -> int:
    checkout, log = Path(sys.argv[1]), Path(sys.argv[2])
    labels = fracoq_labels(checkout)
    lists = scan_lists(log.read_text())
    if len(lists) < 4:
        print("expected matched/mismatches lists for both scans in the log")
        return 1
    runs = {"as translated": verdicts(lists[0], lists[1]),
            "with background knowledge": verdicts(lists[2], lists[3])}
    for name, sections in SUBSETS:
        ids = sorted(i for i, a in labels.items() if a != "Unclear" and section(i) in sections)
        print(f"{name}: {len(ids)} problems with a clear FraCoq label")
        for run, v in runs.items():
            score = sum(compatible(labels[i], v.get(i, "unknown")) for i in ids)
            wrong = [i for i in ids
                     if v.get(i, "unknown") != "unknown" and not compatible(labels[i], v.get(i, "unknown"))]
            per = {k: f"{sum(compatible(labels[i], v.get(i, 'unknown')) for i in ids if section(i) == k)}"
                      f"/{sum(1 for i in ids if section(i) == k)}" for k in sections}
            print(f"  {run}: {score}/{len(ids)} = {100 * score / len(ids):.1f}%  "
                  f"(answers FraCoq's labels call wrong: {wrong or 'none'})")
            print(f"    per section: {per}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
