#!/usr/bin/env python3
"""Turn `EndToEnd/AblationScan.lean`'s CI log into the soundness ablation
table: for the baseline under each reading rule, and for each ablation
(`EndToEnd/ablations.json`), how many verdicts match gold and which are
wrong.

Reading rules, from the baseline's per-claim results (one result per
consistent assignment of readings to the ambiguous constructions):
- every: "yes" only if every reading's yes-claim is proved (the
  pipeline's rule; reproduces `Scan.lean`),
- weak / strong: the first / last assignment alone (every ambiguity read
  weakly / strongly), as if the pipeline committed to one reading,
- any: "yes" if some reading's yes-claim is proved, "no" if some no-claim
  is (FraCoq's labelling rule for ambiguous problems).

An ablation's verdict for a problem it changes comes from its own claims
under the every-reading rule; any other problem keeps the baseline's, and
a problem it no longer reaches counts as "unknown". A wrong answer is a
"yes"/"no" that does not match the gold label ("undef" accepts only
"unknown", as in `Scan.lean`).

Run: `python3 EndToEnd/ablation_report.py LOG` (a saved CI log of the
`ablations` job).
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LINE = re.compile(r"per_claim (\S+) (\d+) (\w+) yes=(\S*) no=(\S*)")


def verdict(yes: str, no: str, rule: str) -> str:
    if rule == "every":
        y, n = bool(yes) and set(yes) == {"1"}, bool(no) and set(no) == {"1"}
    elif rule == "any":
        y, n = "1" in yes, "1" in no
    else:
        k = 0 if rule == "weak" else -1
        y, n = yes[k] == "1", no[k] == "1"
    if y and n:
        return "contradiction"
    return "yes" if y else "no" if n else "unknown"


def matches(gold: str, v: str) -> bool:
    return v == gold or (gold == "undef" and v == "unknown")


def score(verdicts: dict[int, str], gold: dict[int, str]):
    matched = sum(matches(gold[i], v) for i, v in verdicts.items())
    wrong = sorted((i, gold[i], v) for i, v in verdicts.items() if v in ("yes", "no", "contradiction") and not matches(gold[i], v))
    return matched, wrong


def main() -> None:
    text = Path(sys.argv[1]).read_text()
    try:
        text = json.loads(text)["logs_content"]
    except (ValueError, KeyError):
        pass
    runs: dict[str, dict[int, tuple[str, str]]] = {}
    gold: dict[int, str] = {}
    for m in LINE.finditer(text):
        label, idn, g, yes, no = m.group(1), int(m.group(2)), m.group(3), m.group(4), m.group(5)
        runs.setdefault(label, {})[idn] = (yes, no)
        gold[idn] = g
    manifest = json.loads((HERE / "ablations.json").read_text())
    n = len(manifest["reached"])

    for bk in ("", "_bk"):
        variant = "with background knowledge" if bk else "as translated"
        print(f"\n## {variant} ({n} problems reached by the baseline)\n")
        print("| | matched | wrong answers | which |")
        print("|---|---|---|---|")
        base = runs[f"baseline{bk}"]
        for rule in ("every", "weak", "strong", "any"):
            matched, wrong = score({i: verdict(*base[i], rule) for i in base}, gold)
            print(f"| reading rule: {rule} | {matched}/{len(base)} | {len(wrong)} | {', '.join(f'{i} ({g}→{v})' for i, g, v in wrong)} |")
        every = {i: verdict(*base[i], "every") for i in base}
        for name, m in manifest["ablations"].items():
            own = runs.get(f"{name}{bk}", {})
            verdicts = dict(every)
            for i in m["no_longer_reached"]:
                verdicts[i] = "unknown"
            for i, (yes, no) in own.items():
                verdicts[i] = verdict(yes, no, "every")
            matched, wrong = score(verdicts, gold)
            print(f"| {name} | {matched}/{len(verdicts)} | {len(wrong)} | {', '.join(f'{i} ({g}→{v})' for i, g, v in wrong)} |")


if __name__ == "__main__":
    main()
