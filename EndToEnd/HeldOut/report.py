#!/usr/bin/env python3
"""Every MED figure in README.md, recomputed from the recorded verdicts.

Inputs, all in this directory:
- `verdicts.txt`: the `heldout_verdict` lines of the scoring CI run (or
  pass saved CI logs of the `heldout` job as arguments instead);
- `MED.tsv`, `heldout.json`: the data and the frozen run's reach;
- `namecheck.json`: the post-hoc name check's refusals
  (`posthoc_namecheck.py`).

Prints: the frozen run with and without background knowledge; the same
with the name check's refusals removed (post-hoc); and the subset Haruta,
Mineshima and Bekki (2020) score. Run: `python3 EndToEnd/HeldOut/report.py`.
"""
from __future__ import annotations

import csv
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LINE = re.compile(r"heldout_verdict (\S+) shard \d+/\d+ (\d+) (entailment|neutral) (\w+)")


def verdicts(paths) -> dict:
    out: dict = {}
    for p in paths:
        for label, pid, gold, v in LINE.findall(Path(p).read_text()):
            out.setdefault(label, {})[pid] = (gold, v)
    return out


def score(vs: dict) -> dict:
    matched = [p for p, (g, v) in vs.items() if (g == "entailment" and v == "yes") or (g == "neutral" and v in ("no", "unknown"))]
    wrong = sorted((p for p, (g, v) in vs.items()
                    if v == "contradiction" or (g == "neutral" and v == "yes") or (g == "entailment" and v == "no")), key=int)
    decided = [p for p, (_g, v) in vs.items() if v in ("yes", "no")]
    ent = [p for p, (g, _v) in vs.items() if g == "entailment"]
    proved = [p for p in ent if vs[p][1] == "yes"]
    correct = len(decided) - len([p for p in wrong if vs[p][1] in ("yes", "no")])
    return {"reached": len(vs), "matched": len(matched), "decided": len(decided),
            "entailment proved": f"{len(proved)} / {len(ent)}", "wrong": wrong,
            "precision": f"{correct}/{len(decided)} = {correct / len(decided):.1%}" if decided else "-"}


def table(title: str, rows: dict) -> None:
    print(f"\n## {title}\n")
    cols = ["reached", "matched", "decided", "entailment proved", "precision", "wrong"]
    print("| | " + " | ".join(cols) + " |")
    print("|---" * (len(cols) + 1) + "|")
    for name, s in rows.items():
        print(f"| {name} | " + " | ".join(
            f"{len(s[c])} ({', '.join(s[c])})" if c == "wrong" else str(s[c]) for c in cols) + " |")


def main() -> None:
    v = verdicts(sys.argv[1:] or [HERE / "verdicts.txt"])
    refused = set(json.loads((HERE / "namecheck.json").read_text())["refused"])
    variants = ("as_translated", "with_background")
    table("Frozen run (held out)", {k: score(v[k]) for k in variants})
    table(f"With the name check (post-hoc: {len(refused)} refused)",
          {k: score({p: x for p, x in v[k].items() if p not in refused}) for k in variants})

    # Haruta et al. 2020: "a subset (498 problems) of MED that does not
    # require world knowledge ... collected from various linguistics
    # papers" = `paper:` genre, no lexical_knowledge tag, not FraCaS or GLUE.
    rows = list(csv.DictReader((HERE / "MED.tsv").open(), delimiter="\t"))
    sub = [r for r in rows if r["genre"].startswith("paper") and "lexical_knowledge" not in r["genre"]
           and "GLUE" not in r["genre"] and "FraCaS" not in r["genre"]]
    bk = v["with_background"]
    ok = wrong = proved = reached = 0
    for r in sub:
        g, x = r["gold_label"], bk.get(r["pairID"], (None, "unknown"))[1]
        reached += r["pairID"] in bk
        ok += (g == "entailment" and x == "yes") or (g == "neutral" and x in ("no", "unknown"))
        wrong += (g == "neutral" and x == "yes") or (g == "entailment" and x == "no") or x == "contradiction"
        proved += g == "entailment" and x == "yes"
    ent = sum(r["gold_label"] == "entailment" for r in sub)
    print(f"\n## Haruta et al.'s subset ({len(sub)} problems: {ent} entailment, {len(sub) - ent} neutral)\n")
    print(f"reached {reached}; accuracy {ok}/{len(sub)} = {ok / len(sub):.3f} (unreached as unknown); "
          f"all-unknown baseline {(len(sub) - ent) / len(sub):.3f}; entailments proved {proved}/{ent}; wrong {wrong}")


if __name__ == "__main__":
    main()
