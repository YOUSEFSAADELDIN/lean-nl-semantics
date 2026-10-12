#!/usr/bin/env python3
"""Post-hoc, not held out: which of the 989 reached MED problems the name
check (`EndToEnd/names.py`, added after the MED test) refuses.

Re-assembles each reached problem with the current pipeline against the
held-out grammar and records the refusal reason, if any, in
`namecheck.json`. The check only removes problems; every other problem's
claims are the frozen run's, so `report.py` scores the post-hoc pipeline
from the frozen verdicts minus these refusals. Run from the repository
root (needs the `gf` binary and HeldOutParse.pgf, see gen_heldout.py);
about 25 minutes.
"""
from __future__ import annotations

import csv
import functools
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import gen_heldout  # noqa: E402
from gen_heldout import gen_claims, parse_rank  # noqa: E402


def main() -> None:
    gen_claims.tokenize = functools.partial(parse_rank.tokenize, pgf=gen_heldout.HELD_PGF)
    gen_claims.parse_readings = gen_heldout._parse
    stages = json.loads(gen_heldout.STATS.read_text())["problems"]
    rows = {r["pairID"]: r for r in csv.DictReader(gen_heldout.MED.open(), delimiter="\t")}
    out = {}
    for pid, stage in sorted(stages.items(), key=lambda kv: int(kv[0])):
        if stage != "reached":
            continue
        r = rows[pid]
        claims, reason = gen_claims.assemble(int(pid), [("premise 1", r["sentence1"]), ("hypothesis", r["sentence2"])])
        out[pid] = None if claims is not None else reason
    refused = {p: why for p, why in out.items() if why}
    (HERE / "namecheck.json").write_text(json.dumps(
        {"checked": len(out), "refused": refused}, indent=1, ensure_ascii=False) + "\n")
    print(len(refused), "of", len(out), "refused")


if __name__ == "__main__":
    main()
