#!/usr/bin/env python3
"""Automated `linearize` checks for gf/FraCaSLogic.gf/FraCaSLogicEng.gf,
run in CI (see .github/workflows/build.yml's build-gf job) so a future
grammar change gets checked automatically instead of relying on someone
manually running `linearize` and eyeballing the output, as every one of
these five sentences originally was (see gf/NOTES.md).

Feeds every confirmed sentence's `linearize` command to the `gf` shell
over stdin in one batch, then checks the expected English string
appears somewhere in its output - a substring check, not exact-output
matching, since gf's banner/prompt/timing text around each result isn't
part of what these tests are actually checking.
"""

from __future__ import annotations

import os
import subprocess
import sys

GF_LIB_PATH = os.environ.get("GF_LIB_PATH", os.path.expanduser("~/gf-libs"))
PATH_ARG = f"-path=.:{GF_LIB_PATH}/alltenses:{GF_LIB_PATH}/prelude"

# Keep in sync with gf/FraCaSLogicEng.gf's own confirmed-commands
# comments and gf/translate.py's examples.
CHECKS = [
    (
        "fracas_002",
        "linearize PredVP (DetCN every_Det (AdjCN (PositA italian_A) (UseN man_N))) "
        "(ComplVV want_VV (UseComp (CompCN (AdjCN (PositA great_A) (UseN tenor_N)))))",
        "every Italian man wants to be a great tenor",
    ),
    (
        "fracas_007",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA swedish_A)))",
        "some great tenors are Swedish",
    ),
    (
        "fracas_006",
        "linearize PredVP (DetCN (DetQuant no_Quant NumPl) "
        "(AdjCN (AdAP really_AdA (PositA great_A)) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA modest_A)))",
        "no really great tenors are modest",
    ),
    (
        "fracas_010",
        "linearize PredVP (DetCN most_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA italian_A)))",
        "most great tenors are Italian",
    ),
    (
        "fracas_033",
        "linearize PredVP (DetCN (DetQuant IndefArt NumSg) (UseN irishman_N)) "
        "(ComplV2 win_V2 (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))",
        "an Irishman wins a Nobel prize",
    ),
]


def main() -> int:
    gf_dir = os.path.dirname(os.path.abspath(__file__))
    pgf = os.path.join(gf_dir, "FraCaSLogic.pgf")
    if not os.path.exists(pgf):
        print(f"error: {pgf} not found - did the gf -make step run first?", file=sys.stderr)
        return 1

    script = "\n".join(cmd for _, cmd, _ in CHECKS) + "\nquit\n"
    result = subprocess.run(
        ["gf", PATH_ARG, pgf],
        input=script,
        capture_output=True,
        text=True,
        cwd=gf_dir,
        timeout=60,
    )
    print(result.stdout)
    if result.stderr:
        print(result.stderr, file=sys.stderr)

    failures = [
        (label, expected)
        for label, _cmd, expected in CHECKS
        if expected not in result.stdout
    ]

    if failures:
        print("FAILED checks:", file=sys.stderr)
        for label, expected in failures:
            print(f"  {label}: expected {expected!r} not found in gf output", file=sys.stderr)
        return 1

    print(f"All {len(CHECKS)} linearize checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
