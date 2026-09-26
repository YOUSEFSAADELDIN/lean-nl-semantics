#!/usr/bin/env python3
"""Automated `linearize` checks for gf/FraCaSLogic.gf/FraCaSLogicEng.gf,
run in CI (see .github/workflows/build.yml's build-gf job) so a future
grammar change gets checked automatically instead of relying on someone
manually running `linearize` and eyeballing the output, as every one of
these five sentences originally was (see gf/NOTES.md).

Each check runs `gf` as its own separate process (one `linearize`
command per invocation, not all batched into one shared stdin session)
specifically so one check's expected string can never accidentally be
satisfied by a *different* check's output further up the same session
transcript - a real bug this file's first version had (see NOTES.md).
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
    (
        # Diagnostic, not yet relied on: NOTES.md documents that linearizing
        # a bare `S` (via UseCl directly) produced empty output, so this
        # project's target category is the tenseless `Cl`. This checks
        # whether wrapping in UttS (as gf-rgl's own treebank always does,
        # never linearizing a bare S directly) was the actual missing step
        # all along, rather than a genuine RGL limitation. A previous
        # version of this file falsely reported this passing - it batched
        # all checks into one shared gf session and checked the expected
        # string against the *whole* session's output, so this diagnostic's
        # blank result was masked by "wants to be a great tenor" already
        # appearing in fracas_002's own, separate result further up the
        # same transcript. Isolated per-process now.
        "uttS_diagnostic",
        "linearize UttS (UseCl (TTAnt TPres ASimul) PPos "
        "(PredVP (DetCN every_Det (AdjCN (PositA italian_A) (UseN man_N))) "
        "(ComplVV want_VV (UseComp (CompCN (AdjCN (PositA great_A) (UseN tenor_N)))))))",
        "wants to be a great tenor",
    ),
]


def run_gf_command(gf_dir: str, pgf: str, command: str) -> str:
    result = subprocess.run(
        ["gf", PATH_ARG, pgf],
        input=command + "\nquit\n",
        capture_output=True,
        text=True,
        cwd=gf_dir,
        timeout=60,
    )
    return result.stdout


def main() -> int:
    gf_dir = os.path.dirname(os.path.abspath(__file__))
    pgf = os.path.join(gf_dir, "FraCaSLogic.pgf")
    if not os.path.exists(pgf):
        print(f"error: {pgf} not found - did the gf -make step run first?", file=sys.stderr)
        return 1

    failures = []
    for label, command, expected in CHECKS:
        output = run_gf_command(gf_dir, pgf, command)
        print(f"-- {label}\n{output}")
        if expected not in output:
            failures.append((label, expected, output))

    if failures:
        print("FAILED checks:", file=sys.stderr)
        for label, expected, output in failures:
            print(f"  {label}: expected {expected!r} not found in gf output:\n{output}", file=sys.stderr)
        return 1

    print(f"All {len(CHECKS)} linearize checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
