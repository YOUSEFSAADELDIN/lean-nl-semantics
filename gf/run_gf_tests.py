#!/usr/bin/env python3
"""Automated `linearize` checks for gf/FraCaSLogic.gf/FraCaSLogicEng.gf,
run in CI (see .github/workflows/build.yml's build-gf job) so a future
grammar change gets checked automatically instead of relying on someone
manually running `linearize` and eyeballing the output, as every one of
these five sentences originally was (see gf/NOTES.md).

All checks run as one batch in a single shared `gf` session (feeding
every `linearize` command over stdin at once) - a version of this file
that instead ran each check as its own separate, short-lived `gf`
process found every single check producing blank output, a startup/
piping race specific to that lone-command-then-quit pattern, not a real
result (see NOTES.md). The shared-session approach is what's actually
reliable. To still keep one check's expected string from ever being
satisfied by a *different* check's output (the original bug this file
had), the session's output is split on the `FraCaSLogic> ` prompt
marker into one segment per command, in order, and each check is only
compared against its own segment.
"""

from __future__ import annotations

import os
import subprocess
import sys

GF_LIB_PATH = os.environ.get("GF_LIB_PATH", os.path.expanduser("~/gf-libs"))
PATH_ARG = f"-path=.:{GF_LIB_PATH}/alltenses:{GF_LIB_PATH}/prelude"
PROMPT = "FraCaSLogic> "

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
        "fracas_003",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) "
        "(AdjCN (PositA italian_A) (UseN man_N)))) "
        "(ComplVV want_VV (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) "
        "(AdjCN (PositA great_A) (UseN tenor_N))))))",
        "all Italian men want to be a great tenor",
    ),
    (
        "fracas_004_premise1",
        "linearize PredVP (DetCN each_Det (AdjCN (PositA italian_A) (UseN tenor_N))) "
        "(ComplVV want_VV (UseComp (CompAP (PositA great_A))))",
        "each Italian tenor wants to be great",
    ),
    (
        "fracas_004_premise2",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA italian_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA great_A)))",
        "some Italian tenors are great",
    ),
    (
        "fracas_008",
        "linearize PredVP (DetCN many_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA german_A)))",
        "many great tenors are German",
    ),
    (
        "fracas_009",
        "linearize PredVP (DetCN several_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA british_A)))",
        "several great tenors are British",
    ),
    (
        "fracas_015",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (UseN tenor_N)) "
        "(ComplSlash (SlashV2a take_V2) (AdvNP (MassNP (UseN part_N)) "
        "(PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN concert_N)))))",
        "at least three tenors take part in the concert",
    ),
    (
        "fracas_016",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_most_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2))))))))) (UseN tenor_N)) "
        "(AdvVP (ComplSlash (SlashV2a contribute_V2) (DetCN (DetQuant (PossPron they_Pron) NumPl) (UseN fee_N))) "
        "(PrepNP to_Prep (MassNP (UseN charity_N))))",
        "at most two tenors contribute their fees to charity",
    ),
    (
        "fracas_013_premise2",
        "linearize PredVP (DetCN (DetQuant IndefArt NumPl) "
        "(RelCN (AdjCN (PositA leading_A) (UseN tenor_N)) "
        "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAP (PositA excellent_A))))))) "
        "(UseComp (CompAP (PositA indispensable_A)))",
        "leading tenors who are excellent are indispensable",
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

    segments = result.stdout.split(PROMPT)
    # segments[0]: startup banner, before any command's result.
    # segments[1 .. len(CHECKS)]: each command's own result, in order.
    if len(segments) < len(CHECKS) + 1:
        print(
            f"error: expected at least {len(CHECKS) + 1} '{PROMPT}'-delimited "
            f"segments, got {len(segments)} - gf output shape changed unexpectedly",
            file=sys.stderr,
        )
        return 1

    failures = []
    for idx, (label, _cmd, expected) in enumerate(CHECKS):
        segment = segments[idx + 1]
        if expected not in segment:
            failures.append((label, expected, segment))

    if failures:
        print("FAILED checks:", file=sys.stderr)
        for label, expected, segment in failures:
            print(f"  {label}: expected {expected!r} not found in its own segment: {segment!r}", file=sys.stderr)
        return 1

    print(f"All {len(CHECKS)} linearize checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
