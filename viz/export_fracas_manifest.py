#!/usr/bin/env python3
"""Export a JSON manifest of all 342 FraCaS problems for Visualizer A
(the existing-system explorer: English -> GF/semantic structure -> MTT
representation -> Lean-verified result).

Joins three already-existing, independently-validated sources rather
than re-deriving anything:
  - LeanNLSemantics/FraCaS/Data/Problems.lean: id/premises/hypothesis/
    gold answer, generated from fracas.xml by scripts/gen_fracas_problems.py.
  - gf/run_gf_tests.py's BASE_CHECKS: which premises/hypotheses have a
    real, `linearize`-confirmed GF tree, and the exact English string
    that confirms. Imported as a module (not regex-parsed) so its
    f-string-built commands (_HAVE_RIGHT_VP and friends) resolve
    exactly the way the real CI check sees them, without this script
    re-implementing that string-building logic a second time.
  - LeanNLSemantics/FraCaS/Section{1-9}/*.lean: the actual `theorem
    fracas_NNN ... :=` signatures, extracted as display text only -
    this script does not typecheck or re-derive anything from them.

Section boundaries are the ranges each section's own batch-file header
comments already state (confirmed by grep, not assumed):
  1: 1-80, 2: 81-113, 3: 114-141, 4: 142-196, 5: 197-219, 6: 220-250,
  7: 251-325 (four ids in this range - 276, 305, 309, 310 - are absent
  from Problems.lean entirely: empty <h>/<q> in the source XML), 8:
  326-333, 9: 334-346.
"""
from __future__ import annotations

import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

SECTION_RANGES: list[tuple[int, int, int]] = [
    (1, 1, 80),
    (2, 81, 113),
    (3, 114, 141),
    (4, 142, 196),
    (5, 197, 219),
    (6, 220, 250),
    (7, 251, 325),
    (8, 326, 333),
    (9, 334, 346),
]

SECTION_NAMES = {
    1: "Generalized Quantifiers",
    2: "Plurals",
    3: "Anaphora",
    4: "Ellipsis",
    5: "Adjectives",
    6: "Comparatives",
    7: "Temporal Reference",
    8: "Verbs",
    9: "Attitudes",
}


def section_for(pid: int) -> int | None:
    for sec, lo, hi in SECTION_RANGES:
        if lo <= pid <= hi:
            return sec
    return None


def parse_problems(text: str) -> dict[int, dict]:
    problem_re = re.compile(
        r'\{\s*id\s*:=\s*(\d+),\s*premises\s*:=\s*(\[.*?\]),\s*'
        r'hypothesis\s*:=\s*"(.*?)",\s*answer\s*:=\s*\.(\w+)\s*\}',
        re.DOTALL,
    )
    string_re = re.compile(r'"((?:[^"\\]|\\.)*)"')
    out = {}
    for m in problem_re.finditer(text):
        pid = int(m.group(1))
        out[pid] = {
            "id": pid,
            "section": section_for(pid),
            "premises": string_re.findall(m.group(2)),
            "hypothesis": m.group(3),
            "answer": m.group(4),
        }
    return out


def load_gf_checks(gf_dir: Path) -> dict[int, list[dict]]:
    spec = importlib.util.spec_from_file_location("run_gf_tests", gf_dir / "run_gf_tests.py")
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    # Executing module-level code only builds BASE_CHECKS/TENSE_RECONFIRMATIONS
    # as plain list literals; main() (which shells out to a real `gf`
    # process) is never called since it's not invoked here.
    spec.loader.exec_module(mod)

    name_re = re.compile(r'^fracas_(\d+)(?:_(.+))?$')
    by_problem: dict[int, list[dict]] = {}
    for name, _cmd, expected in mod.BASE_CHECKS:
        m = name_re.match(name)
        if not m:
            continue
        pid = int(m.group(1))
        label = m.group(2) or "premise"
        by_problem.setdefault(pid, []).append({"label": label, "confirmedEnglish": expected})
    return by_problem


def load_lean_theorems(fracas_dir: Path) -> dict[int, list[dict]]:
    theorem_re = re.compile(r'theorem\s+(fracas_(\d+)(?:_\w+)?)\s+(.*?):=', re.DOTALL)
    by_problem: dict[int, list[dict]] = {}
    for path in sorted(fracas_dir.glob("Section*/*.lean")):
        text = path.read_text()
        for m in theorem_re.finditer(text):
            name, pid_str, sig = m.group(1), m.group(2), m.group(3)
            pid = int(pid_str)
            sig_clean = re.sub(r'\s+', ' ', sig).strip()
            by_problem.setdefault(pid, []).append({
                "name": name,
                "signature": sig_clean,
                "file": str(path.relative_to(fracas_dir.parent.parent)),
            })
    return by_problem


def main() -> None:
    fracas_dir = ROOT / "LeanNLSemantics" / "FraCaS"
    problems = parse_problems((fracas_dir / "Data" / "Problems.lean").read_text())
    gf_checks = load_gf_checks(ROOT / "gf")
    lean_theorems = load_lean_theorems(fracas_dir)

    records = []
    for pid in sorted(problems):
        p = problems[pid]
        rec = dict(p)
        rec["gf"] = gf_checks.get(pid, [])
        rec["lean"] = lean_theorems.get(pid, [])
        rec["gfChecked"] = bool(rec["gf"])
        rec["leanFormalized"] = bool(rec["lean"])
        records.append(rec)

    missing = sorted(set(range(1, 347)) - set(problems))
    section_summary = []
    for sec, lo, hi in SECTION_RANGES:
        sec_records = [r for r in records if r["section"] == sec]
        section_summary.append({
            "section": sec,
            "name": SECTION_NAMES[sec],
            "range": [lo, hi],
            "count": len(sec_records),
            "gfCheckedCount": sum(1 for r in sec_records if r["gfChecked"]),
            "answerCounts": {
                a: sum(1 for r in sec_records if r["answer"] == a)
                for a in ("yes", "no", "unknown", "undef")
            },
        })

    manifest = {
        "generatedFrom": "Problems.lean + run_gf_tests.py + Section*/*.lean",
        "totalProblems": len(records),
        "missingFromSource": missing,
        "sections": section_summary,
        "problems": records,
    }

    out_path = ROOT / "viz" / "data" / "fracas_manifest.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(manifest, indent=1))
    print(f"wrote {out_path} ({len(records)} problems, "
          f"{sum(1 for r in records if r['gfChecked'])} with GF checks, "
          f"{sum(1 for r in records if r['leanFormalized'])} with Lean theorems)",
          file=sys.stderr)


if __name__ == "__main__":
    main()
