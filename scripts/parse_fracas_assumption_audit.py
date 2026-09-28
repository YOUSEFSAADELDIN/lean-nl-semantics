#!/usr/bin/env python3
"""Parse a real CI log from the "FraCaS corpus assumption audit" build
step (LeanNLSemantics/FraCaS/AssumptionAudit.lean) into structured JSON.

Usage: python3 scripts/parse_fracas_assumption_audit.py <log_file> [out.json]

Takes a raw log file (e.g. saved from a real GitHub Actions run's "FraCaS
corpus assumption audit" step - fetch it, don't paraphrase it, same
discipline as every other confirmed-number in this project) and extracts
one record per `#print axioms` line Lean actually printed.

Lean 4's `#print axioms` output has exactly two shapes, both starting
with the theorem name in single quotes, which is enough to parse without
any prompt-marker-splitting trick (contrast gf/export_mono_nl_trace.py,
which needs that trick because gf's own REPL prompt is ambiguous - Lean's
build log has no such ambiguity, each theorem's own name anchors its own
line unambiguously):

    'name' does not depend on any axioms
    'name' depends on axioms: [propext, Classical.choice, Quot.sound]

One real wrinkle, found against the first actual CI log rather than
assumed: Lean prints the theorem's fully-qualified name here
(`FraCaS.Section1.fracas_001`) regardless of the bare name
AssumptionAudit.lean's own `#print axioms fracas_001` line asks with -
the `open FraCaS.Section1 ...` at that file's top resolves the
reference, but doesn't change what gets echoed back. So matching
against AssumptionAudit.lean's own (necessarily bare) generated name
list needs the qualified log name's last dot-component, not an exact
string match - `_last_component` below does that, and does it as a
fallback (checked after an exact-match attempt) so a name that's
already unqualified, like MTT/AssumptionAudit.lean's own
`#print axioms MTT.copred_some`, still matches on its own full name
first rather than being incorrectly shortened.

A theorem this script expected to see (from AssumptionAudit.lean's own
generated theorem list) but that never printed either shape is itself a
finding, not something to silently ignore - most likely `#print axioms`
on a name that failed to elaborate, which a truncated or filtered log
could otherwise hide.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

NO_AXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")
DEPENDS_RE = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")

STANDARD_AXIOMS = {"Classical.choice", "Quot.sound", "propext"}


def parse_log(text: str) -> dict[str, list[str]]:
    results: dict[str, list[str]] = {}
    for m in NO_AXIOMS_RE.finditer(text):
        results[m.group(1)] = []
    for m in DEPENDS_RE.finditer(text):
        axioms = [a.strip() for a in m.group(2).split(",") if a.strip()]
        results[m.group(1)] = axioms
    return results


def extract_expected_names(audit_lean_path: Path) -> list[str]:
    text = audit_lean_path.read_text()
    return re.findall(r"^#print axioms (\S+)", text, re.MULTILINE)


def _last_component(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def resolve_expected(expected: list[str], results: dict[str, list[str]]) -> dict[str, str]:
    """Maps each expected (bare) name to the actual key it matched in
    `results`, exact match preferred over a last-dot-component match."""
    by_last_component: dict[str, list[str]] = {}
    for key in results:
        by_last_component.setdefault(_last_component(key), []).append(key)

    resolved: dict[str, str] = {}
    for name in expected:
        if name in results:
            resolved[name] = name
            continue
        candidates = by_last_component.get(name, [])
        if len(candidates) == 1:
            resolved[name] = candidates[0]
        # len == 0: genuinely missing, left unresolved.
        # len > 1: ambiguous last-component collision - also left
        # unresolved rather than guessed, since that would silently
        # under-report a real problem.
    return resolved


def main() -> None:
    if len(sys.argv) < 2:
        print(__doc__, file=sys.stderr)
        sys.exit(1)
    log_path = Path(sys.argv[1])
    out_path = Path(sys.argv[2]) if len(sys.argv) > 2 else None

    text = log_path.read_text()
    results = parse_log(text)

    root = Path(__file__).resolve().parents[1]
    audit_lean = root / "LeanNLSemantics" / "FraCaS" / "AssumptionAudit.lean"
    expected = extract_expected_names(audit_lean) if audit_lean.exists() else []

    resolved = resolve_expected(expected, results)
    missing = [n for n in expected if n not in resolved]

    # Scoped strictly to the 472 expected FraCaS theorems, keyed by their
    # clean bare name - `results` also contains MTT/AssumptionAudit.lean's
    # own 14 entries (same log, same build), which must not silently
    # inflate a FraCaS-corpus-specific count.
    fracas_axioms = {name: results[key] for name, key in resolved.items()}

    nonstandard: dict[str, list[str]] = {}
    sorry_users: list[str] = []
    for name, axioms in fracas_axioms.items():
        extra = [a for a in axioms if a not in STANDARD_AXIOMS]
        if "sorryAx" in axioms:
            sorry_users.append(name)
        if extra:
            nonstandard[name] = axioms

    summary = {
        "expectedTheorems": len(expected),
        "resolvedTheorems": len(resolved),
        "missingFromLog": missing,
        "fullyAxiomFree": sum(1 for a in fracas_axioms.values() if not a),
        "standardOnly": sum(
            1 for a in fracas_axioms.values() if a and set(a) <= STANDARD_AXIOMS
        ),
        "nonstandardAxioms": nonstandard,
        "usesSorry": sorry_users,
    }

    print(json.dumps(summary, indent=1))

    if out_path:
        out_path.write_text(
            json.dumps(
                {"summary": summary, "theorems": fracas_axioms, "allLogEntries": results},
                indent=1,
            )
        )
        print(f"wrote {out_path}", file=sys.stderr)

    if missing:
        print(
            f"\nWARNING: {len(missing)} expected theorem(s) never printed axiom "
            "output - log may be truncated or a #print axioms call failed to "
            "elaborate. Not safe to report a clean result until this is zero.",
            file=sys.stderr,
        )
        sys.exit(1)


if __name__ == "__main__":
    main()
