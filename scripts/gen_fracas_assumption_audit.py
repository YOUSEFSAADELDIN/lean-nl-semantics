#!/usr/bin/env python3
"""Generate LeanNLSemantics/FraCaS/AssumptionAudit.lean.

Extends this project's existing assumption-audit methodology
(LeanNLSemantics/MTT/AssumptionAudit.lean, a faithful port of
`atlas/mtt_ranta/MTT.v` Part 9 - Coq's `Print Assumptions` becomes
Lean's `#print axioms`) from the 14 MTT example theorems it already
covers to every `fracas_*` theorem in the FraCaS corpus - 472 of them
as of this run, not hand-picked.

Deliberately generated, not hand-written, for the same reason
Data/Problems.lean is: 472 `#print axioms` lines would be tedious and
error-prone to keep in sync by hand as the corpus grows. Re-run this
script after adding new FraCaS theorems; do not hand-edit the output.

Theorem names are extracted with a regex close to the one
export_fracas_manifest.py already uses
(`theorem\\s+(fracas_\\d+(?:_\\w+)?)\\s`), but anchored to the start of
a line (`^theorem...`, `re.MULTILINE`) - the unanchored version matches
a `theorem fracas_NNN ...` mention anywhere, including inside a prose
doc comment (confirmed directly: BlindEval.lean's own header comment
illustrates what a hand-proved theorem looks like by literally writing
out `theorem fracas_002 : ...` as an example mid-sentence, which the
unanchored regex happily "found" as if it were a real declaration - a
real one is always written at the start of its own line, this project's
style throughout). Also over a recursive glob (`FraCaS/**/*.lean`, not
`FraCaS/Section*/*.lean`) - the single-level glob export_fracas_manifest.py
uses would silently miss every theorem under Section1/Monotonicity/
(CrossCheck.lean's *_via_mono_nl/*_via_exist_nl theorems included),
which is exactly the reasoner-derived subset this audit most needs to
cover.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FRACAS_DIR = ROOT / "LeanNLSemantics" / "FraCaS"
OUT_PATH = FRACAS_DIR / "AssumptionAudit.lean"

# Updated by hand after each real, confirmed CI run of the generated
# file's own "FraCaS corpus assumption audit" build step (same practice
# as viz/export_mono_nl_trace.py's own hardcoded confirmed-run
# constants) - NOT computed here, since this script only extracts
# theorem names, it never runs Lean. Keeping the confirmed status here
# rather than hand-edited into the generated .lean file means
# regenerating that file (e.g. after adding new FraCaS theorems) can't
# silently wipe it the way a hand-edit there would.
CONFIRMED_STATUS = """\
**Validation status - CI-confirmed** (CI run 36931384884, commit
41fc6bd, branch blind-eval-section1): all 628 expected theorems
resolved (0 missing, 0 elaboration failures) - every theorem in every
FraCaS section (1-9) plus every `_from_gf` GF-cross-check theorem. 485
fully axiom-free ("does not depend on any axioms" at all); the
remaining 143 depend on exactly Lean/Mathlib's own standard three
(`propext`, `Classical.choice`, `Quot.sound`), the ones essentially any
nontrivial Mathlib-based proof uses. Zero depend on anything beyond
that - zero custom, per-problem, or otherwise nonstandard axioms
anywhere in the corpus. Zero use `sorryAx`. See
`assumption_audit_result.json` (committed alongside this file,
produced by `scripts/parse_fracas_assumption_audit.py` against that
run's real log) for the full per-theorem breakdown this summary was
computed from. If this file's own theorem count above no longer reads
628, this status is stale - re-run the CI step and
`parse_fracas_assumption_audit.py`, then update this constant by hand."""

THEOREM_RE = re.compile(r"^theorem\s+(fracas_\d+(?:_\w+)?)\s", re.MULTILINE)
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.MULTILINE)


def main() -> None:
    # Keyed by (namespace, bare name) - NOT bare name alone. Two files can
    # legitimately declare the same bare theorem name in DIFFERENT
    # namespaces with no actual conflict at the Lean level (confirmed
    # directly: GFCrossCheck.lean's own `fracas_002_from_gf`, inside
    # `namespace FraCaS.Section1`, coexists with GFCrossCheckBatch.lean's
    # own top-level `fracas_002_from_gf` - two distinct fully-qualified
    # names, `FraCaS.Section1.fracas_002_from_gf` vs bare
    # `fracas_002_from_gf`). A blanket `open` of every namespace plus bare
    # names would make that pair genuinely ambiguous for `#print axioms`
    # to resolve, so each name below is emitted fully qualified instead -
    # no `open` line needed at all, and only a true same-namespace,
    # same-name redeclaration is a real error.
    qualified: list[str] = []
    namespaces: set[str] = set()
    seen: dict[tuple[str, str], str] = {}

    for path in sorted(FRACAS_DIR.glob("**/*.lean")):
        if path == OUT_PATH:
            continue
        text = path.read_text()
        file_names = THEOREM_RE.findall(text)
        if not file_names:
            continue
        ns_matches = NAMESPACE_RE.findall(text)
        # Every FraCaS file so far declares at most one namespace for its
        # whole body (checked directly - grep across the tree confirmed
        # this before writing this script). Fail loudly rather than
        # silently guessing if that ever stops being true. GFCrossCheckBatch.lean
        # (and any sibling generated the same way) is the one file with
        # NO namespace at all: its own `fracas_NNN_from_gf` theorems are
        # deliberately top-level.
        if ns_matches and len(set(ns_matches)) != 1:
            print(f"error: {path} has multiple distinct namespaces {set(ns_matches)}", file=sys.stderr)
            sys.exit(1)
        ns = ns_matches[0] if ns_matches else ""
        if ns:
            namespaces.add(ns)
        for name in file_names:
            key = (ns, name)
            if key in seen:
                print(
                    f"error: theorem name {name!r} declared twice in namespace {ns!r} "
                    f"(in both {seen[key]} and {path}) - a real redeclaration, not just a "
                    "same-name-different-namespace coincidence",
                    file=sys.stderr,
                )
                sys.exit(1)
            seen[key] = str(path)
            qualified.append(f"{ns}.{name}" if ns else name)

    qualified.sort()

    lines = [
        "-- Generated by scripts/gen_fracas_assumption_audit.py - do not hand-edit;",
        "-- re-run the script instead.",
        "import LeanNLSemantics",
        "",
        "/-!",
        "# FraCaS corpus assumption audit",
        "",
        "Extends `LeanNLSemantics/MTT/AssumptionAudit.lean`'s own methodology -",
        "a faithful port of `atlas/mtt_ranta/MTT.v` Part 9, Coq's `Print",
        "Assumptions` becoming Lean's `#print axioms` - from the 14 MTT example",
        "theorems that file already covers to every `fracas_*` theorem in the",
        f"FraCaS corpus: {len(qualified)} theorems as of this generation, extracted",
        "automatically (see scripts/gen_fracas_assumption_audit.py), not",
        "hand-picked.",
        "",
        "This file is deliberately not imported by anything (it imports the",
        "root `LeanNLSemantics` umbrella to see every theorem, so importing it",
        "back from that umbrella would be circular) - `lake build` never",
        "touches it. Run directly instead",
        "(`lake env lean LeanNLSemantics/FraCaS/AssumptionAudit.lean`), same as",
        "`Section1/Monotonicity/Coverage.lean`'s own CI step.",
        "",
        "Every name below is fully qualified by its own namespace (or left",
        "bare for the handful of top-level-declared files) rather than",
        "resolved through a blanket `open` of every namespace at once - two",
        "files can legitimately declare the same bare theorem name in",
        "different namespaces with no real conflict (confirmed directly:",
        "GFCrossCheck.lean's own `fracas_002_from_gf`, inside `namespace",
        "FraCaS.Section1`, coexists with GFCrossCheckBatch.lean's own",
        "top-level `fracas_002_from_gf`), and a blanket `open` plus bare",
        "names would make that pair genuinely ambiguous for `#print axioms`",
        "to resolve.",
        "",
        CONFIRMED_STATUS,
        "-/",
        "",
    ]
    lines += [f"#print axioms {name}" for name in qualified]
    lines.append("")

    OUT_PATH.write_text("\n".join(lines))
    print(
        f"wrote {OUT_PATH}: {len(qualified)} theorems across {len(namespaces)} namespaces "
        f"({', '.join(sorted(namespaces))})",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
