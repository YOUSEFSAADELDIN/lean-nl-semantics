#!/usr/bin/env python3
"""Export a JSON dataset of the monotonicity reasoner's own trace for
Visualizer B (the reasoner-trace explorer: which FraCaS problems
`mono_nl`/`exist_nl`/`mono_nl_compose` close automatically, and exactly
which rule/position/premise substitution each one used).

Unlike Visualizer A's manifest (`export_fracas_manifest.py`), which joins
static, already-committed sources, this data is genuinely dynamic: each
theorem's trace line (`MonoStep`/`CombineStep`/`ExistentialStep`, see
`LeanNLSemantics/FraCaS/Section1/Monotonicity/Trace.lean`) only exists
because a real Lean elaboration ran the tactic and logged it via
`logInfo` - there is nothing here to derive by inspecting source text
alone. So this script's input is a captured GitHub Actions job log of
the "Monotonicity fragment coverage scan" step (`Coverage.lean`'s
`#mono_nl_coverage`, which logs one `mono_nl_coverage: attempting
{name}` marker per eligible theorem, immediately followed by the winning
tactic's own trace line(s) when one succeeds - see `Coverage.lean`'s own
comment on that marker for why it's needed to group trace lines back to
a theorem name).

Usage:
    python3 export_mono_nl_trace.py <captured-job-log.txt> > data/mono_nl_trace.json

The checked-in `data/mono_nl_trace.json` was produced this way from CI
run 36313846108 (commit 219ecca, branch fracas-rest) - the same run
`Coverage.lean`'s own header cites for the 63-proved/38-distinct/1-
failed/471-scanned numbers (that run only added the `attempting` marker
itself; the underlying reasoning is unchanged from CI run 36312200141,
commit 8934c04, Phase 4). Re-run this script against a fresh job log
whenever a later phase changes what the reasoner closes, to regenerate
Visualizer B's data in step with `Coverage.lean`'s own running log.

The trace values themselves are mangled: `MonoStep`/`ExistentialStep`
name local hypotheses/predicates by `Lean.Name`, and this scan's own
hypotheses are anonymous (`introAll` uses unnamed `intro1`) or macro-
hygiene-wrapped (`Lean.Name.mkNum`/`mkStr` nesting) rather than plain
strings once printed through the derived `Repr` instance (`Trace.lean`'s
own header already anticipated this: "pretty-printing a MonoStep into
something a reader ... can show is a separate, later concern"). `clean_name`
below is that pretty-printer: it recovers the real leaf identifier from
the hygiene-wrapped constructor tree (e.g. `accountant`, `residentWestern`
- always a genuine `variable`-block predicate name for restrictor/scope/
substFrom/substTo, per `Tactic.lean`'s own `nameOf` comment), or the
informative parenthesized suffix from a Phase-3/4 synthesized shape
label (e.g. `compose.exactlyAtLeast`), and maps the anonymous intro'd
hypothesis name (always literally "a") to `None` rather than a
meaningless placeholder.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

LEAF_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_']*)\.«_@»")
GUILL_RE = re.compile(r"`«(.*)»`?$")
PAREN_SUFFIX_RE = re.compile(r"\(([\w.]+)\)\s*$")
LAMBDA_RE = re.compile(r"^`(fun .*)$")

EXIST_RE = re.compile(
    r"exist_nl: \{ rule := FraCaS\.Section1\.Monotonicity\.ExistentialRule\.(\w+), "
    r"sourceHyp := (.*?), restrictor := (.*?), scope := (.*?) \}")
MONO_RE = re.compile(
    r"mono_nl: \{ position := FraCaS\.Section1\.Monotonicity\.Position\.(\w+), "
    r"rule := FraCaS\.Section1\.Monotonicity\.MonoRule\.(\w+), "
    r"factHyp := (.*?), substFrom := (.*?), substTo := (.*?), shapeSource := (.*?) \}")
COMBINE_RE = re.compile(
    r"mono_nl: combine \{ left := (.*?), right := (.*?), sharedLeft := (.*?), "
    r"leftConjunct := (.*?), rightConjunct := (.*?) \}")

PROBLEM_RE = re.compile(
    r'\{ id := (\d+), premises := \[(.*?)\],\s*hypothesis := "(.*?)", answer := \.(\w+) \}',
    re.DOTALL)

RULE_FAMILY = {
    "everyMonoScope": "Phase 1/2: position substitution",
    "everyRestrict": "Phase 1/2: position substitution",
    "someMonoScope": "Phase 1/2: position substitution",
    "someRestrict": "Phase 1/2: position substitution",
    "atLeastMonoScope": "Phase 1/2: position substitution",
    "atLeastRestrict": "Phase 1/2: position substitution",
    "atMostMonoScope": "Phase 1/2: position substitution",
    "atMostRestrict": "Phase 1/2: position substitution",
    "someOfNonemptyViaSome": "Category B: existential transfer",
    "someOfNonemptyViaExists": "Category B: existential transfer",
    "atLeastSome": "Category B: positive cardinality",
    "mostSome": "Category B: positive cardinality",
    "exactlySome": "Category B: positive cardinality",
}


def clean_name(raw_val: str) -> str | None:
    raw_val = raw_val.strip().rstrip(",")
    if raw_val == "none":
        return None
    inner, wrapped_some = raw_val, False
    m_some = re.match(r"^some \((.*)\)$", raw_val)
    if m_some:
        inner, wrapped_some = m_some.group(1), True
    m_lambda = LAMBDA_RE.match(inner)
    if m_lambda:
        return m_lambda.group(1)
    m_leaf = LEAF_RE.search(inner)
    if m_leaf:
        leaf = m_leaf.group(1)
        if leaf == "a":
            return "(unnamed premise)" if wrapped_some else None
        return leaf
    m_guill = GUILL_RE.search(inner)
    if m_guill:
        content = m_guill.group(1)
        m_suffix = PAREN_SUFFIX_RE.search(content)
        return m_suffix.group(1) if m_suffix else content
    return inner


def flatten(text: str) -> str:
    return " ".join(l.strip() for l in text.strip().splitlines())


def problem_id(theorem_name: str) -> int | None:
    last = theorem_name.split(".")[-1]
    if not last.startswith("fracas_"):
        return None
    digits = ""
    for ch in last[len("fracas_"):]:
        if ch.isdigit():
            digits += ch
        else:
            break
    return int(digits) if digits else None


def parse_problems() -> dict[int, dict]:
    src = (ROOT / "LeanNLSemantics/FraCaS/Data/Problems.lean").read_text()
    problems = {}
    for m in PROBLEM_RE.finditer(src):
        pid = int(m.group(1))
        premises = [p.replace('\\"', '"') for p in re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(2))]
        problems[pid] = {
            "premises": premises,
            "hypothesis": m.group(3).replace('\\"', '"'),
            "answer": m.group(4),
        }
    return problems


TIMESTAMP_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+Z ")


def strip_timestamps(log_text: str) -> str:
    """Raw GitHub Actions job logs (`get_job_logs`) prefix every line with
    an ISO timestamp - strip it so `^mono_nl_coverage: attempting`
    actually matches at column 0. A no-op on an already-stripped log."""
    return "\n".join(TIMESTAMP_RE.sub("", line) for line in log_text.splitlines())


def parse_log(log_text: str) -> list[dict]:
    log_text = strip_timestamps(log_text)
    end_idx = log_text.find("mono_nl coverage:")
    body = log_text[:end_idx] if end_idx != -1 else log_text
    parts = re.split(r"^mono_nl_coverage: attempting (.+)$", body, flags=re.MULTILINE)
    results = []
    for i in range(1, len(parts), 2):
        name = parts[i].strip()
        flat = flatten(parts[i + 1] if i + 1 < len(parts) else "")
        entry: dict = {"theorem": name}
        m_exist = EXIST_RE.search(flat)
        m_mono = MONO_RE.search(flat)
        m_combine = COMBINE_RE.search(flat)
        if m_exist:
            entry.update(
                tactic="exist_nl", rule=m_exist.group(1),
                sourceHyp=clean_name(m_exist.group(2)),
                restrictor=clean_name(m_exist.group(3)),
                scope=clean_name(m_exist.group(4)))
        elif m_mono:
            shape_source = clean_name(m_mono.group(6))
            entry.update(
                tactic="mono_nl_compose" if shape_source else "mono_nl",
                position=m_mono.group(1), rule=m_mono.group(2),
                factHyp=clean_name(m_mono.group(3)),
                substFrom=clean_name(m_mono.group(4)),
                substTo=clean_name(m_mono.group(5)))
            if shape_source:
                entry["shapeSource"] = shape_source
            if m_combine:
                entry["combine"] = {
                    "left": clean_name(m_combine.group(1)),
                    "right": clean_name(m_combine.group(2)),
                    "sharedLeft": clean_name(m_combine.group(3)),
                    "leftConjunct": clean_name(m_combine.group(4)),
                    "rightConjunct": clean_name(m_combine.group(5)),
                }
        else:
            entry.update(tactic=None, failed=True)
        results.append(entry)
    return results


def rule_family(entry: dict) -> str | None:
    if entry.get("shapeSource"):
        src = entry["shapeSource"]
        if "exactlyAtLeast" in src or "exactlyAtMost" in src:
            return "Phase 4: Exactly -> AtLeast/AtMost"
        if "someEntailsAnd" in src:
            return "Phase 4: some_trans combine"
        if entry.get("problemId") == 123:
            return "Phase 3: mono_nl_compose (Most -> Some composition)"
        return "Phase 3/4: composition (exist_nl-synthesized shape)"
    if entry.get("tactic") in ("mono_nl", "mono_nl_compose", "exist_nl"):
        return RULE_FAMILY.get(entry.get("rule"), "Phase 1/2: position substitution")
    return None


def main() -> None:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <captured-job-log.txt>", file=sys.stderr)
        raise SystemExit(1)
    log_text = Path(sys.argv[1]).read_text()
    problems = parse_problems()
    trace = parse_log(log_text)

    theorems = []
    for entry in trace:
        pid = problem_id(entry["theorem"])
        entry["problemId"] = pid
        entry["problem"] = problems.get(pid)
        entry["ruleFamily"] = rule_family(entry)
        theorems.append(entry)

    distinct = sorted({e["problemId"] for e in theorems if e.get("tactic") and e["problemId"] is not None})
    proved = [e for e in theorems if e.get("tactic")]
    failed = [e for e in theorems if not e.get("tactic")]

    summary = {
        "generatedFrom": {
            "ciRun": 36313846108,
            "commit": "219ecca095a482f51bfb17d5a5c5482ee0e86884",
            "note": ("trace/coverage numbers match CI run 36312200141 (commit 8934c04); "
                     "this run only added the per-theorem 'attempting' log marker used to "
                     "parse this export, no semantic change"),
        },
        "trivial": 14,
        "proved": len(proved),
        "distinctProblems": len(distinct),
        "eligibleFailed": len(failed),
        "outsideFragment": 393,
        "totalScanned": 471,
    }
    json.dump({"summary": summary, "theorems": theorems}, sys.stdout, indent=2)
    print(file=sys.stderr)
    print(f"proved: {len(proved)} ({len(distinct)} distinct problems), failed: {len(failed)}",
          file=sys.stderr)


if __name__ == "__main__":
    main()
