#!/usr/bin/env python3
"""The lexical-premise audit of the hand-written FraCaS corpus.

For every one of the 342 problems this reads the statement the corpus
proves or evaluates - the main theorem `fracas_NNN` for a yes/no
problem, the generic claim `fracas_NNN_claim` (`BlindEvalUnknown*.lean`)
for an unknown/undef one - and splits it into premises and conclusion.
`LeanNLSemantics/FraCaS/lexical_audit.tsv` then records, by hand, three
things about them:

- `added`: a premise that translates no FraCaS sentence - knowledge the
  formalization supplies - tagged by kind (`TAGS` below);
- `stated_noun`: a premise that translates a FraCaS sentence relating
  two nouns ("Every Swede is a Scandinavian");
- `in_translation`: a yes/no theorem whose conclusion is literally one
  of its premises (or a conjunct of one), so the step from the premises
  to the hypothesis was taken by the translation, not by a proof; tagged
  by what kind of step it was (`STEPS` below).

Every premise of every problem was read; a premise the file does not
list as `added` or `stated_noun` translates a FraCaS sentence.

The script checks that the file still matches the corpus: each recorded
premise must be the premise at that position of that problem's
statement, and the `in_translation` records must be exactly the theorems
whose conclusion is one of their premises. It then prints the summary
tables `LeanNLSemantics/FraCaS/LEXICAL_AUDIT.md` reports. It exits
non-zero on any mismatch, so a change to the corpus that the audit does
not account for fails CI.

Run from the repository root: `python3 scripts/lexical_audit.py`.
"""
from __future__ import annotations

import csv
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FRACAS = ROOT / "LeanNLSemantics" / "FraCaS"
AUDIT = FRACAS / "lexical_audit.tsv"

# What an added premise supplies, and whether nouns-as-types would supply
# it without a premise (see LEXICAL_AUDIT.md for each).
TAGS = {
    "noun": "a modified noun is a kind of the noun (Irish delegate ⊑ delegate)",
    "object_noun": "the same, for a verb's object (won the contract from APCOM ⇒ won a contract)",
    "vp": "a verb phrase without a modifier or with less of a quantity (finish on time ⇒ finish)",
    "adjective": "adjective or degree knowledge (small and large exclude each other; former)",
    "verb": "what a verb entails (know, manage, see; build ⇒ finish)",
    "antonym": "two predicates exclude each other (unemployed, employed)",
    "time": "calendar and event-time facts",
    "existence": "a definite plural's restrictor is not empty",
}
STEPS = {
    "paraphrase": "the English differs only in form: coordination, there-insertion, 'it is true that'",
    "reading": "a reading of the premise was chosen in translation (many as some, or as and)",
    "discourse": "ellipsis or anaphora was resolved in translation",
    "presupposition": "a possessive's presupposition was written into the premise",
    "adjective": "an adjective's class or comparison class was settled in translation",
    "modifier": "a temporal or aspectual modifier was dropped in translation",
    "voice": "reflexive and passive were given one translation",
}

OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"


def problems() -> dict[int, tuple[list[str], str, str]]:
    src = (FRACAS / "Data" / "Problems.lean").read_text()
    out = {}
    for m in re.finditer(
        r'\{ id := (\d+), premises := \[(.*?)\],\s*hypothesis := "((?:[^"\\]|\\.)*)", answer := \.(\w+) \}',
        src, re.S,
    ):
        out[int(m.group(1))] = (re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(2)), m.group(3), m.group(4))
    return out


def split_top(s: str, sep: str) -> list[str]:
    parts, depth, cur, i = [], 0, "", 0
    while i < len(s):
        c = s[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            parts.append(cur)
            cur = ""
            i += len(sep)
            continue
        cur += c
        i += 1
    parts.append(cur)
    return [p.strip() for p in parts]


def strip_parens(s: str) -> str:
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, c in enumerate(s):
            depth += c in OPEN
            depth -= c in CLOSE
            if depth == 0 and i < len(s) - 1:
                return s
        s = s[1:-1].strip()
    return s


def binders(s: str) -> tuple[list[tuple[str, list[str], str]], str]:
    """The leading binder groups of `s`, as (closing bracket, names, type)."""
    out = []
    s = s.strip()
    while s and s[0] in "({[⦃":
        depth = 0
        for i, c in enumerate(s):
            depth += c in "({[⦃"
            depth -= c in ")}]⦄"
            if depth == 0:
                break
        group, close, s = s[1:i], s[i], s[i + 1:].strip()
        names, _, typ = group.partition(":")
        out.append((close, names.split() if typ else [], typ.strip()))
    return out, s


def is_prop(typ: str) -> bool:
    """A binder's type is a premise unless it is a domain, a number or a
    predicate."""
    return not re.fullmatch(r"(A|B|E|ℕ|Nat|Type\*?|Bool|Prop|.*→\s*(Prop|A|ℕ|Nat|Bool|Type\*?))", typ.strip())


def split_statement(stmt: str) -> tuple[list[str], str]:
    """`stmt` is what follows the declaration's name, up to `:=`."""
    stmt = " ".join(stmt.split())
    premises = []
    groups, rest = binders(stmt)
    premises += [t for close, names, t in groups if close == ")" and names and is_prop(t) for _ in names]
    if not rest.startswith(":"):
        raise ValueError(f"no type after the binders: {rest[:40]!r}")
    body = rest[1:].strip()
    while body.startswith("∀"):
        groups, after = binders(body[1:].strip())
        if not groups:
            break
        premises += [t for close, names, t in groups if close == ")" and names and is_prop(t) for _ in names]
        body = after[1:].strip()
    raw = split_top(body, "→")
    parts = []
    for i, p in enumerate(raw):
        # a quantifier at the top level scopes over everything after it
        if re.match(r"(∀|∃|fun\b|¬\s*∀|¬\s*∃)", p):
            parts.append(" → ".join(raw[i:]))
            break
        parts.append(p)
    return [strip_parens(p) for p in premises + parts[:-1]], strip_parens(parts[-1])


def statements(answers: dict[int, str]) -> dict[int, tuple[str, list[str], str]]:
    """Each problem's statement: (declaration, premises, conclusion)."""
    found: dict[int, tuple[str, str]] = {}
    for f in sorted(FRACAS.glob("Section[1-9]/*.lean")):
        if "GFCrossCheck" in f.name:
            continue
        for m in re.finditer(r"^theorem (fracas_(\d{3}))\b(.*?):=", f.read_text(), re.S | re.M):
            if answers.get(int(m.group(2))) in ("yes", "no"):
                found.setdefault(int(m.group(2)), (m.group(1), m.group(3)))
    for f in (FRACAS / "Section1" / "Monotonicity" / "BlindEvalUnknown.lean", FRACAS / "BlindEvalUnknown3to9.lean"):
        for m in re.finditer(r"^def (fracas_(\d{1,3})_claim) : Prop :=\s*(.*?)(?=\n\s*\n|\n--|\ndef |\nend )",
                             f.read_text(), re.S | re.M):
            if answers.get(int(m.group(2))) not in ("yes", "no"):
                found.setdefault(int(m.group(2)), (m.group(1), ": " + m.group(3)))
    out = {}
    for idn, (name, stmt) in found.items():
        premises, conclusion = split_statement(stmt)
        out[idn] = (name, premises, conclusion)
    return out


def norm(s: str) -> str:
    return " ".join(strip_parens(s).split())


def conjuncts(s: str) -> list[str]:
    return [norm(p) for p in split_top(s, "∧")]


def concluded_by_translation(premises: list[str], conclusion: str) -> bool:
    known = {norm(p) for p in premises} | {c for p in premises for c in conjuncts(p)}
    c = norm(conclusion)
    return c in known or (c.startswith("¬") and norm(c[1:]) in known)


def main() -> int:
    probs = problems()
    answers = {i: a for i, (_p, _h, a) in probs.items()}
    stmts = statements(answers)
    errors = [f"{i}: no statement found" for i in probs if i not in stmts]

    rows = list(csv.DictReader(AUDIT.open(encoding="utf-8"), delimiter="\t"))
    added = defaultdict(list)
    stated = defaultdict(list)
    steps: dict[int, str] = {}
    for r in rows:
        idn, kind = int(r["id"]), r["record"]
        if idn not in stmts:
            errors.append(f"{idn}: recorded but has no statement")
            continue
        _name, premises, conclusion = stmts[idn]
        if kind in ("added", "stated_noun"):
            k = int(r["index"])
            if k >= len(premises) or norm(premises[k]) != norm(r["text"]):
                got = premises[k] if k < len(premises) else "(none)"
                errors.append(f"{idn}: premise {k} is now {got!r}, the audit has {r['text']!r}")
            if kind == "added":
                if r["tag"] not in TAGS:
                    errors.append(f"{idn}: unknown tag {r['tag']!r}")
                added[idn].append(r["tag"])
            else:
                stated[idn].append(r["text"])
        elif kind == "in_translation":
            if r["tag"] not in STEPS:
                errors.append(f"{idn}: unknown step {r['tag']!r}")
            if norm(conclusion) != norm(r["text"]):
                errors.append(f"{idn}: conclusion is now {conclusion!r}, the audit has {r['text']!r}")
            steps[idn] = r["tag"]
        else:
            errors.append(f"{idn}: unknown record {kind!r}")

    vacuous = {i for i, (_n, p, c) in stmts.items() if answers[i] in ("yes", "no") and concluded_by_translation(p, c)}
    for i in sorted(vacuous - steps.keys()):
        errors.append(f"{i}: its conclusion is one of its premises, and the audit does not say why")
    for i in sorted(steps.keys() - vacuous):
        errors.append(f"{i}: recorded as concluded in translation, but its conclusion is not a premise")

    if errors:
        print("lexical audit out of date:", *errors, sep="\n  ")
        return 1

    yes_no = sum(a in ("yes", "no") for a in answers.values())
    n_premises = sum(len(p) for _n, p, _c in stmts.values())
    by_tag = Counter(t for ts in added.values() for t in ts)
    print(f"{len(stmts)} problems ({yes_no} yes/no, {len(stmts) - yes_no} unknown/undef), {n_premises} premises read\n")
    print(f"added premises: {sum(by_tag.values())}, in {len(added)} problems\n")
    print("| kind | premises | problems |")
    print("|---|---|---|")
    for tag in TAGS:
        ids = sorted(i for i, ts in added.items() if tag in ts)
        print(f"| {tag} | {by_tag[tag]} | {', '.join(map(str, ids))} |")
    print(f"\nnoun-to-noun premises FraCaS states: {sum(map(len, stated.values()))}, "
          f"in {len(stated)} problems: {', '.join(map(str, sorted(stated)))}\n")
    print(f"yes/no theorems concluded in translation: {len(steps)} of {yes_no}\n")
    print("| step | theorems | problems |")
    print("|---|---|---|")
    for step in STEPS:
        ids = sorted(i for i, s in steps.items() if s == step)
        print(f"| {step} | {len(ids)} | {', '.join(map(str, ids))} |")
    return 0


if __name__ == "__main__":
    sys.exit(main())
