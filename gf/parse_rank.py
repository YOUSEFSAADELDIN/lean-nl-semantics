#!/usr/bin/env python3
"""Parse English with the restricted FraCaSParse grammar and rank the
readings - the automated replacement for hand-building a GF tree.

Ranking is deliberately generic, two standard preferences and nothing
fitted to any one sentence:

1. **Fewest nodes** (a minimal-attachment-style preference for the
   structurally simplest derivation).
2. Ties broken by **right association / late closure**: prefer the reading
   whose adverbial modifiers (`PrepNP` phrases, `PositAdvAdj`, bare `*_Adv`
   words) attach lowest, i.e. most deeply nested. "every person that has
   the right to live in Europe" ties at equal size between "in Europe"
   modifying the whole subject NP and modifying "live" inside the relative
   clause; late closure picks the latter, which is the reading the
   sentence's own hand-built tree and Lean theorem use.

Stated plainly: tie-breaker 2 was added *after* inspecting misses of
tie-breaker 1 alone on this same sentence set (parse_eval.py), so the
measured agreement is not a held-out number - only that the principle is
a textbook one, not invented for these sentences.
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

GF_DIR = Path(__file__).resolve().parent
DEFAULT_PGF = GF_DIR / "FraCaSParse.pgf"
# Section 1/2 sentences are tenseless clauses (`Cl`, this project's default
# target - see FraCaSLogic.gf); later sections' trees are tensed (`S`).
# Tried in this order; the first category with any reading wins.
PARSE_CATS = ("Cl", "S")
_TREE_HEADS = re.compile(r"^[A-Z][A-Za-z0-9_]*( |$)")


def parse_readings(sentence: str, pgf: Path = DEFAULT_PGF, timeout: int = 120):
    """(category, [tree, ...]) for the first category in PARSE_CATS with at
    least one complete parse, or (None, []) if none parses."""
    for cat in PARSE_CATS:
        out = subprocess.run(
            ["gf", "--run", str(pgf)],
            input=f'parse -cat={cat} "{sentence}"\n',
            capture_output=True, text=True, timeout=timeout,
        ).stdout
        trees = [
            line.strip() for line in out.splitlines()
            if _TREE_HEADS.match(line.strip()) and not line.startswith("The ")
        ]
        if trees:
            return cat, trees
    return None, []


def _tokens(tree: str):
    return re.findall(r"\(|\)|[A-Za-z_][A-Za-z0-9_']*", tree)


def size(tree: str) -> int:
    return sum(1 for t in _tokens(tree) if t not in "()")


def adverbial_depth(tree: str) -> int:
    depth = total = 0
    for tok in _tokens(tree):
        if tok == "(":
            depth += 1
        elif tok == ")":
            depth -= 1
        elif tok in ("PrepNP", "PositAdvAdj") or tok.endswith("_Adv"):
            total += depth
    return total


def rank_key(tree: str):
    return (size(tree), -adverbial_depth(tree), tree)


def ranked(trees: list[str]) -> list[str]:
    return sorted(trees, key=rank_key)


def normalize(tree: str) -> str:
    return " ".join(_tokens(tree))
