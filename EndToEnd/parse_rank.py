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

HERE = Path(__file__).resolve().parent
DEFAULT_PGF = HERE / "FraCaSParse.pgf"
# Section 1/2 sentences are tenseless clauses (`Cl`, this project's default
# target - see FraCaSLogic.gf); later sections' trees are tensed (`S`).
# Tried in this order; the first category with any reading wins.
PARSE_CATS = ("Cl", "S")
_TREE_HEADS = re.compile(r"^[A-Z][A-Za-z0-9_]*( |$)")


_VOCAB_CACHE: dict = {}


def vocabulary(pgf: Path = DEFAULT_PGF) -> frozenset:
    """Every token the grammar's concrete syntax can produce (`pg -words`)."""
    key = str(pgf)
    if key not in _VOCAB_CACHE:
        out = subprocess.run(
            ["gf", "--run", str(pgf)], input="pg -words\n",
            capture_output=True, text=True, timeout=120,
        ).stdout
        _VOCAB_CACHE[key] = frozenset(out.split())
    return _VOCAB_CACHE[key]


def tokenize(sentence: str, pgf: Path = DEFAULT_PGF) -> str:
    """A generic lexer step, the same for every sentence: drop sentence-
    final punctuation, split off commas/semicolons/colons as their own
    tokens (the grammar's `ConjNP` linearizes "Smith , Jones"), and look
    each token up in the grammar's vocabulary case-insensitively -
    FraCaS writes "Every"/"The" sentence-initially and "western" where the
    lexicon has "Western". A hyphenated token the grammar doesn't know
    whole ("stock-market") is split if every part is known. Tokens with no
    match are left as they are (the parse then fails honestly)."""
    vocab = vocabulary(pgf)
    s = sentence.strip().rstrip(".?!").strip()
    s = re.sub(r"([,;:])", r" \1 ", s)

    def lookup(tok: str):
        for v in (tok, tok.lower(), tok[:1].upper() + tok[1:], tok.capitalize(), tok.upper()):
            if v in vocab:
                return [v]
        return None

    out: list[str] = []
    for tok in s.split():
        found = lookup(tok)
        if found is None and "-" in tok:
            parts = [lookup(p) for p in tok.split("-")]
            if all(parts):
                found = [w for p in parts for w in p]
        out.extend(found if found is not None else [tok])
    return " ".join(out)


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


# Where anaphoric "one" (FraCaSLogic.gf's anaphOne_NP) may appear: as a
# bare argument of a verb, preposition or copula - "owns one", "Bill owns
# one too". Never modified ("ONE OF the leading tenors" is the partitive
# numeral, "JUST ONE accountant" the counted numeral) and never a possessor.
_ANAPH_NP_PARENTS = {"ComplSlash", "PrepNP", "PredVP", "CompNP"}


def _anaphora_well_formed(t, parent: str = "") -> bool:
    """Anaphoric "one" can only HEAD a noun phrase ("a blue one", "owns
    one"). Readings that use anaphOne_N as a compound-noun modifier ("[one]
    contract") or anaphOne_NP anywhere but a bare argument slot are not
    readings of English, so they are discarded before ranking - otherwise
    the single-node anaphor outranks the multi-node numeral "one" by size
    alone and steals sentences like "Smith signed one contract"."""
    if t.head == "CompoundCN" and t.args and _contains(t.args[0], "anaphOne_N"):
        return False
    if t.head == "anaphOne_NP" and parent not in _ANAPH_NP_PARENTS:
        return False
    return all(_anaphora_well_formed(a, t.head) for a in t.args)


# Elliptical sentences (FraCaSLogic.gf's gapping and fragments) and where
# they may stand: as a whole sentence, after "and"/"but", or as a conjunct.
_FRAGMENTS = {"GapS", "GapS2", "ElliptAdvS", "FragAdvS", "FragNPS"}
_SENTENCE_LEVEL = {"", "UttS", "AndS", "ButS", "CommaAndS", "TooS"}


def _remnant_ok(adv) -> bool:
    """A gapping or fragment remnant is a prepositional phrase or a
    one-word adverbial ("by train", "on Friday"), not a clause."""
    return adv.head == "PrepNP" or (not adv.args and adv.head.endswith("_Adv"))


def _fragments_well_formed(t, parent: str = "") -> bool:
    """A fragment is a sentence on its own ("Bill by train.", "On
    Friday."), never part of one: readings that put one inside a clause
    ("before [Bill]" as a fragment sentence) or use a noun phrase like
    "Smith left" (participle) as a gapped subject are not readings of
    English and are discarded before ranking."""
    if t.head in _FRAGMENTS:
        if parent not in _SENTENCE_LEVEL:
            return False
        if t.head in ("GapS", "GapS2") and (t.args[0].head == "PPartNP" or not all(_remnant_ok(a) for a in t.args[1:])):
            return False
        # a bare noun phrase is a fragment only after "and"/"but" ("But
        # only one woman."): alone, "Smith left." would also be one
        if t.head == "FragNPS" and (parent not in ("AndS", "ButS") or t.args[0].head == "PPartNP"):
            return False
        if t.head == "FragAdvS" and not _remnant_ok(t.args[0]):
            return False
        if t.head == "ElliptAdvS" and not _remnant_ok(t.args[2]):
            return False
    return all(_fragments_well_formed(a, t.head) for a in t.args)


def _contains(t, head: str) -> bool:
    return t.head == head or any(_contains(a, head) for a in t.args)


def _clause_modifiers_well_formed(t) -> bool:
    """A subordinate clause ("before Jones left", "if he came") modifies a
    clause or a verb phrase, never a noun or noun phrase: "[the shore
    before Jones swam to the shore]" is not a reading of English. Right association would
    otherwise prefer it, as the lowest attachment (FraCaS 270)."""
    if t.head in ("AdvCN", "AdvNP") and len(t.args) == 2 and t.args[1].head == "SubjS":
        return False
    return all(_clause_modifiers_well_formed(a) for a in t.args)


def ranked(trees: list[str]) -> list[str]:
    """Readings in preference order, ill-formed readings removed."""
    from translate import parse_tree  # local import: translate.py does not import this module

    kept = []
    for t in trees:
        tree = parse_tree(t)
        if _anaphora_well_formed(tree) and _clause_modifiers_well_formed(tree) \
                and _fragments_well_formed(tree):
            kept.append(t)
    return sorted(kept, key=rank_key)


def normalize(tree: str) -> str:
    return " ".join(_tokens(tree))
