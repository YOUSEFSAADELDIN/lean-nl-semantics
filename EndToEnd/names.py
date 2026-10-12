#!/usr/bin/env python3
"""The name check: no predicate name may stand for two different phrases.

`translate.py` names a predicate after the words of its whole phrase
(`_leaf_words`), and keeps only words of the categories it lists; anything
else under the phrase leaves no trace in the name. A claim binds every
name universally, so a lost word does no harm on its own: `throwBall` may
as well mean "did not throw balls" if nothing else is said about it. It
does harm when the same name is also the name of a *different* phrase,
because then whatever holds of one is applied to the other:

- MED 2718: "Tom said he didn't drink black coffee". The whole verb phrase
  ("said he didn't drink black coffee") and the one inside it ("drink
  black coffee") are both `drinkBlackCoffee`, so the background
  knowledge `background.py` derives for the inner one ("drink black
  coffee" ⊑ "drink coffee") was applied to the outer one.
- FraCaS 30-32 and 47, before determiners were kept in names: "spend a
  lot of time" and "spend time" were one predicate.

So a problem is not translated when a name its claims use is the name of
two phrases in it that differ in what the name leaves out. Which words a
name may leave out without that being a difference is the explicit list
`DELIBERATE` below, each with its reason; everything else counts: a
negation, a verb taking a clause ("say", "believe"), an adverb ("even",
"no longer"), a pronoun, a conjunction.

The check compares every phrase of a category the translator names as a
predicate (`NAMED_CATEGORIES`, read off the grammar), named as the
translator names it (`_name`): the phrases of the problem's resolved
clauses, and the phrases its background knowledge states facts about
without their being in any sentence (a weakening, the event "finish"
stands for; `background.postulates`'s `built`). A construction with no
word of its own whose mark is missing from a name (`CONSTRUCTIONS`)
counts as left out, like a word.
"""
from __future__ import annotations

import functools
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "gf"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

# The naming functions are looked up when called, not imported by name,
# so the check always measures the naming actually in use (the soundness
# ablations patch it, `ablations.py`).
import translate  # noqa: E402
from background import _subtrees  # noqa: E402

# The grammar every parse grammar here restricts; each function's category
# is read from it, so a construction the pipeline adds ("said S" without
# "that", `ComplVSBare`) is covered without being listed here.
GRAMMAR = Path(__file__).resolve().parent / "FraCaSEndToEnd.pgf"

# What a name may leave out without changing what it stands for.
DELIBERATE = {
    # Articles and grammatical number: a determiner on a quantified noun
    # phrase becomes its quantifier, outside the name; inside a verb
    # phrase's name every `_Det` determiner and numeral is kept, and "the
    # Ns" is named "every N" (`_leaf_words`).
    "DefArt", "IndefArt", "NumSg", "NumPl",
    # Tense and aspect: the claims are tenseless (`translate.py`'s
    # `_unwrap_tense`); time adverbials are kept, as words.
    "TPres", "TPast", "TFut", "TCond", "ASimul", "AAnter",
    # Positive polarity. Negative polarity (`PNeg`, `UncNeg`) is not here.
    "PPos",
    # Relative pronouns: the relative clause's own words are kept.
    "who_RP", "IdRP",
    # A floated "all" ("the Ancient Greeks were all noted philosophers") is
    # read as the subject's universal quantifier (`readings.py`).
    "floatAll_AdV",
}


# The categories of phrase the translator names as predicates: nouns,
# verb phrases and their complements, relative clauses ("who did not throw
# balls", named with their polarity), adjectives and adverbials. Not noun
# phrases, whose determiner becomes a quantifier, nor clauses.
NAMED_CATEGORIES = {"CN", "VP", "Comp", "RCl", "RS", "AP", "Adv"}


@functools.cache
def _categories() -> dict[str, str]:
    """Each grammar function's result category (`pg -funs`)."""
    out = subprocess.run(["gf", "--run", str(GRAMMAR)], input="pg -funs\n",
                         capture_output=True, text=True, timeout=120, check=True).stdout
    cats = {}
    for line in out.splitlines():
        head, sep, typ = line.partition(" : ")
        if sep:
            cats[head.strip()] = typ.rstrip(" ;").split("->")[-1].strip()
    if not cats:
        raise RuntimeError(f"no function types read from {GRAMMAR}")
    return cats


def _name(t):
    """`t`'s predicate name as the translator gives it: a verb phrase with
    its determiners kept (`_scope_name`), anything else by its words."""
    try:
        if _categories().get(t.head) == "VP":
            return translate._scope_name(t)
        return translate.camel_name(translate._leaf_words(t))
    except Exception:
        return None


# Constructions that change what a phrase means with no word of their own.
# The translator marks each in the name (`translate.py`'s `NAME_MARKERS`,
# filled by `readings.py`); one whose marker is missing has been left out,
# like a dropped word ("was building MTALK" named like "built MTALK").
CONSTRUCTIONS = {"ProgrVP"}


def _lost(t, keep_det: bool) -> tuple[str, ...]:
    """The leaves under `t` that `_leaf_words(t, keep_det)` leaves out of
    the name, other than `DELIBERATE` ones. A node `_leaf_words` names as
    a whole ("the items" -> "every", a numeral -> its count) accounts for
    all of its leaves."""
    words = translate._leaf_words
    if not t.args:
        return () if t.head in DELIBERATE or words(t, keep_det) else (t.head,)
    parts = [w for a in t.args for w in words(a, keep_det)]
    marker = translate.NAME_MARKERS.get(t.head)
    if marker is not None:
        parts = [marker, *parts]
    if words(t, keep_det) != parts:
        return ()
    own = (t.head,) if t.head in CONSTRUCTIONS and marker is None else ()
    return own + tuple(x for a in t.args for x in _lost(a, keep_det))


def lost(t) -> tuple[str, ...]:
    """What `_name(t)` leaves out of `t`."""
    if _categories().get(t.head) == "VP":
        if translate._scope_name(t) != translate.camel_name(translate._leaf_words(t, keep_det=True)):
            # the one idiom `_scope_name` names by part of the phrase
            # ("comes cheap" -> `cheap`)
            return ()
        return _lost(t, keep_det=True)
    return _lost(t, keep_det=False)


def clashes(trees, used: set[str]) -> dict[str, list[tuple[str, ...]]]:
    """Each name in `used` that names phrases of `trees` differing in what
    the name leaves out, with those differences."""
    seen: dict[str, set[tuple[str, ...]]] = {}
    for tree in trees:
        for st in _subtrees(tree):
            if _categories().get(st.head) not in NAMED_CATEGORIES:
                continue
            name = _name(st)
            if name in used:
                seen.setdefault(name, set()).add(tuple(sorted(lost(st))))
    return {n: sorted(s) for n, s in seen.items() if len(s) > 1}
