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

The check compares every phrase of the problem's resolved clauses of a
kind the translator names as a predicate (`NAMED_HEADS`), named as `background.py` names it (`_name`: a verb phrase
with its determiners kept, `_scope_name`; anything else by its words),
which is how the translator names the same phrases.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "gf"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

# The naming functions are looked up when called, not imported by name,
# so the check always measures the naming actually in use (the soundness
# ablations patch it, `ablations.py`).
import background  # noqa: E402
import translate  # noqa: E402
from background import CN_HEADS, VP_HEADS, _subtrees  # noqa: E402

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


# The phrases the translator names as predicates: nouns and verb phrases
# (`background.py`'s lists), relative clauses ("who did not throw balls",
# named with their polarity), adjectives and prepositional phrases. A noun
# phrase is never one: its determiner becomes a quantifier.
NAMED_HEADS = CN_HEADS | VP_HEADS | {"UseRCl", "RelVP", "PositA", "AdAP", "PrepNP"}


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
    return tuple(x for a in t.args for x in _lost(a, keep_det))


def lost(t) -> tuple[str, ...]:
    """What `background.py`'s `_name(t)` leaves out of `t`."""
    if t.head in VP_HEADS:
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
            if st.head not in NAMED_HEADS:
                continue
            name = background._name(st)
            if name in used:
                seen.setdefault(name, set()).add(tuple(sorted(lost(st))))
    return {n: sorted(s) for n, s in seen.items() if len(s) > 1}
