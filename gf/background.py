#!/usr/bin/env python3
"""Problem-independent background knowledge for the end-to-end pipeline
(EndToEnd/gen_claims.py).

translate.py names a predicate after the words of its whole CN/VP subtree
("win the Nobel prize for literature" -> `winNobelPrizeForLiterature`),
which loses the compositional fact that it entails "win a Nobel prize".
Every hand-written FraCaS theorem supplies facts like that as explicit
premises; this module derives the same *kinds* of facts mechanically, and
nothing else. Two sources, both stated here in full:

1. **Structural entailments, read off the parse trees.** For each
   predicate-defining subtree in a problem's sentences, every tree obtained
   by deleting intersective modifiers in upward-monotone positions is a
   weakening; if a weakening's name is another predicate the same problem
   mentions, `∀ x, P x → Q x` is added. The deletions allowed:
   - an adjective on a noun (`AdjCN`), unless the adjective is listed in
     `NON_SUBSECTIVE` ("former", "fake", ...: a former student is not
     thereby a student);
   - an adverbial/PP on a noun (`AdvCN`) or verb phrase (`AdvVP`), unless
     the adverb is listed in `NON_VERIDICAL`, or the PP is a durative
     measure ("for two hours" - `_is_aspectual`), wherever it attaches;
   - a relative clause on a noun (`RelCN`);
   - a degree word on an adjective (`AdAP`: "really great" -> "great");
   - recursively inside a verb's object or a copula complement, but only
     when that NP is existential or definite-singular ("a/some/several/
     the X") - never under `every`/`no`/`few` (downward or non-monotone)
     and never under a verb taking a verb phrase (`want`, `can`, ...),
     whose complements are not monotone in general.
2. **A small, closed degree-semantics lexicon.** `ANTONYMS` pairs gradable
   adjectives with their contraries. When a problem mentions the relevant
   predicates: contraries are exclusive (`¬ (small x ∧ large x)`, and the
   same for "small N"/"large N" over the *same* noun N - comparison class
   held fixed); a comparative's standard transfers upward (`aThan x y → a
   y → a x`, `aAs x y → a y → a x`); comparatives are asymmetric (`aThan
   x y → ¬ aThan y x`); antonym comparatives are converses (`aThan x y ↔
   bThan y x`).

Nothing here is keyed by problem number or gold answer. The lexicon lists
were written with this corpus in view, so they are not a held-out
resource - see BLIND_EVAL.md, which reports the end-to-end score both
with and without this module.
"""
from __future__ import annotations

import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from translate import App, _leaf_words, _scope_name, camel_name  # noqa: E402

NON_SUBSECTIVE = {"former", "fake", "alleged", "false", "imaginary", "would-be", "fictional", "potential"}
NON_VERIDICAL = {"allegedly", "apparently", "likely", "possibly", "nearly", "almost"}
# Prepositions whose verb-phrase adverbials change aspect rather than just
# restricting the event: "write a report FOR TWO HOURS" does not entail
# "write a report" (the imperfective paradox - an accomplishment with a
# durative adverbial need not culminate). Added after the first CI run of
# this module produced exactly that wrong inference (FraCaS 304) - a rule
# found from an observed failure, stated as such in BLIND_EVAL.md.
ASPECTUAL_PREPS = {"for"}
# ...but only when the PP measures a duration ("for two hours"), wherever
# the parser attached it - "the Nobel prize FOR LITERATURE" is an ordinary
# restrictive modifier and stays deletable (FraCaS 17).
TIME_UNITS = {"second", "minute", "hour", "day", "week", "month", "year", "decade"}


def _is_aspectual(pp) -> bool:
    # FraCaSLogic.gf also lexicalizes some durations as fixed adverbs
    # (`forTwoHours_Adv`, `forAYear_Adv`, ...) - the same thing, one token.
    if not pp.args and pp.head.endswith("_Adv"):
        word = _lemma(pp.head).lower()
        return any(word.startswith(p) for p in ASPECTUAL_PREPS) and any(u in word for u in TIME_UNITS)
    if not (pp.head == "PrepNP" and len(pp.args) == 2):
        return False
    if _lemma(pp.args[0].head) not in ASPECTUAL_PREPS:
        return False
    return any(_lemma(h) in TIME_UNITS for h in _leaf_heads(pp.args[1]))
ANTONYMS = [("small", "large"), ("fast", "slow"), ("fat", "thin"), ("old", "new"), ("cheap", "expensive")]

CN_HEADS = {"UseN", "AdjCN", "AdvCN", "RelCN", "CompoundCN", "SentCN", "ApposCN"}
VP_HEADS = {"UseComp", "ComplSlash", "AdvVP", "ComplVV", "UseV", "PassV2", "AdVVP", "ComplVS", "ComplVQ"}
UPWARD_DETS = {"IndefArt", "someSg_Det", "somePl_Det", "several_Det", "aFew_Det", "aLotOf_Det", "many_Det"}


def _lemma(leaf_head: str) -> str:
    return leaf_head.rsplit("_", 1)[0].split("8")[0]


def _np_allows_weakening(np) -> bool:
    """Is this NP's restrictor in an upward-monotone position?"""
    if np.head == "MassNP":
        return True
    if np.head == "DetCN" and len(np.args) == 2:
        det = np.args[0]
        if det.head in UPWARD_DETS:
            return True
        if det.head == "DetQuant" and len(det.args) == 2:
            quant, num = det.args
            if quant.head == "IndefArt":
                return True
            if quant.head == "DefArt" and num.head == "NumSg":
                return True
    return False


def weakenings(t):
    """Every tree obtained from `t` by one allowed deletion, recursively
    (so the result is closed under repeated deletions)."""
    out = []
    h, a = t.head, t.args
    if h == "AdjCN" and len(a) == 2:
        adj = a[0]
        if not (adj.head == "PositA" and adj.args and _lemma(adj.args[0].head) in NON_SUBSECTIVE):
            out.append(a[1])
        out += [App("AdjCN", [w, a[1]]) for w in weakenings(a[0])]
        out += [App("AdjCN", [a[0], w]) for w in weakenings(a[1])]
    elif h in ("AdvCN", "RelCN") and len(a) == 2:
        if not (h == "AdvCN" and _is_aspectual(a[1])):
            out.append(a[0])
        out += [App(h, [w, a[1]]) for w in weakenings(a[0])]
    elif h == "AdvVP" and len(a) == 2:
        adv_words = {_lemma(x) for x in _leaf_heads(a[1])}
        if not (adv_words & NON_VERIDICAL) and not _is_aspectual(a[1]):
            out.append(a[0])
        out += [App("AdvVP", [w, a[1]]) for w in weakenings(a[0])]
    elif h == "AdAP" and len(a) == 2:
        out.append(a[1])
    elif h == "ComplSlash" and len(a) == 2:
        np = a[1]
        if _np_allows_weakening(np):
            out += [App("ComplSlash", [a[0], w]) for w in _np_weakenings(np)]
    elif h == "UseComp" and len(a) == 1:
        comp = a[0]
        if comp.head == "CompCN":
            out += [App("UseComp", [App("CompCN", [w])]) for w in weakenings(comp.args[0])]
        elif comp.head == "CompAP":
            out += [App("UseComp", [App("CompAP", [w])]) for w in weakenings(comp.args[0])]
        elif comp.head == "CompNP" and _np_allows_weakening(comp.args[0]):
            out += [App("UseComp", [App("CompNP", [w])]) for w in _np_weakenings(comp.args[0])]
    # everything else (ComplVV and other complement-taking verbs, PositA,
    # UseN, ...) has no allowed deletion
    closed, seen = [], set()
    for w in out:
        for x in [w, *weakenings(w)]:
            k = repr(x)
            if k not in seen:
                seen.add(k)
                closed.append(x)
    return closed


def _np_weakenings(np):
    if np.head == "MassNP":
        return [App("MassNP", [w]) for w in weakenings(np.args[0])]
    if np.head == "DetCN":
        return [App("DetCN", [np.args[0], w]) for w in weakenings(np.args[1])]
    return []


def _leaf_heads(t):
    if not t.args:
        return [t.head]
    return [x for a in t.args for x in _leaf_heads(a)]


def _subtrees(t):
    yield t
    for a in t.args:
        yield from _subtrees(a)


def _name(t):
    try:
        if t.head in VP_HEADS:
            return _scope_name(t)
        return camel_name(_leaf_words(t))
    except Exception:
        return None


def postulates(trees, unary: set[str], binary: set[str]) -> list[str]:
    """Lean propositions (as text) to add as premises, for a problem whose
    top-ranked clause trees are `trees` and whose generic assembly bound
    `unary`/`binary` predicate names."""
    facts: list[str] = []

    def add(f):
        if f not in facts:
            facts.append(f)

    # 1. structural entailments
    for tree in trees:
        for st in _subtrees(tree):
            if st.head not in CN_HEADS and st.head not in VP_HEADS:
                continue
            p = _name(st)
            if p not in unary:
                continue
            for w in weakenings(st):
                q = _name(w)
                if q and q != p and q in unary:
                    add(f"(∀ x, {p} x → {q} x)")

    # 2. degree-semantics lexicon
    adj_cn = {}  # (adjective lemma, noun-phrase name) -> predicate name
    for tree in trees:
        for st in _subtrees(tree):
            if st.head == "AdjCN" and len(st.args) == 2 and st.args[0].head == "PositA":
                name = _name(st)
                if name in unary:
                    adj_cn[(_lemma(st.args[0].args[0].head), _name(st.args[1]))] = name
    for a, b in ANTONYMS:
        if a in unary and b in unary:
            add(f"(∀ x, ¬ ({a} x ∧ {b} x))")
        for (adj, noun), name in list(adj_cn.items()):
            if adj == a and (b, noun) in adj_cn:
                add(f"(∀ x, ¬ ({name} x ∧ {adj_cn[(b, noun)]} x))")
        at, bt = a + "Than", b + "Than"
        if at in binary and bt in binary:
            add(f"(∀ x y, {at} x y ↔ {bt} y x)")
    for rel in sorted(binary):
        for suffix in ("Than", "As"):
            if rel.endswith(suffix):
                adj = rel[: -len(suffix)]
                if adj in unary:
                    add(f"(∀ x y, {rel} x y → {adj} y → {adj} x)")
                if suffix == "Than":
                    add(f"(∀ x y, {rel} x y → ¬ {rel} y x)")
    return facts
