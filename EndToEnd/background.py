#!/usr/bin/env python3
"""Problem-independent background knowledge for the end-to-end pipeline
(EndToEnd/gen_claims.py).

translate.py names a predicate after the words of its whole CN/VP subtree
("win the Nobel prize for literature" -> `winNobelPrizeForLiterature`),
which loses the compositional fact that it entails "win a Nobel prize".
Every hand-written FraCaS theorem supplies facts like that as explicit
premises; this module derives the same *kinds* of facts mechanically, and
nothing else. Four sources, all stated here in full:

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
     measure ("for two hours" - `_is_aspectual`) on a noun or on a verb
     phrase that culminates (readings.py's `_telic`);
   - an adverbial on a non-quantified object ("got the results published
     in major newspapers");
   - a counting determiner on an object ("a lot of time" ⊑ "time",
     `COUNTING_TO_BARE`);
   - a relative clause on a noun (`RelCN`);
   - the progressive of a VP that does not culminate ("was running a
     business" ⊑ "ran a business"; not "was building MTALK", the
     imperfective paradox);
   - a degree word on an adjective (`AdAP`: "really great" -> "great");
   - recursively inside a verb's object or a copula complement, but only
     when that NP is existential or definite-singular ("a/some/several/
     the X") - never under `every`/`no`/`few` (downward or non-monotone)
     and never under a verb taking a verb phrase (`want`, `can`, ...),
     whose complements are not monotone in general - except the
     upward-monotone `UPWARD_VV` ("can", "must", "used to").
2. **A small, closed degree-semantics lexicon.** `ANTONYMS` pairs gradable
   adjectives with their contraries. When a problem mentions the relevant
   predicates: contraries are exclusive (`¬ (small x ∧ large x)`, and the
   same for "small N"/"large N" over the *same* noun N - comparison class
   held fixed); a comparative's standard transfers upward (`aThan x y → a
   y → a x`, `aAs x y → a y → a x`); comparatives are asymmetric (`aThan
   x y → ¬ aThan y x`); antonym comparatives are converses (`aThan x y ↔
   bThan y x`).
3. **Adjective classes** (`INTERSECTIVE`, `EXTENSIONAL_SUBSECTIVE`,
   `PRIVATIVE`; any other adjective is plainly subsective and gets only
   part 1's weakening). An intersective "A N" is A and N, so it follows
   the noun's entailments ("every mammal is an animal" ⊢ "every
   four-legged mammal is a four-legged animal") and drops to "A". A
   privative "A N" is not an N. A dimensional adjective's threshold
   depends only on the comparison class's members (coextensive nouns give
   coextensive "A N"s - not so for "competent", FraCaS 215), its
   comparative is the same whatever the noun ("a fatter politician than"
   ⇒ "fatter than" - not so for "cleverer", 217), and over one comparison
   class a contrary pair's thresholds are ordered ("a small animal" is
   smaller than "a large animal").
4. **Time adverbials** on the same verb phrase (gen_claims.py moves them
   to the verb phrase first): "for two years" ⊑ "for a year" and
   excludes "for exactly a year"; a state or
   activity "from 1988 to 1992" ⊑ "in 1990"; "in July 1994" ⊑ "in 1994";
   and a culminating event on one particular object ("wrote his first
   novel") in one year excludes it in another - the one-time-per-event
   assumption readings.py's `_ordered` already makes. Also in part 2:
   "as fast as" excludes "slower than".

Nothing here is keyed by problem number or gold answer. The lexicon lists
were written with this corpus in view, so they are not a held-out
resource - see BLIND_EVAL.md, which reports the end-to-end score both
with and without this module.
"""
from __future__ import annotations

import itertools
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "gf"))
from translate import App, _leaf_words, _scope_name, camel_name  # noqa: E402
from readings import _STATIVE_TRANSITIVE, _telic  # noqa: E402

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
# Adjective classes (Kamp & Partee 1995; Partee 2010; the classes
# Chatzikyriakidis & Luo 2017 and Bernardy & Chatzikyriakidis's FraCoq
# also use). An adjective in none of them is read as plainly subsective -
# "a competent N" is an N and nothing more follows - which is the safe
# default: it licenses only the weakening of part 1.
#   intersective: an A N is something A that is an N ("a four-legged
#   animal" is four-legged and an animal) - colours, sex, nationality,
#   shape;
INTERSECTIVE = {
    "red", "blue", "green", "black", "white", "yellow", "brown",
    "male", "female", "fourLegged",
    "british", "canadian", "irish", "italian", "portuguese", "scandinavian", "northAmerican",
    "swedish", "german", "french", "european", "american",
}
#   extensional subsective: dimensional gradable adjectives, true of an N
#   whose degree on one scale (size, girth, speed, ...) exceeds a threshold
#   set by the comparison class - so what counts depends only on the
#   class's members, the comparative does not depend on the class at all,
#   and a contrary pair's thresholds are ordered (Kennedy 2007);
EXTENSIONAL_SUBSECTIVE = {"small", "large", "big", "fat", "thin", "fast", "slow", "tall", "short", "heavy", "light"}
#   privative: an A N is not an N ("a former student").
PRIVATIVE = {"former", "fake", "counterfeit", "imaginary", "fictional"}

# Verbs whose verb-phrase complement is upward monotone: what one can or
# must do, or used to do, one can/must/used to do any weakening of (a modal
# is a quantifier over possibilities; "used to" one over past times).
# Not "want" and other preference verbs, which are not monotone.
UPWARD_VV = {"usedTo_VV", "can_VV", "must_VV"}
# Counting determiners whose noun phrase entails the bare noun ("a lot of
# time" ⊑ "time", "several hours" ⊑ "hours") in an upward position.
COUNTING_TO_BARE = {"aLotOf_Det", "many_Det", "several_Det", "aFew_Det", "somePl_Det"}

CN_HEADS = {"UseN", "AdjCN", "AdvCN", "RelCN", "CompoundCN", "SentCN", "ApposCN"}
VP_HEADS = {"UseComp", "ComplSlash", "AdvVP", "ComplVV", "UseV", "PassV2", "AdVVP", "ComplVS", "ComplVQ", "ProgrVP"}
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
        # a durative "for two hours" deletes only from a VP that does not
        # culminate (a state or activity: "lived in Birmingham for two
        # years" ⊑ "lived in Birmingham"); "wrote a report for two hours"
        # need not have finished it (the imperfective paradox, FraCaS 304)
        if not (adv_words & NON_VERIDICAL) and not (_is_aspectual(a[1]) and _telic(a[0])):
            out.append(a[0])
        out += [App("AdvVP", [w, a[1]]) for w in weakenings(a[0])]
    elif h == "AdAP" and len(a) == 2:
        out.append(a[1])
    elif h == "ComplSlash" and len(a) == 2:
        np = a[1]
        if _np_allows_weakening(np):
            out += [App("ComplSlash", [a[0], w]) for w in _np_weakenings(np)]
        # an adverbial on a non-quantified object ("got [the results
        # published] in major newspapers")
        if np.head == "AdvNP" and len(np.args) == 2:
            inner, adv = np.args
            adv_words = {_lemma(x) for x in _leaf_heads(adv)}
            if (inner.head in ("PPartNP", "UsePN") or _np_allows_weakening(inner)) \
                    and not (adv_words & NON_VERIDICAL) and not _is_aspectual(adv):
                out.append(App("ComplSlash", [a[0], inner]))
                # the same words with the adverbial on the noun ("rents [a
                # dedicated line] from BT" = "rents a dedicated line from
                # BT"), whose own modifiers then delete as usual
                if inner.head == "DetCN" and _np_allows_weakening(inner):
                    out.append(App("ComplSlash", [a[0], App("DetCN", [inner.args[0], App("AdvCN", [inner.args[1], adv])])]))
    elif h == "ProgrVP" and len(a) == 1:
        # "was running his own business" ⊑ "ran his own business" for a VP
        # that does not culminate; "was building MTALK" need not have
        # built it (the imperfective paradox, FraCaS 327, 329)
        if not _telic(a[0]):
            out.append(a[0])
        out += [App("ProgrVP", [w]) for w in weakenings(a[0])]
    elif h == "ComplVV" and len(a) == 2 and a[0].head in UPWARD_VV:
        out += [App("ComplVV", [a[0], w]) for w in weakenings(a[1])]
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
        out = [App("DetCN", [np.args[0], w]) for w in weakenings(np.args[1])]
        if np.args[0].head in COUNTING_TO_BARE:
            bare = App("MassNP", [np.args[1]])
            out += [bare, *_np_weakenings(bare)]
        return out
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


def postulates(trees, unary: set[str], binary: set[str], built: list | None = None) -> list[str]:
    """Lean propositions (as text) to add as premises, for a problem whose
    top-ranked clause trees are `trees` and whose generic assembly bound
    `unary`/`binary` predicate names. Each phrase a fact is stated about
    that is not itself in `trees` (a weakening, an event "finish" stands
    for) is appended to `built`, for `names.py`'s check."""
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
                    if built is not None:
                        built.append(w)

    # 2. degree-semantics lexicon
    adj_cn = {}  # (adjective lemma, noun-phrase name) -> predicate name
    adj_name = {}  # adjective lemma -> its predicate name ("four-legged" -> fourLegged)
    compar_cn = {}  # (adjective lemma, noun-phrase name) -> "ADJer N than" relation name
    for tree in trees:
        for st in _subtrees(tree):
            if st.head == "AdjCN" and len(st.args) == 2 and st.args[0].head == "PositA":
                name = _name(st)
                if name in unary:
                    adj_cn[(_lemma(st.args[0].args[0].head), _name(st.args[1]))] = name
                    adj_name[_lemma(st.args[0].args[0].head)] = _name(st.args[0])
            if st.head == "ComparCN" and len(st.args) == 3:
                adj, cn = st.args[0], st.args[1]
                rel = camel_name([*_leaf_words(adj), *_leaf_words(cn)]) + "Than"
                if rel in binary:
                    compar_cn[(_lemma(adj.head), _name(cn))] = rel
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

    for a, b in ANTONYMS:
        # "x is as fast as y": x's degree is at least y's - so x is not
        # slower than y, and y is not faster than x
        if a + "As" in binary:
            if b + "Than" in binary:
                add(f"(∀ x y, {a}As x y → ¬ {b}Than x y)")
            if a + "Than" in binary:
                add(f"(∀ x y, {a}As x y → ¬ {a}Than y x)")

    # 3. adjective classes
    for (adj, noun), name in adj_cn.items():
        a = adj_name.get(adj)
        if adj in INTERSECTIVE:
            if a in unary:
                add(f"(∀ x, {name} x → {a} x)")
                if noun in unary:
                    add(f"(∀ x, {a} x → {noun} x → {name} x)")
            # "every mammal is an animal" ⊢ "every four-legged mammal is a
            # four-legged animal", without the bare adjective in the problem
            for (adj2, noun2), name2 in adj_cn.items():
                if adj2 == adj and noun2 != noun and noun2 in unary:
                    add(f"(∀ x, {name} x → {noun2} x → {name2} x)")
        if adj in PRIVATIVE and noun in unary:
            add(f"(∀ x, {name} x → ¬ {noun} x)")
        if adj in EXTENSIONAL_SUBSECTIVE:
            # the threshold depends only on the comparison class's members:
            # coextensive nouns give coextensive "A N"s
            for (adj2, noun2), name2 in adj_cn.items():
                if adj2 == adj and noun2 != noun and noun in unary and noun2 in unary:
                    add(f"(∀ x, (∀ y, {noun} y → {noun2} y) → (∀ y, {noun2} y → {noun} y) → {name} x → {name2} x)")
    for a, b in ANTONYMS:
        if a not in EXTENSIONAL_SUBSECTIVE or b not in EXTENSIONAL_SUBSECTIVE:
            continue
        # contraries over one comparison class: an a-N is below every b-N
        # on the shared scale ("a small animal is smaller than a large one")
        for (adj, noun), name in adj_cn.items():
            if adj == a and (b, noun) in adj_cn:
                other = adj_cn[(b, noun)]
                if a + "Than" in binary:
                    add(f"(∀ x y, {name} x → {other} y → {a}Than x y)")
                if b + "Than" in binary:
                    add(f"(∀ x y, {name} x → {other} y → {b}Than y x)")
    # "ADJer N than" is "ADJer than" for a dimensional adjective: the scale
    # is the same whatever the noun (not so for "cleverer politician")
    for (adj, _noun), rel in compar_cn.items():
        if adj in EXTENSIONAL_SUBSECTIVE and adj + "Than" in binary:
            add(f"(∀ x y, {rel} x y → {adj}Than x y)")

    # 4. time adverbials on the same verb phrase
    timed = []
    for tree in trees:
        for st in _subtrees(tree):
            if st.head == "AdvVP" and len(st.args) == 2:
                when = _time_value(st.args[1])
                name = _name(st)
                if when is not None and name in unary:
                    timed.append((repr(st.args[0]), st.args[0], when, name))
    for (k1, v, w1, p1), (k2, _v, w2, p2) in itertools.permutations(timed, 2):
        if k1 != k2 or p1 == p2:
            continue
        if w1[0] == w2[0] == "for" and w1[2] == w2[2] and w1[1] >= w2[1]:
            # "for two years" ⊑ "for a year"
            add(f"(∀ x, {p1} x → {p2} x)")
        elif w1[0] == "exactly" and w2[0] == "for" and w1[2] == w2[2] and w1[1] >= w2[1]:
            # "for exactly a year" ⊑ "for a year"
            add(f"(∀ x, {p1} x → {p2} x)")
        elif w1[0] == "for" and w2[0] == "exactly" and w1[2] == w2[2] and w1[1] > w2[1]:
            # "for two years" excludes "for exactly a year", which gives
            # the whole duration (FraCaS 299)
            add(f"(∀ x, {p1} x → ¬ {p2} x)")
        elif w1[0] == "span" and w2[0] == "year" and w1[1] <= w2[1] <= w1[2] and not _telic(v):
            # a state or activity holds at every time within its span
            # ("owned APCOM from 1988 to 1992" ⊑ "owned APCOM in 1990")
            add(f"(∀ x, {p1} x → {p2} x)")
        elif w1[0] == "since" and w2[0] == "year" and w1[1] <= w2[1] <= w1[2] and _stative(v):
            # "since 1992 ITEL has been in Birmingham", now 1996 ⊑ "was in
            # Birmingham in 1993": a state the perfect says has held since
            # then holds throughout. Not for other VPs, whose perfect says
            # only that it happened at some time since ("ITEL has expanded
            # since 1992" ⇏ "expanded in 1993", FraCaS 254)
            add(f"(∀ x, {p1} x → {p2} x)")
        elif w1[0] == "month" and w2[0] == "year" and w1[1] == w2[1]:
            add(f"(∀ x, {p1} x → {p2} x)")
        elif w1[0] == w2[0] == "year" and w1[1] < w2[1] and _telic(v) and _unique_object(v):
            # one culminating event on one particular object ("wrote his
            # first novel") happens at one time - the same assumption
            # readings.py's `_ordered` makes
            add(f"(∀ x, {p1} x → ¬ {p2} x)")

    # Frequency within a year: "in 1994 ITEL sent a progress report every
    # month" ⊑ "sent a progress report in July 1994" - every month (week,
    # day) of 1994 has one, July's included (FraCaS 307).
    for tree in trees:
        for st in _subtrees(tree):
            if not (st.head == "AdvVP" and len(st.args) == 2 and st.args[0].head == "AdvVP"
                    and len(st.args[0].args) == 2):
                continue
            v, a, b = st.args[0].args[0], st.args[0].args[1], st.args[1]
            pair = {x.head for x in (a, b) if not x.args}
            every = pair & FREQUENCY
            year = [_time_value(x) for x in (a, b) if _time_value(x) is not None]
            name = _name(st)
            if not (every and len(year) == 1 and year[0][0] == "year" and name in unary):
                continue
            for k, _v, when, occasion in timed:
                if k == repr(v) and when == ("month", year[0][1]):
                    add(f"(∀ x, {name} x → {occasion} x)")

    # What a creation verb's event brings about did not exist before it:
    # "in March 1993 APCOM founded ITEL" ⊢ ITEL did not exist in 1992
    # (FraCaS 258).
    existence = []  # (individual name, year, predicate name)
    for tree in trees:
        for st in _subtrees(tree):
            if st.head == "PredVP" and len(st.args) == 2 and st.args[0].head == "UsePN":
                vp = st.args[1]
                if vp.head == "AdvVP" and len(vp.args) == 2 and vp.args[0].head == "UseV" \
                        and vp.args[0].args[0].head == "exist_V":
                    when, name = _time_value(vp.args[1]), _name(vp)
                    if when is not None and when[0] == "year" and name in unary:
                        existence.append((_name(st.args[0]), when[1], name))
    for _k, v, when, p in timed:
        if not (when[0] in ("year", "month") and v.head == "ComplSlash" and len(v.args) == 2
                and v.args[0].head == "SlashV2a" and v.args[0].args[0].head in CREATION
                and v.args[1].head == "UsePN"):
            continue
        for ind, year, q in existence:
            if ind == _name(v.args[1]) and year < when[1]:
                add(f"(∀ x, {p} x → ¬ {q} {ind})")

    # "Finish" with a noun phrase object finishes some event on it
    # (logical metonymy, Pustejovsky 1995); when the problem mentions
    # exactly one other kind of event on that same particular thing, it is
    # that one, and a culminating one is finished: "ITEL built MTALK in
    # 1993" ⊑ "ITEL finished MTALK in 1993" (FraCaS 326; the progressive
    # "was building", 327, does not culminate).
    for tree in trees:
        for st in _subtrees(tree):
            core = _verb_core(st)
            if core is None or core.args[0].args[0].head != "finish_V2" or not _unique_object(core):
                continue
            finished = _name(st)
            others = {c.args[0].args[0].head for t2 in trees for s2 in _subtrees(t2)
                      if (c := _verb_core(s2)) is not None and repr(c.args[1]) == repr(core.args[1])
                      and c.args[0].args[0].head != "finish_V2"}
            if finished not in unary or len(others) != 1:
                continue
            event = _with_verb(st, others.pop())
            name = _name(event)
            if name in unary and _telic(event):
                add(f"(∀ x, {name} x → {finished} x)")
                if built is not None:
                    built.append(event)

    # 5. "always"/"never" (gen_claims.py marks them `always_Adv`/`never_Adv`)
    # quantify over occasions: "ITEL always delivers
    # reports late" and "ITEL delivered reports in 1993" ⊑ "ITEL delivered
    # reports late in 1993" (and "never" excludes it, FraCaS 312/313)
    for tree in trees:
        for st in _subtrees(tree):
            if not (st.head == "AdVVP" and len(st.args) == 2 and st.args[0].head in ("always_Adv", "never_Adv")):
                continue
            habit, manner = _name(st), st.args[1]
            if habit not in unary or manner.head != "AdvVP" or len(manner.args) != 2:
                continue
            for k, v, when, occasion in timed:
                if k != repr(manner.args[0]):
                    continue
                # the same time adverbial on the habitual VP, if the problem has it
                target = None
                for tree2 in trees:
                    for st2 in _subtrees(tree2):
                        if st2.head == "AdvVP" and len(st2.args) == 2 and repr(st2.args[0]) == repr(manner) \
                                and _time_value(st2.args[1]) == when:
                            target = _name(st2)
                if target in unary:
                    if st.args[0].head == "always_Adv":
                        add(f"(∀ x, {habit} x → {occasion} x → {target} x)")
                    else:
                        add(f"(∀ x, {habit} x → {occasion} x → ¬ {target} x)")
    return facts


# Frequency adverbials: once in every such period ("every month").
FREQUENCY = {"everyDay_Adv", "everyWeek_Adv", "everyMonth_Adv"}
# Verbs whose object comes into existence through the event.
CREATION = {"build_V2", "construct_V2", "create_V2", "establish_V2", "found_V2", "make_V2", "write_V2"}

_NUMBERS = {"A": 1, "An": 1, "One": 1, "Two": 2, "Three": 3, "Four": 4, "Five": 5, "Six": 6,
            "Seven": 7, "Eight": 8, "Nine": 9, "Ten": 10}
_MONTHS = ("January", "February", "March", "April", "May", "June", "July", "August",
           "September", "October", "November", "December")


def _time_value(adv):
    """A lexicalized time adverbial's meaning: ("for", n, unit) for a
    duration of at least n units, ("exactly", n, unit) for exactly n, ("year", y), ("month", y) for a month of
    year y, ("span", y1, y2) for "from y1 to y2"; None for anything else."""
    if adv.args or not adv.head.endswith("_Adv"):
        return None
    w = adv.head.rsplit("_", 1)[0]
    m = re.fullmatch(r"for(MoreThan|Exactly)?([A-Z][a-z]*)(Hour|Year|Day|Week|Month|Minute)s?", w)
    if m and m.group(2) in _NUMBERS:
        if m.group(1) == "Exactly":
            return ("exactly", _NUMBERS[m.group(2)], m.group(3))
        return ("for", _NUMBERS[m.group(2)] + (1 if m.group(1) else 0), m.group(3))
    m = re.fullmatch(r"in(\d{4})", w)
    if m:
        return ("year", int(m.group(1)))
    m = re.fullmatch(r"in([A-Z][a-z]+)(\d{4})", w)
    if m and m.group(1) in _MONTHS:
        return ("month", int(m.group(2)))
    m = re.fullmatch(r"from(\d{4})to(\d{4})", w)
    if m:
        return ("span", int(m.group(1)), int(m.group(2)))
    # the perfect's "since 1992" up to the utterance time (gen_claims.py's
    # `_since_to_now`)
    m = re.fullmatch(r"since(\d{4})to(\d{4})", w)
    if m:
        return ("since", int(m.group(1)), int(m.group(2)))
    return None


def _verb_core(vp):
    """The transitive "V NP" inside one-word adverbials, or None."""
    while vp.head == "AdvVP" and len(vp.args) == 2 and not vp.args[1].args:
        vp = vp.args[0]
    if vp.head == "ComplSlash" and len(vp.args) == 2 and vp.args[0].head == "SlashV2a":
        return vp
    return None


def _with_verb(vp, verb):
    """`vp` with its core transitive verb replaced by `verb`."""
    if vp.head == "AdvVP":
        return App("AdvVP", [_with_verb(vp.args[0], verb), vp.args[1]])
    return App("ComplSlash", [App("SlashV2a", [App(verb, [])]), vp.args[1]])


def _stative(vp) -> bool:
    """A state: the copula ("has been in Birmingham") or a stative verb."""
    if vp.head == "UseComp":
        return True
    return vp.head == "ComplSlash" and len(vp.args) == 2 and vp.args[0].head == "SlashV2a" \
        and vp.args[0].args[0].head in _STATIVE_TRANSITIVE


def _unique_object(vp) -> bool:
    """A transitive VP whose object is one particular thing: a name, or a
    definite or possessive singular ("the contract", "his first novel")."""
    if vp.head != "ComplSlash" or len(vp.args) != 2:
        return False
    np = vp.args[1]
    if np.head == "UsePN":
        return True
    if np.head == "DetCN" and np.args[0].head == "DetQuant" and len(np.args[0].args) == 2:
        quant, num = np.args[0].args
        return num.head == "NumSg" and (quant.head == "DefArt" or quant.head == "PossPron")
    return False
