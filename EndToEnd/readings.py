"""The end-to-end pipeline's readings of ambiguous English.

`gf/translate.py` translates one GF tree into one Lean `Prop`, reading
each construction the one way the hand-written corpus's GF cross-check
needs (its `Readings` base class). This module subclasses that extension
point so the end-to-end pipeline never has to commit to one reading:
`translate_cl_reading` translates a clause under a "weak" reading
(entailed by every reading - used for premises, and for the hypothesis
in the "no" test) or a "strong" one (entailing every reading - the
hypothesis in the "yes" test), so no yes/no the scan reports depends on
picking one reading:

  - definite plural subject ("the inhabitants voted ..."): distributive
    `Every` vs collective/generic - weak `Some`, strong `Every` plus the
    definite's existence presupposition (see `quantified`);
  - bare plural + relative clause ("leading tenors who are excellent
    are ..."): generic vs existential - weak `Some`, strong `Every`;
  - "many": cardinal vs proportional - weak `Some`; strong an opaque
    `Many` relation, stated (by gen_claims.py) only with the properties
    every reading shares;
  - plural "some Xs": number-neutral vs at-least-two - weak `Some`,
    strong `AtLeast 2` (with its "some" consequence spelled out);
  - a bare numeral ("APCOM won ten orders"): at least n vs exactly n -
    weak `AtLeast n`, strong `Exactly n` ("only/just n" is always
    `Exactly n`, and "at least/at most/exactly n" say which outright);
  - "few": cardinal vs proportional (Partee's two readings, as for
    "many") - weak `AtMost fewCount` for an unknown threshold
    `fewCount`; strong an opaque `Few` relation, stated (by the
    generator) only with the property every reading shares: narrowing
    its scope within its restrictor preserves it. Neither reading entails
    that any such X exist (FraCaS 12).

Some constructions are not ambiguous, only translated differently here
than the default does:

  - "a few"/"at least a few" are vague: `AtLeast aFewCount` for an
    unknown threshold `aFewCount ≥ 1` (the default's plain `Some` makes
    "some X are Y" entail "a few X are Y");
  - "several" is vague the same way: `AtLeast severalCount` for an
    unknown threshold `severalCount ≥ 2` (whether "several" needs three
    is contested; every use excludes one). The default's plain `Some`
    made "some X are Y" entail "several X are Y";
  - "both"/"neither" use GQ.lean's own `Both`/`Neither`, which keep the
    exactly-two presupposition the default's `Every`/`No` drop;
  - a proper-name subject's counted object ("APCOM won ten orders") and
    quantity comparatives ("ITEL won more orders than APCOM did") keep
    the verb as a binary predicate (see `named_object`);
  - counting existentials ("there are few committee members from
    southern Europe") and a floated "all" ("the Ancient Greeks were all
    noted philosophers");
  - whole sentences the default does not handle (see `sentence`):
    coordinated subjects ("Smith and Jones", "every representative and
    every client"), "it is true/false that S", "everyone", "one of the
    Ns", perception reports ("Smith saw Jones sign the contract"),
    comparatives inside a noun phrase ("a fatter politician than Bill"),
    and conditionals ("if S, S");
  - attitude reports ("Bill said Peter wrote a report"), with factive
    "know that S" committing to S, and implicative "manage to VP",
    which commits to the VP (see `_attitude`, `_implicative`);
  - temporal order between two completed events ("Smith left before
    Jones left"), see `_ordered`;
  - "more than n" is `AtLeast (n+1)`, and a floated "all" before the
    verb ("the people who were at the meeting all voted") makes a plural
    subject universal.

`reading` may also be a dict assigning "weak"/"strong" per KIND of
ambiguity (AMBIGUITY_KINDS), so a caller can read the same kind of
ambiguity the same way in every sentence of a problem (gen_claims.py
enumerates all such assignments); a kind missing from the dict reads
"weak".
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "gf"))
from translate import (  # noqa: E402
    App,
    translate_cl,
    Readings,
    Translation,
    _bare_count,
    _decode_numeral,
    _leaf_words,
    _normalize_cn,
    _RELATIVE_PRONOUNS,
    _resolve_quantifier,
    _restrictor_expr,
    _scope_name,
    camel_name,
    translate_cl_with,
)

AMBIGUITY_KINDS = ("defpl", "generic", "many", "somepl", "numeral", "few")

# Object determiners that make a named subject's transitive VP count its
# objects, so the count is kept as a quantifier over a binary verb rather
# than fused into one predicate name (see `named_object`).
_COUNTING_OBJECT_DETS = ("somePl_Det", "several_Det", "aFew_Det", "many_Det")


def _is_counting_det(det) -> bool:
    if det.head in _COUNTING_OBJECT_DETS and not det.args:
        return True
    return (
        det.head == "DetQuant"
        and len(det.args) == 2
        and det.args[1].head == "NumCard"
    )


# Verbs whose subject is a group as a whole ("Smith, Anderson and Jones
# met"): a coordinated subject does not distribute over them.
_COLLECTIVE_VERBS = ("meet_V", "gather_V")


def _np_list(t):
    """`BaseNP a b` / `ConsNP a (...)` -> [a, b, ...]."""
    if t.head == "BaseNP" and len(t.args) == 2:
        return list(t.args)
    if t.head == "ConsNP" and len(t.args) == 2:
        rest = _np_list(t.args[1])
        return None if rest is None else [t.args[0], *rest]
    return None


def _mentions(t, heads) -> bool:
    return t.head in heads or any(_mentions(a, heads) for a in t.args)


def _counted_object(vp) -> bool:
    """Whether `vp`'s object counts ("signed two contracts", "won
    several orders")."""
    return (
        vp.head == "ComplSlash"
        and len(vp.args) == 2
        and vp.args[1].head == "DetCN"
        and len(vp.args[1].args) == 2
        and _is_counting_det(vp.args[1].args[0])
    )


def _plain(tr) -> bool:
    """A translation the generic assembly can use as it stands."""
    return not (tr.conjuncts or tr.free_functions or tr.template)


def _combine(parts, op: str) -> Translation:
    preds, individuals, binary = [], [], []
    for tr in parts:
        for name, seen in ((tr.free_predicates, preds), (tr.free_individuals, individuals),
                           (tr.binary_predicates, binary)):
            seen.extend(n for n in name if n not in seen)
    return Translation(
        lean_prop="(" + f" {op} ".join(tr.lean_prop for tr in parts) + ")",
        free_predicates=preds,
        free_individuals=individuals,
        binary_predicates=binary,
    )


# Telicity (Verkuyl; Krifka): whether a VP describes an event that
# culminates, which "before"/"after" can place at a single time. A copula
# is a state; a VP with a quantized object ("revised the contract") or a
# goal ("swam to the shore") culminates unless its verb is stative ("owned
# a business"); an intransitive verb culminates only if it is lexically an
# achievement ("left", not "swam"). The two word lists are textbook
# examples of each class, not drawn from FraCaS's answers.
_TELIC_INTRANSITIVE = ("leave_V", "arrive_V", "die_V", "depart_V", "fall_V", "win_V")
_STATIVE_TRANSITIVE = ("own_V2", "have_V2", "know_V2", "like_V2", "love_V2", "need_V2",
                       "want_V2", "contain_V2", "believe_V2", "hate_V2")
_ORDER = {"before_Subj": "<", "after_Subj": ">"}

# Karttunen's (1971) verbs that commit the speaker to their complement:
# factives presuppose a "that"-clause ("Smith knew that S" ⇒ S), and a
# (two-way) implicative's positive use entails its infinitive ("ITEL
# managed to win" ⇒ ITEL won). Non-factive "believe" and non-implicative
# "try"/"want" are not listed, so nothing follows from them (FraCaS 335,
# 337). Textbook members of each class, not drawn from FraCaS's answers.
_FACTIVE = ("know_VS", "realize_VS", "regret_VS")
_IMPLICATIVE = ("manage_VV",)


def _quantized(np) -> bool:
    if np.head == "UsePN":
        return True
    if np.head == "DetCN" and np.args[0].head == "DetQuant" and len(np.args[0].args) == 2:
        num = np.args[0].args[1]
        return num.head == "NumSg" or num.head == "NumCard"
    return False


def _telic(vp) -> bool:
    if vp.head == "UseV":
        return vp.args[0].head in _TELIC_INTRANSITIVE
    if vp.head == "ComplSlash" and vp.args[0].head == "SlashV2a":
        return vp.args[0].args[0].head not in _STATIVE_TRANSITIVE and _quantized(vp.args[1])
    if vp.head == "AdvVP" and vp.args[1].head == "PrepNP" and vp.args[1].args[0].head == "to_Prep":
        return vp.args[0].head == "UseV" and _quantized(vp.args[1].args[1])
    return False


class EndToEndReadings(Readings):
    def __init__(self, reading, position: str):
        self.reading = reading
        self.position = position
        # Event-time functions (`A → ℕ`) the translation uses, see `_ordered`.
        self.time_functions: list[str] = []
        # Existence facts a strong reading entails, stated as separate
        # premises (see `quantified`).
        self.side_premises: list[str] = []

    def mode(self, kind: str) -> str:
        if isinstance(self.reading, dict):
            return self.reading.get(kind, "weak")
        return self.reading

    def sentence(self, t):
        if t.head == "ExtAdvS" and len(t.args) == 2:
            return self._conditional(*t.args)
        if t.head != "PredVP" or len(t.args) != 2:
            return None
        subject, vp = t.args
        if subject.head == "UsePN" and vp.head == "AdvVP" and vp.args[1].head == "SubjS":
            ordered = self._ordered(subject, vp.args[0], vp.args[1])
            if ordered is not None:
                return ordered
        if subject.head == "AndEveryNP" and len(subject.args) == 2:
            every = [App("DetCN", [App("every_Det", []), cn]) for cn in subject.args]
            return self._distribute(every, vp, "∧")
        if subject.head == "UsePN" and vp.head == "ComplSlash" and vp.args[0].head == "SlashV2V":
            return self._perception(subject, vp)
        if subject.head == "UsePN" and vp.head in ("ComplVS", "ComplVSBare") and len(vp.args) == 2:
            attitude = self._attitude(subject, vp)
            if attitude is not None:
                return attitude
        if subject.head == "UsePN" and vp.head == "ComplVV" and vp.args[0].head in _IMPLICATIVE:
            return self._implicative(subject, vp)
        if subject.head == "UsePN" and vp.head == "UseComp" and len(vp.args) == 1:
            compared = self._compared_cn(vp.args[0])
            if compared is not None:
                return self._comparative_cn(subject, *compared)
        if subject.head == "UsePron" and subject.args[0].head == "it_Pron":
            return self._truth_of(vp)
        if subject.head == "ConjNP" and len(subject.args) == 2:
            return self._coordinated(subject, vp)
        if subject.head == "everyone_NP" or (
            subject.head == "AdvNP" and len(subject.args) == 2 and subject.args[0].head == "everyone_NP"
        ):
            return self._everyone(subject, vp)
        if subject.head == "CountNP" and len(subject.args) == 2:
            return self._partitive(subject, vp)
        return None

    def _truth_of(self, vp):
        """"It is true that S" is S, and "it is false that S" is not-S:
        `true`/`false` are the veridical and anti-veridical sentential
        predicates (FraCaS 338/339). Only a positive embedded clause."""
        if not (
            vp.head == "UseComp"
            and vp.args[0].head == "CompAP"
            and vp.args[0].args[0].head == "SentAP"
            and len(vp.args[0].args[0].args) == 2
        ):
            return None
        adj, embedded = vp.args[0].args[0].args
        if adj.head != "PositA" or adj.args[0].head not in ("true_A", "false_A") or embedded.head != "EmbedS":
            return None
        s = embedded.args[0]
        if not (s.head == "UseCl" and len(s.args) == 3 and s.args[1].head == "PPos"):
            raise NotImplementedError("'it is true/false that' with a negative or non-clausal complement")
        tr = translate_cl(s.args[2])
        if not _plain(tr) or adj.args[0].head == "true_A":
            return tr
        return Translation(
            lean_prop=f"¬ ({tr.lean_prop})",
            free_predicates=tr.free_predicates,
            free_individuals=tr.free_individuals,
            binary_predicates=tr.binary_predicates,
        )

    def _coordinated(self, subject, vp):
        """"Smith, Jones and Anderson signed the contract": the VP holds of
        each conjunct ("and") or of at least one ("or"/"either ... or").
        Distributing is a reading, not a given: a coordinated subject can
        also be read collectively. It is the only reading for an ordinary
        distributive predicate (signing a contract, leaving a meeting),
        so two cases where the collective reading is live are left
        untranslated: a collective verb ("Smith, Anderson and Jones
        met"), and a counted object ("Smith and Jones signed two
        contracts", which on its cumulative reading is two in all -
        FraCaS 111-113 turn on exactly that)."""
        conj, items = subject.args
        ops = {"and_Conj": "∧", "both7and_DConj": "∧", "or_Conj": "∨", "either7or_DConj": "∨"}
        nps = _np_list(items)
        if conj.head not in ops or nps is None:
            return None
        return self._distribute(nps, vp, ops[conj.head])

    def _distribute(self, nps, vp, op: str):
        """The VP of each of `nps`, joined by `op` (see `_coordinated`)."""
        if _mentions(vp, _COLLECTIVE_VERBS):
            raise NotImplementedError("coordinated subject of a collective verb")
        if _counted_object(vp):
            raise NotImplementedError("coordinated subject with a counted object (cumulative reading)")
        parts = [translate_cl(App("PredVP", [np, vp])) for np in nps]
        if not all(_plain(tr) for tr in parts):
            raise NotImplementedError("a conjunct of a coordinated subject needs non-generic assembly")
        return _combine(parts, op)

    def _ordered(self, subject, vp, sub):
        """"Smith left before/after Jones left", "Jones revised the
        contract before Smith did": each culminating event of a named
        individual has one time, `leaveTime smith : ℕ` - FraCaS's own
        assumption for these problems (each person leaves once), and the
        hand-written corpus's encoding of them. "A after B" is factive in
        B: `A ∧ B ∧ t(A) > t(B)`. "A before B" is not ("Smith left the
        meeting before he lost his temper" leaves open whether he did,
        FraCaS 275): `A ∧ t(A) < t(B)`, where t(B) is when B happens or
        would have. Only between two culminating events (`_telic`): for a
        state or activity ("was present", "swam") an event has no single
        time, "before" and "after" are not converses (FraCaS 269, 271,
        272), and the clause keeps translate.py's opaque translation."""
        conj, s = sub.args
        if conj.head not in _ORDER:
            return None
        if s.head == "UseCl" and len(s.args) == 3 and s.args[1].head == "PPos":
            other = s.args[2]
        elif s.head == "ElliptS" and len(s.args) == 2 and s.args[1].head == "ellDid":
            other = App("PredVP", [s.args[0], vp])  # "before Smith did"
        else:
            return None
        if other.head != "PredVP" or other.args[0].head != "UsePN":
            return None
        if not (_telic(vp) and _telic(other.args[1])):
            return None
        main = translate_cl(App("PredVP", [subject, vp]))
        then = translate_cl(other)
        if not (_plain(main) and _plain(then)):
            return None
        times, who = [], []
        for v, np in ((vp, subject), (other.args[1], other.args[0])):
            name = _scope_name(v) + "Time"
            if name not in self.time_functions:
                self.time_functions.append(name)
            who.append(camel_name(_leaf_words(np)))
            times.append(f"{name} {who[-1]}")
        # The order mentions both individuals even when B's clause is not
        # asserted ("before"), so it declares them itself.
        order = Translation(
            lean_prop=f"{times[0]} {_ORDER[conj.head]} {times[1]}",
            free_predicates=[],
            free_individuals=list(dict.fromkeys(who)),
        )
        parts = [main, then, order] if conj.head == "after_Subj" else [main, order]
        return _combine(parts, "∧")

    def _perception(self, subject, vp):
        """"Smith saw Jones sign the contract": a perception report with a
        bare infinitive is veridical - what was seen happened ("Jones
        signed the contract", FraCaS 342) - and relates the perceiver to
        the event's agent: `seeSignContract smith jones ∧ signContract
        jones`. Only with proper names on both sides; a description as the
        perceived agent ("saw the chairman of ITEL sign", 343) is left
        untranslated."""
        slash, agent = vp.args
        if slash.args[0].head != "seeDo_V2V" or len(slash.args) != 2:
            return None
        if agent.head != "UsePN":
            raise NotImplementedError("perception report whose perceived agent is not a proper name")
        seen = translate_cl(App("PredVP", [agent, slash.args[1]]))
        if not _plain(seen):
            raise NotImplementedError("perceived event needs non-generic assembly")
        relation = camel_name(["see", *_leaf_words(slash.args[1], keep_det=True)])
        report = Translation(
            lean_prop=f"{relation} {camel_name(_leaf_words(subject))} {camel_name(_leaf_words(agent))}",
            free_predicates=[relation],
            free_individuals=[camel_name(_leaf_words(subject)), camel_name(_leaf_words(agent))],
            binary_predicates=[relation],
        )
        return _combine([report, seen], "∧")

    def _attitude(self, subject, vp):
        """"Smith knew that ITEL had won the contract": the attitude, as a
        relation between the holder and the complement's subject named by
        the verb and the complement's verb phrase (`knowWinContract smith
        itel`) - so "said", "believed" and "knew" never share a predicate -
        and, for a factive only, the complement itself (`winContract
        itel`), which it commits to (FraCaS 334); "believe"/"say" commit to
        nothing (335). Only a positive complement clause with a
        proper-name subject; anything else keeps the default."""
        verb, s = vp.args
        if not (s.head == "UseCl" and len(s.args) == 3 and s.args[1].head == "PPos"):
            return None
        cl = s.args[2]
        if not (cl.head == "PredVP" and cl.args[0].head == "UsePN"):
            return None
        said = translate_cl(cl)
        if not _plain(said):
            return None
        words = _leaf_words(cl.args[1], keep_det=True)
        # the name keeps the voice: "said Bill hurt himself" and "said Bill
        # had been hurt" are different reports
        if cl.args[1].head == "PassV2":
            words = ["be", *words]
        elif cl.args[1].head == "ReflVP":
            words = [*words, "self"]
        relation = camel_name([verb.head.rsplit("_", 1)[0], *words])
        knower, agent = camel_name(_leaf_words(subject)), camel_name(_leaf_words(cl.args[0]))
        attitude = Translation(
            lean_prop=f"{relation} {knower} {agent}",
            free_predicates=[relation],
            free_individuals=[knower, agent],
            binary_predicates=[relation],
        )
        if verb.head not in _FACTIVE:
            return attitude
        return _combine([attitude, said], "∧")

    def _implicative(self, subject, vp):
        """"ITEL managed to win the contract": the managing, as the
        default's opaque predicate of the whole verb phrase
        (`manageWinContract itel`), and the infinitive's own claim
        (`winContract itel`), which an implicative verb's positive use
        entails (FraCaS 336)."""
        done = translate_cl(App("PredVP", [subject, vp.args[1]]))
        if not _plain(done):
            return None
        who, managed = camel_name(_leaf_words(subject)), _scope_name(vp)
        attempt = Translation(
            lean_prop=f"{managed} {who}",
            free_predicates=[managed],
            free_individuals=[who],
        )
        return _combine([attempt, done], "∧")

    @staticmethod
    def _compared_cn(comp):
        """(adjective, noun, standard) for "is a ADJer N than NP"."""
        if comp.head == "CompNP" and comp.args[0].head == "DetCN" and len(comp.args[0].args) == 2:
            det, cn = comp.args[0].args
            if not (det.head == "DetQuant" and det.args[0].head == "IndefArt" and det.args[1].head == "NumSg"):
                return None
        elif comp.head == "CompCN":
            cn = comp.args[0]
        else:
            return None
        if cn.head != "ComparCN" or len(cn.args) != 3:
            return None
        return tuple(cn.args)

    def _comparative_cn(self, subject, adj, cn, standard):
        """"John is a fatter politician than Bill": John is a politician,
        and fatter *as a politician* than Bill - a relation of its own,
        `fatPoliticianThan john bill`, not `fatThan`. For some adjectives
        the two coincide ("fat") and for others they do not ("clever":
        clever for a politician need not be clever), and FraCaS tests
        exactly that pair (216/217); telling them apart needs lexical
        knowledge this pipeline does not have, so neither follows."""
        if standard.head != "UsePN":
            raise NotImplementedError("noun-phrase comparative with a non-proper-name standard")
        restrictor_expr, restrictor_preds = _restrictor_expr(_normalize_cn(cn))
        relation = camel_name([*_leaf_words(adj), *_leaf_words(cn)]) + "Than"
        x, y = camel_name(_leaf_words(subject)), camel_name(_leaf_words(standard))
        return Translation(
            lean_prop=f"({restrictor_expr} {x} ∧ {relation} {x} {y})",
            free_predicates=[*restrictor_preds, relation],
            free_individuals=[x, y],
            binary_predicates=[relation],
        )

    def _polar(self, s):
        """A tensed clause `UseCl tense pol cl` as a Prop. Negation only
        with a proper-name subject or a coordination of them; for the
        latter it is homogeneous - "Smith and Anderson did not sign" says
        neither signed - as plural predication is generally (Križ 2015)."""
        if not (s.head == "UseCl" and len(s.args) == 3):
            raise NotImplementedError("conditional clause that is not a plain tensed clause")
        pol, cl = s.args[1], s.args[2]
        tr = translate_cl(cl)
        if not _plain(tr):
            raise NotImplementedError("conditional clause needs non-generic assembly")
        if pol.head == "PPos":
            return tr
        subject = cl.args[0] if cl.head == "PredVP" else None
        if subject is not None and subject.head == "UsePN":
            names = [subject]
        elif subject is not None and subject.head == "ConjNP" and subject.args[0].head == "and_Conj":
            names = _np_list(subject.args[1]) or []
            if not all(np.head == "UsePN" for np in names):
                names = []
        else:
            names = []
        if not names:
            raise NotImplementedError("negated conditional clause without proper-name subjects (scope)")
        parts = []
        for np in names:
            one = translate_cl(App("PredVP", [np, cl.args[1]]))
            parts.append(Translation(
                lean_prop=f"¬ ({one.lean_prop})",
                free_predicates=one.free_predicates,
                free_individuals=one.free_individuals,
                binary_predicates=one.binary_predicates,
            ))
        return _combine(parts, "∧") if len(parts) > 1 else parts[0]

    def _conditional(self, adv, main):
        """"If S1, S2" as the material conditional S1 → S2."""
        if not (adv.head == "SubjS" and len(adv.args) == 2 and adv.args[0].head == "if_Subj"):
            return None
        antecedent, consequent = self._polar(adv.args[1]), self._polar(main)
        both = _combine([antecedent, consequent], "→")
        return both

    def _everyone(self, subject, vp):
        """"everyone (at the meeting) VP": every person (at the meeting)."""
        restrictor_preds = ["person"]
        restrictor_expr = "person"
        if subject.head == "AdvNP":
            pp_name = _scope_name(App("UseComp", [App("CompAdv", [subject.args[1]])]))
            restrictor_preds.append(pp_name)
            restrictor_expr = f"(fun x => person x ∧ {pp_name} x)"
        scope_name = _scope_name(vp)
        return Translation(
            lean_prop=self.quantified("Every", restrictor_expr, scope_name),
            free_predicates=[*restrictor_preds, scope_name],
        )

    def _partitive(self, subject, vp):
        """"one of the commissioners", "two of the machines": a counted
        partitive over a definite plural, read like a bare numeral (at
        least n / exactly n, the "numeral" ambiguity). "One of the Ns is
        NAME" is an identity, not a count, and is left to translate.py's
        own partitive-identity rule (FraCaS 14)."""
        det, np = subject.args
        if vp.head == "UseComp" and vp.args[0].head == "CompNP":
            return None
        if not (
            np.head == "DetCN"
            and len(np.args) == 2
            and np.args[0].head == "DetQuant"
            and np.args[0].args[0].head == "DefArt"
            and np.args[0].args[1].head == "NumPl"
        ):
            return None
        if det.head == "DetQuant" and len(det.args) == 2 and det.args[1].head == "NumSg":
            count = 1
        else:
            count = _bare_count(det)
        if count is None:
            return None
        quant = f"AtLeast {count}" if self.mode("numeral") == "weak" else f"Exactly {count}"
        restrictor_expr, restrictor_preds = _restrictor_expr(_normalize_cn(np.args[1]))
        scope_name = _scope_name(vp)
        return Translation(
            lean_prop=self.quantified(quant, restrictor_expr, scope_name),
            free_predicates=[*restrictor_preds, scope_name],
        )

    def quantifier(self, det):
        if not det.args:
            if det.head == "atLeastAFew_Det":
                return "AtLeast aFewCount"
            if det.head == "few_Det":
                return "AtMost fewCount" if self.mode("few") == "weak" else "Few"
            if det.head == "many_Det":
                return "Many" if self.mode("many") == "strong" else "Some"
            if det.head == "somePl_Det" and self.mode("somepl") == "strong":
                return "AtLeast 2+"
            if det.head == "aFew_Det":
                return "AtLeast aFewCount"
            if det.head == "several_Det":
                return "AtLeast severalCount"
            if det.head == "both_Det":
                return "Both"
            if det.head == "neither_Det":
                return "Neither"
            return None
        if det.head == "DetQuant" and len(det.args) == 2:
            quant, num = det.args
            if (
                num.head == "NumCard"
                and len(num.args) == 1
                and num.args[0].head == "AdNum"
                and num.args[0].args[0].head == "moreThan_AdN"
                and num.args[0].args[1].head == "NumNumeral"
            ):
                return f"AtLeast {_decode_numeral(num.args[0].args[1].args[0]) + 1}"
            if num.head == "NumCard" and len(num.args) == 1:
                count = _bare_count(det)
                if count is not None and self.mode("numeral") == "weak":
                    return f"AtLeast {count}"
                return None
            if quant.head == "DefArt" and num.head == "NumPl":
                return "Some" if self.mode("defpl") == "weak" else "Every+"
        return None

    def clause(self, quant: str, cn, vp):
        if vp.head == "AdVVP" and len(vp.args) == 2 and vp.args[0].head == "floatAll_AdV":
            # "The people who were at the meeting ALL voted" (FraCaS 93):
            # a floated "all" makes a plural subject universal, removing
            # the definite plural's collective/generic reading; the
            # definite still presupposes that there are such people.
            if quant not in ("Some", "Every+"):
                raise NotImplementedError(f"floated 'all' with quantifier {quant}")
            return "Every+", cn, vp.args[1]
        if quant == "Some" and cn.head == "RelCN" and self.mode("generic") != "weak":
            quant = "Every"
        # A floated "all" ("the Ancient Greeks were ALL noted philosophers",
        # FraCaS 96): a parse attaches it to the predicate nominal ("[all
        # noted philosophers]"), but a predicate nominal is not itself
        # quantified, so "all" there can only be floated off the subject -
        # which makes the subject unambiguously universal, whatever its own
        # determiner.
        if (
            vp.head == "UseComp"
            and len(vp.args) == 1
            and vp.args[0].head == "CompNP"
            and len(vp.args[0].args) == 1
            and vp.args[0].args[0].head == "PredetNP"
            and len(vp.args[0].args[0].args) == 2
            and vp.args[0].args[0].args[0].head == "all_Predet"
        ):
            quant = "Every"
            vp = App("UseComp", [App("CompNP", [vp.args[0].args[0].args[1]])])
        return quant, cn, vp

    def named_object(self, subject_name: str, vp):
        """A proper-name subject with a transitive verb whose object COUNTS:
        "APCOM won ten orders" (`AtLeast 10 order (win apcom)` / `Exactly 10
        ...`, see the "numeral" reading), "ITEL won some orders", and the
        quantity comparative "ITEL won more orders than APCOM did / than
        APCOM / than APCOM lost" (`More order (win itel) (win apcom)`; an
        elided verb is the main clause's own). The verb becomes a binary
        predicate and the object's determiner a quantifier over it, so
        counts can be compared and added - fused into one name ("won ten
        orders" -> `win10Order`) they can't. Only with a proper-name subject
        (no scope interaction with a quantified subject); other objects keep
        the fused name, so a problem mixing the two shapes may lose an
        inference, never gain a wrong one. Returns None when the shape
        doesn't match."""
        if not (
            vp.head == "ComplSlash"
            and len(vp.args) == 2
            and vp.args[0].head == "SlashV2a"
            and len(vp.args[0].args) == 1
        ):
            return None
        verb = camel_name(_leaf_words(vp.args[0]))
        obj = vp.args[1]
        if obj.head in ("MoreThanNP", "MoreThanAux", "MoreThanV2") and len(obj.args) >= 2:
            cn, standard = obj.args[0], obj.args[1]
            if standard.head != "UsePN" or len(standard.args) != 1:
                return None
            if obj.head == "MoreThanAux" and obj.args[2].head not in ("ellDid", "ellDoes", "ellHas"):
                return None
            other = camel_name(_leaf_words(standard))
            other_verb = camel_name(_leaf_words(obj.args[2])) if obj.head == "MoreThanV2" else verb
            restrictor_expr, restrictor_preds = _restrictor_expr(cn)
            return Translation(
                lean_prop=f"More {restrictor_expr} ({verb} {subject_name}) ({other_verb} {other})",
                free_predicates=[*restrictor_preds, verb, other_verb],
                free_individuals=[subject_name, other],
                binary_predicates=[verb, other_verb],
            )
        if obj.head != "DetCN" or len(obj.args) != 2 or not _is_counting_det(obj.args[0]):
            return None
        quant = _resolve_quantifier(obj.args[0])
        restrictor_expr, restrictor_preds = _restrictor_expr(_normalize_cn(obj.args[1]))
        return Translation(
            lean_prop=self.quantified(quant, restrictor_expr, f"({verb} {subject_name})"),
            free_predicates=[*restrictor_preds, verb],
            free_individuals=[subject_name],
            binary_predicates=[verb],
        )

    def counting_existential(self, quant: str, cn):
        """A counting existential ("there are few committee members from
        southern Europe", FraCaS 28/44) says the same as "few committee
        members are from southern Europe": the NP's own relative clause or
        PP is the scope. Without one there is nothing to count, so it is
        not handled."""
        if cn.head == "CompoundCN" and len(cn.args) == 2 and cn.args[1].head == "AdvCN":
            # "committee [members from southern Europe]" is the same set as
            # "[committee members] from southern Europe"
            inner = cn.args[1]
            cn = App("AdvCN", [App("CompoundCN", [cn.args[0], inner.args[0]]), inner.args[1]])
        if cn.head == "AdvCN" and len(cn.args) == 2 and cn.args[1].head == "PrepNP":
            restrictor_expr, restrictor_preds = _restrictor_expr(cn.args[0])
            scope_name = _scope_name(App("UseComp", [App("CompAdv", [cn.args[1]])]))
        elif (
            cn.head == "RelCN"
            and len(cn.args) == 2
            and cn.args[1].head == "UseRCl"
            and len(cn.args[1].args) == 3
            and cn.args[1].args[2].head == "RelVP"
            and len(cn.args[1].args[2].args) == 2
            and cn.args[1].args[2].args[0].head in _RELATIVE_PRONOUNS
        ):
            restrictor_expr, restrictor_preds = _restrictor_expr(cn.args[0])
            scope_name = _scope_name(cn.args[1].args[2].args[1])
        else:
            raise NotImplementedError(f"counting existential ({quant}) without a relative clause or PP")
        return Translation(
            lean_prop=self.quantified(quant, restrictor_expr, scope_name),
            free_predicates=[*restrictor_preds, scope_name],
        )

    def quantified(self, quant: str, restrictor: str, scope: str) -> str:
        """Two strong readings entail an existence fact: a definite plural
        presupposes its referents exist ("Every+": `Every` alone is
        vacuously true of no tenors at all), and "at least two" entails
        "some" ("AtLeast 2+"). In premise position that fact becomes a
        SEPARATE premise (`side_premises`) - logically the same as
        conjoining it, but a conjunction hides the plain `Every`/`AtLeast`
        premise from shape-directed tactics like `mono_nl` (CI run
        37185572606: FraCaS 23/55 were provable with `AtLeast 2 P Q` as a
        premise but not with `AtLeast 2 P Q ∧ Some P Q`). As a hypothesis,
        a definite plural must establish existence too, so it stays a
        conjunction; "at least two" needs no extra conjunct there."""
        if quant in ("Every+", "AtLeast 2+"):
            base = "Every" if quant == "Every+" else "AtLeast 2"
            if self.position == "premise":
                self.side_premises.append(f"Some {restrictor} {scope}")
                return f"{base} {restrictor} {scope}"
            if quant == "Every+":
                return f"(Every {restrictor} {scope} ∧ Some {restrictor} {scope})"
            return f"AtLeast 2 {restrictor} {scope}"
        return f"{quant} {restrictor} {scope}"


def translate_cl_reading(t, reading, position: str = "premise"):
    """Translate clause `t` under `reading` ("weak", "strong", or a dict
    {kind: "weak"|"strong"} over AMBIGUITY_KINDS). `position`
    ("premise"/"hypothesis") only chooses between equivalent renderings
    (see `EndToEndReadings.quantified`). Returns the translation, the
    side premises it entails, and the event-time functions it uses."""
    readings = EndToEndReadings(reading, position)
    tr = translate_cl_with(t, readings)
    return tr, list(readings.side_premises), list(readings.time_functions)
