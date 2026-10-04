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
  - "both"/"neither" use GQ.lean's own `Both`/`Neither`, which keep the
    exactly-two presupposition the default's `Every`/`No` drop;
  - a proper-name subject's counted object ("APCOM won ten orders") and
    quantity comparatives ("ITEL won more orders than APCOM did") keep
    the verb as a binary predicate (see `named_object`);
  - counting existentials ("there are few committee members from
    southern Europe") and a floated "all" ("the Ancient Greeks were all
    noted philosophers").

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
    Readings,
    Translation,
    _bare_count,
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


class EndToEndReadings(Readings):
    def __init__(self, reading, position: str):
        self.reading = reading
        self.position = position
        # Existence facts a strong reading entails, stated as separate
        # premises (see `quantified`).
        self.side_premises: list[str] = []

    def mode(self, kind: str) -> str:
        if isinstance(self.reading, dict):
            return self.reading.get(kind, "weak")
        return self.reading

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
            if det.head == "both_Det":
                return "Both"
            if det.head == "neither_Det":
                return "Neither"
            return None
        if det.head == "DetQuant" and len(det.args) == 2:
            quant, num = det.args
            if num.head == "NumCard" and len(num.args) == 1:
                count = _bare_count(det)
                if count is not None and self.mode("numeral") == "weak":
                    return f"AtLeast {count}"
                return None
            if quant.head == "DefArt" and num.head == "NumPl":
                return "Some" if self.mode("defpl") == "weak" else "Every+"
        return None

    def clause(self, quant: str, cn, vp):
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
    (see `EndToEndReadings.quantified`). Returns the translation and the
    side premises it entails."""
    readings = EndToEndReadings(reading, position)
    tr = translate_cl_with(t, readings)
    return tr, list(readings.side_premises)
