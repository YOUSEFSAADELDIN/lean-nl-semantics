#!/usr/bin/env python3
"""Translate a GF abstract syntax tree (as printed by the `gf` shell's
own tree notation - see gf/NOTES.md) into a Lean proposition using this
project's FraCaS.Section1.GQ vocabulary (Every/Some/No/Most).

This is deliberately narrow: it only handles the sentence shapes
proven end-to-end in gf/FraCaSLogic.gf / gf/NOTES.md so far. The main
one is
    PredVP (DetCN <det> <cn>) <vp>
a determiner-quantified subject predicated of a verb phrase, treating
the whole restrictor CN and the whole scope VP each as one named,
free predicate (matching how the existing hand-formalized FraCaS
Section 1 proofs already name things, e.g. `italianMan`,
`wantsGreatTenor` in LeanNLSemantics/FraCaS/Section1/Batch1.lean) -
not a deeper decomposition of the VP's own internal structure (a
control verb like "want" is not further translated into a relation
between an individual and a property; the whole VP becomes one
predicate name, exactly as the existing Lean proofs already do it).
A second, INVERTED shape (`_try_translate_partitive_identity`) handles
partitive-identity subjects ("one of the leading tenors is Pavarotti"):
there the proper noun becomes a free *individual* and the restrictor CN
becomes a predicate applied to it, matching Batch1.lean's own
`leadingTenor pavarotti` exactly - this is the one place the direction
of the match runs GF-tree-shape -> whatever-gets-a-human-picked-name-
right, rather than a uniform "restrictor/scope" split.

Two further wrinkles, both surfaced by problems 13/18-21 ("every_mp"/
"every_trans" in GQ.lean): a restrictor CN that's itself
relative-clause-modified (`RelCN base (UseRCl _ _ (RelVP IdRP vp))`,
"person that has the right to live in Europe") translates to a
CONJUNCTION of two separate predicates (`_restrictor_expr`, `fun x =>
basePred x ∧ vpPred x`), not one fused name - that's what the Lean
side's own `every_trans`/`every_mp` hypotheses actually need, and the
one place a restrictor isn't a bare predicate name. And a definite
subject NP, whether bare (`DetCN (DetQuant DefArt _) cn`) or
PP-modified (`AdvNP (DetCN ...) pp`, "the residents of member states"),
resolves to `Every`, not `Some` (`_QUANTIFIER_BY_QUANT`/
`_det_and_restrictor`) - matching how this project's own Lean proofs
already treat a definite-plural-subject premise (fracas_005,
fracas_021), and never for a definite NP used as an object elsewhere in
the same sentence.

Direction of the match, generally: this module always goes GF tree ->
Lean text, never the reverse. A GF tree carries real, unambiguous
linguistic structure (it comes from parsing/generating actual English
through the grammar, checked by `linearize`/`parse`); a hand-written
Lean identifier like `leadingTenor` or `cheap` is just an opaque string
a human already chose for readability, with no reliable way to invert
it back into a tree (which word is the noun vs. the adjective? is
"cheap" a predicate applied to individuals or a copula complement?).
So "matching the existing Lean proofs faithfully" means teaching this
translator to reproduce the name/shape a human already picked (see
`_scope_name`'s come_V special case and the partitive-identity case
above) - never editing the already-proven Lean theorems to match
whatever this translator happens to emit. The latter would also defeat
the point of cross-checking: it's only meaningful if the Lean proofs
were written independently from the English text, not backfit from
this tool.

Extending this to more sentence shapes (negation, relative clauses,
comparatives, ...) is expected to mean adding more cases to
`translate_cl` (or another `_try_translate_*` special case), not
redesigning the tree parser or the naming scheme.
"""

from __future__ import annotations
import re

from dataclasses import dataclass, field


# ---------------------------------------------------------------------
# 1. Parse GF's own tree notation ("Fun arg1 arg2 ...", parens group)
#    into a small Python tree: a Tree is either a bare identifier
#    (str) or an application (head: str, args: list[Tree]).
# ---------------------------------------------------------------------


@dataclass
class App:
    head: str
    args: list


def tokenize(s: str) -> list[str]:
    tokens = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
        elif c in "()":
            tokens.append(c)
            i += 1
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] not in "()":
                j += 1
            tokens.append(s[i:j])
            i = j
    return tokens


class ParseError(ValueError):
    pass


def parse_tree(text: str):
    """Parse GF tree notation into a Tree. A bare word is a 0-ary App
    (identical in shape to an application with no arguments, so callers
    can always pattern-match on `.head`)."""
    tokens = tokenize(text)
    pos = 0

    def peek():
        return tokens[pos] if pos < len(tokens) else None

    def parse_atom():
        nonlocal pos
        tok = peek()
        if tok is None:
            raise ParseError("unexpected end of input")
        if tok == "(":
            pos += 1
            t = parse_app()
            if peek() != ")":
                raise ParseError(f"expected ')', got {peek()!r}")
            pos += 1
            return t
        if tok == ")":
            raise ParseError("unexpected ')'")
        pos += 1
        return App(tok, [])

    def parse_app():
        nonlocal pos
        head_tree = parse_atom()
        args = []
        while peek() not in (None, ")"):
            args.append(parse_atom())
        if args:
            if head_tree.args:
                raise ParseError(f"'{head_tree.head}' already has arguments")
            return App(head_tree.head, args)
        return head_tree

    tree = parse_app()
    if pos != len(tokens):
        raise ParseError(f"trailing input after tree: {tokens[pos:]}")
    return tree


# ---------------------------------------------------------------------
# 2. Naming: turn a subtree into a Lean-identifier-friendly name by
#    collecting its leaf lexical items (in left-to-right order) and
#    camelCasing them together. Matches the existing hand-written
#    FraCaS Section 1 proofs' own naming style closely enough to be
#    readable (exact match isn't the goal - these are free variable
#    names, not semantic content).
# ---------------------------------------------------------------------

# Suffixes this grammar's own lexical funs use (gf/FraCaSLogic.gf) plus
# the handful of Structural words already reused directly (want_VV).
# _AdA is a degree word ("really", "very") - content-bearing enough to
# fold into the predicate name, unlike a bare quantifier/number marker.
# _PN (proper nouns, e.g. pavarotti_PN) is content-bearing too, but -
# unlike every other suffix here - it names a free *individual*, not a
# free *predicate*; see _try_translate_partitive_identity below for the
# one place that distinction actually matters. _V3 (a ditransitive verb,
# e.g. award_V3) is confirmed needed by fracas_139's own reflexive
# construction - the only id in this corpus that uses one.
_LEXICAL_SUFFIXES = ("_A", "_N", "_V2", "_VV", "_V", "_AdA", "_PN", "_Adv", "_V3", "_Prep")


def _is_leaf_lexical(name: str) -> bool:
    return any(name.endswith(suf) for suf in _LEXICAL_SUFFIXES)


def _leaf_words(t, keep_det: bool = False) -> list[str]:
    # Inside a VP name (keep_det), a definite plural object ("read out THE
    # ITEMS on the agenda") is read universally - the same convention this
    # translator already applies to a definite plural SUBJECT ("the
    # residents ..." -> `Every`, see _QUANTIFIER_BY_QUANT) - so it names
    # the same predicate as "read out EVERY ITEM on the agenda" (FraCaS 90).
    if (
        keep_det
        and t.head == "DetQuant"
        and len(t.args) == 2
        and t.args[0].head == "DefArt"
        and t.args[1].head == "NumPl"
    ):
        return ["every"]
    # A counted numeral on the object stays in the name too ("won TEN
    # orders" -> `win10Order`): dropping it made "won ten orders" and "won
    # eleven orders" one predicate, so either would have "followed" from
    # the other.
    if keep_det and t.head == "NumCard" and len(t.args) == 1:
        try:
            count, approx = _decode_card(t.args[0])
        except NotImplementedError:
            count, approx = None, None
        if count is not None:
            return ([approx[:1].lower() + approx[1:]] if approx else []) + [str(count)]
    if not t.args:
        if keep_det and t.head.endswith("_Det"):
            return [t.head[: -len("_Det")]]
        if _is_leaf_lexical(t.head):
            for suf in _LEXICAL_SUFFIXES:
                if t.head.endswith(suf):
                    # Drop the RGL's word-sense tag (`by8agent_Prep`/
                    # `by8means_Prep` -> "by"): both are the same English
                    # word, and a real parse can return either one for
                    # the same sentence - the tag must not leak into a
                    # predicate's name and split one predicate in two.
                    return [re.sub(r"8[a-z]+$", "", t.head[: -len(suf)])]
        return []
    words = []
    for a in t.args:
        words.extend(_leaf_words(a, keep_det))
    return words


def camel_name(words: list[str]) -> str:
    if not words:
        raise ValueError("no lexical content to name a predicate from")
    first, *rest = words
    return first[:1].lower() + first[1:] + "".join(w[:1].upper() + w[1:] for w in rest)


# ---------------------------------------------------------------------
# 3. The translator proper.
# ---------------------------------------------------------------------

# Determiners that are directly Det-typed (a bare *_Det constant sits
# straight in DetCN's first argument).
_QUANTIFIER_BY_DET = {
    "every_Det": "Every",
    "each_Det": "Every",
    "both_Det": "Every",  # restrictor-invariant cases ONLY - see note below
    "someSg_Det": "Some",
    "somePl_Det": "Some",
    "many_Det": "Some",
    "several_Det": "Some",
    "aFew_Det": "Some",
    "most_Det": "Most",
    "neither_Det": "No",  # restrictor-invariant cases ONLY - see note below
}
# CAUTION - `both_Det`/`neither_Det` -> "Every"/"No" is NOT a general
# translation of "both"/"neither": `GQ.lean`'s own `Both`/`Neither`
# types carry a real cardinality presupposition (`card P = 2 ∧ Every
# P Q`) that bare `Every`/`No` drop entirely, and `GQ.lean`'s own doc
# comment is explicit about when dropping it is harmless versus not -
# safe exactly when the restrictor never changes between premise and
# hypothesis (13/29/46, confirmed by reading each real theorem's own
# stated type: `fracas_029_from_gf` below genuinely needs this mapping,
# matching `fracas_029`'s own `Every commissioner leadingBusinessman`),
# unsafe the moment it does (77/78: "both/neither commissioners"
# narrowed to "both/neither FEMALE commissioners" of unknown size -
# `GQ.lean`'s own comment on `Both`/`Neither` names this exact pair as
# the reason those types exist at all). This translator has no way to
# tell the two apart from the determiner alone (that's a fact about the
# REST of the sentence, not about "both"/"neither" itself), so it
# can't safely attempt 77/78 at all - they are deliberately absent from
# the examples below and from `GFCrossCheckBatch.lean`, not silently
# mistranslated. Whoever wires 77/78 through this translator next needs
# to build the real `Both`/`Neither`-aware case first, not reuse this
# mapping assuming it generalizes.

# Determiners that are Quant-typed instead (no_Quant, this_Quant, ...):
# DetCN's first argument is then `DetQuant <quant> <num>` (mkDet's own
# bare-Quant desugaring, gf-rgl's Constructors.gf), not a bare *_Det.
# IndefArt ("a"/"an") is treated as existential, matching how this
# project's own Lean `Some` already covers "a/an/some/many/..." (see
# LeanNLSemantics/FraCaS/Section1/GQ.lean's doc comment on `Some`).
# DefArt ("the") is treated as universal when it's the SUBJECT's own
# determiner ("the residents of member states have..."/"the really
# ambitious tenors are Italian") - this only ever fires from
# `_resolve_subject` (never for a definite NP used as an object, e.g.
# "the concert" inside a PP), matching this project's own Lean
# convention for a definite-plural-subject premise (fracas_005,
# fracas_021: `Every ambitious italianPred`/`Every residentMemberState
# right`, not `Some`).
_QUANTIFIER_BY_QUANT = {
    "no_Quant": "No",
    "IndefArt": "Some",
    "DefArt": "Every",
}


# Numeral decoding: GF/RGL encodes a numeral as a chain of positional
# coercions (see gf/FraCaSLogic.gf's own comment on this), not as a
# plain int - `NumCard`'s own argument has to be walked apart to
# recover the count "three" was actually made of, rather than just
# reading `_num.head` as this project's earlier code did (which meant
# "at least three tenors" and "at most two tenors" both silently
# collapsed to the same bare `Some`, discarding the numeral entirely -
# the bug this decoder fixes).
_DIGIT_BY_CONST = {f"n{i}": i for i in range(2, 10)}

_APPROX_BY_ADN = {
    "at_least_AdN": "AtLeast",
    "at_most_AdN": "AtMost",
    "exactly_AdN": "Exactly",
}


def _decode_sub10(t) -> int:
    if t.head == "pot01" and not t.args:
        return 1
    if t.head == "pot0" and len(t.args) == 1 and t.args[0].head in _DIGIT_BY_CONST:
        return _DIGIT_BY_CONST[t.args[0].head]
    raise NotImplementedError(f"unrecognized Sub10 numeral shape: {t.head!r}")


def _decode_sub100(t) -> int:
    if t.head == "pot0as1" and len(t.args) == 1:
        return _decode_sub10(t.args[0])
    # pot110/pot111 are Numeral.gf's own dedicated "10"/"11" constants
    # (not built from a digit coercion the way 2-9 are) - problem 48's
    # "at most ten commissioners" is the first tree fed through this
    # translator that actually uses one (problem 32's identical "ten"
    # tree was never translated at all, since problem 32 itself is a
    # countermodel - see this file's own comment on why).
    if t.head == "pot110" and not t.args:
        return 10
    if t.head == "pot111" and not t.args:
        return 11
    raise NotImplementedError(f"unrecognized Sub100 numeral shape: {t.head!r}")


def _decode_sub1000(t) -> int:
    if t.head == "pot1as2" and len(t.args) == 1:
        return _decode_sub100(t.args[0])
    # `pot2` is the hundreds digit itself (a Sub10 tree, e.g. `pot2 (pot0
    # n5)` for "five hundred") - a real, general completion of this same
    # numeral hierarchy, not a one-off fact (same reasoning as pot110/
    # pot111's own earlier addition for "ten"/"eleven"); problem 242's
    # "500 MIPS" is the first tree fed through this translator that
    # actually needs a hundreds digit.
    if t.head == "pot2" and len(t.args) == 1:
        return 100 * _decode_sub10(t.args[0])
    raise NotImplementedError(f"unrecognized Sub1000 numeral shape: {t.head!r}")


def _decode_sub1000000(t) -> int:
    if t.head == "pot2as3" and len(t.args) == 1:
        return _decode_sub1000(t.args[0])
    raise NotImplementedError(f"unrecognized Sub1000000 numeral shape: {t.head!r}")


def _decode_numeral(t) -> int:
    if t.head == "num" and len(t.args) == 1:
        return _decode_sub1000000(t.args[0])
    raise NotImplementedError(f"unrecognized Numeral shape: {t.head!r}")


def _decode_card(card):
    """Returns (count, approx) for a `Card` tree - `approx` is
    'AtLeast'/'AtMost'/'Exactly' when the Card is `AdNum`-wrapped ("at
    least three"/"at most two"/"exactly two"), or None for a bare count
    with no AdNum wrapper at all ("one")."""
    if card.head == "NumNumeral" and len(card.args) == 1:
        return _decode_numeral(card.args[0]), None
    if card.head == "AdNum" and len(card.args) == 2:
        adn, inner = card.args
        if adn.head not in _APPROX_BY_ADN:
            raise NotImplementedError(f"unrecognized AdN {adn.head!r}")
        if inner.head != "NumNumeral" or len(inner.args) != 1:
            raise NotImplementedError(
                f"unrecognized AdNum-wrapped Card shape: {inner.head!r}"
            )
        return _decode_numeral(inner.args[0]), _APPROX_BY_ADN[adn.head]
    raise NotImplementedError(f"unrecognized Card shape: {card.head!r}")


# How to read constructions that have more than one reading. This base
# class is the translator's own (default) behaviour, which the GF
# cross-check theorems (scripts/gen_gf_cross_check.py) are proved
# against: each hook either returns None (no override) or the one fixed
# reading this module has always produced.
#
# The end-to-end pipeline (the project's fourth part) subclasses it in
# EndToEnd/readings.py to translate ambiguous English under several
# readings instead. That subclass, not this file, holds every reading
# the end-to-end pipeline adds; CI's default-translation snapshot
# (gf/default_translations.tsv) fails if anything here changes what the
# default produces.
class Readings:
    def quantifier(self, det):
        """Override `_resolve_quantifier` for `det`, or None."""
        return None

    def clause(self, quant: str, cn, vp):
        """Adjust a quantified clause's (quantifier, restrictor, VP).

        Bare-plural + relative-clause subjects ("leading tenors that are
        excellent are indispensable", problem 13) are a genuine ambiguity
        this translator can't resolve from syntax alone: `DetQuant IndefArt
        NumPl` is GF's own encoding for an article-less bare plural, used
        both for real existentials ("tenors are singing") and for FraCaS's
        own "characterizing generic construed as universal" idiom - which
        is what this specific problem needs (`every_mp`'s own `Every (fun
        x => leadingTenor x ∧ excellent x) indispensable`, not `Some`).
        Narrowly overridden here (not a blanket "bare plural = Every" rule,
        which would be wrong for a genuine existential bare plural) for
        exactly the shape that's actually confirmed to need it: a
        RelCN-restricted bare plural."""
        if quant == "Some" and cn.head == "RelCN":
            quant = "Every"
        return quant, cn, vp

    def named_object(self, subject_name: str, vp):
        """A translation of a proper-name subject's VP that keeps its
        object's quantifier separate from the verb, or None (the VP is then
        fused into one predicate name, see _scope_name)."""
        return None

    def counting_existential(self, quant: str, cn):
        """"there are QUANT CN ..." for a quantifier other than `Some`."""
        raise NotImplementedError(f"existential with a non-indefinite NP ({quant}) is not handled")

    def quantified(self, quant: str, restrictor: str, scope: str) -> str:
        """Render `quant restrictor scope`."""
        return f"{quant} {restrictor} {scope}"


_readings = Readings()


def translate_cl_with(t, readings: Readings):
    """`translate_cl` with `readings` in place of the default."""
    global _readings
    previous, _readings = _readings, readings
    try:
        return translate_cl(t)
    finally:
        _readings = previous


def _resolve_quantifier(det) -> str:
    override = _readings.quantifier(det)
    if override is not None:
        return override
    if det.head in _QUANTIFIER_BY_DET and not det.args:
        return _QUANTIFIER_BY_DET[det.head]
    if det.head == "DetQuant" and len(det.args) == 2:
        quant, num = det.args
        # A numeral-bounded Card ("at least three"/"at most two") always
        # decides the quantifier itself - the DetQuant's own `quant`
        # (typically IndefArt) is semantically vacuous here, just the
        # required article slot, same as PredetNP's wrapped NP.
        if num.head == "NumCard" and len(num.args) == 1:
            count, approx = _decode_card(num.args[0])
            if approx is not None:
                return f"{approx} {count}"
            # A bare counted numeral with no AdNum wrapper at all ("six
            # lawyers", not "at least"/"at most"/"exactly six") is this
            # project's own "Exactly" reading, not "Some" - confirmed by
            # fracas_085/086's own real theorems (`Exactly 6 lawyer
            # signed`/`Exactly 6 accountant signed`, for the gold
            # hypotheses "Six lawyers/accountants signed the contract"),
            # not guessed from the English alone. The end-to-end readings
            # (EndToEnd/readings.py) treat it as ambiguous instead.
            return f"Exactly {count}"
        if quant.head in _QUANTIFIER_BY_QUANT:
            return _QUANTIFIER_BY_QUANT[quant.head]
        raise NotImplementedError(
            f"quantifier {quant.head!r} has no known Lean mapping yet "
            "(see _QUANTIFIER_BY_QUANT)"
        )
    raise NotImplementedError(
        f"determiner shape {det.head!r} has no known Lean quantifier mapping yet "
        "(see _QUANTIFIER_BY_DET / _QUANTIFIER_BY_QUANT)"
    )


def _bare_count(det):
    """n for a bare counted numeral determiner ("six", not "at least
    six"), else None."""
    if det.head == "DetQuant" and len(det.args) == 2:
        num = det.args[1]
        if num.head == "NumCard" and len(num.args) == 1:
            count, approx = _decode_card(num.args[0])
            if approx is None:
                return count
    return None


# Predeterminers (PredetNP predet np - "all Italian men", not a *_Det
# itself): the wrapped NP's own Det is semantically vacuous (a bare
# plural, `DetQuant IndefArt NumPl`, chosen only because English needs
# *some* Det slot filled with something that realizes as no article -
# see gf/FraCaSLogic.gf's own comment on this), so the predeterminer
# alone decides the quantifier, same as this project's Lean `Every`
# already treats "all" as "every" (LeanNLSemantics/FraCaS/Section1/GQ.lean).
_QUANTIFIER_BY_PREDET = {
    "all_Predet": "Every",
}


def _det_and_restrictor(np):
    """Returns (det, restrictor_tree) for an NP that's either a bare
    `DetCN det cn` or a PP-modified `AdvNP (DetCN det cn) pp` - "the
    residents of member states" (problem 21). For the AdvNP case,
    restrictor_tree is the WHOLE AdvNP, not just its inner cn: the PP's
    own lexical content has to fold into the restrictor's name too
    ("the residents of member states" is one fused restrictor,
    `residentMemberState`, matching Batch1.lean's own variable name -
    not just `resident`, dropping "member states" on the floor)."""
    if np.head == "DetCN" and len(np.args) == 2:
        det, cn = np.args
        return det, cn
    if np.head == "AdvNP" and len(np.args) == 2:
        inner_np, _pp = np.args
        if inner_np.head != "DetCN" or len(inner_np.args) != 2:
            raise NotImplementedError(
                "AdvNP's own wrapped NP is only handled as a bare DetCN so far, "
                f"got head={inner_np.head!r}"
            )
        det, _inner_cn = inner_np.args
        return det, np
    raise NotImplementedError(
        f"only a DetCN or a PP-modified AdvNP(DetCN) subject is handled so far, "
        f"got head={np.head!r}"
    )


def _resolve_subject(subject):
    """Returns (quantifier, restrictor_tree) for a Cl's subject NP,
    handling `DetCN det cn`, `AdvNP (DetCN det cn) pp`, and either of
    those wrapped in `PredetNP predet (...)`."""
    if subject.head in ("DetCN", "AdvNP"):
        det, cn = _det_and_restrictor(subject)
        return _resolve_quantifier(det), cn
    if subject.head == "PredetNP" and len(subject.args) == 2:
        predet, np = subject.args
        # "only/just one accountant": a bare counted numeral already reads
        # as `Exactly n` (see _resolve_quantifier), which is exactly what
        # "only"/"just" add - so these defer to the wrapped determiner, and
        # only when it IS a counted numeral ("only accountants ..." is a
        # different, focus-sensitive construction, not handled).
        if predet.head in ("only_Predet", "just_Predet"):
            det, cn = _det_and_restrictor(np)
            count = _bare_count(det)
            if count is not None:
                return f"Exactly {count}", cn
            raise NotImplementedError(f"{predet.head} without a counted numeral is not handled")
        if predet.head not in _QUANTIFIER_BY_PREDET:
            raise NotImplementedError(
                f"predeterminer {predet.head!r} has no known Lean mapping yet "
                "(see _QUANTIFIER_BY_PREDET)"
            )
        _det, cn = _det_and_restrictor(np)
        return _QUANTIFIER_BY_PREDET[predet.head], cn
    raise NotImplementedError(
        "only a determiner-quantified subject (DetCN det cn), a PP-modified "
        "one (AdvNP (DetCN det cn) pp), or either wrapped in a predeterminer "
        f"(PredetNP predet (...)) is handled so far, got subject head={subject.head!r}"
    )


def _scope_name(vp) -> str:
    """Most VPs name their scope predicate from all of their own lexical
    content (matching e.g. `wantsGreatTenor`). "comes cheap" (`AdvVP
    (UseV come_V) cheap_Adv`) is a linking-verb idiom where "come"
    contributes no separate meaning of its own - the existing
    hand-written proof (`fracas_014`, Batch1.lean) already treats this
    as bare `cheap`, not a fused `comeCheap`, so this is special-cased
    to match it rather than generalized (e.g. "runs fast" is NOT
    reduced to "fast" here - only this specific come_V idiom is)."""
    if (
        vp.head == "AdvVP"
        and len(vp.args) == 2
        and vp.args[0].head == "UseV"
        and len(vp.args[0].args) == 1
        and vp.args[0].args[0].head == "come_V"
    ):
        return camel_name(_leaf_words(vp.args[1], keep_det=True))
    # Determiners inside the VP (on its object) stay in the name: "spend
    # a lot of time at home" and "spend time at home" (FraCaS 30-32, 47,
    # 48) are different predicates, and dropping `aLotOf_Det` made them
    # one - which let the end-to-end evaluation "prove" FraCaS 30/32/47
    # trivially, against gold. Subject determiners never reach this
    # function (the subject's own determiner becomes the quantifier), and
    # the grammatical articles (`DefArt`/`IndefArt`, inside `DetQuant`) are
    # not `_Det` leaves, so "read out the item" still names `readOutItem`.
    return camel_name(_leaf_words(vp, keep_det=True))


# Relative pronouns `_restrictor_expr` treats alike: `IdRP` (realized
# "that") and `who_RP` (FraCaSLogic.gf's own, realized "who" - FraCaS's
# own wording). Same relative clause, same translation.
_RELATIVE_PRONOUNS = ("IdRP", "who_RP")


def _normalize_cn(cn):
    """`AdjCN ap (RelCN base rel)` ("leading [tenors that are excellent]")
    and `RelCN (AdjCN ap base) rel` ("[leading tenors] that are
    excellent") are two attachments of the same words that a real parse
    (EndToEnd/parse_eval.py) returns side by side. With an intersective
    adjective both denote the same set, so the first is normalized into
    the second - otherwise the same English would translate differently
    (a fused name vs a conjunction, or - via translate_cl's bare-plural
    RelCN override - `Some` vs `Every`) purely as an artifact of which
    tree the parser ranked first."""
    if (
        cn.head == "AdjCN"
        and len(cn.args) == 2
        and cn.args[1].head == "RelCN"
        and len(cn.args[1].args) == 2
    ):
        inner = cn.args[1]
        return App("RelCN", [App("AdjCN", [cn.args[0], inner.args[0]]), inner.args[1]])
    return cn


def _restrictor_expr(cn):
    """Returns (expr, free_predicates) for a Cl's restrictor CN. Most
    CNs name a single free predicate over the whole CN's own lexical
    content (the existing behavior, matching e.g. `italianMan`). A
    relative-clause-modified CN - `RelCN base (UseRCl _ _ (RelVP IdRP
    vp))`, "person that has the right to live in Europe" - is different
    on purpose: FraCaS problems 18-21's own Lean encoding (`every_trans`
    in GQ.lean) treats this as a CONJUNCTION of two separate predicates
    (`fun x => person x ∧ right x`), not one fused name - matching that
    shape exactly is what "faithfully as possible" means here, the same
    principle behind `_try_translate_partitive_identity`'s inversion."""
    cn = _normalize_cn(cn)
    if (
        cn.head == "RelCN"
        and len(cn.args) == 2
        and cn.args[1].head == "UseRCl"
        and len(cn.args[1].args) == 3
        and cn.args[1].args[2].head == "RelVP"
        and len(cn.args[1].args[2].args) == 2
        and cn.args[1].args[2].args[0].head in _RELATIVE_PRONOUNS
    ):
        base_cn = cn.args[0]
        inner_vp = cn.args[1].args[2].args[1]
        base_name = camel_name(_leaf_words(base_cn))
        vp_name = _scope_name(inner_vp)
        return f"(fun x => {base_name} x ∧ {vp_name} x)", [base_name, vp_name]
    # A CN-conjunction - `ConjCN and_Conj (BaseCN cn1 cn2)`, "every
    # representative and client" on its narrow-scope (N-bar-conjunction)
    # reading - is the same "conjunction of predicates, not one fused
    # name" story as the RelCN case above: FraCaS problem 88's own Lean
    # encoding treats "representative and client" as the intersection
    # restrictor `fun x => rep x ∧ client x`, matching this project's
    # own conjunctive-restrictor convention exactly (problem 89's
    # "representative or client" is the disjunctive analogue,
    # `∨` instead of `∧`). Only the two-element case is handled - a
    # longer conjoined list would need a real n-ary fold, not attempted
    # here since no FraCaS problem so far needs one.
    if (
        cn.head == "ConjCN"
        and len(cn.args) == 2
        and cn.args[0].head in ("and_Conj", "or_Conj")
        and cn.args[1].head == "BaseCN"
        and len(cn.args[1].args) == 2
    ):
        op = "∧" if cn.args[0].head == "and_Conj" else "∨"
        left_cn, right_cn = cn.args[1].args
        left_name = camel_name(_leaf_words(left_cn))
        right_name = camel_name(_leaf_words(right_cn))
        return f"(fun x => {left_name} x {op} {right_name} x)", [left_name, right_name]
    name = camel_name(_leaf_words(cn))
    return name, [name]


@dataclass
class Translation:
    """One sentence's translation: the Lean Prop it denotes, plus the
    free predicates (name -> arity-1 predicate over the domain) and
    free individuals (name -> a bare element of the domain, e.g. a
    proper noun used as an individual constant) it needs declared as
    `variable`s before that Prop typechecks."""

    lean_prop: str
    free_predicates: list  # list[str], in the order first referenced
    free_individuals: list = field(default_factory=list)
    # Set only by `_try_translate_conjnp_subject`: the two conjuncts'
    # own separate Translations ("exactly two lawyers signed"/"three
    # accountants signed", for "exactly two lawyers and three
    # accountants signed"), each with its OWN narrower free_predicates -
    # a caller that needs to apply a theorem taking only ONE conjunct as
    # its premise (see scripts/gen_gf_cross_check.py's PROJECT_CONJUNCT)
    # has to use a conjunct's own predicates, not this Translation's
    # merged (wider) ones.
    conjuncts: "list | None" = None
    # Which of `free_predicates` are BINARY (`A -> A -> Prop`, applied
    # to two individuals) rather than this project's usual unary
    # restrictor/scope predicates (`A -> Prop`) - every predicate this
    # translator produced before `_try_translate_possessive_presupposition`
    # was unary, so callers built elsewhere (scripts/gen_gf_cross_check.py)
    # assumed it uniformly; this field lets them keep doing that for
    # every OTHER predicate while declaring these few correctly.
    binary_predicates: list = field(default_factory=list)
    # Free SKOLEM FUNCTIONS (`A -> A`, as opposed to every other free
    # variable this translator produces, which is either a predicate
    # or a bare individual) - set only by
    # `_try_translate_bound_possessive_presupposition`, for a bound
    # possessive pronoun ("every student used HER workstation": one
    # workstation per student, not one fixed individual).
    free_functions: list = field(default_factory=list)
    # Set only by `_try_translate_bound_possessive_presupposition`: the
    # raw, UNINSTANTIATED components of a universally-quantified
    # presupposition bundle (restrictor/gender/skolem/verb names, and
    # whether negated) - unlike `conjuncts` (already-concrete sub-
    # Translations), these are all parameterized by the bound variable,
    # so a caller (gen_gf_cross_check.py's SKOLEM_PROJECT) instantiates
    # ONE part at a SPECIFIC individual itself, rather than projecting
    # an already-built piece.
    template: "dict | None" = None


def _try_translate_partitive_identity(subject, vp):
    """Handles "N of the Xs is/are ProperNoun" (`CountNP (DetQuant _
    (NumCard ...)) (DetCN _ cn)` predicated of `UseComp (CompNP (UsePN
    pn))`) - e.g. fracas_014's "one of the leading tenors is Pavarotti".
    This is a genuine subject/predicate INVERSION relative to every
    other sentence shape handled here: the proper noun is a free
    *individual*, not folded into a scope predicate name, and the
    restrictor CN becomes a predicate applied directly to it - matching
    Batch1.lean's own `leadingTenor pavarotti` exactly (not an
    existential/counting statement built from the partitive's own
    numeral, which this problem's Lean formalization doesn't need
    either). Returns None when the shapes don't match, so the caller
    falls through to the general PredVP path."""
    if subject.head != "CountNP" or len(subject.args) != 2:
        return None
    _count, inner_np = subject.args
    if inner_np.head != "DetCN" or len(inner_np.args) != 2:
        return None
    _det, cn = inner_np.args
    if (
        vp.head != "UseComp"
        or len(vp.args) != 1
        or vp.args[0].head != "CompNP"
        or len(vp.args[0].args) != 1
        or vp.args[0].args[0].head != "UsePN"
        or len(vp.args[0].args[0].args) != 1
    ):
        return None
    pn = vp.args[0].args[0].args[0]
    restrictor_name = camel_name(_leaf_words(cn))
    individual_name = camel_name(_leaf_words(pn))
    return Translation(
        lean_prop=f"{restrictor_name} {individual_name}",
        free_predicates=[restrictor_name],
        free_individuals=[individual_name],
    )


def _try_translate_comparative(subject_name: str, vp):
    """"X is ADJ-er than Y" (`ComparA`) and "X is as ADJ as Y" (`CAdvAP
    as_CAdv`) as BINARY relations `adjThan x y` / `adjAs x y` - the
    naming scripts/gen_gf_cross_check.py's own comparative builders
    already use. Previously these fell through to `_scope_name`, which
    fused the whole VP into one unary predicate of the subject
    (`fastItelXZ pc6082`), so "as fast as" and "faster than" became the
    same predicate (FraCaS 228 then "followed" trivially, against gold),
    and the standard of comparison was lost entirely.

    The standard may be a named individual, `every`/indefinite-quantified
    ("faster than every ITEL computer" - `Every itelComputer (fastThan
    pc6082)`), or a two-way and/or coordination of named individuals.
    Anything else (a measure phrase like "five hundred MIPS", FraCaS 242)
    returns None and is left to the existing paths."""
    if not (
        vp.head == "UseComp"
        and len(vp.args) == 1
        and vp.args[0].head == "CompAP"
        and len(vp.args[0].args) == 1
    ):
        return None
    ap = vp.args[0].args[0]
    if ap.head == "ComparA" and len(ap.args) == 2:
        adj, standard = ap.args
        relation = camel_name(_leaf_words(adj)) + "Than"
    elif (
        ap.head == "CAdvAP"
        and len(ap.args) == 3
        and ap.args[0].head == "as_CAdv"
        and ap.args[1].head == "PositA"
    ):
        adj, standard = ap.args[1], ap.args[2]
        relation = camel_name(_leaf_words(adj)) + "As"
    else:
        return None

    def named(np):
        if np.head == "UsePN" and len(np.args) == 1:
            return camel_name(_leaf_words(np))
        return None

    other = named(standard)
    if other is not None:
        return Translation(
            lean_prop=f"{relation} {subject_name} {other}",
            free_predicates=[relation],
            free_individuals=[subject_name, other],
            binary_predicates=[relation],
        )
    if (
        standard.head == "ConjNP"
        and len(standard.args) == 2
        and standard.args[0].head in ("and_Conj", "or_Conj")
        and standard.args[1].head == "BaseNP"
        and len(standard.args[1].args) == 2
    ):
        names = [named(np) for np in standard.args[1].args]
        if all(names):
            op = "∧" if standard.args[0].head == "and_Conj" else "∨"
            return Translation(
                lean_prop=f"({relation} {subject_name} {names[0]} {op} {relation} {subject_name} {names[1]})",
                free_predicates=[relation],
                free_individuals=[subject_name, *names],
                binary_predicates=[relation],
            )
        return None
    if standard.head == "DetCN" and len(standard.args) == 2:
        # Free-choice "any" in a comparative's standard is universal:
        # "faster than any ITEL computer" is faster than each of them
        # (FraCaS 248). Read this way only here - elsewhere "any" is
        # mostly a negative-polarity existential.
        if standard.args[0].head == "anySg_Det" and not standard.args[0].args:
            quant = "Every"
        else:
            try:
                quant = _resolve_quantifier(standard.args[0])
            except NotImplementedError:
                return None
        if quant not in ("Every", "Some"):
            return None
        restrictor_expr, restrictor_preds = _restrictor_expr(standard.args[1])
        return Translation(
            lean_prop=f"{quant} {restrictor_expr} ({relation} {subject_name})",
            free_predicates=[*restrictor_preds, relation],
            free_individuals=[subject_name],
            binary_predicates=[relation],
        )
    return None


def _try_translate_named_individual_fact(subject, vp):
    """Handles a bare 'ProperNoun is/was a CN' or 'ProperNoun VERB-PHRASE'
    fact about a single named individual - e.g. fracas_099's "Smith was
    a client at the demonstration" and "Smith was impressed by the
    system's performance", or fracas_103's "Jones is an APCOM manager"
    and "Jones has a company car". This is the instantiate-a-universal-
    at-a-named-individual half of a FraCaS argument whose universal
    premise translate_cl already reaches via _resolve_subject/PredetNP
    - a genuinely different, much simpler shape than
    _try_translate_partitive_identity above (no partitive count
    involved: the fact directly names its own subject, so the only
    question is which predicate name it's a fact about).

    A copula 'is/was a CN' predicate reuses _restrictor_expr's own
    CN-naming (so "a client at the demonstration" fuses to the same
    name a corresponding "every client at the demonstration ..."
    premise would use); any other VP reuses _scope_name, the same way
    translate_cl's own scope predicate already does below. Neither
    name is required to match the hand-written Lean proof's own
    variable name exactly (see this module's docstring) - only to be
    the SAME name across a premise/hypothesis pair translated from the
    same English words, which both paths already guarantee."""
    if subject.head != "UsePN" or len(subject.args) != 1:
        return None
    individual_name = camel_name(_leaf_words(subject))
    comparative = _try_translate_comparative(individual_name, vp)
    if comparative is not None:
        return comparative
    counted = _readings.named_object(individual_name, vp)
    if counted is not None:
        return counted
    if (
        vp.head == "UseComp"
        and len(vp.args) == 1
        and vp.args[0].head == "CompNP"
        and len(vp.args[0].args) == 1
        and vp.args[0].args[0].head == "DetCN"
        and len(vp.args[0].args[0].args) == 2
    ):
        cn = vp.args[0].args[0].args[1]
        pred_expr, preds = _restrictor_expr(cn)
        return Translation(
            lean_prop=f"{pred_expr} {individual_name}",
            free_predicates=preds,
            free_individuals=[individual_name],
        )
    # `UseComp (CompCN cn)` - the RGL's other derivation of "is a CN",
    # with the indefinite article supplied by CompCN's own linearization
    # rather than a DetCN node. A real parse returns both derivations
    # for the same English (EndToEnd/parse_eval.py), so this must translate
    # identically to the CompNP/DetCN branch just above, not fall
    # through to `_scope_name`'s single fused name.
    if (
        vp.head == "UseComp"
        and len(vp.args) == 1
        and vp.args[0].head == "CompCN"
        and len(vp.args[0].args) == 1
    ):
        pred_expr, preds = _restrictor_expr(vp.args[0].args[0])
        return Translation(
            lean_prop=f"{pred_expr} {individual_name}",
            free_predicates=preds,
            free_individuals=[individual_name],
        )
    scope_name = _scope_name(vp)
    return Translation(
        lean_prop=f"{scope_name} {individual_name}",
        free_predicates=[scope_name],
        free_individuals=[individual_name],
    )


def _try_translate_conjnp_subject(subject, vp):
    """Handles a subject that's a conjunction of two INDEPENDENTLY
    quantified NPs - `ConjNP and_Conj (BaseNP np1 np2)`, "exactly two
    lawyers and three accountants signed the contract" (fracas_085/086)
    - as opposed to `_restrictor_expr`'s own `ConjCN` case (two bare CNs
    sharing ONE determiner, "every representative and client"). Each
    conjunct keeps its own determiner, so this isn't a single restrictor
    at all: it's the distributive reading "np1 VP and np2 VP", gotten by
    recursively translating each conjunct as its own full `PredVP np_i
    vp` sentence (reusing every existing subject/VP rule with no
    duplication) and `∧`-joining the results - the same "conjunction of
    two independent facts, not one fused predicate" principle as
    `CONJUNCT_IDS` in scripts/gen_gf_cross_check.py, just discovered
    from the GF tree shape directly instead of hard-coded per id. Only
    the two-conjunct case is handled (ConjCN's own restriction, for the
    same reason: no FraCaS problem so far needs a longer list). Returns
    None when the shape doesn't match."""
    if (
        subject.head != "ConjNP"
        or len(subject.args) != 2
        or subject.args[0].head != "and_Conj"
        or subject.args[1].head != "BaseNP"
        or len(subject.args[1].args) != 2
    ):
        return None
    np1, np2 = subject.args[1].args
    t1 = translate_cl(App("PredVP", [np1, vp]))
    t2 = translate_cl(App("PredVP", [np2, vp]))
    preds: list[str] = []
    for p in [*t1.free_predicates, *t2.free_predicates]:
        if p not in preds:
            preds.append(p)
    individuals: list[str] = []
    for v in [*t1.free_individuals, *t2.free_individuals]:
        if v not in individuals:
            individuals.append(v)
    return Translation(
        lean_prop=f"({t1.lean_prop} ∧ {t2.lean_prop})",
        free_predicates=preds,
        free_individuals=individuals,
        conjuncts=[t1, t2],
    )


def _unwrap_tense(t):
    """Strips a tensed utterance wrapper (`UttS (UseCl tense PPos cl)`)
    down to its own bare clause. Tense/aspect carries no Lean-side
    content for this project's own tenseless Props - every sentence
    this translator handled through Section 1/2 was written as a bare,
    present-tense `PredVP` tree with no wrapper at all, but Section 3's
    own GF trees (`gf/run_gf_tests.py`'s `_SECTION3_TENSED_CHECKS`) are
    written in the past tense throughout, wrapped accordingly - this
    unwrapping is what lets the same, tenseless `translate_cl` machinery
    apply unchanged. Only PPos is handled (every Section 3 tree
    confirmed so far is positive polarity); a PNeg tree falls through
    unwrapped and hits `translate_cl`'s own "only PredVP" error, rather
    than being guessed at here."""
    if (
        t.head == "UttS"
        and len(t.args) == 1
        and t.args[0].head == "UseCl"
        and len(t.args[0].args) == 3
        and t.args[0].args[1].head == "PPos"
    ):
        return t.args[0].args[2]
    return t


# Only she_Pron is handled - confirmed needed by fracas_114/115/116
# ("Mary used her workstation"); any other possessive pronoun is left
# to translate_cl's own general path rather than guessed at here.
_GENDER_BY_POSS_PRON = {"she_Pron": "female"}


def _try_translate_possessive_presupposition(subject, vp):
    """Handles "ProperNoun V2 POSS-PRON's N" ("Mary used her
    workstation") as a three-way presupposition bundle - gender(owner)
    AND has(owner, possessed) AND verb(owner, possessed) - matching
    this project's own Section 3 convention directly (Batch1.lean's own
    comment on fracas_114/115/116: "formalized as a bundle... 114/115/
    116 are then just projections out of the same bundle"), the same
    "presupposition as an explicit conjunct" principle Section 1's
    fracas_005 already uses for definite-article presupposition. The
    THREE conjuncts are exposed via `Translation.conjuncts` (same
    mechanism `_try_translate_conjnp_subject` already uses) so a caller
    that only needs ONE of them (scripts/gen_gf_cross_check.py's
    BUNDLE_PROJECT, for 114/115/116's own real theorems, each a
    projection out of this exact bundle) can use it directly instead of
    re-deriving it from a separately-translated hypothesis sentence -
    deliberately so: "Mary has a workstation", read on its own with no
    discourse link back to this premise, is genuinely ambiguous between
    a fresh existential (this project's own usual "has a N" reading,
    e.g. fracas_103's `haveCompanyCar jones`) and this bundle's own
    SPECIFIC named-possessed-individual reading, a distinction no
    single sentence's own GF tree resolves by itself. Returns None when
    the shape doesn't match."""
    if subject.head != "UsePN" or len(subject.args) != 1:
        return None
    if (
        vp.head != "ComplSlash"
        or len(vp.args) != 2
        or vp.args[0].head != "SlashV2a"
        or len(vp.args[0].args) != 1
    ):
        return None
    obj = vp.args[1]
    if obj.head != "DetCN" or len(obj.args) != 2:
        return None
    det, cn = obj.args
    if (
        det.head != "DetQuant"
        or len(det.args) != 2
        or det.args[0].head != "PossPron"
        or len(det.args[0].args) != 1
        or det.args[0].args[0].head not in _GENDER_BY_POSS_PRON
    ):
        return None
    gender_name = _GENDER_BY_POSS_PRON[det.args[0].args[0].head]
    owner_name = camel_name(_leaf_words(subject))
    noun_name = camel_name(_leaf_words(cn))
    possessed_name = owner_name + noun_name[0].upper() + noun_name[1:]
    verb_name = camel_name(_leaf_words(vp.args[0]))
    gender_part = Translation(
        lean_prop=f"{gender_name} {owner_name}",
        free_predicates=[gender_name],
        free_individuals=[owner_name],
    )
    has_part = Translation(
        lean_prop=f"has {owner_name} {possessed_name}",
        free_predicates=["has"],
        free_individuals=[owner_name, possessed_name],
        binary_predicates=["has"],
    )
    verb_part = Translation(
        lean_prop=f"{verb_name} {owner_name} {possessed_name}",
        free_predicates=[verb_name],
        free_individuals=[owner_name, possessed_name],
        binary_predicates=[verb_name],
    )
    parts = [gender_part, has_part, verb_part]
    preds: list[str] = []
    individuals: list[str] = []
    binary_preds: list[str] = []
    for p in parts:
        for pr in p.free_predicates:
            if pr not in preds:
                preds.append(pr)
        for v in p.free_individuals:
            if v not in individuals:
                individuals.append(v)
        for pr in p.binary_predicates:
            if pr not in binary_preds:
                binary_preds.append(pr)
    return Translation(
        lean_prop=f"({gender_part.lean_prop} ∧ {has_part.lean_prop} ∧ {verb_part.lean_prop})",
        free_predicates=preds,
        free_individuals=individuals,
        conjuncts=parts,
        binary_predicates=binary_preds,
    )


def _try_translate_bound_possessive_presupposition(subject, vp):
    """Handles a QUANTIFIED subject with a possessive-pronoun-object VP
    - "every/no student used her workstation" (fracas_117/118's shared
    premise 1, fracas_119's own premise 1) - the BOUND-pronoun analogue
    of `_try_translate_possessive_presupposition`: "her" here is bound
    by the quantifier, not a fixed individual, so it becomes a Skolem
    function `workstationOf : A -> A` (one workstation per student)
    rather than one fixed named individual - matching Batch1.lean's own
    fracas_117 comment directly ("the bound possessive 'her' becomes a
    Skolem function... the standard way to formalize a bound pronoun
    without building general anaphora machinery").

    Only `every_Det` (positive) and a bare `DetQuant no_Quant NumSg`
    (negative) are handled - confirmed needed by 117/118 and 119
    respectively. The negative case DROPS the gender/has conjuncts
    entirely (matching fracas_119's own narrower stated type, which
    never mentions `female`/`hasA` at all - confirmed by reading
    Batch1.lean's own separate `variable` block for P119 directly, not
    assumed from the positive case's shape), producing just the bare
    negated verb relation.

    Exposes its own raw components via `template` (not a flat lean_prop
    breakdown like `conjuncts`, since every part here is parameterized
    by the bound variable, not concrete) so a caller
    (scripts/gen_gf_cross_check.py's SKOLEM_PROJECT) can instantiate
    ONE part at a SPECIFIC individual - needed because "Mary used her
    workstation" or "Mary used a workstation", read on their own with
    no explicit link back to THIS premise's own Skolem function, are
    exactly as ambiguous as fracas_115's "Mary has a workstation" was
    (see `_try_translate_possessive_presupposition`'s own comment): the
    correspondence is a fact about this specific problem's own two
    premises together, not something a compositional, single-sentence
    reading of the hypothesis recovers on its own. Returns None when the
    shape doesn't match."""
    if subject.head != "DetCN" or len(subject.args) != 2:
        return None
    det, cn = subject.args
    if det.head == "every_Det" and not det.args:
        negated = False
    elif (
        det.head == "DetQuant"
        and len(det.args) == 2
        and det.args[0].head == "no_Quant"
        and not det.args[0].args
    ):
        negated = True
    else:
        return None
    if (
        vp.head != "ComplSlash"
        or len(vp.args) != 2
        or vp.args[0].head != "SlashV2a"
        or len(vp.args[0].args) != 1
    ):
        return None
    obj = vp.args[1]
    if obj.head != "DetCN" or len(obj.args) != 2:
        return None
    obj_det, obj_cn = obj.args
    if (
        obj_det.head != "DetQuant"
        or len(obj_det.args) != 2
        or obj_det.args[0].head != "PossPron"
        or len(obj_det.args[0].args) != 1
        or obj_det.args[0].args[0].head not in _GENDER_BY_POSS_PRON
    ):
        return None
    gender_name = _GENDER_BY_POSS_PRON[obj_det.args[0].args[0].head]
    restrictor_name = camel_name(_leaf_words(cn))
    noun_name = camel_name(_leaf_words(obj_cn))
    skolem_name = noun_name + "Of"
    verb_name = camel_name(_leaf_words(vp.args[0]))
    verb_expr = f"{verb_name} x ({skolem_name} x)"
    if negated:
        body = f"¬ {verb_expr}"
        preds = [restrictor_name, verb_name]
        binary_preds = [verb_name]
    else:
        body = f"({gender_name} x ∧ has x ({skolem_name} x) ∧ {verb_expr})"
        preds = [restrictor_name, gender_name, "has", verb_name]
        binary_preds = ["has", verb_name]
    template = {
        "restrictor": restrictor_name,
        "gender": gender_name,
        "skolem": skolem_name,
        "verb": verb_name,
        "negated": negated,
    }
    return Translation(
        lean_prop=f"(∀ x, {restrictor_name} x → {body})",
        free_predicates=preds,
        free_individuals=[],
        binary_predicates=binary_preds,
        free_functions=[skolem_name],
        template=template,
    )


def _translate_existential(np) -> Translation:
    """`ExistNP np` - "there is/are/was NP", FraCaS Section 1's usual
    hypothesis shape ("There are Italian men who want to be a great
    tenor"). Only an indefinite NP is handled (the existential's own
    definiteness restriction makes that the normal case). A relative
    clause on it supplies the scope - "there are [Italian men] [who want
    to be a great tenor]" is `Some italianMan wantToBeGreatTenor`, the same
    shape this project's own Lean statement of those problems uses - and
    a bare one is plain existence."""
    quant, cn = _resolve_subject(np)
    cn = _normalize_cn(cn)
    if quant != "Some":
        return _readings.counting_existential(quant, cn)
    if (
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
        return Translation(
            lean_prop=f"Some {restrictor_expr} {scope_name}",
            free_predicates=[*restrictor_preds, scope_name],
        )
    restrictor_expr, restrictor_preds = _restrictor_expr(cn)
    return Translation(
        lean_prop=f"∃ x, {restrictor_expr} x",
        free_predicates=restrictor_preds,
    )


# ---------------------------------------------------------------------
# 3b. Cross-sentential discourse resolution (FraCaS Section 3's
#     referential-pronoun class, problem 120: "Smith attended a
#     meeting. She chaired it." -> Lean: `∃ m, attended smith m ∧
#     chaired smith m`). This is a SEPARATE, PARALLEL pipeline from
#     `translate_cl` above, not a new case inside it - deliberately,
#     because the two pipelines disagree on what an indefinite object
#     means. `translate_cl`'s own existing convention for "ProperNoun V2
#     a/an N" (confirmed by fracas_103's real theorem, `hasCar jones`)
#     fuses the whole VP into one unary predicate; but THAT fact, read
#     with no discourse link to anything else, is exactly as ambiguous
#     as `_try_translate_possessive_presupposition`'s own documented
#     "Mary has a workstation" case - nothing in a single sentence's own
#     syntax picks the fused reading over a fresh-existential one. What
#     actually forces the existential reading for fracas_120's own
#     hypothesis is that it has to type-match its premise's own shared
#     bound variable - a discourse-structural fact, not something
#     `translate_cl`'s single-sentence dispatch could or should guess at
#     automatically (doing so would silently break fracas_103's own
#     already-confirmed translation, which needs the fused reading for
#     the identical tree shape). So this pipeline is invoked
#     explicitly, per problem, by whatever caller already knows a
#     specific sentence is playing a discourse-continuation role -
#     narrower than `translate_cl`'s own "any PredVP" scope, the same
#     "only what's confirmed needed" discipline every `_try_translate_*`
#     special case above already follows. It is NOT a general DRT/
#     assignment-function implementation (`Anaphora.lean`'s own header
#     explains why this project doesn't build one) - just enough
#     machinery to resolve a personal subject pronoun (she/he) to the
#     most recently introduced PERSONAL referent and an impersonal
#     object pronoun (it) to the most recently introduced IMPERSONAL
#     (existentially-bound) referent, confirmed sufficient for
#     fracas_120 and extended only when another confirmed GF tree needs
#     more (fracas_121's own PP-complement VP and three-sentence chain,
#     for instance, isn't handled yet).
# ---------------------------------------------------------------------


@dataclass
class Referent:
    """One discourse referent: either a NAMED individual (a proper noun
    already given a Lean constant name, `bound=False`) or a freshly
    introduced EXISTENTIAL variable (an indefinite object NP, `bound=
    True` - the noun's own predicate is dropped entirely, matching this
    project's existing convention elsewhere of not asserting "and x is
    a meeting" when nothing downstream needs it). `personal` is the
    primary disambiguator `DiscourseState.resolve` uses: True for a
    referent a personal pronoun (she/he) can pick out, False for one an
    impersonal pronoun (it/they) can. `proper` marks a referent
    introduced by an actual proper noun (`UsePN`, e.g. "ITEL") as
    opposed to a fresh indefinite object ("a report") - confirmed
    needed by fracas_121's own "them": once a sentence has introduced
    BOTH a named recipient (ITEL) and a same-impersonal-gender
    indefinite theme (a report) in the same clause, "them" in a LATER
    sentence has to prefer the proper-noun referent over the more
    recently introduced indefinite one, not just take whichever was
    added last (see `resolve`'s own comment)."""

    name: str
    bound: bool
    personal: bool
    proper: bool = False


class DiscourseState:
    """Threads discourse referents across a SEQUENCE of sentences, for
    cross-sentential pronoun resolution. See this section's own module
    comment for scope - this is deliberately narrow, not a general
    assignment-function implementation."""

    def __init__(self):
        self.referents: list[Referent] = []
        self._fresh_count = 0

    def add_named(self, name: str, *, personal: bool, proper: bool = False) -> Referent:
        for ref in self.referents:
            if not ref.bound and ref.name == name:
                return ref
        ref = Referent(name=name, bound=False, personal=personal, proper=proper)
        self.referents.append(ref)
        return ref

    def add_bound(self, *, personal: bool) -> Referent:
        self._fresh_count += 1
        name = "m" if self._fresh_count == 1 else f"m{self._fresh_count}"
        ref = Referent(name=name, bound=True, personal=personal)
        self.referents.append(ref)
        return ref

    def resolve(self, *, personal: bool) -> Referent:
        """Among referents matching `personal`, prefers the most
        recently introduced PROPER-NOUN one (a named recipient like
        "ITEL" is a far more salient antecedent than a same-gender
        indefinite theme mentioned in between), falling back to the
        most recent match of any kind when no proper-noun candidate
        exists (fracas_120's own "it", resolving to the indefinite
        "a meeting" - there is no competing proper-noun referent to
        prefer over it in that problem at all)."""
        matches = [ref for ref in reversed(self.referents) if ref.personal == personal]
        if not matches:
            raise NotImplementedError(
                f"no compatible discourse referent to resolve a pronoun to (personal={personal})"
            )
        proper_matches = [ref for ref in matches if ref.proper]
        return proper_matches[0] if proper_matches else matches[0]


# she_Pron/he_Pron resolve to the most recent PERSONAL referent;
# it_Pron/they_Pron to the most recent IMPERSONAL one. they_Pron is
# genuinely ambiguous in general (plural personal or plural impersonal)
# - only its impersonal reading is handled, confirmed needed by
# fracas_121's own "them" (referring back to ITEL, a company); a
# PERSONAL plural "they" isn't needed yet and isn't guessed at.
_PERSONAL_SUBJECT_PRON = {"she_Pron", "he_Pron"}
_IMPERSONAL_OBJECT_PRON = {"it_Pron", "they_Pron"}

# Proper nouns this corpus treats as IMPERSONAL (picked up again by
# "it"/"they", never "she"/"he") despite using the same `UsePN` shape
# personal names do - confirmed needed by fracas_121's "ITEL" (a
# company); `UsePN`'s own tree carries no gender/animacy marking the
# way a pronoun does, so this has to be an explicit lookup, extended
# only when another confirmed GF tree needs another impersonal proper
# noun, not guessed at from the name alone.
_IMPERSONAL_PROPER_NOUNS = {"itel_PN"}


def _resolve_np_referent(np, state: DiscourseState, *, existential: bool) -> Referent:
    """Resolves one NP to a discourse referent against `state`,
    introducing a new one when the NP is a proper noun (named) or a
    singular indefinite, or looking one up when it's a pronoun. Raises
    NotImplementedError for any other NP shape, same "narrow by design"
    discipline as every `_try_translate_*` special case in this file.

    `existential` controls what a singular indefinite NP introduces:
    `True` (fracas_120's own convention) gives it a fresh EXISTENTIALLY-
    BOUND referent, dropping the noun's own predicate entirely; `False`
    (fracas_121's own convention - confirmed by its real theorem's `:=
    id` proof, which has no existential anywhere) gives it a fresh
    NAMED free individual instead, keyed by the noun's own name. Which
    reading a given indefinite object needs is NOT recoverable from its
    own syntax alone (the two trees have an identical shape) - it's a
    discourse-structural fact about whether anything later needs to
    refer back to a SPECIFIC witness by name, which is why this is a
    parameter the caller supplies (already knowing the real theorem's
    own shape), not something this function infers."""
    if np.head == "UsePN" and len(np.args) == 1:
        personal = np.args[0].head not in _IMPERSONAL_PROPER_NOUNS
        return state.add_named(camel_name(_leaf_words(np)), personal=personal, proper=True)
    if np.head == "UsePron" and len(np.args) == 1:
        pron = np.args[0].head
        if pron in _PERSONAL_SUBJECT_PRON:
            return state.resolve(personal=True)
        if pron in _IMPERSONAL_OBJECT_PRON:
            return state.resolve(personal=False)
        raise NotImplementedError(
            f"pronoun {pron!r} not handled yet in discourse resolution "
            "(see _PERSONAL_SUBJECT_PRON/_IMPERSONAL_OBJECT_PRON)"
        )
    if (
        np.head == "DetCN"
        and len(np.args) == 2
        and np.args[0].head == "DetQuant"
        and len(np.args[0].args) == 2
        and np.args[0].args[0].head == "IndefArt"
    ):
        if existential:
            return state.add_bound(personal=False)
        return state.add_named(camel_name(_leaf_words(np)), personal=False)
    raise NotImplementedError(f"NP shape {np.head!r} not handled yet in discourse resolution")


def _strip_adv_wrapper(vp):
    """Strips an `AdVVP` adverb wrapper ("she ALSO delivered...") down
    to the VP it modifies - confirmed by fracas_121's own real theorem
    that "also" carries no truth-conditional content of its own here
    (its premise 2's formalization is the plain ternary relation, same
    as premises 1/3, nothing "also"-shaped added). Only `AdVVP` is
    stripped; any other wrapper is left alone for `translate_discourse`
    to reject on its own terms."""
    while vp.head == "AdVVP" and len(vp.args) == 2:
        vp = vp.args[1]
    return vp


def translate_discourse(sentences, *, existential_objects: bool = True) -> Translation:
    """Translates a SEQUENCE of already-tense-unwrapped `PredVP subject
    vp` clauses sharing ONE threaded `DiscourseState`, producing a
    single conjunction (bare, no outer parens - same convention as
    every other `Translation.lean_prop` this file produces; the caller
    wraps it if it's embedded in a larger expression). When
    `existential_objects` is true (the default, fracas_120's own
    reading), the result is existentially closed over every bound
    (indefinite-object) referent introduced anywhere in the sequence -
    fracas_120's own two premises, "Smith attended a meeting" + "she
    chaired it", become `∃ m, attended smith m ∧ chaired smith m`, the
    same proposition `scripts/gen_gf_cross_check.py`'s own
    `_build_fracas_120` used to hand-build directly from the raw trees.
    Called with a single sentence (no pronouns to resolve), this is
    also how fracas_120's own HYPOTHESIS gets its existential reading
    rather than `translate_cl`'s own fused-predicate one - see this
    section's module comment for why that's a different, explicitly-
    invoked pipeline rather than a new case inside `translate_cl`
    itself. With `existential_objects=False` (fracas_121's own reading -
    see `_resolve_np_referent`'s own comment on why that's a real,
    discourse-structural choice rather than a flag this function could
    infer), every indefinite object instead becomes a fresh NAMED free
    individual, and nothing is existentially bound at all.

    Two VP shapes are handled: a plain transitive `ComplSlash (SlashV2a
    verb) obj` (fracas_120's own binary relation), and a PP-complement
    `AdvVP (ComplSlash (SlashV2a verb) obj) (PrepNP prep pp)`
    (fracas_121's own ternary one, "delivered a report to ITEL" -
    `deliver subject pp obj`, confirmed argument order by
    `scripts/gen_gf_cross_check.py`'s own prior hand-built version of
    `_build_fracas_121`). An `AdVVP` adverb wrapper around either shape
    is stripped first (`_strip_adv_wrapper`). The PP's own NP is always
    resolved BEFORE the direct object within one sentence, regardless
    of the trees' own nesting order - deliberately, since a pronoun in
    the PP (fracas_121's own "them") must resolve against referents
    introduced by EARLIER sentences only, not get shadowed by a brand
    new indefinite direct object this SAME sentence is about to
    introduce (confirmed necessary: "she delivered an invoice to them"
    introduces "invoice" and resolves "them" in the same clause, and
    processing them in the wrong order would make "them" resolve to the
    invoice it sits next to instead of ITEL)."""
    state = DiscourseState()
    conjuncts: list[str] = []
    free_predicates: list[str] = []
    free_individuals: list[str] = []
    for cl in sentences:
        if cl.head != "PredVP" or len(cl.args) != 2:
            raise NotImplementedError(
                f"only 'PredVP subject vp' is handled in a discourse, got head={cl.head!r}"
            )
        subject, vp = cl.args
        vp = _strip_adv_wrapper(vp)
        subj_ref = _resolve_np_referent(subject, state, existential=existential_objects)
        if (
            vp.head == "ComplSlash"
            and len(vp.args) == 2
            and vp.args[0].head == "SlashV2a"
            and len(vp.args[0].args) == 1
        ):
            obj_ref = _resolve_np_referent(vp.args[1], state, existential=existential_objects)
            verb_name = camel_name(_leaf_words(vp.args[0]))
            conjuncts.append(f"{verb_name} {subj_ref.name} {obj_ref.name}")
            new_refs = (subj_ref, obj_ref)
        elif (
            vp.head == "AdvVP"
            and len(vp.args) == 2
            and vp.args[0].head == "ComplSlash"
            and len(vp.args[0].args) == 2
            and vp.args[0].args[0].head == "SlashV2a"
            and len(vp.args[0].args[0].args) == 1
            and vp.args[1].head == "PrepNP"
            and len(vp.args[1].args) == 2
        ):
            inner = vp.args[0]
            pp_ref = _resolve_np_referent(vp.args[1].args[1], state, existential=existential_objects)
            obj_ref = _resolve_np_referent(inner.args[1], state, existential=existential_objects)
            verb_name = camel_name(_leaf_words(inner.args[0]))
            conjuncts.append(f"{verb_name} {subj_ref.name} {pp_ref.name} {obj_ref.name}")
            new_refs = (subj_ref, pp_ref, obj_ref)
        else:
            raise NotImplementedError(
                "only a plain transitive VP (ComplSlash (SlashV2a verb) obj) or a "
                "PP-complement one (AdvVP (ComplSlash (SlashV2a verb) obj) (PrepNP "
                f"prep pp)) is handled in a discourse so far, got vp head={vp.head!r}"
            )
        if verb_name not in free_predicates:
            free_predicates.append(verb_name)
        for ref in new_refs:
            if not ref.bound and ref.name not in free_individuals:
                free_individuals.append(ref.name)
    bound_names = [r.name for r in state.referents if r.bound]
    body = " ∧ ".join(conjuncts)
    prop = f"∃ {' '.join(bound_names)}, {body}" if bound_names else body
    return Translation(
        lean_prop=prop,
        free_predicates=free_predicates,
        free_individuals=free_individuals,
        binary_predicates=list(free_predicates),
    )


def _try_translate_reflexive_indefinite_subject(subject, vp):
    """Handles an INDEFINITE subject with a reflexive ditransitive VP -
    e.g. fracas_139's own "A company director awarded himself a large
    payrise" -> `∃ d, awardLargePayrise d d`. Confirmed by the real
    theorem's own `:= id` proof (`(exists d, awarded d d) -> exists d,
    awarded d d`): the ditransitive's own direct object ("a large
    payrise") contributes nothing beyond the predicate's OWN name (the
    real Lean predicate is BINARY, `A -> A -> Prop`, not ternary), and
    "a company director" itself - not just its reflexive pronoun - is
    what's existentially bound, since nothing about being specifically
    a company director survives into the real theorem's stated type
    either. Matches `scripts/gen_gf_cross_check.py`'s own prior
    hand-built `_build_fracas_139` exactly (same verb-name derivation:
    the verb's own lexical content fused with the ditransitive object's,
    e.g. "award" + "largePayrise" -> "awardLargePayrise").

    Only a singular-indefinite subject (`DetCN (DetQuant IndefArt
    NumSg) cn`) with a `ReflVP (Slash2V3 verb obj)` VP is handled -
    confirmed sufficient for fracas_139, the only id in this corpus
    using a ditransitive verb at all. Returns None when the shape
    doesn't match, so the caller falls through to the general path."""
    if (
        subject.head != "DetCN"
        or len(subject.args) != 2
        or subject.args[0].head != "DetQuant"
        or len(subject.args[0].args) != 2
        or subject.args[0].args[0].head != "IndefArt"
    ):
        return None
    if vp.head != "ReflVP" or len(vp.args) != 1:
        return None
    inner = vp.args[0]
    if inner.head != "Slash2V3" or len(inner.args) != 2:
        return None
    verb_prefix = camel_name(_leaf_words(inner.args[0]))
    obj_name = camel_name(_leaf_words(inner.args[1]))
    verb_name = verb_prefix + obj_name[0].upper() + obj_name[1:]
    return Translation(
        lean_prop=f"∃ d, {verb_name} d d",
        free_predicates=[verb_name],
        free_individuals=[],
        binary_predicates=[verb_name],
    )


def _try_translate_reflexive_named_subject(subject, vp):
    """Handles a NAMED subject with a reflexive TRANSITIVE VP - e.g.
    fracas_140's own embedded clause "Bill had hurt himself" -> `hurt
    bill bill`. Distinct from `_try_translate_reflexive_indefinite_
    subject` above (that one's subject is INDEFINITE and its verb
    DITRANSITIVE, dropping its own direct object and existentially
    binding the subject itself); here the subject is already a fixed
    named individual and the verb is plain transitive, so nothing is
    existentially bound and there's no ditransitive object to drop -
    "himself" just doubles the named subject as both arguments of an
    ordinary binary relation. Returns None when the shape doesn't
    match."""
    if subject.head != "UsePN" or len(subject.args) != 1:
        return None
    if vp.head != "ReflVP" or len(vp.args) != 1:
        return None
    inner = vp.args[0]
    if inner.head != "SlashV2a" or len(inner.args) != 1:
        return None
    name = camel_name(_leaf_words(subject))
    verb_name = camel_name(_leaf_words(inner))
    return Translation(
        lean_prop=f"{verb_name} {name} {name}",
        free_predicates=[verb_name],
        free_individuals=[name],
        binary_predicates=[verb_name],
    )


def _unwrap_bare_usecl(t):
    """Strips a BARE `UseCl tense PPos clause` (no outer `UttS` the way
    `_unwrap_tense` expects) down to `clause` - needed for an EMBEDDED
    clause under `ComplVS` (fracas_140's own "said [that] Bill had hurt
    himself"), which this grammar never wraps in its own `UttS` (that
    wrapper only ever appears at the top of a whole utterance). Only
    PPos is handled, the same restriction `_unwrap_tense` already has."""
    if t.head == "UseCl" and len(t.args) == 3 and t.args[1].head == "PPos":
        return t.args[2]
    return t


def _try_translate_sentential_complement(subject, vp):
    """Handles a `ComplVS verb embedded` VP - "John said [that] Bill had
    hurt himself" -> `said john (hurt bill bill)`, confirmed by
    fracas_140's own real theorem (`said : A -> Prop -> Prop`, a flat
    embedding with no factivity/implicativity modeled - this project's
    own Section 9, Attitudes, explicitly doesn't attempt that in
    general; see `translate.py`'s own module-level comment on why
    Section 9 isn't in the generic pipeline). The embedded clause is
    translated RECURSIVELY via `translate_cl` itself (after stripping
    its own bare `UseCl` tense wrapper), reusing every existing single-
    sentence case - including `_try_translate_reflexive_named_subject`
    above - rather than re-parsing it by hand.

    Only `say_VS` is handled: `gf/run_gf_tests.py` confirms several
    OTHER attitude verbs share the same `_VS` lexical suffix (`claim_VS`/
    `know_VS`/`believe_VS`, across Section 4/9's own ids), but each of
    those ids' own real theorem needs checking individually before
    reusing this same flat-embedding treatment for it - not attempted
    here, same "only what's confirmed needed" discipline as
    `_LEXICAL_SUFFIXES` itself. Returns None when the shape doesn't
    match."""
    if vp.head != "ComplVS" or len(vp.args) != 2:
        return None
    verb_lemma, embedded = vp.args
    if verb_lemma.head != "say_VS" or verb_lemma.args:
        return None
    embedded_t = translate_cl(_unwrap_bare_usecl(embedded))
    subject_name = camel_name(_leaf_words(subject))
    return Translation(
        lean_prop=f"said {subject_name} ({embedded_t.lean_prop})",
        free_predicates=["said", *embedded_t.free_predicates],
        free_individuals=[subject_name, *embedded_t.free_individuals],
        binary_predicates=list(embedded_t.binary_predicates),
    )


# ---------------------------------------------------------------------
# 3c. Skolem-function continuation across a sentence pair (fracas_131/
#     132's shared "Each department has a dedicated line." premise,
#     continued either by a universally-bound pronoun subject ("They
#     rent them from BT.", 131) or by a definite-description subject
#     naming ONE specific instance ("The sales department rents it from
#     BT.", 132)). This is a THIRD, separate pipeline alongside
#     `translate_cl` and `translate_discourse` above - not a case inside
#     either - because the Skolem-function reading it builds is exactly
#     as context-dependent as `translate_discourse`'s own
#     `existential_objects` flag: "every department has a dedicated
#     line", read on its own, fuses into one unary predicate the same
#     way fracas_103's "Jones has a company car" does (confirmed - there
#     is no POSSESSIVE PRONOUN inside this sentence at all, the signal
#     `_try_translate_possessive_presupposition` relies on instead);
#     it's only a LATER sentence's own anaphoric
#     continuation that forces "a dedicated line" to become a function
#     of the department instead. Kept deliberately narrow to the one
#     shape confirmed needed by 131/132's own real theorems, not a
#     general "any later sentence licenses a Skolem function" rule.


def _head_noun_word(cn):
    """The innermost `UseN`'s own lexical head word, stripping any
    `AdjCN` adjective wrapper (descending into the modified noun) or
    `CompoundCN` noun-noun compounding (descending into the RIGHTMOST
    component, the standard English compound-noun headedness rule -
    "cover page" -> "page", confirmed needed by fracas_138's own "cover
    page" Skolem object) - distinct from `camel_name(_leaf_words(cn))`,
    which keeps the WHOLE compound (used to name the Skolem function
    itself, "dedicated line" -> `dedicatedLineOf`, "cover page" ->
    `coverPageOf`), whereas picking a short Lean bound-variable letter
    ("l" from "line", not "d" from "dedicated"; "p" from "page") wants
    just the head noun. Returns None if the shape isn't a bare, AdjCN-
    wrapped, or CompoundCN-wrapped `UseN`."""
    node = cn
    while True:
        if node.head == "AdjCN" and len(node.args) == 2:
            node = node.args[1]
        elif node.head == "CompoundCN" and len(node.args) == 2:
            node = node.args[1]
        else:
            break
    if node.head == "UseN" and len(node.args) == 1:
        leaf = node.args[0]
        for suf in _LEXICAL_SUFFIXES:
            if leaf.head.endswith(suf):
                return leaf.head[: -len(suf)]
    return None


@dataclass
class SkolemTemplate:
    restrictor: str
    skolem: str
    has_name: str
    bound_var: str
    witness_var: str


def _try_translate_skolem_universal_premise(subject, vp):
    """Recognizes "every/each X has a [possibly Adj-modified] Y" with NO
    possessive pronoun inside (unlike `_try_translate_possessive_
    presupposition`'s own single-sentence Skolem case) - confirmed
    needed by fracas_131/132's shared premise 1 ("Each department has a
    dedicated line"). Returns None on shape mismatch, else a
    (SkolemTemplate, this sentence's own universally-quantified Lean
    statement) pair; the caller decides, via which continuation
    function it goes on to use, whether the Skolem reading or the
    simpler fused one is the one actually wanted (matching this id's own
    real theorem) - this function alone never commits to that choice."""
    if subject.head != "DetCN" or len(subject.args) != 2:
        return None
    det, cn = subject.args
    if det.head not in ("every_Det", "each_Det") or det.args:
        return None
    if (
        vp.head != "ComplSlash"
        or len(vp.args) != 2
        or vp.args[0].head != "SlashV2a"
        or len(vp.args[0].args) != 1
        or vp.args[0].args[0].head != "have_V2"
    ):
        return None
    obj = vp.args[1]
    if obj.head != "DetCN" or len(obj.args) != 2:
        return None
    obj_det, obj_cn = obj.args
    if (
        obj_det.head != "DetQuant"
        or len(obj_det.args) != 2
        or obj_det.args[0].head != "IndefArt"
        or obj_det.args[1].head != "NumSg"
    ):
        return None
    head_noun = _head_noun_word(obj_cn)
    if head_noun is None:
        return None
    restrictor = camel_name(_leaf_words(cn))
    skolem = camel_name(_leaf_words(obj_cn)) + "Of"
    template = SkolemTemplate(
        restrictor=restrictor,
        skolem=skolem,
        has_name="has",
        bound_var=restrictor[0].lower(),
        witness_var=head_noun[0].lower(),
    )
    v = template.bound_var
    lean_prop = f"∀ {v}, {restrictor} {v} → has {v} ({skolem} {v})"
    return template, lean_prop


def _try_translate_skolem_continuation(subject, vp, template: SkolemTemplate):
    """Recognizes premise 2's own two shapes continuing a
    `SkolemTemplate`: a universally-bound pronoun subject ("they rent
    them from BT", 131) or a definite-description subject naming ONE
    instance ("the sales department rents it from BT", 132). Both are a
    ternary PP-complement VP ("rent ... from BT") whose own name is
    derived the SAME way `_try_translate_possessive_presupposition`'s
    own fused names are - `camel_name(_leaf_words(...))` over the WHOLE
    verb phrase INCLUDING its PP, which silently drops the preposition
    itself (`_Prep` isn't a recognized lexical suffix) and keeps just
    the verb and the PP's own object ("rent" + "BT" -> `rentBt`) -
    because nothing in this discourse ever refers back to the PP's
    object (BT) pronominally the way fracas_121's ITEL is (there "them"/
    "it" pick out ITEL specifically; here "from BT" is a fixed,
    never-anaphorically-continued modifier, so fusing it into the
    predicate name is the intended reading, not an explicit ternary
    argument). Returns None on shape mismatch, else (is_bound,
    instantiation, rel_name): `instantiation` is None for the bound
    (131) case, the camel-cased named individual for the named (132)
    case."""
    if (
        subject.head == "UsePron"
        and len(subject.args) == 1
        and subject.args[0].head == "they_Pron"
    ):
        is_bound = True
        instantiation = None
    elif subject.head == "DetCN" and len(subject.args) == 2:
        det, cn = subject.args
        if (
            det.head == "DetQuant"
            and len(det.args) == 2
            and det.args[0].head == "DefArt"
            and det.args[1].head == "NumSg"
        ):
            is_bound = False
            instantiation = camel_name(_leaf_words(cn))
        else:
            return None
    else:
        return None
    if vp.head != "AdvVP" or len(vp.args) != 2 or vp.args[1].head != "PrepNP":
        return None
    inner, pp = vp.args
    if (
        inner.head != "ComplSlash"
        or len(inner.args) != 2
        or inner.args[0].head != "SlashV2a"
        or inner.args[1].head != "UsePron"
    ):
        return None
    rel_name = camel_name(_leaf_words(vp))
    return is_bound, instantiation, rel_name


# ---------------------------------------------------------------------
# 3d. Donkey-pronoun MERGE across a sentence pair (fracas_122's own
#     "Every committee has a chairman. He is appointed by its members."
#     -> ONE combined statement, `∀c, committee c → ∃ch, chairman ch c
#     ∧ appointedByMembers ch c`, confirmed by the real theorem's own
#     `:= id` proof). This is a FOURTH pipeline, not a variant of 3c's
#     Skolem-continuation one: the SAME "every/each X has a [Adj] Y"
#     premise-1 shape needs a THIRD distinct reading here (an
#     existentially-bound witness SHARED with - not a function
#     parameter OF - the later sentence's own continuation, nested
#     INSIDE the same `∀` scope as one conjunction, not two separate
#     top-level antecedents), alongside fracas_103's fused-unary-
#     predicate reading and fracas_131/132's Skolem-function one - each
#     decided only by how (or whether) a later sentence continues it,
#     never recoverable from this one sentence's own syntax. Premise
#     2's own passive-voice continuation ("He is appointed by its
#     members") additionally needs PASSIVE-VP parsing (`PassV2` +
#     `by8agent_Prep`) and a POSSESSIVE-PRONOUN-governed agent phrase,
#     neither handled anywhere else in this translator - both kept
#     deliberately narrow to the one shape confirmed needed here.


@dataclass
class ExistentialTemplate:
    restrictor: str
    obj_name: str
    bound_var: str
    witness_var: str


def _try_translate_universal_existential_premise(subject, vp):
    """Recognizes the SAME "every/each X has a [possibly Adj-modified]
    Y" shape `_try_translate_skolem_universal_premise` does, but commits
    to a DIFFERENT reading of it: an existentially-bound witness SHARED
    with a later sentence's own continuation inside the SAME `∀` scope,
    rather than a Skolem function of the bound variable - confirmed
    needed by fracas_122's own premise 1 ("Every committee has a
    chairman"), whose real theorem merges it with "he is appointed by
    its members" into ONE statement, `∀c, committee c → ∃ch, chairman
    ch c ∧ appointedByMembers ch c` (see `_try_translate_universal_
    existential_continuation` for the second conjunct). The witness
    variable avoids colliding with the bound variable (both "committee"
    and "chairman" start with the same letter here) by falling back to
    a two-letter prefix - the same "ch" the prior hand-built version
    already used. Returns None on shape mismatch, else (
    ExistentialTemplate, this premise's own standalone existential
    statement - not used to assemble the final combined theorem, which
    needs premise 2's own continuation first, but kept for
    documentation/debugging parity with `_try_translate_skolem_
    universal_premise`'s own return shape)."""
    if subject.head != "DetCN" or len(subject.args) != 2:
        return None
    det, cn = subject.args
    if det.head not in ("every_Det", "each_Det") or det.args:
        return None
    if (
        vp.head != "ComplSlash"
        or len(vp.args) != 2
        or vp.args[0].head != "SlashV2a"
        or len(vp.args[0].args) != 1
        or vp.args[0].args[0].head != "have_V2"
    ):
        return None
    obj = vp.args[1]
    if obj.head != "DetCN" or len(obj.args) != 2:
        return None
    obj_det, obj_cn = obj.args
    if (
        obj_det.head != "DetQuant"
        or len(obj_det.args) != 2
        or obj_det.args[0].head != "IndefArt"
        or obj_det.args[1].head != "NumSg"
    ):
        return None
    head_noun = _head_noun_word(obj_cn)
    if head_noun is None:
        return None
    restrictor = camel_name(_leaf_words(cn))
    obj_name = camel_name(_leaf_words(obj_cn))
    bound_var = restrictor[0].lower()
    witness_var = head_noun[0].lower()
    if witness_var == bound_var:
        witness_var = head_noun[:2].lower()
    template = ExistentialTemplate(
        restrictor=restrictor, obj_name=obj_name, bound_var=bound_var, witness_var=witness_var
    )
    v, w = bound_var, witness_var
    lean_prop = f"∀ {v}, {restrictor} {v} → ∃ {w}, {obj_name} {w} {v}"
    return template, lean_prop


def _try_translate_universal_existential_continuation(subject, vp, template: ExistentialTemplate):
    """Recognizes premise 2's own passive-voice continuation of an
    `ExistentialTemplate` - "he is appointed by its members"
    (fracas_122) - a personal pronoun subject referring back to the
    existentially-bound witness (not the universally-bound restrictor),
    predicated by a passive VP (`PassV2`) whose own agent phrase
    (`by8agent_Prep`) is a plural NP governed by a POSSESSIVE PRONOUN
    referring back to the restrictor's own bound variable instead of a
    fixed individual - neither passive voice nor a possessive-pronoun-
    governed agent phrase is handled ANYWHERE else in this translator;
    both are confirmed needed here and nowhere else, so kept narrowly
    scoped to this one shape, the same "only what's confirmed needed"
    discipline as every other `_try_translate_*` function. The
    predicate name is derived the SAME way fracas_103's own fused names
    are - `camel_name(_leaf_words(vp))` over the WHOLE verb phrase,
    which (since neither `_Pron` nor the `by8agent_Prep`'s own `_Prep`
    is a recognized lexical suffix) keeps just the verb and the agent
    noun ("appoint" + "member" -> `appointMember`), silently dropping
    the preposition and the pronoun itself - the same way `_Prep`
    already drops "from" in fracas_131/132's own `rentBt`. Only
    `he_Pron`/`it_Pron` are recognized (confirmed sufficient for
    fracas_122 - the only id in this corpus using this shape at all).
    Returns None on shape mismatch, else the predicate name (the caller
    already has the template's own bound/witness variable names to
    apply it to)."""
    if subject.head != "UsePron" or len(subject.args) != 1 or subject.args[0].head != "he_Pron":
        return None
    if vp.head != "AdvVP" or len(vp.args) != 2 or vp.args[1].head != "PrepNP":
        return None
    inner, pp = vp.args
    if inner.head != "PassV2" or len(inner.args) != 1:
        return None
    if len(pp.args) != 2 or pp.args[0].head != "by8agent_Prep":
        return None
    agent_np = pp.args[1]
    if agent_np.head != "DetCN" or len(agent_np.args) != 2:
        return None
    agent_det, agent_cn = agent_np.args
    if (
        agent_det.head != "DetQuant"
        or len(agent_det.args) != 2
        or agent_det.args[0].head != "PossPron"
        or len(agent_det.args[0].args) != 1
        or agent_det.args[0].args[0].head != "it_Pron"
    ):
        return None
    return camel_name(_leaf_words(vp))


# ---------------------------------------------------------------------
# 3e. Cardinal/set-based anaphora (fracas_124's own "Two out of ten
#     machines are missing. They have been removed." -> "Two machines
#     have been removed."). The "ten" (the partitive's own denominator)
#     and the restrictor noun ("machines") both carry NO information in
#     this id's own real theorem - the whole domain is treated as being
#     exactly the ten machines, via a trivial `fun _ => True` restrictor
#     rather than a named one - so only the numerator count and the
#     adjective's/verb's own name are recovered from each sentence.


def _try_translate_cardinal_adjective_property(subject, vp):
    """Recognizes "N out of M Xs are ADJ" (fracas_124's own premise 1,
    "two out of ten machines are missing"). Returns None on shape
    mismatch, else (count, adj_name) - the restrictor noun and the
    partitive's own denominator M are both discarded, confirmed by
    this id's own real theorem never mentioning either."""
    if (
        subject.head != "AdvNP"
        or len(subject.args) != 2
        or subject.args[0].head != "DetNP"
        or len(subject.args[0].args) != 1
        or subject.args[1].head != "PrepNP"
        or len(subject.args[1].args) != 2
        or subject.args[1].args[0].head != "out_of_Prep"
    ):
        return None
    det_quant = subject.args[0].args[0]
    if (
        det_quant.head != "DetQuant"
        or len(det_quant.args) != 2
        or det_quant.args[0].head != "IndefArt"
        or det_quant.args[1].head != "NumCard"
        or len(det_quant.args[1].args) != 1
    ):
        return None
    count, approx = _decode_card(det_quant.args[1].args[0])
    if approx is not None:
        return None
    if vp.head != "UseComp" or len(vp.args) != 1 or vp.args[0].head != "CompAP":
        return None
    return count, camel_name(_leaf_words(vp))


def _try_translate_cardinal_passive_property(subject, vp):
    """Recognizes "N Xs have been PASSIVE-VERBed" (fracas_124's own
    hypothesis, "two machines have been removed"). Returns None on
    shape mismatch, else (count, verb_name) - the restrictor noun is
    again discarded, same reason as `_try_translate_cardinal_adjective_
    property`."""
    if subject.head != "DetCN" or len(subject.args) != 2:
        return None
    det, cn = subject.args
    if (
        det.head != "DetQuant"
        or len(det.args) != 2
        or det.args[0].head != "IndefArt"
        or det.args[1].head != "NumCard"
        or len(det.args[1].args) != 1
    ):
        return None
    count, approx = _decode_card(det.args[1].args[0])
    if approx is not None:
        return None
    if vp.head != "PassV2" or len(vp.args) != 1:
        return None
    return count, camel_name(_leaf_words(vp))


# ---------------------------------------------------------------------
# 3f. Definite-description-licensed total function (fracas_138's own
#     "Every report has a cover page [...] Smith signed the cover page
#     of R-95-103." -> `signed smith (coverPageOf r95103)`). Premise 1
#     reuses `_try_translate_skolem_universal_premise` directly (the
#     SAME "every X has a [possibly compound] Y" shape 131/132/138 all
#     share - only the Skolem function's own NAME is needed here, not
#     the bound/witness variables 131/132's own continuation uses,
#     since 138 never weakens back to an existential at all). The
#     hypothesis's own fully explicit "the cover page OF R-95-103" (an
#     `AdvCN`-wrapped definite description with its own `of`-PP) is what
#     licenses applying that Skolem function to a NAMED individual - not
#     premise 3's own bare "the cover page" alone, whose tree has no
#     link to R-95-103 at all (that link is a discourse fact, recovered
#     here from the hypothesis's own fuller tree instead, since premise
#     3 and the hypothesis share the identical fact textually anyway).


def _try_translate_definite_skolem_application(subject, vp):
    """Recognizes a named subject predicated of a definite description
    explicitly linked to ANOTHER named individual via an `of`-PP -
    "Smith signed the cover page of R-95-103" (fracas_138's own
    hypothesis). Returns None on shape mismatch, else (subject_name,
    verb_name, skolem_name, pn_name) - `skolem_name` matches the SAME
    `camel_name(_leaf_words(cn)) + "Of"` convention `_try_translate_
    skolem_universal_premise` already uses, so the two agree on the
    Skolem function's own name without either calling the other."""
    if subject.head != "UsePN":
        return None
    if (
        vp.head != "ComplSlash"
        or len(vp.args) != 2
        or vp.args[0].head != "SlashV2a"
        or len(vp.args[0].args) != 1
    ):
        return None
    obj = vp.args[1]
    if obj.head != "DetCN" or len(obj.args) != 2:
        return None
    obj_det, obj_cn = obj.args
    if (
        obj_det.head != "DetQuant"
        or len(obj_det.args) != 2
        or obj_det.args[0].head != "DefArt"
        or obj_det.args[1].head != "NumSg"
    ):
        return None
    if obj_cn.head != "AdvCN" or len(obj_cn.args) != 2:
        return None
    base_cn, pp = obj_cn.args
    if (
        pp.head != "PrepNP"
        or len(pp.args) != 2
        or pp.args[0].head != "of_Prep"
        or pp.args[1].head != "UsePN"
    ):
        return None
    subject_name = camel_name(_leaf_words(subject))
    verb_name = camel_name(_leaf_words(vp.args[0]))
    skolem_name = camel_name(_leaf_words(base_cn)) + "Of"
    pn_name = camel_name(_leaf_words(pp.args[1]))
    return subject_name, verb_name, skolem_name, pn_name


# ---------------------------------------------------------------------
# 3g. Genuine multi-reading referential ambiguity (fracas_128/129's own
#     shared premises, "John and his colleagues went to a meeting. They
#     hated it." - already formalized as TWO SEPARATE theorems, one per
#     reading of "they" (128: excludes John; 129: includes him), rather
#     than one theorem picking a winner - the correct response to
#     genuine ambiguity, not something either reading's own pipeline
#     should try to resolve automatically. Both readings share the
#     IDENTICAL premise 1 and premise 2 trees; only the hypothesis
#     (translated separately per id) differs.


def _try_translate_conjoined_possessive_restrictor(subject):
    """Recognizes "NAME and his/her Ns" (fracas_128/129's own shared
    premise 1 subject, "John and his colleagues") - a `ConjNP` of a
    named individual with a plural NP governed by a possessive pronoun
    referring back to that SAME individual. Returns None on shape
    mismatch, else (person_name, restrictor_name); only the restrictor
    name is used by either of this corpus's two callers - premise 1's
    own VP ("went to a meeting") is a pure distractor neither 128 nor
    129's real theorem ever uses, so the caller passes only `subject`,
    never `vp`."""
    if subject.head != "ConjNP" or len(subject.args) != 2 or subject.args[0].head != "and_Conj":
        return None
    base = subject.args[1]
    if base.head != "BaseNP" or len(base.args) != 2:
        return None
    person, poss_np = base.args
    if person.head != "UsePN":
        return None
    if poss_np.head != "DetCN" or len(poss_np.args) != 2:
        return None
    det, cn = poss_np.args
    if (
        det.head != "DetQuant"
        or len(det.args) != 2
        or det.args[0].head != "PossPron"
        or len(det.args[0].args) != 1
        or det.args[1].head != "NumPl"
    ):
        return None
    person_name = camel_name(_leaf_words(person))
    restrictor_name = camel_name(_leaf_words(cn))
    return person_name, restrictor_name


def _try_translate_pronoun_verb_pronoun(subject, vp):
    """Recognizes a plain "PronSubj V2 PronObj" VP ("they hated it",
    fracas_128/129's own shared premise 2) where BOTH the subject and
    object are pronouns contributing nothing to naming - confirmed by
    this corpus's own two callers, which only ever need the verb's own
    name (same as every other pronoun this generator's builders have
    seen). Returns None on shape mismatch, else the verb name."""
    if subject.head != "UsePron":
        return None
    if (
        vp.head != "ComplSlash"
        or len(vp.args) != 2
        or vp.args[0].head != "SlashV2a"
        or len(vp.args[0].args) != 1
        or vp.args[1].head != "UsePron"
    ):
        return None
    return camel_name(_leaf_words(vp))


# ---------------------------------------------------------------------
# 3h. E-type anaphora (fracas_133's own "GFI owns several computers.
#     ITEL maintains them." -> `(∃x, ownComputer x) → (∀x, ownComputer x
#     → maintain x) → ∀x, ownComputer x → maintain x`). "Them" resolves
#     to the MAXIMAL set GFI owns, not just the "several" witnesses, so
#     premise 1's own named subject (GFI) is existentially QUANTIFIED
#     AWAY entirely rather than kept as a fixed individual - the
#     opposite move from every other named-subject case in this
#     corpus, and the reason this needs its own dedicated pair of
#     functions rather than reusing `translate_cl`'s own general fused-
#     predicate path (which keeps the subject, giving `ownComputer gfi`
#     - correct for fracas_103's identical shape, wrong for this one).


def _try_translate_named_verb_several(subject, vp):
    """Recognizes "NAME V2s several Ns" (fracas_133's own premise 1,
    "GFI owns several computers"). Returns None on shape mismatch, else
    the fused verb+object predicate name ("own"+"computer" ->
    `ownComputer`) - the SAME fused-name convention `translate_cl`'s own
    general path already uses for a named-subject-plus-indefinite-
    object VP (fracas_103's `hasCar`), just confirmed here via
    `several_Det` instead of an ordinary indefinite article. The named
    subject itself is discarded entirely: this id's own real theorem
    existentially quantifies over a FRESH variable instead of applying
    the predicate to GFI, the e-type reading, not a fused "subject has
    property" one."""
    if subject.head != "UsePN":
        return None
    if (
        vp.head != "ComplSlash"
        or len(vp.args) != 2
        or vp.args[0].head != "SlashV2a"
        or len(vp.args[0].args) != 1
    ):
        return None
    obj = vp.args[1]
    if obj.head != "DetCN" or len(obj.args) != 2 or obj.args[0].head != "several_Det":
        return None
    return camel_name(_leaf_words(vp))


def _try_translate_named_verb_pronoun_object(subject, vp):
    """Recognizes "NAME V2s PronObj" (fracas_133's own premise 2, "ITEL
    maintains them") - both the named subject and the pronoun object
    are discarded entirely (the pronoun resolves to the SAME fresh
    variable `_try_translate_named_verb_several`'s own premise 1
    existentially quantifies, not to ITEL or to any individual named in
    this sentence at all), leaving only the verb's own name. Returns
    None on shape mismatch, else the verb name."""
    if subject.head != "UsePN":
        return None
    if (
        vp.head != "ComplSlash"
        or len(vp.args) != 2
        or vp.args[0].head != "SlashV2a"
        or len(vp.args[0].args) != 1
        or vp.args[1].head != "UsePron"
    ):
        return None
    return camel_name(_leaf_words(vp))


# ---------------------------------------------------------------------
# 3i. Single-sentence donkey relative clause with a TWO-SORTED domain
#     (fracas_134/135's shared "Every customer that owns a computer has
#     a service contract for it." -> `∀x, customer x → ∀c, own x c →
#     haveServiceContract x c`). Unlike every other donkey/Skolem
#     pipeline in this file (120-122/131/132, all built across TWO
#     sentences), this donkey binding is internal to ONE sentence's own
#     subject-gap relative clause (`RelCN`+`RelVP IdRP`), continued by a
#     pronoun in the SAME sentence's main-clause object ("for it"). The
#     customer/computer distinction also needs a genuinely two-sorted
#     Lean domain (`{A B : Type*}`) - every other id in this corpus
#     (every CUSTOM_BUILD function before this one) uses a single
#     `{A : Type*}`, but nothing about the GENERATOR's own dispatch
#     mechanism requires that - `binders`/`arrow_chain` are plain
#     strings a builder function is free to write however its own real
#     theorem needs, so a second sort is just a matter of actually
#     doing it, not a structural blocker.


def _unwrap_rel_tense(t):
    """Strips a `UseRCl tense PPos relvp` wrapper down to `relvp` - the
    relative-clause analog of `_unwrap_tense`."""
    if t.head == "UseRCl" and len(t.args) == 3 and t.args[1].head == "PPos":
        return t.args[2]
    return t


def _try_translate_donkey_relative_premise(subject, vp):
    """Recognizes "every CN that V2s a [indefinite] CN2 V2s [complex
    object] for it" (fracas_134/135's own shared premise 1, "Every
    customer that owns a computer has a service contract for it") - a
    subject-gap relative clause (`RelCN`+`RelVP IdRP`) introducing a
    donkey-bound indefinite, continued by a pronoun in the MAIN
    clause's own object ("for it"), the standard donkey-sentence
    construction (the same strong/weak donkey logical shape 134/135/136
    already document, built here directly from ONE sentence's own
    internal structure rather than across two sentences the way every
    other donkey/Skolem pipeline in this file is). `translate_cl`'s own
    general restrictor-fusion path ALSO parses this tree shape without
    erroring, but commits to the WRONG reading for it (fusing the
    relative clause into one conjunctive restrictor and the whole "for
    it" object into one unary predicate, discarding the donkey
    pronoun's own link entirely) - confirmed by direct comparison, not
    assumed, the same "check what translate_cl already does before
    writing a new case" discipline every other pipeline this session
    followed. Returns None on shape mismatch, else (restrictor_name,
    donkey_verb_name, main_verb_name)."""
    if subject.head != "DetCN" or len(subject.args) != 2:
        return None
    det, relcn = subject.args
    if det.head != "every_Det" or det.args:
        return None
    if relcn.head != "RelCN" or len(relcn.args) != 2:
        return None
    outer_cn, rel_clause = relcn.args
    rel_clause = _unwrap_rel_tense(rel_clause)
    if rel_clause.head != "RelVP" or len(rel_clause.args) != 2 or rel_clause.args[0].head != "IdRP":
        return None
    inner_vp = rel_clause.args[1]
    if (
        inner_vp.head != "ComplSlash"
        or len(inner_vp.args) != 2
        or inner_vp.args[0].head != "SlashV2a"
        or len(inner_vp.args[0].args) != 1
    ):
        return None
    donkey_obj = inner_vp.args[1]
    if (
        donkey_obj.head != "DetCN"
        or len(donkey_obj.args) != 2
        or donkey_obj.args[0].head != "DetQuant"
        or len(donkey_obj.args[0].args) != 2
        or donkey_obj.args[0].args[0].head != "IndefArt"
        or donkey_obj.args[0].args[1].head != "NumSg"
    ):
        return None
    if (
        vp.head != "ComplSlash"
        or len(vp.args) != 2
        or vp.args[0].head != "SlashV2a"
        or len(vp.args[0].args) != 1
    ):
        return None
    main_obj = vp.args[1]
    if main_obj.head != "AdvNP" or len(main_obj.args) != 2 or main_obj.args[1].head != "PrepNP":
        return None
    pp = main_obj.args[1]
    if (
        len(pp.args) != 2
        or pp.args[1].head != "UsePron"
        or len(pp.args[1].args) != 1
        or pp.args[1].args[0].head != "it_Pron"
    ):
        return None
    restrictor_name = camel_name(_leaf_words(outer_cn))
    donkey_verb_name = camel_name(_leaf_words(inner_vp.args[0]))
    main_verb_name = camel_name(_leaf_words(vp))
    return restrictor_name, donkey_verb_name, main_verb_name


def _try_translate_named_copula_relative_restrictor(subject, vp):
    """Recognizes "NAME is a CN that ..." (fracas_134/135's own shared
    premise 2 shape, "MFI is a customer that owns exactly one/several
    computers") - the relative clause's own content is a pure
    distractor, confirmed by reading the real theorem's own stated type
    directly (both 134 and 135 reduce premise 2 to just `customer mfi`,
    discarding whether it's "exactly one" or "several" entirely, so
    this function never even looks past the relative clause's own
    opening `RelCN` node). Returns None on shape mismatch, else
    (subject_name, restrictor_name)."""
    if subject.head != "UsePN":
        return None
    if vp.head != "UseComp" or len(vp.args) != 1 or vp.args[0].head != "CompNP":
        return None
    np = vp.args[0].args[0] if vp.args[0].args else None
    if np is None or np.head != "DetCN" or len(np.args) != 2:
        return None
    det, cn = np.args
    if (
        det.head != "DetQuant"
        or len(det.args) != 2
        or det.args[0].head != "IndefArt"
        or det.args[1].head != "NumSg"
    ):
        return None
    if cn.head != "RelCN" or len(cn.args) != 2:
        return None
    outer_cn = cn.args[0]
    subject_name = camel_name(_leaf_words(subject))
    restrictor_name = camel_name(_leaf_words(outer_cn))
    return subject_name, restrictor_name


# ---------------------------------------------------------------------
# Section 4 (ellipsis/gapping). Per Ellipsis.lean's own approach note,
# this project never models ellipsis/gapping RESOLUTION itself, only
# the already-resolved content - most Section 4 ids already go through
# `_atomic_name` (fusing a whole resolved sentence into one bare `Prop`
# atom, gen_gf_cross_check.py's own helper, not translate.py's, since
# there's no domain-quantified structure left to preserve once
# resolved). These two functions are for the MINORITY of ids whose own
# real theorem keeps real domain-quantified structure after resolution.


def _try_translate_double_pp_verb(vp):
    """Recognizes an intransitive verb with two PP adjuncts - "goes to
    Paris by car" (fracas_150-153's own shared gapping pattern,
    `AdvVP(AdvVP(UseV verb)(PrepNP prep1 obj1))(PrepNP prep2 obj2)`).
    Returns None on shape mismatch, else (verb_name, pp1_name,
    pp2_name)."""
    if vp.head != "AdvVP" or len(vp.args) != 2 or vp.args[1].head != "PrepNP":
        return None
    inner, pp2 = vp.args
    if inner.head != "AdvVP" or len(inner.args) != 2 or inner.args[1].head != "PrepNP":
        return None
    verb_vp, pp1 = inner.args
    if verb_vp.head != "UseV" or len(verb_vp.args) != 1:
        return None
    if len(pp1.args) != 2 or len(pp2.args) != 2:
        return None
    verb_name = camel_name(_leaf_words(verb_vp))
    pp1_name = camel_name(_leaf_words(pp1.args[1]))
    pp2_name = camel_name(_leaf_words(pp2.args[1]))
    return verb_name, pp1_name, pp2_name


def _try_translate_gapped_travel_fact(subject, vp):
    """Recognizes a full "X goes/went to CITY by VEHICLE" sentence
    (fracas_150-153's own shared gapping pattern), subject either a
    named individual (150-152's own "John"/"Bill") or a definite plural
    (153's own "the students", this project's usual distributive-
    universal convention for definite plurals, with a TRIVIAL
    restrictor over the whole domain - the same `fun _ => True` device
    id 124's own cardinal-anaphora case already established, since
    "the students" here names the WHOLE domain, not a named subset of
    a larger one). Returns None on shape mismatch, else (is_universal,
    subject_name_or_restrictor, verb_name, pp1_name, pp2_name)."""
    result = _try_translate_double_pp_verb(vp)
    if result is None:
        return None
    verb_name, pp1_name, pp2_name = result
    if subject.head == "UsePN":
        return False, camel_name(_leaf_words(subject)), verb_name, pp1_name, pp2_name
    if subject.head == "DetCN" and len(subject.args) == 2:
        det, cn = subject.args
        if (
            det.head == "DetQuant"
            and len(det.args) == 2
            and det.args[0].head == "DefArt"
            and det.args[1].head == "NumPl"
        ):
            return True, camel_name(_leaf_words(cn)), verb_name, pp1_name, pp2_name
    return None


def _try_translate_existential_universal_object(subject, vp):
    """Recognizes "one N1 V2s all the N2s" (fracas_196's own premise 2/
    hypothesis shape, "one lawyer signed all the reports") - a
    cardinal-one subject taking EXISTENTIAL scope over an inner
    universal, the wide-scope "so did" reading ("there is a single N1
    who V2s every N2"), as opposed to `translate_cl`'s own general path
    for this tree shape, which instead produces a cardinal-quantified
    `Exactly 1` GQ statement fusing the whole VP into one unary
    predicate - confirmed by direct comparison, not assumed, the wrong
    reading for this id. Returns None on shape mismatch, else
    (subject_cn_name, verb_name, object_cn_name)."""
    if subject.head != "DetCN" or len(subject.args) != 2:
        return None
    det, cn = subject.args
    if (
        det.head != "DetQuant"
        or len(det.args) != 2
        or det.args[0].head != "IndefArt"
        or det.args[1].head != "NumCard"
        or len(det.args[1].args) != 1
    ):
        return None
    count, approx = _decode_card(det.args[1].args[0])
    if count != 1 or approx is not None:
        return None
    if (
        vp.head != "ComplSlash"
        or len(vp.args) != 2
        or vp.args[0].head != "SlashV2a"
        or len(vp.args[0].args) != 1
    ):
        return None
    obj = vp.args[1]
    if obj.head != "PredetNP" or len(obj.args) != 2 or obj.args[0].head != "all_Predet":
        return None
    obj_np = obj.args[1]
    if obj_np.head != "DetCN" or len(obj_np.args) != 2:
        return None
    obj_det, obj_cn = obj_np.args
    if (
        obj_det.head != "DetQuant"
        or len(obj_det.args) != 2
        or obj_det.args[0].head != "DefArt"
        or obj_det.args[1].head != "NumPl"
    ):
        return None
    subject_cn_name = camel_name(_leaf_words(cn))
    verb_name = camel_name(_leaf_words(vp.args[0]))
    object_cn_name = camel_name(_leaf_words(obj_cn))
    return subject_cn_name, verb_name, object_cn_name


def translate_cl(t) -> Translation:
    t = _unwrap_tense(t)
    if t.head == "ExistNP" and len(t.args) == 1:
        return _translate_existential(t.args[0])
    if t.head != "PredVP" or len(t.args) != 2:
        raise NotImplementedError(
            f"only 'PredVP (DetCN det cn) vp' is handled so far, got head={t.head!r}"
        )
    subject, vp = t.args

    sentential_complement = _try_translate_sentential_complement(subject, vp)
    if sentential_complement is not None:
        return sentential_complement

    reflexive = _try_translate_reflexive_indefinite_subject(subject, vp)
    if reflexive is not None:
        return reflexive

    reflexive_named = _try_translate_reflexive_named_subject(subject, vp)
    if reflexive_named is not None:
        return reflexive_named

    inverted = _try_translate_partitive_identity(subject, vp)
    if inverted is not None:
        return inverted

    # Checked BEFORE _try_translate_named_individual_fact: that function's
    # own fallback (any "ProperNoun VP" fuses the whole VP, object
    # included, into one unary predicate) would otherwise shadow this
    # MORE SPECIFIC possessive-pronoun-object shape first, silently
    # giving the wrong (fused-unary) structure instead of the bundle.
    possessive_bundle = _try_translate_possessive_presupposition(subject, vp)
    if possessive_bundle is not None:
        return possessive_bundle

    # Same reasoning, for a QUANTIFIED subject with this same possessive-
    # pronoun-object shape ("every/no student used her workstation") -
    # checked before the general `_resolve_subject` path, which would
    # otherwise fuse the whole VP (object included) into one unary scope
    # predicate, same wrong shape the unbound case guards against above.
    bound_bundle = _try_translate_bound_possessive_presupposition(subject, vp)
    if bound_bundle is not None:
        return bound_bundle

    named_fact = _try_translate_named_individual_fact(subject, vp)
    if named_fact is not None:
        return named_fact

    conj_subject = _try_translate_conjnp_subject(subject, vp)
    if conj_subject is not None:
        return conj_subject

    quant, cn = _resolve_subject(subject)
    cn = _normalize_cn(cn)

    quant, cn, vp = _readings.clause(quant, cn, vp)

    restrictor_expr, restrictor_preds = _restrictor_expr(cn)
    scope_name = _scope_name(vp)

    return Translation(
        lean_prop=_readings.quantified(quant, restrictor_expr, scope_name),
        free_predicates=[*restrictor_preds, scope_name],
    )


def render_lean(translation: Translation, *, domain: str = "A") -> str:
    preds = " ".join(translation.free_predicates)
    lines = [f"variable {{{domain} : Type*}} ({preds} : {domain} → Prop)"]
    for individual in translation.free_individuals:
        lines.append(f"variable ({individual} : {domain})")
    lines.append("")
    lines.append(f"example : Prop := {translation.lean_prop}")
    return "\n".join(lines)


def translate_tree_text(text: str, *, domain: str = "A") -> str:
    return render_lean(translate_cl(parse_tree(text)), domain=domain)


if __name__ == "__main__":
    # All five are confirmed end-to-end via `linearize` on the real
    # toolchain (gf/FraCaSLogicEng.gf / gf/NOTES.md). fracas_033 is also
    # the first VP shape this translator has been fed that isn't
    # copula/control-verb: the ComplSlash/SlashV2a tree's object NP
    # flattens into the scope predicate's name exactly like every other
    # VP-internal structure does, so no new code path was needed here,
    # just the IndefArt quantifier mapping above.
    examples = {
        "fracas_002 (premise)": (
            "PredVP (DetCN every_Det (AdjCN (PositA italian_A) (UseN man_N))) "
            "(ComplVV want_VV (UseComp (CompCN (AdjCN (PositA great_A) (UseN tenor_N)))))"
        ),
        "fracas_007 (premise)": (
            "PredVP (DetCN somePl_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
            "(UseComp (CompAP (PositA swedish_A)))"
        ),
        "fracas_006 (premise)": (
            "PredVP (DetCN (DetQuant no_Quant NumPl) "
            "(AdjCN (AdAP really_AdA (PositA great_A)) (UseN tenor_N))) "
            "(UseComp (CompAP (PositA modest_A)))"
        ),
        "fracas_010 (premise)": (
            "PredVP (DetCN most_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
            "(UseComp (CompAP (PositA italian_A)))"
        ),
        "fracas_033 (premise)": (
            "PredVP (DetCN (DetQuant IndefArt NumSg) (UseN irishman_N)) "
            "(ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))"
        ),
        "fracas_003 (premise)": (
            "PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) "
            "(AdjCN (PositA italian_A) (UseN man_N)))) "
            "(ComplVV want_VV (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) "
            "(AdjCN (PositA great_A) (UseN tenor_N))))))"
        ),
        "fracas_004 (premise 1)": (
            "PredVP (DetCN each_Det (AdjCN (PositA italian_A) (UseN tenor_N))) "
            "(ComplVV want_VV (UseComp (CompAP (PositA great_A))))"
        ),
        "fracas_008 (premise)": (
            "PredVP (DetCN many_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
            "(UseComp (CompAP (PositA german_A)))"
        ),
        "fracas_009 (premise)": (
            "PredVP (DetCN several_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
            "(UseComp (CompAP (PositA british_A)))"
        ),
        "fracas_015 (premise)": (
            "PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN "
            "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (UseN tenor_N)) "
            "(ComplSlash (SlashV2a take_V2) (AdvNP (MassNP (UseN part_N)) "
            "(PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN concert_N)))))"
        ),
        "fracas_016 (premise)": (
            "PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_most_AdN "
            "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2))))))))) (UseN tenor_N)) "
            "(AdvVP (ComplSlash (SlashV2a contribute_V2) (DetCN (DetQuant (PossPron they_Pron) NumPl) (UseN fee_N))) "
            "(PrepNP to_Prep (MassNP (UseN charity_N))))"
        ),
        "fracas_014 (premise 1)": (
            "PredVP (DetCN neither_Det (AdjCN (PositA leading_A) (UseN tenor_N))) "
            "(AdvVP (UseV come_V) cheap_Adv)"
        ),
        "fracas_014 (premise 2)": (
            "PredVP "
            "(CountNP (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) "
            "(DetCN (DetQuant DefArt NumPl) (AdjCN (PositA leading_A) (UseN tenor_N)))) "
            "(UseComp (CompNP (UsePN pavarotti_PN)))"
        ),
        "fracas_013 (premise 2)": (
            "PredVP (DetCN (DetQuant IndefArt NumPl) "
            "(RelCN (AdjCN (PositA leading_A) (UseN tenor_N)) "
            "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAP (PositA excellent_A))))))) "
            "(UseComp (CompAP (PositA indispensable_A)))"
        ),
        "fracas_021 (premise 1)": (
            "PredVP "
            "(AdvNP (DetCN (DetQuant DefArt NumPl) (UseN resident_N)) "
            "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN member_N) (UseN state_N))))) "
            "(ComplSlash (SlashV2a have_V2) (DetCN (DetQuant DefArt NumSg) "
            "(AdvCN (SentCN (UseN right_N) (EmbedVP (UseV live_V))) (PrepNP in_Prep (UsePN europe_PN)))))"
        ),
        "fracas_018 (premise 1)": (
            "PredVP (DetCN every_Det (UseN european_N)) "
            "(ComplSlash (SlashV2a have_V2) (DetCN (DetQuant DefArt NumSg) "
            "(AdvCN (SentCN (UseN right_N) (EmbedVP (UseV live_V))) (PrepNP in_Prep (UsePN europe_PN)))))"
        ),
        "fracas_018 (premise 2)": (
            "PredVP (DetCN every_Det (UseN european_N)) (UseComp (CompCN (UseN person_N)))"
        ),
        "fracas_018 (premise 3)": (
            "PredVP (DetCN every_Det (RelCN (UseN person_N) "
            "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP "
            "(ComplSlash (SlashV2a have_V2) (DetCN (DetQuant DefArt NumSg) "
            "(AdvCN (SentCN (UseN right_N) (EmbedVP (UseV live_V))) (PrepNP in_Prep (UsePN europe_PN))))))))) "
            "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) "
            "(PrepNP within_Prep (UsePN europe_PN))))"
        ),
        "fracas_021 (premise 2)": (
            "PredVP (PredetNP all_Predet (AdvNP (DetCN (DetQuant IndefArt NumPl) (UseN resident_N)) "
            "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN member_N) (UseN state_N)))))) "
            "(UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (UseN individual_N))))"
        ),
        "fracas_021 (premise 3)": (
            "PredVP (DetCN every_Det (RelCN (UseN individual_N) "
            "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP "
            "(ComplSlash (SlashV2a have_V2) (DetCN (DetQuant DefArt NumSg) "
            "(AdvCN (SentCN (UseN right_N) (EmbedVP (UseV live_V))) (PrepNP in_Prep (UsePN europe_PN))))))))) "
            "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) "
            "(PrepNP within_Prep (UsePN europe_PN))))"
        ),
        "fracas_001 (premise)": (
            "PredVP (DetCN (DetQuant IndefArt NumSg) (UseN italian_N)) "
            "(ComplSlash (SlashV2a become_V2) (DetCN worlds_Det (AdjCN (PositA greatest_A) (UseN tenor_N))))"
        ),
        "fracas_005 (premise)": (
            "PredVP (DetCN (DetQuant DefArt NumPl) (AdjCN (AdAP really_AdA (PositA ambitious_A)) (UseN tenor_N))) "
            "(UseComp (CompAP (PositA italian_A)))"
        ),
        "fracas_011 (premise 1)": (
            "PredVP (DetCN aFew_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
            "(ComplSlash (SlashV2a sing_V2) (MassNP (AdjCN (PositA popular_A) (UseN music_N))))"
        ),
        "fracas_011 (premise 2)": (
            "PredVP (DetCN somePl_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
            "(ComplSlash (SlashV2a like_V2) (MassNP (AdjCN (PositA popular_A) (UseN music_N))))"
        ),
        # fracas_012 ("Few great tenors are poor.") is deliberately NOT
        # here: `few_Det` has no entry in `_QUANTIFIER_BY_DET` at all,
        # and shouldn't get one. Checked against Batch1.lean directly -
        # problem 12 isn't formalized as a named-predicate `Prop` this
        # translator could produce in the first place; it's a
        # countermodel/independence proof over abstract `Bool`-indexed
        # models (`AtMost 2 (fun _ : Bool => True) (fun _ : Bool =>
        # False)`, "few" being genuinely bound-less in the source text -
        # the "2" is the proof author's own arbitrary countermodel
        # parameter, not something derivable from "few" itself). The GF
        # sentence is still confirmed via run_gf_tests.py independently
        # - only the Lean cross-check doesn't apply here.
        "fracas_017 (premise)": (
            "PredVP (DetCN (DetQuant IndefArt NumSg) (UseN irishman_N)) "
            "(ComplSlash (SlashV2a win_V2) (AdvNP (DetCN (DetQuant DefArt NumSg) (UseN nobelPrize_N)) "
            "(PrepNP for_Prep (MassNP (UseN literature_N)))))"
        ),
        # Problems 22/28/30/32 (the four adjunct-dropping-under-negation
        # countermodels, same shape as problem 12) are deliberately NOT
        # here either, for the same reason as fracas_012 above - checked
        # directly against Batch2.lean/Batch3.lean: all four are
        # countermodel/independence proofs over abstract Bool/Fin-indexed
        # models, not named-predicate Props this translator could produce.
        "fracas_023 (premise)": (
            "PredVP (DetCN somePl_Det (UseN delegate_N)) "
            "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN survey_N))) "
            "(PrepNP on_Prep (MassNP (UseN time_N))))"
        ),
        "fracas_024 (premise)": (
            "PredVP (DetCN many_Det (UseN delegate_N)) "
            "(ComplSlash (SlashV2a obtain_V2) (AdvNP (DetCN (DetQuant IndefArt NumPl) "
            "(AdjCN (PositA interesting_A) (UseN result_N))) (PrepNP from_Prep "
            "(DetCN (DetQuant DefArt NumSg) (UseN survey_N)))))"
        ),
        "fracas_025 (premise)": (
            "PredVP (DetCN several_Det (UseN delegate_N)) "
            "(ComplSlash (SlashV2a get_V2) (AdvNP (PPartNP (DetCN (DetQuant DefArt NumPl) (UseN result_N)) publish_V2) "
            "(PrepNP in_Prep (DetCN (DetQuant IndefArt NumPl) "
            "(AdjCN (PositA major_A) (AdjCN (PositA national_A) (UseN newspaper_N)))))))"
        ),
        "fracas_026 (premise 1)": (
            "PredVP (DetCN most_Det (UseN european_N)) "
            "(UseComp (CompAP (AdvAP (PositA resident_A) (PrepNP in_Prep (UsePN europe_PN)))))"
        ),
        "fracas_026 (premise 2)": (
            "PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (UseN european_N))) "
            "(UseComp (CompCN (UseN person_N)))"
        ),
        "fracas_026 (premise 3)": (
            "PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (RelCN (UseN person_N) "
            "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAP "
            "(AdvAP (PositA resident_A) (PrepNP in_Prep (UsePN europe_PN)))))))))) "
            "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) "
            "(PrepNP within_Prep (UsePN europe_PN))))"
        ),
        "fracas_027 (premise 1)": (
            "PredVP (DetCN aFew_Det (CompoundCN (UseN committee_N) (UseN member_N))) "
            "(UseComp (CompAdv (PrepNP from_Prep (UsePN sweden_PN))))"
        ),
        "fracas_027 (premise 2)": (
            "PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) "
            "(CompoundCN (UseN committee_N) (UseN member_N)))) (UseComp (CompCN (UseN person_N)))"
        ),
        "fracas_027 (premise 3)": (
            "PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (RelCN (UseN person_N) "
            "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAdv "
            "(PrepNP from_Prep (UsePN sweden_PN))))))))) "
            "(UseComp (CompAdv (PrepNP from_Prep (UsePN scandinavia_PN))))"
        ),
        "fracas_029 (premise)": (
            "PredVP (DetCN both_Det (UseN commissioner_N)) "
            "(UseComp (CompCN (AdjCN (PositA leading_A) (UseN businessman_N))))"
        ),
        "fracas_031 (premise)": (
            "PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN "
            "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (UseN commissioner_N)) "
            "(AdvVP (ComplSlash (SlashV2a spend_V2) (DetCN aLotOf_Det (UseN time_N))) "
            "(PrepNP at_Prep (MassNP (UseN home_N))))"
        ),
        # Problems 34-37/39-43/45 (Batch3.lean's "converse" subsection)
        # are deliberately NOT here, for the same reason as fracas_012/
        # fracas_022 above: checked directly against Batch3.lean, all of
        # them are countermodel/independence proofs over abstract Bool/
        # Fin-indexed models, not named-predicate Props this translator
        # could produce. Only problems 38 and 44 are real theorems.
        "fracas_038 (premise)": (
            "PredVP (DetCN (DetQuant no_Quant NumSg) (UseN delegate_N)) "
            "(ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N)))"
        ),
        # fracas_044 (all three premises, plus its "there are few..."
        # hypothesis) is deliberately NOT here either, despite being a
        # real theorem (not a countermodel): its own Lean statement is
        # `AtMost n committee southernEurope → ... → AtMost n committee
        # portugal`, generic over *any* `n` - deliberately stronger than
        # FraCaS's own vague "few" needs (see Batch3.lean's own comment
        # on why) - so there is no single Lean quantifier "few_Det"
        # could map to in the first place, the same reason problem 12's
        # own premise isn't here. Premises 2/3 alone (`all_Predet`-headed,
        # unaffected by this) would translate fine in isolation, but
        # leaving premise 1 out would misrepresent the chain as
        # complete when it structurally isn't - all three are confirmed
        # via run_gf_tests.py instead, independent of this translator.
        #
        # Problems 47/50-54/58 (Batch4.lean) are countermodels, same
        # reasoning as above - not here either. 46/48/49/55/56/57/59 are
        # real theorems, added below (46's own premise reuses fracas_030's
        # own hypothesis tree verbatim, and 48's reuses fracas_032's own
        # hypothesis tree - see run_gf_tests.py's own comment on both).
        "fracas_046 (premise)": (
            "PredVP (DetCN neither_Det (UseN commissioner_N)) "
            "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))"
        ),
        "fracas_048 (premise)": (
            "PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_most_AdN "
            "(NumNumeral (num (pot2as3 (pot1as2 pot110))))))) (UseN commissioner_N)) "
            "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))"
        ),
        "fracas_049 (premise 1)": (
            "PredVP (DetCN (DetQuant IndefArt NumSg) (UseN swedeMasc_N)) "
            "(ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))"
        ),
        "fracas_049 (premise 2)": (
            "PredVP (DetCN every_Det (UseN swedeMasc_N)) (UseComp (CompCN (UseN scandinavian_N)))"
        ),
        "fracas_055 (premise)": (
            "PredVP (DetCN somePl_Det (AdjCN (PositA irish_A) (UseN delegate_N))) "
            "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN survey_N))) "
            "(PrepNP on_Prep (MassNP (UseN time_N))))"
        ),
        "fracas_056 (premise)": (
            "PredVP (DetCN many_Det (AdjCN (PositA british_A) (UseN delegate_N))) "
            "(ComplSlash (SlashV2a obtain_V2) (AdvNP (DetCN (DetQuant IndefArt NumPl) "
            "(AdjCN (PositA interesting_A) (UseN result_N))) (PrepNP from_Prep "
            "(DetCN (DetQuant DefArt NumSg) (UseN survey_N)))))"
        ),
        "fracas_057 (premise)": (
            "PredVP (DetCN several_Det (AdjCN (PositA portuguese_A) (UseN delegate_N))) "
            "(ComplSlash (SlashV2a get_V2) (AdvNP (PPartNP (DetCN (DetQuant DefArt NumPl) (UseN result_N)) publish_V2) "
            "(PrepNP in_Prep (DetCN (DetQuant IndefArt NumPl) "
            "(AdjCN (PositA major_A) (AdjCN (PositA national_A) (UseN newspaper_N)))))))"
        ),
        "fracas_059 (premise)": (
            "PredVP (DetCN aFew_Det (AdjCN (PositA female_A) (CompoundCN (UseN committee_N) (UseN member_N)))) "
            "(UseComp (CompAdv (PrepNP from_Prep (UsePN scandinavia_PN))))"
        ),
        # Problems 60-62/64/65/71-75/79 (Batch5.lean) are countermodels,
        # same reasoning as above - not here. Problem 76 is a real
        # theorem (atMost_restrict) but its own stated premise uses
        # few_Det, which still has no Lean quantifier mapping - excluded
        # same as problems 12/44. 63/66-70/77/78/80 are real theorems,
        # added below - all reusing an earlier problem's own tree
        # verbatim except 63 and 69's premise 1 (both genuinely new).
        "fracas_063 (premise)": (
            "PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN "
            "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (AdjCN (PositA female_A) (UseN commissioner_N))) "
            "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))"
        ),
        "fracas_066 (premise 1)": (
            "PredVP (DetCN every_Det (AdvCN (UseN resident_N) (PrepNP of_Prep (DetCN (DetQuant DefArt NumSg) "
            "(AdjCN (PositA northAmerican_A) (UseN continent_N)))))) "
            "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) (PrepNP within_Prep (UsePN europe_PN))))"
        ),
        "fracas_066 (premise 2)": (
            "PredVP (DetCN every_Det (AdjCN (PositA canadian_A) (UseN resident_N))) "
            "(UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdvCN (UseN resident_N) "
            "(PrepNP of_Prep (DetCN (DetQuant DefArt NumSg) (AdjCN (PositA northAmerican_A) (UseN continent_N))))))))"
        ),
        "fracas_067 (premise 1)": (
            "PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (AdvCN (UseN resident_N) "
            "(PrepNP of_Prep (DetCN (DetQuant DefArt NumSg) (AdjCN (PositA northAmerican_A) (UseN continent_N))))))) "
            "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) (PrepNP within_Prep (UsePN europe_PN))))"
        ),
        "fracas_068 (premise 1)": (
            "PredVP (DetCN each_Det (AdvCN (UseN resident_N) (PrepNP of_Prep (DetCN (DetQuant DefArt NumSg) "
            "(AdjCN (PositA northAmerican_A) (UseN continent_N)))))) "
            "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) (PrepNP within_Prep (UsePN europe_PN))))"
        ),
        "fracas_069 (premise 1)": (
            "PredVP (AdvNP (DetCN (DetQuant DefArt NumPl) (UseN resident_N)) "
            "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA western_A) (UseN country_N))))) "
            "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) (PrepNP within_Prep (UsePN europe_PN))))"
        ),
        "fracas_069 (premise 2)": (
            "PredVP (PredetNP all_Predet (AdvNP (DetCN (DetQuant IndefArt NumPl) (UseN resident_N)) "
            "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA major_A) (AdjCN (PositA western_A) (UseN country_N))))))) "
            "(UseComp (CompNP (AdvNP (DetCN (DetQuant IndefArt NumPl) (UseN resident_N)) "
            "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA western_A) (UseN country_N)))))))"
        ),
        "fracas_070 (premise)": (
            "PredVP (DetCN (DetQuant no_Quant NumSg) (UseN delegate_N)) "
            "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))) "
            "(PrepNP on_Prep (MassNP (UseN time_N))))"
        ),
        # CAUTION, not a counterexample to fix: 077's "both" and 078's
        # "neither" are exactly the UNSAFE case `_QUANTIFIER_BY_DET`'s
        # own comment names (the restrictor narrows between premise and
        # hypothesis - "commissioners" to "female commissioners" -
        # unlike 029/046's restrictor-invariant cases) - the `Every`/
        # `No` output these two print below is the WRONG reading
        # (confirmed against `Batch2.lean`'s real `fracas_077`/
        # `fracas_078`, which correctly use `Both`/`Neither` instead),
        # kept here deliberately so the failure mode stays visible
        # rather than quietly dropped, not wired into any `_from_gf`
        # theorem (neither id has one).
        "fracas_077 (premise)": (
            "PredVP (DetCN both_Det (UseN commissioner_N)) "
            "(UseComp (CompAdv (PrepNP in_Prep (MassNP (UseN business_N)))))"
        ),
        "fracas_078 (premise)": (
            "PredVP (DetCN neither_Det (UseN commissioner_N)) "
            "(AdvVP (ComplSlash (SlashV2a spend_V2) (DetCN aLotOf_Det (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))"
        ),
        "fracas_080 (premise)": (
            "PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_most_AdN "
            "(NumNumeral (num (pot2as3 (pot1as2 pot110))))))) (UseN commissioner_N)) "
            "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))"
        ),
        # FraCaS Section 2 (Plurals), problems 81-97 (Section2/Batch1.lean).
        # Most of this bucket is deliberately NOT here: 81/82/83/85/86
        # need a ConjNP-of-named-individuals subject translated into a
        # conjunction of atomic named Props (`smithSigned ∧ jonesSigned
        # ∧ ...`), and 85/86 also need Section2.Plurals' own `Exactly`
        # quantifier - both genuinely new translate.py architecture this
        # pass doesn't build (this translator's whole design is
        # "one quantified Cl -> one GQ.lean Prop"; a bare conjunction of
        # named individuals is a different shape entirely, out of scope
        # here the same way the "there are few..." existential was in
        # Section 1). 84/91/94/95 are countermodels/independence proofs
        # (checked directly against Batch1.lean), not translatable
        # either way. 87 is a real theorem but its premise is itself a
        # conjunction of two separate `Every` facts, not one clause -
        # same "not this translator's shape" reason as 81/82/83.
        # 89/90/92/96/97 are real theorems this translator DOES reach,
        # added below. 88 itself is NOT among them despite looking like
        # 89's own mirror-image: checked directly against Batch1.lean,
        # fracas_088 is actually a countermodel (dir1/dir2, `.unknown`)
        # over Bool-indexed stand-ins, not a named-predicate Prop -
        # the "every representative and client" premise, on this
        # narrow-scope reading, genuinely doesn't license "every
        # representative" (a rep who isn't also a client breaks it),
        # unlike 89's wide-scope "representative or client" premise,
        # which does. Its own GF sentence is still confirmed via
        # run_gf_tests.py independently.
        "fracas_089 (premise)": (
            "PredVP (DetCN every_Det (ConjCN or_Conj (BaseCN (UseN representativeMasc_N) (UseN client_N)))) "
            "(UseComp (CompAdv (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))"
        ),
        "fracas_090 (premise)": (
            "PredVP (DetCN (DetQuant DefArt NumSg) (UseN chairman_N)) "
            "(ComplSlash (SlashV2a read_out_V2) (DetCN (DetQuant DefArt NumPl) "
            "(AdvCN (UseN item_N) (PrepNP on_Prep (DetCN (DetQuant DefArt NumSg) (UseN agenda_N))))))"
        ),
        "fracas_092 (premise)": (
            "PredVP (PredetNP all_Predet (DetCN (DetQuant DefArt NumPl) (RelCN (UseN person_N) "
            "(UseRCl (TTAnt TPast ASimul) PPos (RelVP IdRP (UseComp (CompAdv "
            "(PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))))))) "
            "(AdvVP (UseV vote_V) (PrepNP for_Prep (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN chairman_N)))))"
        ),
        "fracas_096 (premise)": (
            "PredVP (PredetNP all_Predet (DetCN (DetQuant DefArt NumPl) (AdjCN (PositA ancient_A) (UseN greek_N)))) "
            "(UseComp (CompCN (AdjCN (PositA noted_A) (UseN philosopher_N))))"
        ),
        "fracas_097 (premise)": (
            "PredVP (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN software_N) (UseN fault_N))) "
            "(AdvVP (PassV2 blame_V2) (PrepNP for_Prep (DetCN (DetQuant DefArt NumSg) (CompoundCN (UseN system_N) (UseN failure_N)))))"
        ),
        # FraCaS Section 2 Batch2 (problems 98-113, Section2/Batch2.lean).
        # 99 and 103 are both "Every RESTRICTOR SCOPE" premises
        # instantiated at a named individual - the exact shape
        # _try_translate_named_individual_fact above was added for.
        # Everything else in this bucket is deliberately NOT here: 98 is
        # a countermodel; 100/101/102 are the bare-plural/generic
        # quasi-universal ambiguity translate_cl already can't resolve
        # from syntax alone (same reason as problem 13's RelCN case,
        # documented in translate_cl's own comment); 104 is a
        # countermodel; 105-110 need Section2.Plurals' own `Exactly`
        # quantifier, not built here (same deferral as 85/86); 111-113
        # are named-individual cumulative/distributive "and" facts, a
        # different shape entirely (same "not this translator's shape"
        # reason as 81-86). Every sentence's own GF tree is still
        # confirmed independently via run_gf_tests.py regardless.
        "fracas_099 (premise1)": (
            "PredVP (PredetNP all_Predet (AdvNP (DetCN (DetQuant IndefArt NumPl) (UseN client_N)) "
            "(PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN demonstration_N))))) "
            "(AdvVP (PassV2 impress_V2) (PrepNP by8means_Prep (DetCN (DetQuant "
            "(GenNP (DetCN (DetQuant DefArt NumSg) (UseN system_N))) NumSg) (UseN performance_N))))"
        ),
        "fracas_099 (premise2)": (
            "PredVP (UsePN smith_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) "
            "(AdvCN (UseN client_N) (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN demonstration_N)))))))"
        ),
        "fracas_099 (hypothesis)": (
            "PredVP (UsePN smith_PN) (AdvVP (PassV2 impress_V2) (PrepNP by8means_Prep "
            "(DetCN (DetQuant (GenNP (DetCN (DetQuant DefArt NumSg) (UseN system_N))) NumSg) (UseN performance_N))))"
        ),
        "fracas_103 (premise1)": (
            "PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (UseN apcomManager_N))) "
            "(ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN company_N) (UseN car_N))))"
        ),
        "fracas_103 (premise2)": (
            "PredVP (UsePN jones_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN apcomManager_N))))"
        ),
        "fracas_103 (hypothesis)": (
            "PredVP (UsePN jones_PN) (ComplSlash (SlashV2a have_V2) "
            "(DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN company_N) (UseN car_N))))"
        ),
        # FraCaS Section 3 (Anaphora), problems 114-141: deliberately
        # NOT added here, none of it. Anaphora.lean's own header explains
        # why this section doesn't build general anaphora-resolution
        # machinery in Lean - each pronoun is resolved by hand, per
        # problem, into presupposition bundles, Skolem functions, or
        # shared bound variables across sentences - and none of those
        # shapes is "one quantified Cl" the way this translator's whole
        # architecture (_resolve_subject/_restrictor_expr/_scope_name)
        # expects. Every sentence in this section still gets a real,
        # independently-confirmed GF tree (see run_gf_tests.py's own
        # comment on this section for the full per-problem breakdown).
        #
        # FraCaS Section 4 (Ellipsis), problems 142-196: also
        # deliberately NOT added here, for the same reason - Ellipsis.lean's
        # own header explains this section builds the RESOLVED,
        # non-elliptical reading of each sentence by hand rather than
        # modeling ellipsis itself, the same "resolved bundled fact, not
        # one quantified Cl" shape as Section 3's anaphora. Every
        # sentence still gets a real GF tree (see run_gf_tests.py's own
        # comment on this section).
        #
        # FraCaS Section 5 (Adjectives), problems 197-219: also
        # deliberately NOT added, despite most of its sentences being
        # simple enough to fit translate_cl's existing shapes (a named-
        # individual copula fact or an "Every CN1 CN2" universal) - the
        # reason is different from Sections 3/4's own: this section's
        # whole point is PER-ADJECTIVE entailment behavior (intersective
        # "genuine diamond" licenses noun/adjective-drop; privative
        # "former student" doesn't; subsective "small"/"large" are
        # contrary; comparison classes are extensional or intensional),
        # and _restrictor_expr/_scope_name's own generic CN/VP-fusion
        # would collapse exactly that distinction into one opaque
        # predicate name ("genuineDiamond") - silently discarding the
        # very thing each problem is testing, not just translating it
        # coarser. Every sentence still gets a real GF tree (see
        # run_gf_tests.py's own comment on this section).
        #
        # FraCaS Section 6 (Comparatives), problems 220-250: also
        # deliberately NOT added, same reason as Section 5 - this
        # section's whole point is the ASSUMED comparative relation
        # between two gradable adjectives ("faster than" licensing
        # "fast" via an explicit assumed fact) or real Nat arithmetic
        # between named counts, and translate_cl's own generic CN/VP-
        # fusion would collapse either into one opaque predicate name,
        # translating the sentence but losing the very relation each
        # problem is about. Every sentence still gets a real GF tree
        # (see run_gf_tests.py's own comment on this section).
        #
        # FraCaS Section 7 (Temporal Reference), problems 251-325: also
        # deliberately NOT added - the strongest case yet for skipping,
        # since this section's own Lean formalization is ALREADY almost
        # entirely abstract (bare `Nat`/`Prop` variables, never
        # accumulating named concrete predicates the way Sections 1-6
        # do), so there is no real Lean-side content translate_cl's
        # generic fusion could even usefully cross-check against here.
        # Every buildable sentence still gets a real GF tree (a
        # representative sample, not one per Lean theorem - see
        # run_gf_tests.py's own comment on this section for why).
        #
        # FraCaS Section 8 (Verbs), problems 326-333: also deliberately
        # NOT added, same "assumed connecting fact" reasoning as
        # Sections 5-7 (the imperfective-paradox and interval-
        # containment content here isn't captured by generic CN/VP
        # fusion). Every sentence still gets a real GF tree (see
        # run_gf_tests.py's own comment on this section).
        #
        # FraCaS Section 9 (Attitudes), problems 334-346 - the final
        # FraCaS section. Also deliberately NOT added, same reasoning as
        # Sections 5-8: factivity/implicativity is an assumed connecting
        # fact this translator's generic fusion doesn't represent.
        # Every sentence still gets a real GF tree (see run_gf_tests.py's
        # own comment on this section). This is translate.py's own last
        # word on all nine FraCaS sections.
    }
    for label, tree_text in examples.items():
        print(f"-- {label}")
        print(f"-- {tree_text}")
        print(translate_tree_text(tree_text))
        print()
