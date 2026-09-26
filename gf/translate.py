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


Tree = "str | App"


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
# one place that distinction actually matters.
_LEXICAL_SUFFIXES = ("_A", "_N", "_V2", "_VV", "_V", "_AdA", "_PN")


def _is_leaf_lexical(name: str) -> bool:
    return any(name.endswith(suf) for suf in _LEXICAL_SUFFIXES)


def _leaf_words(t) -> list[str]:
    if not t.args:
        if _is_leaf_lexical(t.head):
            for suf in _LEXICAL_SUFFIXES:
                if t.head.endswith(suf):
                    return [t.head[: -len(suf)]]
        return []
    words = []
    for a in t.args:
        words.extend(_leaf_words(a))
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
    "both_Det": "Every",  # "both" treated as "every" restricted to two - GQ.lean
    "someSg_Det": "Some",
    "somePl_Det": "Some",
    "many_Det": "Some",
    "several_Det": "Some",
    "aFew_Det": "Some",
    "most_Det": "Most",
    "neither_Det": "No",  # "neither" treated as "no" restricted to two - GQ.lean
}

# Determiners that are Quant-typed instead (no_Quant, this_Quant, ...):
# DetCN's first argument is then `DetQuant <quant> <num>` (mkDet's own
# bare-Quant desugaring, gf-rgl's Constructors.gf), not a bare *_Det.
# IndefArt ("a"/"an") is treated as existential, matching how this
# project's own Lean `Some` already covers "a/an/some/many/..." (see
# LeanNLSemantics/FraCaS/Section1/GQ.lean's doc comment on `Some`).
_QUANTIFIER_BY_QUANT = {
    "no_Quant": "No",
    "IndefArt": "Some",
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
    raise NotImplementedError(f"unrecognized Sub100 numeral shape: {t.head!r}")


def _decode_sub1000(t) -> int:
    if t.head == "pot1as2" and len(t.args) == 1:
        return _decode_sub100(t.args[0])
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
    'AtLeast'/'AtMost' when the Card is `AdNum`-wrapped ("at least
    three"/"at most two"), or None for a bare exact count ("one")."""
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


def _resolve_quantifier(det) -> str:
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


def _resolve_subject(subject):
    """Returns (quantifier, restrictor_cn_tree) for a Cl's subject NP,
    handling both `DetCN det cn` and `PredetNP predet (DetCN _ cn)`."""
    if subject.head == "DetCN" and len(subject.args) == 2:
        det, cn = subject.args
        return _resolve_quantifier(det), cn
    if subject.head == "PredetNP" and len(subject.args) == 2:
        predet, np = subject.args
        if predet.head not in _QUANTIFIER_BY_PREDET:
            raise NotImplementedError(
                f"predeterminer {predet.head!r} has no known Lean mapping yet "
                "(see _QUANTIFIER_BY_PREDET)"
            )
        if np.head != "DetCN" or len(np.args) != 2:
            raise NotImplementedError(
                "PredetNP's own NP is only handled as a bare DetCN so far, "
                f"got head={np.head!r}"
            )
        _det, cn = np.args
        return _QUANTIFIER_BY_PREDET[predet.head], cn
    raise NotImplementedError(
        "only a determiner-quantified subject (DetCN det cn) or a "
        "predeterminer-quantified one (PredetNP predet (DetCN _ cn)) is "
        f"handled so far, got subject head={subject.head!r}"
    )


def _scope_name(vp) -> str:
    """Most VPs name their scope predicate from all of their own lexical
    content (matching e.g. `wantsGreatTenor`). "comes cheap" (`AdvVP
    (UseV come_V) (PositAdvAdj cheap_A)`) is a linking-verb idiom where
    "come" contributes no separate meaning of its own - the existing
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
        return camel_name(_leaf_words(vp.args[1]))
    return camel_name(_leaf_words(vp))


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


def translate_cl(t) -> Translation:
    if t.head != "PredVP" or len(t.args) != 2:
        raise NotImplementedError(
            f"only 'PredVP (DetCN det cn) vp' is handled so far, got head={t.head!r}"
        )
    subject, vp = t.args

    inverted = _try_translate_partitive_identity(subject, vp)
    if inverted is not None:
        return inverted

    quant, cn = _resolve_subject(subject)

    restrictor_name = camel_name(_leaf_words(cn))
    scope_name = _scope_name(vp)

    return Translation(
        lean_prop=f"{quant} {restrictor_name} {scope_name}",
        free_predicates=[restrictor_name, scope_name],
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
    # copula/control-verb: the ComplV2 tree's object NP flattens into
    # the scope predicate's name exactly like every other VP-internal
    # structure does, so no new code path was needed here, just the
    # IndefArt quantifier mapping above.
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
            "(ComplV2 win_V2 (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))"
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
            "(AdvVP (UseV come_V) (PositAdvAdj cheap_A))"
        ),
        "fracas_014 (premise 2)": (
            "PredVP "
            "(CountNP (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) "
            "(DetCN (DetQuant DefArt NumPl) (AdjCN (PositA leading_A) (UseN tenor_N)))) "
            "(UseComp (CompNP (UsePN pavarotti_PN)))"
        ),
    }
    for label, tree_text in examples.items():
        print(f"-- {label}")
        print(f"-- {tree_text}")
        print(translate_tree_text(tree_text))
        print()
