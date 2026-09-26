#!/usr/bin/env python3
"""Translate a GF abstract syntax tree (as printed by the `gf` shell's
own tree notation - see gf/NOTES.md) into a Lean proposition using this
project's FraCaS.Section1.GQ vocabulary (Every/Some/No/Most).

This is deliberately narrow: it only handles the one sentence shape
proven end-to-end in gf/FraCaSLogic.gf / gf/NOTES.md so far -
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

Extending this to more sentence shapes (negation, relative clauses,
comparatives, ...) is expected to mean adding more cases to
`translate_cl`, not redesigning the tree parser or the naming scheme.
"""

from __future__ import annotations

from dataclasses import dataclass


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
_LEXICAL_SUFFIXES = ("_A", "_N", "_V2", "_VV", "_V", "_AdA")


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
    "someSg_Det": "Some",
    "somePl_Det": "Some",
    "most_Det": "Most",
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


def _resolve_quantifier(det) -> str:
    if det.head in _QUANTIFIER_BY_DET and not det.args:
        return _QUANTIFIER_BY_DET[det.head]
    if det.head == "DetQuant" and len(det.args) == 2:
        quant, _num = det.args
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


@dataclass
class Translation:
    """One sentence's translation: the Lean Prop it denotes, plus the
    free predicates (name -> arity-1 predicate over the domain) it
    needs declared as `variable`s before that Prop typechecks."""

    lean_prop: str
    free_predicates: list  # list[str], in the order first referenced


def translate_cl(t) -> Translation:
    if t.head != "PredVP" or len(t.args) != 2:
        raise NotImplementedError(
            f"only 'PredVP (DetCN det cn) vp' is handled so far, got head={t.head!r}"
        )
    subject, vp = t.args
    quant, cn = _resolve_subject(subject)

    restrictor_name = camel_name(_leaf_words(cn))
    scope_name = camel_name(_leaf_words(vp))

    return Translation(
        lean_prop=f"{quant} {restrictor_name} {scope_name}",
        free_predicates=[restrictor_name, scope_name],
    )


def render_lean(translation: Translation, *, domain: str = "A") -> str:
    preds = " ".join(translation.free_predicates)
    return (
        f"variable {{{domain} : Type*}} ({preds} : {domain} → Prop)\n\n"
        f"example : Prop := {translation.lean_prop}"
    )


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
            "(ComplVV want_VV (UseComp (CompCN (AdjCN (PositA great_A) (UseN tenor_N)))))"
        ),
        "fracas_004 (premise 1)": (
            "PredVP (DetCN each_Det (AdjCN (PositA italian_A) (UseN tenor_N))) "
            "(ComplVV want_VV (UseComp (CompAP (PositA great_A))))"
        ),
    }
    for label, tree_text in examples.items():
        print(f"-- {label}")
        print(f"-- {tree_text}")
        print(translate_tree_text(tree_text))
        print()
