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
_LEXICAL_SUFFIXES = ("_A", "_N", "_V2", "_VV", "_V", "_AdA", "_PN", "_Adv")


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
            # A bare counted numeral with no AdNum wrapper at all ("six
            # lawyers", not "at least"/"at most"/"exactly six") is this
            # project's own "Exactly" reading, not "Some" - confirmed by
            # fracas_085/086's own real theorems (`Exactly 6 lawyer
            # signed`/`Exactly 6 accountant signed`, for the gold
            # hypotheses "Six lawyers/accountants signed the contract"),
            # not guessed from the English alone.
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
        if predet.head == "only_Predet":
            # Unlike every other predeterminer here, "only" is NOT
            # semantically vacuous - the wrapped NP's own numeral
            # determiner carries the real count ("only one accountant" =
            # "exactly one accountant", FraCaS 105-110's shared premise),
            # so it's read off via the normal numeral-decoding path
            # (_resolve_quantifier) instead of being discarded the way
            # all_Predet's own vacuous `DetQuant IndefArt NumPl` wrapper
            # is. Confirmed directly against Batch2.lean: 105-110 are all
            # stated as `Exactly 1 accountant attended`, never a bare
            # existential.
            det, cn = _det_and_restrictor(np)
            quant = _resolve_quantifier(det)
            if not quant.startswith("Exactly"):
                raise NotImplementedError(
                    f"'only_Predet' wrapping determiner {det.head!r} (quantifier "
                    f"{quant!r}) isn't a known exact count - only a bare counted "
                    "numeral under only_Predet is handled so far"
                )
            return quant, cn
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
        return camel_name(_leaf_words(vp.args[1]))
    return camel_name(_leaf_words(vp))


# FraCaS Section 5's own adjectives whose entailment behavior this
# translator represents by SPLITTING an `AdjCN` into two conjoined
# predicates rather than fusing it into one opaque name - the real
# Lean theorems these feed (fracas_202/fracas_214) are stated directly
# over the split conjunction (`mammal x ∧ fourLegged x`), not a fused
# `fourLeggedMammal`, so faithfully matching them means not fusing here
# either. Each entry is an independent, citable fact about the WORD,
# not reverse-engineered from either problem's own proof:
# "four-legged" is a textbook INTERSECTIVE adjective (a four-legged
# mammal is exactly something that is both four-legged and a mammal);
# "fat" is SUBSECTIVE but, per FraCaS's own problem 214 (and the
# extensional/intensional subsective split this project's `Adjectives.lean`
# documents, the same fat/competent contrast as Barbara Partee's own
# running example in the literature), EXTENSIONAL - it doesn't matter
# which coextensive description names the comparison class, so it
# still distributes across a noun bi-implication the same way an
# intersective adjective does. Deliberately NOT every adjective this
# project's grammar has: an intensional subsective adjective like
# "competent" (fracas_215, FraCaS's own contrasting case) must NOT be
# added here - its entailment does NOT distribute this way, confirmed
# directly by fracas_215 being a countermodel/independence pair, not a
# real theorem with this shape at all.
_SPLITTING_ADJECTIVES = {"fourLegged_A", "fat_A"}

# Comparison-class-relative ("subsective") adjectives that are CONTRARY
# pairs - "small"/"large" (fracas_204/205/208/209's own shared vocabulary)
# - an independent, citable fact about these two specific WORDS (not
# reverse-engineered from either problem's own proof): being small
# entails not being large and vice versa, but "not small" doesn't give
# "large" (a genuine middle ground, e.g. medium-sized) - the same
# contrary-not-contradictory distinction `Adjectives.lean`'s own header
# documents. Only used by `_try_translate_named_individual_fact`'s own
# bare-copula-predication case, never by `_restrictor_expr` - see that
# case's own comment for why the same two words need the OPPOSITE
# (fused, not dropped) treatment in a subclass/superclass-shift context
# (fracas_210/211/212).
_CONTRARY_ADJECTIVES = {"small_A", "large_A"}


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
    if (
        cn.head == "AdjCN"
        and len(cn.args) == 2
        and cn.args[0].head == "PositA"
        and len(cn.args[0].args) == 1
        and cn.args[0].args[0].head in _SPLITTING_ADJECTIVES
    ):
        adj_name = camel_name(_leaf_words(cn.args[0]))
        base_name = camel_name(_leaf_words(cn.args[1]))
        # Noun-then-adjective, matching fracas_202's/fracas_214's own
        # stated conjunction order directly (`mammal x ∧ fourLegged x`,
        # `legalAuth x ∧ fat x`) - not a fixed universal convention (this
        # project's own fracas_203 states the OPPOSITE order for its
        # single conjunction, `fourLegged dumbo ∧ animal dumbo`, which is
        # why 203 stays on its own hand-built CUSTOM_BUILD path instead
        # of this generic one: `∧` isn't definitionally commutative, so
        # a single fixed order here can't match every real theorem).
        return f"(fun x => {base_name} x ∧ {adj_name} x)", [base_name, adj_name]
    if (
        cn.head == "RelCN"
        and len(cn.args) == 2
        and cn.args[1].head == "UseRCl"
        and len(cn.args[1].args) == 3
        and cn.args[1].args[2].head == "RelVP"
        and len(cn.args[1].args[2].args) == 2
        and cn.args[1].args[2].args[0].head == "IdRP"
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


def _scope_expr(vp):
    """Returns (expr, free_predicates) for a Cl's scope VP - mirrors
    `_restrictor_expr`'s own (expr, preds) convention, since a quantified
    sentence's SCOPE can need exactly the same AdjCN-splitting treatment
    its RESTRICTOR already does: "every four-legged mammal is a
    four-legged animal" (fracas_202) splits BOTH the subject's own
    restrictor ("four-legged mammal") and the copula complement's own
    scope ("a four-legged animal") into the same `N x ∧ Adj x`
    conjunction, not one fused name on either side. A copula
    predication over a determiner-quantified CN (`UseComp (CompNP
    (DetCN det cn))`, "is a/an CN") delegates straight to
    `_restrictor_expr(cn)` - safe to share, since for every CN shape
    `_restrictor_expr` doesn't special-case, it already reduces to the
    exact same `camel_name(_leaf_words(cn))` fusion `_scope_name` itself
    uses (confirmed directly: a `DetCN`'s own determiner contributes no
    lexical leaves `_leaf_words` ever collects, so the two converge).
    Every other VP shape keeps `_scope_name`'s own single-fused-name
    behavior unchanged."""
    if (
        vp.head == "UseComp"
        and len(vp.args) == 1
        and vp.args[0].head == "CompNP"
        and len(vp.args[0].args) == 1
        and vp.args[0].args[0].head == "DetCN"
        and len(vp.args[0].args[0].args) == 2
    ):
        cn = vp.args[0].args[0].args[1]
        return _restrictor_expr(cn)
    name = _scope_name(vp)
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
    # A bare comparative predication over a named standard ("Mickey is
    # smaller than Dumbo", fracas_208's/209's own hypothesis) is a
    # genuinely different shape from every other case here: it names a
    # BINARY relation between the subject and the comparison standard,
    # not a unary predicate applied to one individual - "smaller"'s own
    # lexical content becomes `smallerThan`, read directly off ComparA's
    # own adjective argument (general over any comparative, not a
    # fracas_208/209-specific name).
    if (
        vp.head == "UseComp"
        and len(vp.args) == 1
        and vp.args[0].head == "CompAP"
        and len(vp.args[0].args) == 1
        and vp.args[0].args[0].head == "ComparA"
        and len(vp.args[0].args[0].args) == 2
    ):
        adj_tree, standard = vp.args[0].args[0].args
        relation_name = camel_name(_leaf_words(adj_tree)) + "Than"
        if standard.head == "UsePN":
            standard_name = camel_name(_leaf_words(standard))
            return Translation(
                lean_prop=f"{relation_name} {individual_name} {standard_name}",
                free_predicates=[relation_name],
                free_individuals=[individual_name, standard_name],
                binary_predicates=[relation_name],
            )
        # A QUANTIFIED standard ("faster than every/any ITEL computer",
        # fracas_246's/248's own premise) distributes the comparative
        # relation across the restrictor via this project's own usual
        # `Every`/`Some` machinery (`_resolve_quantifier`/
        # `_restrictor_expr`, the same combinators Sections 1-5 already
        # reuse throughout) - `Every itelComputer (fasterThan pc)`, a
        # partially-applied binary relation as `Every`'s own scope
        # predicate, confirmed directly against fracas_246's/248's own
        # stated type (no lambda needed - GQ.lean's `Every P Q` already
        # takes `Q` as a bare `A -> Prop`, and `fasterThan pc` already IS
        # one, point-free). "any" gets the SAME universal reading as
        # "every" here (Comparatives.lean's own approach note: "any" is
        # universal in this construction, not an NPI), so no separate
        # case is needed for it.
        if standard.head == "DetCN" and len(standard.args) == 2:
            det, cn = standard.args
            quant = _resolve_quantifier(det)
            restrictor_expr, restrictor_preds = _restrictor_expr(cn)
            return Translation(
                lean_prop=f"{quant} {restrictor_expr} ({relation_name} {individual_name})",
                free_predicates=[*restrictor_preds, relation_name],
                free_individuals=[individual_name],
                binary_predicates=[relation_name],
            )
        # A conjoined/disjoined standard of NAMED individuals ("faster
        # than the ITEL-ZX and the ITEL-ZY"/"... or the ITEL-ZY",
        # fracas_249's/250's own premise) becomes a CONJUNCTION of the
        # relation applied to each one - confirmed directly against both
        # real theorems' own stated types, which need the identical `∧`
        # conjunction for EITHER connective: FraCaS's own stipulated
        # reading of "or" here is conjunctive ("faster than both"), per
        # Comparatives.lean's own approach note ("on one reading of the
        # premise") - a genuine non-compositional modeling choice this
        # project makes for THIS construction specifically, not a general
        # "or means and" rule, so both `and_Conj`/`or_Conj` map to the
        # same `∧` output rather than only `and_Conj` doing so. Only the
        # two-standard case is handled, the same restriction every other
        # binary conjunction case in this translator already has.
        if (
            standard.head == "ConjNP"
            and len(standard.args) == 2
            and standard.args[0].head in ("and_Conj", "or_Conj")
            and standard.args[1].head == "BaseNP"
            and len(standard.args[1].args) == 2
        ):
            pn1, pn2 = standard.args[1].args
            name1 = camel_name(_leaf_words(pn1))
            name2 = camel_name(_leaf_words(pn2))
            conjunct1 = Translation(
                lean_prop=f"{relation_name} {individual_name} {name1}",
                free_predicates=[relation_name],
                free_individuals=[individual_name, name1],
                binary_predicates=[relation_name],
            )
            conjunct2 = Translation(
                lean_prop=f"{relation_name} {individual_name} {name2}",
                free_predicates=[relation_name],
                free_individuals=[individual_name, name2],
                binary_predicates=[relation_name],
            )
            # Exposes its own two conjuncts via `Translation.conjuncts`
            # (the same mechanism `_try_translate_conjnp_subject` already
            # uses) - fracas_249's/250's own real theorem states this
            # SAME sentence as its one real premise directly (no
            # projection needed there), but their own hypothesis is just
            # its FIRST conjunct alone ("the PC-6082 is faster than the
            # ITEL-ZX") restated - `BUNDLE_PROJECT` in
            # scripts/gen_gf_cross_check.py reuses this conjunct directly
            # rather than this sentence needing its own separately
            # registered (and separately GF-toolchain-confirmed) tree.
            return Translation(
                lean_prop=f"({conjunct1.lean_prop} ∧ {conjunct2.lean_prop})",
                free_predicates=[relation_name],
                free_individuals=[individual_name, name1, name2],
                binary_predicates=[relation_name],
                conjuncts=[conjunct1, conjunct2],
            )
    # "As fast as", the equative counterpart of ComparA's own comparative
    # - FraCaS's own Section 6 reads this as an "at least as", not
    # "exactly as", bound (Comparatives.lean's own header) - same binary-
    # relation treatment as the comparative case above, general over any
    # "as Adj as" construction this grammar can produce, named `{adj}As`
    # rather than `{adj}Than` only to keep the two constructions'
    # auto-generated names visibly distinct (neither name has to match
    # the real theorem's own choice either way).
    if (
        vp.head == "UseComp"
        and len(vp.args) == 1
        and vp.args[0].head == "CompAP"
        and len(vp.args[0].args) == 1
        and vp.args[0].args[0].head == "CAdvAP"
        and len(vp.args[0].args[0].args) == 3
        and vp.args[0].args[0].args[0].head == "as_CAdv"
        and vp.args[0].args[0].args[1].head == "PositA"
        and vp.args[0].args[0].args[2].head == "UsePN"
    ):
        _as_cadv, adj_tree, standard_pn = vp.args[0].args[0].args
        relation_name = camel_name(_leaf_words(adj_tree)) + "As"
        standard_name = camel_name(_leaf_words(standard_pn))
        return Translation(
            lean_prop=f"{relation_name} {individual_name} {standard_name}",
            free_predicates=[relation_name],
            free_individuals=[individual_name, standard_name],
            binary_predicates=[relation_name],
        )
    if (
        vp.head == "UseComp"
        and len(vp.args) == 1
        and vp.args[0].head == "CompNP"
        and len(vp.args[0].args) == 1
        and vp.args[0].args[0].head == "DetCN"
        and len(vp.args[0].args[0].args) == 2
    ):
        cn = vp.args[0].args[0].args[1]
        # A comparison-class-relative ("contrary", not contradictory)
        # gradable adjective predicated bare over a named individual
        # ("Mickey is a small animal", fracas_204's/205's own premise) -
        # unlike `_SPLITTING_ADJECTIVES`' own intersective/extensional-
        # subsective adjectives, this project's own Lean encoding drops
        # the noun ENTIRELY here (`small mickey`, never `smallAnimal
        # mickey`): Adjectives.lean's own header states the comparison
        # class only matters when it's SHIFTING between a subclass and a
        # superclass (fracas_210/211/212's own distinct shape, reached
        # through `_restrictor_expr` instead, which still fuses "small
        # animal" into one name there - deliberately NOT reused here,
        # since the two contexts need opposite treatments of the same
        # word). Confirmed directly against fracas_204/205's own stated
        # types, which never mention "animal" at all.
        if (
            cn.head == "AdjCN"
            and len(cn.args) == 2
            and cn.args[0].head == "PositA"
            and len(cn.args[0].args) == 1
            and cn.args[0].args[0].head in _CONTRARY_ADJECTIVES
        ):
            pred_name = camel_name(_leaf_words(cn.args[0]))
            return Translation(
                lean_prop=f"{pred_name} {individual_name}",
                free_predicates=[pred_name],
                free_individuals=[individual_name],
            )
        pred_expr, preds = _restrictor_expr(cn)
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


def translate_cl(t) -> Translation:
    t = _unwrap_tense(t)
    if t.head != "PredVP" or len(t.args) != 2:
        raise NotImplementedError(
            f"only 'PredVP (DetCN det cn) vp' is handled so far, got head={t.head!r}"
        )
    subject, vp = t.args

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

    # Bare-plural + relative-clause subjects ("leading tenors that are
    # excellent are indispensable", problem 13) are a genuine ambiguity
    # this translator can't resolve from syntax alone: `DetQuant IndefArt
    # NumPl` is GF's own encoding for an article-less bare plural, used
    # both for real existentials ("tenors are singing") and for FraCaS's
    # own "characterizing generic construed as universal" idiom - which
    # is what this specific problem needs (`every_mp`'s own `Every (fun
    # x => leadingTenor x ∧ excellent x) indispensable`, not `Some`).
    # Narrowly overridden here (not a blanket "bare plural = Every" rule,
    # which would be wrong for a genuine existential bare plural) for
    # exactly the shape that's actually confirmed to need it: a
    # RelCN-restricted bare plural.
    if quant == "Some" and cn.head == "RelCN":
        quant = "Every"

    restrictor_expr, restrictor_preds = _restrictor_expr(cn)
    scope_expr, scope_preds = _scope_expr(vp)

    return Translation(
        lean_prop=f"{quant} {restrictor_expr} {scope_expr}",
        free_predicates=[*restrictor_preds, *scope_preds],
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
            "(UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdvCN (UseN resident_N) "
            "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA western_A) (UseN country_N))))))))"
        ),
        "fracas_070 (premise)": (
            "PredVP (DetCN (DetQuant no_Quant NumSg) (UseN delegate_N)) "
            "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))) "
            "(PrepNP on_Prep (MassNP (UseN time_N))))"
        ),
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
        # countermodel; 105/106/107/108/110 ARE now handled generically
        # (see `only_Predet`'s own handling in `_resolve_subject` above -
        # "only one accountant" reads its exact count off the wrapped
        # NP's own numeral, not vacuous the way "all" is); 109 stays
        # excluded even though it shares 107's own premise AND hypothesis
        # text verbatim ("some accountants attended the meeting") - 107
        # and 109 are deliberately given DIFFERENT gold formalizations of
        # the identical sentence (Batch2.lean's own comment on 109), and
        # no single translate_cl output can agree with two divergent
        # readings of the same text; 111-113 are named-individual
        # cumulative/distributive "and" facts, a different shape
        # entirely (same "not this translator's shape" reason as 81-86).
        # Every sentence's own GF tree is still confirmed independently
        # via run_gf_tests.py regardless.
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
