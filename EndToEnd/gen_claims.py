#!/usr/bin/env python3
"""Generate EndToEnd/Claims.lean: FraCaS problems translated into Lean
**automatically, from their original English**, for the end-to-end
evaluation (EndToEnd/Scan.lean).

Every other evaluation in this project scores inference over a
*hand-translated* `Prop`. This one removes the human from the translation
step too, for every problem the pipeline can carry all the way through:

1. **English**: each premise and the hypothesis exactly as FraCaS states
   them (`FraCaS/Data/Problems.lean`), passed through one generic lexer
   step (`EndToEnd/parse_rank.py`'s `tokenize`: final punctuation dropped,
   commas split off, each token looked up in the grammar's vocabulary
   case-insensitively). Never the project's own confirmed rewordings in
   `gf/run_gf_tests.py`.
2. **Parse**: `EndToEnd/parse_rank.py`'s `parse_readings` against the restricted
   FraCaSParse grammar (see `EndToEnd/gen_parse_grammar.py` for what that
   restriction is and isn't), then its generic ranking picks one reading.
3. **Translate**: `gf/translate.py`, under `EndToEnd/readings.py`'s
   readings (`translate_cl_reading`; see "Yes/no claims" below).
4. **Assemble**, by one generic rule with no per-problem cases: bind every
   free predicate/individual the sentences mention universally, over one
   domain `A`, and chain `premise₁ → ... → premiseₙ → hypothesis`.
   Decidability binders are added for each unary predicate (the counting
   quantifiers `Most`/`AtLeast`/... need them). Unlike the hand-written
   theorems, **no background-knowledge premise** a human would add ("an
   Irishman winning the Nobel prize for literature wins a Nobel prize") is
   ever supplied - a problem needing one should come out "unknown", and
   that is reported as the real end-to-end result, not repaired. A
   second claim per problem (`fracas_NNN_bk_*`) adds the problem-
   independent background knowledge `EndToEnd/background.py` derives (tree-
   structural entailments and a small degree-semantics lexicon), and the
   two are scored separately.

**Yes/no claims.** Some English is genuinely ambiguous ("the inhabitants
voted" - distributive or collective; a bare plural with a relative clause
- generic or existential; "many" - cardinal or proportional; "some
accountants" - number-neutral or at least two), and committing to one
reading lets the pipeline give a confident answer FraCaS marks wrong. So
`EndToEnd/readings.py` produces each kind of ambiguity in a "weak" and a
"strong" reading (`translate_cl_reading`), and every problem is translated
under every *consistent* assignment of readings to the kinds of ambiguity
it actually contains - the same word read the same way in each of its
sentences, as a reader would. Each assignment gives a **yes** claim
(premises → hypothesis) and a **no** claim (premises → ¬ hypothesis); the
scan answers "yes"/"no" only when the claim is proved under **every**
assignment, so no such answer depends on picking one reading. Ellipsis
("so did Bill", "Bill didn't") and one-anaphora ("a blue one") are
resolved here (`resolve`) by copying the antecedent clause's VP / noun,
the standard copy treatment; negation is translated only with a proper-
name subject, where its scope is unambiguous.

A problem is skipped, with its reason reported, if any sentence fails to
parse, any top-ranked reading fails to translate, or a translation needs
something the generic rule doesn't assemble (Skolem functions, presupposition
bundles, conjunct projections, a name used at two different kinds).

Needs the `gf` binary and a compiled EndToEnd/FraCaSParse.pgf (the `build-gf` CI
job has both and regenerates this file to check it is reproducible). Do not
hand-edit the output.
"""
from __future__ import annotations

import collections
import itertools
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GF_DIR = ROOT / "gf"
OUT_PATH = ROOT / "EndToEnd" / "Claims.lean"
PROBLEMS = ROOT / "LeanNLSemantics" / "FraCaS" / "Data" / "Problems.lean"

sys.path.insert(0, str(GF_DIR))
sys.path.insert(0, str(ROOT / "EndToEnd"))
from parse_rank import parse_readings, ranked, tokenize  # noqa: E402
from translate import App, _leaf_words, camel_name, parse_tree  # noqa: E402
from readings import AMBIGUITY_KINDS, translate_cl_reading  # noqa: E402
from background import postulates  # noqa: E402

# Identifiers a generated predicate/individual name must not collide with.
LEAN_RESERVED = {
    "at", "by", "do", "else", "end", "fun", "have", "if", "in", "let", "match",
    "open", "show", "then", "from", "with", "where", "for", "this", "calc",
    "suffices", "obtain", "def", "theorem", "x", "A", "Prop", "Type", "Sort",
    # bound by the assembler itself
    "Many", "Few", "fewCount", "aFewCount", "severalCount",
}


def load_problems():
    src = PROBLEMS.read_text()
    out = []
    for m in re.finditer(
        r'\{ id := (\d+), premises := \[(.*?)\],\s*hypothesis := "((?:[^"\\]|\\.)*)", answer := \.(\w+) \}',
        src, re.S,
    ):
        premises = re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(2))
        out.append((int(m.group(1)), premises, m.group(3), m.group(4)))
    return out


def to_clause(t):
    if t.head == "UttS" and len(t.args) == 1:
        t = t.args[0]
    if t.head == "UseCl" and len(t.args) == 3 and t.args[1].head == "PPos":
        return t.args[2]
    return t


_NEGATIVE_POLARITIES = ("PNeg", "UncNeg")

# Time adverbials the grammar lexicalizes as one word ("in 1993", "for two
# years", "from 1988 to 1992", "in July 1994", "on Friday").
_TIME_ADVERB = re.compile(
    r"(in|for|from|since|on|at)[A-Z0-9][A-Za-z0-9]*"
    r"(\d|Year|Hour|Month|Week|Day|OClock|Quarter|day|January|February|March|April|May|June|July|August|"
    r"September|October|November|December)[A-Za-z0-9]*_Adv"
)
# Where a time adverbial is not lifted out of: embedded clauses and the
# complements of verbs taking a clause or a verb phrase, whose own event
# it may modify ("managed to win the contract in 1992").
_TIME_OPAQUE = ("UseCl", "EmbedS", "EmbedVP", "RelCN", "SentCN", "SubjS", "ComplVS", "ComplVV", "SlashV2V")


# Manner adverbials that modify the event, lifted like time adverbials
# ("delivered [reports late]" -> "[delivered reports] late").
_EVENT_ADVERBS = ("late_Adv", "everyDay_Adv", "everyWeek_Adv", "everyMonth_Adv")


def _is_time_adverb(t) -> bool:
    return not t.args and bool(_TIME_ADVERB.fullmatch(t.head))


def _is_event_adverb(t) -> bool:
    return _is_time_adverb(t) or (not t.args and t.head in _EVENT_ADVERBS)


def _lift_time_adverbs(clause):
    """The parser attaches a time adverbial wherever the string allows,
    usually to a noun phrase ("won [the contract in 1993]", "lived in
    [Birmingham for two years]"); it locates the event, so it is moved to
    the verb phrase ("[won the contract] in 1993"), the attachment
    `background.py`'s temporal rules read. Only inside the main clause's
    verb phrase, inside any "before/after" clause."""
    if clause.head != "PredVP" or len(clause.args) != 2:
        return clause
    found = []

    def strip(t):
        if t.head in ("AdvNP", "AdvCN") and len(t.args) == 2 and _is_event_adverb(t.args[1]):
            found.append(t.args[1])
            return strip(t.args[0])
        if t.head in _TIME_OPAQUE:
            return t
        return App(t.head, [strip(a) for a in t.args])

    def wrap(vp):
        if vp.head == "AdvVP" and len(vp.args) == 2 and vp.args[1].head == "SubjS":
            return App("AdvVP", [wrap(vp.args[0]), vp.args[1]])
        # inside "always"/"never": "always [delivers reports late]"
        if vp.head == "AdVVP" and len(vp.args) == 2:
            return App("AdVVP", [vp.args[0], wrap(vp.args[1])])
        # innermost first, as in the sentence ("reports late in 1993")
        for adv in reversed(found):
            vp = App("AdvVP", [vp, adv])
        return vp

    vp = strip(clause.args[1])
    return App("PredVP", [clause.args[0], wrap(vp)]) if found else clause


def _strip_outer_adjective(cn):
    """One-anaphora with its own modifier ("a BLUE one") contrasts with the
    antecedent's outermost adjective: after "a red car", "a blue one" is a
    blue CAR, and after "a fast red car", "a slow one" is a slow RED CAR."""
    if cn.head == "AdjCN" and len(cn.args) == 2:
        return cn.args[1]
    return cn


def _object_cn(vp):
    """The noun phrase content one-anaphora can pick up from a clause: the
    CN of the first common-noun NP inside its VP."""
    if vp.head in ("DetCN", "MassNP") and vp.args:
        return vp.args[-1]
    for a in vp.args:
        found = _object_cn(a)
        if found is not None:
            return found
    return None


def _replace_one(t, antecedent_cn):
    """Substitute anaphoric `one` (anaphOne_N / anaphOne_NP) by the
    antecedent's CN; (tree, used_anaphor)."""
    if t.head == "AdjCN" and len(t.args) == 2 and t.args[1].head == "UseN" \
            and t.args[1].args and t.args[1].args[0].head == "anaphOne_N":
        return App("AdjCN", [t.args[0], _strip_outer_adjective(antecedent_cn)]), True
    if t.head == "UseN" and t.args and t.args[0].head == "anaphOne_N":
        return antecedent_cn, True
    if t.head == "anaphOne_NP" and not t.args:
        return App("DetCN", [App("DetQuant", [App("IndefArt", []), App("NumSg", [])]), antecedent_cn]), True
    used = False
    args = []
    for a in t.args:
        na, u = _replace_one(a, antecedent_cn)
        args.append(na)
        used = used or u
    return App(t.head, args), used


_QUANTIFIED_DETS = ("every_Det", "each_Det", "no_Det", "all_Predet")


def _it_antecedent(clause):
    """The noun "it" in the next sentence can be resolved to: the CN of an
    indefinite singular object ("each department has [a dedicated
    line]"), only when the subject is quantified, so "it" cannot be the
    subject instead."""
    if clause.head != "PredVP" or len(clause.args) != 2:
        return None
    subject, vp = clause.args
    if not _mentions(subject, _QUANTIFIED_DETS):
        return None
    if vp.head == "ComplSlash" and len(vp.args) == 2:
        np = vp.args[1]
        if np.head == "DetCN" and np.args[0].head == "DetQuant" and len(np.args[0].args) == 2 \
                and np.args[0].args[0].head == "IndefArt" and np.args[0].args[1].head == "NumSg":
            return np.args[1]
    return None


def _replace_it_object(vp, cn, pronoun="it_Pron"):
    """A transitive VP's object "it" (possibly with an adverbial: "rents
    it from BT") -> "a CN"; (vp, replaced)."""
    if vp.head != "ComplSlash" or len(vp.args) != 2:
        return vp, False
    np = vp.args[1]
    indefinite = App("DetCN", [App("DetQuant", [App("IndefArt", []), App("NumSg", [])]), cn])
    if np.head == "UsePron" and np.args[0].head == pronoun:
        return App("ComplSlash", [vp.args[0], indefinite]), True
    if np.head == "AdvNP" and np.args[0].head == "UsePron" and np.args[0].args[0].head == pronoun:
        return App("ComplSlash", [vp.args[0], App("AdvNP", [indefinite, np.args[1]])]), True
    return vp, False


def _mentions(t, head):
    if isinstance(head, tuple):
        return t.head in head or any(_mentions(a, head) for a in t.args)
    return t.head == head or any(_mentions(a, head) for a in t.args)


def resolve(t, antecedent_vp, antecedent_cn, antecedent_subject=None):
    """A parsed sentence -> (clause, negated, error). Resolves VP ellipsis
    ("so did Bill", "Bill didn't", "the students have too") by copying the
    antecedent clause's VP - the standard copy treatment - and one-anaphora
    by the antecedent's noun. Sentential negation is translated only with a
    proper-name subject: with a quantified subject ("every tenor is not
    modest") its scope is ambiguous, and no reading is guessed."""
    if t.head == "UttS" and len(t.args) == 1:
        t = t.args[0]
    t = _strip_too(t)
    if antecedent_vp is not None and t.head in _ELLIPTICAL and _ambiguous_antecedent(antecedent_vp):
        return None, False, "ellipsis whose antecedent embeds another verb phrase (which one is elided is ambiguous)"
    if t.head == "ExtAdvS" and len(t.args) == 2:
        # "If S1, then S2": "then" adds nothing; an elliptical S2 ("then
        # Bill did too") takes S1's verb phrase
        adv, main = t.args
        if main.head == "ThenS" and len(main.args) == 1:
            main = main.args[0]
        if adv.head == "SubjS" and len(adv.args) == 2 and main.head in ("ElliptS", "SoS"):
            antecedent = to_clause(adv.args[1])
            if antecedent.head != "PredVP" or _ambiguous_antecedent(antecedent.args[1]):
                return None, False, "elliptical consequent without a plain antecedent clause"
            np, aux = main.args if main.head == "ElliptS" else (main.args[1], main.args[0])
            pol = App("PNeg" if aux.head == "ellDidnt" else "PPos", [])
            main = App("UseCl", [App("TTAnt", [App("TPast", []), App("ASimul", [])]), pol,
                                 App("PredVP", [np, antecedent.args[1]])])
        return App("ExtAdvS", [adv, main]), False, None
    if t.head in ("GapS", "GapS2", "ElliptAdvS", "FragAdvS", "FragNPS"):
        # gapping and fragments: the antecedent clause with its parallel
        # constituent(s) replaced (see `_replace_modifiers`)
        if antecedent_vp is None:
            return None, False, "fragment with no antecedent clause"
        negated = False
        if t.head == "GapS":
            clause = App("PredVP", [t.args[0], _replace_modifiers(antecedent_vp, [t.args[1]])])
        elif t.head == "GapS2":
            clause = App("PredVP", [t.args[0], _replace_modifiers(antecedent_vp, list(t.args[1:]))])
        elif t.head == "ElliptAdvS":
            clause = App("PredVP", [t.args[0], _replace_modifiers(antecedent_vp, [t.args[2]])])
            negated = t.args[1].head == "ellDidnt"
        elif t.head == "FragAdvS":
            if antecedent_subject is None:
                return None, False, "fragment adverbial with no antecedent subject"
            clause = App("PredVP", [antecedent_subject, _replace_modifiers(antecedent_vp, [t.args[0]])])
        else:
            clause = App("PredVP", [t.args[0], antecedent_vp])
        if negated and clause.args[0].head != "UsePN":
            return None, False, "negation with a non-proper-name subject (scope ambiguous)"
        return _lift_time_adverbs(clause), negated, None
    if t.head == "AdvS" and len(t.args) == 2:
        # A fronted adverbial ("In 1993 ITEL won the contract") modifies
        # the clause's VP, as it would in final position ("ITEL won the
        # contract in 1993"). Only with a positive clause and a
        # proper-name subject: under negation or a quantified subject a
        # fronted adverbial can take wider scope than a final one.
        adv, inner = t.args
        clause, negated, err = resolve(inner, antecedent_vp, antecedent_cn)
        if clause is None:
            return None, False, err
        if negated or clause.head != "PredVP" or clause.args[0].head != "UsePN":
            return None, False, "fronted adverbial with negation or a non-proper-name subject (scope)"
        return App("PredVP", [clause.args[0], App("AdvVP", [clause.args[1], adv])]), False, None
    negated = False
    if t.head in ("ElliptS", "SoS") and len(t.args) == 2:
        np, aux = (t.args if t.head == "ElliptS" else (t.args[1], t.args[0]))
        if antecedent_vp is None:
            return None, False, "VP ellipsis with no antecedent clause"
        clause = App("PredVP", [np, antecedent_vp])
        negated = aux.head == "ellDidnt"
    elif t.head == "UseCl" and len(t.args) == 3:
        negated = t.args[1].head in _NEGATIVE_POLARITIES
        clause = t.args[2]
    else:
        clause = t
    if negated:
        if not (clause.head == "PredVP" and clause.args and clause.args[0].head == "UsePN"):
            return None, False, "negation with a non-proper-name subject (scope ambiguous)"
    if _mentions(clause, "anaphOne_N") or _mentions(clause, "anaphOne_NP"):
        if antecedent_cn is None:
            return None, False, "one-anaphora with no antecedent noun"
        clause, _ = _replace_one(clause, antecedent_cn)
    clause = _possessor_in_coordination(clause)
    clause = _own_possessive(clause)
    clause = _subordinate_pronoun(clause)
    if _complement_ellipsis(clause):
        # ellipsis as a clausal complement ("Bill said Peter did too");
        # "before Smith did" is readings.py's `_ordered`'s, copying the
        # main clause's own VP
        if antecedent_vp is None:
            return None, False, "embedded VP ellipsis with no antecedent clause"
        clause = _resolve_embedded_ellipsis(clause, antecedent_vp)
    return _lift_time_adverbs(clause), negated, None


# Sentence heads whose verb phrase is copied from the antecedent clause.
_ELLIPTICAL = ("ElliptS", "SoS", "ElliptAdvS", "GapS", "GapS2", "FragAdvS", "FragNPS")


def _strip_too(t):
    """"too" adds nothing to truth conditions, wherever it attaches; nor
    does "currently" in a translation that reads the present tense as the
    present ("ITEL currently has a factory", FraCaS 251)."""
    if t.head == "TooS" and len(t.args) == 1:
        return _strip_too(t.args[0])
    if t.head == "AdVVP" and len(t.args) == 2 and t.args[0].head == "currently_AdV":
        return _strip_too(t.args[1])
    # "always"/"never" quantify over occasions and must stay in the VP's
    # name (translate.py's namer drops pre-verbal adverbs, which would make
    # "never delivers reports late" the same predicate as "delivers reports
    # late"): as a one-word adverbial they name it, `neverDeliverReportLate`
    if t.head == "AdVVP" and len(t.args) == 2 and t.args[0].head in ("always_AdV", "never_AdV"):
        word = t.args[0].head[: -len("_AdV")]
        return App("AdVVP", [App(f"{word}_Adv", []), _strip_too(t.args[1])])
    return App(t.head, [_strip_too(a) for a in t.args])


def _own_possessive(t):
    """"Smith ran his own business": "his own" is the subject's own, so the
    VP is a property of the subject - "ran an own business" names it
    (`runOwnBusiness`), with no pronoun left to resolve."""
    if t.head == "DetCN" and len(t.args) == 2 and t.args[0].head == "DetQuant" \
            and t.args[0].args[0].head == "PossPron" and t.args[1].head == "AdjCN" \
            and t.args[1].args[0].head == "PositA" and t.args[1].args[0].args[0].head == "own_A":
        return App("DetCN", [App("DetQuant", [App("IndefArt", []), t.args[0].args[1]]), t.args[1]])
    return App(t.head, [_own_possessive(a) for a in t.args])


def _subordinate_pronoun(clause):
    """"Smith left the house before she took a taxi": a he/she subject of
    the subordinate clause is the main clause's named subject, the only
    antecedent in the sentence."""
    if not (clause.head == "PredVP" and len(clause.args) == 2 and clause.args[0].head == "UsePN"):
        return clause
    subject, vp = clause.args
    if vp.head == "AdvVP" and len(vp.args) == 2 and vp.args[1].head == "SubjS":
        conj, sub = vp.args[1].args
        if sub.head == "UseCl" and len(sub.args) == 3 and sub.args[2].head == "PredVP" \
                and sub.args[2].args[0].head == "UsePron" and sub.args[2].args[0].args[0].head in ("he_Pron", "she_Pron"):
            inner = App("PredVP", [subject, sub.args[2].args[1]])
            vp = App("AdvVP", [vp.args[0], App("SubjS", [conj, App("UseCl", [sub.args[0], sub.args[1], inner])])])
            return App("PredVP", [subject, vp])
    return clause


def _ambiguous_antecedent(vp) -> bool:
    """Whether an elided VP could copy this VP or one embedded in it ("John
    said Mary wrote a report, and Bill did too": Bill said so, or John
    said Bill wrote one - FraCaS 175/176; "John wanted to buy a car, and
    he did", 180). No reading is guessed."""
    return _mentions(vp, ("ComplVS", "ComplVSBare", "ComplVV", "EmbedVP", "EmbedS"))


_CLAUSAL_COMPLEMENT = ("ComplVS", "ComplVSBare")


def _complement_ellipsis(t) -> bool:
    if t.head in _CLAUSAL_COMPLEMENT and len(t.args) == 2 and t.args[1].head in ("ElliptS", "SoS"):
        return True
    return any(_complement_ellipsis(a) for a in t.args)


def _resolve_embedded_ellipsis(t, antecedent_vp):
    if t.head in _CLAUSAL_COMPLEMENT and len(t.args) == 2 and t.args[1].head in ("ElliptS", "SoS"):
        return App(t.head, [t.args[0], _resolve_embedded_ellipsis(t.args[1], antecedent_vp)])
    if t.head in ("ElliptS", "SoS") and len(t.args) == 2:
        np, aux = t.args if t.head == "ElliptS" else (t.args[1], t.args[0])
        pol = App("PNeg" if aux.head == "ellDidnt" else "PPos", [])
        return App("UseCl", [App("TTAnt", [App("TPast", []), App("ASimul", [])]), pol,
                             App("PredVP", [np, antecedent_vp])])
    if t.head in ("ElliptS", "SoS", "SubjS"):
        return t
    return App(t.head, [_resolve_embedded_ellipsis(a, antecedent_vp) for a in t.args])


def _adv_items(adv):
    """A VP adverbial as a list of adverbials: the parser attaches a
    second one to the first one's noun phrase ("to [Paris by car]")."""
    if adv.head == "PrepNP" and len(adv.args) == 2 and adv.args[1].head == "AdvNP" \
            and len(adv.args[1].args) == 2:
        np, inner = adv.args[1].args
        return [App("PrepNP", [adv.args[0], np]), *_adv_items(inner)]
    return [adv]


def _vp_frame(vp):
    """(VP without its adverbials, [its adverbials in order])."""
    if vp.head == "AdvVP" and len(vp.args) == 2:
        core, mods = _vp_frame(vp.args[0])
        return core, mods + _adv_items(vp.args[1])
    return vp, []


def _parallel(remnant, mod) -> bool:
    """Whether a remnant adverbial stands in for an antecedent one: the same
    preposition ("by train" for "by car"), or a time adverbial of the same
    kind ("at five o'clock" for "at four o'clock", "on Friday" for "on
    Thursday")."""
    if remnant.head == "PrepNP" and mod.head == "PrepNP":
        return remnant.args[0].head == mod.args[0].head
    if _is_time_adverb(remnant) and _is_time_adverb(mod):
        return re.match(r"[a-z]+", remnant.head).group() == re.match(r"[a-z]+", mod.head).group()
    return False


def _replace_modifiers(vp, remnants):
    """The antecedent VP with each remnant replacing its parallel adverbial,
    or added if it has none - gapping ("John went to Paris by car, and
    Bill to Berlin": Bill went to Berlin by car, FraCaS 152) and fragments
    ("John spoke to Mary on Thursday. And on Friday.")."""
    core, mods = _vp_frame(vp)
    mods = list(mods)
    for r in remnants:
        for i, m in enumerate(mods):
            if _parallel(r, m):
                mods[i] = r
                break
        else:
            mods.append(r)
    for m in mods:
        core = App("AdvVP", [core, m])
    return core


def _sentence_parts(t):
    """A sentence as the clauses it asserts in order: "S1, and S2" is S1
    then S2, and a sentence-initial "and"/"but" adds nothing to truth
    conditions."""
    if t.head == "UttS" and len(t.args) == 1:
        t = t.args[0]
    if t.head in ("AndS", "ButS") and len(t.args) == 1:
        return _sentence_parts(t.args[0])
    if t.head == "CommaAndS" and len(t.args) == 2:
        return _sentence_parts(t.args[0]) + _sentence_parts(t.args[1])
    return [t]


_PLURAL_INDEFINITE_DETS = ("several_Det", "somePl_Det", "aFew_Det", "many_Det")


def _etype_antecedent(clause):
    """(name, verb, CN, number) for a clause "NAME V-ed a/several CN",
    whose object a later pronoun can stand for."""
    if clause.head != "PredVP" or len(clause.args) != 2 or clause.args[0].head != "UsePN":
        return None
    vp = clause.args[1]
    if not (vp.head == "ComplSlash" and len(vp.args) == 2 and vp.args[0].head == "SlashV2a"
            and vp.args[1].head == "DetCN" and len(vp.args[1].args) == 2):
        return None
    det, cn = vp.args[1].args
    if det.head == "DetQuant" and len(det.args) == 2 and det.args[0].head == "IndefArt":
        number = {"NumSg": "sg", "NumPl": "pl", "NumCard": "pl"}.get(det.args[1].head)
    elif det.head in _PLURAL_INDEFINITE_DETS:
        number = "pl"
    else:
        number = None
    return None if number is None else (clause.args[0], vp.args[0], cn, number)


def _etype_description(antecedent):
    """An E-type pronoun's description (Evans 1977; Cooper 1979; Heim
    1990): "Smith attended a meeting. She chaired IT" - the meeting that
    Smith attended; "GFI owns several computers. ITEL maintains THEM" -
    all the computers that GFI owns (FraCaS 133: maximality)."""
    name, verb, cn, number = antecedent
    relative = App("UseRCl", [App("TTAnt", [App("TPast", []), App("ASimul", [])]), App("PPos", []),
                              App("StrandRelSlash", [App("IdRP", []), App("SlashVP", [name, verb])])])
    cn = App("RelCN", [cn, relative])
    if number == "sg":
        return App("DetCN", [App("DetQuant", [App("DefArt", []), App("NumSg", [])]), cn])
    return App("PredetNP", [App("all_Predet", []), App("DetCN", [App("DetQuant", [App("DefArt", []), App("NumPl", [])]), cn])])


_PRONOUN_NUMBER = {"it_Pron": "sg", "they_Pron": "pl"}


def _replace_etype_object(vp, antecedent):
    """A transitive VP's object pronoun matching the antecedent's number
    (possibly with an adverbial) -> the antecedent's E-type description."""
    if vp.head != "ComplSlash" or len(vp.args) != 2:
        return vp, False
    np = vp.args[1]
    pron, wrap = None, None
    if np.head == "UsePron":
        pron = np.args[0].head
    elif np.head == "AdvNP" and np.args[0].head == "UsePron":
        pron, wrap = np.args[0].args[0].head, np.args[1]
    if _PRONOUN_NUMBER.get(pron) != antecedent[3]:
        return vp, False
    description = _etype_description(antecedent)
    if wrap is not None:
        description = App("AdvNP", [description, wrap])
    return App("ComplSlash", [vp.args[0], description]), True


def _dependent_have(clause):
    """(M, N) for "every/each M has a N" - a dependency of each M's N on
    the M, which a later bridging definite can use (`_bridge`)."""
    if not (clause.head == "PredVP" and len(clause.args) == 2):
        return None
    subject, vp = clause.args
    if not (subject.head == "DetCN" and len(subject.args) == 2 and subject.args[0].head in ("every_Det", "each_Det")):
        return None
    if vp.head == "ComplSlash" and len(vp.args) == 2 and vp.args[0].head == "SlashV2a" \
            and vp.args[0].args[0].head == "have_V2" and vp.args[1].head == "DetCN":
        det, n = vp.args[1].args
        if det.head == "DetQuant" and det.args[0].head == "IndefArt" and det.args[1].head == "NumSg":
            return subject.args[1], n
    return None


def _sort_of(clause):
    """(name, M) for "NAME is a M"."""
    if not (clause.head == "PredVP" and len(clause.args) == 2 and clause.args[0].head == "UsePN"):
        return None
    vp = clause.args[1]
    if vp.head == "UseComp" and vp.args[0].head == "CompCN":
        return clause.args[0], vp.args[0].args[0]
    if vp.head == "UseComp" and vp.args[0].head == "CompNP" and vp.args[0].args[0].head == "DetCN":
        det, cn = vp.args[0].args[0].args
        if det.head == "DetQuant" and det.args[0].head == "IndefArt" and det.args[1].head == "NumSg":
            return clause.args[0], cn
    return None


def _of_name(cn):
    """(N, name) for "N of NAME", either attachment of the PP ("cover [page
    of R-95-103]" or "[cover page] of R-95-103")."""
    if cn.head == "AdvCN" and len(cn.args) == 2 and cn.args[1].head == "PrepNP" \
            and cn.args[1].args[0].head == "of_Prep" and cn.args[1].args[1].head == "UsePN":
        return cn.args[0], cn.args[1].args[1]
    if cn.head == "CompoundCN" and len(cn.args) == 2:
        inner = _of_name(cn.args[1])
        if inner is not None:
            return App("CompoundCN", [cn.args[0], inner[0]]), inner[1]
    return None


def _bridge(vp, bridging, named, premise):
    """A transitive VP's definite object as a value of a dependency
    `_dependent_have` recorded ("every report has a cover page"): "the
    cover page of R-95-103" is `coverPageOf r95103` (`FunTermNP`), and in a
    premise a bare "the cover page" is the cover page of the one report
    the discourse has named (Clark's bridging; FraCaS 138) - only when
    exactly one is named."""
    if not (vp.head == "ComplSlash" and len(vp.args) == 2 and vp.args[1].head == "DetCN"):
        return vp
    det, cn = vp.args[1].args
    if not (det.head == "DetQuant" and det.args[0].head == "DefArt" and det.args[1].head == "NumSg"):
        return vp
    of = _of_name(cn)
    if of is not None and repr(of[0]) in bridging:
        return App("ComplSlash", [vp.args[0], App("FunTermNP", [of[0], of[1]])])
    if premise and repr(cn) in bridging:
        sort = bridging[repr(cn)]
        owners = [n for n, m in named if m == sort]
        if len(owners) == 1:
            return App("ComplSlash", [vp.args[0], App("FunTermNP", [cn, owners[0]])])
    return vp


def _possessor_in_coordination(t):
    """"John and his colleagues": in a coordination with exactly one name,
    "his"/"her" is that name's ("John's colleagues")."""
    if t.head == "ConjNP" and len(t.args) == 2:
        items = _np_items(t.args[1])
        names = [i for i in items if i.head == "UsePN"]
        if len(names) == 1:
            def fix(np):
                if np.head == "DetCN" and np.args[0].head == "DetQuant" and np.args[0].args[0].head == "PossPron" \
                        and np.args[0].args[0].args[0].head in ("he_Pron", "she_Pron"):
                    return App("DetCN", [App("DetQuant", [App("GenNP", [names[0]]), np.args[0].args[1]]), np.args[1]])
                return np
            return App("ConjNP", [t.args[0], _map_items(t.args[1], fix)])
    return App(t.head, [_possessor_in_coordination(a) for a in t.args])


def _np_items(t):
    if t.head in ("BaseNP", "ConsNP") and len(t.args) == 2:
        return [t.args[0], *_np_items(t.args[1])] if t.head == "ConsNP" else list(t.args)
    return [t]


def _map_items(t, f):
    if t.head == "BaseNP":
        return App("BaseNP", [f(t.args[0]), f(t.args[1])])
    if t.head == "ConsNP":
        return App("ConsNP", [f(t.args[0]), _map_items(t.args[1], f)])
    return f(t)


def _resolve_sentence(tree, role, state):
    """([(clause, negated), ...], new state, error) for one sentence."""
    antecedent_vp, antecedent_cn, antecedent_subject, it_cn, etype, bridging, named, now = state
    bridging, named = dict(bridging), list(named)
    parts = _sentence_parts(tree)
    if role == "hypothesis" and len(parts) != 1:
        return None, state, "a coordinated hypothesis"
    out = []
    for part in parts:
        # "It is now 1996": the utterance time, for the perfect's "since"
        # (see `_since_to_now`); it asserts nothing else.
        if part.head == "ItIsNow" and part.args[0].head == "UsePN" and re.fullmatch(r"y\d{4}_PN", part.args[0].args[0].head):
            now = int(part.args[0].args[0].head[1:5])
            continue
        # "Then S." after a premise: S's event follows the previous one
        # ("Smith had left the house. Then she took a taxi" - she took a
        # taxi after Smith left the house, FraCaS 311).
        then = part.head == "ThenS" and len(part.args) == 1
        if then:
            part = part.args[0]
        clause, negated, err = resolve(part, antecedent_vp, antecedent_cn, antecedent_subject)
        if then and clause is not None:
            if negated or clause.head != "PredVP" or antecedent_subject is None or antecedent_vp is None \
                    or role == "hypothesis":
                return None, state, "\"then\" without a positive premise to follow"
            subject = clause.args[0]
            if subject.head == "UsePron" and subject.args[0].head in ("he_Pron", "she_Pron") \
                    and antecedent_subject.head == "UsePN":
                subject = antecedent_subject
            before = App("UseCl", [App("TTAnt", [App("TPast", []), App("ASimul", [])]), App("PPos", []),
                                   App("PredVP", [antecedent_subject, antecedent_vp])])
            clause = App("PredVP", [subject, App("AdvVP", [clause.args[1], App("SubjS", [App("after_Subj", []), before])])])
        if clause is None:
            return None, state, err
        # Object "it" in a premise, with an antecedent `_it_antecedent`
        # allows, reads as "a CN": what "it" picks out is one, so the
        # premise only gets weaker (never in the hypothesis, where that
        # would be stronger, and never under negation).
        if it_cn is not None and role != "hypothesis" and not negated and clause.head == "PredVP":
            vp, replaced = _replace_it_object(clause.args[1], it_cn)
            if replaced:
                clause = App("PredVP", [clause.args[0], vp])
            # Distributive "they" after "each department has a dedicated
            # line" ranges over the departments, and "them" is each one's
            # own line ("They rent them from BT", FraCaS 131): read as
            # "each department rents a dedicated line from BT", which the
            # dependent reading (Π d. Σ l. ...) entails.
            elif clause.args[0].head == "UsePron" and clause.args[0].args[0].head == "they_Pron" \
                    and antecedent_subject is not None:
                vp, replaced = _replace_it_object(clause.args[1], it_cn, "they_Pron")
                if replaced:
                    clause = App("PredVP", [antecedent_subject, vp])
        # Pronouns after "NAME V-ed a/several CN", in a positive premise: a
        # "he"/"she" subject is that name, and an object "it"/"them" is the
        # antecedent's E-type description (`_etype_description`).
        if etype is not None and role != "hypothesis" and not negated and clause.head == "PredVP":
            subject, vp = clause.args
            if subject.head == "UsePron" and subject.args[0].head in ("she_Pron", "he_Pron"):
                subject = etype[0]
            vp, _ = _replace_etype_object(vp, etype)
            clause = App("PredVP", [subject, vp])
        # "John and his colleagues went to a meeting. They hated it": on
        # either reading of "they" (all of them, or the colleagues), the
        # colleagues hated it - the plural conjunct; and "it" is the
        # meeting (FraCaS 128).
        if role != "hypothesis" and not negated and clause.head == "PredVP" and antecedent_subject is not None \
                and antecedent_subject.head == "ConjNP" and clause.args[0].head == "UsePron" \
                and clause.args[0].args[0].head == "they_Pron":
            plural = [i for i in _np_items(antecedent_subject.args[1]) if i.head != "UsePN"]
            if len(plural) == 1:
                vp = clause.args[1]
                if antecedent_cn is not None and vp.head == "ComplSlash" and vp.args[1].head == "UsePron" \
                        and vp.args[1].args[0].head == "it_Pron":
                    the = App("DetCN", [App("DetQuant", [App("DefArt", []), App("NumSg", [])]), antecedent_cn])
                    vp = App("ComplSlash", [vp.args[0], the])
                clause = App("PredVP", [plural[0], vp])
        if clause.head == "PredVP" and len(clause.args) == 2:
            clause = App("PredVP", [clause.args[0], _bridge(clause.args[1], bridging, named, role != "hypothesis")])
        dependent = _dependent_have(clause)
        if dependent is not None and not negated:
            bridging[repr(dependent[1])] = repr(dependent[0])
        sort = _sort_of(clause)
        if sort is not None and not negated:
            named.append((sort[0], repr(sort[1])))
        out.append((clause, negated))
        it_cn = _it_antecedent(clause)
        etype = _etype_antecedent(clause) if not negated else None
        if clause.head == "PredVP" and len(clause.args) == 2:
            antecedent_vp = clause.args[1]
            antecedent_cn = _object_cn(clause.args[1]) or antecedent_cn
            antecedent_subject = clause.args[0]
    return out, (antecedent_vp, antecedent_cn, antecedent_subject, it_cn, etype, tuple(bridging.items()), tuple(named), now), None


def _object_slot(vp):
    """(the transitive VP inside one-word adverbials, rebuild) for "V NP
    [ADV...]": rebuild(new_object) gives the same VP with its object
    replaced."""
    if vp.head == "AdvVP" and len(vp.args) == 2:
        inner = _object_slot(vp.args[0])
        if inner is None:
            return None
        core, rebuild = inner
        return core, lambda np: App("AdvVP", [rebuild(np), vp.args[1]])
    if vp.head == "ComplSlash" and len(vp.args) == 2 and vp.args[0].head == "SlashV2a":
        return vp, lambda np: App("ComplSlash", [vp.args[0], np])
    return None


def _is_it(np):
    return np.head == "UsePron" and np.args[0].head == "it_Pron"


def _singular_nps(t):
    """The singular noun phrases in a tree - everything a later "it" could
    in principle pick up."""
    if t.head == "UsePN" or t.head == "MassNP":
        yield t
    elif t.head == "DetCN" and len(t.args) == 2 and t.args[0].head == "DetQuant" \
            and len(t.args[0].args) == 2 and t.args[0].args[1].head == "NumSg":
        yield t
    for a in t.args:
        yield from _singular_nps(a)


def _hypothesis_referent(clauses):
    """An object "it" in the hypothesis whose only possible antecedent is a
    premise's "NAME V-ed a CN" ("Smith wrote a novel in 1991 ⊢ Smith wrote
    IT in 1992"): the indefinite introduces a discourse referent, named
    here (`theNovel`), and "it" is that referent - DRT's dynamic
    entailment, under which the premises' existential binds the
    hypothesis's pronoun (Kamp 1981; Groenendijk and Stokhof 1991). The
    premise becomes "Smith wrote theNovel in 1991" with "theNovel is a
    novel", which the claim's universal binding of `theNovel` makes
    exactly as strong as "Smith wrote a novel in 1991". Only when "it" has
    no other candidate: every other singular noun phrase in the premises
    is the hypothesis's own subject, which an object pronoun cannot be
    (binding principle B)."""
    role, hyp, negated, n = clauses[-1]
    if hyp.head != "PredVP" or len(hyp.args) != 2:
        return clauses
    slot = _object_slot(hyp.args[1])
    if slot is None:
        return clauses
    obj = slot[0].args[1]
    wrap = None
    if obj.head == "AdvNP" and len(obj.args) == 2:
        obj, wrap = obj.args
    if not _is_it(obj):
        return clauses
    subject = repr(hyp.args[0])
    found = None
    for i, (_r, clause, neg, _n) in enumerate(clauses[:-1]):
        others = [np for np in _singular_nps(clause) if repr(np) != subject]
        if not others:
            continue
        if found is not None or neg or clause.head != "PredVP" or clause.args[0].head != "UsePN":
            return clauses
        premise_slot = _object_slot(clause.args[1])
        if premise_slot is None:
            return clauses
        np = premise_slot[0].args[1]
        if not (np.head == "DetCN" and np.args[0].head == "DetQuant" and np.args[0].args[0].head == "IndefArt"
                and others == [np]):
            return clauses
        found = (i, premise_slot[1], np.args[1])
    if found is None:
        return clauses
    i, rebuild, cn = found
    ref = App("UsePN", [App(camel_name(["the", *_leaf_words(cn)]) + "_PN", [])])
    r, clause, neg, k = clauses[i]
    sort = App("PredVP", [ref, App("UseComp", [App("CompCN", [cn])])])
    out = list(clauses[:i]) + [(r, App("PredVP", [clause.args[0], rebuild(ref)]), neg, k), (r, sort, False, k)]
    out += clauses[i + 1:-1]
    out.append((role, App("PredVP", [hyp.args[0], slot[1](ref if wrap is None else App("AdvNP", [ref, wrap]))]),
                negated, n))
    return out


def _unresolved_object_pronoun(t):
    """An "it"/"them" left inside a verb phrase that nothing resolved:
    predicate names are built from words and a pronoun has none, so it
    would silently drop out ("Smith wrote it" named like "Smith wrote")."""
    if t.head in ("ComplSlash", "ComplVV", "AdvVP", "UseComp", "ComplVS", "PrepNP"):
        return any(n.head == "UsePron" and n.args[0].head in ("it_Pron", "they_Pron")
                   for n in _subtrees_of(t))
    return any(_unresolved_object_pronoun(a) for a in t.args)


def _since_to_now(t, now):
    """"Since 1992 ITEL has been in Birmingham. It is now 1996": the
    perfect's "since" runs up to the utterance time, `since1992to1996`
    (background.py relates it to the years within it, for a state)."""
    if not t.args and (m := re.fullmatch(r"since(\d{4})_Adv", t.head)) and int(m.group(1)) <= now:
        return App(f"since{m.group(1)}to{now}_Adv", [])
    return App(t.head, [_since_to_now(a, now) for a in t.args])


def _subtrees_of(t):
    yield t
    for a in t.args:
        yield from _subtrees_of(a)


_parse_cache: dict = {}


def ranked_readings(sentence: str) -> list[str]:
    tokens = tokenize(sentence)
    if tokens not in _parse_cache:
        _parse_cache[tokens] = parse_readings(tokens)
    _cat, trees = _parse_cache[tokens]
    return ranked(trees)


def assemble(idn, sentences):
    """(claims, None) or (None, reason). claims["assignments"] is one entry
    per consistent assignment of readings (see the header's "Yes/no
    claims"), each with its yes/no claims with and without background
    knowledge."""
    clauses = []  # (clause tree, negated)
    # antecedent VP, CN, subject; "it"'s CN; E-type antecedent; bridging
    # dependencies and named individuals' sorts (see `_bridge`)
    state = (None, None, None, None, None, (), (), None)
    for role, s in sentences:
        candidates = ranked_readings(s)
        n = len(candidates)
        if not candidates:
            return None, f"{role} does not parse: {s!r}"
        # The top-ranked reading that resolves: an anaphoric/elliptical
        # reading with nothing earlier to resolve against falls through to
        # the next-ranked one (ill-formed anaphora readings are already
        # filtered out by parse_rank.ranked).
        resolved = err = None
        for tree in candidates:
            resolved, new_state, err = _resolve_sentence(parse_tree(tree), role, state)
            if resolved is not None:
                break
        if resolved is None:
            return None, f"{role} parses ({n} readings) but does not translate: {err or 'no reading resolves'}"
        state = new_state
        clauses.extend((role, clause, negated, n) for clause, negated in resolved)
    if state[-1] is not None:
        clauses = [(role, _since_to_now(cl, state[-1]), neg, n) for role, cl, neg, n in clauses]
    clauses = _hypothesis_referent(clauses)
    for role, cl, _neg, n in clauses:
        if _unresolved_object_pronoun(cl):
            return None, f"{role} parses ({n} readings) but does not translate: an object pronoun with no resolved antecedent"
    # A dependency a bridging definite used is stated with its function
    # (readings.py's `DependentHave`).
    used = {repr(c.args[0]) for _r, cl, _n, _k in clauses for c in _subtrees_of(cl) if c.head == "FunTermNP"}
    clauses = [
        (role, App("DependentHave", [cl]) if (d := _dependent_have(cl)) is not None and repr(d[1]) in used else cl, neg, n)
        for role, cl, neg, n in clauses
    ]

    time_functions: list[str] = []  # event times, see readings.py's `_ordered`
    functions: list[str] = []  # possession functions, see readings.py's `_possessive`
    encodings: list[tuple[str, str, str]] = []

    def translate_all(reading):
        out = []
        for idx, (role, clause, negated, n) in enumerate(clauses):
            position = "hypothesis" if idx == len(clauses) - 1 else "premise"
            try:
                tr, side, times, extras = translate_cl_reading(clause, reading, position)
                time_functions.extend(t for t in times if t not in time_functions)
                functions.extend(f for f in extras["functions"] if f not in functions)
                encodings.extend(e for e in extras["encodings"] if e not in encodings)
            except Exception as e:  # translate.py signals unsupported shapes this way
                raise ValueError(f"{role} parses ({n} readings) but does not translate: {str(e)[:120]}")
            if tr.conjuncts or tr.free_functions or tr.template:
                raise ValueError(f"{role} needs non-generic assembly (conjuncts/Skolem/bundle)")
            out.append((tr, side, f"¬ ({tr.lean_prop})" if negated else tr.lean_prop))
        return out

    def premise_props(trs):
        # A premise's side premises (see readings.py's `quantified`) follow
        # it as separate hypotheses.
        props = []
        for _tr, side, p in trs:
            props.append(f"({p})")
            props += [f"({sp})" for sp in side]
        return props

    try:
        base = translate_all({})
        present = [
            k for k in AMBIGUITY_KINDS
            if [p for *_, p in translate_all({k: "strong"})] != [p for *_, p in base]
        ]
        assignments = [dict(zip(present, combo)) for combo in itertools.product(("weak", "strong"), repeat=len(present))]
        translated = [(a, translate_all(a)) for a in assignments]
    except ValueError as e:
        return None, str(e)

    kinds: dict[str, str] = {}
    order: list[str] = []
    for _a, trs in translated:
        for tr, _side, _p in trs:
            for name in tr.free_predicates:
                kind = "binary" if name in tr.binary_predicates else "unary"
                if kinds.setdefault(name, kind) != kind:
                    return None, f"name {name} used at two arities"
                if name not in order:
                    order.append(name)
            for name in tr.free_individuals:
                if kinds.setdefault(name, "individual") != "individual":
                    return None, f"name {name} used as both predicate and individual"
                if name not in order:
                    order.append(name)
    for name in time_functions:
        if kinds.setdefault(name, "time") != "time":
            return None, f"name {name} used as both a time and something else"
        if name not in order:
            order.append(name)
    for name in functions:
        if kinds.setdefault(name, "function") != "function":
            return None, f"name {name} used as both a function and something else"
        if name not in order:
            order.append(name)
    bad = [n for n in order if n in LEAN_RESERVED or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", n)]
    if bad:
        return None, f"generated names unusable as Lean binders: {bad}"

    unary = [n for n in order if kinds[n] == "unary"]
    binary = [n for n in order if kinds[n] == "binary"]
    inds = [n for n in order if kinds[n] == "individual"]
    times = [n for n in order if kinds[n] == "time"]
    fns = [n for n in order if kinds[n] == "function"]
    binders = ["{A : Type}", "[Fintype A]"]
    if unary:
        binders.append(f"({' '.join(unary)} : A → Prop)")
        binders += [f"[DecidablePred {n}]" for n in unary]
    if binary:
        binders.append(f"({' '.join(binary)} : A → A → Prop)")
        # Counting over a binary verb ("more orders than APCOM won":
        # `card (fun x => order x ∧ win apcom x)`) needs it decidable,
        # like the unary predicates above.
        binders += [f"[DecidableRel {n}]" for n in binary]
    if inds:
        binders.append(f"({' '.join(inds)} : A)")
    if times:
        # When each individual's culminating event of that kind happens
        # (or would): "Smith left before Jones left" is `leave smith ∧
        # leaveTime smith < leaveTime jones`.
        binders.append(f"({' '.join(times)} : A → ℕ)")
    if fns:
        # Each possessor's possessed thing ("her workstation"), see
        # readings.py's `_possessive`.
        binders.append(f"({' '.join(fns)} : A → A)")
    # The proportional reading of "many" is an opaque relation, stated
    # with the two properties every reading of "many" (cardinal or
    # proportional) has, as part of what the word means: it entails
    # "some", and it is upward monotone in its scope ("many delegates got
    # interesting results" => "many delegates got results"). It is NOT
    # monotone in its restrictor - "many British delegates" says nothing
    # about "many delegates" on the proportional reading (FraCaS 56).
    meaning = []
    if any(re.search(r"\bMany\b", p) for _a, trs in translated for *_, p in trs):
        binders.append("(Many : (A → Prop) → (A → Prop) → Prop)")
        meaning.append("(∀ P Q : A → Prop, Many P Q → Some P Q)")
        meaning.append("(∀ P Q R : A → Prop, Many P Q → (∀ x, Q x → R x) → Many P R)")
    # "few" on its proportional reading is likewise opaque, stated with the
    # one property every reading of "few" has: narrowing its scope within
    # its restrictor preserves it ("few committee members are from
    # southern Europe" => "few are from Portugal", FraCaS 44). It is not
    # monotone in its restrictor on that reading, and does not entail that
    # any such X exist (12). The cardinal reading, `AtMost fewCount`, and
    # "a few", `AtLeast aFewCount`, and "several", `AtLeast severalCount`,
    # count against an unknown threshold.
    if any(re.search(r"\bFew\b", p) for _a, trs in translated for *_, p in trs):
        binders.append("(Few : (A → Prop) → (A → Prop) → Prop)")
        meaning.append("(∀ P Q R : A → Prop, Few P Q → (∀ x, P x → R x → Q x) → Few P R)")
    if any(re.search(r"\bfewCount\b", p) for _a, trs in translated for *_, p in trs):
        binders.append("(fewCount : Nat)")
    if any(re.search(r"\baFewCount\b", p) for _a, trs in translated for *_, p in trs):
        binders.append("(aFewCount : Nat)")
        meaning.append("(aFewCount ≥ 1)")
    if any(re.search(r"\bseveralCount\b", p) for _a, trs in translated for *_, p in trs):
        binders.append("(severalCount : Nat)")
        meaning.append("(severalCount ≥ 2)")
    # A relation and the fused name of "V a CN" (`use x y`, `useWorkstation
    # x`) say the same thing in two encodings: `useWorkstation x` is "x
    # uses some workstation". Stated wherever a problem uses both, as part
    # of what the names mean, not as background knowledge.
    for relation, noun, fused in encodings:
        if relation in binary and noun in unary and fused in unary:
            meaning.append(f"(∀ x, {fused} x ↔ ∃ y, {noun} y ∧ {relation} x y)")
    knowledge = postulates([c for _r, c, _n, _k in clauses], set(unary), set(binary))
    head = f"∀ {' '.join(binders)}, "

    out = []
    for a, trs in translated:
        premises = premise_props(trs[:-1])
        hyp = trs[-1][2]

        def chain(facts, conclusion):
            return head + " → ".join([*meaning, *facts, *premises, f"({conclusion})"])

        desc = ", ".join(f"{k} {v}" for k, v in a.items()) or "unambiguous"
        out.append({
            "desc": desc,
            "yes": chain([], hyp),
            "no": chain([], f"¬ ({hyp})"),
            "bk_yes": chain(knowledge, hyp),
            "bk_no": chain(knowledge, f"¬ ({hyp})"),
        })
    return {"assignments": out, "n_facts": len(knowledge)}, None


def main() -> None:
    problems = load_problems()
    emitted: list[tuple[int, str]] = []
    skipped: dict[int, str] = {}
    for idn, premises, hypothesis, answer in problems:
        sentences = [(f"premise {i + 1}", p) for i, p in enumerate(premises)]
        sentences.append(("hypothesis", hypothesis))
        claims, reason = assemble(idn, sentences)
        if claims is None:
            skipped[idn] = reason
        else:
            emitted.append((idn, answer, claims))

    def stage(reason: str) -> str:
        for key, label in (
            ("does not parse", "a sentence does not parse"),
            ("does not translate", "a sentence parses but translate.py does not cover its reading"),
            ("non-generic assembly", "a translation needs non-generic assembly"),
            ("used", "a generated name is used at two different kinds"),
            ("unusable", "a generated name is not a usable Lean binder"),
        ):
            if key in reason:
                return label
        return reason

    reasons = collections.Counter(stage(r) for r in skipped.values())
    lines = [
        "-- Generated by EndToEnd/gen_claims.py - do not hand-edit;",
        "-- re-run the script instead (needs the gf binary - see its header).",
        "import LeanNLSemantics.FraCaS.Types",
        "import LeanNLSemantics.FraCaS.Section1.GQ",
        "import LeanNLSemantics.FraCaS.Section2.Plurals",
        "import EndToEnd.Quantifiers",
        "",
        "/-!",
        "# End-to-end evaluation: claims translated from FraCaS's English",
        "",
        "Each `fracas_NNN_*` below was produced with no human in the",
        "translation step: FraCaS's own English, parsed by the restricted GF",
        "grammar, the top-ranked reading translated by `gf/translate.py`, and",
        "assembled by one generic rule. See `EndToEnd/gen_claims.py` for the",
        "exact pipeline and what it deliberately does not supply. Evaluated by",
        "`EndToEnd/Scan.lean`.",
        "",
        f"{len(emitted)} of {len(problems)} problems carried all the way through;",
        "the rest, by first failing stage:",
    ]
    for r, c in reasons.most_common():
        lines.append(f"- {r}: {c}")
    lines += [
        "",
        "Per-problem skip reasons (first failing sentence/stage):",
        "",
    ]
    for idn in sorted(skipped):
        # Lean block comments nest, so neither delimiter may appear inside.
        lines.append(f"- {idn}: {skipped[idn]}".replace("-/", "- /").replace("/-", "/ -"))
    lines += [
        "-/",
        "",
        "namespace FraCaS.EndToEnd",
        "namespace Claims",
        "open FraCaS.Section1 FraCaS.Section2",
        "",
    ]
    def names(idn, c, kind):
        return [f"``Claims.fracas_{idn:03d}_{kind}_{i}" for i in range(len(c["assignments"]))]

    for idn, _answer, c in emitted:
        for i, asg in enumerate(c["assignments"]):
            lines.append(f"/-- Reading assignment {i} ({asg['desc']}): \"yes\" test. -/")
            lines.append(f"def fracas_{idn:03d}_yes_{i} : Prop :=\n  {asg['yes']}")
            lines.append("")
            lines.append(f"/-- Reading assignment {i} ({asg['desc']}): \"no\" test. -/")
            lines.append(f"def fracas_{idn:03d}_no_{i} : Prop :=\n  {asg['no']}")
            lines.append("")
            lines.append(f"/-- As `_yes_{i}`, with {c['n_facts']} background-knowledge premise(s) from `EndToEnd/background.py`. -/")
            lines.append(f"def fracas_{idn:03d}_bk_yes_{i} : Prop :=\n  {asg['bk_yes']}")
            lines.append("")
            lines.append(f"/-- As `_no_{i}`, with the same background knowledge. -/")
            lines.append(f"def fracas_{idn:03d}_bk_no_{i} : Prop :=\n  {asg['bk_no']}")
            lines.append("")
    lines += [
        "end Claims",
        "",
        "/-- `(problem id, gold answer, yes-claims, no-claims)` - one claim per",
        "consistent reading assignment - for every problem the pipeline carried",
        "through; read by `EndToEnd/Scan.lean`. -/",
        "def registry : List (Nat × Answer × List Lean.Name × List Lean.Name) := [",
    ]
    rows = [
        f"  ({idn}, .{answer}, [{', '.join(names(idn, c, 'yes'))}], [{', '.join(names(idn, c, 'no'))}])"
        for idn, answer, c in emitted
    ]
    lines.append(",\n".join(rows))
    lines += [
        "]",
        "",
        "/-- The same problems, each claim with `EndToEnd/background.py`'s",
        "problem-independent background knowledge added as premises. -/",
        "def registryBk : List (Nat × Answer × List Lean.Name × List Lean.Name) := [",
    ]
    rows = [
        f"  ({idn}, .{answer}, [{', '.join(names(idn, c, 'bk_yes'))}], [{', '.join(names(idn, c, 'bk_no'))}])"
        for idn, answer, c in emitted
    ]
    lines.append(",\n".join(rows))
    lines += ["]", "", "end FraCaS.EndToEnd", ""]
    OUT_PATH.write_text("\n".join(lines))
    print(f"emitted {len(emitted)} / {len(problems)}; skipped: {dict(reasons)}")


if __name__ == "__main__":
    main()
