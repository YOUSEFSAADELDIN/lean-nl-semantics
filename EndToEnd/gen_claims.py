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
from translate import App, parse_tree  # noqa: E402
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


def _mentions(t, head):
    return t.head == head or any(_mentions(a, head) for a in t.args)


def resolve(t, antecedent_vp, antecedent_cn):
    """A parsed sentence -> (clause, negated, error). Resolves VP ellipsis
    ("so did Bill", "Bill didn't", "the students have too") by copying the
    antecedent clause's VP - the standard copy treatment - and one-anaphora
    by the antecedent's noun. Sentential negation is translated only with a
    proper-name subject: with a quantified subject ("every tenor is not
    modest") its scope is ambiguous, and no reading is guessed."""
    if t.head == "UttS" and len(t.args) == 1:
        t = t.args[0]
    if t.head == "TooS" and len(t.args) == 1:
        t = t.args[0]
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
    return clause, negated, None


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
    antecedent_vp = antecedent_cn = None
    for role, s in sentences:
        candidates = ranked_readings(s)
        n = len(candidates)
        if not candidates:
            return None, f"{role} does not parse: {s!r}"
        # The top-ranked reading that resolves: an anaphoric/elliptical
        # reading with nothing earlier to resolve against falls through to
        # the next-ranked one (ill-formed anaphora readings are already
        # filtered out by parse_rank.ranked).
        clause = err = None
        for tree in candidates:
            clause, negated, err = resolve(parse_tree(tree), antecedent_vp, antecedent_cn)
            if clause is not None:
                break
        if clause is None:
            return None, f"{role} parses ({n} readings) but does not translate: {err or 'no reading resolves'}"
        clauses.append((role, clause, negated, n))
        if clause.head == "PredVP" and len(clause.args) == 2:
            antecedent_vp = clause.args[1]
            antecedent_cn = _object_cn(clause.args[1]) or antecedent_cn

    def translate_all(reading):
        out = []
        for idx, (role, clause, negated, n) in enumerate(clauses):
            position = "hypothesis" if idx == len(clauses) - 1 else "premise"
            try:
                tr, side = translate_cl_reading(clause, reading, position)
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
    bad = [n for n in order if n in LEAN_RESERVED or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", n)]
    if bad:
        return None, f"generated names unusable as Lean binders: {bad}"

    unary = [n for n in order if kinds[n] == "unary"]
    binary = [n for n in order if kinds[n] == "binary"]
    inds = [n for n in order if kinds[n] == "individual"]
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
