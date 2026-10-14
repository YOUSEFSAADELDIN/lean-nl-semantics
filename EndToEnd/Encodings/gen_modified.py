#!/usr/bin/env python3
"""Generate EndToEnd/Encodings/Modified.lean: Phase 3 of the noun-encoding
comparison (README.md here), the modified nouns of Section 1.

The lexical-premise audit (LeanNLSemantics/FraCaS/LEXICAL_AUDIT.md) found 8
problems whose hand-written proof needs an added premise saying that a
modified noun is a kind of the noun ("an Irish delegate is a delegate";
`lexical_audit.tsv`, tag `noun`). The pipeline reaches all 8, and supplies
the same fact as background knowledge (`EndToEnd/background.py`), because
it states "Irish delegate" as one fused predicate, `irishDelegate`. This
phase asks which encodings supply the fact themselves.

It starts from F's own claims without background knowledge
(`fracas_NNN_yes_k`, `fracas_NNN_no_k` in EndToEnd/Claims.lean), so the
parse, the readings, the determiners and the verb phrases are F's, and
changes only the fused names the pipeline's trees build from an adjective
and a noun (`AdjCN`), and the one built from "used to be" and such a noun
(`ComplVV usedTo_VV`). Each is restated in three encodings, with the
adjective classes of EndToEnd/background.py, as in Phase 1a
(gen_encodings.py):

- P (extensional Montague): a noun is a predicate. An intersective
  adjective conjoins: "Irish delegate" is `fun x => delegate x ∧ irish x`.
  A subsective one takes the noun's extension, `leading businessman`, and
  "a leading businessman is a businessman" is a counted postulate.
- W (intensional Montague): as P, but the decomposed nouns and adjectives
  are intensions, evaluated at the actual world `w₀`; a subsective
  adjective takes the noun's intension. The other predicates, F's fused
  verb phrases among them, keep F's extensional type: binding `p : A →
  Prop` is the same as binding `p : W → A → Prop` and using `p w₀`.
- M (MTT): P's claim lifted as in Phase 2 (gen_lifted.py): each noun that
  restricts a quantifier is a type with an embedding into the
  individuals, and an intersective adjective restricts the type ("some
  Irish delegate" is `SomeT eDelegate (fun x => irish x) …`). A
  subsective adjective is indexed by the noun's type, as in Phase 1a:
  "x is a leading businessman" is `∃ y : Businessman, leading Businessman
  (eBusinessman y) ∧ eBusinessman y = x`, so subsectivity is built in.

"Used to" is an opaque operator on properties in all three, with one
counted postulate: it is upward monotone (EndToEnd/background.py's
UPWARD_VV, which F folds into its background fact).

Run: `python3 EndToEnd/Encodings/gen_modified.py` (needs the gf binary,
like gen_claims.py). Do not hand-edit the output.
"""
from __future__ import annotations

import csv
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
END_TO_END = HERE.parent
ROOT = END_TO_END.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(END_TO_END))
sys.path.insert(0, str(ROOT / "gf"))

import gen_encodings  # noqa: E402
import gen_lifted  # noqa: E402
from gen_lifted import Group, read_seq, render, split_claim, tokenize  # noqa: E402
from translate import _leaf_words, camel_name  # noqa: E402

CLAIMS = END_TO_END / "Claims.lean"
AUDIT = ROOT / "LeanNLSemantics" / "FraCaS" / "lexical_audit.tsv"
OUT = HERE / "Modified.lean"
STATS = HERE / "modified.json"
ENCODINGS = ("P", "W", "M")


class Unsupported(Exception):
    pass


def audit_problems() -> list[int]:
    """The problems whose added premise the audit tags `noun`."""
    rows = csv.DictReader(AUDIT.open(encoding="utf-8"), delimiter="\t")
    return sorted({int(r["id"]) for r in rows if r["record"] == "added" and r["tag"] == "noun"})


def _walk(t):
    yield t
    for a in t.args:
        yield from _walk(a)


def _noun(cn) -> str:
    if cn.head in ("UseN", "CompoundCN"):
        return camel_name(_leaf_words(cn))
    raise Unsupported(f"noun {cn.head}")


def decompositions(idn: int, problem) -> dict:
    """Fused name -> ("adj", adjective, kind, noun) | ("usedTo", inner), from
    the pipeline's own resolved trees."""
    _i, premises, hypothesis, _answer = problem
    out: dict = {}

    def cn_parts(cn):
        if cn.head == "AdjCN" and len(cn.args) == 2:
            a = gen_encodings._adj(cn.args[0])
            return ("adj", a, gen_encodings._kind(a), _noun(cn.args[1]))
        return ("noun", _noun(cn))

    for _role, clause, _neg in gen_encodings.resolved(idn, premises, hypothesis):
        for t in _walk(clause):
            if t.head == "AdjCN" and len(t.args) == 2:
                try:
                    out.setdefault(camel_name(_leaf_words(t)), cn_parts(t))
                except (Unsupported, gen_encodings.Unsupported):
                    pass
            if (t.head == "ComplVV" and t.args[0].head == "usedTo_VV" and t.args[1].head == "UseComp"
                    and t.args[1].args[0].head == "CompCN"):
                out.setdefault(camel_name(_leaf_words(t)), ("usedTo", cn_parts(t.args[1].args[0].args[0])))
    return out


class Problem:
    """One problem's decomposed names, rendered in one encoding."""

    def __init__(self, enc: str, decomp: dict, f_unary: list[str]):
        self.enc = enc
        # Only names F's claim actually binds are restated.
        self.decomp = {n: d for n, d in decomp.items() if n in f_unary}
        self.nouns: list[str] = []  # atomic nouns the decomposition uses
        self.inter: list[str] = []  # intersective adjectives
        self.subs: list[str] = []  # subsective adjectives
        self.used_to = False
        self.postulates: list[tuple[str, str]] = []
        for d in self.decomp.values():
            self._collect(d)
        # In M, a noun under a subsective adjective is a type.
        self.typed_nouns = [d[3] for d in self._parts() if d[0] == "adj" and d[2] == "subsective"]

    def _parts(self):
        for d in self.decomp.values():
            yield d[1] if d[0] == "usedTo" else d

    def _collect(self, d):
        if d[0] == "usedTo":
            self.used_to = True
            d = d[1]
        if d[0] == "noun":
            self._add(self.nouns, d[1])
            return
        _t, a, kind, n = d
        self._add(self.nouns, n)
        if kind == "intersective":
            self._add(self.inter, a)
        elif kind == "subsective":
            self._add(self.subs, a)
        else:
            raise Unsupported(f"{kind} adjective {a}")

    @staticmethod
    def _add(lst, x):
        if x not in lst:
            lst.append(x)

    # -- what the encoding states ---------------------------------------
    def intension(self, p: str) -> bool:
        """W: decomposed nouns and adjectives are intensions."""
        return self.enc == "W" and (p in self.nouns or p in self.inter)

    def at(self, p: str) -> str:
        return f"({p} w₀)" if self.intension(p) else p

    def cls(self, d) -> str:
        """A noun phrase's class, a term of type `A → Prop`."""
        if d[0] == "noun":
            if self.enc == "M" and d[1] in self.typed_nouns:
                return f"(IsA e{gen_encodings._type_name(d[1])})"
            return self.at(d[1])
        _t, a, kind, n = d
        if kind == "intersective":
            # The noun first: Phase 2's lift reads `fun x => n x ∧ …` as
            # the noun `n` restricted further.
            if self.enc == "W":
                return f"(fun x => {n} w₀ x ∧ {a} w₀ x)"
            return f"(fun x => {n} x ∧ {a} x)"
        if self.enc == "P":
            return f"({a} {n})"
        if self.enc == "W":
            return f"({a} {n} w₀)"
        ty = gen_encodings._type_name(n)
        return f"(fun x => ∃ y_m : {ty}, {a} {ty} (e{ty} y_m) ∧ e{ty} y_m = x)"

    def term(self, name: str) -> str:
        d = self.decomp[name]
        if d[0] == "usedTo":
            return f"(usedTo {self.cls(d[1])})"
        return self.cls(d)

    def make_postulates(self):
        for a in self.subs:
            if self.enc == "P":
                self.postulates.append(("subsectivity", f"∀ (c : A → Prop) x, {a} c x → c x"))
            elif self.enc == "W":
                self.postulates.append(("subsectivity", f"∀ (c : W → A → Prop) w x, {a} c w x → c w x"))
        if self.used_to:
            self.postulates.append(
                ("verb", "∀ P Q : A → Prop, (∀ x, P x → Q x) → ∀ x, usedTo P x → usedTo Q x"))

    def new_binders(self, f_unary: list[str]) -> list[str]:
        """Binders for the symbols the decomposition introduces."""
        world = "W → " if self.enc == "W" else ""
        out = ["{W : Type} (w₀ : W)"] if self.enc == "W" else []
        for p in [*self.nouns, *self.inter]:
            if p in f_unary or (self.enc == "M" and p in self.typed_nouns):
                continue
            out.append(f"({p} : {world}A → Prop) [DecidablePred {self.at(p)}]")
        if self.enc == "M":
            for n in self.typed_nouns:
                ty = gen_encodings._type_name(n)
                out.append(f"({ty} : Type) [Fintype {ty}] (e{ty} : {ty} → A)")
        for a in self.subs:
            cls = {"P": "(A → Prop)", "W": "(W → A → Prop)", "M": "Type"}[self.enc]
            out.append(f"({a} : {cls} → {world}A → Prop)")
        if self.used_to:
            out.append("(usedTo : (A → Prop) → A → Prop)")
        return out


def restate(enc: str, claim: str, decomp: dict) -> tuple[str, list[str]]:
    """F's claim with its decomposed names restated in `enc` (for M, the
    pre-lift claim); and the postulate categories it uses."""
    groups, parts = split_claim(claim)
    f_unary = gen_lifted.unary_names(groups)
    pr = Problem(enc, decomp, f_unary)
    if not pr.decomp:
        raise Unsupported("no decomposed name")
    pr.make_postulates()
    binders = []
    for g in groups:
        text = render([g])
        if gen_lifted._is_unary_group(g):
            names = g.items[: g.items.index(":")]
            plain = [n for n in names if n not in pr.decomp and not pr.intension(n)
                     and not (enc == "M" and n in pr.typed_nouns)]
            worlds = [n for n in names if n not in pr.decomp and pr.intension(n)]
            if plain:
                binders.append(f"({' '.join(plain)} : A → Prop)")
            if worlds:
                binders.append(f"({' '.join(worlds)} : W → A → Prop)")
            continue
        if g.open == "[" and g.items[0] == "DecidablePred" and len(g.items) == 2:
            p = g.items[1]
            if p in pr.decomp or (enc == "M" and p in pr.typed_nouns):
                continue
            binders.append(f"[DecidablePred {pr.at(p)}]")
            continue
        binders.append(text)
        if text == "[Fintype A]":
            binders += pr.new_binders(f_unary)

    def subst(seq):
        out = []
        for x in seq:
            if isinstance(x, Group):
                out.append(Group(x.open, subst(x.items)))
            elif isinstance(x, gen_lifted.Binder):
                out.append(gen_lifted.Binder(x.kind, x.header, subst(x.body)))
            elif x in pr.decomp:
                out.append(pr.term(x))
            elif isinstance(x, str) and pr.intension(x):
                out.append(pr.at(x))
            else:
                out.append(x)
        return out

    props = [render(subst(p)) for p in parts]
    facts = [f"({p})" for _c, p in pr.postulates]
    text = "∀ " + " ".join(binders) + ", " + " → ".join([*facts, *props])
    return text, [c for c, _p in pr.postulates], pr


def lift_m(pre: str, pr: Problem, all_pre: list[str]) -> str:
    """M: the pre-lift claim lifted as in Phase 2, with the nouns under a
    subsective adjective typed too."""
    nouns, used = gen_lifted.problem_nouns([("yes", c) for c in all_pre])
    for n in pr.typed_nouns:
        nouns.pop(n, None)
    lifted, lift = gen_lifted.lift_claim(pre, nouns, used | {"y_m"}, False)
    if lift.untyped:
        raise Unsupported("a quantifier restrictor is not a noun")
    return lifted, list(nouns)


def describe(d) -> str:
    if d[0] == "usedTo":
        return "used to be " + describe(d[1])
    if d[0] == "noun":
        return d[1]
    return f"{d[1]} ({d[2]}) {d[3]}"


def main() -> None:
    problems = {p[0]: p for p in gen_encodings.gen_claims.load_problems()}
    src = CLAIMS.read_text()
    reg = re.search(r"def registry : [^\n]*:= \[\n(.*?)\n\]", src, re.S).group(1)
    rows = {}
    for line in reg.split("\n"):
        m = re.match(r"\s*\((\d+), \.(\w+), \[(.*?)\], \[(.*?)\]\)", line)
        if m:
            rows[int(m.group(1))] = (m.group(2), re.findall(r"Claims\.(\w+)", m.group(3)),
                                     re.findall(r"Claims\.(\w+)", m.group(4)))
    defs = dict(re.findall(r"def (fracas_\w+) : Prop :=\n  (.*)", src))

    lines = [
        "-- Generated by EndToEnd/Encodings/gen_modified.py - do not hand-edit; re-run it.",
        "import EndToEnd.Claims",
        "import EndToEnd.Encodings.Typed",
        "",
        "/-!",
        "# Phase 3: the modified nouns of Section 1 in three noun encodings",
        "",
        "The 8 problems whose hand-written proof needs an added premise that a",
        "modified noun is a kind of the noun (`LEXICAL_AUDIT.md`), from F's own",
        "claims without background knowledge, with the fused modified nouns",
        "restated in P, W and M. See the generator's header and",
        "`EndToEnd/Encodings/README.md`.",
        "-/",
        "",
        "namespace FraCaS.Encodings.Modified",
        "open FraCaS FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed",
        "open scoped Classical",
        "",
    ]
    stats: dict = {"problems": {}, "skipped": {}}
    registry: dict = {enc: [] for enc in ENCODINGS}
    ids = audit_problems()
    for idn in ids:
        if idn not in rows:
            stats["skipped"][idn] = "the pipeline does not reach it"
            continue
        answer, ys, ns = rows[idn]
        try:
            decomp = decompositions(idn, problems[idn])
            built = {}
            for enc in ENCODINGS:
                pre = {n: restate(enc, defs[n], decomp) for n in ys + ns}
                if enc == "M":
                    all_pre = [t for t, _c, _p in pre.values()]
                    out = {}
                    for n, (t, cats, pr) in pre.items():
                        lifted, typed = lift_m(t, pr, all_pre)
                        out[n] = (lifted, cats, typed + pr.typed_nouns)
                    built[enc] = out
                else:
                    built[enc] = {n: (t, cats, pr.nouns) for n, (t, cats, pr) in pre.items()}
        except (Unsupported, gen_encodings.Unsupported) as err:
            stats["skipped"][idn] = str(err)
            continue
        names = sorted({n for n, d in decomp.items() if any(n in defs[c] for c in ys + ns)})
        stats["problems"][idn] = {
            "decomposed": {n: describe(decomp[n]) for n in names},
            "postulates": {enc: max((len(c) for _t, c, _n in built[enc].values()), default=0)
                           for enc in ENCODINGS},
            "postulate_kinds": {enc: sorted({k for _t, c, _n in built[enc].values() for k in c})
                                for enc in ENCODINGS},
            "M_types": sorted({x for _t, _c, n in built["M"].values() for x in n}),
        }
        for enc in ENCODINGS:
            lines.append(f"namespace {enc}")
            for n in ys + ns:
                lines += [f"def {n} : Prop :=\n  {built[enc][n][0]}", ""]
            lines += [f"end {enc}", ""]
            registry[enc].append(
                f"  ({idn}, .{answer}, [{', '.join(f'``{enc}.{n}' for n in ys)}], "
                f"[{', '.join(f'``{enc}.{n}' for n in ns)}])")
    for enc in ENCODINGS:
        lines += [
            f"/-- Encoding {enc}: (problem, gold, yes-claims, no-claims), one claim per reading. -/",
            f"def registry{enc} : List (Nat × Answer × List Lean.Name × List Lean.Name) := [",
            ",\n".join(registry[enc]),
            "]",
            "",
        ]
    lines += [
        "/-- The problems, for scoring F's own claims on the same set. -/",
        f"def problems : List Nat := [{', '.join(str(i) for i in stats['problems'])}]",
        "",
        "end FraCaS.Encodings.Modified",
        "",
    ]
    OUT.write_text("\n".join(lines))
    STATS.write_text(json.dumps(stats, indent=1, ensure_ascii=False) + "\n")
    print(f"{len(stats['problems'])} of {len(ids)} audit problems restated; skipped: {stats['skipped']}")


if __name__ == "__main__":
    main()
