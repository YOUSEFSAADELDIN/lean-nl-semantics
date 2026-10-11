#!/usr/bin/env python3
"""Generate EndToEnd/Encodings/Section5.lean: FraCaS Section 5's problems
stated in three noun encodings (see README.md here), from the same parsed
and resolved trees the end-to-end pipeline uses (EndToEnd/gen_claims.py).

The fourth encoding, F (the pipeline's own fused predicates), is
EndToEnd/Claims.lean itself.

The three encodings predicate every adjective of individuals (`e : E`) and
differ only in what fixes a non-intersective adjective's comparison
class - the noun:
- P (extensional Montague): its extension, `E → Prop`;
- W (intensional Montague): its intension, `W → E → Prop`, premises and
  hypothesis at the actual world `w₀`;
- M (MTT): its type, an opaque `Type` with an embedding into `E`
  (`eMouse : Mouse → E`); a modified noun is a subtype of its noun.

What an encoding does not supply is stated as a postulate, and the
generator records how many each claim uses (`EndToEnd/Encodings/
postulates.json`): subsectivity (P and W; built into M's subtypes),
privativity, extensional subsectivity of a dimensional adjective (a
postulate in W and M; a theorem of P, supplied but not counted), and the
degree lexicon (the same in all three).

Lexical classes come from EndToEnd/background.py, unchanged, so the three
encodings share one lexicon with the pipeline.

Run: `python3 EndToEnd/Encodings/gen_encodings.py` (needs the gf binary,
like gen_claims.py). Do not hand-edit the output.
"""
from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent
END_TO_END = HERE.parent
ROOT = END_TO_END.parent
sys.path.insert(0, str(END_TO_END))
sys.path.insert(0, str(ROOT / "gf"))

import gen_claims  # noqa: E402
from background import ANTONYMS, EXTENSIONAL_SUBSECTIVE, INTERSECTIVE, PRIVATIVE  # noqa: E402
from translate import _leaf_words, camel_name, parse_tree  # noqa: E402

OUT = HERE / "Section5.lean"
POSTULATES = HERE / "postulates.json"
PROBLEMS = range(197, 220)
ENCODINGS = ("P", "W", "M")


class Unsupported(Exception):
    pass


def _adj(a) -> str:
    """`PositA fat_A` / `fat_A` -> "fat"."""
    if a.head == "PositA":
        a = a.args[0]
    if a.args or not a.head.endswith("_A"):
        raise Unsupported(f"adjective {a.head}")
    return a.head[: -len("_A")]


def _kind(adj: str) -> str:
    if adj in INTERSECTIVE:
        return "intersective"
    if adj in PRIVATIVE:
        return "privative"
    if adj in EXTENSIONAL_SUBSECTIVE:
        return "dimensional"
    return "subsective"


def _type_name(name: str) -> str:
    return name[:1].upper() + name[1:]


@dataclass(frozen=True)
class MClass:
    """A class in M: the elements of `base` (a noun's type, or `E`) that
    satisfy `conds` (templates over `§`), seen as individuals through
    `emb`. Quantifying over the class quantifies over `base` with the
    conditions as hypotheses - the curried form of quantifying over the
    Σ-type `{x : base // conds}`, which is logically the same and leaves
    the prover no subtype elements to build. That Σ-type itself is the
    class's `index`, what a non-intersective adjective is indexed by."""

    base: str
    emb: str  # an embedding function's name, or "id"
    conds: tuple = ()

    def elt(self, v: str) -> str:
        return v if self.emb == "id" else f"({self.emb} {v})"

    def cond(self, v: str) -> list[str]:
        return [c.replace("§", v) for c in self.conds]

    @property
    def index(self) -> str:
        if not self.conds:
            return self.base
        return f"{{x : {self.base} // {' ∧ '.join(self.cond('x'))}}}"

    def add(self, cond: str) -> "MClass":
        return MClass(self.base, self.emb, (*self.conds, cond))


class Encoding:
    """Builds one problem's claim in one encoding, collecting the symbols
    it binds and the postulates it needs."""

    def __init__(self, enc: str):
        self.enc = enc
        self.nouns: list[str] = []
        self.adjs: dict[str, str] = {}  # name -> kind
        self.comparatives: list[str] = []  # "smallThan", ...
        self.compar_cn: list[str] = []  # "fatThanAs", ...
        self.verbs: list[str] = []
        self.names: list[str] = []
        self.postulates: list[tuple[str, str]] = []  # (category, prop)
        self.classes: dict[str, list] = {}  # adj -> [class, ...] it is applied to
        self._fresh = 0

    def fresh(self, prefix: str) -> str:
        """A bound variable name no other binder in the claim uses."""
        self._fresh += 1
        return f"{prefix}{self._fresh}"

    # -- symbols -------------------------------------------------------
    def _add(self, lst, x):
        if x not in lst:
            lst.append(x)

    def noun(self, n):
        self._add(self.nouns, n)
        if self.enc == "M":
            return MClass(_type_name(n), f"e{_type_name(n)}")
        return n

    def name(self, n):
        self._add(self.names, n)
        return n

    def adjective(self, a):
        self.adjs.setdefault(a, _kind(a))
        return a

    # -- classes (what a noun phrase denotes) -------------------------
    def is_member(self, c, e):
        """`e` is a member of class `c`."""
        if self.enc == "P":
            return f"{c} {e}"
        if self.enc == "W":
            return f"{c} w₀ {e}"
        x = self.fresh("x")
        return f"(∃ {x} : {c.base}, {' ∧ '.join([*c.cond(x), f'{c.elt(x)} = {e}'])})"

    def adj_holds(self, a, c, e):
        """Adjective `a`, relative to class `c` unless intersective, holds of `e`."""
        kind = self.adjs[a]
        if kind == "intersective":
            return f"{a} {e}" if self.enc != "W" else f"{a} w₀ {e}"
        self.classes.setdefault(a, [])
        if c not in self.classes[a]:
            self.classes[a].append(c)
        if self.enc == "P":
            return f"{a} {c} {e}"
        if self.enc == "W":
            return f"{a} {c} w₀ {e}"
        return f"{a} {c.index} {e}"

    def thing(self):
        """The comparison class of a predicative adjective with no noun."""
        return {"P": "(fun _ => True)", "W": "(fun _ _ => True)", "M": MClass("E", "id")}[self.enc]

    def cn(self, t):
        """A CN subtree's class."""
        if t.head in ("UseN", "CompoundCN"):
            return self.noun(camel_name(_leaf_words(t)))
        if t.head == "AdjCN" and len(t.args) == 2:
            a = self.adjective(_adj(t.args[0]))
            base = self.cn(t.args[1])
            kind = self.adjs[a]
            if kind == "intersective":
                if self.enc == "P":
                    return f"(fun e => {a} e ∧ {base} e)"
                if self.enc == "W":
                    return f"(fun w e => {a} w e ∧ {base} w e)"
                return base.add(f"{a} {base.elt('§')}")
            if kind == "privative" and self.enc == "M":
                self.classes.setdefault(a, [])
                if base not in self.classes[a]:
                    self.classes[a].append(base)
                return MClass("E", "id", (f"{a} {base.index} §",))
            if self.enc in ("P", "W"):
                self.classes.setdefault(a, [])
                if base not in self.classes[a]:
                    self.classes[a].append(base)
                return f"({a} {base})"
            self.classes.setdefault(a, [])
            if base not in self.classes[a]:
                self.classes[a].append(base)
            return base.add(f"{a} {base.index} {base.elt('§')}")
        if t.head == "ComparCN" and len(t.args) == 3:
            a = _adj(t.args[0])
            base = self.cn(t.args[1])
            other = self.np_name(t.args[2])
            rel = a + "ThanAs"
            self._add(self.compar_cn, rel)
            self._add(self.comparatives, a + "Than")
            if self.enc == "P":
                return f"(fun e => {rel} {base} e {other})"
            if self.enc == "W":
                return f"(fun w e => {rel} {base} w e {other})"
            return base.add(f"{rel} {base.index} {base.elt('§')} {other}")
        raise Unsupported(f"CN {t.head}")

    def np_name(self, np):
        if np.head == "UsePN":
            return self.name(camel_name(_leaf_words(np)))
        raise Unsupported(f"NP {np.head}")

    # -- clauses -------------------------------------------------------
    def vp(self, vp, e):
        """The VP as a proposition about `e`."""
        if vp.head == "UseComp":
            comp = vp.args[0]
            if comp.head == "CompCN":
                return self.is_member(self.cn(comp.args[0]), e)
            if comp.head == "CompNP" and comp.args[0].head == "DetCN":
                det, cn = comp.args[0].args
                if det.head == "DetQuant" and det.args[0].head == "IndefArt":
                    return self.is_member(self.cn(cn), e)
            if comp.head == "CompAP":
                ap = comp.args[0]
                if ap.head == "PositA":
                    a = self.adjective(_adj(ap))
                    return self.adj_holds(a, self.thing(), e)
                if ap.head == "ComparA":
                    a = _adj(ap.args[0])
                    rel = a + "Than"
                    self._add(self.comparatives, rel)
                    other = self.np_name(ap.args[1])
                    return f"{rel} {e} {other}" if self.enc != "W" else f"{rel} w₀ {e} {other}"
        if vp.head == "ComplSlash" and vp.args[0].head == "SlashV2a":
            v = vp.args[0].args[0].head.rsplit("_", 1)[0]
            if v in gen_claims.LEAN_RESERVED:
                v += "V"
            obj = vp.args[1]
            if obj.head == "DetCN" and obj.args[0].head == "DetQuant" and obj.args[0].args[0].head == "IndefArt":
                self._add(self.verbs, v)
                c = self.cn(obj.args[1])
                y = self.fresh("y")
                if self.enc == "M":
                    return f"∃ {y} : {c.base}, {' ∧ '.join([*c.cond(y), f'{v} {e} {c.elt(y)}'])}"
                rel = f"{v} {e} {y}" if self.enc == "P" else f"{v} w₀ {e} {y}"
                return f"∃ {y}, {self.is_member(c, y)} ∧ {rel}"
        raise Unsupported(f"VP {vp.head}")

    def clause(self, cl):
        if cl.head != "PredVP":
            raise Unsupported(f"clause {cl.head}")
        subj, vp = cl.args
        if subj.head == "UsePN":
            return self.vp(vp, self.np_name(subj))
        cn = None
        if subj.head == "DetCN" and subj.args[0].head in ("every_Det", "each_Det"):
            cn = subj.args[1]
        if subj.head == "PredetNP" and subj.args[0].head == "all_Predet" and subj.args[1].head == "DetCN":
            cn = subj.args[1].args[1]
        if cn is None:
            raise Unsupported(f"subject {subj.head}")
        c = self.cn(cn)
        if self.enc == "M":
            x = self.fresh("x")
            return f"∀ {x} : {c.base}, {' → '.join([*c.cond(x), self.vp(vp, c.elt(x))])}"
        x = self.fresh("e")
        return f"∀ {x}, {self.is_member(c, x)} → {self.vp(vp, x)}"

    # -- postulates ----------------------------------------------------
    def make_postulates(self):
        out = self.postulates
        cls = "(c : E → Prop)" if self.enc == "P" else "(c : W → E → Prop)" if self.enc == "W" else "(c : Type)"
        at = "" if self.enc != "W" else " w₀"
        for a, kind in self.adjs.items():
            if kind in ("subsective", "dimensional") and self.enc != "M" and self.classes.get(a):
                if self.enc == "P":
                    out.append(("subsectivity", f"∀ (c : E → Prop) e, {a} c e → c e"))
                else:
                    out.append(("subsectivity", f"∀ (c : W → E → Prop) w e, {a} c w e → c w e"))
            if kind == "privative":
                for c in self.classes.get(a, []):
                    if self.enc == "M":
                        out.append(("privativity", f"∀ e, {a} {c.index} e → ¬ {self.is_member(c, 'e')}"))
                    elif self.enc == "P":
                        out.append(("privativity", f"∀ (c : E → Prop) e, {a} c e → ¬ c e"))
                        break
                    else:
                        out.append(("privativity", f"∀ (c : W → E → Prop) w e, {a} c w e → ¬ c w e"))
                        break
            if kind == "dimensional":
                cs = self.classes.get(a, [])
                for c1 in cs:
                    for c2 in cs:
                        if c1 == c2:
                            continue
                        same = f"(∀ e, {self.is_member(c1, 'e')} ↔ {self.is_member(c2, 'e')})"
                        h1, h2 = self.adj_holds(a, c1, "e"), self.adj_holds(a, c2, "e")
                        category = "extensionality (theorem of P)" if self.enc == "P" else "extensionality"
                        out.append((category, f"{same} → ∀ e, {h1} → {h2}"))
        for a, b in ANTONYMS:
            if a in self.adjs and b in self.adjs:
                out.append(("degree", f"∀ {cls} e, {a} c{at} e → ¬ {b} c{at} e"))
                for x, y in ((a, b),):
                    if x + "Than" in self.comparatives:
                        out.append(("degree", f"∀ {cls} e₁ e₂, {x} c{at} e₁ → {y} c{at} e₂ → {x}Than{at} e₁ e₂"))
                    if y + "Than" in self.comparatives:
                        out.append(("degree", f"∀ {cls} e₁ e₂, {x} c{at} e₁ → {y} c{at} e₂ → {y}Than{at} e₂ e₁"))
            if a + "Than" in self.comparatives and b + "Than" in self.comparatives:
                out.append(("degree", f"∀ e₁ e₂, {a}Than{at} e₁ e₂ ↔ {b}Than{at} e₂ e₁"))
        for rel in self.comparatives:
            out.append(("degree", f"∀ e₁ e₂, {rel}{at} e₁ e₂ → ¬ {rel}{at} e₂ e₁"))
        for rel in self.compar_cn:
            a = rel[: -len("ThanAs")]
            if a in EXTENSIONAL_SUBSECTIVE:
                out.append(("degree", f"∀ {cls} e₁ e₂, {rel} c{at} e₁ e₂ → {a}Than{at} e₁ e₂"))

    def binders(self):
        b = ["{E : Type}"]
        if self.enc == "W":
            b += ["{W : Type}", "(w₀ : W)"]
        cls = {"P": "(E → Prop)", "W": "(W → E → Prop)", "M": "Type"}[self.enc]
        world = "W → " if self.enc == "W" else ""
        if self.enc == "M":
            for n in self.nouns:
                b.append(f"({_type_name(n)} : Type) (e{_type_name(n)} : {_type_name(n)} → E)")
        elif self.nouns:
            b.append(f"({' '.join(self.nouns)} : {world}E → Prop)")
        for a, kind in self.adjs.items():
            if kind == "intersective":
                b.append(f"({a} : {world}E → Prop)")
            else:
                b.append(f"({a} : {cls} → {world}E → Prop)")
        if self.comparatives:
            b.append(f"({' '.join(self.comparatives)} : {world}E → E → Prop)")
        for rel in self.compar_cn:
            b.append(f"({rel} : {cls} → {world}E → E → Prop)")
        if self.verbs:
            b.append(f"({' '.join(self.verbs)} : {world}E → E → Prop)")
        if self.names:
            b.append(f"({' '.join(self.names)} : E)")
        return b


def resolved(idn, premises, hypothesis):
    """The pipeline's resolved clauses, [(role, clause, negated)]."""
    state = (None, None, None, None, None, (), (), None)
    out = []
    for i, s in enumerate([*premises, hypothesis]):
        role = "hypothesis" if i == len(premises) else f"premise {i + 1}"
        candidates = gen_claims.ranked_readings(s)
        if not candidates:
            raise Unsupported(f"{role} does not parse")
        clauses, state, err = gen_claims._resolve_sentence(parse_tree(candidates[0]), role, state)
        if clauses is None:
            raise Unsupported(f"{role}: {err}")
        out += [(role, cl, neg) for cl, neg in clauses]
    return out


def claim(enc, clauses):
    e = Encoding(enc)
    props = []
    for _role, cl, neg in clauses:
        p = e.clause(cl)
        props.append(f"¬ ({p})" if neg else f"({p})")
    e.make_postulates()
    head = "∀ " + " ".join(e.binders()) + ", "
    facts = [f"({p})" for _c, p in e.postulates]
    premises, hyp = props[:-1], props[-1]
    yes = head + " → ".join([*facts, *premises, hyp])
    no = head + " → ".join([*facts, *premises, f"¬ {hyp}"])
    counted = [c for c, _p in e.postulates if not c.endswith("(theorem of P)")]
    return yes, no, counted


def main() -> None:
    problems = {p[0]: p for p in gen_claims.load_problems()}
    lines = [
        "-- Generated by EndToEnd/Encodings/gen_encodings.py - do not hand-edit; re-run it.",
        "import Mathlib",
        "import LeanNLSemantics.FraCaS.Types",
        "",
        "/-!",
        "# FraCaS Section 5 in three noun encodings",
        "",
        "P (extensional Montague), W (intensional Montague) and M (MTT), from the",
        "end-to-end pipeline's own parsed and resolved trees; see",
        "`EndToEnd/Encodings/README.md` and the generator's header.",
        "-/",
        "",
        "namespace FraCaS.Encodings",
        "",
    ]
    registry: dict[str, list] = {enc: [] for enc in ENCODINGS}
    counts: dict[str, dict] = {enc: {} for enc in ENCODINGS}
    skipped = {}
    for idn in PROBLEMS:
        _i, premises, hypothesis, answer = problems[idn]
        try:
            clauses = resolved(idn, premises, hypothesis)
            built = {enc: claim(enc, clauses) for enc in ENCODINGS}
        except Unsupported as err:
            skipped[idn] = str(err)
            continue
        for enc in ENCODINGS:
            yes, no, counted = built[enc]
            lines += [
                f"namespace {enc}",
                f"def fracas_{idn:03d}_yes : Prop :=\n  {yes}",
                "",
                f"def fracas_{idn:03d}_no : Prop :=\n  {no}",
                f"end {enc}",
                "",
            ]
            registry[enc].append(f"  ({idn}, .{answer}, ``{enc}.fracas_{idn:03d}_yes, ``{enc}.fracas_{idn:03d}_no)")
            counts[enc][idn] = counted
    for enc in ENCODINGS:
        lines += [
            f"/-- Encoding {enc}: (problem, gold, yes-claim, no-claim). -/",
            f"def registry{enc} : List (Nat × FraCaS.Answer × Lean.Name × Lean.Name) := [",
            ",\n".join(registry[enc]),
            "]",
            "",
        ]
    lines += ["end FraCaS.Encodings", ""]
    OUT.write_text("\n".join(lines))
    POSTULATES.write_text(json.dumps({"skipped": skipped, "postulates": counts}, indent=1) + "\n")
    print(f"{len(registry['P'])} problems in each encoding; skipped: {skipped}")


if __name__ == "__main__":
    main()
