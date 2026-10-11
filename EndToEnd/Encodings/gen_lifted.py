#!/usr/bin/env python3
"""Generate EndToEnd/Encodings/Lifted.lean: every claim the end-to-end
pipeline produces (EndToEnd/Claims.lean), restated with nouns as types.

Phase 2 of the comparison (README.md here). Phases 1a and 1b re-rendered
Sections 5 and 3 from the parse trees, with M's modified nouns built from
their base noun. This phase asks a narrower question about *all* the
problems the pipeline reaches: with everything else fixed - the parse, the
readings, the background knowledge, the fused names - does stating the
quantifiers' nouns as types change what is proved? So it works on F's own
claims, not on the trees, and changes only the nouns:

- A **noun** is a one-place predicate that restricts a quantifier somewhere
  in the problem (`Every italianMan ...`, or the noun of a restrictor
  `fun x => person x ∧ ...`). It becomes a type `ItalianMan` with
  `[Fintype ItalianMan]` and an embedding into the individuals,
  `eItalianMan : ItalianMan → A`. Its `[DecidablePred]` binder goes.
- A **quantifier over a noun** ranges over its type: `Every italianMan Q`
  becomes `EveryT eItalianMan (fun _ => True) Q` - every element of
  `ItalianMan` is, as an individual, `Q` (EndToEnd/Encodings/Typed.lean).
  Verbs and adjectives stay predicates of individuals, as in Phases 1a/1b.
  A restrictor's further condition (a relative clause, the other conjunct
  of "N and M") is the second argument; a disjunction of two nouns
  ("representative or client") quantifies over their sum type. A few
  translations' explicit `∃ x, n x ∧ …` and `∀ x, n x → …` become
  `SomeT` and `EveryT` the same way.
- **Anywhere else** a noun is a predicate of individuals, stated through
  its type: `italianMan x` becomes `IsA eItalianMan x`, "x is the
  individual of some element of ItalianMan".
- `Many` and `Few`, opaque in F, are opaque at every type in M, with the
  same meaning postulates stated at every type.

Everything else is F's claim unchanged. Two variants:
- **M**: the embeddings are arbitrary functions, as in Phases 1a/1b. Two
  elements of a noun's type may be the same individual, so counting an
  `N` counts elements of `N`, not individuals - MTT's individuation
  question (Chatzikyriakidis & Luo).
- **MInj**: each embedding is injective (`Function.Injective eN`), one
  counted postulate per noun: counting `N`s counts individuals.

Run: `python3 EndToEnd/Encodings/gen_lifted.py` (reads only
EndToEnd/Claims.lean; no gf binary needed). Do not hand-edit the output.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
CLAIMS = HERE.parent / "Claims.lean"
OUT = HERE / "Lifted.lean"
STATS = HERE / "lifted.json"

# Determiner -> how many numeric arguments precede the restrictor, and how
# many scope arguments follow it.
DETERMINERS = {
    "Every": (0, 1), "Some": (0, 1), "No": (0, 1), "Most": (0, 1),
    "Both": (0, 1), "Neither": (0, 1), "Many": (0, 1), "Few": (0, 1),
    "AtLeast": (1, 1), "AtMost": (1, 1), "Exactly": (1, 1), "More": (0, 2),
}
TYPED = {d: d + "T" for d in DETERMINERS}
OPAQUE = {"Many", "Few"}
RESERVED = {*TYPED.values(), "IsA", *DETERMINERS, "A", "Type", "Prop", "Nat", "Fintype", "True", "False", "Sum", "D",
            "DecidablePred", "DecidableRel", "Function"}
VARIANTS = ("M", "MInj")


# -- a small reader for the pipeline's generated terms ----------------------

_TOKEN = re.compile(r"=>|[A-Za-z_][A-Za-z0-9_'₀-₉]*|\d+|\S")


def tokenize(s: str) -> list[str]:
    return _TOKEN.findall(s)


@dataclass
class Group:
    open: str
    items: list  # a sequence (see `read_seq`)


@dataclass
class Binder:
    kind: str  # "∀", "∃", "fun"
    header: list  # the binder's tokens, up to "," / "=>"
    body: list  # a sequence: a binder extends to the end of its group


_CLOSE = {"(": ")", "[": "]", "{": "}"}


def read_seq(toks: list[str], i: int, close: str | None):
    """A sequence of atoms (str), operators (str), Groups and Binders, up
    to `close`; returns (seq, index after it)."""
    seq: list = []
    while i < len(toks):
        t = toks[i]
        if t == close:
            return seq, i + 1
        if t in _CLOSE:
            inner, i = read_seq(toks, i + 1, _CLOSE[t])
            seq.append(Group(t, inner))
            continue
        if t in ("∀", "∃", "fun"):
            stop = "=>" if t == "fun" else ","
            j, depth = i + 1, 0
            while not (depth == 0 and toks[j] == stop):
                depth += toks[j] in _CLOSE
                depth -= toks[j] in _CLOSE.values()
                j += 1
            header = toks[i + 1:j]
            body, i = read_seq(toks, j + 1, close)
            seq.append(Binder(t, header, body))
            return seq, i
        seq.append(t)
        i += 1
    if close is not None:
        raise ValueError(f"unclosed {close}")
    return seq, i


def render(seq) -> str:
    out = []
    for x in seq:
        if isinstance(x, Group):
            out.append(x.open + render(x.items) + _CLOSE[x.open])
        elif isinstance(x, Binder):
            sep = " =>" if x.kind == "fun" else ","
            out.append(f"{x.kind} {' '.join(x.header)}{sep} {render(x.body)}")
        else:
            out.append(x)
    s = " ".join(out)
    return re.sub(r"([(\[{]) ", r"\1", re.sub(r" ([)\]}])", r"\1", s))


def is_operand(x) -> bool:
    return isinstance(x, Group) or (isinstance(x, str) and re.match(r"[A-Za-z_0-9]", x) is not None)


def spines(seq):
    """Split a sequence into runs of operands (applications) and the rest."""
    out, run = [], []
    for x in seq:
        if is_operand(x):
            run.append(x)
        else:
            if run:
                out.append(run)
                run = []
            out.append(x)
    if run:
        out.append(run)
    return out


# -- what is a noun ---------------------------------------------------------

def _fun_body(g):
    """`(fun x => body)` -> (x, body), else None."""
    if isinstance(g, Group) and g.open == "(" and len(g.items) == 1 and isinstance(g.items[0], Binder):
        b = g.items[0]
        if b.kind == "fun" and len(b.header) == 1:
            return b.header[0], b.body
    return None


_LOOSER_THAN_AND = {"∨", "→", "↔", ","}


def restrictor_shape(r, unary):
    """("noun", n, None) | ("cond", n, (x, rest)) | ("sum", (n, m), None) | None."""
    if isinstance(r, str):
        return ("noun", r, None) if r in unary else None
    fb = _fun_body(r)
    if fb is None:
        return None
    x, body = fb
    if len(body) >= 4 and body[0] in unary and body[1] == x and body[2] == "∧":
        rest = body[3:]
        if not any(isinstance(t, str) and t in _LOOSER_THAN_AND for t in rest):
            return ("cond", body[0], (x, rest))
    if len(body) == 5 and body[0] in unary and body[1] == x and body[2] == "∨" and body[3] in unary and body[4] == x:
        return ("sum", (body[0], body[3]), None)
    return None


def binder_restrictor(b, unary):
    """`∃ x, n x ∧ rest` / `∀ x, n x → rest` with `n` a noun -> (n, x, rest)."""
    if b.kind not in ("∃", "∀") or len(b.header) != 1 or len(b.body) < 4:
        return None
    x = b.header[0]
    link, looser = ("∧", _LOOSER_THAN_AND) if b.kind == "∃" else ("→", {"↔"})
    if isinstance(b.body[0], str) and b.body[0] in unary and b.body[1] == x and b.body[2] == link:
        rest = b.body[3:]
        if not any(isinstance(t, str) and t in looser for t in rest):
            return b.body[0], x, rest
    return None


def walk_binders(seq):
    for x in seq:
        if isinstance(x, Group):
            yield from walk_binders(x.items)
        elif isinstance(x, Binder):
            yield x
            yield from walk_binders(x.body)


def walk_dets(seq):
    """Every determiner application (det, args) in a sequence, nested ones included."""
    for x in seq:
        if isinstance(x, Group):
            yield from walk_dets(x.items)
        elif isinstance(x, Binder):
            yield from walk_dets(x.body)
    for sp in spines(seq):
        if isinstance(sp, list) and isinstance(sp[0], str) and sp[0] in DETERMINERS:
            yield sp[0], sp[1:]


# -- the lift ----------------------------------------------------------------

@dataclass
class Lift:
    nouns: dict  # noun predicate -> (type name, embedding name)
    used: set  # every token in the problem, to keep fresh names fresh
    unary: set = field(default_factory=set)  # the claim's one-place predicates
    untyped: int = 0  # quantifier restrictors with no noun
    sums: int = 0
    _n: int = 0
    seen_untyped: set = field(default_factory=set)

    def fresh(self, prefix):
        while True:
            self._n += 1
            v = f"{prefix}_{self._n}"
            if v not in self.used:
                return v

    def member(self, noun, e):
        return f"(IsA {self.nouns[noun][1]} {e})"

    def det(self, d, args):
        nnum, nscope = DETERMINERS[d]
        if len(args) != nnum + 1 + nscope:
            return None
        nums, r, scopes = args[:nnum], args[nnum], args[nnum + 1:]
        shape = restrictor_shape(r, self.nouns)
        if shape is None:
            # A bound variable (`Many P Q` in `Many`'s meaning postulates)
            # is not a restrictor of the English.
            key = render([r])
            if set(tokenize(key)) & self.unary and key not in self.seen_untyped:
                self.seen_untyped.add(key)
                self.untyped += 1
            return None
        kind, n, cond = shape
        if kind == "sum":
            (t1, e1), (t2, e2) = self.nouns[n[0]], self.nouns[n[1]]
            dom, emb = f"({t1} ⊕ {t2})", f"(Sum.elim {e1} {e2})"
            self.sums += 1
        else:
            dom, emb = self.nouns[n]
        if kind == "cond":
            x, rest = cond
            restr = f"(fun {x} => {self.term(rest)})"
        else:
            restr = "(fun _ => True)"
        nums = [self.term([a]) for a in nums]
        scopes = [self.term([sc]) for sc in scopes]
        if d in OPAQUE:
            # Opaque at every type: applied to the type's elements.
            y = self.fresh("y")
            at = lambda p: f"(fun ({y} : {dom}) => {p} ({emb} {y}))"  # noqa: E731
            return " ".join([d, at(restr), *map(at, scopes)])
        return " ".join([TYPED[d], *nums, emb, restr, *scopes])

    def term(self, seq) -> str:
        out = []
        for sp in spines(seq):
            if isinstance(sp, Binder):
                br = binder_restrictor(sp, self.nouns)
                if br is not None:
                    n, x, rest = br
                    det = "SomeT" if sp.kind == "∃" else "EveryT"
                    out.append(f"{det} {self.nouns[n][1]} (fun _ => True) (fun {x} => {self.term(rest)})")
                    continue
                sep = " =>" if sp.kind == "fun" else ","
                out.append(f"{sp.kind} {' '.join(sp.header)}{sep} {self.term(sp.body)}")
                continue
            if isinstance(sp, str):
                out.append(sp)
                continue
            head = sp[0]
            if isinstance(head, str) and head in DETERMINERS:
                lifted = self.det(head, sp[1:])
                if lifted is not None:
                    out.append(lifted)
                    continue
            if isinstance(head, str) and head in self.nouns and len(sp) == 2:
                out.append(self.member(head, self.term([sp[1]])))
                continue
            for x in sp:
                if isinstance(x, Group):
                    out.append(x.open + self.term(x.items) + _CLOSE[x.open])
                elif x in self.nouns:
                    out.append(f"(IsA {self.nouns[x][1]})")
                else:
                    out.append(x)
        s = " ".join(out)
        return re.sub(r"([(\[{]) ", r"\1", re.sub(r" ([)\]}])", r"\1", s))


# -- claims ------------------------------------------------------------------

_MANY = "(Many : (A → Prop) → (A → Prop) → Prop)"
_FEW = "(Few : (A → Prop) → (A → Prop) → Prop)"
_OPAQUE_MEANING = {
    "(∀ P Q : A → Prop, Many P Q → Some P Q)":
        "(∀ (D : Type) (P Q : D → Prop), Many P Q → Some P Q)",
    "(∀ P Q R : A → Prop, Many P Q → (∀ x, Q x → R x) → Many P R)":
        "(∀ (D : Type) (P Q R : D → Prop), Many P Q → (∀ x, Q x → R x) → Many P R)",
    "(∀ P Q R : A → Prop, Few P Q → (∀ x, P x → R x → Q x) → Few P R)":
        "(∀ (D : Type) (P Q R : D → Prop), Few P Q → (∀ x, P x → R x → Q x) → Few P R)",
}


def split_claim(c: str):
    """`∀ <binders>, h₁ → … → c` -> (binder groups, [premise, …, conclusion] as sequences)."""
    seq, _ = read_seq(tokenize(c), 0, None)
    assert len(seq) == 1 and isinstance(seq[0], Binder) and seq[0].kind == "∀", c[:80]
    b = seq[0]
    groups, _ = read_seq(b.header, 0, None)
    parts, cur = [], []
    for x in b.body:
        if x == "→":
            parts.append(cur)
            cur = []
        else:
            cur.append(x)
    parts.append(cur)
    return groups, parts


def _is_unary_group(g) -> bool:
    """`(p q : A → Prop)`."""
    return (isinstance(g, Group) and g.open == "(" and ":" in g.items
            and g.items[g.items.index(":") + 1:] == ["A", "→", "Prop"])


def unary_names(groups):
    out = []
    for g in groups:
        if _is_unary_group(g):
            out += g.items[: g.items.index(":")]
    return out


def lift_claim(c: str, nouns: dict, used: set, injective: bool):
    for k, v in _OPAQUE_MEANING.items():
        c = c.replace(k, v)
    groups, parts = split_claim(c)
    lift = Lift(nouns, used, set(unary_names(groups)))
    binders = []
    for g in groups:
        text = render([g])
        if text == _MANY:
            binders.append("(Many : ∀ {D : Type}, (D → Prop) → (D → Prop) → Prop)")
        elif text == _FEW:
            binders.append("(Few : ∀ {D : Type}, (D → Prop) → (D → Prop) → Prop)")
        elif g.open == "[" and g.items[0] == "DecidablePred" and g.items[1] in nouns:
            continue
        elif _is_unary_group(g):
            names = [n for n in g.items[: g.items.index(":")] if n not in nouns]
            if names:
                binders.append(f"({' '.join(names)} : A → Prop)")
        else:
            binders.append(text)
        if text == "[Fintype A]":
            for n, (ty, emb) in nouns.items():
                binders.append(f"({ty} : Type) [Fintype {ty}] ({emb} : {ty} → A)")
    props = [lift.term(p) for p in parts]
    facts = [f"(Function.Injective {emb})" for _ty, emb in nouns.values()] if injective else []
    return "∀ " + " ".join(binders) + ", " + " → ".join([*facts, *props]), lift


def problem_nouns(claims: list[str]) -> dict:
    """The problem's nouns: what restricts a quantifier in any of its claims."""
    found: list[str] = []
    used: set = set()
    # Background facts (`∀ x, P x → Q x`) relate predicates; only what the
    # English itself says counts as quantifying over a noun.
    stated = {render(p) for kind, c in claims if not kind.startswith("bk_") for p in split_claim(c)[1]}
    for kind, c in claims:
        used |= set(tokenize(c))
        groups, parts = split_claim(c)
        unary = set(unary_names(groups))
        for p in parts:
            if render(p) in stated:
                for b in walk_binders(p):
                    br = binder_restrictor(b, unary)
                    if br is not None and br[0] not in found:
                        found.append(br[0])
            for _d, args in walk_dets(p):
                nnum = DETERMINERS[_d][0]
                if len(args) <= nnum:
                    continue
                shape = restrictor_shape(args[nnum], unary)
                if shape is None:
                    continue
                kind, n, _ = shape
                for x in (n if kind == "sum" else (n,)):
                    if x not in found:
                        found.append(x)
    nouns = {}
    taken = used | RESERVED
    for n in found:
        ty = n[:1].upper() + n[1:]
        while ty in taken:
            ty += "N"
        taken.add(ty)
        emb = "e" + ty
        while emb in taken:
            emb += "'"
        taken.add(emb)
        nouns[n] = (ty, emb)
    return nouns, used


def main() -> None:
    src = CLAIMS.read_text()
    defs = re.findall(r"def (fracas_(\d+)_(\w+)) : Prop :=\n  (.*)", src)
    by_problem: dict[int, list] = {}
    for name, idn, kind, claim in defs:
        by_problem.setdefault(int(idn), []).append((name, kind, claim))
    registries = {}
    for reg in ("registry", "registryBk"):
        body = re.search(rf"def {reg} : [^\n]*:= \[\n(.*?)\n\]", src, re.S).group(1)
        registries[reg] = [line.strip().rstrip(",") for line in body.split("\n")]

    lines = [
        "-- Generated by EndToEnd/Encodings/gen_lifted.py from EndToEnd/Claims.lean - do not hand-edit.",
        "import EndToEnd.Claims",
        "import EndToEnd.Encodings.Typed",
        "",
        "/-!",
        "# Every end-to-end claim with nouns as types",
        "",
        "Phase 2 of the noun-encoding comparison: the pipeline's own claims",
        "(`EndToEnd/Claims.lean`) with each quantifier's noun stated as a type",
        "and embedded into the individuals; `M` with arbitrary embeddings,",
        "`MInj` with injective ones. See the generator's header and",
        "`EndToEnd/Encodings/README.md`.",
        "-/",
        "",
        "namespace FraCaS.Encodings.Lifted",
        "open FraCaS FraCaS.Section1 FraCaS.Section2 FraCaS.EndToEnd FraCaS.Encodings.Typed",
        "open scoped Classical",
        "",
    ]
    stats: dict = {}
    for enc in VARIANTS:
        lines.append(f"namespace {enc}")
        for idn, items in sorted(by_problem.items()):
            nouns, used = problem_nouns([(k, c) for _n, k, c in items])
            untyped = sums = 0
            for name, _kind, claim in items:
                lifted, lift = lift_claim(claim, nouns, used, enc == "MInj")
                if not nouns and tokenize(lifted) != tokenize(claim):
                    raise SystemExit(f"{name}: no noun, yet the lifted claim differs from F's")
                untyped, sums = max(untyped, lift.untyped), max(sums, lift.sums)
                lines.append(f"def {name} : Prop :=\n  {lifted}\n")
            if enc == "M":
                stats[idn] = {"nouns": list(nouns), "untyped_restrictors": untyped, "sum_types": sums}
        lines += [f"end {enc}", ""]
    for enc in VARIANTS:
        for reg, rows in registries.items():
            label = enc + ("Bk" if reg == "registryBk" else "")
            lines.append(f"def registry{label} : List (Nat × Answer × List Lean.Name × List Lean.Name) := [")
            lines.append(",\n".join("  " + r.replace("``Claims.", f"``{enc}.") for r in rows))
            lines += ["]", ""]
    typed = [str(i) for i, st in stats.items() if st["nouns"]]
    lines += [
        "/-- The problems whose claims quantify over a noun: on every other problem",
        "the lifted claim is F's, token for token (the generator checks). -/",
        f"def typed : List Nat := [{', '.join(typed)}]",
        "",
        "end FraCaS.Encodings.Lifted",
        "",
    ]
    OUT.write_text("\n".join(lines))
    STATS.write_text(json.dumps(stats, indent=1) + "\n")
    n_nouns = sum(len(s["nouns"]) for s in stats.values())
    print(f"{len(by_problem)} problems, {len(defs)} claims per variant; {n_nouns} nouns; "
          f"{sum(s['untyped_restrictors'] for s in stats.values())} untyped restrictors; "
          f"{sum(s['sum_types'] for s in stats.values())} sum types")


if __name__ == "__main__":
    main()
