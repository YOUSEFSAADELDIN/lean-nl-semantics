#!/usr/bin/env python3
"""Generate EndToEnd/Encodings/Section3.lean: the FraCaS Section 3
(anaphora) problems the end-to-end pipeline reaches through possessives,
dependencies and pronouns, stated in M (MTT) with dependent types, from
the pipeline's own resolved trees (EndToEnd/gen_claims.py), so both
encodings follow the same resolution decisions.

The pipeline (F) states a possessive or bridging definite as a
*stipulated function* on individuals ("her workstation" is
`workstationOf mary`, with `workstationOf : A → A` bound by the claim) and
an E-type pronoun as a fused description name. M follows Dependent Type
Semantics (Bekki 2014; Ranta 1994): premises that introduce something a
later phrase depends on are stated as Σ-typed *proof objects* -

- "every report has a cover page": `(x : Report) → Σ' c : CoverPage, …`,
- "R-95-103 is a report": `Σ' x : Report, eReport x = r95103`,
- "Smith attended a meeting": `Σ' m : Meeting, attend smith (eMeeting m)`,

and a possessive, bridging or E-type phrase is a *projection* of one,
found by looking for one in the context (DTS's proof search for its
`@`-operator, here a lookup): "the cover page of R-95-103" is
`(p q.1).1`. Only when the context has none is the presupposition
accommodated, as a Σ-hypothesis restricted to the possessor's type rather
than a function on every individual. `MTT/DependentAnaphora.lean` states
some of these problems the same way by hand; this generates them.

A second encoding, **D**, states the same discourses with nouns as
*predicates* over one type of entities, as Dependent Type Semantics
itself does (Bekki 2014: "a man entered" is `(Σu:(Σx:e) man(x))
enter(π₁u)`), keeping the Σ-typed proof objects: "every report has a
cover page" is `(x : E) → report x → Σ' y : E, coverPage y ∧ haveV x y`.
D differs from M only in how nouns are stated, so comparing them asks
whether M's saving (no stipulated functions) is owed to nouns as types or
to dependent types. It is written to `Section3D.lean`.

Run: `python3 EndToEnd/Encodings/gen_anaphora.py` (needs the gf binary).
Do not hand-edit the output.
"""
from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from gen_encodings import MClass, Unsupported, _adj, _kind, _type_name, gen_claims, resolved  # noqa: E402
from translate import _leaf_words, camel_name  # noqa: E402

OUT = HERE / "Section3.lean"
COUNTS = HERE / "assumptions3.json"
OUT_D = HERE / "Section3D.lean"
COUNTS_D = HERE / "assumptions3D.json"
PROBLEMS = (114, 115, 116, 117, 118, 119, 120, 131, 132, 133, 138)


@dataclass(frozen=True)
class DClass(MClass):
    """A class in D: the individuals (`E`) that are of noun `noun` and
    satisfy the further conditions. The noun's predicate is the first
    condition; a non-intersective adjective takes it as its argument."""

    noun: str = ""

    @property
    def index(self) -> str:
        if len(self.conds) == 1:
            return self.noun
        return f"(fun z => {' ∧ '.join(self.cond('z'))})"

    def add(self, cond: str) -> "DClass":
        return DClass(self.base, self.emb, (*self.conds, cond), self.noun)


def _verb(head: str) -> str:
    v = head.rsplit("_", 1)[0]
    return v + "V" if v in gen_claims.LEAN_RESERVED else v


class Discourse:
    def __init__(self, enc: str = "M"):
        self.enc = enc
        self.nouns: list[str] = []
        self.adjs: dict[str, str] = {}
        self.preds: list[str] = []  # intersective adjectives on individuals
        self.verbs: list[str] = []
        self.preps: list[str] = []
        self.names: list[str] = []
        self.counts: list[str] = []
        self.proofs: list[str] = []  # Σ-typed binders, in order
        self.assumptions: list[tuple[str, str]] = []  # (kind, description)
        self.deps: list[tuple[MClass, MClass, str]] = []  # (possessor class, noun class, proof)
        self.member: dict[str, list[tuple[MClass, str]]] = {}  # name -> [(class, witness)]
        self.events: list[tuple[str, str, MClass, str]] = []  # (subject, verb, class, witness)
        self.cache: dict = {}
        self.facts: list[str] = []  # accommodated presuppositions that are plain facts ("female mary")
        self._n = 0

    def fresh(self, p):
        self._n += 1
        return f"{p}{self._n}"

    def _add(self, lst, x):
        if x not in lst:
            lst.append(x)

    # -- lexicon -------------------------------------------------------
    def noun(self, n):
        self._add(self.nouns, n)
        if self.enc == "D":
            return DClass("E", "id", (f"{n} §",), n)
        return MClass(_type_name(n), f"e{_type_name(n)}")

    def forall(self, cls, x, body):
        """`∀ x` of class `cls`, with `body`. In D the noun's predicate gets
        a named hypothesis, `h{x}`, which a dependency is applied to."""
        conds = cls.cond(x)
        if self.enc == "D":
            return f"∀ {x} : E, ∀ h{x} : {conds[0]}, {' → '.join([*conds[1:], body])}"
        return f"∀ {x} : {cls.base}, {' → '.join([*conds, body])}"

    def name(self, np):
        n = camel_name(_leaf_words(np))
        self._add(self.names, n)
        return n

    def verb(self, head):
        v = _verb(head)
        self._add(self.verbs, v)
        return v

    def cn(self, t):
        if t.head in ("UseN", "CompoundCN"):
            return self.noun(camel_name(_leaf_words(t)))
        if t.head == "AdjCN" and len(t.args) == 2:
            a = _adj(t.args[0])
            base = self.cn(t.args[1])
            kind = _kind(a)
            if kind == "intersective":
                self._add(self.preds, a)
                return base.add(f"{a} {base.elt('§')}")
            if kind in ("subsective", "dimensional"):
                self.adjs[a] = kind
                return base.add(f"{a} {base.index} {base.elt('§')}")
            raise Unsupported(f"{kind} adjective in Section 3")
        if t.head == "AdvCN" and len(t.args) == 2 and t.args[1].head == "PrepNP":
            base = self.cn(t.args[0])
            return base.add(self._pp(t.args[1], base.elt("§")))
        raise Unsupported(f"CN {t.head}")

    def _pp(self, pp, x):
        p = pp.args[0].head.rsplit("_", 1)[0].split("8")[0] + "P"
        self._add(self.preps, p)
        return f"{p} {x} {self.term(pp.args[1])}"

    # -- resolution ----------------------------------------------------
    def dependent(self, possessor, possessor_cls, noun_cls, gender=None):
        """The `noun_cls` that `possessor` has: a projection of a
        dependency or witness in the context, or an accommodated one."""
        key = (possessor, repr(noun_cls))
        if key in self.cache:
            return self.cache[key]
        if gender:
            self._add(self.preds, gender)
        if possessor_cls is not None:  # a bound variable of that class
            proof = next((p for c, n, p in self.deps if c == possessor_cls and n == noun_cls), None)
            if proof is None:
                proof = self._dependency(possessor_cls, noun_cls, accommodated=True, gender=gender)
            arg = f"{possessor} h{possessor}" if self.enc == "D" else possessor
            term = f"({proof} {arg}).1"
        else:  # a name
            term = None
            for cls, witness in self.member.get(possessor, []):
                proof = next((p for c, n, p in self.deps if c == cls and n == noun_cls), None)
                if proof is not None:
                    arg = f"{witness}.1 {witness}.2.1" if self.enc == "D" else f"{witness}.1"
                    term = f"({proof} {arg}).1"
                    break
            if term is None:
                w = self.fresh("acc")
                self.proofs.append(f"({w} : Σ' y : {noun_cls.base}, "
                                   f"{' ∧ '.join([*noun_cls.cond('y'), f'haveV {possessor} {noun_cls.elt(chr(121))}'])})")
                self.assumptions.append(("accommodated", f"{possessor}'s {noun_cls.base}"))
                self._add(self.verbs, "haveV")
                if gender:
                    self.facts.append(f"{gender} {possessor}")
                term = f"{w}.1"
        self.cache[key] = term
        return term

    def _dependency(self, cls, noun_cls, accommodated, gender=None):
        p = self.fresh("dep")
        conds = [*noun_cls.cond("y"), f"haveV {cls.elt('x')} {noun_cls.elt('y')}"]
        if gender:
            conds = [f"{gender} {cls.elt('x')}", *conds]
        domain = f"(x : E) → {cls.cond('x')[0]} →" if self.enc == "D" else f"(x : {cls.base}) →"
        self.proofs.append(f"({p} : {domain} Σ' y : {noun_cls.base}, {' ∧ '.join(conds)})")
        self.assumptions.append(("accommodated" if accommodated else "asserted", f"{cls.base} → {noun_cls.base}"))
        self._add(self.verbs, "haveV")
        self.deps.append((cls, noun_cls, p))
        return p

    # -- terms and clauses ---------------------------------------------
    def term(self, np):
        if np.head == "UsePN":
            return self.name(np)
        raise Unsupported(f"term {np.head}")

    def possessive(self, det, cn, subject_term, subject_cls):
        """`her N` / `NAME's N` as an individual."""
        q = det.args[0]
        noun = self.cn(cn)
        if q.head == "PossPron":
            gender = {"she_Pron": "female", "he_Pron": "male"}.get(q.args[0].head)
            if gender is None:
                raise Unsupported("possessive pronoun")
            return noun.elt(self.dependent(subject_term, subject_cls, noun, gender))
        if q.head == "GenNP":
            return noun.elt(self.dependent(self.term(q.args[0]), None, noun))
        raise Unsupported("possessive")

    def obj(self, v, np, subj, subj_cls):
        """`subj V np` as a proposition."""
        rel = lambda y: f"{v} {subj} {y}"
        if np.head == "AdvNP" and np.args[1].head == "PrepNP" and np.args[0].head == "DetCN" \
                and np.args[0].args[0].head == "DetQuant" and np.args[0].args[0].args[0].head == "IndefArt":
            inner, pp = np.args
            return self._indef(v, inner, subj, extra=pp)
        if np.head == "DetCN" and np.args[0].head == "DetQuant":
            q, num = np.args[0].args
            cn = np.args[1]
            if q.head == "IndefArt" and num.head == "NumSg":
                return self._indef(v, np, subj)
            if q.head in ("PossPron", "GenNP"):
                return rel(self.possessive(np.args[0], cn, subj, subj_cls))
            if q.head == "DefArt" and num.head == "NumSg" and cn.head == "RelCN":
                return rel(self.description(cn))
        if np.head == "FunTermNP":
            noun = self.cn(np.args[0])
            return rel(noun.elt(self.dependent(self.term(np.args[1]), None, noun)))
        if np.head == "PredetNP" and np.args[0].head == "all_Predet":
            cls = self.relative(np.args[1].args[1])
            x = self.fresh("x")
            return f"∀ {x} : {cls.base}, {' → '.join([*cls.cond(x), rel(cls.elt(x))])}"
        if np.head == "DetCN" and np.args[0].head == "several_Det":
            cls = self.cn(np.args[1])
            self._add(self.counts, "severalCount")
            s = self.fresh("s")
            return (f"∃ {s} : Finset {cls.base}, severalCount ≤ {s}.card ∧ "
                    f"∀ y ∈ {s}, {' ∧ '.join([*cls.cond('y'), rel(cls.elt('y'))])}")
        raise Unsupported(f"object {np.head}")

    def _indef(self, v, np, subj, extra=None):
        cls = self.cn(np.args[1])
        if extra is not None:
            cls = cls.add(self._pp(extra, cls.elt("§")))
        y = self.fresh("y")
        return f"∃ {y} : {cls.base}, {' ∧ '.join([*cls.cond(y), f'{v} {subj} {cls.elt(y)}'])}"

    def relative(self, cn):
        """`N that NAME V-ed` as a class."""
        base, rcl = cn.args
        cls = self.cn(base)
        slash = rcl.args[2]
        if slash.head != "StrandRelSlash" or slash.args[1].head != "SlashVP":
            raise Unsupported("relative clause")
        who, vs = slash.args[1].args
        v = self.verb(vs.args[0].head)
        return cls.add(f"{v} {self.term(who)} {cls.elt('§')}")

    def description(self, cn):
        """`the N that NAME V-ed`: the witness the context has for it (an
        E-type pronoun the pipeline resolved to this description)."""
        base, rcl = cn.args
        slash = rcl.args[2]
        who, vs = slash.args[1].args
        cls, subj, v = self.cn(base), self.term(who), _verb(vs.args[0].head)
        for s, verb, c, w in self.events:
            if s == subj and verb == v and c == cls:
                return cls.elt(f"{w}.1")
        raise Unsupported("description without an antecedent in the context")

    def vp(self, vp, subj, subj_cls):
        if vp.head == "ComplSlash" and vp.args[0].head == "SlashV2a":
            return self.obj(self.verb(vp.args[0].args[0].head), vp.args[1], subj, subj_cls)
        if vp.head == "UseComp":
            comp = vp.args[0]
            if comp.head == "CompCN":
                cls = self.cn(comp.args[0])
                x = self.fresh("x")
                return f"∃ {x} : {cls.base}, {' ∧ '.join([*cls.cond(x), f'{cls.elt(x)} = {subj}'])}"
            if comp.head == "CompAP" and comp.args[0].head == "PositA" and _kind(_adj(comp.args[0])) == "intersective":
                a = _adj(comp.args[0])
                self._add(self.preds, a)
                return f"{a} {subj}"
        raise Unsupported(f"VP {vp.head}")

    def clause(self, cl, premise: bool):
        """A Prop, or None when a premise became a proof object."""
        subj, vp = cl.args
        if subj.head == "UsePN":
            n = self.term(subj)
            if premise and vp.head == "UseComp" and vp.args[0].head == "CompCN":
                cls = self.cn(vp.args[0].args[0])
                w = self.fresh("is")
                self.proofs.append(f"({w} : Σ' x : {cls.base}, {' ∧ '.join([*cls.cond('x'), f'{cls.elt(chr(120))} = {n}'])})")
                self.member.setdefault(n, []).append((cls, w))
                return None
            if premise and vp.head == "ComplSlash" and vp.args[1].head == "DetCN" \
                    and vp.args[1].args[0].head == "DetQuant" and vp.args[1].args[0].args[0].head == "IndefArt":
                v = self.verb(vp.args[0].args[0].head)
                cls = self.cn(vp.args[1].args[1])
                w = self.fresh("ev")
                self.proofs.append(f"({w} : Σ' y : {cls.base}, {' ∧ '.join([*cls.cond('y'), f'{v} {n} {cls.elt(chr(121))}'])})")
                self.events.append((n, v, cls, w))
                return None
            return self.vp(vp, n, None)
        if subj.head == "DetCN":
            det, cn = subj.args
            cls = self.cn(cn)
            every = det.head in ("every_Det", "each_Det") or (
                det.head == "DetQuant" and det.args[0].head == "DefArt" and det.args[1].head == "NumSg")
            no = det.head == "DetQuant" and det.args[0].head == "no_Quant"
            if premise and every and vp.head == "ComplSlash" and vp.args[0].args[0].head == "have_V2" \
                    and vp.args[1].head == "DetCN" and vp.args[1].args[0].head == "DetQuant" \
                    and vp.args[1].args[0].args[0].head == "IndefArt":
                self._dependency(cls, self.cn(vp.args[1].args[1]), accommodated=False)
                return None
            if every or no:
                x = self.fresh("x")
                body = self.vp(vp, cls.elt(x), None)
                body = f"¬ ({body})" if no else body
                return f"∀ {x} : {cls.base}, {' → '.join([*cls.cond(x), body])}"
        if subj.head == "DetCN" and subj.args[0].head == "DetQuant" and subj.args[0].args[0].head == "GenNP" \
                and vp.head == "PassV2":
            who = self.possessive(subj.args[0], subj.args[1], None, None)
            v = self.verb(vp.args[0].head)
            return f"∃ z : E, {v} z {who}"
        raise Unsupported(f"subject {subj.head}")



def render(clauses, enc="M"):
    d = Discourse(enc)
    props = []
    for role, cl, neg in clauses:
        premise = role != "hypothesis"
        p = _clause(d, cl, premise)
        if p is not None:
            props.append(f"¬ ({p})" if neg else f"({p})")
    return d, props


def _clause(d, cl, premise):
    """A quantified subject with a possessive in its VP ("every student
    used her workstation"): the possessive depends on the bound variable."""
    subj, vp = cl.args
    if subj.head == "DetCN" and subj.args[0].head in ("every_Det", "each_Det", "DetQuant") and "PossPron" in repr(vp):
        det, cn = subj.args
        cls = d.cn(cn)
        x = d.fresh("x")
        no = det.head == "DetQuant" and det.args[0].head == "no_Quant"
        v = d.verb(vp.args[0].args[0].head)
        thing = d.possessive(vp.args[1].args[0], vp.args[1].args[1], x, cls)
        body = f"{v} {cls.elt(x)} {thing}"
        body = f"¬ ({body})" if no else body
        return d.forall(cls, x, body)
    return d.clause(cl, premise)


def claim(clauses, enc="M"):
    d, props = render(clauses, enc)
    premises, hyp = props[:-1], props[-1]
    b = ["{E : Type}"]
    if enc == "D":
        if d.nouns:
            b.append(f"({' '.join(d.nouns)} : E → Prop)")
        for a in d.adjs:
            b.append(f"({a} : (E → Prop) → E → Prop)")
    else:
        for n in d.nouns:
            b.append(f"({_type_name(n)} : Type) (e{_type_name(n)} : {_type_name(n)} → E)")
        for a in d.adjs:
            b.append(f"({a} : Type → E → Prop)")
    if d.preds:
        b.append(f"({' '.join(d.preds)} : E → Prop)")
    if d.verbs:
        b.append(f"({' '.join(d.verbs)} : E → E → Prop)")
    if d.preps:
        b.append(f"({' '.join(d.preps)} : E → E → Prop)")
    if d.names:
        b.append(f"({' '.join(d.names)} : E)")
    if d.counts:
        b.append(f"({' '.join(d.counts)} : Nat)")
    b += d.proofs
    head = "∀ " + " ".join(b) + ", "
    facts = [f"({f})" for f in d.facts] + (["(severalCount ≥ 2)"] if d.counts else [])
    yes = head + " → ".join([*facts, *premises, hyp])
    no = head + " → ".join([*facts, *premises, f"¬ {hyp}"])
    return yes, no, d.assumptions


def main() -> None:
    problems = {p[0]: p for p in gen_claims.load_problems()}
    trees = {}
    for idn in PROBLEMS:
        _i, premises, hypothesis, _a = problems[idn]
        try:
            trees[idn] = resolved(idn, premises, hypothesis)
        except Unsupported as err:
            trees[idn] = err
    write(problems, trees, "M", OUT, COUNTS, "S3",
          "FraCaS Section 3 in M, with dependent types")
    write(problems, trees, "D", OUT_D, COUNTS_D, "S3D",
          "FraCaS Section 3 in D: nouns as predicates, with dependent types")


def write(problems, trees, enc, out, counts_path, ns, title) -> None:
    lines = [
        "-- Generated by EndToEnd/Encodings/gen_anaphora.py - do not hand-edit; re-run it.",
        "import Mathlib",
        "import LeanNLSemantics.FraCaS.Types",
        "",
        "/-!",
        f"# {title}",
        "",
        "From the end-to-end pipeline's own resolved trees; see the generator's",
        "header and `EndToEnd/Encodings/README.md`.",
        "-/",
        "",
        f"namespace FraCaS.Encodings.{ns}",
        "",
    ]
    registry, counts, skipped = [], {}, {}
    for idn in PROBLEMS:
        _i, premises, hypothesis, answer = problems[idn]
        try:
            if isinstance(trees[idn], Exception):
                raise trees[idn]
            yes, no, assumed = claim(trees[idn], enc)
        except Unsupported as err:
            skipped[idn] = str(err)
            continue
        lines += [f"def fracas_{idn:03d}_yes : Prop :=\n  {yes}", "", f"def fracas_{idn:03d}_no : Prop :=\n  {no}", ""]
        registry.append(f"  ({idn}, .{answer}, ``fracas_{idn:03d}_yes, ``fracas_{idn:03d}_no)")
        counts[idn] = assumed
    lines += [
        "/-- (problem, gold, yes-claim, no-claim). -/",
        "def registry : List (Nat × FraCaS.Answer × Lean.Name × Lean.Name) := [",
        ",\n".join(registry),
        "]",
        "",
        f"end FraCaS.Encodings.{ns}",
        "",
    ]
    out.write_text("\n".join(lines))
    counts_path.write_text(json.dumps({"skipped": skipped, "assumptions": counts}, indent=1) + "\n")
    print(f"{enc}: {len(registry)} problems; skipped: {skipped}")


if __name__ == "__main__":
    main()
