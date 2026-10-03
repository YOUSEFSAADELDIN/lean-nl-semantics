#!/usr/bin/env python3
"""Generate LeanNLSemantics/FraCaS/Section1/Monotonicity/BlindEvalUnknown.lean.

Extends BlindEval.lean's methodology (take a theorem's *type* only, never
its hand-written proof, and let the certified tactic chain decide
yes/no/unknown) to the FraCaS problems BlindEval.lean's own scan skips as
"not entailment-shaped": the `.unknown`/`.undef` problems in Sections 1-2,
each represented in the real corpus not as a single theorem but as a
`_dir1`/`_dir2` countermodel pair (two concrete models, over `Bool`/`Fin n`,
witnessing that neither direction is a validity) - see each pair's own file
for the hand-proved, CI-confirmed countermodels this generator's claims are
lifted from.

A genuine "unknown" is, by construction, NOT a valid universal claim in
either direction - so there is no provable theorem of shape "premises ->
hypothesis" to write down for these the way bare .yes/.no problems already
are. This generator does not try to write one. Instead, each entry below is
a bare `Prop`-valued `def` (no proof, no proof obligation) stating the
GENERIC form of what the problem's own dir1/dir2 pair already demonstrates
concretely: every concrete predicate/individual in the pair is replaced by
a fresh, free, schematic variable, with the SAME variable reused wherever
the identical concrete term recurs (preserving which premise shares a
predicate with which), so the generic claim is a faithful, purely
mechanical generalization of content this project has already verified
compiles and holds in some model - not a new translation from English.
`BlindEvalUnknown.lean`'s own scan command feeds each claim's *value* (the
Prop the `def` names, never a proof of it) through the exact same
`attemptClose`/`negateConclusion` pipeline BlindEval.lean already uses for
bare theorems, and expects BOTH directions to fail - that failure, not a
yes/no verdict, is itself the correct automated outcome for genuine
independence.

Several ids share the identical generic shape (FraCaS poses the same
phenomenon across near-identical paraphrases - "every"/"all"/"each"/"the
residents of", or "some"/"many"/"several" - and the existing dir1/dir2
pairs already reuse the same countermodel for these). One `def` is still
emitted per FraCaS id (not deduplicated into one shared claim) so the scan
output stays one-row-per-problem, matching every other report this project
produces; FAMILY below is purely a documentation label, not a Lean name.

Run `python3 scripts/gen_blind_eval_unknown.py` to regenerate; do not
hand-edit the output file.
"""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT_PATH = ROOT / "LeanNLSemantics" / "FraCaS" / "Section1" / "Monotonicity" / "BlindEvalUnknown.lean"

# Each entry: id -> (gold answer, family label, Lean binders, Lean claim body).
# `binders` is the full explicit/implicit argument telescope; `body` is the
# bare Prop (the arrow chain premises -> hypothesis). Together they form:
#   def fracas_<id>_claim <binders> : Prop := <body>
ENTRIES: dict[int, tuple[str, str, str, str]] = {
    12: (".undef", "AtMost-does-not-give-Some",
         "{A : Type*} [Fintype A] (P Q : A → Prop) [DecidablePred fun x => P x ∧ Q x]",
         "AtMost 2 P Q → Some P Q"),
    16: (".undef", "AtMost-does-not-give-Some",
         "{A : Type*} [Fintype A] (P Q : A → Prop) [DecidablePred fun x => P x ∧ Q x]",
         "AtMost 2 P Q → Some P Q"),
    22: (".unknown", "No-scope-independence",
         "{A : Type*} (P Q1 Q2 : A → Prop)",
         "No P Q1 → No P Q2"),
    28: (".unknown", "AtMost-chain-converse",
         "{A : Type*} [Fintype A] (Committee Portugal People SouthernEurope : A → Prop) "
         "[DecidablePred fun x => Committee x ∧ Portugal x] "
         "[DecidablePred fun x => Committee x ∧ SouthernEurope x]",
         "AtMost 1 Committee Portugal → Every Committee People → "
         "Every (fun x => People x ∧ Portugal x) SouthernEurope → AtMost 1 Committee SouthernEurope"),
    30: (".unknown", "No-scope-independence",
         "{A : Type*} (P Q1 Q2 : A → Prop)",
         "No P Q1 → No P Q2"),
    32: (".unknown", "AtMost-scope-independence",
         "{A : Type*} [Fintype A] (n : Nat) (P Q1 Q2 : A → Prop) "
         "[DecidablePred fun x => P x ∧ Q1 x] [DecidablePred fun x => P x ∧ Q2 x]",
         "AtMost n P Q1 → AtMost n P Q2"),
    33: (".unknown", "Some-scope-independence",
         "{A : Type*} (P Q1 Q2 : A → Prop)",
         "Some P Q1 → Some P Q2"),
    34: (".unknown", "Every-converse-chain",
         "{A : Type*} (Dom Travel Person RightToLive : A → Prop)",
         "Every Dom Travel → Every Dom Person → "
         "Every (fun x => Person x ∧ RightToLive x) Travel → Every Dom RightToLive"),
    35: (".unknown", "Every-converse-chain",
         "{A : Type*} (Dom Travel Person RightToLive : A → Prop)",
         "Every Dom Travel → Every Dom Person → "
         "Every (fun x => Person x ∧ RightToLive x) Travel → Every Dom RightToLive"),
    36: (".unknown", "Every-converse-chain",
         "{A : Type*} (Dom Travel Person RightToLive : A → Prop)",
         "Every Dom Travel → Every Dom Person → "
         "Every (fun x => Person x ∧ RightToLive x) Travel → Every Dom RightToLive"),
    37: (".unknown", "Every-converse-chain",
         "{A : Type*} (Dom Travel Person RightToLive : A → Prop)",
         "Every Dom Travel → Every Dom Person → "
         "Every (fun x => Person x ∧ RightToLive x) Travel → Every Dom RightToLive"),
    39: (".unknown", "Some-scope-independence",
         "{A : Type*} (P Q1 Q2 : A → Prop)",
         "Some P Q1 → Some P Q2"),
    40: (".unknown", "Some-scope-independence",
         "{A : Type*} (P Q1 Q2 : A → Prop)",
         "Some P Q1 → Some P Q2"),
    41: (".unknown", "Some-scope-independence",
         "{A : Type*} (P Q1 Q2 : A → Prop)",
         "Some P Q1 → Some P Q2"),
    42: (".unknown", "Most-converse-chain",
         "{A : Type*} [Fintype A] (Dom Travel Person ResidentEurope : A → Prop) "
         "[DecidablePred Dom] [DecidablePred fun x => Dom x ∧ Travel x] "
         "[DecidablePred fun x => Dom x ∧ ResidentEurope x]",
         "Most Dom Travel → Every Dom Person → "
         "Every (fun x => Person x ∧ ResidentEurope x) Travel → Most Dom ResidentEurope"),
    43: (".unknown", "Some-chain-unique",
         "{A : Type*} (Committee People Scandinavian Swedish : A → Prop)",
         "Some Committee Scandinavian → Every Committee People → "
         "Every (fun x => People x ∧ Swedish x) Scandinavian → Some Committee Swedish"),
    45: (".unknown", "Every-scope-independence",
         "{A : Type*} (P Q1 Q2 : A → Prop)",
         "Every P Q1 → Every P Q2"),
    47: (".unknown", "AtLeast-scope-independence",
         "{A : Type*} [Fintype A] (n : Nat) (P Q1 Q2 : A → Prop) "
         "[DecidablePred fun x => P x ∧ Q1 x] [DecidablePred fun x => P x ∧ Q2 x]",
         "AtLeast n P Q1 → AtLeast n P Q2"),
    50: (".unknown", "Every-restrict-converse",
         "{A : Type*} (P Q R : A → Prop)",
         "Every P Q → Every P R → Every R Q"),
    51: (".unknown", "Every-restrict-converse",
         "{A : Type*} (P Q R : A → Prop)",
         "Every P Q → Every P R → Every R Q"),
    52: (".unknown", "Every-restrict-converse",
         "{A : Type*} (P Q R : A → Prop)",
         "Every P Q → Every P R → Every R Q"),
    53: (".unknown", "Every-restrict-converse",
         "{A : Type*} (P Q R : A → Prop)",
         "Every P Q → Every P R → Every R Q"),
    54: (".unknown", "No-Some-unrelated",
         "{A : Type*} (P1 P2 Q : A → Prop)",
         "No P1 Q → Some P2 Q"),
    56: (".unknown", "Most-restrict-widen",
         "{A : Type*} [Fintype A] (Extra Dom Scope : A → Prop) "
         "[DecidablePred Extra] [DecidablePred fun x => Extra x ∧ Scope x] "
         "[DecidablePred Dom] [DecidablePred fun x => Dom x ∧ Scope x]",
         "Most Extra Scope → Most Dom Scope"),
    58: (".unknown", "Most-restrict-narrow-conjunctive",
         "{A : Type*} [Fintype A] (Dom Extra Scope : A → Prop) "
         "[DecidablePred fun x => Dom x ∧ Extra x] "
         "[DecidablePred fun x => (Dom x ∧ Extra x) ∧ Scope x] "
         "[DecidablePred Dom] [DecidablePred fun x => Dom x ∧ Scope x]",
         "Most (fun x => Dom x ∧ Extra x) Scope → Most Dom Scope"),
    60: (".unknown", "AtMost-restrict-widen",
         "{A : Type*} [Fintype A] (n : Nat) (P1 P2 Q : A → Prop) "
         "[DecidablePred fun x => P1 x ∧ Q x] [DecidablePred fun x => P2 x ∧ Q x]",
         "AtMost n P1 Q → AtMost n P2 Q"),
    61: (".undef", "Every-restrict-widen",
         "{A : Type*} (P1 P2 Q : A → Prop)",
         "Every P1 Q → Every P2 Q"),
    62: (".undef", "No-Some-unrelated",
         "{A : Type*} (P1 P2 Q : A → Prop)",
         "No P1 Q → Some P2 Q"),
    64: (".unknown", "AtMost-restrict-widen",
         "{A : Type*} [Fintype A] (n : Nat) (P1 P2 Q : A → Prop) "
         "[DecidablePred fun x => P1 x ∧ Q x] [DecidablePred fun x => P2 x ∧ Q x]",
         "AtMost n P1 Q → AtMost n P2 Q"),
    65: (".unknown", "Some-restrict-converse",
         "{A : Type*} (P Q R : A → Prop)",
         "Some P Q → Every R P → Some R Q"),
    71: (".unknown", "Some-restrict-narrow",
         "{A : Type*} (P1 P2 Q : A → Prop)",
         "Some P1 Q → Some P2 Q"),
    72: (".unknown", "Some-restrict-narrow",
         "{A : Type*} (P1 P2 Q : A → Prop)",
         "Some P1 Q → Some P2 Q"),
    73: (".unknown", "Some-restrict-narrow",
         "{A : Type*} (P1 P2 Q : A → Prop)",
         "Some P1 Q → Some P2 Q"),
    74: (".unknown", "Most-restrict-narrow",
         "{A : Type*} [Fintype A] (Dom SubDom Scope : A → Prop) "
         "[DecidablePred Dom] [DecidablePred fun x => Dom x ∧ Scope x] "
         "[DecidablePred SubDom] [DecidablePred fun x => SubDom x ∧ Scope x]",
         "Most Dom Scope → Most SubDom Scope"),
    75: (".unknown", "Some-restrict-narrow",
         "{A : Type*} (P1 P2 Q : A → Prop)",
         "Some P1 Q → Some P2 Q"),
    77: (".undef", "Both-restrict-narrow",
         "{A : Type*} [Fintype A] (P1 P2 Q : A → Prop) "
         "[DecidablePred P1] [DecidablePred P2]",
         "Both P1 Q → Both P2 Q"),
    78: (".undef", "Neither-restrict-narrow",
         "{A : Type*} [Fintype A] (P1 P2 Q : A → Prop) "
         "[DecidablePred P1] [DecidablePred P2]",
         "Neither P1 Q → Neither P2 Q"),
    79: (".unknown", "AtLeast-restrict-narrow",
         "{A : Type*} [Fintype A] (n : Nat) (P1 P2 Q : A → Prop) "
         "[DecidablePred fun x => P1 x ∧ Q x] [DecidablePred fun x => P2 x ∧ Q x]",
         "AtLeast n P1 Q → AtLeast n P2 Q"),
    83: (".unknown", "disjunctive-syllogism-gap",
         "(S J An : Prop)",
         "(S ∨ J ∨ An) → J"),
    88: (".unknown", "Every-conjunctive-restrictor",
         "{A : Type*} (Rep Client AtMeeting : A → Prop)",
         "Every (fun x => Rep x ∧ Client x) AtMeeting → Every Rep AtMeeting"),
    91: (".unknown", "collective-vs-distributive",
         "(CollectiveFact : Prop) {A : Type*} (AtMeeting Voted : A → Prop)",
         "CollectiveFact → Every AtMeeting Voted"),
    94: (".unknown", "collective-vs-distributive",
         "(CollectiveFact : Prop) {A : Type*} (AtMeeting Voted : A → Prop)",
         "CollectiveFact → Every AtMeeting Voted"),
    95: (".unknown", "collective-vs-distributive",
         "(CollectiveFact : Prop) {A : Type*} (AtMeeting Voted : A → Prop)",
         "CollectiveFact → Every AtMeeting Voted"),
    98: (".unknown", "Some-instantiation-at-individual",
         "{A : Type*} (Fault Blamed : A → Prop) (bug32985 : A)",
         "Some Fault Blamed → Fault bug32985 → Blamed bug32985"),
    102: (".unknown", "unconnected-stronger-predicate",
          "(LikelyPoorTrader WillMakePoorTrader : Prop)",
          "LikelyPoorTrader → WillMakePoorTrader"),
    104: (".unknown", "unconnected-stronger-predicate",
          "(HasCar HasMoreThanOneCar : Prop)",
          "HasCar → HasMoreThanOneCar"),
}


def render() -> str:
    lines = [
        "-- Generated by scripts/gen_blind_eval_unknown.py - do not hand-edit;",
        "-- re-run the script instead.",
        "import LeanNLSemantics.FraCaS.Section1.GQ",
        "import LeanNLSemantics.FraCaS.Section2.Plurals",
        "",
        "/-!",
        "# Generic claims for Sections 1-2's `.unknown`/`.undef` countermodel-pair problems",
        "",
        "See `scripts/gen_blind_eval_unknown.py`'s own module docstring for what these",
        "are and how they were derived (a mechanical generalization of each problem's",
        "own already-proved `_dir1`/`_dir2` pair, not a fresh translation). Each `def`",
        "is a bare `Prop` - intentionally never proved, since a genuine independence",
        "claim is not a theorem in either direction. The quantification lives *inside*",
        "the Prop (`def foo : Prop := ∀ ..., premises → hypothesis`, not `def foo",
        "<binders> : Prop := ...`), so `BlindEvalUnknownScan.lean`'s scan can feed each",
        "one's *value* directly to the same `attemptClose`/`negateConclusion` pipeline",
        "`BlindEval.lean` already uses for bare theorems' *types* - `introAll` peels",
        "these binders exactly the same way either way.",
        "-/",
        "",
        "namespace FraCaS.Section1.Monotonicity",
        "namespace BlindEvalUnknownClaims",
        "",
    ]
    for idn in sorted(ENTRIES):
        gold, family, binders, body = ENTRIES[idn]
        lines.append(f"-- fracas_{idn} ({gold}) - {family}")
        lines.append(f"def fracas_{idn}_claim : Prop :=")
        lines.append(f"  ∀ {binders}, {body}")
        lines.append("")
    lines.append("end BlindEvalUnknownClaims")
    lines.append("")
    lines.append("/-- `(FraCaS id, gold answer, claim constant name)` for every entry above -")
    lines.append("the one list `BlindEvalUnknownScan.lean`'s scan iterates, so the set of")
    lines.append("ids covered is explicit and generated, never scraped by naming")
    lines.append("convention (which could silently pick up an unrelated declaration). -/")
    lines.append("def blindEvalUnknownRegistry : List (Nat × String × Lean.Name) :=")
    lines.append("  [")
    registry_rows = []
    for idn in sorted(ENTRIES):
        gold, _family, _binders, _body = ENTRIES[idn]
        registry_rows.append(
            f'    ({idn}, "{gold}", ``BlindEvalUnknownClaims.fracas_{idn}_claim)'
        )
    lines.append(",\n".join(registry_rows))
    lines.append("  ]")
    lines.append("")
    lines.append("end FraCaS.Section1.Monotonicity")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    OUT_PATH.write_text(render())
    print(f"wrote {OUT_PATH}: {len(ENTRIES)} claims")


if __name__ == "__main__":
    main()
