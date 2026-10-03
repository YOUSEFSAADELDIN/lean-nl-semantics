#!/usr/bin/env python3
"""Generate LeanNLSemantics/FraCaS/BlindEvalUnknown3to9.lean.

The Sections 3-9 analogue of `gen_blind_eval_unknown.py` (see that
script's own module docstring for the full methodology - mechanical
generalization of an already-proved `_dir1`/`_dir2` countermodel pair
into a bare, unprovable, generic `Prop`, never a fresh translation from
English). The same discipline applies here: every entry below was
derived by reading the real `_dir1`/`_dir2` pair (and, for a lid of ids
with no explanatory doc comment at all, the real FraCaS English text
in `FraCaS/Data/fracas.xml`) and promoting exactly what differs between
the two models to a free variable, keeping shared structure shared.

Sections 3-9 differ from Sections 1-2 in one important way: the VAST
majority of their `.unknown`/`.undef` countermodel pairs (53 of 60) were
found to be *vacuous* `True ∧ ¬False`/`True ∧ True` stubs - the same bug
class as Sections 1-2's fracas_91/94/95/102/104, just far more common
here, since ellipsis-ambiguity (Section 4) and tense/aspect independence
(Section 7) are both *inherently* "two unconnected facts" phenomena.
Every one of those 53 was fixed in place (named, real content standing
for what the problem's own doc comment - or, absent one, the real
FraCaS English text - says it should contain) before being generalized
here; see each theorem's own updated doc comment in the corpus itself
for that fix, and `BlindEvalUnknown3to9.lean`'s own header for why a few
cases (263, 269, 271-274: state/achievement composition across "before"/
"after") deliberately use opaque Props rather than real `Nat` timestamps
- real `<`/`>` would make the composition trivially (and wrongly)
provable, since transitivity is a mathematical fact, not a linguistic
one.

Run `python3 scripts/gen_blind_eval_unknown_3to9.py` to regenerate; do
not hand-edit the output file.
"""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT_PATH = ROOT / "LeanNLSemantics" / "FraCaS" / "BlindEvalUnknown3to9.lean"

# Each entry: id -> (gold answer, family label, Lean binders, Lean claim body).
ENTRIES: dict[int, tuple[str, str, str, str]] = {
    125: (".unknown", "AtLeast-mono-scope-sharper-bound",
          "{A : Type*} [Fintype A] (missing removed : A → Prop) "
          "[DecidablePred fun x => True ∧ missing x] [DecidablePred fun x => True ∧ removed x]",
          "Exactly 2 (fun _ : A => True) missing → (∀ x, missing x → removed x) → "
          "AtLeast 8 (fun _ : A => True) removed"),
    130: (".unknown", "Every-outside-domain-independence",
          "{A : Type*} (P Q : A → Prop) (x : A)",
          "Every P Q → ¬ P x → Q x"),
    136: (".unknown", "weak-donkey-not-universal",
          "(Q : Fin 5 → Prop) [DecidablePred Q]",
          "Exactly 5 (fun _ : Fin 5 => True) (fun _ : Fin 5 => True) → "
          "((∃ _c : Fin 5, True) → ∃ c : Fin 5, True ∧ Q c) → "
          "Exactly 5 (fun _ : Fin 5 => True) Q"),
    141: (".unknown", "unconnected-stronger-predicate",
          "{A : Type*} (john bill : A) (said : A → Prop → Prop) (hurt : A → A → Prop)",
          "said john (hurt bill bill) → ∃ p, said p (hurt john john)"),
    143: (".unknown", "unconnected-stronger-predicate",
          "(SpokeBillMary SpokeAt4BillMary : Prop)",
          "SpokeBillMary → SpokeAt4BillMary"),
    156: (".unknown", "one-anaphora-not-same-witness",
          "{A : Type*} (Own1 Own2 : A → Prop)",
          "(∃ c, Own1 c) → (∃ c, Own2 c) → ∃ c, Own1 c ∧ Own2 c"),
    158: (".unknown", "unaddressed-modifier",
          "{A : Type*} (car red blue : A → Prop) (owns : A → A → Prop) (john bill : A)",
          "((∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ blue c ∧ owns bill c)) → "
          "∃ c, car c ∧ red c ∧ owns bill c"),
    161: (".unknown", "unaddressed-modifier",
          "{A : Type*} (car red fast : A → Prop) (owns : A → A → Prop) (john bill : A)",
          "((∃ c, car c ∧ red c ∧ owns john c) ∧ (∃ c, car c ∧ fast c ∧ owns bill c)) → "
          "∃ c, car c ∧ fast c ∧ red c ∧ owns bill c"),
    174: (".unknown", "Every-covers-not-covered-by",
          "{A : Type*} (johnSpokeTo billSpokeTo : A → Prop) (mary : A)",
          "Every johnSpokeTo billSpokeTo → billSpokeTo mary → johnSpokeTo mary"),
    177: (".unknown", "unconnected-stronger-predicate",
          "(JohnMadeDoubledClaim BillSaidMaryWroteReport : Prop)",
          "JohnMadeDoubledClaim → BillSaidMaryWroteReport"),
    181: (".unknown", "unconnected-stronger-predicate",
          "(BillNeededBuyCar BillBoughtCar : Prop)",
          "BillNeededBuyCar → BillBoughtCar"),
    184: (".unknown", "cross-combination-unaddressed",
          "{A : Type*} (represents : A → A → Prop) (companyOf : A → A) (smith jones : A)",
          "(represents smith (companyOf smith) ∧ represents jones (companyOf jones)) → "
          "represents smith (companyOf jones)"),
    188: (".unknown", "cross-combination-unaddressed",
          "{A : Type*} (claimedCosted : A → A → A → Prop) (smith jones : A)",
          "claimedCosted smith smith smith → claimedCosted jones smith jones"),
    192: (".unknown", "cross-combination-unaddressed",
          "(SuggestedBillFrank SuggestedCarlAlanWife : Prop)",
          "SuggestedBillFrank → SuggestedCarlAlanWife"),
    194: (".unknown", "cross-combination-unaddressed",
          "(SuggestedBillFrankBoss SuggestedCarlAlan : Prop)",
          "SuggestedBillFrankBoss → SuggestedCarlAlan"),
    200: (".unknown", "unconnected-stronger-predicate",
          "(WasFormerSuccessfulUnivStudent CurrentlySuccessful : Prop)",
          "WasFormerSuccessfulUnivStudent → CurrentlySuccessful"),
    201: (".unknown", "unconnected-stronger-predicate",
          "(WasFormerSuccessfulUnivStudent CurrentlyUnivStudent : Prop)",
          "WasFormerSuccessfulUnivStudent → CurrentlyUnivStudent"),
    206: (".unknown", "contrary-not-contradictory",
          "{A : Type*} (small large : A → Prop) (x : A)",
          "¬ small x → large x"),
    207: (".unknown", "contrary-not-contradictory",
          "{A : Type*} (small large : A → Prop) (x : A)",
          "¬ large x → small x"),
    213: (".undef", "comparison-class-presupposition-failure",
          "(MiceSmallAnimalsAndMickeyLargeMouse MickeyIsSmall : Prop)",
          "MiceSmallAnimalsAndMickeyLargeMouse → MickeyIsSmall"),
    215: (".unknown", "intensional-comparison-class",
          "(CompetentAsLegalAuth CompetentAsLawLect : Prop)",
          "CompetentAsLegalAuth → CompetentAsLawLect"),
    217: (".unknown", "intensional-comparative",
          "(CleverPoliticianThanBill ClevererThanBill : Prop)",
          "CleverPoliticianThanBill → ClevererThanBill"),
    219: (".unknown", "non-default-comparison-class",
          "(CleverPolitician CleverKim : Prop)",
          "CleverPolitician → CleverKim"),
    221: (".unknown", "comparative-no-absolute-bound",
          "{A : Type*} (fasterThan : A → A → Prop) (fast : A → Prop) (pc itel : A)",
          "fasterThan pc itel → fast pc"),
    222: (".unknown", "comparative-no-absolute-bound",
          "{A : Type*} (fasterThan : A → A → Prop) (fast : A → Prop) (pc itel : A)",
          "(fasterThan pc itel ∧ fast pc) → fast itel"),
    225: (".unknown", "comparative-no-absolute-bound",
          "{A : Type*} (asFastAs : A → A → Prop) (fast : A → Prop) (pc itel : A)",
          "asFastAs pc itel → fast pc"),
    226: (".unknown", "comparative-no-absolute-bound",
          "{A : Type*} (asFastAs : A → A → Prop) (fast : A → Prop) (pc itel : A)",
          "(asFastAs pc itel ∧ fast pc) → fast itel"),
    228: (".unknown", "as-fast-as-not-strict",
          "{A : Type*} (asFastAs fasterThan : A → A → Prop) (pc itel : A)",
          "asFastAs pc itel → fasterThan pc itel"),
    231: (".unknown", "cardinal-comparative-no-positivity",
          "(wonITEL wonAPCOM : Nat)",
          "wonITEL > wonAPCOM → wonAPCOM > 0"),
    234: (".unknown", "cardinal-comparative-no-positivity",
          "(wonITEL wonAPCOM : Nat)",
          "wonITEL > wonAPCOM → wonAPCOM > 0"),
    240: (".unknown", "cardinal-comparative-no-positivity",
          "(wonITEL lostAPCOM : Nat)",
          "wonITEL > lostAPCOM → lostAPCOM > 0"),
    247: (".unknown", "Some-instantiation-at-individual",
          "{A : Type*} (fasterThan : A → A → Prop) (itelComputer : A → Prop) (pc itelzx : A)",
          "Some itelComputer (fasterThan pc) → itelComputer itelzx → fasterThan pc itelzx"),
    253: (".unknown", "since-at-least-once-not-pointwise",
          "(P : Nat → Prop)",
          "(∃ y, 1992 ≤ y ∧ y ≤ 1996 ∧ P y) → P 1993"),
    254: (".unknown", "since-at-least-once-not-pointwise",
          "(P : Nat → Prop)",
          "(∃ y, 1992 ≤ y ∧ y ≤ 1996 ∧ P y) → P 1993"),
    256: (".unknown", "since-at-least-once-not-pointwise",
          "(P : Nat → Prop)",
          "(∃ y, 1992 ≤ y ∧ y ≤ 1996 ∧ P y) → P 1993"),
    263: (".unknown", "state-achievement-composition-fails",
          "(SmithPresentAfterJonesLeft JonesLeftAfterAndersonPresent "
          "SmithPresentAfterAndersonPresent : Prop)",
          "(SmithPresentAfterJonesLeft ∧ JonesLeftAfterAndersonPresent) → "
          "SmithPresentAfterAndersonPresent"),
    269: (".unknown", "repeated-bare-event-no-shared-occasion",
          "(SmithSwam JonesSwam SmithSwamBeforeJonesSwam JonesSwamAfterSmithSwam : Prop)",
          "(SmithSwam ∧ JonesSwam ∧ SmithSwamBeforeJonesSwam) → JonesSwamAfterSmithSwam"),
    271: (".unknown", "repeated-bare-event-no-shared-occasion",
          "(SmithPresent JonesPresent SmithPresentAfterJonesPresent "
          "JonesPresentBeforeSmithPresent : Prop)",
          "(SmithPresent ∧ JonesPresent ∧ SmithPresentAfterJonesPresent) → "
          "JonesPresentBeforeSmithPresent"),
    272: (".unknown", "repeated-bare-event-no-shared-occasion",
          "(SmithPresent JonesPresent SmithPresentBeforeJonesPresent "
          "JonesPresentAfterSmithPresent : Prop)",
          "(SmithPresent ∧ JonesPresent ∧ SmithPresentBeforeJonesPresent) → "
          "JonesPresentAfterSmithPresent"),
    273: (".unknown", "repeated-bare-event-no-shared-occasion",
          "(SmithWritingReport JonesWritingReport SmithWritingBeforeJonesWriting "
          "JonesWritingAfterSmithWriting : Prop)",
          "(SmithWritingReport ∧ JonesWritingReport ∧ SmithWritingBeforeJonesWriting) → "
          "JonesWritingAfterSmithWriting"),
    274: (".unknown", "repeated-bare-event-no-shared-occasion",
          "(SmithWritingReport JonesWritingReport SmithWritingAfterJonesWriting "
          "JonesWritingBeforeSmithWriting : Prop)",
          "(SmithWritingReport ∧ JonesWritingReport ∧ SmithWritingAfterJonesWriting) → "
          "JonesWritingBeforeSmithWriting"),
    275: (".unknown", "before-non-factive",
          "(SmithLeftBeforeLostTemper SmithLostTemper : Prop)",
          "SmithLeftBeforeLostTemper → SmithLostTemper"),
    277: (".unknown", "bare-state-no-projection",
          "(P : Nat → Prop)",
          "P 1991 → P 1992"),
    280: (".unknown", "bare-state-no-projection",
          "(P : Nat → Prop)",
          "P 1991 → P 1992"),
    281: (".unknown", "bare-state-no-projection",
          "(P : Nat → Prop)",
          "P 1991 → P 1992"),
    283: (".unknown", "bare-state-no-projection",
          "(P : Nat → Prop)",
          "P 1991 → P 1992"),
    285: (".unknown", "in-N-hours-not-exact",
          "(spentHours : Nat)",
          "spentHours ≤ 2 → spentHours = 2"),
    287: (".unknown", "in-N-hours-independent-of-smaller-N",
          "(spentHours : Nat)",
          "spentHours ≤ 2 → spentHours ≤ 1"),
    292: (".unknown", "inception-vs-duration",
          "(inceptionYears spentYearsRunning : Nat)",
          "inceptionYears = 2 → spentYearsRunning = 2"),
    293: (".unknown", "inception-vs-duration",
          "(inceptionYears spentYearsRunning : Nat)",
          "inceptionYears = 2 → spentYearsRunning > 2"),
    295: (".unknown", "inception-vs-duration",
          "(inceptionYearsChain ownedChainYears : Nat)",
          "inceptionYearsChain = 2 → ownedChainYears = 2"),
    296: (".unknown", "inception-vs-duration",
          "(inceptionYearsChain ownedChainYears : Nat)",
          "inceptionYearsChain = 2 → ownedChainYears > 2"),
    304: (".unknown", "for-N-hours-no-culmination",
          "(WroteForTwoHours FinishedReport : Prop)",
          "WroteForTwoHours → FinishedReport"),
    308: (".unknown", "forall-exists-not-exists-forall",
          "{Week Rep : Type*} (wroteTo : Week → Rep → Prop)",
          "(∀ w, ∃ r, wroteTo w r) → ∃ r, ∀ w, wroteTo w r"),
    327: (".unknown", "imperfective-paradox",
          "(wasBuilding finished : Nat → Prop)",
          "wasBuilding 1993 → finished 1993"),
    329: (".unknown", "imperfective-paradox",
          "(wasWinningContract wonAContract : Nat → Prop)",
          "wasWinningContract 1993 → wonAContract 1993"),
    335: (".unknown", "non-factive-attitude-verb",
          "(BelievedWon Won : Prop)",
          "BelievedWon → Won"),
    337: (".unknown", "non-implicative-control-verb",
          "(TriedToWin Won : Prop)",
          "TriedToWin → Won"),
    340: (".unknown", "perception-opacity-to-inferred",
          "(Q : Prop)",
          "True → (True → True) → (True → True) → Q"),
    341: (".unknown", "perception-opacity-to-inferred",
          "(Q : Prop)",
          "True → (True → True) → (True → True) → Q"),
}


def render() -> str:
    lines = [
        "-- Generated by scripts/gen_blind_eval_unknown_3to9.py - do not hand-edit;",
        "-- re-run the script instead.",
        "import LeanNLSemantics.FraCaS.Section1.GQ",
        "",
        "/-!",
        "# Generic claims for Sections 3-9's `.unknown`/`.undef` countermodel-pair problems",
        "",
        "See `scripts/gen_blind_eval_unknown_3to9.py`'s own module docstring for what",
        "these are and how they were derived - the Sections 3-9 analogue of",
        "`Section1/Monotonicity/BlindEvalUnknown.lean`, same methodology, same reason",
        "each `def` is a bare, never-proved `Prop`. Most of the state/achievement",
        "temporal-composition claims (263, 269, 271-274) use opaque `Prop` variables",
        "rather than real `Nat` timestamps even though their own corpus theorems are",
        "about event ordering - using real `<`/`>` here would make the claim provable",
        "via plain transitivity, which is mathematically true but would wrongly close",
        "as \"yes\" a case FraCaS gives `.unknown` (the composition fails for linguistic,",
        "not arithmetic, reasons no `Nat` encoding captures faithfully).",
        "-/",
        "",
        "namespace FraCaS",
        "namespace BlindEvalUnknownClaims3to9",
        "",
        "open FraCaS.Section1",
        "",
    ]
    for idn in sorted(ENTRIES):
        gold, family, binders, body = ENTRIES[idn]
        lines.append(f"-- fracas_{idn} ({gold}) - {family}")
        lines.append(f"def fracas_{idn}_claim : Prop :=")
        lines.append(f"  ∀ {binders}, {body}")
        lines.append("")
    lines.append("end BlindEvalUnknownClaims3to9")
    lines.append("")
    lines.append("/-- `(FraCaS id, gold answer, claim constant name)` for every entry above -")
    lines.append("the one list `BlindEvalUnknown3to9Scan.lean`'s scan iterates. -/")
    lines.append("def blindEvalUnknownRegistry3to9 : List (Nat × String × Lean.Name) :=")
    lines.append("  [")
    registry_rows = []
    for idn in sorted(ENTRIES):
        gold, _family, _binders, _body = ENTRIES[idn]
        registry_rows.append(
            f'    ({idn}, "{gold}", ``BlindEvalUnknownClaims3to9.fracas_{idn}_claim)'
        )
    lines.append(",\n".join(registry_rows))
    lines.append("  ]")
    lines.append("")
    lines.append("end FraCaS")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    OUT_PATH.write_text(render())
    print(f"wrote {OUT_PATH}: {len(ENTRIES)} claims")


if __name__ == "__main__":
    main()
