#!/usr/bin/env python3
"""The end-to-end pipeline's confirmation checks: one `linearize` check of
FraCaS's own wording per construction the pipeline's parser needs and the
hand-built trees of the corpus's GF cross-check (gf/) never used. Run
against EndToEnd/FraCaSEndToEnd.pgf (gf/'s grammar extended with those
constructions) by gf/run_gf_tests.py's runner, in CI's build-gf job.
gen_parse_grammar.py inherits every function these checks and
gf/run_gf_tests.py's use; parse_eval.py parses their English.

Run: `python3 EndToEnd/english_checks.py` (needs a compiled
EndToEnd/FraCaSEndToEnd.pgf).
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
GF_DIR = HERE.parent / "gf"

# FraCaS's OWN wording, for the constructions the end-to-end parser
# (parse_rank.py / EndToEnd/gen_claims.py) needs but which the
# hand-built trees above never used, because they were written for the
# project's rewordings ("leading tenors THAT are excellent", "SOME Italian
# men want ..."): the `who` relative pronoun, the "there are/was NP"
# existential (FraCaS Section 1's usual hypothesis shape), the frozen
# "used to", "just one", and - for Section 4 - VP ellipsis ("so did Bill",
# "Bill didn't", "the students have too"), one-anaphora ("a blue one",
# "owns one too") and uncontracted negation ("is not"). One confirmed tree per construction is
# enough - the restricted parse grammar (gen_parse_grammar.py) inherits
# every function a confirmed tree uses, and the parser then has to find
# trees for all other sentences on its own. Labelled `english_...`, not
# `fracas_...`, so scripts/gen_gf_cross_check.py (which reads `fracas_`
# labels as premise/hypothesis roles of its own cross-check theorems)
# never mistakes one for an extra role.
ENGLISH_CHECKS = [
    (
        'english_001_hypothesis',
        'linearize UttS (UseCl (TTAnt TPast ASimul) PPos (ExistNP (DetCN (DetQuant IndefArt NumSg) (RelCN (UseN italian_N) (UseRCl (TTAnt TPast ASimul) PPos (RelVP who_RP (ComplSlash (SlashV2a become_V2) (DetCN worlds_Det (AdjCN (PositA greatest_A) (UseN tenor_N))))))))))',
        "there was an Italian who became the world's greatest tenor",
    ),
    (
        'english_002_hypothesis',
        'linearize ExistNP (DetCN (DetQuant IndefArt NumPl) (RelCN (AdjCN (PositA italian_A) (UseN man_N)) (UseRCl (TTAnt TPres ASimul) PPos (RelVP who_RP (ComplVV want_VV (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA great_A) (UseN tenor_N))))))))))',
        'there are Italian men who want to be a great tenor',
    ),
    (
        'english_015_hypothesis',
        'linearize ExistNP (DetCN (DetQuant IndefArt NumPl) (RelCN (UseN tenor_N) (UseRCl (TTAnt TFut ASimul) PPos (RelVP who_RP (ComplSlash (SlashV2a take_V2) (AdvNP (MassNP (UseN part_N)) (PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN concert_N)))))))))',
        'there are tenors who will take part in the concert',
    ),
    (
        'english_013_premise2',
        'linearize PredVP (DetCN (DetQuant IndefArt NumPl) (RelCN (AdjCN (PositA leading_A) (UseN tenor_N)) (UseRCl (TTAnt TPres ASimul) PPos (RelVP who_RP (UseComp (CompAP (PositA excellent_A))))))) (UseComp (CompAP (PositA indispensable_A)))',
        'leading tenors who are excellent are indispensable',
    ),
    (
        'english_029_premise1',
        'linearize PredVP (DetCN both_Det (UseN commissioner_N)) (ComplVV usedTo_VV (UseComp (CompCN (AdjCN (PositA leading_A) (UseN businessman_N)))))',
        'both commissioners used to be leading businessmen',
    ),
    (
        'english_105_premise1',
        'linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (PredetNP just_Predet (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) (UseN accountant_N))) (ComplSlash (SlashV2a attend_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))',
        'just one accountant attended the meeting',
    ),
    (
        'english_142_premise2',
        'linearize SoS ellDid (UsePN bill_PN)',
        'so did Bill',
    ),
    (
        'english_147_premise2',
        'linearize ElliptS (UsePN bill_PN) ellDidnt',
        "Bill didn't",
    ),
    (
        'english_149_premise2',
        'linearize TooS (ElliptS (DetCN (DetQuant DefArt NumPl) (UseN student_N)) ellHas)',
        'the students have too',
    ),
    (
        'english_155_premise2',
        'linearize TooS (UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN bill_PN) (ComplSlash (SlashV2a own_V2) anaphOne_NP)))',
        'Bill owns one too',
    ),
    (
        'english_157_premise2',
        'linearize UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN bill_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA blue_A) (UseN anaphOne_N)))))',
        'Bill owns a blue one',
    ),
    (
        'english_206_premise1',
        'linearize UseCl (TTAnt TPres ASimul) UncNeg (PredVP (UsePN fido_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA small_A) (UseN animal_N))))))',
        'Fido is not a small animal',
    ),
    (
        'english_230_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (ComplSlash (SlashV2a win_V2) (MoreThanAux (UseN order_N) (UsePN apcom_PN) ellDid)))',
        'ITEL won more orders than APCOM did',
    ),
    (
        'english_233_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (ComplSlash (SlashV2a win_V2) (MoreThanNP (UseN order_N) (UsePN apcom_PN))))',
        'ITEL won more orders than APCOM',
    ),
    (
        'english_239_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (ComplSlash (SlashV2a win_V2) (MoreThanV2 (UseN order_N) (UsePN apcom_PN) lose_V2)))',
        'ITEL won more orders than APCOM lost',
    ),
    (
        'english_248_premise1',
        'linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA fast_A (DetCN anySg_Det (UseN itelComputer_N)))))',
        'the PC-6082 is faster than any ITEL computer',
    ),
    (
        'english_342_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2V seeDo_V2V (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))) (UsePN jones_PN)))',
        'Smith saw Jones sign the contract',
    ),
    (
        'english_089_hypothesis',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (AndEveryNP (UseN representativeMasc_N) (UseN client_N)) (UseComp (CompAdv (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N))))))',
        'every representative and every client was at the meeting',
    ),
    (
        'english_093_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant DefArt NumPl) (RelCN (UseN person_N) (UseRCl (TTAnt TPast ASimul) PPos (RelVP who_RP (UseComp (CompAdv (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N))))))))) (AdVVP floatAll_AdV (AdvVP (UseV vote_V) (PrepNP for_Prep (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN chairman_N)))))))',
        'the people who were at the meeting all voted for a new chairman',
    ),
    (
        'english_104_hypothesis',
        'linearize UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt (NumCard (AdNum moreThan_AdN (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01)))))))) (CompoundCN (UseN company_N) (UseN car_N)))))',
        'Jones has more than one company car',
    ),
    (
        'english_216_premise1',
        'linearize UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN john_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (ComparCN fat_A (UseN politician_N) (UsePN bill_PN))))))',
        'John is a fatter politician than Bill',
    ),
    (
        'english_084_hypothesis',
        'linearize ExtAdvS (SubjS if_Subj (UseCl (TTAnt TPast ASimul) UncNeg (PredVP (ConjNP and_Conj (BaseNP (UsePN smith_PN) (UsePN anderson_PN))) (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))',
        'if Smith and Anderson did not sign the contract , Jones signed the contract',
    ),
    (
        'english_150_premise1',
        'linearize CommaAndS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (AdvVP (UseV go_V) (PrepNP to_Prep (UsePN paris_PN))) (PrepNP by8agent_Prep (MassNP (UseN car_N)))))) (GapS (UsePN bill_PN) (PrepNP by8agent_Prep (MassNP (UseN train_N))))',
        'John went to Paris by car , and Bill by train',
    ),
    (
        'english_151_premise1',
        'linearize CommaAndS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (AdvVP (UseV go_V) (PrepNP to_Prep (UsePN paris_PN))) (PrepNP by8agent_Prep (MassNP (UseN car_N)))))) (GapS2 (UsePN bill_PN) (PrepNP by8agent_Prep (MassNP (UseN train_N))) (PrepNP to_Prep (UsePN berlin_PN)))',
        'John went to Paris by car , and Bill by train to Berlin',
    ),
    (
        'english_145_premise2',
        'linearize AndS (ElliptAdvS (UsePN bill_PN) ellDid atFiveOClock_Adv)',
        "and Bill did at five o'clock",
    ),
    (
        'english_146_premise2',
        'linearize ElliptS (UsePN bill_PN) ellGoingTo',
        'Bill is going to',
    ),
    (
        'english_164_premise2',
        'linearize AndS (FragAdvS (PrepNP to_Prep (UsePN sue_PN)))',
        'and to Sue',
    ),
    (
        'english_165_premise2',
        'linearize FragAdvS onFriday_Adv',
        'on Friday',
    ),
    (
        'english_167_premise2',
        'linearize ButS (FragNPS (PredetNP only_Predet (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) (UseN woman_N))))',
        'but only one woman',
    ),
    (
        'english_178_premise1',
        'linearize CommaAndS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (ComplVSBare say_VS (TooS (ElliptS (UsePN peter_PN) ellDid)))))',
        'John wrote a report , and Bill said Peter did too',
    ),
    (
        'english_179_premise1',
        'linearize ExtAdvS (SubjS if_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N)))))) (ThenS (TooS (ElliptS (UsePN bill_PN) ellDid)))',
        'if John wrote a report , then Bill did too',
    ),
    (
        'english_251_hypothesis',
        'linearize UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN itel_PN) (AdVVP currently_AdV (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (AdvCN (UseN factory_N) (PrepNP in_Prep (UsePN birmingham_PN)))))))',
        'ITEL currently has a factory in Birmingham',
    ),
    (
        'english_252_premise2',
        'linearize ItIsNow (UsePN y1996_PN)',
        'it is now 1996',
    ),
    (
        'english_301_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a run_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (AdjCN (PositA own_A) (UseN business_N)))) forTwoYears_Adv))',
        'Smith ran his own business for two years',
    ),
    (
        'english_311_premise1',
        'linearize UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a leave_V2) (DetCN (DetQuant DefArt NumSg) (UseN house_N))) atAQuarterPastFive_Adv))',
        'Smith had left the house at a quarter past five',
    ),
    (
        'english_311_premise2',
        'linearize ThenS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePron she_Pron) (AdvVP (ComplSlash (SlashV2a take_V2) (DetCN (DetQuant IndefArt NumSg) (UseN taxi_N))) (PrepNP to_Prep (DetCN (DetQuant DefArt NumSg) (UseN station_N))))))',
        'then she took a taxi to the station',
    ),
    (
        'english_312_premise1',
        'linearize UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN itel_PN) (AdVVP always_AdV (AdvVP (ComplSlash (SlashV2a deliver_V2) (DetCN (DetQuant IndefArt NumPl) (UseN report_N))) late_Adv)))',
        'ITEL always delivers reports late',
    ),
    (
        'english_313_premise1',
        'linearize UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN itel_PN) (AdVVP never_AdV (AdvVP (ComplSlash (SlashV2a deliver_V2) (DetCN (DetQuant IndefArt NumPl) (UseN report_N))) late_Adv)))',
        'ITEL never delivers reports late',
    ),
    # The progressive (ProgrVP).
    (
        'english_141_hypothesis',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP someone_NP (ComplVSBare say_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePN john_PN) (PassV2 hurt_V2)))))',
        'someone said John had been hurt',
    ),
    (
        'english_273_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ProgrVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N)))))',
        'Smith was writing a report',
    ),
    (
        'english_281_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ProgrVP (ComplSlash (SlashV2a run_V2) (DetCN (DetQuant IndefArt NumSg) (UseN business_N)))) in1991_Adv))',
        'Smith was running a business in 1991',
    ),
    (
        'english_294_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ProgrVP (ComplSlash (SlashV2a run_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (AdjCN (PositA own_A) (UseN business_N))))) inTwoYears_Adv))',
        'Smith was running his own business in two years',
    ),
    (
        'english_296_hypothesis',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdvCN (UseN chain_N) (PrepNP of_Prep (MassNP (UseN business_N)))))) forMoreThanTwoYears_Adv))',
        'Smith owned a chain of business for more than two years',
    ),
    (
        'english_299_hypothesis',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (AdvVP (UseV live_V) (PrepNP in_Prep (UsePN birmingham_PN))) forExactlyAYear_Adv))',
        'Smith lived in Birmingham for exactly a year',
    ),
    (
        'english_327_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ProgrVP (ComplSlash (SlashV2a build_V2) (UsePN mtalk_PN))) in1993_Adv))',
        'ITEL was building MTALK in 1993',
    ),
    (
        'english_329_premise1',
        'linearize UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ProgrVP (AdvVP (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))) (PrepNP from_Prep (UsePN apcom_PN)))) in1993_Adv))',
        'ITEL was winning the contract from APCOM in 1993',
    ),
]


def main() -> int:
    spec = importlib.util.spec_from_file_location("run_gf_tests", GF_DIR / "run_gf_tests.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.run_checks(ENGLISH_CHECKS, str(HERE / "FraCaSEndToEnd.pgf"), str(HERE))


if __name__ == "__main__":
    sys.exit(main())
