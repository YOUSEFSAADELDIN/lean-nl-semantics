concrete FraCaSLogicEng of FraCaSLogic =
  CatEng, StructuralEng, SentenceEng, NounEng, AdjectiveEng, VerbEng, DictEng
  ** open ParadigmsEng in {
  lin
    really_AdA = mkAdA "really" ;
}

-- Confirmed working (see gf/NOTES.md), building with:
--   gf -make -path=.:$GF_LIB_PATH/alltenses:$GF_LIB_PATH/prelude FraCaSLogicEng.gf
--   gf -path=$GF_LIB_PATH/alltenses:$GF_LIB_PATH/prelude FraCaSLogic.pgf
--
-- FraCaS problem 2's premise ("Every Italian man wants to be a great
-- tenor."):
--   linearize PredVP (DetCN every_Det (AdjCN (PositA italian_A) (UseN man_N)))
--                     (ComplVV want_VV (UseComp (CompCN (AdjCN (PositA great_A) (UseN tenor_N)))))
--   => "every Italian man wants to be a great tenor"
--
-- FraCaS problem 7's premise ("Some great tenors are Swedish."):
--   linearize PredVP (DetCN somePl_Det (AdjCN (PositA great_A) (UseN tenor_N)))
--                     (UseComp (CompAP (PositA swedish_A)))
--   => "some great tenors are Swedish"
--
-- FraCaS problem 6's premise ("No really great tenors are modest."),
-- NOT YET CONFIRMED (needs a linearize round-trip on the actual
-- toolchain): "no" is Quant-typed, not Det-typed, so the subject is
-- DetCN wrapping `DetQuant no_Quant NumSg` (both from Noun, already in
-- scope) rather than a bare *_Det constant, and "really great" is a
-- degree-modified adjective, AdAP really_AdA (PositA great_A) : AP
-- (from Adjective, also already in scope), fed to AdjCN just like a
-- plain PositA AP is:
--   linearize PredVP
--     (DetCN (DetQuant no_Quant NumSg) (AdjCN (AdAP really_AdA (PositA great_A)) (UseN tenor_N)))
--     (UseComp (CompAP (PositA modest_A)))
--   expected: "no really great tenors are modest"
--
-- FraCaS problem 10's premise ("Most great tenors are Italian."), NOT
-- YET CONFIRMED: most_Det (from DictEngAbs/DictEng, freshly extended
-- with this round) is a bare Det, so this is the same shape as problem
-- 7 with a different determiner and complement:
--   linearize PredVP
--     (DetCN most_Det (AdjCN (PositA great_A) (UseN tenor_N)))
--     (UseComp (CompAP (PositA italian_A)))
--   expected: "most great tenors are Italian"
