concrete FraCaSLogicEng of FraCaSLogic =
  CatEng, StructuralEng, SentenceEng, NounEng, AdjectiveEng, VerbEng, BackwardEng
  ** open ParadigmsEng, MorphoEng in {
  lin
    most_Det = mkDeterminer plural "most" ;
    really_AdA = mkAdA "really" ;
    italian_A = mkA "Italian" ;
    great_A = mkA "great" ;
    swedish_A = mkA "Swedish" ;
    modest_A = mkA "modest" ;
    man_N = mkN "man" "men" ;
    tenor_N = mkN "tenor" ;
    irishman_N = mkN "Irishman" "Irishmen" ;
    nobelPrize_N = mkN "Nobel prize" ;
    win_V2 = mkV2 "win" ;
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
-- FraCaS problem 6's premise ("No really great tenors are modest."):
-- "no" is Quant-typed, not Det-typed, so the subject is DetCN wrapping
-- `DetQuant no_Quant NumPl` (both from Noun, already in scope) rather
-- than a bare *_Det constant, and "really great" is a degree-modified
-- adjective, AdAP really_AdA (PositA great_A) : AP (from Adjective,
-- also already in scope), fed to AdjCN just like a plain PositA AP is.
-- NumPl, not NumSg: NumSg was tried first and round-tripped to "no
-- really great tenor is modest" (singular agreement) instead of the
-- target plural sentence - the quantifier's own Number argument drives
-- subject-verb agreement, and FraCaS's sentence is plural.
--   linearize PredVP
--     (DetCN (DetQuant no_Quant NumPl) (AdjCN (AdAP really_AdA (PositA great_A)) (UseN tenor_N)))
--     (UseComp (CompAP (PositA modest_A)))
--   => "no really great tenors are modest"
--
-- FraCaS problem 10's premise ("Most great tenors are Italian."):
-- most_Det (declared directly above, using DictEng's own recipe - see
-- gf/NOTES.md's "DictEngAbs/DictEng aren't in Setup.sh's build output"
-- section) is a bare Det, so this is the same shape as problem 7 with a
-- different determiner and complement:
--   linearize PredVP
--     (DetCN most_Det (AdjCN (PositA great_A) (UseN tenor_N)))
--     (UseComp (CompAP (PositA italian_A)))
--   => "most great tenors are Italian"
--
-- All four of the above are confirmed end-to-end on the real toolchain.
--
-- FraCaS problem 33's premise ("An Irishman won a Nobel prize."), NOT
-- YET CONFIRMED: the first subject-verb-object sentence shape (every
-- prior one was copula/control-verb - "is"/"are"/"wants to be"). The
-- object is itself a full determiner-quantified NP, same as the
-- subject, built from the plain transitive-VP constructor ComplV2 (in
-- Backward/BackwardEng - see gf/FraCaSLogic.gf's own comment on why
-- that module, not Verb, has it). IndefArt (from Noun, already in
-- scope) is the a/an quantifier; the RGL picks "a" vs "an" for us
-- automatically based on the following word. Note this project's
-- target category Cl is tenseless (see the file-top comment), so the
-- confirmed output is expected to come out present tense ("wins"), not
-- an exact string match to FraCaS's own past-tense wording ("won") -
-- that's a deliberate, already-established limitation, not a bug here:
--   linearize PredVP
--     (DetCN (DetQuant IndefArt NumSg) (UseN irishman_N))
--     (ComplV2 win_V2 (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))
--   expected: "an Irishman wins a Nobel prize"
