concrete FraCaSLogicEng of FraCaSLogic =
  CatEng, StructuralEng, SentenceEng, NounEng, AdjectiveEng, VerbEng
  ** open ParadigmsEng, MorphoEng, ResEng in {
  lin
    most_Det = mkDeterminer plural "most" ;
    each_Det = mkDeterminer singular "each" ;
    several_Det = mkDeterminer plural "several" ;
    both_Det = mkDeterminer plural "both" ;
    neither_Det = mkDeterminer singular "neither" ;
    aFew_Det = mkDeterminer plural "a few" ;
    really_AdA = mkAdA "really" ;
    italian_A = mkA "Italian" ;
    great_A = mkA "great" ;
    swedish_A = mkA "Swedish" ;
    modest_A = mkA "modest" ;
    german_A = mkA "German" ;
    british_A = mkA "British" ;
    man_N = mkN "man" "men" ;
    tenor_N = mkN "tenor" ;
    irishman_N = mkN "Irishman" "Irishmen" ;
    nobelPrize_N = mkN "Nobel prize" ;
    win_V2 = mkV2 "win" ;
    ComplV2 v np = insertObj (\\_ => v.c2 ++ np.s ! NPAcc) (predV v) ;
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
-- FraCaS problem 33's premise ("An Irishman won a Nobel prize."): the
-- first subject-verb-object sentence shape (every prior one was
-- copula/control-verb - "is"/"are"/"wants to be"). The object is
-- itself a full determiner-quantified NP, same as the subject, built
-- from the plain transitive-VP constructor ComplV2 - self-declared
-- above (see gf/FraCaSLogic.gf's own comment on why, not extended from
-- Backward/BackwardEng). IndefArt (from Noun, already in scope) is the
-- a/an quantifier; the RGL picks "a" vs "an" for us automatically based
-- on the following word. Note this project's target category Cl is
-- tenseless (see the file-top comment), so the confirmed output
-- correctly comes out present tense ("wins"), not an exact string
-- match to FraCaS's own past-tense wording ("won") - that's a
-- deliberate, already-established limitation, not a bug here:
--   linearize PredVP
--     (DetCN (DetQuant IndefArt NumSg) (UseN irishman_N))
--     (ComplV2 win_V2 (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))
--   => "an Irishman wins a Nobel prize"
--
-- Confirmed end-to-end on the real toolchain.
--
-- FraCaS problem 3's premise ("All Italian men want to be a great
-- tenor."): see gf/FraCaSLogic.gf's own comment on why "all" is
-- PredetNP all_Predet over a bare plural NP, not a Det. The complement
-- uses CompNP wrapping an explicit singular indefinite NP, not CompCN,
-- specifically to force "a great tenor" (singular) despite the plural
-- subject - CompCN's complement agrees in number with the subject,
-- which would give "want to be great tenors" instead (confirmed by CI
-- catching exactly this the first time):
--   linearize PredVP
--     (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA italian_A) (UseN man_N))))
--     (ComplVV want_VV (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA great_A) (UseN tenor_N))))))
--   => "all Italian men want to be a great tenor"
--
-- FraCaS problem 4's premises ("Each Italian tenor wants to be great."/
-- "Some Italian tenors are great."): each_Det is self-declared above.
--   linearize PredVP (DetCN each_Det (AdjCN (PositA italian_A) (UseN tenor_N)))
--                     (ComplVV want_VV (UseComp (CompAP (PositA great_A))))
--   => "each Italian tenor wants to be great"
--   linearize PredVP (DetCN somePl_Det (AdjCN (PositA italian_A) (UseN tenor_N)))
--                     (UseComp (CompAP (PositA great_A)))
--   => "some Italian tenors are great"
--
-- FraCaS problem 8's premise ("Many great tenors are German."):
-- many_Det is free via Structural, not self-declared:
--   linearize PredVP (DetCN many_Det (AdjCN (PositA great_A) (UseN tenor_N)))
--                     (UseComp (CompAP (PositA german_A)))
--   => "many great tenors are German"
--
-- FraCaS problem 9's premise ("Several great tenors are British."):
--   linearize PredVP (DetCN several_Det (AdjCN (PositA great_A) (UseN tenor_N)))
--                     (UseComp (CompAP (PositA british_A)))
--   => "several great tenors are British"
--
-- All confirmed end-to-end on the real toolchain.
