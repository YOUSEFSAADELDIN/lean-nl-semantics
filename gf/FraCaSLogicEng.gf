concrete FraCaSLogicEng of FraCaSLogic =
  CatEng, StructuralEng, SentenceEng, NounEng, AdjectiveEng, VerbEng, NumeralEng, AdverbEng, RelativeEng,
  TenseX - [Pol, PPos, PNeg, SC, CAdv], PhraseEng,
  -- Same 104-name exclusion as FraCaSLogic.gf's own extends line (kept
  -- in sync with it - see that file's comment for the full story: 30
  -- against this grammar's own words, 74 more against StructuralEng's).
  DictEng - [
    above_Prep, after_Prep, all_Predet, almost_AdA, almost_AdN,
    although_Subj, always_AdV, and_Conj, at_least_AdN, because_Subj,
    before_Prep, behind_Prep, between_Prep, both7and_DConj, both_Det,
    british_A, but_PConj, can_VV, charity_N, cheap_A, come_V, concert_N,
    contribute_V2, during_Prep, each_Det, either7or_DConj, europe_PN,
    every_Det, everybody_NP, everything_NP, everywhere_Adv, excellent_A,
    except_Prep, fee_N, for_Prep, from_Prep, german_A, great_A, have_V2,
    he_Pron, here_Adv, how8many_IDet, how_IAdv, i_Pron, if_Subj, in_Prep,
    indispensable_A, irishman_N, it_Pron, italian_A, live_V, man_N, many_Det,
    member_N, modest_A, most_Det, much_Det, must_VV, neither_Det, no_Quant,
    nobody_NP, nothing_NP, of_Prep, on_Prep, only_Predet, or_Conj, part_N,
    quite_Adv, resident_N, right_N, she_Pron, so_AdA, somebody_NP,
    something_NP, somewhere_Adv, state_N, swedish_A, take_V2, tenor_N,
    that_Quant, that_Subj, there_Adv, they_Pron, this_Quant, through_Prep,
    to_Prep, too_AdA, under_Prep, very_AdA, want_VV, we_Pron, whatPl_IP,
    whatSg_IP, when_IAdv, when_Subj, where_IAdv, which_IQuant, whoPl_IP,
    whoSg_IP, why_IAdv, with_Prep, without_Prep, youPl_Pron, youSg_Pron
  ]
  ** open ParadigmsEng, MorphoEng, ResEng, Prelude in {
  lin
    -- PPos/PNeg excluded from TenseX above (real conflict: TenseX's own
    -- CAdv/CommonX shape doesn't unify with CatEng's) - GrammarEng.gf
    -- solves this the exact same way (extend TenseX minus these five,
    -- redefine PPos/PNeg itself); copied that recipe directly.
    PPos = {s = []; p = CPos} ;
    PNeg = {s = []; p = CNeg True} ;
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
    leading_A = mkA "leading" ;
    excellent_A = mkA "excellent" ;
    indispensable_A = mkA "indispensable" ;
    cheap_A = mkA "cheap" ;
    cheap_Adv = mkAdv "cheap" ;
    man_N = mkN "man" "men" ;
    tenor_N = mkN "tenor" ;
    irishman_N = mkN "Irishman" "Irishmen" ;
    nobelPrize_N = mkN "Nobel prize" ;
    part_N = mkN "part" ;
    concert_N = mkN "concert" ;
    fee_N = mkN "fee" ;
    charity_N = mkN "charity" ;
    member_N = mkN "member" ;
    state_N = mkN "state" ;
    resident_N = mkN "resident" ;
    right_N = mkN "right" ;
    take_V2 = mkV2 "take" ;
    contribute_V2 = mkV2 "contribute" ;
    live_V = mkV "live" ;
    come_V = mkV "come" ;
    europe_PN = mkPN "Europe" ;
    pavarotti_PN = mkPN "Pavarotti" ;
    of_Prep = mkPrep "of" ;
    CompoundCN a b = {s = \\n,c => a.s ! Sg ! Nom ++ b.s ! n ! c ; g = b.g} ;
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
-- from `ComplSlash (SlashV2a win_V2) np` (Verb, already extended - the
-- same combinator problems 15/16/21 already use for their own
-- transitive/prepositional objects). IndefArt (from Noun, already in
-- scope) is the a/an quantifier; the RGL picks "a" vs "an" for us
-- automatically based on the following word. Note this project's
-- target category Cl is tenseless by choice (see the file-top comment
-- - tense support is fully available now, just not used by default),
-- so the confirmed output correctly comes out present tense ("wins"),
-- not an exact string match to FraCaS's own past-tense wording ("won")
-- - that's the deliberate default, not a limitation we're stuck with:
--   linearize PredVP
--     (DetCN (DetQuant IndefArt NumSg) (UseN irishman_N))
--     (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))
--   => "an Irishman wins a Nobel prize"
--
-- Confirmed end-to-end on the real toolchain. (This premise originally
-- used a self-declared `ComplV2`/`predV` combinator instead of
-- `ComplSlash`/`SlashV2a` - see FraCaSLogic.gf's own comment on why
-- that was replaced: it had a real bug under `TPast`, caught by
-- run_gf_tests.py's past-tense pilot.)
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
--
-- FraCaS problem 15's premise ("At least three tenors will take part
-- in the concert."): the first numeral quantifier and the first use of
-- PrepNP (a very high-leverage addition - used 81 times across the
-- treebank's Section 1 sentences alone). at_least_AdN/at_most_AdN are
-- free via Structural (real, current - unlike all_Det/a8few_Det, which
-- looked similar but were stale). The numeral itself is built from
-- Noun's NumCard/NumNumeral/AdNum plus Numeral's own digit constants
-- (n2..n9) and positional coercions (pot0/pot0as1/pot1as2/pot2as3) -
-- this exact encoding is RGL's generic, sentence-independent mechanism
-- for representing any numeral, not FraCaS-specific content, so
-- reusing it isn't a licensing concern the way copying an actual
-- sentence tree would be (see CREDITS.md). Tenseless Cl (this
-- project's target category) drops "will", same already-established
-- limitation as problem 33's "won" -> "wins":
--   linearize PredVP
--     (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (UseN tenor_N))
--     (ComplSlash (SlashV2a take_V2) (AdvNP (MassNP (UseN part_N)) (PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN concert_N)))))
--   => "at least three tenors take part in the concert"
--
-- Not yet wired into translate.py: this project's Lean AtLeast/AtMost
-- combinators (GQ.lean) take an explicit Nat bound, which the simple
-- string-keyed quantifier tables (_QUANTIFIER_BY_DET/_QUANTIFIER_BY_QUANT)
-- don't carry - needs its own translate_cl case, not just a table
-- entry. Confirmed working in the grammar first, translator mapping to
-- follow.
--
-- FraCaS problem 16's premise ("At most two tenors will contribute
-- their fees to charity."): PossPron/they_Pron (both free via
-- Noun/Structural) build "their". AdvVP (Verb, already extended)
-- attaches the PrepNP adjunct to the VP rather than the object NP:
--   linearize PredVP
--     (DetCN (DetQuant IndefArt (NumCard (AdNum at_most_AdN (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2))))))))) (UseN tenor_N))
--     (AdvVP (ComplSlash (SlashV2a contribute_V2) (DetCN (DetQuant (PossPron they_Pron) NumPl) (UseN fee_N))) (PrepNP to_Prep (MassNP (UseN charity_N))))
--   => "at most two tenors contribute their fees to charity"
--
-- FraCaS problem 13's second premise ("Leading tenors who are excellent
-- are indispensable."): the first relative clause. RelCN/UseRCl (Noun/
-- Sentence, already extended) plus RelVP/IdRP (Relative, newly
-- extended) build the relative clause as a CN modifier. IdRP ("the
-- default/unmarked relative pronoun") realizes as "that" in English,
-- not "who" - a real, current, cross-language-generic choice (its own
-- source comment: "since 5/6/2016 default for IdRP"), not a bug - same
-- category of harmless divergence as "wins" vs "won". The subject is a
-- bare plural (DetQuant IndefArt NumPl, no article - same mechanism as
-- problem 3's "all"). "leading" is a plain adjective, not derived from
-- lead_V via VerbCN (stale, doesn't exist - see gf/NOTES.md). This was
-- also the sentence that surfaced the real TenseX gap below ("[RelCN]"
-- placeholder output before that fix, since UseRCl's own TTAnt/PPos was
-- affected the exact same way UseCl's was):
--   linearize PredVP
--     (DetCN (DetQuant IndefArt NumPl) (RelCN (AdjCN (PositA leading_A) (UseN tenor_N)) (UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAP (PositA excellent_A)))))))
--     (UseComp (CompAP (PositA indispensable_A)))
--   => "leading tenors that are excellent are indispensable"
--
-- FraCaS problem 21's first premise ("The residents of member states
-- have the right to live in Europe."): a definite plural subject
-- modified by a PP (AdvNP+PrepNP, "of member states"), and a
-- complex complement noun ("the right to live in Europe" - SentCN
-- attaches an infinitival SC, built via EmbedVP, to a CN; another
-- PrepNP attaches the locative PP). CompoundCN ("member states") is
-- self-declared above (see gf/FraCaSLogic.gf's own comment, not
-- extended from ExtraEngAbs). have_V2 needed no declaration at all -
-- it's already in Structural (same collision want_VV hit early on):
--   linearize PredVP
--     (AdvNP (DetCN (DetQuant DefArt NumPl) (UseN resident_N)) (PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN member_N) (UseN state_N)))))
--     (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant DefArt NumSg) (AdvCN (SentCN (UseN right_N) (EmbedVP (UseV live_V))) (PrepNP in_Prep (UsePN europe_PN)))))
--   => "the residents of member states have the right to live in Europe"
--
-- FraCaS problem 14's premises ("Neither leading tenor comes cheap."/
-- "One of the leading tenors is Pavarotti."): "comes cheap" is not the
-- copula (UseComp is specifically "be") - it's an intransitive verb
-- plus an adjective used adverbially. This was ORIGINALLY built with
-- Adverb's own `PositAdvAdj cheap_A`, which looks exactly right for
-- this idiom - but at the current pinned gf-rgl tag it actually
-- linearizes to "cheaply" (the regular derived manner-adverb form),
-- not the flat "cheap" the idiom needs. This went unnoticed at first
-- because the original CI check used a substring match ("comes cheap"
-- is a prefix of "comes cheaply", so the check kept "passing"); caught
-- once the tense-reconfirmation pass switched to an exact-line match
-- (see run_gf_tests.py). Fixed by self-declaring `cheap_Adv : Adv =
-- mkAdv "cheap"` instead - bypassing PositAdvAdj's derivation entirely,
-- same "don't trust it, self-declare the literal string" pattern as
-- most_Det/of_Prep/etc. above. The partitive "one of the X" is
-- CountNP : Det -> NP -> NP ("three of them" - Noun, already extended)
-- with "one" built the same numeral way as problems 15/16, using pot01
-- (Numeral's own dedicated constant for 1, since Digit only covers
-- 2..9):
--   linearize PredVP (DetCN neither_Det (AdjCN (PositA leading_A) (UseN tenor_N))) (AdvVP (UseV come_V) cheap_Adv)
--   => "neither leading tenor comes cheap"
--   linearize PredVP
--     (CountNP (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) (DetCN (DetQuant DefArt NumPl) (AdjCN (PositA leading_A) (UseN tenor_N))))
--     (UseComp (CompNP (UsePN pavarotti_PN)))
--   => "one of the leading tenors is Pavarotti"
--
-- Problem 33's win_V2 had a matching latent bug, caught by the same
-- tense-reconfirmation pass's past-tense pilot (this one DID fail the
-- original substring check, since "winned" doesn't contain "won"):
-- `mkV2 "win"` derives a fully regular verb, so `TPast` gave "winned"
-- instead of the irregular "won". This took three CI-verified attempts
-- to actually fix: (1) switching problem 33's own VP construction from
-- the self-declared ComplV2/predV to the genuine ComplSlash/SlashV2a
-- didn't help - still "winned", ruling out VP-building as the cause;
-- (2) a temporary bare-V diagnostic (bypassing V2/ComplSlash entirely)
-- confirmed the fault was in `mkV` itself: `mkV "win" "won"` (2 args,
-- guessing infinitive+preterite) still gave "winned" even with no
-- V2/VP-building involved at all; (3) the working fix is the
-- 3-argument form, `mkV "win" "won" "won"` (infinitive, preterite,
-- past-participle, all explicit - "win"'s preterite and
-- past-participle happen to coincide). 3rd-singular present ("wins")
-- and the present participle ("winning") are still regular, so still
-- derived automatically.
--
-- This whole bug-hunt is also why win_V2 no longer has a hand-declared
-- `lin` rule at all: it's the one word this grammar now takes from
-- DictEng (see FraCaSLogic.gf's own comment on the dictionary
-- integration pilot this motivated) - DictEng's own
-- `win_V2 = mkV2 (IrregEng.win_V)` already had the correct irregular
-- conjugation the whole time, via IrregEng's dedicated
-- `win_V = irregDuplV "win" "won" "won"`.
