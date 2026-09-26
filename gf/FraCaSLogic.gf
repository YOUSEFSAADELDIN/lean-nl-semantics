-- Phase 3 proof-of-concept grammar. See gf/NOTES.md for the full story
-- of how this shape was arrived at (the modules it needs to extend and
-- why, the Syntax/SyntaxEng bug it avoids, the TenseX fix).
--
-- Target category is `Cl` (clause), not `S`/`Utt` (sentence/utterance)
-- - by deliberate choice, not technical necessity: tense support is
-- fully available now (see NOTES.md's "SOLVED: UseCl/tense support"
-- section - it was a missing module extension on our side, not a real
-- RGL limitation, as first assumed). `Cl` is kept as the default target
-- because a tenseless clause is the right semantic unit for this
-- project's purposes regardless: tense is separate information from
-- the core proposition (cf. FraCaS Section 7 in the Lean suite), not
-- something to bake into every sentence's target category. Nothing
-- stops a future sentence from using full `S`/`Utt` where its tense
-- specifically matters - see NOTES.md for the working recipe.
--
-- DictEngAbs/DictEng (RGL's general dictionary) turned out NOT to be
-- part of Setup.sh's default build output at all (confirmed: `find
-- ~/gf-libs -iname 'DictEngAbs*'` finds nothing anywhere under the
-- built libs directory, even though the module exists in the gf-rgl
-- *source* tree) - it's a separate, much heavier build step Setup.sh
-- doesn't run, which is why every content word and determiner this
-- grammar needs was originally declared here by hand instead, same as
-- really_AdA always was.
--
-- DICTIONARY INTEGRATION PILOT: the win_V2 bug-hunt below (three CI
-- round-trips to get `mkV "win" "won" "won"`'s arity right) motivated
-- actually measuring whether extending DictEngAbs/DictEng is worth it
-- instead of hand-declaring everything - see .github/workflows/build.yml's
-- own "Build DictEng" step and gf/NOTES.md for the measured build-time
-- cost. Checking every one of this grammar's ~33 hand-declared words
-- against DictEngAbs found 31 *already there*, same name, same type
-- (most_Det, italian_A, man_N, win_V2, come_V, europe_PN, ...). As a
-- pilot, DictEngAbs/DictEng are now extended, with 30 of those 31
-- collisions excluded on the extends line below (kept hand-declared,
-- unchanged) - only win_V2 is let through, now coming from the
-- dictionary instead of a hand-declared recipe. DictEng's own
-- `win_V2 = mkV2 (IrregEng.win_V)` (built from IrregEng's dedicated
-- irregular-verb table, `irregDuplV "win" "won" "won"`) is exactly the
-- correctly-conjugated entry the hand-declared version took three
-- attempts to get right. most_Det's own linearization was originally
-- copied directly from DictEngAbs's real recipe this same way (checked
-- against gf-rgl/src/english/DictEng.gf): `mkDeterminer plural "most"`
-- - see gf/NOTES.md for where mkDeterminer itself actually needs to
-- come from (MorphoEng, opened directly - NOT inherited from
-- StructuralEng just because StructuralEng happens to use it
-- internally).
--
-- Problem 33 ("An Irishman won a Nobel prize.", the first plain
-- subject-verb-object sentence) originally used a self-declared
-- `ComplV2 : V2 -> NP -> VP`, copied from Backward.gf/BackwardEng.gf's
-- own recipe (`insertObj (\_ => v.c2 ++ np.s ! NPAcc) (predV v)`,
-- needed because Backward.gf has the exact same "not part of Setup.sh's
-- build output" problem DictEngAbs did). The past-tense pilot in
-- run_gf_tests.py caught a real bug here - under `TPast`, "won" came
-- out "winned" - and `ComplV2`/`predV` was the first, entirely
-- reasonable suspect. It turned out NOT to be the cause: swapping in
-- `ComplSlash (SlashV2a v2) np` instead (Verb, already extended - the
-- same combinator problems 15/16/21 already use for their own
-- transitive objects, and proven correct under full tense-wrapping)
-- made no difference - still "winned". The real cause was win_V2's own
-- `mkV` call (see FraCaSLogicEng.gf's comment on win_V2 for the full
-- elimination story). `ComplSlash`/`SlashV2a` was kept anyway once the
-- real fix landed - it's a genuine RGL combinator doing the same job
-- the self-declared `ComplV2`/`predV` hack was for, so there was no
-- reason to keep the hack around once nothing needed it.
--
-- each_Det (problems 4, 18-20 etc: "each Italian tenor"/"each
-- European") is declared directly below rather than extending
-- ExtraEngAbs (where the RGL puts it) - that module lives in
-- src/english/, not src/abstract/, meaning it's an English-specific
-- "abstract" module despite the name, not genuinely cross-language.
-- Depending on it would tie this project's abstract syntax to English
-- specifically, contradicting the multi-language goal in the README.
-- Its real recipe (checked against gf-rgl/src/english/ExtraEng.gf) is
-- the trivial `mkDeterminer Sg "each"` - see gf/NOTES.md's section on
-- gf-rgl's own treebank for how this and several other mechanisms
-- below were found: it ships pre-built, validated trees for most of
-- FraCaS Section 1 already.
--
-- "all" (problems 3, 19, etc: "All Italian men want...") is NOT a Det
-- at all in the current RGL (the treebank's own `all_Det` is stale -
-- confirmed absent from the current source, same situation as
-- Backward's `Acc`/`NPAcc`). The real, current mechanism is
-- `PredetNP all_Predet np` (`all_Predet` already free via Structural,
-- `PredetNP` already free via Noun) applied to a *bare* plural NP -
-- `DetCN (DetQuant IndefArt NumPl) cn`, which realizes with no article
-- at all (`IndefArt`'s own linearization is the empty string for
-- plural - see gf/NOTES.md/NounEng.gf) - not `DetCN all_Det cn`.
--
-- many_Det/few_Det are ALREADY free via Structural (checked directly
-- against src/abstract/Structural.gf, not just the concrete side) -
-- not declared here. several_Det/both_Det/neither_Det are DictEng-only
-- (same story as most_Det - real recipes copied from
-- gf-rgl/src/english/DictEng.gf). "a few" (treebank's own `a8few_Det` -
-- the `8` is the RGL's own convention for a space inside a multi-word
-- identifier, same as `how8many_IDet` - is ALSO stale, absent from
-- current source) is declared here as `aFew_Det` instead, since no
-- real function for it exists to copy a recipe from - just the
-- obvious, generic `mkDeterminer plural "a few"`.
-- Numeral quantifiers (problem 15: "At least three tenors...") use
-- Structural's already-free at_least_AdN/at_most_AdN (real, current -
-- unlike all_Det/a8few_Det, these checked out fine) wrapping a numeral
-- built from Noun's NumCard/NumNumeral/AdNum and Numeral's own digit
-- constants (n2..n9) and positional coercions (pot0/pot0as1/...) -
-- Numeral is a genuine cross-language abstract module (src/abstract/,
-- not English-specific like ExtraEngAbs was), so extended normally.
-- Adverb is extended for PrepNP ("in the concert") - a very
-- high-leverage addition, used 81 times across the treebank's Section
-- 1 sentences alone.
-- Relative is extended for RelVP/IdRP (problem 13: "leading tenors who
-- are excellent"). RelCN and UseRCl (the other two relative-clause
-- pieces) are already free via Noun/Sentence. "leading" is a plain
-- adjective (mkA "leading"), not derived from lead_V via VerbCN - same
-- stale-function substitution as problem 13's premise 1 needed
-- (VerbCN doesn't exist in current RGL at all, see gf/NOTES.md).
-- CompoundCN : CN -> CN -> CN ("member states" = member_N + state_N) is
-- declared directly below rather than extending ExtraEngAbs, same
-- reasoning as each_Det (English-specific "abstract" module - see
-- above). Its real recipe (gf-rgl/src/english/ExtraEng.gf) is
-- `{s = \n,c => a.s ! Sg ! Nom ++ b.s ! n ! c ; g = b.g}` - the first
-- noun always singular-nominative ("member"), the second inflected for
-- whatever number/case is asked of the whole compound.
--
-- of_Prep : Prep doesn't exist as such anywhere in the current RGL at
-- all ("of" is hardcoded directly inside PossNP/PartNP's own concrete
-- definitions rather than exposed as a reusable Prep) - self-declared
-- via the generic `mkPrep "of"`.
--
-- cheap_Adv : Adv ("Neither leading tenor comes cheap.") is declared
-- separately from cheap_A - NOT built from it via Adverb's own
-- PositAdvAdj (A -> Adv), despite that being exactly the combinator
-- this idiom looks like it wants. The systematic tense-reconfirmation
-- pass (gf/run_gf_tests.py) caught this the hard way: at the current
-- pinned gf-rgl tag, `PositAdvAdj cheap_A` linearizes to "cheaply", the
-- regular derived manner-adverb form, not the flat "cheap" this idiom
-- needs - a real, silent bug that predates the tense work (the CI
-- check's own substring match let "comes cheap" pass even against
-- "comes cheaply", since the former is a prefix of the latter; fixed
-- alongside this, see run_gf_tests.py). Self-declared instead via the
-- generic `mkAdv "cheap"`, same "don't trust an RGL derivation whose
-- exact behavior isn't pinned down, self-declare the literal string
-- instead" pattern as most_Det/of_Prep/etc. above.
abstract FraCaSLogic =
  Cat, Structural, Sentence, Tense, Noun, Adjective, Verb, Numeral, Adverb, Relative, Phrase,
  -- DictEngAbs turned out to collide with TWO different sources, not
  -- just this grammar's own hand-declared words: 30 of them (checked
  -- directly), PLUS 74 more against Structural specifically (its own
  -- closed-class words - pronouns, prepositions, conjunctions,
  -- every_Det/many_Det/etc. - which DictEngAbs's general coverage
  -- happens to duplicate). All 104 are excluded here (kept exactly as
  -- they already were, via Structural or this grammar's own fun block
  -- below) - only win_V2 is deliberately let through, so it now
  -- resolves to DictEngAbs's own `win_V2 : V2` instead of a
  -- hand-declared one.
  DictEngAbs - [
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
  ** {
  fun
    most_Det, each_Det, several_Det, both_Det, neither_Det, aFew_Det : Det ;
    really_AdA : AdA ;
    italian_A, great_A, swedish_A, modest_A, german_A, british_A,
      leading_A, excellent_A, indispensable_A, cheap_A : A ;
    cheap_Adv : Adv ;
    man_N, tenor_N, irishman_N, nobelPrize_N, part_N, concert_N, fee_N, charity_N,
      member_N, state_N, resident_N, right_N : N ;
    take_V2, contribute_V2 : V2 ;
    live_V, come_V : V ;
    europe_PN, pavarotti_PN : PN ;
    of_Prep : Prep ;
    CompoundCN : CN -> CN -> CN ;
}
