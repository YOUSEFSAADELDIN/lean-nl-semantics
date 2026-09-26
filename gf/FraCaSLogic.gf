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
-- DICTIONARY INTEGRATION: the win_V2 bug-hunt below (three CI
-- round-trips to get `mkV "win" "won" "won"`'s arity right) motivated
-- actually measuring whether extending DictEngAbs/DictEng is worth it
-- instead of hand-declaring everything - see .github/workflows/build.yml's
-- own "Build DictEng" step and gf/NOTES.md for the measured build-time
-- cost (~10 seconds to compile the whole ~65k-line dictionary, paid
-- once and cached - far cheaper than assumed). Checking every one of
-- this grammar's ~33 hand-declared words against DictEngAbs found 31
-- *already there*, same name, same type. Piloted on win_V2 alone
-- first (DictEng's own `win_V2 = mkV2 (IrregEng.win_V)`, built from
-- IrregEng's dedicated irregular-verb table, was exactly the
-- correctly-conjugated entry the hand-declared version took three
-- attempts to get right) - then, once that held up, extended to the
-- rest, after actually comparing each one's real recipe (checked
-- against gf-rgl/src/english/DictEng.gf) to ours rather than assuming
-- they'd match:
--   - Most were functionally identical for what this grammar actually
--     exercises (differences like `compoundA`-wrapping or explicit
--     comparative forms only affect comparison/anaphora, never tested
--     here - most_Det's own `mkDeterminer plural "most"` was always
--     exactly this, going back to before this grammar even declared
--     it by hand - see gf/NOTES.md for where mkDeterminer itself needs
--     to come from, MorphoEng, opened directly).
--   - take_V2/come_V were ALSO latently broken the exact same way
--     win_V2 was (`mkV2 "take"`/`mkV "come"`, fully regular derivation
--     for verbs that are genuinely irregular - "took"/"came" - just
--     never exercised by a past-tense check before now). Swapping
--     fixed both proactively.
--   - irishman_N is the one word kept hand-declared: DictEng's own
--     `mkN masculine (mkN "irishman" "irishmen")` is lowercase, but
--     problem 33's confirmed sentence needs the capitalized "an
--     Irishman" - swapping it would silently break that check.
-- Net result: of the 31 collisions against this grammar's own words,
-- only irishman_N is still excluded on the extends line below -
-- combined with 74 more against Structural specifically (its own
-- closed-class words: pronouns, prepositions, conjunctions,
-- every_Det/many_Det/etc., which DictEngAbs's general coverage happens
-- to duplicate), that's 75 excluded overall.
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
-- European") is NOT declared by hand below - it's one of the 30 words
-- now sourced from DictEngAbs (see the dictionary-integration comment
-- above), same as both_Det/neither_Det/most_Det. It was never in
-- ExtraEngAbs (where the RGL's own treebank puts it) - that module
-- lives in src/english/, not src/abstract/, meaning it's an
-- English-specific "abstract" module despite the name, not genuinely
-- cross-language; depending on it would tie this project's abstract
-- syntax to English specifically, contradicting the multi-language
-- goal in the README. Its real recipe (checked against
-- gf-rgl/src/english/ExtraEng.gf, back when it was still hand-declared
-- here) was the trivial `mkDeterminer Sg "each"` - DictEngAbs's own
-- copy uses the exact same recipe - see gf/NOTES.md's section on
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
-- not declared here. both_Det/neither_Det are two more of the 30 words
-- now sourced from DictEngAbs (same story as most_Det/each_Det).
-- several_Det stays hand-declared below (not one of the 31 collisions
-- - DictEngAbs simply has no entry for it under this name). "a few"
-- (treebank's own `a8few_Det` - the `8` is the RGL's own convention
-- for a space inside a multi-word identifier, same as `how8many_IDet`
-- - is ALSO stale, absent from current source, and not in DictEngAbs
-- either) stays hand-declared as `aFew_Det` too, since no real
-- function for it exists to copy a recipe from - just the obvious,
-- generic `mkDeterminer plural "a few"`.
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
  -- Extended the dictionary swap (originally piloted on win_V2 alone)
  -- to the rest of the 30 collisions checked directly against this
  -- grammar's own words, after comparing each one's real DictEng
  -- recipe against ours: most turned out functionally identical for
  -- what this grammar actually exercises (differences like
  -- `compoundA`-wrapping or explicit comparative forms only affect
  -- comparison/anaphora, never tested here - and the existing 34
  -- exact-match CI checks would catch it if that were wrong). Two real
  -- differences found, handled deliberately:
  --   - take_V2/come_V were ALSO latently broken here the exact same
  --     way win_V2 was (`mkV2 "take"`/`mkV "come"`, a fully regular
  --     derivation for verbs that are genuinely irregular - "took"/
  --     "came", never actually exercised by a past-tense check before
  --     now) - swapping to DictEng's own `mkV2 (IrregEng.take_V)`/
  --     `IrregEng.come_V` fixes both proactively, not just win_V2.
  --   - irishman_N is the one word kept hand-declared and excluded:
  --     DictEng's own `mkN masculine (mkN "irishman" "irishmen")` is
  --     lowercase, but problem 33's confirmed sentence needs the
  --     capitalized "an Irishman" - swapping it would silently break
  --     that check's exact string match.
  -- So of the 31 total collisions against this grammar's own words,
  -- only irishman_N is still excluded - combined with the 74 against
  -- Structural, that's 75 excluded overall (down from 104).
  DictEngAbs - [
    above_Prep, after_Prep, all_Predet, almost_AdA, almost_AdN,
    although_Subj, always_AdV, and_Conj, at_least_AdN, because_Subj,
    before_Prep, behind_Prep, between_Prep, both7and_DConj, but_PConj,
    can_VV, during_Prep, either7or_DConj, every_Det, everybody_NP,
    everything_NP, everywhere_Adv, except_Prep, for_Prep, from_Prep, have_V2,
    he_Pron, here_Adv, how8many_IDet, how_IAdv, i_Pron, if_Subj, in_Prep,
    irishman_N, it_Pron, many_Det, much_Det, must_VV, no_Quant, nobody_NP,
    nothing_NP, on_Prep, only_Predet, or_Conj, quite_Adv, she_Pron, so_AdA,
    somebody_NP, something_NP, somewhere_Adv, that_Quant, that_Subj,
    there_Adv, they_Pron, this_Quant, through_Prep, to_Prep, too_AdA,
    under_Prep, very_AdA, want_VV, we_Pron, whatPl_IP, whatSg_IP, when_IAdv,
    when_Subj, where_IAdv, which_IQuant, whoPl_IP, whoSg_IP, why_IAdv,
    with_Prep, without_Prep, youPl_Pron, youSg_Pron
  ]
  ** {
  fun
    several_Det, aFew_Det : Det ;
    really_AdA : AdA ;
    leading_A : A ;
    cheap_Adv : Adv ;
    irishman_N, nobelPrize_N : N ;
    pavarotti_PN : PN ;
    CompoundCN : CN -> CN -> CN ;
}
