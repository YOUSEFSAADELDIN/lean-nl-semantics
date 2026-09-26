-- Phase 3 proof-of-concept grammar. See gf/NOTES.md for the full story
-- of how this shape was arrived at (the modules it needs to extend and
-- why, the Syntax/SyntaxEng bug it avoids, the Cl-vs-S issue).
--
-- Target category is `Cl` (clause), not `S` (sentence) - see NOTES.md's
-- "UseCl silently produces empty output" section. A tenseless clause is
-- also the right semantic unit for this project's purposes: tense is
-- separate information from the core proposition (cf. FraCaS Section 7
-- in the Lean suite), not something to bake into the target category.
--
-- DictEngAbs/DictEng (RGL's general dictionary) turned out NOT to be
-- part of Setup.sh's default build output at all (confirmed: `find
-- ~/gf-libs -iname 'DictEngAbs*'` finds nothing anywhere under the
-- built libs directory, even though the module exists in the gf-rgl
-- *source* tree) - it's a separate, much heavier build step Setup.sh
-- doesn't run. So this grammar doesn't extend it; every content word
-- and determiner it needs is declared here instead, same as
-- really_AdA always was. most_Det's own linearization is copied
-- directly from DictEngAbs's real recipe (checked against
-- gf-rgl/src/english/DictEng.gf): `mkDeterminer plural "most"` - see
-- gf/NOTES.md for where mkDeterminer itself actually needs to come from
-- (MorphoEng, opened directly - NOT inherited from StructuralEng just
-- because StructuralEng happens to use it internally).
--
-- ComplV2 : V2 -> NP -> VP (the plain transitive-verb VP constructor,
-- needed for the first subject-verb-object sentence shape, problem 33
-- "An Irishman won a Nobel prize.") is declared directly below rather
-- than extending Backward (where the RGL itself puts it) - Backward.gf
-- has the exact same problem DictEngAbs did: it isn't part of
-- Setup.sh's build output either (same "File X.gf does not exist"
-- error, confirmed the same way). Its real recipe is copied from
-- gf-rgl/src/english/BackwardEng.gf instead - see gf/NOTES.md.
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
abstract FraCaSLogic = Cat, Structural, Sentence, Tense, Noun, Adjective, Verb, Numeral, Adverb, Relative ** {
  fun
    most_Det, each_Det, several_Det, both_Det, neither_Det, aFew_Det : Det ;
    really_AdA : AdA ;
    italian_A, great_A, swedish_A, modest_A, german_A, british_A,
      leading_A, excellent_A, indispensable_A : A ;
    man_N, tenor_N, irishman_N, nobelPrize_N, part_N, concert_N, fee_N, charity_N : N ;
    win_V2, take_V2, contribute_V2 : V2 ;
    ComplV2 : V2 -> NP -> VP ;
}
