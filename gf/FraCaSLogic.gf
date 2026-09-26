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
-- gf-rgl/src/english/DictEng.gf): `mkDeterminer plural "most"` -
-- mkDeterminer itself is already in scope via StructuralEng (which
-- uses it for someSg_Det/somePl_Det/etc.), not a new dependency.
abstract FraCaSLogic = Cat, Structural, Sentence, Tense, Noun, Adjective, Verb ** {
  fun
    most_Det : Det ;
    really_AdA : AdA ;
    italian_A, great_A, swedish_A, modest_A : A ;
    man_N, tenor_N : N ;
}
