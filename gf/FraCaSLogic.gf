-- Phase 3 proof-of-concept grammar. See gf/NOTES.md for the full story
-- of how this shape was arrived at (the modules it needs to extend and
-- why, the Syntax/SyntaxEng bug it avoids, the Cl-vs-S issue).
--
-- Target category is `Cl` (clause), not `S` (sentence) - see NOTES.md's
-- "UseCl silently produces empty output" section. A tenseless clause is
-- also the right semantic unit for this project's purposes: tense is
-- separate information from the core proposition (cf. FraCaS Section 7
-- in the Lean suite), not something to bake into the target category.
abstract FraCaSLogic = Cat, Structural, Sentence, Tense, Noun, Adjective, Verb ** {
  fun
    italian_A, great_A, swedish_A : A ;
    man_N, tenor_N : N ;
    -- want_VV is NOT declared here - it already exists in Structural
    -- (a builtin structural word); redeclaring it is a name collision.
}
