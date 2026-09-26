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
-- DictEngAbs (RGL's general dictionary) is extended for two reasons:
-- it's where most_Det (and, eventually, each_Det/neither_Det/...) live,
-- and it turns out to already declare every ordinary content word this
-- grammar needs (italian_A, great_A, swedish_A, man_N, tenor_N,
-- modest_A - checked directly against the RGL source) under the exact
-- names this project had already independently chosen for them. So
-- none of those are declared here anymore - redeclaring a word DictEngAbs
-- already has is the same collision want_VV hit with Structural.
-- really_AdA is the one genuinely new item (not in DictEngAbs).
abstract FraCaSLogic = Cat, Structural, Sentence, Tense, Noun, Adjective, Verb, DictEngAbs ** {
  fun
    really_AdA : AdA ;
}
