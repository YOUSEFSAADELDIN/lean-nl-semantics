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
  -- Conjunction (ConjNP/BaseNP/ConsNP and friends) is FraCaS Section 2's
  -- own first new requirement: named-individual subjects joined by
  -- "and"/"or"/"either...or" ("Smith, Jones and Anderson signed the
  -- contract"), never needed in Section 1 (every subject there was a
  -- single quantified NP, not a list of proper nouns).
  Conjunction,
  -- Extend is Section 2 Batch2's own first new requirement: GenNP
  -- (NP -> Quant, "this man's") gives a REAL prenominal genitive -
  -- problem 99's "the system's performance" - unlike worlds_Det above
  -- (Section 1 problem 1's "the world's greatest tenor"), which had to
  -- be self-declared as a fixed string because no such combinator was
  -- found at the time. Checked directly this time (gf-rgl/src/abstract/
  -- Extend.gf, gf-rgl/src/english/ExtendEng.gf) before repeating that
  -- same self-declaration: GenNP genuinely exists and is a real
  -- cross-language module (every language has its own ExtendXxx.gf,
  -- same as Numeral/Adverb/Relative above), so it's extended normally
  -- rather than hand-copied. (worlds_Det itself is left as-is, not
  -- retrofitted onto GenNP, since it already works and retrofitting
  -- risks reopening an already-closed Section 1 check for no benefit.)
  Extend,
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
    nothing_NP, on_Prep, only_Predet, or_Conj,
    -- person_N joins irishman_N here as a second word excluded and
    -- hand-declared instead of taken from the dictionary as-is - found
    -- the same way irishman_N was (a real CI failure, not a
    -- precautionary check): DictEng's own `person_N = mkN masculine
    -- (mkN "person" "persons")` regularly pluralizes to "persons", but
    -- problems 26-28's own bare-plural premises ("all Europeans are
    -- people") need the actual irregular plural "people" - a real,
    -- separate dictionary entry (`people_N = mkN "people" (variants
    -- {"people"; "peoples"})`), not a second form of `person_N` at all,
    -- so there's no single already-existing word with the right
    -- sg/pl pair to source from.
    person_N,
    -- mp_N joins irishman_N/person_N as a third word excluded and
    -- hand-declared instead: DictEngAbs's own `mp_N = mkN "mp" "mp's"`
    -- is lowercase, but the actual abbreviation "MP"/"MPs" needs
    -- capitalizing.
    mp_N,
    quite_Adv, she_Pron, so_AdA,
    somebody_NP, something_NP, somewhere_Adv, that_Quant, that_Subj,
    there_Adv, they_Pron, this_Quant, through_Prep, to_Prep, too_AdA,
    under_Prep, very_AdA, want_VV, we_Pron, whatPl_IP, whatSg_IP, when_IAdv,
    when_Subj, where_IAdv, which_IQuant, whoPl_IP, whoSg_IP, why_IAdv,
    with_Prep, without_Prep, youPl_Pron, youSg_Pron
  ]
  ** {
  cat
    EllAux ;  -- the auxiliary left behind by VP ellipsis ("did", "didn't", "has", ...)
  fun
    several_Det, aFew_Det : Det ;
    -- worlds_Det : Det ("the world's", problem 1's "the world's greatest
    -- tenor") is self-declared rather than built from a real combinator:
    -- RGL's only possessive-NP mechanism, PossNP : CN -> NP -> NP, is a
    -- "CN of NP" paraphrase (`cn.s ++ "of" ++ np.s ! NPNomPoss`, checked
    -- directly against gf-rgl/src/english/NounEng.gf), not the
    -- prenominal 's-genitive FraCaS's own text uses, and there's no
    -- general `NP -> Quant` combinator (only `PossPron : Pron -> Quant`,
    -- pronouns only) to build "the world's" as a determiner from "the
    -- world" the normal way. Same "self-declare the literal string"
    -- pattern as most_Det/of_Prep/etc.
    worlds_Det : Det ;
    really_AdA : AdA ;
    leading_A : A ;
    -- greatest_A is NOT declared here despite looking like the same kind
    -- of "self-declare the literal string" call as worlds_Det above: it
    -- already exists in DictEngAbs (`fun greatest_A : A;`, same
    -- `mkA "greatest"` recipe) - confirmed directly against
    -- gf-rgl/src/english/{DictEngAbs,DictEng}.gf, and the hard way first,
    -- via a genuine "cannot unify" CI failure from declaring it here too.
    -- Left free via the extends line instead, same as every other
    -- DictEngAbs collision above.
    cheap_Adv : Adv ;
    irishman_N, nobelPrize_N, person_N : N ;
    pavarotti_PN : PN ;
    CompoundCN : CN -> CN -> CN ;
    -- aLotOf_Det : Det ("a lot of", problems 30-32's "spends a lot of
    -- time at home") is the same "self-declare the literal string" call
    -- as most_Det/several_Det/aFew_Det/worlds_Det above: Noun's own
    -- quantity combinators (PartNP, QuantityNP) don't cover a bare
    -- informal-quantity idiom like this, and DictEngAbs has no entry
    -- under this name either (checked directly, same as every other
    -- word below). Used with a singular Num slot, same as most_Det/
    -- worlds_Det, since it combines with the mass noun "time".
    aLotOf_Det : Det ;
    -- scandinavia_PN, southernEurope_PN : PN (problems 27/28's "from
    -- Scandinavia"/"from southern Europe") - DictEngAbs has
    -- scandinavian_A/scandinavian_N (the adjective/demonym) but no
    -- proper noun for the region itself, and "southern Europe" isn't in
    -- the dictionary as any kind of word at all (unlike the countries
    -- Sweden/Portugal, which are). Adjective-modifying a `PN` isn't a
    -- real RGL mechanism (AdjCN only takes a common noun `CN`, and
    -- "Europe" is a proper noun, not a common one) - self-declared as
    -- their own fixed-string proper nouns instead, same pattern as
    -- pavarotti_PN.
    scandinavia_PN, southernEurope_PN : PN ;
    -- atLeastAFew_Det : Det (problem 43's converse hypothesis, "at
    -- least a few committee members are from Sweden") - "at least"
    -- normally combines with a numeral Card via Numeral's own AdNum
    -- (problem 15's "at least three"), but "a few" is a Det, not a
    -- Card/Numeral, so there's no real combinator to build "at least a
    -- few" from aFew_Det the normal way. Self-declared as its own fixed
    -- string instead, same pattern as aLotOf_Det/worlds_Det/etc. Only
    -- needed for this one GF sentence - problem 43 itself is a
    -- countermodel (Batch3.lean's fracas_043_dir1/dir2), so this never
    -- needs a translate.py quantifier mapping.
    atLeastAFew_Det : Det ;
    -- northAmerican_A : A (problems 50-52's "a resident of the North
    -- American continent") - DictEngAbs has american_A but no compound
    -- demonym for "North American" specifically, and adjective-adjective
    -- compounding ("north" + "american") isn't a real RGL mechanism
    -- (AdjCN combines an AP with a CN, not two APs) - self-declared as
    -- its own fixed string instead, same pattern as worlds_Det/etc.
    northAmerican_A : A ;
    -- Section 2's own new proper nouns: smith_PN/jones_PN/anderson_PN
    -- (FraCaS's own recurring fictional cast for Section 2's contract-
    -- signing problems) aren't in a general-purpose dictionary -
    -- checked directly, same as every other word here, and unsurprising
    -- for personal surnames (cf. pavarotti_PN, a real person, still
    -- needed the same treatment in Section 1).
    smith_PN, jones_PN, anderson_PN : PN ;
    -- mp_N ("a Labour MP") is excluded above (joining irishman_N/
    -- person_N) and hand-declared here instead: same casing mismatch,
    -- "MP"/"MPs" not "mp"/"mp's".
    mp_N : N ;
    -- labour_A ("a Labour MP", the UK political party as an attributive
    -- adjective) and noted_A ("noted philosophers") are both genuine
    -- dictionary gaps - checked directly - self-declared as fixed
    -- strings, same pattern as most_Det/of_Prep/etc.
    labour_A, noted_A : A ;
    -- exactly_AdN ("exactly two lawyers", problems 85/86) is the exact-
    -- cardinality counterpart of Structural's own at_least_AdN/
    -- at_most_AdN (both already free, same AdNum-wrapping mechanism) -
    -- checked directly, no dictionary entry under this name.
    exactly_AdN : AdN ;
    -- Section 2 Batch2 (problems 98-113):
    -- bug32985_PN ("Bug # 32-985 is a known software fault") - FraCaS's
    -- own invented bug-tracker id, obviously not in any dictionary.
    bug32985_PN : PN ;
    -- known_A ("a known software fault") - genuine dictionary gap,
    -- checked directly, same pattern as labour_A/noted_A above.
    known_A : A ;
    -- apcomManager_N ("an APCOM manager", problems 103/104) is FraCaS's
    -- own fictional company name fused directly onto "manager" as ONE
    -- lexical item (mkN "APCOM manager" "APCOM managers"), the same
    -- move as northAmerican_A above, rather than trying to compound a
    -- self-declared "APCOM" proper noun with manager_N via CompoundCN -
    -- CompoundCN's own recipe always renders its first part in
    -- singular-nominative (see this file's own comment on CompoundCN
    -- above), which is irrelevant for an invariant acronym like "APCOM"
    -- but adds a moving part for no benefit; fusing it as a single noun
    -- also matches Batch2.lean's own fused `apcomManager` variable name.
    apcomManager_N : N ;
    -- likely_AdV ("Smith is likely to make a poor stock-market trader",
    -- problem 101) is used as a preverbal manner adverb via Verb's own
    -- AdVVP ("Smith likely makes...") rather than attempting the real
    -- "NP is likely to VP" raising-adjective construction, which this
    -- grammar has no combinator for (Extend's own PredVPS/VPI family
    -- handles VV-controlled infinitives, not A-controlled ones) -
    -- a documented simplification, the same spirit as this problem's own
    -- Lean formalization already simplifying the generic to a plain
    -- universal (see Batch2.lean's comment on fracas_101). Declared as
    -- its own fixed AdV string rather than derived from likely_A via
    -- PositAdvAdj, same "don't trust an unpinned RGL derivation, self-
    -- declare the literal string instead" reasoning as cheap_Adv above.
    likely_AdV : AdV ;
    -- Section 3 (Anaphora), problems 114-141:
    -- itel_PN, gfi_PN, mfi_PN, icm_PN (FraCaS's own recurring fictional
    -- companies, same reasoning as smith_PN/jones_PN/anderson_PN
    -- above) and r95103_PN ("R-95-103", problem 138's own invented
    -- report id, same reasoning as bug32985_PN) aren't in a
    -- general-purpose dictionary. mary_PN/john_PN/bill_PN/bt_PN are
    -- NOT here - all four already exist in DictEngAbs, checked
    -- directly, and are left free via the extends line.
    itel_PN, gfi_PN, mfi_PN, icm_PN, r95103_PN : PN ;
    -- customer_N/student_N: DictEngAbs only has gendered pairs
    -- (customerMasc_N/customerFem_N, studentMasc_N/studentFem_N), no
    -- plain gender-neutral form - the same gap person_N/mp_N filled
    -- above, checked directly the same way.
    customer_N, student_N : N ;
    -- salesDepartment_N ("the sales department", problem 132) is
    -- fused as one lexical item rather than built via CompoundCN:
    -- CompoundCN's own recipe always forces its first noun into
    -- singular-nominative (see this file's own comment on CompoundCN
    -- above), which would wrongly give "sale department" - "sales"
    -- stays plural in this compound irregularly, so it's self-declared
    -- as a fixed string instead, same move as apcomManager_N.
    salesDepartment_N : N ;
    -- payrise_N ("a large payrise", problem 139) - genuine dictionary
    -- gap (DictEngAbs only has the separate, un-compounded raise_N/
    -- rise_N), checked directly.
    payrise_N : N ;
    -- dedicated_A ("a dedicated line", problem 131) - genuine
    -- dictionary gap, checked directly.
    dedicated_A : A ;
    -- onTuesday_Adv/onWednesday_Adv (problem 127's "on Tuesday"/"on
    -- Wednesday") are self-declared as fixed strings rather than built
    -- from RGL's real Weekday/weekdayPunctualAdv subsystem - that
    -- subsystem is disproportionate machinery for the one sentence
    -- that needs it here (never reused elsewhere in this problem, and
    -- this problem's own premise is a GF-sentence-only check, never
    -- fed to translate.py), same "self-declare the literal string"
    -- call as worlds_Det/most_Det/etc. above.
    onTuesday_Adv, onWednesday_Adv : Adv ;
    -- missing_A ("two out of ten machines are missing", problems
    -- 124-126) is self-declared as a plain adjective rather than built
    -- from miss_V via Idiom's ProgrVP ("be missing") - Idiom turned out
    -- to be a genuinely broken extend for this grammar at the current
    -- pinned gf-rgl tag (a real "unknown identifier CleftAdv" error at
    -- PMCFG-generation time, caught locally before ever reaching CI,
    -- not assumed), and DictEngAbs has no missing_A of its own either
    -- (checked directly) - self-declaring the adjective directly
    -- sidesteps the whole module rather than debugging it, for a
    -- construction only these three sentences need.
    missing_A : A ;
    -- Section 4 (Ellipsis), problems 142-196: this section's own
    -- philosophy (Ellipsis.lean's header) is to build the RESOLVED,
    -- non-elliptical reading of each sentence directly - "Bill spoke
    -- to Mary" rather than modeling "So did Bill" as a literal
    -- ellipsis construction - the same move Section 3 already made for
    -- pronouns. That keeps this section's own vocabulary needs small:
    -- atFourOClock_Adv/atFiveOClock_Adv/onMonday_Adv/onFriday_Adv/
    -- onThursday_Adv (fixed one-off time adverbials, same
    -- "disproportionate to build the real Weekday/clock-time
    -- subsystem for one sentence" reasoning as onTuesday_Adv/
    -- onWednesday_Adv in Section 3) and partTime_Adv ("work part
    -- time" - genuine dictionary gap, checked directly).
    atFourOClock_Adv, atFiveOClock_Adv : Adv ;
    onMonday_Adv, onFriday_Adv, onThursday_Adv : Adv ;
    partTime_Adv : Adv ;
    -- Section 5 (Adjectives), problems 197-219: dumbo_PN/fido_PN/
    -- kim_PN (FraCaS's own recurring cast, not in a general-purpose
    -- dictionary - same reasoning as smith_PN/mfi_PN/etc. above;
    -- mickey_PN and bill_PN are NOT here, both already exist in
    -- DictEngAbs). fourLegged_A ("a four-legged animal") - genuine
    -- dictionary gap, checked directly.
    dumbo_PN, fido_PN, kim_PN : PN ;
    fourLegged_A : A ;
    -- Section 6 (Comparatives), problems 220-250: FraCaS's own
    -- recurring computer-market cast - pc6082_PN, itelXZ_PN, itelZX_PN,
    -- itelZY_PN, apcom_PN - none in a general-purpose dictionary (itel_PN
    -- itself is NOT here, already self-declared in Section 3).
    pc6082_PN, itelXZ_PN, itelZX_PN, itelZY_PN, apcom_PN : PN ;
    -- itelComputer_N ("an ITEL computer", problems 246-248) is fused as
    -- one lexical item, same reasoning as apcomManager_N in Section 2.
    itelComputer_N : N ;
    -- mips_N ("500 MIPS", a computer-speed unit) - genuine dictionary
    -- gap, checked directly.
    mips_N : N ;
    -- Section 7 (Temporal Reference), problems 251-308 (311-325 are
    -- skipped entirely - see FraCaSLogicEng.gf's own comment on why).
    -- first_A ("his first novel") - no plain ordinal adjective exists
    -- in DictEngAbs (only compounds like first_class_A/firstborn_A),
    -- checked directly - self-declared as an ordinary A, same
    -- "self-declare the literal string" move as fourLegged_A.
    first_A : A ;
    -- birmingham_PN - not in DictEngAbs (checked directly), FraCaS's
    -- own recurring city.
    birmingham_PN : PN ;
    -- This section's own recurring temporal PPs ("since 1992", "in
    -- 1993", "in March 1993", "in two hours", "for two years", "every
    -- month") are each self-declared as a fixed Adv rather than built
    -- from a general Year/Duration subsystem - the same "disproportionate
    -- machinery for a one-off adverbial" reasoning as onTuesday_Adv
    -- (Section 3) and atFourOClock_Adv (Section 4), just with more of
    -- them at once since this section repeats the pattern across many
    -- distinct years/durations.
    since1992_Adv, in1991_Adv, in1992_Adv, in1993_Adv, in1996_Adv : Adv ;
    inMarch1993_Adv, in1994_Adv, inJuly1994_Adv : Adv ;
    inTwoHours_Adv, inOneHour_Adv, inTwoYears_Adv : Adv ;
    forTwoYears_Adv, forAYear_Adv, forAnHour_Adv, forTwoHours_Adv : Adv ;
    everyMonth_Adv, everyWeek_Adv : Adv ;
    -- Added in a later round, extending Section 7 past its own initial
    -- "representative sample" (problems 319, 321): forEightYears_Adv/
    -- forMoreThanTenYears_Adv (same fixed-duration-adverbial reasoning
    -- as forTwoYears_Adv, just two more instances of the identical
    -- pattern). mortgage_N/interest_N/pay_V2/florence_PN/visit_V2/
    -- twice_Adv all already exist in DictEngAbs - checked directly, not
    -- self-declared.
    forEightYears_Adv, forMoreThanTenYears_Adv : Adv ;
    -- Two more of the same pattern (296, 299).
    forMoreThanTwoYears_Adv, forExactlyAYear_Adv : Adv ;
    -- Section 8 (Verbs), problems 326-333: mtalk_PN (ITEL's own
    -- invented product name, problems 326/327) is FraCaS's own
    -- fictional entity, not in a general-purpose dictionary. in1990_Adv/
    -- from1988to1992_Adv (self-declared fixed strings, same one-off
    -- reasoning as Section 7's temporal adverbials).
    mtalk_PN : PN ;
    in1990_Adv, from1988to1992_Adv : Adv ;
    -- Added for parsing FraCaS's own English (scripts/gen_blind_eval_
    -- parsed.py), where the hand-built trees above used rewordings:
    -- who_RP: FraCaS writes "tenors who are excellent"; IdRP realizes
    --   "that" by design (see FraCaSLogicEng.gf's problem 13 note).
    -- ExistNP: "there are/was NP" - FraCaS Section 1's own hypothesis
    --   shape. Self-declared rather than extending Idiom, which fails at
    --   PMCFG-generation time at this gf-rgl tag (see missing_A above);
    --   the lin is IdiomEng's own, verbatim.
    -- (just_Predet, "just one accountant" in 105-109, already comes
    --   from DictEng.)
    -- usedTo_VV: the frozen past-habitual "used to" (problems 29, 45,
    --   61, 77) - DictEng's use_VV is the freely-conjugated verb "use".
    who_RP : RP ;
    ExistNP : NP -> Cl ;
    usedTo_VV : VV ;
    -- Ellipsis and anaphora, FraCaS's own wording (Section 4):
    -- UncNeg: uncontracted negation ("Fido is NOT a small animal"); the
    --   grammar's own PNeg realizes the contracted "isn't".
    -- EllAux / ElliptS / SoS / TooS: VP ellipsis - "Bill didn't",
    --   "the students have [too]", "so did Bill". The elided VP is NOT
    --   represented here; scripts/gen_blind_eval_parsed.py resolves it to
    --   the antecedent clause's VP, the standard copy treatment.
    -- anaphOne_N / anaphOne_NP: one-anaphora - "a blue one", "owns one
    --   too"; likewise resolved to the antecedent's noun by the generator.
    UncNeg : Pol ;
    ElliptS : NP -> EllAux -> S ;
    SoS : EllAux -> NP -> S ;
    TooS : S -> S ;
    ellDid, ellDidnt, ellDoes, ellHas : EllAux ;
    anaphOne_N : N ;
    anaphOne_NP : NP ;
    -- Quantity comparatives, FraCaS's own wording (Section 6, 230-241):
    -- "more orders than APCOM", "more orders than APCOM did", "more
    --   orders than APCOM lost". An object NP whose meaning is a
    --   comparison of two counts (gf/translate.py: `More`); the "than"
    --   part is not a full clause here - the elided verb ("did", or
    --   nothing) is resolved to the main clause's verb by the translator,
    --   and an explicit one ("lost") is a bare past-tense V2 with the
    --   object gap that the compared noun fills.
    MoreThanNP : CN -> NP -> NP ;
    MoreThanAux : CN -> NP -> EllAux -> NP ;
    MoreThanV2 : CN -> NP -> V2 -> NP ;
    -- More of FraCaS's own wording, each confirmed by one linearize
    -- check in run_gf_tests.py's _FRACAS_ENGLISH_CHECKS:
    -- seeDo_V2V: perception with a bare infinitive ("Smith saw Jones
    --   sign the contract", 340-346). DictEng's see_V2V takes "to" ("saw
    --   Jones to sign"), which is not FraCaS's English.
    -- AndEveryNP: "every representative and every client WAS at the
    --   meeting" (89) - English allows singular agreement for coordinated
    --   "every" phrases; ConjNP only gives the plural.
    -- floatAll_AdV: a floated "all" before the verb ("the people who
    --   were at the meeting all voted", 93), as an AdV like "always".
    -- moreThan_AdN: "more than one company car" (104), the strict
    --   counterpart of Structural's at_least_AdN/at_most_AdN.
    -- ComparCN: a comparative inside a noun phrase ("John is a fatter
    --   politician than Bill", 216/217), which the RGL's ComparA can
    --   only place after the noun.
    seeDo_V2V : V2V ;
    AndEveryNP : CN -> CN -> NP ;
    floatAll_AdV : AdV ;
    moreThan_AdN : AdN ;
    ComparCN : A -> CN -> NP -> CN ;
    -- Ellipsis beyond a bare auxiliary, FraCaS's own wording (Section 4).
    -- The missing material is NOT represented; EndToEnd/gen_claims.py
    -- copies it from the antecedent clause, as for ElliptS.
    -- GapS / GapS2: gapping - a subject and one or two remnant adverbials,
    --   the verb left out ("[John went to Paris by car], and Bill by
    --   train [to Berlin]", 150-154).
    -- ElliptAdvS: VP ellipsis with a new adverbial ("Bill did at five
    --   o'clock", 145).
    -- FragAdvS / FragNPS: a fragment - an adverbial or a noun phrase
    --   standing alone as a sentence ("On Friday.", 165; "only one
    --   woman", 167).
    -- AndS / ButS: a sentence opened by "and"/"but" ("And to Sue.", 164).
    -- CommaAndS: "S, and S" (150-153, 178).
    -- ThenS: "then S" after an "if" clause (179).
    -- ellGoingTo: "is/are going to" as an ellipsis auxiliary (146).
    -- ComplVSBare: a clausal complement without "that" ("Bill said
    --   Peter did too", 175-178); the RGL's ComplVS always adds it.
    GapS : NP -> Adv -> S ;
    GapS2 : NP -> Adv -> Adv -> S ;
    ElliptAdvS : NP -> EllAux -> Adv -> S ;
    FragAdvS : Adv -> S ;
    FragNPS : NP -> S ;
    AndS : S -> S ;
    ButS : S -> S ;
    CommaAndS : S -> S -> S ;
    ThenS : S -> S ;
    ellGoingTo : EllAux ;
    ComplVSBare : VS -> S -> VP ;
    -- Tense and aspect, FraCaS's own wording (Section 7):
    -- currently_AdV: "ITEL currently has a factory" (251).
    -- ItIsNow / y1996_PN: "It is now 1996" (252-257), the utterance time
    --   the perfect's "since 1992" runs up to.
    -- atAQuarterPastFive_Adv: a clock time, lexicalized like
    --   atFiveOClock_Adv (311).
    currently_AdV : AdV ;
    ItIsNow : NP -> S ;
    y1996_PN : PN ;
    atAQuarterPastFive_Adv : Adv ;
    -- ProgrVP: the progressive, "was writing a report" (273, 274, 281,
    --   294, 327, 329). Declared here with the RGL's own linearization
    --   (IdiomEng's ProgrVP), since Idiom itself does not build with
    --   this grammar (see missing_A above).
    ProgrVP : VP -> VP ;
}
