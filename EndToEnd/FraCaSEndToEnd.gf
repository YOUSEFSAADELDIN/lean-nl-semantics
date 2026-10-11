-- The constructions only the end-to-end pipeline uses: FraCaS's own
-- wording, which its parser has to read and the hand-built trees of the
-- corpus's GF cross-check (gf/) never needed. Each is confirmed by one
-- linearize check in EndToEnd/english_checks.py. Extending gf/'s grammar
-- rather than editing it keeps part 2's grammar exactly what the
-- cross-check uses.
abstract FraCaSEndToEnd = FraCaSLogic ** {
  cat
    EllAux ;  -- the auxiliary left behind by VP ellipsis ("did", "didn't", "has", ...)
  fun
    -- Two more of the same pattern (296, 299).
    forMoreThanTwoYears_Adv, forExactlyAYear_Adv : Adv ;
    -- Added for parsing FraCaS's own English (scripts/gen_blind_eval_
    -- parsed.py), where the hand-built trees in gf/ used rewordings:
    -- who_RP: FraCaS writes "tenors who are excellent"; IdRP realizes
    --   "that" by design (see FraCaSLogicEng.gf's problem 13 note).
    -- ExistNP: "there are/was NP" - FraCaS Section 1's own hypothesis
    --   shape. Self-declared rather than extending Idiom, which fails at
    --   PMCFG-generation time at this gf-rgl tag (see missing_A in gf/FraCaSLogic.gf);
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
    -- check in english_checks.py:
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
    --   this grammar (see missing_A in gf/FraCaSLogic.gf).
    ProgrVP : VP -> VP ;
}
