#!/usr/bin/env python3
"""Automated `linearize` checks for gf/FraCaSLogic.gf/FraCaSLogicEng.gf,
run in CI (see .github/workflows/build.yml's build-gf job) so a future
grammar change gets checked automatically instead of relying on someone
manually running `linearize` and eyeballing the output, as every one of
these five sentences originally was (see gf/NOTES.md).

All checks run as one batch in a single shared `gf` session (feeding
every `linearize` command over stdin at once) - a version of this file
that instead ran each check as its own separate, short-lived `gf`
process found every single check producing blank output, a startup/
piping race specific to that lone-command-then-quit pattern, not a real
result (see NOTES.md). The shared-session approach is what's actually
reliable. To still keep one check's expected string from ever being
satisfied by a *different* check's output (the original bug this file
had), the session's output is split on the `FraCaSLogic> ` prompt
marker into one segment per command, in order, and each check is only
compared against its own segment.

Each segment's own expected string is checked by *exact* match against
the linearized output's first line, not a substring check - a
substring check let a real bug through silently for a while ("comes
cheap" is a prefix of the wrong output "comes cheaply", so it kept
"passing"; see FraCaSLogicEng.gf's own comment on that bug and its
fix), caught only once the tense-reconfirmation pass below made it
worth actually reading the full session output closely.

`CHECKS` (the list `main()` actually runs) is assembled from three
parts: `BASE_CHECKS` (each FraCaS sentence as this project's default
bare-`Cl` tree), `TENSE_RECONFIRMATIONS` (every one of those same
sentences again, generated automatically by wrapping the same tree in
`UttS (UseCl (TTAnt TPres ASimul) PPos (...))` - confirming tense-
wrapping doesn't break any of them), and `PILOT_TENSE_CHECKS` (two new,
hand-written checks - `TPast`/`TFut` in place of `TPres` - piloting
past/future tense specifically, since only present tense had ever been
confirmed via CI before).
"""

from __future__ import annotations

import os
import subprocess
import sys

GF_LIB_PATH = os.environ.get("GF_LIB_PATH", os.path.expanduser("~/gf-libs"))
PATH_ARG = f"-path=.:{GF_LIB_PATH}/alltenses:{GF_LIB_PATH}/prelude"
PROMPT = "FraCaSLogic> "

# Keep in sync with gf/FraCaSLogicEng.gf's own confirmed-commands
# comments and gf/translate.py's examples.
#
# Every entry below is a bare `Cl` (tenseless clause) - this project's
# deliberate default target category (see gf/FraCaSLogic.gf's file-top
# comment and NOTES.md's "SOLVED: UseCl/tense support" section). Each
# one is reconfirmed below under full `UttS (UseCl (TTAnt TPres ASimul)
# PPos ...)` tense-wrapping too (TENSE_RECONFIRMATIONS), so a future
# switch to full `S`/`Utt` for any of these sentences is known in
# advance not to hit a blank-linearization surprise.
BASE_CHECKS = [
    (
        "fracas_002",
        "linearize PredVP (DetCN every_Det (AdjCN (PositA italian_A) (UseN man_N))) "
        "(ComplVV want_VV (UseComp (CompCN (AdjCN (PositA great_A) (UseN tenor_N)))))",
        "every Italian man wants to be a great tenor",
    ),
    (
        "fracas_007",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA swedish_A)))",
        "some great tenors are Swedish",
    ),
    (
        "fracas_006",
        "linearize PredVP (DetCN (DetQuant no_Quant NumPl) "
        "(AdjCN (AdAP really_AdA (PositA great_A)) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA modest_A)))",
        "no really great tenors are modest",
    ),
    (
        "fracas_010",
        "linearize PredVP (DetCN most_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA italian_A)))",
        "most great tenors are Italian",
    ),
    (
        "fracas_033",
        "linearize PredVP (DetCN (DetQuant IndefArt NumSg) (UseN irishman_N)) "
        "(ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))",
        "an Irishman wins a Nobel prize",
    ),
    (
        "fracas_003",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) "
        "(AdjCN (PositA italian_A) (UseN man_N)))) "
        "(ComplVV want_VV (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) "
        "(AdjCN (PositA great_A) (UseN tenor_N))))))",
        "all Italian men want to be a great tenor",
    ),
    (
        "fracas_004_premise1",
        "linearize PredVP (DetCN each_Det (AdjCN (PositA italian_A) (UseN tenor_N))) "
        "(ComplVV want_VV (UseComp (CompAP (PositA great_A))))",
        "each Italian tenor wants to be great",
    ),
    (
        "fracas_004_premise2",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA italian_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA great_A)))",
        "some Italian tenors are great",
    ),
    (
        "fracas_008",
        "linearize PredVP (DetCN many_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA german_A)))",
        "many great tenors are German",
    ),
    (
        "fracas_009",
        "linearize PredVP (DetCN several_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA british_A)))",
        "several great tenors are British",
    ),
    (
        "fracas_015",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (UseN tenor_N)) "
        "(ComplSlash (SlashV2a take_V2) (AdvNP (MassNP (UseN part_N)) "
        "(PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN concert_N)))))",
        "at least three tenors take part in the concert",
    ),
    (
        "fracas_016",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_most_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2))))))))) (UseN tenor_N)) "
        "(AdvVP (ComplSlash (SlashV2a contribute_V2) (DetCN (DetQuant (PossPron they_Pron) NumPl) (UseN fee_N))) "
        "(PrepNP to_Prep (MassNP (UseN charity_N))))",
        "at most two tenors contribute their fees to charity",
    ),
    (
        "fracas_013_premise2",
        "linearize PredVP (DetCN (DetQuant IndefArt NumPl) "
        "(RelCN (AdjCN (PositA leading_A) (UseN tenor_N)) "
        "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAP (PositA excellent_A))))))) "
        "(UseComp (CompAP (PositA indispensable_A)))",
        "leading tenors that are excellent are indispensable",
    ),
    (
        "fracas_021_premise1",
        "linearize PredVP "
        "(AdvNP (DetCN (DetQuant DefArt NumPl) (UseN resident_N)) "
        "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN member_N) (UseN state_N))))) "
        "(ComplSlash (SlashV2a have_V2) (DetCN (DetQuant DefArt NumSg) "
        "(AdvCN (SentCN (UseN right_N) (EmbedVP (UseV live_V))) (PrepNP in_Prep (UsePN europe_PN)))))",
        "the residents of member states have the right to live in Europe",
    ),
    (
        "fracas_014_premise1",
        "linearize PredVP (DetCN neither_Det (AdjCN (PositA leading_A) (UseN tenor_N))) "
        "(AdvVP (UseV come_V) cheap_Adv)",
        "neither leading tenor comes cheap",
    ),
    (
        "fracas_014_premise2",
        "linearize PredVP "
        "(CountNP (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) "
        "(DetCN (DetQuant DefArt NumPl) (AdjCN (PositA leading_A) (UseN tenor_N)))) "
        "(UseComp (CompNP (UsePN pavarotti_PN)))",
        "one of the leading tenors is Pavarotti",
    ),
]

# Problems 18-21 ("three-premise universal transitivity", GQ.lean's
# every_trans shape) complete the bucket problem 21's own premise 1
# started. Every word these need - european_N, person_N, individual_N,
# travel_V, within_Prep, free_A - already exists in DictEngAbs/DictEng
# with exactly the recipe wanted (checked directly, same as the
# dictionary-integration work above), so none of them needed a single
# hand-declared fun/lin rule - a first for a whole mechanism bucket.
# _HAVE_RIGHT_VP ("have the right to live in Europe") is exactly
# fracas_021_premise1's own VP subtree, reused verbatim - it's shared
# by every premise below that needs it. Built with an explicit
# paren-balance assertion (not hand-typed into each f-string) after an
# earlier draft of this exact block had a stray extra ')' that only a
# balance check - not eyeballing - actually caught.
def _balanced(tree: str, label: str) -> str:
    opens, closes = tree.count("("), tree.count(")")
    assert opens == closes, f"{label}: unbalanced parens ({opens} open, {closes} close): {tree!r}"
    return tree


_HAVE_RIGHT_VP = _balanced(
    "(ComplSlash (SlashV2a have_V2) (DetCN (DetQuant DefArt NumSg) "
    "(AdvCN (SentCN (UseN right_N) (EmbedVP (UseV live_V))) (PrepNP in_Prep (UsePN europe_PN)))))",
    "_HAVE_RIGHT_VP",
)
# "can travel freely within Europe" - PositAdvAdj free_A is safe here
# (unlike cheap_A's own idiom, see FraCaSLogicEng.gf's comment) since
# "free" -> "freely" genuinely is the regular -ly derivation this
# combinator performs.
_CAN_TRAVEL_FREELY_VP = _balanced(
    "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) "
    "(PrepNP within_Prep (UsePN europe_PN))))",
    "_CAN_TRAVEL_FREELY_VP",
)


def _relative_subject(det: str, head_n: str) -> str:
    """DetCN det (RelCN (UseN head_n) (UseRCl ... (RelVP IdRP _HAVE_RIGHT_VP)))
    - "<det> <head_n> that has the right to live in Europe" (IdRP's own
    linearization here is "that", not "who" - confirmed via CI; matches
    problem 13's own "leading tenors that are excellent")."""
    return _balanced(
        f"(DetCN {det} (RelCN (UseN {head_n}) "
        f"(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP {_HAVE_RIGHT_VP}))))",
        f"_relative_subject({det},{head_n})",
    )


BASE_CHECKS += [
    (
        "fracas_018_premise1",
        f"linearize PredVP (DetCN every_Det (UseN european_N)) {_HAVE_RIGHT_VP}",
        "every European has the right to live in Europe",
    ),
    (
        "fracas_018_premise2",
        "linearize PredVP (DetCN every_Det (UseN european_N)) "
        "(UseComp (CompCN (UseN person_N)))",
        "every European is a person",
    ),
    (
        "fracas_018_premise3",
        f"linearize PredVP {_relative_subject('every_Det', 'person_N')} {_CAN_TRAVEL_FREELY_VP}",
        "every person that has the right to live in Europe can travel freely within Europe",
    ),
    (
        "fracas_019_premise1",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (UseN european_N))) "
        f"{_HAVE_RIGHT_VP}",
        "all Europeans have the right to live in Europe",
    ),
    (
        "fracas_020_premise1",
        f"linearize PredVP (DetCN each_Det (UseN european_N)) {_HAVE_RIGHT_VP}",
        "each European has the right to live in Europe",
    ),
    (
        "fracas_021_premise2",
        "linearize PredVP (PredetNP all_Predet (AdvNP (DetCN (DetQuant IndefArt NumPl) (UseN resident_N)) "
        "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN member_N) (UseN state_N)))))) "
        "(UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (UseN individual_N))))",
        "all residents of member states are individuals",
    ),
    (
        "fracas_021_premise3",
        f"linearize PredVP {_relative_subject('every_Det', 'individual_N')} {_CAN_TRAVEL_FREELY_VP}",
        "every individual that has the right to live in Europe can travel freely within Europe",
    ),
]


def _tense_reconfirm(label: str, cmd: str, expected: str):
    """Wraps an already-confirmed bare-`Cl` check's own tree in `UttS
    (UseCl (TTAnt TPres ASimul) PPos (...))`, expecting the exact same
    English string - a tense-wrapped sentence should say the same thing
    a bare Cl already said, just via a different category. Building
    this from BASE_CHECKS's own command strings (rather than retyping
    all 16 trees a second time) keeps the two forever in sync."""
    prefix = "linearize "
    assert cmd.startswith(prefix), cmd
    tree = cmd[len(prefix):]
    return (
        f"{label}_tense_reconfirm",
        f"linearize UttS (UseCl (TTAnt TPres ASimul) PPos ({tree}))",
        expected,
    )


# Remaining Batch1.lean problems (1, 5, 11, 12, 17) - the rest of
# FraCaS Section 1's first "batch" (2-4/6-10/13-16/18-21/33 already
# done). Every word these need except "the world's"/"greatest"
# (problem 1 - see FraCaSLogic.gf's own comment on why those two are
# self-declared) already exists in DictEngAbs/DictEng, checked
# directly the same way as every other bucket since the dictionary
# integration: italian_N, ambitious_A, sing_V2, popular_A, music_N,
# like_V2, poor_A, literature_N. few_Det (problem 12) is Structural's
# own, already free (same as many_Det).
BASE_CHECKS += [
    (
        "fracas_001_premise",
        "linearize PredVP (DetCN (DetQuant IndefArt NumSg) (UseN italian_N)) "
        "(ComplSlash (SlashV2a become_V2) (DetCN worlds_Det (AdjCN (PositA greatest_A) (UseN tenor_N))))",
        "an Italian becomes the world's greatest tenor",
    ),
    (
        "fracas_005_premise",
        "linearize PredVP (DetCN (DetQuant DefArt NumPl) (AdjCN (AdAP really_AdA (PositA ambitious_A)) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA italian_A)))",
        "the really ambitious tenors are Italian",
    ),
    (
        "fracas_011_premise1",
        "linearize PredVP (DetCN aFew_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(ComplSlash (SlashV2a sing_V2) (MassNP (AdjCN (PositA popular_A) (UseN music_N))))",
        "a few great tenors sing popular music",
    ),
    (
        "fracas_011_premise2",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(ComplSlash (SlashV2a like_V2) (MassNP (AdjCN (PositA popular_A) (UseN music_N))))",
        "some great tenors like popular music",
    ),
    (
        "fracas_012_premise",
        "linearize PredVP (DetCN few_Det (AdjCN (PositA great_A) (UseN tenor_N))) (UseComp (CompAP (PositA poor_A)))",
        "few great tenors are poor",
    ),
    (
        "fracas_017_premise",
        "linearize PredVP (DetCN (DetQuant IndefArt NumSg) (UseN irishman_N)) "
        "(ComplSlash (SlashV2a win_V2) (AdvNP (DetCN (DetQuant DefArt NumSg) (UseN nobelPrize_N)) "
        "(PrepNP for_Prep (MassNP (UseN literature_N)))))",
        "an Irishman wins the Nobel prize for literature",
    ),
]

# Problems 22-31 ("the delegate/commissioner subsection", Batch2.lean) -
# continuing the dictionary-first pattern: every word these need except
# aLotOf_Det/scandinavia_PN/southernEurope_PN (see FraCaSLogic.gf's own
# comment on why those three are self-declared) already exists in
# DictEngAbs/DictEng, checked directly the same way as every other
# bucket: delegate_N, finish_V2, report_N, survey_N, obtain_V2,
# interesting_A, result_N, get_V2, publish_V2, major_A, national_A,
# newspaper_N, european_N, resident_A, person_N, committee_N, member_N,
# sweden_PN, portugal_PN, commissioner_N, businessman_N, spend_V2,
# time_N, home_N. Every sentence below is normalized to present tense,
# same as every other BASE_CHECKS entry (problem 1's "became" -> "becomes",
# problem 17/33's "won" -> "wins") - the original FraCaS text's own past
# tense carries no logical difference GQ.lean's tenseless Props would
# ever need to preserve, including problem 29's "used to be": that's
# genuinely a habitual-past idiom, not just narrative past tense, but
# fracas_029's own Lean proof (every_mono_scope) doesn't encode any
# temporal structure either - it just needs *a* meaning-bearing scope
# predicate - so "are leading businessmen" is adequate here too, and
# avoids a real complication for no benefit: DictEng's own "used to" verb
# (`use_VV = mkVV (mkV "use")`) is a regular, freely-conjugated VV, not
# the actual frozen, only-ever-past "used to" idiom, so wrapping it in
# this project's default present-tense Cl would have produced the wrong,
# ungrammatical "use to be" rather than the idiom - sidestepped entirely
# by not needing "used to" at all.
#
# Problem 25's "got the results published in major national newspapers"
# is this bucket's one genuinely new VP shape: `PPartNP : NP -> V2 -> NP`
# ("the man seen") postmodifies "the results" with publish_V2's own past
# participle, `AdvNP` then attaches "in major national newspapers" to
# that whole modified NP, and `get_V2` takes the result as a plain direct
# object - a real, compositional reading of the causative-passive
# ("get X published"), not a self-declared shortcut.
#
# Problems 22/28/30/32 are the four adjunct-dropping-under-negation
# countermodels (same `.unknown` shape as problem 12) - both premise and
# hypothesis sentences are still confirmed via run_gf_tests.py (the two
# differ, unlike problem 12's single sentence), just not fed through
# translate.py (see gf/translate.py's own comment on why).
BASE_CHECKS += [
    (
        "fracas_022_premise",
        "linearize PredVP (DetCN (DetQuant no_Quant NumSg) (UseN delegate_N)) "
        "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))) "
        "(PrepNP on_Prep (MassNP (UseN time_N))))",
        "no delegate finishes the report on time",
    ),
    (
        "fracas_022_hypothesis",
        "linearize PredVP (DetCN (DetQuant no_Quant NumSg) (UseN delegate_N)) "
        "(ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N)))",
        "no delegate finishes the report",
    ),
    (
        "fracas_023_premise",
        "linearize PredVP (DetCN somePl_Det (UseN delegate_N)) "
        "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN survey_N))) "
        "(PrepNP on_Prep (MassNP (UseN time_N))))",
        "some delegates finish the survey on time",
    ),
    (
        "fracas_023_hypothesis",
        "linearize PredVP (DetCN somePl_Det (UseN delegate_N)) "
        "(ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN survey_N)))",
        "some delegates finish the survey",
    ),
    (
        "fracas_024_premise",
        "linearize PredVP (DetCN many_Det (UseN delegate_N)) "
        "(ComplSlash (SlashV2a obtain_V2) (AdvNP (DetCN (DetQuant IndefArt NumPl) "
        "(AdjCN (PositA interesting_A) (UseN result_N))) (PrepNP from_Prep "
        "(DetCN (DetQuant DefArt NumSg) (UseN survey_N)))))",
        "many delegates obtain interesting results from the survey",
    ),
    (
        "fracas_024_hypothesis",
        "linearize PredVP (DetCN many_Det (UseN delegate_N)) "
        "(ComplSlash (SlashV2a obtain_V2) (AdvNP (DetCN (DetQuant IndefArt NumPl) (UseN result_N)) "
        "(PrepNP from_Prep (DetCN (DetQuant DefArt NumSg) (UseN survey_N)))))",
        "many delegates obtain results from the survey",
    ),
    (
        "fracas_025_premise",
        "linearize PredVP (DetCN several_Det (UseN delegate_N)) "
        "(ComplSlash (SlashV2a get_V2) (AdvNP (PPartNP (DetCN (DetQuant DefArt NumPl) (UseN result_N)) publish_V2) "
        "(PrepNP in_Prep (DetCN (DetQuant IndefArt NumPl) "
        "(AdjCN (PositA major_A) (AdjCN (PositA national_A) (UseN newspaper_N)))))))",
        "several delegates get the results published in major national newspapers",
    ),
    (
        "fracas_025_hypothesis",
        "linearize PredVP (DetCN several_Det (UseN delegate_N)) "
        "(ComplSlash (SlashV2a get_V2) (PPartNP (DetCN (DetQuant DefArt NumPl) (UseN result_N)) publish_V2))",
        "several delegates get the results published",
    ),
    (
        "fracas_026_premise1",
        "linearize PredVP (DetCN most_Det (UseN european_N)) "
        "(UseComp (CompAP (AdvAP (PositA resident_A) (PrepNP in_Prep (UsePN europe_PN)))))",
        "most Europeans are resident in Europe",
    ),
    (
        "fracas_026_premise2",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (UseN european_N))) "
        "(UseComp (CompCN (UseN person_N)))",
        "all Europeans are people",
    ),
    (
        "fracas_026_premise3",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (RelCN (UseN person_N) "
        "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAP "
        "(AdvAP (PositA resident_A) (PrepNP in_Prep (UsePN europe_PN)))))))))) "
        f"{_CAN_TRAVEL_FREELY_VP}",
        "all people that are resident in Europe can travel freely within Europe",
    ),
    (
        "fracas_027_premise1",
        "linearize PredVP (DetCN aFew_Det (CompoundCN (UseN committee_N) (UseN member_N))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN sweden_PN))))",
        "a few committee members are from Sweden",
    ),
    (
        "fracas_027_premise2",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) "
        "(CompoundCN (UseN committee_N) (UseN member_N)))) (UseComp (CompCN (UseN person_N)))",
        "all committee members are people",
    ),
    (
        "fracas_027_premise3",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (RelCN (UseN person_N) "
        "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAdv "
        "(PrepNP from_Prep (UsePN sweden_PN))))))))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN scandinavia_PN))))",
        "all people that are from Sweden are from Scandinavia",
    ),
    (
        "fracas_028_premise1",
        "linearize PredVP (DetCN few_Det (CompoundCN (UseN committee_N) (UseN member_N))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN portugal_PN))))",
        "few committee members are from Portugal",
    ),
    (
        "fracas_028_premise2",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) "
        "(CompoundCN (UseN committee_N) (UseN member_N)))) (UseComp (CompCN (UseN person_N)))",
        "all committee members are people",
    ),
    (
        "fracas_028_premise3",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (RelCN (UseN person_N) "
        "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAdv "
        "(PrepNP from_Prep (UsePN portugal_PN))))))))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN southernEurope_PN))))",
        "all people that are from Portugal are from southern Europe",
    ),
    (
        "fracas_029_premise",
        "linearize PredVP (DetCN both_Det (UseN commissioner_N)) "
        "(UseComp (CompCN (AdjCN (PositA leading_A) (UseN businessman_N))))",
        "both commissioners are leading businessmen",
    ),
    (
        "fracas_029_hypothesis",
        "linearize PredVP (DetCN both_Det (UseN commissioner_N)) (UseComp (CompCN (UseN businessman_N)))",
        "both commissioners are businessmen",
    ),
    (
        "fracas_030_premise",
        "linearize PredVP (DetCN neither_Det (UseN commissioner_N)) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (DetCN aLotOf_Det (UseN time_N))) "
        "(PrepNP at_Prep (MassNP (UseN home_N))))",
        "neither commissioner spends a lot of time at home",
    ),
    (
        "fracas_030_hypothesis",
        "linearize PredVP (DetCN neither_Det (UseN commissioner_N)) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))",
        "neither commissioner spends time at home",
    ),
    (
        "fracas_031_premise",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (UseN commissioner_N)) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (DetCN aLotOf_Det (UseN time_N))) "
        "(PrepNP at_Prep (MassNP (UseN home_N))))",
        "at least three commissioners spend a lot of time at home",
    ),
    (
        "fracas_031_hypothesis",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (UseN commissioner_N)) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))",
        "at least three commissioners spend time at home",
    ),
    (
        "fracas_032_premise",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_most_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 pot110))))))) (UseN commissioner_N)) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (DetCN aLotOf_Det (UseN time_N))) "
        "(PrepNP at_Prep (MassNP (UseN home_N))))",
        "at most ten commissioners spend a lot of time at home",
    ),
    (
        "fracas_032_hypothesis",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_most_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 pot110))))))) (UseN commissioner_N)) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))",
        "at most ten commissioners spend time at home",
    ),
]

# Problems 34-45 (Batch3.lean's "converse" subsection, continuing 32/33
# already done) - almost every sentence here already exists verbatim as
# a confirmed check under an earlier problem's label (34-36's own
# premises 2/3 = 18's; 34/35/36's hypotheses = 18/19/20's own premise 1;
# 39/40/41 are exactly 23/24/25's premise/hypothesis pairs, swapped;
# 42's premises 2/3 = 26's; 43's premises 2/3 = 27's; 44's premises 2/3
# = 28's; 45 = 29's premise/hypothesis pair, swapped) - not re-added
# under a new label here, since that would just re-run an identical
# `linearize` command for no new information; only the genuinely new
# sentences below get their own check. anywhere_Adv (problem 37's "the
# right to live ANYWHERE in Europe", unlike 18-21/34-36's plain "in
# Europe") is free via DictEngAbs, not self-declared - checked directly,
# same as every other word here.
_HAVE_RIGHT_ANYWHERE_VP = _balanced(
    "(ComplSlash (SlashV2a have_V2) (DetCN (DetQuant DefArt NumSg) "
    "(AdvCN (SentCN (UseN right_N) (EmbedVP (AdvVP (UseV live_V) anywhere_Adv))) "
    "(PrepNP in_Prep (UsePN europe_PN)))))",
    "_HAVE_RIGHT_ANYWHERE_VP",
)
_RESIDENTS_OF_MEMBER_STATES_NP = _balanced(
    "(AdvNP (DetCN (DetQuant DefArt NumPl) (UseN resident_N)) "
    "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN member_N) (UseN state_N)))))",
    "_RESIDENTS_OF_MEMBER_STATES_NP",
)

BASE_CHECKS += [
    (
        "fracas_034_premise1",
        f"linearize PredVP (DetCN every_Det (UseN european_N)) {_CAN_TRAVEL_FREELY_VP}",
        "every European can travel freely within Europe",
    ),
    (
        "fracas_035_premise1",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (UseN european_N))) "
        f"{_CAN_TRAVEL_FREELY_VP}",
        "all Europeans can travel freely within Europe",
    ),
    (
        "fracas_036_premise1",
        f"linearize PredVP (DetCN each_Det (UseN european_N)) {_CAN_TRAVEL_FREELY_VP}",
        "each European can travel freely within Europe",
    ),
    (
        "fracas_037_premise1",
        f"linearize PredVP {_RESIDENTS_OF_MEMBER_STATES_NP} {_CAN_TRAVEL_FREELY_VP}",
        "the residents of member states can travel freely within Europe",
    ),
    (
        "fracas_037_premise3",
        f"linearize PredVP {_relative_subject('every_Det', 'individual_N').replace(_HAVE_RIGHT_VP, _HAVE_RIGHT_ANYWHERE_VP)} "
        f"{_CAN_TRAVEL_FREELY_VP}",
        "every individual that has the right to live anywhere in Europe can travel freely within Europe",
    ),
    (
        "fracas_037_hypothesis",
        f"linearize PredVP {_RESIDENTS_OF_MEMBER_STATES_NP} {_HAVE_RIGHT_ANYWHERE_VP}",
        "the residents of member states have the right to live anywhere in Europe",
    ),
    (
        "fracas_038_premise",
        "linearize PredVP (DetCN someSg_Det (UseN delegate_N)) "
        "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))) "
        "(PrepNP on_Prep (MassNP (UseN time_N))))",
        "some delegate finishes the report on time",
    ),
    (
        "fracas_042_premise1",
        f"linearize PredVP (DetCN most_Det (UseN european_N)) {_CAN_TRAVEL_FREELY_VP}",
        "most Europeans can travel freely within Europe",
    ),
    (
        "fracas_043_premise1",
        "linearize PredVP (DetCN aFew_Det (CompoundCN (UseN committee_N) (UseN member_N))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN scandinavia_PN))))",
        "a few committee members are from Scandinavia",
    ),
    (
        "fracas_043_hypothesis",
        "linearize PredVP (DetCN atLeastAFew_Det (CompoundCN (UseN committee_N) (UseN member_N))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN sweden_PN))))",
        "at least a few committee members are from Sweden",
    ),
    (
        "fracas_044_premise1",
        "linearize PredVP (DetCN few_Det (CompoundCN (UseN committee_N) (UseN member_N))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN southernEurope_PN))))",
        "few committee members are from southern Europe",
    ),
    # fracas_044's own hypothesis ("There are few committee members from
    # Portugal.") is deliberately NOT here: it's a genuine "there are"
    # existential construction, a different clause shape from every
    # other check in this file (a plain predicative "NP is/are Comp"),
    # and out of scope for this batch - same principled omission as
    # problem 28's identical-shaped hypothesis one bucket ago. Doesn't
    # affect the Lean cross-check either way: translate.py only ever
    # feeds a chain theorem's PREMISES through, never its conclusion.
]

# Problems 46-59 (Batch4.lean) - mostly new vocabulary/subsections
# rather than one theme. Every word needed except northAmerican_A (see
# FraCaSLogic.gf's own comment on why) already exists in DictEngAbs,
# checked directly the same way as every other bucket: swedeMasc_N,
# canadian_A, continent_N, western_A, country_N, irish_A, british_A,
# portuguese_A, female_A. As with problems 34-45, many of these
# sentences already exist verbatim as a confirmed check under an
# earlier problem's own label (47's premise/hypothesis pair = 31's
# hypothesis/premise, swapped; 48's premise/hypothesis pair = 32's
# hypothesis/premise, swapped; 54's hypothesis = 38's premise; 55/56/57's
# hypotheses = 23/24/25's premises; 58's hypothesis = 42's premise 1) -
# not re-added under a new label. Only the genuinely new sentences get
# their own check below.
_RESIDENT_OF_NAC_CN = _balanced(
    "(AdvCN (UseN resident_N) (PrepNP of_Prep (DetCN (DetQuant DefArt NumSg) "
    "(AdjCN (PositA northAmerican_A) (UseN continent_N)))))",
    "_RESIDENT_OF_NAC_CN",
)
_CANADIAN_RESIDENT_CN = "(AdjCN (PositA canadian_A) (UseN resident_N))"
_WESTERN_COUNTRY_CN = "(AdjCN (PositA western_A) (UseN country_N))"
_MAJOR_WESTERN_COUNTRY_CN = f"(AdjCN (PositA major_A) {_WESTERN_COUNTRY_CN})"

BASE_CHECKS += [
    (
        "fracas_046_hypothesis",
        "linearize PredVP (CountNP (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) "
        "(DetCN (DetQuant DefArt NumPl) (UseN commissioner_N))) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (DetCN aLotOf_Det (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))",
        "one of the commissioners spends a lot of time at home",
    ),
    (
        "fracas_049_premise1",
        "linearize PredVP (DetCN (DetQuant IndefArt NumSg) (UseN swedeMasc_N)) "
        "(ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))",
        "a Swede wins a Nobel prize",
    ),
    (
        "fracas_049_premise2",
        "linearize PredVP (DetCN every_Det (UseN swedeMasc_N)) (UseComp (CompCN (UseN scandinavian_N)))",
        "every Swede is a Scandinavian",
    ),
    (
        "fracas_050_premise1",
        f"linearize PredVP (DetCN every_Det {_CANADIAN_RESIDENT_CN}) {_CAN_TRAVEL_FREELY_VP}",
        "every Canadian resident can travel freely within Europe",
    ),
    (
        "fracas_050_premise2",
        f"linearize PredVP (DetCN every_Det {_CANADIAN_RESIDENT_CN}) "
        f"(UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) {_RESIDENT_OF_NAC_CN})))",
        "every Canadian resident is a resident of the North American continent",
    ),
    (
        "fracas_050_hypothesis",
        f"linearize PredVP (DetCN every_Det {_RESIDENT_OF_NAC_CN}) {_CAN_TRAVEL_FREELY_VP}",
        "every resident of the North American continent can travel freely within Europe",
    ),
    (
        "fracas_051_premise1",
        f"linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) {_CANADIAN_RESIDENT_CN})) "
        f"{_CAN_TRAVEL_FREELY_VP}",
        "all Canadian residents can travel freely within Europe",
    ),
    (
        "fracas_051_hypothesis",
        f"linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) {_RESIDENT_OF_NAC_CN})) "
        f"{_CAN_TRAVEL_FREELY_VP}",
        "all residents of the North American continent can travel freely within Europe",
    ),
    (
        "fracas_052_premise1",
        f"linearize PredVP (DetCN each_Det {_CANADIAN_RESIDENT_CN}) {_CAN_TRAVEL_FREELY_VP}",
        "each Canadian resident can travel freely within Europe",
    ),
    (
        "fracas_052_hypothesis",
        f"linearize PredVP (DetCN each_Det {_RESIDENT_OF_NAC_CN}) {_CAN_TRAVEL_FREELY_VP}",
        "each resident of the North American continent can travel freely within Europe",
    ),
    (
        "fracas_053_premise1",
        "linearize PredVP (AdvNP (DetCN (DetQuant DefArt NumPl) (UseN resident_N)) "
        f"(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) {_MAJOR_WESTERN_COUNTRY_CN}))) "
        f"{_CAN_TRAVEL_FREELY_VP}",
        "the residents of major Western countries can travel freely within Europe",
    ),
    (
        "fracas_053_premise2",
        "linearize PredVP (PredetNP all_Predet (AdvNP (DetCN (DetQuant IndefArt NumPl) (UseN resident_N)) "
        f"(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) {_MAJOR_WESTERN_COUNTRY_CN})))) "
        "(UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdvCN (UseN resident_N) "
        f"(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) {_WESTERN_COUNTRY_CN}))))))",
        "all residents of major Western countries are residents of Western countries",
    ),
    (
        "fracas_053_hypothesis",
        "linearize PredVP (AdvNP (DetCN (DetQuant DefArt NumPl) (UseN resident_N)) "
        f"(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) {_WESTERN_COUNTRY_CN}))) "
        f"{_HAVE_RIGHT_VP}",
        "the residents of Western countries have the right to live in Europe",
    ),
    (
        "fracas_054_premise",
        "linearize PredVP (DetCN (DetQuant no_Quant NumSg) (AdjCN (PositA scandinavian_A) (UseN delegate_N))) "
        "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))) "
        "(PrepNP on_Prep (MassNP (UseN time_N))))",
        "no Scandinavian delegate finishes the report on time",
    ),
    (
        "fracas_055_premise",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA irish_A) (UseN delegate_N))) "
        "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN survey_N))) "
        "(PrepNP on_Prep (MassNP (UseN time_N))))",
        "some Irish delegates finish the survey on time",
    ),
    (
        "fracas_056_premise",
        "linearize PredVP (DetCN many_Det (AdjCN (PositA british_A) (UseN delegate_N))) "
        "(ComplSlash (SlashV2a obtain_V2) (AdvNP (DetCN (DetQuant IndefArt NumPl) "
        "(AdjCN (PositA interesting_A) (UseN result_N))) (PrepNP from_Prep "
        "(DetCN (DetQuant DefArt NumSg) (UseN survey_N)))))",
        "many British delegates obtain interesting results from the survey",
    ),
    (
        "fracas_057_premise",
        "linearize PredVP (DetCN several_Det (AdjCN (PositA portuguese_A) (UseN delegate_N))) "
        "(ComplSlash (SlashV2a get_V2) (AdvNP (PPartNP (DetCN (DetQuant DefArt NumPl) (UseN result_N)) publish_V2) "
        "(PrepNP in_Prep (DetCN (DetQuant IndefArt NumPl) "
        "(AdjCN (PositA major_A) (AdjCN (PositA national_A) (UseN newspaper_N)))))))",
        "several Portuguese delegates get the results published in major national newspapers",
    ),
    (
        "fracas_058_premise",
        "linearize PredVP (DetCN most_Det (RelCN (UseN european_N) "
        "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAP "
        "(AdvAP (PositA resident_A) (PrepNP in_Prep (UsePN europe_PN))))))))) "
        f"{_CAN_TRAVEL_FREELY_VP}",
        "most Europeans that are resident in Europe can travel freely within Europe",
    ),
    (
        "fracas_059_premise",
        "linearize PredVP (DetCN aFew_Det (AdjCN (PositA female_A) (CompoundCN (UseN committee_N) (UseN member_N)))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN scandinavia_PN))))",
        "a few female committee members are from Scandinavia",
    ),
    (
        "fracas_059_hypothesis",
        "linearize PredVP (DetCN atLeastAFew_Det (CompoundCN (UseN committee_N) (UseN member_N))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN scandinavia_PN))))",
        "at least a few committee members are from Scandinavia",
    ),
]

# Problems 60-80 (Batch5.lean, completing Section 1's 80 problems) -
# "restrictor variance": narrowing/widening which subgroup a
# determiner ranges over. Every word needed (business_N, outside_Prep,
# male_A) already exists in DictEngAbs, checked directly the same way
# as every other bucket. This is the highest-reuse bucket yet: most of
# these 21 problems' own premise/hypothesis sentences are EXACT
# byte-for-byte matches of a sentence already confirmed under an
# earlier problem's label (66/67/68's own three sentences = 50/51/52's,
# entirely, zero new GF; 69's premise 2 = 53's; 70/71/72/73/76/77/78/80's
# stated premise = 22/23/24/25/28/61/30/32's, respectively) - not
# re-added under a new label. Only the genuinely new sentences below
# get their own check. 64's own premise ("at most ten female
# commissioners spend time at home") is itself reused again as 80's
# hypothesis (same restrictor+scope combination both problems need).
BASE_CHECKS += [
    (
        "fracas_060_premise",
        "linearize PredVP (DetCN few_Det (AdjCN (PositA female_A) (CompoundCN (UseN committee_N) (UseN member_N)))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN southernEurope_PN))))",
        "few female committee members are from southern Europe",
    ),
    (
        "fracas_061_premise",
        "linearize PredVP (DetCN both_Det (AdjCN (PositA female_A) (UseN commissioner_N))) "
        "(UseComp (CompAdv (PrepNP in_Prep (MassNP (UseN business_N)))))",
        "both female commissioners are in business",
    ),
    (
        "fracas_061_hypothesis",
        "linearize PredVP (DetCN both_Det (UseN commissioner_N)) "
        "(UseComp (CompAdv (PrepNP in_Prep (MassNP (UseN business_N)))))",
        "both commissioners are in business",
    ),
    (
        "fracas_062_premise",
        "linearize PredVP (DetCN neither_Det (AdjCN (PositA female_A) (UseN commissioner_N))) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (DetCN aLotOf_Det (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))",
        "neither female commissioner spends a lot of time at home",
    ),
    (
        "fracas_063_premise",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (AdjCN (PositA female_A) (UseN commissioner_N))) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))",
        "at least three female commissioners spend time at home",
    ),
    (
        "fracas_064_premise",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_most_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 pot110))))))) (AdjCN (PositA female_A) (UseN commissioner_N))) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))",
        "at most ten female commissioners spend time at home",
    ),
    (
        "fracas_065_premise1",
        "linearize PredVP (DetCN (DetQuant IndefArt NumSg) (UseN scandinavian_N)) "
        "(ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))",
        "a Scandinavian wins a Nobel prize",
    ),
    (
        "fracas_069_premise1",
        "linearize PredVP (AdvNP (DetCN (DetQuant DefArt NumPl) (UseN resident_N)) "
        "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA western_A) (UseN country_N))))) "
        f"{_CAN_TRAVEL_FREELY_VP}",
        "the residents of Western countries can travel freely within Europe",
    ),
    (
        "fracas_069_hypothesis",
        "linearize PredVP (AdvNP (DetCN (DetQuant DefArt NumPl) (UseN resident_N)) "
        f"(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) {_MAJOR_WESTERN_COUNTRY_CN}))) "
        f"{_HAVE_RIGHT_VP}",
        "the residents of major Western countries have the right to live in Europe",
    ),
    (
        "fracas_070_hypothesis",
        "linearize PredVP (DetCN someSg_Det (AdjCN (PositA scandinavian_A) (UseN delegate_N))) "
        "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))) "
        "(PrepNP on_Prep (MassNP (UseN time_N))))",
        "some Scandinavian delegate finishes the report on time",
    ),
    (
        "fracas_074_hypothesis",
        "linearize PredVP (DetCN most_Det (RelCN (UseN european_N) "
        "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (UseComp (CompAP "
        "(AdvAP (PositA resident_A) (PrepNP outside_Prep (UsePN europe_PN))))))))) "
        f"{_CAN_TRAVEL_FREELY_VP}",
        "most Europeans that are resident outside Europe can travel freely within Europe",
    ),
    (
        "fracas_075_hypothesis",
        "linearize PredVP (DetCN atLeastAFew_Det (AdjCN (PositA female_A) (CompoundCN (UseN committee_N) (UseN member_N)))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN scandinavia_PN))))",
        "at least a few female committee members are from Scandinavia",
    ),
    (
        "fracas_078_hypothesis",
        "linearize PredVP (CountNP (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) "
        "(DetCN (DetQuant DefArt NumPl) (AdjCN (PositA female_A) (UseN commissioner_N)))) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (DetCN aLotOf_Det (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))",
        "one of the female commissioners spends a lot of time at home",
    ),
    (
        "fracas_079_hypothesis",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (AdjCN (PositA male_A) (UseN commissioner_N))) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))",
        "at least three male commissioners spend time at home",
    ),
]

# FraCaS Section 2 (Plurals), problems 81-97 (Section2/Batch1.lean) -
# this project's first bucket outside Section 1's own determiner-
# monotonicity phenomena. Needs a genuinely new module (Conjunction,
# for named-individual/CN conjunction - "Smith, Jones and Anderson",
# "representative and client") plus new vocabulary: smith_PN/jones_PN/
# anderson_PN (FraCaS's own recurring cast, self-declared - not in a
# general dictionary), mp_N (excluded/hand-declared for capitalization,
# same reason as irishman_N/person_N), labour_A/noted_A/exactly_AdN
# (genuine dictionary gaps, self-declared). Every other word
# (lawyer_N, accountant_N, sign_V2, contract_N, representativeMasc_N, client_N,
# meeting_N, chairman_N, item_N, agenda_N, inhabitant_N, cambridge_PN,
# ancient_A, greek_N, philosopher_N, software_N, fault_N, blame_V2,
# system_N, failure_N, vote_V, new_A, read_out_V2) already exists in
# DictEngAbs, checked directly the same way as every Section 1 bucket.
BASE_CHECKS += [
    (
        "fracas_081_premise",
        "linearize PredVP (ConjNP and_Conj (ConsNP (UsePN smith_PN) (BaseNP (UsePN jones_PN) (UsePN anderson_PN)))) "
        "(ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))",
        "Smith , Jones and Anderson sign the contract",
    ),
    (
        "fracas_081_hypothesis",
        "linearize PredVP (UsePN jones_PN) (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))",
        "Jones signs the contract",
    ),
    (
        "fracas_082_premise",
        "linearize PredVP (ConjNP and_Conj (ConsNP (UsePN smith_PN) (BaseNP (UsePN jones_PN) (DetCN several_Det (UseN lawyer_N))))) "
        "(ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))",
        "Smith , Jones and several lawyers sign the contract",
    ),
    (
        "fracas_083_premise",
        "linearize PredVP (ConjNP either7or_DConj (ConsNP (UsePN smith_PN) (BaseNP (UsePN jones_PN) (UsePN anderson_PN)))) "
        "(ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))",
        "either Smith , Jones or Anderson signs the contract",
    ),
    (
        "fracas_085_premise",
        "linearize PredVP (ConjNP and_Conj (BaseNP "
        "(DetCN (DetQuant IndefArt (NumCard (AdNum exactly_AdN (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2))))))))) (UseN lawyer_N)) "
        "(DetCN (DetQuant IndefArt (NumCard (AdNum exactly_AdN (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (UseN accountant_N)))) "
        "(ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))",
        "exactly two lawyers and exactly three accountants sign the contract",
    ),
    (
        "fracas_085_hypothesis",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n6)))))))) (UseN lawyer_N)) "
        "(ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))",
        "six lawyers sign the contract",
    ),
    (
        "fracas_086_hypothesis",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n6)))))))) (UseN accountant_N)) "
        "(ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))",
        "six accountants sign the contract",
    ),
    (
        "fracas_088_premise",
        "linearize PredVP (DetCN every_Det (ConjCN and_Conj (BaseCN (UseN representativeMasc_N) (UseN client_N)))) "
        "(UseComp (CompAdv (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "every representative and client is at the meeting",
    ),
    (
        "fracas_089_premise",
        "linearize PredVP (DetCN every_Det (ConjCN or_Conj (BaseCN (UseN representativeMasc_N) (UseN client_N)))) "
        "(UseComp (CompAdv (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "every representative or client is at the meeting",
    ),
    (
        "fracas_089_hypothesis_rep",
        "linearize PredVP (DetCN every_Det (UseN representativeMasc_N)) (UseComp (CompAdv (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "every representative is at the meeting",
    ),
    (
        "fracas_089_hypothesis_client",
        "linearize PredVP (DetCN every_Det (UseN client_N)) (UseComp (CompAdv (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "every client is at the meeting",
    ),
    (
        "fracas_090_premise",
        "linearize PredVP (DetCN (DetQuant DefArt NumSg) (UseN chairman_N)) "
        "(ComplSlash (SlashV2a read_out_V2) (DetCN (DetQuant DefArt NumPl) "
        "(AdvCN (UseN item_N) (PrepNP on_Prep (DetCN (DetQuant DefArt NumSg) (UseN agenda_N))))))",
        "the chairman reads out the items on the agenda",
    ),
    (
        "fracas_090_hypothesis",
        "linearize PredVP (DetCN (DetQuant DefArt NumSg) (UseN chairman_N)) "
        "(ComplSlash (SlashV2a read_out_V2) (DetCN every_Det "
        "(AdvCN (UseN item_N) (PrepNP on_Prep (DetCN (DetQuant DefArt NumSg) (UseN agenda_N))))))",
        "the chairman reads out every item on the agenda",
    ),
    (
        "fracas_091_premise",
        "linearize PredVP (DetCN (DetQuant DefArt NumPl) (RelCN (UseN person_N) "
        "(UseRCl (TTAnt TPast ASimul) PPos (RelVP IdRP (UseComp (CompAdv "
        "(PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N))))))))) "
        "(AdvVP (UseV vote_V) (PrepNP for_Prep (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN chairman_N)))))",
        "the people that were at the meeting vote for a new chairman",
    ),
    (
        "fracas_092_premise",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant DefArt NumPl) (RelCN (UseN person_N) "
        "(UseRCl (TTAnt TPast ASimul) PPos (RelVP IdRP (UseComp (CompAdv "
        "(PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))))))) "
        "(AdvVP (UseV vote_V) (PrepNP for_Prep (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN chairman_N)))))",
        "all the people that were at the meeting vote for a new chairman",
    ),
    (
        "fracas_092_hypothesis",
        "linearize PredVP everyone_NP (AdvVP (AdvVP (UseV vote_V) (PrepNP for_Prep "
        "(DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN chairman_N))))) "
        "(PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N))))",
        "everyone votes for a new chairman at the meeting",
    ),
    (
        "fracas_094_premise",
        "linearize PredVP (AdvNP (DetCN (DetQuant DefArt NumPl) (UseN inhabitant_N)) (PrepNP of_Prep (UsePN cambridge_PN))) "
        "(AdvVP (UseV vote_V) (PrepNP for_Prep (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA labour_A) (UseN mp_N)))))",
        "the inhabitants of Cambridge vote for a Labour MP",
    ),
    (
        "fracas_095_premise",
        "linearize PredVP (DetCN (DetQuant DefArt NumPl) (AdjCN (PositA ancient_A) (UseN greek_N))) "
        "(UseComp (CompCN (AdjCN (PositA noted_A) (UseN philosopher_N))))",
        "the ancient Greeks are noted philosophers",
    ),
    (
        "fracas_096_premise",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant DefArt NumPl) (AdjCN (PositA ancient_A) (UseN greek_N)))) "
        "(UseComp (CompCN (AdjCN (PositA noted_A) (UseN philosopher_N))))",
        "all the ancient Greeks are noted philosophers",
    ),
    (
        "fracas_096_hypothesis",
        "linearize PredVP (DetCN every_Det (AdjCN (PositA ancient_A) (UseN greek_N))) "
        "(UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA noted_A) (UseN philosopher_N)))))",
        "every ancient Greek is a noted philosopher",
    ),
    (
        "fracas_097_premise",
        "linearize PredVP (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN software_N) (UseN fault_N))) "
        "(AdvVP (PassV2 blame_V2) (PrepNP for_Prep (DetCN (DetQuant DefArt NumSg) (CompoundCN (UseN system_N) (UseN failure_N)))))",
        "software faults are blamed for the system failure",
    ),
]

# Section 2 Batch2, problems 98-113 (Section2/Batch2.lean). Unlike
# Batch1's checks above, most of these need an explicit past (or
# future, for 102) tense wrapper - `UttS (UseCl (TTAnt TPast ASimul)
# PPos (...))` - rather than the bare `linearize PredVP ...` form:
# a bare PredVP's own default rendering is present tense (confirmed
# throughout Batch1), but nearly every Batch2 sentence is itself past
# tense ("were blamed", "was a client", "signed"), so leaving it bare
# would silently check the wrong tense. Copied verbatim, this doubles
# as this batch's own `TENSE_RECONFIRMATIONS` coverage isn't needed
# for these entries specifically, so they're written pre-wrapped
# instead of relying on the auto-wrapper (which assumes a bare Cl,
# same reasoning as _FRACAS_084_HYPOTHESIS_CHECK below).
#
# New words this batch needed (all cross-checked directly against
# gf-rgl's DictEngAbs/DictEng first, same discipline as every earlier
# batch): bug32985_PN, known_A, apcomManager_N, likely_AdV (all
# self-declared - see FraCaSLogic.gf's own comments for why each one
# isn't sourced from the dictionary). Every other word (software_N,
# fault_N, system_N, failure_N, client_N, demonstration_N,
# performance_N, impress_V2, university_N, graduate_N, poor_A,
# stock_N, market_N, trader_N, make_V2, company_N, car_N, have_V2,
# accountant_N, attend_V2, meeting_N, contract_N, sign_V2,
# another_Quant, also_AdV, most_Det, somePl_Det, someSg_Det,
# only_Predet) already exists in DictEngAbs/Structural, checked the
# same way as every earlier bucket.
#
# GenNP (Extend module, newly extended - see FraCaSLogic.gf's own
# comment on why) gives problem 99/100's "the system's performance" a
# REAL prenominal genitive, unlike worlds_Det's self-declared-string
# workaround back in Section 1 problem 1.
#
# Two confirmed, documented near-misses from the real toolchain (not
# just this file's own guesses), both accepted as the closest buildable
# rendering rather than chased further:
#   - only_Predet's own fixed lin is "only", not "just" - FraCaS's own
#     "Just one accountant attended the meeting" (105/106/107/108)
#     comes out "only one accountant attended the meeting" here.
#     Confirmed directly against gf-rgl's own English FraCaS treebank
#     (src/english/treebank.txt), which independently parses this exact
#     FraCaS sentence to the same only_Predet tree - so this isn't a
#     one-off guess, it's this RGL's own standard analysis of "just
#     one" as a scalar-focus determiner, spelled "only".
#   - CompoundCN's own recipe (plain concatenation, no hyphen
#     insertion) can't produce FraCaS's hyphenated "stock-market" -
#     "stock market" (space, no hyphen) is what's actually achievable,
#     same spirit as the ancient_A/"ancient Greeks" lowercase
#     acceptance in Batch1.
#
# 101's hypothesis ("Smith is likely to make a poor stock-market
# trader") is a genuine raising construction (an adjective controlling
# an infinitival complement) this grammar has no combinator for -
# paraphrased instead as "Smith likely makes..." via Verb's own AdVVP
# (a plain preverbal adverb), matching this problem's own Lean
# formalization already simplifying the generic to a plain "likely"
# universal (see Batch2.lean's comment on fracas_101).
#
# 104's hypothesis ("Jones has more than one company car") is skipped
# entirely: "more than one" has no established determiner in this
# grammar, this sentence is never fed to translate.py either way (104
# is a countermodel), and the closest paraphrase available
# (at_least_AdN wrapping "two", i.e. "at least two company cars")
# changes the surface wording enough not to be worth it for a sentence
# this low-value.
BASE_CHECKS += [
    (
        "fracas_098_premise2",
        "linearize PredVP (UsePN bug32985_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) "
        "(AdjCN (PositA known_A) (CompoundCN (UseN software_N) (UseN fault_N))))))",
        "Bug # 32-985 is a known software fault",
    ),
    (
        "fracas_101_premise1",
        "linearize PredVP (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN university_N) (UseN graduate_N))) "
        "(ComplSlash (SlashV2a make_V2) (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA poor_A) "
        "(CompoundCN (CompoundCN (UseN stock_N) (UseN market_N)) (UseN trader_N)))))",
        "university graduates make poor stock market traders",
    ),
    (
        "fracas_101_premise2",
        "linearize PredVP (UsePN smith_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) "
        "(CompoundCN (UseN university_N) (UseN graduate_N)))))",
        "Smith is a university graduate",
    ),
    (
        "fracas_101_hypothesis",
        "linearize PredVP (UsePN smith_PN) (AdVVP likely_AdV (ComplSlash (SlashV2a make_V2) "
        "(DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA poor_A) "
        "(CompoundCN (CompoundCN (UseN stock_N) (UseN market_N)) (UseN trader_N))))))",
        "Smith likely makes a poor stock market trader",
    ),
    (
        "fracas_103_premise1",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (UseN apcomManager_N))) "
        "(ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN company_N) (UseN car_N))))",
        "all APCOM managers have company cars",
    ),
    (
        "fracas_103_premise2",
        "linearize PredVP (UsePN jones_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN apcomManager_N))))",
        "Jones is an APCOM manager",
    ),
    (
        "fracas_103_hypothesis",
        "linearize PredVP (UsePN jones_PN) (ComplSlash (SlashV2a have_V2) "
        "(DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN company_N) (UseN car_N))))",
        "Jones has a company car",
    ),
]

# The rest of Batch2's sentences are themselves past (or future, for
# 102) tense, so their own trees are ALREADY `UttS (UseCl (TTAnt
# TPast/TFut ASimul) PPos (...))`-wrapped rather than a bare Cl -
# feeding one of these into `_tense_reconfirm` (which assumes every
# BASE_CHECKS entry is a bare Cl it can wrap in its own UseCl) would
# produce the same genuine "Couldn't match expected type Cl" build
# error _FRACAS_084_HYPOTHESIS_CHECK below was first written to avoid.
# Kept as their own standalone list instead, same reasoning.
_SECTION2_BATCH2_TENSED_CHECKS = [
    (
        "fracas_098_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant IndefArt NumPl) "
        "(CompoundCN (UseN software_N) (UseN fault_N))) (AdvVP (PassV2 blame_V2) (PrepNP for_Prep "
        "(DetCN (DetQuant DefArt NumSg) (CompoundCN (UseN system_N) (UseN failure_N)))))))",
        "software faults were blamed for the system failure",
    ),
    (
        "fracas_098_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bug32985_PN) (AdvVP (PassV2 blame_V2) "
        "(PrepNP for_Prep (DetCN (DetQuant DefArt NumSg) (CompoundCN (UseN system_N) (UseN failure_N)))))))",
        "Bug # 32-985 was blamed for the system failure",
    ),
    (
        "fracas_099_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (PredetNP all_Predet (AdvNP "
        "(DetCN (DetQuant IndefArt NumPl) (UseN client_N)) (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) "
        "(UseN demonstration_N))))) (AdvVP (PassV2 impress_V2) (PrepNP by8means_Prep (DetCN (DetQuant "
        "(GenNP (DetCN (DetQuant DefArt NumSg) (UseN system_N))) NumSg) (UseN performance_N))))))",
        "all clients at the demonstration were impressed by the system's performance",
    ),
    (
        "fracas_099_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseComp (CompNP "
        "(DetCN (DetQuant IndefArt NumSg) (AdvCN (UseN client_N) (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) "
        "(UseN demonstration_N)))))))))",
        "Smith was a client at the demonstration",
    ),
    (
        "fracas_099_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (PassV2 impress_V2) "
        "(PrepNP by8means_Prep (DetCN (DetQuant (GenNP (DetCN (DetQuant DefArt NumSg) (UseN system_N))) NumSg) "
        "(UseN performance_N))))))",
        "Smith was impressed by the system's performance",
    ),
    (
        "fracas_100_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (AdvNP (DetCN (DetQuant IndefArt NumPl) "
        "(UseN client_N)) (PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN demonstration_N)))) "
        "(AdvVP (PassV2 impress_V2) (PrepNP by8means_Prep (DetCN (DetQuant (GenNP (DetCN (DetQuant DefArt NumSg) "
        "(UseN system_N))) NumSg) (UseN performance_N))))))",
        "clients at the demonstration were impressed by the system's performance",
    ),
    (
        "fracas_100_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN most_Det (AdvCN (UseN client_N) "
        "(PrepNP at_Prep (DetCN (DetQuant DefArt NumSg) (UseN demonstration_N))))) (AdvVP (PassV2 impress_V2) "
        "(PrepNP by8means_Prep (DetCN (DetQuant (GenNP (DetCN (DetQuant DefArt NumSg) (UseN system_N))) NumSg) "
        "(UseN performance_N))))))",
        "most clients at the demonstration were impressed by the system's performance",
    ),
    (
        "fracas_102_hypothesis",
        "linearize UttS (UseCl (TTAnt TFut ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a make_V2) "
        "(DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA poor_A) "
        "(CompoundCN (CompoundCN (UseN stock_N) (UseN market_N)) (UseN trader_N)))))))",
        "Smith will make a poor stock market trader",
    ),
    (
        "fracas_105_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (PredetNP only_Predet "
        "(DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) "
        "(UseN accountant_N))) (ComplSlash (SlashV2a attend_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "only one accountant attended the meeting",
    ),
    (
        "fracas_105_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant no_Quant NumPl) (UseN accountant_N)) "
        "(ComplSlash (SlashV2a attend_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "no accountants attended the meeting",
    ),
    (
        "fracas_106_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant no_Quant NumSg) (UseN accountant_N)) "
        "(ComplSlash (SlashV2a attend_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "no accountant attended the meeting",
    ),
    (
        "fracas_107_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN somePl_Det (UseN accountant_N)) "
        "(ComplSlash (SlashV2a attend_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "some accountants attended the meeting",
    ),
    (
        "fracas_108_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN someSg_Det (UseN accountant_N)) "
        "(ComplSlash (SlashV2a attend_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "some accountant attended the meeting",
    ),
    (
        "fracas_111_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a sign_V2) "
        "(DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) (UseN contract_N)))))",
        "Smith signed one contract",
    ),
    (
        "fracas_111_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a sign_V2) "
        "(DetCN (DetQuant another_Quant NumSg) (UseN contract_N)))))",
        "Jones signed another contract",
    ),
    (
        "fracas_111_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (ConjNP and_Conj (BaseNP (UsePN smith_PN) (UsePN jones_PN))) "
        "(ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 "
        "(pot0as1 (pot0 n2)))))))) (UseN contract_N)))))",
        "Smith and Jones signed two contracts",
    ),
    (
        "fracas_112_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a sign_V2) "
        "(DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2)))))))) (UseN contract_N)))))",
        "Smith signed two contracts",
    ),
    (
        "fracas_112_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a sign_V2) "
        "(DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2)))))))) (UseN contract_N)))))",
        "Jones signed two contracts",
    ),
    (
        "fracas_113_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (AdVVP also_AdV "
        "(ComplSlash (SlashV2a sign_V2) (UsePron they_Pron)))))",
        "Jones also signed them",
    ),
]

TENSE_RECONFIRMATIONS = [_tense_reconfirm(*check) for check in BASE_CHECKS]

# Pilot past/future tense checks: NOTES.md's tense fix was only ever
# confirmed for TPres before now. "wins"/"won"/"will win" (fracas_033's
# tree - a plain transitive main verb, no auxiliary/control verb
# involved) is a clean, simple test of whether TPast/TFut's own verb
# conjugation actually differs correctly, not just TPres's already-
# confirmed path. Picked as pilots (rather than converting every
# sentence's tense outright) precisely because this is genuinely new
# ground - past/future have never been checked via CI before.
#
# This pilot is what caught win_V2's own latent bug: `mkV2 "win"`
# derives a fully regular verb, so TPast originally gave "winned". A
# temporary bare-V diagnostic (since removed) proved the fault was in
# `mkV` itself, not V2-wrapping or VP-building - see FraCaSLogicEng.gf's
# own comment on win_V2 for the full elimination story. Fixed via
# `mkV "win" "won" "won"` (the 3-argument form, all principal parts
# explicit).
_FRACAS_033_TREE = (
    "PredVP (DetCN (DetQuant IndefArt NumSg) (UseN irishman_N)) "
    "(ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))"
)

PILOT_TENSE_CHECKS = [
    (
        "fracas_033_past_pilot",
        f"linearize UttS (UseCl (TTAnt TPast ASimul) PPos ({_FRACAS_033_TREE}))",
        "an Irishman won a Nobel prize",
    ),
    (
        "fracas_033_future_pilot",
        f"linearize UttS (UseCl (TTAnt TFut ASimul) PPos ({_FRACAS_033_TREE}))",
        "an Irishman will win a Nobel prize",
    ),
]

# fracas_084's own hypothesis ("If Smith and Anderson did not sign the
# contract, Jones signed the contract.") is a full conditional S built
# from AdvS/SubjS/UseCl directly - already S-typed, not a bare Cl - so
# it can't go through _tense_reconfirm (which assumes every BASE_CHECKS
# entry is a bare Cl it can wrap in its own UseCl; feeding an
# already-S-typed tree into that produces a genuine "Couldn't match
# expected type Cl" build error, caught locally before ever reaching
# CI). Kept as its own standalone check instead, same reasoning as
# PILOT_TENSE_CHECKS above. Two real surprises from the actual
# toolchain, not just this file's own guesses: negative polarity
# contracts to "don't" (not "do not"), and AdvS's own "if..., ..."
# placement doesn't insert a comma before the main clause.
_FRACAS_084_HYPOTHESIS_CHECK = [
    (
        "fracas_084_hypothesis",
        "linearize UttS (AdvS (SubjS if_Subj (UseCl (TTAnt TPres ASimul) PNeg "
        "(PredVP (ConjNP and_Conj (BaseNP (UsePN smith_PN) (UsePN anderson_PN))) "
        "(ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))) "
        "(UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN jones_PN) "
        "(ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))))))",
        "if Smith and Anderson don't sign the contract Jones signs the contract",
    ),
]

CHECKS = (
    BASE_CHECKS
    + TENSE_RECONFIRMATIONS
    + PILOT_TENSE_CHECKS
    + _FRACAS_084_HYPOTHESIS_CHECK
    + _SECTION2_BATCH2_TENSED_CHECKS
)


def main() -> int:
    gf_dir = os.path.dirname(os.path.abspath(__file__))
    pgf = os.path.join(gf_dir, "FraCaSLogic.pgf")
    if not os.path.exists(pgf):
        print(f"error: {pgf} not found - did the gf -make step run first?", file=sys.stderr)
        return 1

    script = "\n".join(cmd for _, cmd, _ in CHECKS) + "\nquit\n"
    result = subprocess.run(
        ["gf", PATH_ARG, pgf],
        input=script,
        capture_output=True,
        text=True,
        cwd=gf_dir,
        timeout=60,
    )
    print(result.stdout)
    if result.stderr:
        print(result.stderr, file=sys.stderr)

    segments = result.stdout.split(PROMPT)
    # segments[0]: startup banner, before any command's result.
    # segments[1 .. len(CHECKS)]: each command's own result, in order.
    if len(segments) < len(CHECKS) + 1:
        print(
            f"error: expected at least {len(CHECKS) + 1} '{PROMPT}'-delimited "
            f"segments, got {len(segments)} - gf output shape changed unexpectedly",
            file=sys.stderr,
        )
        return 1

    failures = []
    for idx, (label, _cmd, expected) in enumerate(CHECKS):
        segment = segments[idx + 1]
        # Exact match on the linearized output's own first line - NOT a
        # substring check (`expected in segment`, this file's original
        # approach) - a real bug slipped through that way: "neither
        # leading tenor comes cheap" is a *prefix* of the wrong output
        # "neither leading tenor comes cheaply", so the substring check
        # kept "passing" against the wrong string for as long as that
        # bug existed (see FraCaSLogicEng.gf's own comment on it).
        stripped = segment.strip()
        actual = stripped.splitlines()[0].strip() if stripped else ""
        if actual != expected:
            failures.append((label, expected, actual))

    if failures:
        print("FAILED checks:", file=sys.stderr)
        for label, expected, actual in failures:
            print(f"  {label}: expected {expected!r}, got {actual!r}", file=sys.stderr)
        return 1

    print(f"All {len(CHECKS)} linearize checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
