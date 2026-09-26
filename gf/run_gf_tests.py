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

CHECKS = BASE_CHECKS + TENSE_RECONFIRMATIONS + PILOT_TENSE_CHECKS


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
