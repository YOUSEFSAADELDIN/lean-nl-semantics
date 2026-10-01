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
        # fracas_086's own gold premise text is identical to fracas_085's
        # ("Exactly two lawyers and three accountants signed the
        # contract.") - reusing 085's own already-confirmed tree rather
        # than re-linearizing the same sentence under a new label.
        "fracas_086_premise",
        "linearize PredVP (ConjNP and_Conj (BaseNP "
        "(DetCN (DetQuant IndefArt (NumCard (AdNum exactly_AdN (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2))))))))) (UseN lawyer_N)) "
        "(DetCN (DetQuant IndefArt (NumCard (AdNum exactly_AdN (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (UseN accountant_N)))) "
        "(ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))",
        "exactly two lawyers and exactly three accountants sign the contract",
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

# FraCaS Section 3 (Anaphora), problems 114-141 (Section3/Batch1.lean,
# Section3/Batch2.lean). Anaphora.lean's own header explains why this
# section doesn't need (and doesn't build) general anaphora-resolution
# machinery in Lean - each pronoun is resolved by hand, per problem,
# directly into the formalization. The same principle carries over to
# translate.py: none of this section's sentences are added there (see
# translate.py's own comment on why), even though every sentence still
# gets a real, independently-confirmed GF tree here, same rigor as
# every earlier section.
#
# New words this section needed (all checked directly against
# DictEngAbs/DictEng first): itel_PN, gfi_PN, mfi_PN, icm_PN,
# r95103_PN, customer_N, student_N, salesDepartment_N, payrise_N,
# dedicated_A, onTuesday_Adv, onWednesday_Adv, missing_A (all
# self-declared - see FraCaSLogic.gf's own comments for why). mary_PN/
# john_PN/bill_PN/bt_PN are NOT self-declared - all four already exist
# in DictEngAbs and are left free via the extends line. Every other
# word (workstation_N, desk_N, meeting_N, report_N, invoice_N,
# project_N, proposal_N, committee_N, chairman_N, member_N, machine_N,
# lobby_N, colleague_N, department_N, line_N, computer_N, executive_N,
# laptop_N, cover_N, page_N, director_N, company_N, use_V2, chair_V2,
# deliver_V2, appoint_V2, rent_V2, own_V2, maintain_V2, go_V, put_V2,
# take_V2, bring_V2, sign_V2, hurt_V2, hate_V2, attend_V2, remove_V2,
# award_V3, say_VS, female_A, large_A, different_A, here_Adv,
# yesterday_Adv, also_AdV) already exists in DictEngAbs.
#
# No new module this time - PossPron and GenNP (both already free from
# Section 2 Batch2's own Extend/Noun extension) turned out to cover
# every possessive this section needs ("her workstation", "John's
# colleagues", "its members", "Smith's desk", "its computers") without
# any further self-declaration, and Extend's own StrandRelSlash covers
# the one object-gap relative clause this section needs ("computers
# that GFI owns", problem 133) the same way IdRP already covered every
# subject-gap relative clause since Section 1. ReflVP (Verb, already
# extended) covers reflexives ("hurt himself") directly; Slash2V3
# (Verb, already extended) covers 139's ditransitive "awarded ... a
# large payrise" by leaving the recipient slot open for ReflVP to fill
# reflexively, at the cost of a dative-shifted surface form (see
# below). Idiom was tried for ProgrVP ("are missing") and abandoned -
# a genuine "unknown identifier CleftAdv" internal error at
# PMCFG-generation time at the current pinned gf-rgl tag, caught
# locally, not worth debugging for the one construction that needed
# it; missing_A self-declared instead.
#
# IdRP's own fixed lin is "that", not "who", confirmed directly - every
# relative clause below reads "customer that owns..."/"executive that
# had...", not "who".
#
# Five more documented near-misses/simplifications, all accepted as
# the closest buildable rendering or a deliberate paraphrase (same
# spirit as every earlier section's own near-misses):
#   - 121's "delivered them an invoice"/"delivered them a project
#     proposal" (double-object dative) are paraphrased to the
#     PP-dative "delivered an invoice/a project proposal to them" -
#     this grammar has no double-object V2 combinator, and the
#     PP-dative is truth-conditionally identical; "And she delivered
#     ..." also drops the leading "And" (a discourse connective with no
#     truth-conditional content of its own).
#   - 122's premise ("He is appointed its members", copied verbatim
#     from Problems.lean) is missing its own "by" - not reproduced
#     literally (ungrammatical as written); built instead as the
#     grammatical "He is appointed by its members".
#   - 126's premise ("They were all here yesterday") drops "all": a
#     floating quantifier on a bare pronoun subject ("all they") isn't
#     grammatical via PredetNP's own prenominal-only placement, and
#     this sentence is a GF-only check (never fed to translate.py), so
#     "They were here yesterday" is accepted instead.
#   - 136's premise drops "to take notes" (an infinitival purpose
#     clause this grammar has no combinator for): "brought it to the
#     meeting" instead of "brought it to take notes at the meeting".
#   - 139's "awarded himself a large payrise" comes out "awarded itself
#     a large payrise": CompoundCN's own gender-inheritance recipe
#     (`g = b.g`, see this file's comment on CompoundCN) takes
#     "company director"'s gender from director_N's own dictionary
#     gender, which isn't masculine, so ReflVP's own reflexive-pronoun
#     agreement doesn't produce "himself" here. Accepted as the
#     achievable rendering rather than chasing a gendered variant for
#     one sentence. Separately, ComplVS's own fixed recipe always
#     inserts "that" ("said that Bill...", not "said Bill..." exactly
#     as Problems.lean has it) - the standard, more explicit form,
#     accepted the same way.
BASE_CHECKS += [
    (
        "fracas_115_hypothesis",
        "linearize PredVP (UsePN mary_PN) (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (UseN workstation_N)))",
        "Mary has a workstation",
    ),
    (
        "fracas_116_hypothesis",
        "linearize PredVP (UsePN mary_PN) (UseComp (CompAP (PositA female_A)))",
        "Mary is female",
    ),
    (
        "fracas_117_premise2",
        "linearize PredVP (UsePN mary_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN student_N))))",
        "Mary is a student",
    ),
    (
        # fracas_118/119's own gold premise text (second premise, "Mary
        # is a student") is identical to fracas_117's own - reusing its
        # already-confirmed tree rather than re-linearizing it twice
        # more under new labels.
        "fracas_118_premise2",
        "linearize PredVP (UsePN mary_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN student_N))))",
        "Mary is a student",
    ),
    (
        "fracas_119_premise2",
        "linearize PredVP (UsePN mary_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN student_N))))",
        "Mary is a student",
    ),
    (
        "fracas_122_premise1",
        "linearize PredVP (DetCN every_Det (UseN committee_N)) (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (UseN chairman_N)))",
        "every committee has a chairman",
    ),
    (
        "fracas_122_premise2",
        "linearize PredVP (UsePron he_Pron) (AdvVP (PassV2 appoint_V2) (PrepNP by8agent_Prep (DetCN (DetQuant (PossPron it_Pron) NumPl) (UseN member_N))))",
        "he is appointed by its members",
    ),
    (
        "fracas_122_hypothesis",
        "linearize PredVP (DetCN every_Det (UseN committee_N)) (ComplSlash (SlashV2a have_V2) (AdvNP (PPartNP (DetCN (DetQuant IndefArt NumSg) (UseN chairman_N)) appoint_V2) (PrepNP by8agent_Prep (DetCN (DetQuant IndefArt NumPl) (AdvCN (UseN member_N) (PrepNP of_Prep (DetCN (DetQuant DefArt NumSg) (UseN committee_N))))))))",
        "every committee has a chairman appointed by members of the committee",
    ),
    (
        "fracas_123_premise2",
        "linearize PredVP (UsePron they_Pron) (UseComp (CompAdv (PrepNP on_Prep (DetCN (DetQuant (PossPron she_Pron) NumSg) (UseN desk_N)))))",
        "they are on her desk",
    ),
    (
        "fracas_123_hypothesis",
        "linearize PredVP (DetCN somePl_Det (AdvCN (UseN report_N) (PrepNP from_Prep (UsePN itel_PN)))) (UseComp (CompAdv (PrepNP on_Prep (DetCN (DetQuant (GenNP (UsePN smith_PN)) NumSg) (UseN desk_N)))))",
        "some reports from ITEL are on Smith's desk",
    ),
    (
        "fracas_124_premise1",
        "linearize PredVP (AdvNP (DetNP (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2))))))))) (PrepNP out_of_Prep (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 pot110)))))) (UseN machine_N)))) (UseComp (CompAP (PositA missing_A)))",
        "two out of ten machines are missing",
    ),
    (
        "fracas_131_premise1",
        "linearize PredVP (DetCN each_Det (UseN department_N)) (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA dedicated_A) (UseN line_N))))",
        "each department has a dedicated line",
    ),
    (
        # fracas_132's own gold premise 1 is identical to fracas_131's
        # ("Each department has a dedicated line.") - reusing 131's own
        # already-confirmed tree rather than re-linearizing it.
        "fracas_132_premise1",
        "linearize PredVP (DetCN each_Det (UseN department_N)) (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA dedicated_A) (UseN line_N))))",
        "each department has a dedicated line",
    ),
    (
        "fracas_131_premise2",
        "linearize PredVP (UsePron they_Pron) (AdvVP (ComplSlash (SlashV2a rent_V2) (UsePron they_Pron)) (PrepNP from_Prep (UsePN bt_PN)))",
        "they rent them from BT",
    ),
    (
        "fracas_131_hypothesis",
        "linearize PredVP (DetCN every_Det (UseN department_N)) (AdvVP (ComplSlash (SlashV2a rent_V2) (DetCN (DetQuant IndefArt NumSg) (UseN line_N))) (PrepNP from_Prep (UsePN bt_PN)))",
        "every department rents a line from BT",
    ),
    (
        "fracas_132_premise2",
        "linearize PredVP (DetCN (DetQuant DefArt NumSg) (UseN salesDepartment_N)) (AdvVP (ComplSlash (SlashV2a rent_V2) (UsePron it_Pron)) (PrepNP from_Prep (UsePN bt_PN)))",
        "the sales department rents it from BT",
    ),
    (
        "fracas_132_hypothesis",
        "linearize PredVP (DetCN (DetQuant DefArt NumSg) (UseN salesDepartment_N)) (AdvVP (ComplSlash (SlashV2a rent_V2) (DetCN (DetQuant IndefArt NumSg) (UseN line_N))) (PrepNP from_Prep (UsePN bt_PN)))",
        "the sales department rents a line from BT",
    ),
    (
        "fracas_133_premise1",
        "linearize PredVP (UsePN gfi_PN) (ComplSlash (SlashV2a own_V2) (DetCN several_Det (UseN computer_N)))",
        "GFI owns several computers",
    ),
    (
        "fracas_133_premise2",
        "linearize PredVP (UsePN itel_PN) (ComplSlash (SlashV2a maintain_V2) (UsePron they_Pron))",
        "ITEL maintains them",
    ),
    (
        "fracas_133_hypothesis",
        "linearize PredVP (UsePN itel_PN) (ComplSlash (SlashV2a maintain_V2) (PredetNP all_Predet (DetCN (DetQuant DefArt NumPl) (RelCN (UseN computer_N) (UseRCl (TTAnt TPres ASimul) PPos (StrandRelSlash IdRP (SlashVP (UsePN gfi_PN) (SlashV2a own_V2))))))))",
        "ITEL maintains all the computers that GFI owns",
    ),
    (
        "fracas_134_premise1",
        "linearize PredVP (DetCN every_Det (RelCN (UseN customer_N) (UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (UseN computer_N))))))) (ComplSlash (SlashV2a have_V2) (AdvNP (DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN service_N) (UseN contract_N))) (PrepNP for_Prep (UsePron it_Pron))))",
        "every customer that owns a computer has a service contract for it",
    ),
    (
        "fracas_134_premise2",
        "linearize PredVP (UsePN mfi_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (RelCN (UseN customer_N) (UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt (NumCard (AdNum exactly_AdN (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01)))))))) (UseN computer_N)))))))))",
        "MFI is a customer that owns exactly one computer",
    ),
    (
        "fracas_135_premise2",
        "linearize PredVP (UsePN mfi_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (RelCN (UseN customer_N) (UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (ComplSlash (SlashV2a own_V2) (DetCN several_Det (UseN computer_N)))))))))",
        "MFI is a customer that owns several computers",
    ),
    (
        "fracas_134_hypothesis",
        "linearize PredVP (UsePN mfi_PN) (AdvVP (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN service_N) (UseN contract_N)))) (PrepNP for_Prep (PredetNP all_Predet (DetCN (DetQuant (PossPron it_Pron) NumPl) (UseN computer_N)))))",
        "MFI has a service contract for all its computers",
    ),
    (
        "fracas_136_premise2",
        "linearize PredVP (UsePN smith_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (RelCN (UseN executive_N) (UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n5)))))))) (AdjCN (PositA different_A) (CompoundCN (UseN laptop_N) (UseN computer_N)))))))))))",
        "Smith is an executive that owns five different laptop computers",
    ),
    (
        "fracas_138_premise1",
        "linearize PredVP (DetCN every_Det (UseN report_N)) (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN cover_N) (UseN page_N))))",
        "every report has a cover page",
    ),
    (
        "fracas_138_premise2",
        "linearize PredVP (UsePN r95103_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN report_N))))",
        "R-95-103 is a report",
    ),
]

# The rest of Section 3's sentences are themselves past tense (or, for
# 124/125's hypotheses, present-perfect - `TTAnt TPres AAnter`, a
# tense/anteriority combination not used anywhere before this section),
# or already S-typed (127's ConjS premise) - so, same reasoning as
# _SECTION2_BATCH2_TENSED_CHECKS above, they're written pre-wrapped and
# kept out of BASE_CHECKS/_tense_reconfirm entirely.
_SECTION3_TENSED_CHECKS = [
    (
        "fracas_114_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN mary_PN) (ComplSlash (SlashV2a use_V2) (DetCN (DetQuant (PossPron she_Pron) NumSg) (UseN workstation_N)))))",
        "Mary used her workstation",
    ),
    (
        "fracas_114_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant (GenNP (UsePN mary_PN)) NumSg) (UseN workstation_N)) (PassV2 use_V2)))",
        "Mary's workstation was used",
    ),
    (
        # fracas_115/116's own gold premise text is identical to
        # fracas_114's ("Mary used her workstation.") - reusing 114's
        # own already-confirmed tree rather than re-linearizing the
        # same sentence under a new label.
        "fracas_115_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN mary_PN) (ComplSlash (SlashV2a use_V2) (DetCN (DetQuant (PossPron she_Pron) NumSg) (UseN workstation_N)))))",
        "Mary used her workstation",
    ),
    (
        "fracas_116_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN mary_PN) (ComplSlash (SlashV2a use_V2) (DetCN (DetQuant (PossPron she_Pron) NumSg) (UseN workstation_N)))))",
        "Mary used her workstation",
    ),
    (
        "fracas_117_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN every_Det (UseN student_N)) (ComplSlash (SlashV2a use_V2) (DetCN (DetQuant (PossPron she_Pron) NumSg) (UseN workstation_N)))))",
        "every student used her workstation",
    ),
    (
        # fracas_118's own gold premise text (first premise) is
        # identical to fracas_117's - reusing its already-confirmed tree.
        "fracas_118_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN every_Det (UseN student_N)) (ComplSlash (SlashV2a use_V2) (DetCN (DetQuant (PossPron she_Pron) NumSg) (UseN workstation_N)))))",
        "every student used her workstation",
    ),
    (
        "fracas_119_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant no_Quant NumSg) (UseN student_N)) (ComplSlash (SlashV2a use_V2) (DetCN (DetQuant (PossPron she_Pron) NumSg) (UseN workstation_N)))))",
        "no student used her workstation",
    ),
    (
        "fracas_119_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN mary_PN) (ComplSlash (SlashV2a use_V2) (DetCN (DetQuant IndefArt NumSg) (UseN workstation_N)))))",
        "Mary used a workstation",
    ),
    (
        "fracas_120_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a attend_V2) (DetCN (DetQuant IndefArt NumSg) (UseN meeting_N)))))",
        "Smith attended a meeting",
    ),
    (
        "fracas_120_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePron she_Pron) (ComplSlash (SlashV2a chair_V2) (UsePron it_Pron))))",
        "she chaired it",
    ),
    (
        "fracas_120_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a chair_V2) (DetCN (DetQuant IndefArt NumSg) (UseN meeting_N)))))",
        "Smith chaired a meeting",
    ),
    (
        "fracas_121_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a deliver_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N))) (PrepNP to_Prep (UsePN itel_PN)))))",
        "Smith delivered a report to ITEL",
    ),
    (
        "fracas_121_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePron she_Pron) (AdVVP also_AdV (AdvVP (ComplSlash (SlashV2a deliver_V2) (DetCN (DetQuant IndefArt NumSg) (UseN invoice_N))) (PrepNP to_Prep (UsePron they_Pron))))))",
        "she also delivered an invoice to them",
    ),
    (
        "fracas_121_premise3",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePron she_Pron) (AdvVP (ComplSlash (SlashV2a deliver_V2) (DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN project_N) (UseN proposal_N)))) (PrepNP to_Prep (UsePron they_Pron)))))",
        "she delivered a project proposal to them",
    ),
    (
        "fracas_121_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a deliver_V2) (ConjNP and_Conj (ConsNP (DetCN (DetQuant IndefArt NumSg) (UseN report_N)) (BaseNP (DetCN (DetQuant IndefArt NumSg) (UseN invoice_N)) (DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN project_N) (UseN proposal_N))))))) (PrepNP to_Prep (UsePN itel_PN)))))",
        "Smith delivered a report , an invoice and a project proposal to ITEL",
    ),
    (
        "fracas_124_hypothesis",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2)))))))) (UseN machine_N)) (PassV2 remove_V2)))",
        "two machines have been removed",
    ),
    (
        "fracas_125_hypothesis",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n8)))))))) (UseN machine_N)) (PassV2 remove_V2)))",
        "eight machines have been removed",
    ),
    (
        "fracas_126_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePron they_Pron) (AdvVP (UseComp (CompAdv here_Adv)) yesterday_Adv)))",
        "they were here yesterday",
    ),
    (
        "fracas_126_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 pot110)))))) (UseN machine_N)) (AdvVP (UseComp (CompAdv here_Adv)) yesterday_Adv)))",
        "ten machines were here yesterday",
    ),
    (
        "fracas_127_premise1",
        "linearize UttS (ConjS and_Conj (BaseS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a take_V2) (DetCN (DetQuant IndefArt NumSg) (UseN machine_N))) onTuesday_Adv))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (AdvVP (ComplSlash (SlashV2a take_V2) (DetCN (DetQuant IndefArt NumSg) (UseN machine_N))) onWednesday_Adv)))))",
        "Smith took a machine on Tuesday and Jones took a machine on Wednesday",
    ),
    (
        "fracas_127_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePron they_Pron) (AdvVP (ComplSlash (SlashV2a put_V2) (UsePron they_Pron)) (PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN lobby_N))))))",
        "they put them in the lobby",
    ),
    (
        "fracas_127_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (ConjNP and_Conj (BaseNP (UsePN smith_PN) (UsePN jones_PN))) (AdvVP (ComplSlash (SlashV2a put_V2) (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2)))))))) (UseN machine_N))) (PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN lobby_N))))))",
        "Smith and Jones put two machines in the lobby",
    ),
    (
        "fracas_128_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (ConjNP and_Conj (BaseNP (UsePN john_PN) (DetCN (DetQuant (PossPron he_Pron) NumPl) (UseN colleague_N)))) (AdvVP (UseV go_V) (PrepNP to_Prep (DetCN (DetQuant IndefArt NumSg) (UseN meeting_N))))))",
        "John and his colleagues went to a meeting",
    ),
    (
        "fracas_128_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePron they_Pron) (ComplSlash (SlashV2a hate_V2) (UsePron it_Pron))))",
        "they hated it",
    ),
    (
        # fracas_129's own gold premise 1 is identical to fracas_128's
        # ("John and his colleagues went to a meeting.") - reusing 128's
        # own already-confirmed tree rather than re-linearizing it.
        "fracas_129_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (ConjNP and_Conj (BaseNP (UsePN john_PN) (DetCN (DetQuant (PossPron he_Pron) NumPl) (UseN colleague_N)))) (AdvVP (UseV go_V) (PrepNP to_Prep (DetCN (DetQuant IndefArt NumSg) (UseN meeting_N))))))",
        "John and his colleagues went to a meeting",
    ),
    (
        "fracas_128_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant (GenNP (UsePN john_PN)) NumPl) (UseN colleague_N)) (ComplSlash (SlashV2a hate_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "John's colleagues hated the meeting",
    ),
    (
        "fracas_129_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplSlash (SlashV2a hate_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "John hated the meeting",
    ),
    (
        "fracas_136_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN every_Det (RelCN (UseN executive_N) (UseRCl (TTAnt TPast ASimul) PPos (RelVP IdRP (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN laptop_N) (UseN computer_N)))))))) (AdvVP (ComplSlash (SlashV2a bring_V2) (UsePron it_Pron)) (PrepNP to_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N))))))",
        "every executive that had a laptop computer brought it to the meeting",
    ),
    (
        "fracas_136_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a take_V2) (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n5)))))))) (CompoundCN (UseN laptop_N) (UseN computer_N)))) (PrepNP to_Prep (DetCN (DetQuant DefArt NumSg) (UseN meeting_N))))))",
        "Smith took five laptop computers to the meeting",
    ),
    (
        "fracas_138_premise3",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (CompoundCN (UseN cover_N) (UseN page_N))))))",
        "Smith signed the cover page",
    ),
    (
        "fracas_138_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (AdvCN (CompoundCN (UseN cover_N) (UseN page_N)) (PrepNP of_Prep (UsePN r95103_PN)))))))",
        "Smith signed the cover page of R-95-103",
    ),
    (
        "fracas_139_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN company_N) (UseN director_N))) (ReflVP (Slash2V3 award_V3 (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA large_A) (UseN payrise_N)))))))",
        "a company director awarded itself a large payrise",
    ),
    (
        "fracas_140_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplVS say_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePN bill_PN) (ReflVP (SlashV2a hurt_V2)))))))",
        "John said that Bill had hurt himself",
    ),
    (
        "fracas_140_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplVS say_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePN bill_PN) (PassV2 hurt_V2))))))",
        "John said that Bill had been hurt",
    ),
    (
        "fracas_141_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP somebody_NP (ComplVS say_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePN john_PN) (PassV2 hurt_V2))))))",
        "somebody said that John had been hurt",
    ),
    (
        # Paraphrased as the passive "most reports that Smith needs have
        # been sent by ITEL" (truth-conditionally identical to the gold
        # active-voice "ITEL has sent most of the reports Smith needs") -
        # same accepted-paraphrase convention as this section's other
        # five documented near-misses (see this file's own comment on
        # problems 121/122/126/136/139 above): this grammar's quantifier
        # convention always treats the quantified NP as subject, so the
        # object-position "most of the reports..." needs the passive
        # voice to become the grammatical subject.
        "fracas_123_premise1",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (DetCN most_Det (RelCN (UseN report_N) "
        "(UseRCl (TTAnt TPres ASimul) PPos (StrandRelSlash IdRP (SlashVP (UsePN smith_PN) (SlashV2a need_V2)))))) "
        "(AdvVP (PassV2 send_V2) (PrepNP by8agent_Prep (UsePN itel_PN)))))",
        "most reports that Smith needs have been sent by ITEL",
    ),
]

# FraCaS Section 4 (Ellipsis), problems 142-196 (Section4/Batch1-4.lean).
# Ellipsis.lean's own header states this section's approach directly:
# build the RESOLVED, non-elliptical reading of each sentence rather
# than modeling the ellipsis mechanism itself ("So did Bill" -> "Bill
# spoke to Mary", the same move Section 3 already made for pronouns).
# Every check below is therefore a plain resolved sentence, not a
# literal rendering of FraCaS's own elliptical surface form - and, same
# as Section 3, nothing is added to translate.py here (see translate.py's
# own comment): resolved-ellipsis facts are bundled/Skolemized/
# ambiguity-per-reading the same way Section 3's anaphora facts are,
# never "one quantified Cl".
#
# New words: atFourOClock_Adv/atFiveOClock_Adv/onMonday_Adv/
# onFriday_Adv/onThursday_Adv (fixed one-off time adverbials, same
# reasoning as Section 3's onTuesday_Adv/onWednesday_Adv) and
# partTime_Adv (genuine dictionary gap) - all self-declared, see
# FraCaSLogic.gf's own comment. Every other word (speak_V, find_V2,
# write_V2, buy_V2, represent_V2, cost_V2, claim_VS, say_VS, own_V2,
# work_V, sign_V2, man_N, woman_N, lawyer_N, auditor_N, report_N,
# company_N, proposal_N, sue_PN, peter_PN, before_Subj, if_Subj,
# red_A/blue_A/fast_A/slow_A) already exists in DictEngAbs.
#
# One genuine toolchain bug found and worked around: `pot1plus` (the
# tens-plus-ones numeral combinator, "forty-five") renders its own BIND
# tokens literally ("forty &+ - &+ five") rather than collapsing them,
# at the current pinned gf-rgl tag - confirmed directly, not assumed,
# and NumDigits hits the same bug on any multi-digit number. Round tens
# via bare `pot1` ("twenty") are unaffected - confirmed directly too.
# 168's own second sentence ("forty five women work part time") is
# skipped entirely rather than either fought further or faked with a
# wrong number; its first sentence ("five men work part time") already
# exercises the same construction cleanly.
#
# Other documented near-misses, same spirit as every earlier section:
# GenNP's own regular rule gives "Jones's"/"Smith's" (not FraCaS's own
# "Jones'" elided-apostrophe style for names ending in s); AdvS/SubjS
# always fronts the subordinate clause (same as Section 2's "if"
# pattern), so 169/170's "before"-sentences come out "before Bill found
# Mary, John found Mary" rather than FraCaS's own clause order.
#
# Several problems are skipped entirely, each for a genuine construction
# gap rather than fought as one-offs: 163 ("know why S", an embedded
# question under a V2Q-style verb), 171/172 ("want to know how
# many/which Xs...", embedded questions under want), 173/174
# ("everyone that John did" - relativizing a quantificational pronoun
# NP, which this grammar's RelCN-based relative clauses don't support;
# only CNs relativize), 177 (no new sentence needed - its own
# countermodel is pure True/False, and 175/176 already exercise the
# "said" construction this problem shares), 181 (same, no named
# predicate at all in its own countermodel), 188 (ditto), and 191-195
# (a passive impersonal "it was suggested that X and Y should go
# together", combining a raising passive, modal "should", and a
# reciprocal "together" this grammar has no combinator for - all five
# share one already-complex premise and are all either `id` or pure
# True/False countermodels in Lean, so nothing here would ever reach
# translate.py either way).
BASE_CHECKS += [
    (
        "fracas_153_premise1",
        "linearize PredVP (UsePN john_PN) (AdvVP (AdvVP (UseV go_V) (PrepNP to_Prep (UsePN paris_PN))) (PrepNP by8means_Prep (MassNP (UseN car_N))))",
        "John goes to Paris by car",
    ),
    (
        "fracas_153_premise2",
        "linearize PredVP (DetCN (DetQuant DefArt NumPl) (UseN student_N)) (AdvVP (AdvVP (UseV go_V) (PrepNP to_Prep (UsePN paris_PN))) (PrepNP by8means_Prep (MassNP (UseN train_N))))",
        "the students go to Paris by train",
    ),
    (
        "fracas_155_premise1",
        "linearize PredVP (UsePN john_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (UseN car_N)))",
        "John owns a car",
    ),
    (
        "fracas_155_premise2",
        "linearize PredVP (UsePN bill_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (UseN car_N)))",
        "Bill owns a car",
    ),
    (
        "fracas_156_premise",
        "linearize PredVP (ConjNP and_Conj (BaseNP (UsePN john_PN) (UsePN bill_PN))) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (UseN car_N)))",
        "John and Bill own a car",
    ),
    (
        "fracas_157_premise1",
        "linearize PredVP (UsePN john_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA red_A) (UseN car_N))))",
        "John owns a red car",
    ),
    (
        "fracas_157_premise2",
        "linearize PredVP (UsePN bill_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA blue_A) (UseN car_N))))",
        "Bill owns a blue car",
    ),
    (
        "fracas_159_hypothesis",
        "linearize PredVP (UsePN bill_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA fast_A) (UseN car_N))))",
        "Bill owns a fast car",
    ),
    (
        # fracas_159's/160's own gold premise 1 ("John owns a red car")
        # is identical to fracas_157's own premise 1 - reusing its
        # already-confirmed tree rather than re-linearizing it.
        "fracas_159_premise1",
        "linearize PredVP (UsePN john_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA red_A) (UseN car_N))))",
        "John owns a red car",
    ),
    (
        "fracas_160_hypothesis",
        "linearize PredVP (UsePN bill_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA fast_A) (AdjCN (PositA red_A) (UseN car_N)))))",
        "Bill owns a fast red car",
    ),
    (
        "fracas_160_premise1",
        "linearize PredVP (UsePN john_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA red_A) (UseN car_N))))",
        "John owns a red car",
    ),
    (
        "fracas_162_premise1",
        "linearize PredVP (UsePN john_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA fast_A) (AdjCN (PositA red_A) (UseN car_N)))))",
        "John owns a fast red car",
    ),
    (
        "fracas_162_hypothesis",
        "linearize PredVP (UsePN bill_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA slow_A) (AdjCN (PositA red_A) (UseN car_N)))))",
        "Bill owns a slow red car",
    ),
    (
        "fracas_167_premise1",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot1 n2))))))) (UseN man_N)) (AdvVP (UseV work_V) (PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN salesDepartment_N))))",
        "twenty men work in the sales department",
    ),
    (
        "fracas_167_premise2",
        "linearize PredVP (PredetNP only_Predet (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) (UseN woman_N))) (AdvVP (UseV work_V) (PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN salesDepartment_N))))",
        "only one woman works in the sales department",
    ),
    (
        "fracas_167_hypothesis",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2)))))))) (UseN woman_N)) (AdvVP (UseV work_V) (PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN salesDepartment_N))))",
        "two women work in the sales department",
    ),
    (
        "fracas_168_premise1",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n5)))))))) (UseN man_N)) (AdvVP (UseV work_V) partTime_Adv)",
        "five men work part time",
    ),
    (
        "fracas_182_premise",
        "linearize PredVP (UsePN smith_PN) (ComplSlash (SlashV2a represent_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN company_N)))",
        "Smith represents his company",
    ),
    (
        "fracas_182_hypothesis",
        "linearize PredVP (UsePN jones_PN) (ComplSlash (SlashV2a represent_V2) (DetCN (DetQuant (GenNP (UsePN jones_PN)) NumSg) (UseN company_N)))",
        "Jones represents Jones's company",
    ),
    (
        "fracas_183_hypothesis",
        "linearize PredVP (UsePN jones_PN) (ComplSlash (SlashV2a represent_V2) (DetCN (DetQuant (GenNP (UsePN smith_PN)) NumSg) (UseN company_N)))",
        "Jones represents Smith's company",
    ),
    (
        # fracas_183's own gold premise ("Smith represents his company")
        # is identical to fracas_182's own premise - reusing its
        # already-confirmed tree rather than re-linearizing it.
        "fracas_183_premise",
        "linearize PredVP (UsePN smith_PN) (ComplSlash (SlashV2a represent_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN company_N)))",
        "Smith represents his company",
    ),
    (
        "fracas_184_hypothesis",
        "linearize PredVP (UsePN smith_PN) (ComplSlash (SlashV2a represent_V2) (DetCN (DetQuant (GenNP (UsePN jones_PN)) NumSg) (UseN company_N)))",
        "Smith represents Jones's company",
    ),
    (
        "fracas_189_premise1a",
        "linearize PredVP (UsePN john_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN man_N))))",
        "John is a man",
    ),
    (
        "fracas_189_premise1b",
        "linearize PredVP (UsePN mary_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN woman_N))))",
        "Mary is a woman",
    ),
    (
        "fracas_189_hypothesis",
        "linearize PredVP (UsePN mary_PN) (ComplSlash (SlashV2a represent_V2) (DetCN (DetQuant (PossPron she_Pron) NumSg) (UseN company_N)))",
        "Mary represents her company",
    ),
    (
        "fracas_190_hypothesis",
        "linearize PredVP (UsePN mary_PN) (ComplSlash (SlashV2a represent_V2) (DetCN (DetQuant (GenNP (UsePN john_PN)) NumSg) (UseN company_N)))",
        "Mary represents John's company",
    ),
    (
        # fracas_190's own gold premise 1a/1b ("John is a man"/"Mary is
        # a woman", the gender-agreement distractor) is identical to
        # fracas_189's own - reusing its already-confirmed trees rather
        # than re-linearizing them.
        "fracas_190_premise1a",
        "linearize PredVP (UsePN john_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN man_N))))",
        "John is a man",
    ),
    (
        "fracas_190_premise1b",
        "linearize PredVP (UsePN mary_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN woman_N))))",
        "Mary is a woman",
    ),
]

# The rest of Section 4's sentences are past/future/perfect tense, or
# already S-typed (169/170/179's AdvS conditionals) - same reasoning as
# every earlier section's own tensed-exempt list.
_SECTION4_TENSED_CHECKS = [
    (
        "fracas_142_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN)))))",
        "John spoke to Mary",
    ),
    (
        "fracas_142_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN)))))",
        "Bill spoke to Mary",
    ),
    (
        "fracas_143_premise3",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN))) atFourOClock_Adv)))",
        "John spoke to Mary at four o'clock",
    ),
    (
        "fracas_143_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (AdvVP (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN))) atFourOClock_Adv)))",
        "Bill spoke to Mary at four o'clock",
    ),
    (
        "fracas_145_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (AdvVP (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN))) atFiveOClock_Adv)))",
        "Bill spoke to Mary at five o'clock",
    ),
    (
        "fracas_146_premise1",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (UsePN john_PN) (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN)))))",
        "John has spoken to Mary",
    ),
    (
        "fracas_146_hypothesis",
        "linearize UttS (UseCl (TTAnt TFut ASimul) PPos (PredVP (UsePN bill_PN) (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN)))))",
        "Bill will speak to Mary",
    ),
    (
        "fracas_147_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN))) onMonday_Adv)))",
        "John spoke to Mary on Monday",
    ),
    (
        "fracas_147_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PNeg (PredVP (UsePN bill_PN) (AdvVP (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN))) onMonday_Adv)))",
        "Bill didn't speak to Mary on Monday",
    ),
    (
        "fracas_147_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (AdvVP (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN))) onMonday_Adv)))",
        "Bill spoke to Mary on Monday",
    ),
    (
        "fracas_148_hypothesis",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (UsePN bill_PN) (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN)))))",
        "Bill has spoken to Mary",
    ),
    (
        "fracas_149_premise2",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (DetCN (DetQuant DefArt NumPl) (UseN student_N)) (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN)))))",
        "the students have spoken to Mary",
    ),
    (
        "fracas_150_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (AdvVP (UseV go_V) (PrepNP to_Prep (UsePN paris_PN))) (PrepNP by8means_Prep (MassNP (UseN car_N))))))",
        "John went to Paris by car",
    ),
    (
        "fracas_150_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (AdvVP (AdvVP (UseV go_V) (PrepNP to_Prep (UsePN paris_PN))) (PrepNP by8means_Prep (MassNP (UseN train_N))))))",
        "Bill went to Paris by train",
    ),
    (
        "fracas_151_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (AdvVP (AdvVP (UseV go_V) (PrepNP to_Prep (UsePN berlin_PN))) (PrepNP by8means_Prep (MassNP (UseN train_N))))))",
        "Bill went to Berlin by train",
    ),
    (
        "fracas_152_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (AdvVP (AdvVP (UseV go_V) (PrepNP to_Prep (UsePN berlin_PN))) (PrepNP by8means_Prep (MassNP (UseN car_N))))))",
        "Bill went to Berlin by car",
    ),
    (
        "fracas_164_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN sue_PN)))))",
        "John spoke to Sue",
    ),
    (
        "fracas_165_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN))) onFriday_Adv)))",
        "John spoke to Mary on Friday",
    ),
    (
        "fracas_166_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN))) onThursday_Adv)))",
        "John spoke to Mary on Thursday",
    ),
    (
        # fracas_164's/165's own gold premise 1 ("John spoke to Mary", the
        # unelided antecedent both ellipses resolve against) is identical
        # to fracas_142's own premise 1 - reusing its already-confirmed
        # tree rather than re-linearizing it.
        "fracas_164_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN)))))",
        "John spoke to Mary",
    ),
    (
        "fracas_165_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN)))))",
        "John spoke to Mary",
    ),
    (
        # fracas_166's own gold hypothesis ("John spoke to Mary on
        # Friday") is identical to fracas_165's own hypothesis - reusing
        # its already-confirmed tree rather than re-linearizing it.
        "fracas_166_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (AdvVP (UseV speak_V) (PrepNP to_Prep (UsePN mary_PN))) onFriday_Adv)))",
        "John spoke to Mary on Friday",
    ),
    (
        "fracas_169",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (ComplSlash (SlashV2a find_V2) (UsePN mary_PN))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplSlash (SlashV2a find_V2) (UsePN mary_PN)))))",
        "before Bill found Mary John found Mary",
    ),
    (
        "fracas_170",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplSlash (SlashV2a find_V2) (UsePN bill_PN))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplSlash (SlashV2a find_V2) (UsePN mary_PN)))))",
        "before John found Bill John found Mary",
    ),
    (
        "fracas_178_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N)))))",
        "John wrote a report",
    ),
    (
        "fracas_178_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (ComplVS say_VS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN peter_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N))))))))",
        "Bill said that Peter wrote a report",
    ),
    (
        "fracas_179",
        "linearize UttS (AdvS (SubjS if_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN bill_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N))))))",
        "if John wrote a report Bill wrote a report",
    ),
    (
        "fracas_180_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN john_PN) (ComplSlash (SlashV2a buy_V2) (DetCN (DetQuant IndefArt NumSg) (UseN car_N)))))",
        "John bought a car",
    ),
    (
        "fracas_185_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplVS claim_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePron he_Pron) (ComplSlash (SlashV2a cost_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN proposal_N))))))))",
        "Smith claimed that he had costed his proposal",
    ),
    (
        "fracas_185_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplVS claim_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePron he_Pron) (ComplSlash (SlashV2a cost_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN proposal_N))))))))",
        "Jones claimed that he had costed his proposal",
    ),
    (
        "fracas_186_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplVS claim_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePron he_Pron) (ComplSlash (SlashV2a cost_V2) (DetCN (DetQuant (GenNP (UsePN smith_PN)) NumSg) (UseN proposal_N))))))))",
        "Jones claimed that he had costed Smith's proposal",
    ),
    (
        # fracas_186's/187's own gold premise ("Smith claimed that he
        # had costed his proposal") is identical to fracas_185's own
        # premise - reusing its already-confirmed tree rather than
        # re-linearizing it.
        "fracas_186_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplVS claim_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePron he_Pron) (ComplSlash (SlashV2a cost_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN proposal_N))))))))",
        "Smith claimed that he had costed his proposal",
    ),
    (
        "fracas_187_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplVS claim_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a cost_V2) (DetCN (DetQuant (GenNP (UsePN smith_PN)) NumSg) (UseN proposal_N))))))))",
        "Jones claimed that Smith had costed Smith's proposal",
    ),
    (
        "fracas_187_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplVS claim_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePron he_Pron) (ComplSlash (SlashV2a cost_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN proposal_N))))))))",
        "Smith claimed that he had costed his proposal",
    ),
    (
        "fracas_196_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant IndefArt NumSg) (UseN lawyer_N)) (ComplSlash (SlashV2a sign_V2) (DetCN every_Det (UseN report_N)))))",
        "a lawyer signed every report",
    ),
    (
        "fracas_196_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) (UseN lawyer_N)) (ComplSlash (SlashV2a sign_V2) (PredetNP all_Predet (DetCN (DetQuant DefArt NumPl) (UseN report_N))))))",
        "one lawyer signed all the reports",
    ),
    (
        "fracas_196_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))))) (UseN auditor_N)) (ComplSlash (SlashV2a sign_V2) (PredetNP all_Predet (DetCN (DetQuant DefArt NumPl) (UseN report_N))))))",
        "one auditor signed all the reports",
    ),
]

# FraCaS Section 5 (Adjectives), problems 197-219 (Section5/Batch1-2.lean).
# Intersective/subsective/privative adjective distinctions - noun/
# adjective-drop for affirmative adjectives, the opposite entailment
# for privatives ("former"), adjective ordering with a stacked
# privative+affirmative pair, contrary (not contradictory) comparison-
# class adjectives, comparatives via ComparA, and extensional vs.
# intensional comparison classes. Every sentence here is a plain
# present-tense copula predication - by far the simplest section's
# worth of GF sentences so far, no new module needed. Self-declares
# dumbo_PN, fido_PN, kim_PN (FraCaS's own recurring cast - mickey_PN
# and bill_PN are NOT here, both already free from DictEngAbs) and
# fourLegged_A (genuine dictionary gap). Every other word (diamond_N,
# genuine_A, former_A, successful_A, mammal_N, animal_N, mouse_N,
# elephant_N, small_A, large_A, fat_A, competent_A, clever_A,
# politician_N, legal_A, authority_N, law_N, lecturer_N) already
# exists in DictEngAbs.
#
# ComparA : A -> NP -> AP ("warmer than I", Adjective module, already
# extended) gives every comparative here directly - "smaller than
# Dumbo" via `UseComp (CompAP (ComparA small_A (UsePN dumbo_PN)))`, and
# "a fatter politician than Bill" via `AdjCN (ComparA fat_A (UsePN
# bill_PN)) politician_N` - confirmed to place the comparative AFTER
# the noun ("a politician fatter than Bill"), not before it, since the
# AP now carries its own "than Bill" complement; standard English
# placement for a "heavy" AP, and equally faithful to the meaning, not
# a bug.
#
# The one real trap hit here: "all mice are small animals"/"all
# elephants are large animals"/etc use a bare `all_Det` at first,
# which doesn't exist (a genuine "Function all_Det is not in scope"
# error, caught locally) - this project's own established pattern for
# "all Xs are Ys" is `PredetNP all_Predet` wrapping a bare-plural
# `DetCN (DetQuant IndefArt NumPl) cn`, same as Section 2's own
# all_Predet uses, not a dedicated determiner.
BASE_CHECKS += [
    (
        "fracas_197_premise",
        "linearize PredVP (UsePN john_PN) (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA genuine_A) (UseN diamond_N))))",
        "John has a genuine diamond",
    ),
    (
        "fracas_197_hypothesis",
        "linearize PredVP (UsePN john_PN) (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (UseN diamond_N)))",
        "John has a diamond",
    ),
    (
        "fracas_198_premise",
        "linearize PredVP (UsePN john_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA former_A) (CompoundCN (UseN university_N) (UseN student_N))))))",
        "John is a former university student",
    ),
    (
        "fracas_198_hypothesis",
        "linearize PredVP (UsePN john_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN university_N) (UseN student_N)))))",
        "John is a university student",
    ),
    (
        "fracas_199_premise",
        "linearize PredVP (UsePN john_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA successful_A) (AdjCN (PositA former_A) (CompoundCN (UseN university_N) (UseN student_N)))))))",
        "John is a successful former university student",
    ),
    (
        "fracas_199_hypothesis",
        "linearize PredVP (UsePN john_PN) (UseComp (CompAP (PositA successful_A)))",
        "John is successful",
    ),
    (
        "fracas_202_premise",
        "linearize PredVP (DetCN every_Det (UseN mammal_N)) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN animal_N))))",
        "every mammal is an animal",
    ),
    (
        "fracas_202_hypothesis",
        "linearize PredVP (DetCN every_Det (AdjCN (PositA fourLegged_A) (UseN mammal_N))) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA fourLegged_A) (UseN animal_N)))))",
        "every four-legged mammal is a four-legged animal",
    ),
    (
        "fracas_203_premise",
        "linearize PredVP (UsePN dumbo_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA fourLegged_A) (UseN animal_N)))))",
        "Dumbo is a four-legged animal",
    ),
    (
        "fracas_203_hypothesis",
        "linearize PredVP (UsePN dumbo_PN) (UseComp (CompAP (PositA fourLegged_A)))",
        "Dumbo is four-legged",
    ),
    (
        "fracas_204_premise",
        "linearize PredVP (UsePN mickey_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA small_A) (UseN animal_N)))))",
        "Mickey is a small animal",
    ),
    (
        "fracas_205_premise",
        "linearize PredVP (UsePN dumbo_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA large_A) (UseN animal_N)))))",
        "Dumbo is a large animal",
    ),
    (
        # fracas_204's own contrary-adjective aux fact needs BOTH "small"
        # and "large" named - "large" isn't in 204's own premise at all,
        # so this reuses fracas_205's own already-confirmed premise tree
        # purely to name it (the subject, Dumbo, is irrelevant here).
        "fracas_204_hypothesis",
        "linearize PredVP (UsePN dumbo_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA large_A) (UseN animal_N)))))",
        "Dumbo is a large animal",
    ),
    (
        # Symmetric reuse: fracas_205 needs "small" named too, from
        # fracas_204's own already-confirmed premise tree.
        "fracas_205_hypothesis",
        "linearize PredVP (UsePN mickey_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA small_A) (UseN animal_N)))))",
        "Mickey is a small animal",
    ),
    (
        "fracas_208_hypothesis",
        "linearize PredVP (UsePN mickey_PN) (UseComp (CompAP (ComparA small_A (UsePN dumbo_PN))))",
        "Mickey is smaller than Dumbo",
    ),
    (
        # fracas_208's own two premises ("Mickey is a small animal"/
        # "Dumbo is a large animal") are identical to fracas_204's/205's
        # own premises - reusing those already-confirmed trees rather
        # than re-linearizing them.
        "fracas_208_premise1",
        "linearize PredVP (UsePN mickey_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA small_A) (UseN animal_N)))))",
        "Mickey is a small animal",
    ),
    (
        "fracas_208_premise2",
        "linearize PredVP (UsePN dumbo_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA large_A) (UseN animal_N)))))",
        "Dumbo is a large animal",
    ),
    (
        "fracas_209_hypothesis",
        "linearize PredVP (UsePN mickey_PN) (UseComp (CompAP (ComparA large_A (UsePN dumbo_PN))))",
        "Mickey is larger than Dumbo",
    ),
    (
        # Same reuse as fracas_208's own premises - fracas_209 shares the
        # identical antecedent (only the hypothesis differs).
        "fracas_209_premise1",
        "linearize PredVP (UsePN mickey_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA small_A) (UseN animal_N)))))",
        "Mickey is a small animal",
    ),
    (
        "fracas_209_premise2",
        "linearize PredVP (UsePN dumbo_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA large_A) (UseN animal_N)))))",
        "Dumbo is a large animal",
    ),
    (
        "fracas_210_premise1",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (UseN mouse_N))) (UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA small_A) (UseN animal_N)))))",
        "all mice are small animals",
    ),
    (
        "fracas_210_premise2",
        "linearize PredVP (UsePN mickey_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA large_A) (UseN mouse_N)))))",
        "Mickey is a large mouse",
    ),
    (
        # fracas_210's own conclusion needs "largeAnimal" (fused
        # adjective+noun) named - not present in 210's own two premises
        # at all, so this reuses fracas_205's own already-confirmed
        # premise tree purely to name it.
        "fracas_210_hypothesis",
        "linearize PredVP (UsePN dumbo_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA large_A) (UseN animal_N)))))",
        "Dumbo is a large animal",
    ),
    (
        "fracas_211_premise1",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (UseN elephant_N))) (UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA large_A) (UseN animal_N)))))",
        "all elephants are large animals",
    ),
    (
        "fracas_211_premise2",
        "linearize PredVP (UsePN dumbo_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA small_A) (UseN elephant_N)))))",
        "Dumbo is a small elephant",
    ),
    (
        # Symmetric to 210's own reuse: fracas_211 needs "smallAnimal"
        # named, from fracas_204's own already-confirmed premise tree.
        "fracas_211_hypothesis",
        "linearize PredVP (UsePN mickey_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA small_A) (UseN animal_N)))))",
        "Mickey is a small animal",
    ),
    (
        "fracas_212_hypothesis",
        "linearize PredVP (UsePN dumbo_PN) (UseComp (CompAP (ComparA large_A (UsePN mickey_PN))))",
        "Dumbo is larger than Mickey",
    ),
    (
        # fracas_212's own four premises are identical to fracas_210's/
        # fracas_211's own two premises each (it combines both problems'
        # setups) - reusing those already-confirmed trees rather than
        # re-linearizing them.
        "fracas_212_premise1",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (UseN mouse_N))) (UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA small_A) (UseN animal_N)))))",
        "all mice are small animals",
    ),
    (
        "fracas_212_premise2",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (UseN elephant_N))) (UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA large_A) (UseN animal_N)))))",
        "all elephants are large animals",
    ),
    (
        "fracas_212_premise3",
        "linearize PredVP (UsePN mickey_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA large_A) (UseN mouse_N)))))",
        "Mickey is a large mouse",
    ),
    (
        "fracas_212_premise4",
        "linearize PredVP (UsePN dumbo_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA small_A) (UseN elephant_N)))))",
        "Dumbo is a small elephant",
    ),
    (
        "fracas_213_hypothesis",
        "linearize PredVP (UsePN mickey_PN) (UseComp (CompAP (PositA small_A)))",
        "Mickey is small",
    ),
    (
        "fracas_214_premise1",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA legal_A) (UseN authority_N)))) (UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN law_N) (UseN lecturer_N)))))",
        "all legal authorities are law lecturers",
    ),
    (
        "fracas_214_premise2",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN law_N) (UseN lecturer_N)))) (UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA legal_A) (UseN authority_N)))))",
        "all law lecturers are legal authorities",
    ),
    (
        "fracas_214_hypothesis",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA fat_A) (AdjCN (PositA legal_A) (UseN authority_N))))) (UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA fat_A) (CompoundCN (UseN law_N) (UseN lecturer_N))))))",
        "all fat legal authorities are fat law lecturers",
    ),
    (
        "fracas_215_hypothesis",
        "linearize PredVP (PredetNP all_Predet (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA competent_A) (AdjCN (PositA legal_A) (UseN authority_N))))) (UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA competent_A) (CompoundCN (UseN law_N) (UseN lecturer_N))))))",
        "all competent legal authorities are competent law lecturers",
    ),
    (
        "fracas_216_premise",
        "linearize PredVP (UsePN john_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (ComparA fat_A (UsePN bill_PN)) (UseN politician_N)))))",
        "John is a politician fatter than Bill",
    ),
    (
        "fracas_216_hypothesis",
        "linearize PredVP (UsePN john_PN) (UseComp (CompAP (ComparA fat_A (UsePN bill_PN))))",
        "John is fatter than Bill",
    ),
    (
        "fracas_217_premise",
        "linearize PredVP (UsePN john_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (ComparA clever_A (UsePN bill_PN)) (UseN politician_N)))))",
        "John is a politician cleverer than Bill",
    ),
    (
        "fracas_217_hypothesis",
        "linearize PredVP (UsePN john_PN) (UseComp (CompAP (ComparA clever_A (UsePN bill_PN))))",
        "John is cleverer than Bill",
    ),
    (
        "fracas_218_premise",
        "linearize PredVP (UsePN kim_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA clever_A) (UseN person_N)))))",
        "Kim is a clever person",
    ),
    (
        "fracas_218_hypothesis",
        "linearize PredVP (UsePN kim_PN) (UseComp (CompAP (PositA clever_A)))",
        "Kim is clever",
    ),
    (
        "fracas_219_premise",
        "linearize PredVP (UsePN kim_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA clever_A) (UseN politician_N)))))",
        "Kim is a clever politician",
    ),
]

# 206/207's own premises are already S-typed (built via `UseCl ... PNeg
# (...)` directly to get the negative polarity), not a bare Cl -
# same reasoning as every earlier tensed-exempt list.
_SECTION5_TENSED_CHECKS = [
    (
        "fracas_206_premise",
        "linearize UseCl (TTAnt TPres ASimul) PNeg (PredVP (UsePN fido_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA small_A) (UseN animal_N))))))",
        "Fido isn't a small animal",
    ),
    (
        "fracas_207_premise",
        "linearize UseCl (TTAnt TPres ASimul) PNeg (PredVP (UsePN fido_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA large_A) (UseN animal_N))))))",
        "Fido isn't a large animal",
    ),
]

# FraCaS Section 6 (Comparatives), problems 220-250 (Section6/Batch1-2.lean).
# "Faster than"/"as fast as" licensing or refuting a bare "fast"
# predication via an assumed connecting fact (220-229), genuine
# cardinal comparatives as real Nat arithmetic (230-243), and
# quantified comparative standards reusing Every/Some (246-250).
#
# ComparA (Adjective, already extended since Section 5) and CAdvAP +
# as_CAdv ("as cool as John" - CAdvAP in Adjective, as_CAdv in
# Structural, both already extended, newly exercised this section)
# cover every comparative/equative here. Self-declares pc6082_PN,
# itelXZ_PN, itelZX_PN, itelZY_PN, apcom_PN (FraCaS's own recurring
# computer-market cast - itel_PN itself is NOT here, already
# self-declared in Section 3), itelComputer_N (fused, same reasoning
# as apcomManager_N in Section 2), and mips_N (genuine dictionary
# gap - declared with an explicit invariant plural, `mkN "MIPS"
# "MIPS"`, after a single-arg mkN's own regular pluralization first
# gave "MIPSs", caught locally). Every other word (fast_A, slow_A,
# order_N, win_V2, lose_V2, sell_V2, computer_N, at_least_AdN,
# exactly_AdN) already exists or was already self-declared.
#
# Genuine numeral-building bugs caught locally, not assumed: `pot2`/
# `pot3plus` (hundreds/thousands) both take a `Sub10`/`Sub1000`
# argument, not a bare `Digit`/`Numeral` - `pot2 n5` alone is a real
# "Couldn't match expected type Sub10" error; fixed to `pot2 (pot0
# n5)`, the same `pot0`-first coercion single digits already needed.
# "Eleven" is `pot111` (Numeral's own dedicated irregular constant, not
# `pot1plus` composing "one" + "ten" + "one" the regular way - "eleven"
# isn't decomposable that way at all).
#
# Genuinely skipped: FraCaS's own "more N than NP" cardinal-comparative-
# quantifier construction ("ITEL won more orders than APCOM(did)",
# "twice as many orders", "3000 more computers") has no combinator in
# this grammar - "more"/"twice as many" modifying a plural count noun's
# quantity relative to another NP is a different construction from
# ComparA's own adjective-comparative machinery, and building it from
# scratch for a handful of sentences whose own Lean formalization is
# already pure `Nat` arithmetic (never itself tied to a GF tree) isn't
# worth it; every OTHER sentence in 230-243 (the plain counts and
# "at least"/"exactly" bounds) is still built and confirmed normally.
# 236/237/244/245 (comparative-ellipsis readings whose own Lean proofs
# are bare `id` over an opaque Prop variable) are skipped for the same
# reason - each one's own premise is the same unbuilt "more N than NP"
# construction.
BASE_CHECKS += [
    (
        "fracas_220_premise1",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA fast_A (UsePN itelXZ_PN))))",
        "the PC-6082 is faster than the ITEL-XZ",
    ),
    (
        "fracas_220_premise2",
        "linearize PredVP (UsePN itelXZ_PN) (UseComp (CompAP (PositA fast_A)))",
        "the ITEL-XZ is fast",
    ),
    (
        "fracas_220_hypothesis",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (PositA fast_A)))",
        "the PC-6082 is fast",
    ),
    (
        # fracas_223's own premise 1 ("PC-6082 is faster than ITEL-XZ")
        # is identical to fracas_220's own premise 1 - reusing its
        # already-confirmed tree rather than re-linearizing it.
        "fracas_223_premise1",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA fast_A (UsePN itelXZ_PN))))",
        "the PC-6082 is faster than the ITEL-XZ",
    ),
    (
        "fracas_223_premise2",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (PositA slow_A)))",
        "the PC-6082 is slow",
    ),
    (
        # fracas_223's own hypothesis, resolved (before negation), is
        # "the ITEL-XZ is fast" - identical to fracas_220's own premise
        # 2, reused for naming "fast" rather than re-linearizing it.
        "fracas_223_hypothesis",
        "linearize PredVP (UsePN itelXZ_PN) (UseComp (CompAP (PositA fast_A)))",
        "the ITEL-XZ is fast",
    ),
    (
        "fracas_224_premise1",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (CAdvAP as_CAdv (PositA fast_A) (UsePN itelXZ_PN))))",
        "the PC-6082 is as fast as the ITEL-XZ",
    ),
    (
        # fracas_224's own premise 2 ("ITEL-XZ is fast") is identical to
        # fracas_220's own premise 2 - reused rather than re-linearized.
        "fracas_224_premise2",
        "linearize PredVP (UsePN itelXZ_PN) (UseComp (CompAP (PositA fast_A)))",
        "the ITEL-XZ is fast",
    ),
    (
        # fracas_227's own three roles are each identical to an
        # already-confirmed sibling id's own tree: premise 1 to
        # fracas_224's, premise 2 to fracas_223's, and the hypothesis
        # (resolved, before negation) to fracas_220's own premise 2.
        "fracas_227_premise1",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (CAdvAP as_CAdv (PositA fast_A) (UsePN itelXZ_PN))))",
        "the PC-6082 is as fast as the ITEL-XZ",
    ),
    (
        "fracas_227_premise2",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (PositA slow_A)))",
        "the PC-6082 is slow",
    ),
    (
        "fracas_227_hypothesis",
        "linearize PredVP (UsePN itelXZ_PN) (UseComp (CompAP (PositA fast_A)))",
        "the ITEL-XZ is fast",
    ),
    (
        "fracas_229_hypothesis",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA slow_A (UsePN itelXZ_PN))))",
        "the PC-6082 is slower than the ITEL-XZ",
    ),
    (
        # fracas_229's own premise ("PC-6082 is as fast as ITEL-XZ") is
        # identical to fracas_224's own premise 1 - reused rather than
        # re-linearized.
        "fracas_229_premise",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (CAdvAP as_CAdv (PositA fast_A) (UsePN itelXZ_PN))))",
        "the PC-6082 is as fast as the ITEL-XZ",
    ),
    (
        "fracas_242_premise1",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA fast_A (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot2 (pot0 n5))))))) (UseN mips_N)))))",
        "the PC-6082 is faster than five hundred MIPS",
    ),
    (
        "fracas_242_premise2",
        "linearize PredVP (UsePN itelZX_PN) (UseComp (CompAP (ComparA slow_A (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot2 (pot0 n5))))))) (UseN mips_N)))))",
        "the ITEL-ZX is slower than five hundred MIPS",
    ),
    (
        "fracas_242_hypothesis",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA fast_A (UsePN itelZX_PN))))",
        "the PC-6082 is faster than the ITEL-ZX",
    ),
    (
        "fracas_246_premise1",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA fast_A (DetCN every_Det (UseN itelComputer_N)))))",
        "the PC-6082 is faster than every ITEL computer",
    ),
    (
        "fracas_246_premise2",
        "linearize PredVP (UsePN itelZX_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN itelComputer_N))))",
        "the ITEL-ZX is an ITEL computer",
    ),
    (
        "fracas_247_premise1",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA fast_A (DetCN (DetQuant IndefArt NumSg) (UseN itelComputer_N)))))",
        "the PC-6082 is faster than an ITEL computer",
    ),
    (
        # fracas_248's own "faster than any ITEL computer" gets the same
        # universal formalization as fracas_246's own "every" (per
        # Comparatives.lean's own approach note: "any" is universal here,
        # not an NPI) - reusing its own premise 1/2 trees rather than
        # building a fresh "any_Det" tree for truth-conditionally
        # identical content.
        "fracas_248_premise1",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA fast_A (DetCN every_Det (UseN itelComputer_N)))))",
        "the PC-6082 is faster than every ITEL computer",
    ),
    (
        "fracas_248_premise2",
        "linearize PredVP (UsePN itelZX_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN itelComputer_N))))",
        "the ITEL-ZX is an ITEL computer",
    ),
    (
        "fracas_249_premise",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA fast_A (ConjNP and_Conj (BaseNP (UsePN itelZX_PN) (UsePN itelZY_PN))))))",
        "the PC-6082 is faster than the ITEL-ZX and the ITEL-ZY",
    ),
    (
        "fracas_250_premise",
        "linearize PredVP (UsePN pc6082_PN) (UseComp (CompAP (ComparA fast_A (ConjNP or_Conj (BaseNP (UsePN itelZX_PN) (UsePN itelZY_PN))))))",
        "the PC-6082 is faster than the ITEL-ZX or the ITEL-ZY",
    ),
]

# 230-243's own sentences are past tense ("won"/"lost"/"sold") - same
# reasoning as every earlier tensed-exempt list.
_SECTION6_TENSED_CHECKS = [
    (
        "fracas_230_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (ComplSlash (SlashV2a win_V2) (DetCN somePl_Det (UseN order_N)))))",
        "ITEL won some orders",
    ),
    (
        "fracas_232_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN apcom_PN) (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 pot110)))))) (UseN order_N)))))",
        "APCOM won ten orders",
    ),
    (
        "fracas_232_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN (NumNumeral (num (pot2as3 (pot1as2 pot111))))))) (UseN order_N)))))",
        "ITEL won at least eleven orders",
    ),
    (
        "fracas_234_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN apcom_PN) (ComplSlash (SlashV2a win_V2) (DetCN somePl_Det (UseN order_N)))))",
        "APCOM won some orders",
    ),
    (
        "fracas_238_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 (pot1 n2))))))) (UseN order_N)))))",
        "ITEL won twenty orders",
    ),
    (
        "fracas_240_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN apcom_PN) (ComplSlash (SlashV2a lose_V2) (DetCN somePl_Det (UseN order_N)))))",
        "APCOM lost some orders",
    ),
    (
        "fracas_241_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN apcom_PN) (ComplSlash (SlashV2a lose_V2) (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot2as3 (pot1as2 pot110)))))) (UseN order_N)))))",
        "APCOM lost ten orders",
    ),
    (
        "fracas_243_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN apcom_PN) (ComplSlash (SlashV2a sell_V2) (DetCN (DetQuant IndefArt (NumCard (AdNum exactly_AdN (NumNumeral (num (pot3plus (pot1as2 (pot0as1 (pot0 n2))) (pot2 (pot0 n5)))))))) (UseN computer_N)))))",
        "APCOM sold exactly two thousand five hundred computers",
    ),
    (
        "fracas_243_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (ComplSlash (SlashV2a sell_V2) (DetCN (DetQuant IndefArt (NumCard (NumNumeral (num (pot3plus (pot1as2 (pot0as1 (pot0 n5))) (pot2 (pot0 n5))))))) (UseN computer_N)))))",
        "ITEL sold five thousand five hundred computers",
    ),
]

# FraCaS Section 7 (Temporal Reference), problems 251-325
# (Section7/Batch1-5.lean) - the largest FraCaS section, and, uniquely
# among all nine, one whose Lean formalization is ALREADY almost
# entirely abstract: most theorems here are bare `Nat`/`Prop` variables
# (`tSmith tJones : Nat`, `madeALoss : Nat -> Prop`) or pure True/False
# countermodels, never accumulating named concrete predicates the way
# Sections 1-6 do. Given that, this section's own GF checks are a
# REPRESENTATIVE SAMPLE of each distinct English construction FraCaS
# uses (state+"since"+year, accomplishment+"in N hours", event-
# ordering "before"/"after" with named individuals, durative "for N"),
# not one check per Lean theorem the way every earlier section's own
# checks are - many of 251-325's problems literally share the same
# premise/hypothesis text across several problem numbers (e.g. 255-257
# all use "ITEL has made a loss since 1992"/"...in 1993"), so building
# each shared sentence once and noting its reuse in this comment is
# more honest than fifteen near-duplicate labels.
#
# 311-325 are skipped entirely: each combines several constructions
# this grammar has no combinator for at once (embedded modal "would",
# passive "had been duped", nested attitude-verb complements, specific
# calendar dates like "Saturday, July 14th") - genuinely disproportionate
# to build from scratch for problems whose own Lean formalizations are
# already pure Nat arithmetic or countermodels never tied to a GF tree.
# 259/260 (specific calendar-date arithmetic) are skipped for the same
# reason.
#
# New self-declared words (all checked directly against DictEngAbs
# first): birmingham_PN, first_A (no plain ordinal adjective exists,
# only compounds like first_class_A), and this section's own recurring
# temporal adverbials - since1992_Adv, in1991_Adv..in1996_Adv,
# inMarch1993_Adv, in1994_Adv, inJuly1994_Adv, inTwoHours_Adv,
# inOneHour_Adv, inTwoYears_Adv, forTwoYears_Adv, forAYear_Adv,
# forAnHour_Adv, forTwoHours_Adv, everyMonth_Adv, everyWeek_Adv - each
# self-declared as a fixed Adv rather than built from a general Year/
# Duration subsystem, same "disproportionate machinery for a one-off
# adverbial" reasoning as onTuesday_Adv (Section 3)/atFourOClock_Adv
# (Section 4), just with many more of them at once. Every other word
# already exists in DictEngAbs.
#
# after_Subj (Structural, already free - a genuine "before"/"after"
# subordinator pair, not just before_Subj alone) newly exercised this
# section for the "after" half of every event-ordering sentence.
# AdvS/SubjS's own fixed clause-ordering (subordinate clause always
# fronted, same as Section 2's "if" and Section 4's "before") means
# "Smith left before Jones left" comes out "before Jones left, Smith
# left" - the same accepted reordering as those sections.
#
# A few deliberate simplifications, same spirit as every earlier
# section: progressive aspect ("was running a business", "was writing
# a report") is dropped to plain past ("ran a business", "wrote a
# report") throughout, since Idiom's ProgrVP is unavailable (see
# Section 3's own comment on why) and this section never needs the
# progressive/non-progressive contrast to be visible in the GF
# rendering itself. "Spent N hours/years V-ing" (a gerund-complement
# construction under "spend", recurring across ~2/2 285/286, 289,
# 291-293, 296) is skipped throughout - genuinely new grammatical
# machinery (GerundNP exists in Extend, but "spend" taking a duration
# NP plus a bare gerund adjunct has no confirmed combinator) that would
# take real effort to get right for sentences whose own Lean content
# is, again, pure Nat arithmetic never tied to a GF tree.
BASE_CHECKS += [
    (
        "fracas_251_premise",
        "linearize PredVP (UsePN itel_PN) (ComplSlash (SlashV2a have_V2) (DetCN (DetQuant IndefArt NumSg) (AdvCN (UseN factory_N) (PrepNP in_Prep (UsePN birmingham_PN)))))",
        "ITEL has a factory in Birmingham",
    ),
]

_SECTION7_TENSED_CHECKS = [
    (
        "fracas_252_premise1",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (UsePN itel_PN) (AdvVP (UseComp (CompAdv (PrepNP in_Prep (UsePN birmingham_PN)))) since1992_Adv)))",
        "ITEL has been in Birmingham since 1992",
    ),
    (
        "fracas_252_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (UseComp (CompAdv (PrepNP in_Prep (UsePN birmingham_PN)))) in1993_Adv)))",
        "ITEL was in Birmingham in 1993",
    ),
    (
        "fracas_253_premise",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a develop_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN editor_N)))) since1992_Adv)))",
        "ITEL has developed a new editor since 1992",
    ),
    (
        "fracas_253_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a develop_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN editor_N)))) in1993_Adv)))",
        "ITEL developed a new editor in 1993",
    ),
    (
        "fracas_254_premise",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (UsePN itel_PN) (AdvVP (UseV expand_V) since1992_Adv)))",
        "ITEL has expanded since 1992",
    ),
    (
        "fracas_254_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (UseV expand_V) in1993_Adv)))",
        "ITEL expanded in 1993",
    ),
    (
        "fracas_255_premise",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a make_V2) (DetCN (DetQuant IndefArt NumSg) (UseN loss_N))) since1992_Adv)))",
        "ITEL has made a loss since 1992",
    ),
    (
        "fracas_255_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a make_V2) (DetCN (DetQuant IndefArt NumSg) (UseN loss_N))) in1993_Adv)))",
        "ITEL made a loss in 1993",
    ),
    (
        # 257 has no own premise/hypothesis sentence in FraCaS's corpus at
        # all - Batch1.lean's own comment on 257 ("formally identical with
        # preceding") confirms it's the exact same sentence as 255, just
        # given `.yes` instead of `.unknown`; reused verbatim here under
        # 257's own role name so it gets its own by_id entry.
        "fracas_257_premise",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a make_V2) (DetCN (DetQuant IndefArt NumSg) (UseN loss_N))) since1992_Adv)))",
        "ITEL has made a loss since 1992",
    ),
    (
        "fracas_257_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a make_V2) (DetCN (DetQuant IndefArt NumSg) (UseN loss_N))) in1993_Adv)))",
        "ITEL made a loss in 1993",
    ),
    (
        "fracas_258_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN apcom_PN) (AdvVP (ComplSlash (SlashV2a found_V2) (UsePN itel_PN)) inMarch1993_Adv)))",
        "APCOM founded ITEL in March 1993",
    ),
    (
        "fracas_258_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (UseV exist_V) in1992_Adv)))",
        "ITEL existed in 1992",
    ),
    (
        # Bare "APCOM signed the contract", no "yesterday" adverbial - the
        # real theorem's own `signedOn (todayDay - 1)`/`signedOn 13`
        # relates this predicate to literal day numbers (14, 13) read
        # directly off Problems.lean's own English ("Today is Saturday,
        # July 14th"), not derived from any GF tree (same move as 252's
        # own hardcoded "1996" literal) - this tree supplies only the
        # predicate's name, not the day arithmetic itself.
        "fracas_260_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN apcom_PN) (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))",
        "APCOM signed the contract",
    ),
    (
        "fracas_261_premise1",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV leave_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV leave_V))))",
        "before Jones left Smith left",
    ),
    (
        "fracas_261_hypothesis",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN anderson_PN) (UseV leave_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV leave_V))))",
        "before Anderson left Smith left",
    ),
    (
        # 261's own second premise - "Jones left before Anderson left" -
        # was missing from this suite even though it's a real, independent
        # FraCaS premise (not a synthesized fact): main=Jones (earlier),
        # embedded=Anderson, same before_Subj convention as premise1.
        "fracas_261_premise2",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN anderson_PN) (UseV leave_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV leave_V))))",
        "before Anderson left Jones left",
    ),
    (
        "fracas_262_premise1",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV leave_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV leave_V))))",
        "after Jones left Smith left",
    ),
    (
        # Likewise 262's own real second premise - "Jones left after
        # Anderson left" - previously missing.
        "fracas_262_premise2",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN anderson_PN) (UseV leave_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV leave_V))))",
        "after Anderson left Jones left",
    ),
    (
        "fracas_262_hypothesis",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN anderson_PN) (UseV leave_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV leave_V))))",
        "after Anderson left Smith left",
    ),
    (
        "fracas_263_premise1",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV leave_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseComp (CompAP (PositA present_A))))))",
        "after Jones left Smith was present",
    ),
    (
        "fracas_263_premise2",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN anderson_PN) (UseComp (CompAP (PositA present_A)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV leave_V))))",
        "after Anderson was present Jones left",
    ),
    (
        "fracas_264_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV leave_V)))",
        "Smith left",
    ),
    (
        "fracas_264_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV leave_V)))",
        "Jones left",
    ),
    (
        # Reused verbatim from fracas_261_premise1 ("Smith left before Jones
        # left" paraphrased as "before Jones left Smith left") - byte-
        # identical tree, already GF-toolchain-confirmed under that id.
        "fracas_264_premise3",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV leave_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV leave_V))))",
        "before Jones left Smith left",
    ),
    (
        # Reused verbatim from fracas_262_premise1 ("Smith left after Jones
        # left" paraphrased as "after Jones left Smith left") - byte-
        # identical tree, already GF-toolchain-confirmed under that id.
        "fracas_265_premise3",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV leave_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV leave_V))))",
        "after Jones left Smith left",
    ),
    (
        # "Jones left before Smith left" (main=Jones, earlier; subordinate
        # =Smith) - a genuinely new tree (not a byte-identical reuse of
        # any sibling's own), confirmed via direct GF-toolchain linearize
        # before being registered.
        "fracas_266_premise3",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV leave_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV leave_V))))",
        "before Smith left Jones left",
    ),
    (
        "fracas_267_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a revise_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))",
        "Jones revised the contract",
    ),
    (
        "fracas_267_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a revise_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))",
        "Smith revised the contract",
    ),
    (
        "fracas_267_premise3",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a revise_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a revise_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))))))",
        "before Smith revised the contract Jones revised the contract",
    ),
    (
        "fracas_267_hypothesis",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a revise_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a revise_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))))))",
        "after Jones revised the contract Smith revised the contract",
    ),
    (
        # "Jones revised the contract after Smith did" (main=Jones, later;
        # subordinate=Smith) - same subject arrangement as 267's own
        # premise3, connective flipped to after_Subj; genuinely new,
        # confirmed via direct GF-toolchain linearize before registering.
        "fracas_268_premise3",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a revise_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a revise_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))))))",
        "after Smith revised the contract Jones revised the contract",
    ),
    (
        "fracas_269_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV swim_V)))",
        "Smith swam",
    ),
    (
        "fracas_269_premise2",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV swim_V)))",
        "Jones swam",
    ),
    (
        # "Smith swam before Jones swam" (main=Smith, earlier; subordinate=
        # Jones) - this grammar's AdvS/SubjS combinator always fronts the
        # before/after-marked clause, so the correct tree puts the TRUE
        # subordinate subject (Jones) in SubjS and the TRUE main subject
        # (Smith) in the outer slot, even though that reorders the surface
        # text relative to Problems.lean's own (matrix-first) wording - the
        # same paraphrase-not-transcription convention already used by
        # 267's own premise3 (confirmed by direct GF-toolchain linearize
        # cross-check against the real theorem's own stated hypothesis
        # direction for 270, the sibling that does have a real theorem).
        "fracas_269_premise3",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV swim_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV swim_V))))",
        "before Jones swam Smith swam",
    ),
    (
        "fracas_269_hypothesis",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (UseV swim_V)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (UseV swim_V))))",
        "after Smith swam Jones swam",
    ),
    (
        "fracas_270_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (UseV swim_V) (PrepNP to_Prep (DetCN (DetQuant DefArt NumSg) (UseN shore_N))))))",
        "Smith swam to the shore",
    ),
    (
        # "Smith swam to the shore before Jones swam to the shore" (main=
        # Smith, earlier; subordinate=Jones) - see 269_premise3's own
        # comment just above for why Jones (the true subordinate) goes in
        # SubjS and Smith (the true main subject) goes in the outer slot.
        "fracas_270_premise3",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (AdvVP (UseV swim_V) (PrepNP to_Prep (DetCN (DetQuant DefArt NumSg) (UseN shore_N))))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (UseV swim_V) (PrepNP to_Prep (DetCN (DetQuant DefArt NumSg) (UseN shore_N)))))))",
        "before Jones swam to the shore Smith swam to the shore",
    ),
    (
        "fracas_270_hypothesis",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (UseV swim_V) (PrepNP to_Prep (DetCN (DetQuant DefArt NumSg) (UseN shore_N))))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (AdvVP (UseV swim_V) (PrepNP to_Prep (DetCN (DetQuant DefArt NumSg) (UseN shore_N)))))))",
        "after Smith swam to the shore Jones swam to the shore",
    ),
    (
        "fracas_273_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N)))))",
        "Smith wrote the report",
    ),
    (
        "fracas_273_premise3",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))))))",
        "before Smith wrote the report Jones wrote the report",
    ),
    (
        "fracas_273_hypothesis",
        "linearize UttS (AdvS (SubjS after_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))))))",
        "after Jones wrote the report Smith wrote the report",
    ),
    (
        "fracas_275_premise",
        "linearize UttS (AdvS (SubjS before_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePron he_Pron) (ComplSlash (SlashV2a lose_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN temper_N)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a leave_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N))))))",
        "before he lost his temper Smith left the meeting",
    ),
    (
        "fracas_275_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a lose_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN temper_N)))))",
        "Smith lost his temper",
    ),
    (
        "fracas_277_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (AdvVP (UseV live_V) (PrepNP in_Prep (UsePN birmingham_PN))) in1991_Adv)))",
        "Smith lived in Birmingham in 1991",
    ),
    (
        "fracas_277_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (AdvVP (UseV live_V) (PrepNP in_Prep (UsePN birmingham_PN))) in1992_Adv)))",
        "Smith lived in Birmingham in 1992",
    ),
    (
        "fracas_278_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (AdjCN (PositA first_A) (UseN novel_N)))) in1991_Adv)))",
        "Smith wrote his first novel in 1991",
    ),
    (
        "fracas_278_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (AdjCN (PositA first_A) (UseN novel_N)))) in1992_Adv)))",
        "Smith wrote his first novel in 1992",
    ),
    (
        "fracas_279_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN novel_N))) in1991_Adv)))",
        "Smith wrote a novel in 1991",
    ),
    (
        "fracas_279_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (UsePron it_Pron)) in1992_Adv)))",
        "Smith wrote it in 1992",
    ),
    (
        "fracas_280_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN novel_N))) in1992_Adv)))",
        "Smith wrote a novel in 1992",
    ),
    (
        "fracas_281_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a run_V2) (DetCN (DetQuant IndefArt NumSg) (UseN business_N))) in1991_Adv)))",
        "Smith ran a business in 1991",
    ),
    (
        "fracas_281_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a run_V2) (UsePron it_Pron)) in1992_Adv)))",
        "Smith ran it in 1992",
    ),
    (
        "fracas_282_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a discover_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN species_N)))) in1991_Adv)))",
        "Smith discovered a new species in 1991",
    ),
    (
        "fracas_282_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a discover_V2) (UsePron it_Pron)) in1992_Adv)))",
        "Smith discovered it in 1992",
    ),
    (
        "fracas_283_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a discover_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN species_N)))) in1992_Adv)))",
        "Smith discovered a new species in 1992",
    ),
    (
        "fracas_284_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N))) inTwoHours_Adv)))",
        "Smith wrote a report in two hours",
    ),
    (
        # Reused verbatim from fracas_284_premise1 - same sentence.
        "fracas_286_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N))) inTwoHours_Adv)))",
        "Smith wrote a report in two hours",
    ),
    (
        "fracas_287_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N))) inOneHour_Adv)))",
        "Smith wrote a report in one hour",
    ),
    (
        # Reused verbatim from fracas_284_premise1 - same sentence.
        "fracas_288_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N))) inTwoHours_Adv)))",
        "Smith wrote a report in two hours",
    ),
    (
        "fracas_288_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N)))))",
        "Smith wrote a report",
    ),
    (
        "fracas_289_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a discover_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN species_N)))) inTwoHours_Adv)))",
        "Smith discovered a new species in two hours",
    ),
    (
        "fracas_290_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a discover_V2) (DetCN (DetQuant IndefArt NumSg) (AdjCN (PositA new_A) (UseN species_N))))))",
        "Smith discovered a new species",
    ),
    (
        "fracas_291_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a discover_V2) (DetCN many_Det (AdjCN (PositA new_A) (UseN species_N)))) inTwoHours_Adv)))",
        "Smith discovered many new species in two hours",
    ),
    (
        "fracas_292_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a run_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN business_N))) inTwoYears_Adv)))",
        "Smith ran his business in two years",
    ),
    (
        "fracas_294_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a run_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN business_N)))))",
        "Smith ran his business",
    ),
    (
        # Reused verbatim from fracas_294_hypothesis - 302's own hypothesis
        # ("Smith ran his own business.") is the same bare restatement.
        "fracas_302_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a run_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN business_N)))))",
        "Smith ran his business",
    ),
    (
        "fracas_295_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdvCN (UseN chain_N) (PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (UseN business_N)))))) inTwoYears_Adv)))",
        "Smith owned a chain of businesses in two years",
    ),
    (
        "fracas_297_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a own_V2) (DetCN (DetQuant IndefArt NumSg) (AdvCN (UseN chain_N) (PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (UseN business_N))))))))",
        "Smith owned a chain of businesses",
    ),
    (
        "fracas_298_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (AdvVP (UseV live_V) (PrepNP in_Prep (UsePN birmingham_PN))) forTwoYears_Adv)))",
        "Smith lived in Birmingham for two years",
    ),
    (
        "fracas_298_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (AdvVP (UseV live_V) (PrepNP in_Prep (UsePN birmingham_PN))) forAYear_Adv)))",
        "Smith lived in Birmingham for a year",
    ),
    (
        # Reused verbatim from fracas_298_premise - 299's own premise is
        # the same sentence.
        "fracas_299_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (AdvVP (UseV live_V) (PrepNP in_Prep (UsePN birmingham_PN))) forTwoYears_Adv)))",
        "Smith lived in Birmingham for two years",
    ),
    (
        # Reused verbatim from fracas_298_hypothesis - 299's own hypothesis
        # ("for exactly a year") isn't separately modeled (no combinator
        # for "exactly" on a measure-phrase adverbial), but the duration
        # literal (1) this id's own arithmetic needs is the same either
        # way, matching this generator's existing precedent of reusing a
        # tree purely for a literal/name it doesn't itself supply.
        "fracas_299_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (AdvVP (UseV live_V) (PrepNP in_Prep (UsePN birmingham_PN))) forAYear_Adv)))",
        "Smith lived in Birmingham for a year",
    ),
    (
        "fracas_300_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (UseV live_V) (PrepNP in_Prep (UsePN birmingham_PN)))))",
        "Smith lived in Birmingham",
    ),
    (
        "fracas_301_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a run_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN business_N))) forTwoYears_Adv)))",
        "Smith ran his business for two years",
    ),
    (
        "fracas_301_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a run_V2) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN business_N))) forAYear_Adv)))",
        "Smith ran his business for a year",
    ),
    (
        "fracas_303_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N))) forTwoHours_Adv)))",
        "Smith wrote a report for two hours",
    ),
    (
        "fracas_303_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a write_V2) (DetCN (DetQuant IndefArt NumSg) (UseN report_N))) forAnHour_Adv)))",
        "Smith wrote a report for an hour",
    ),
    (
        "fracas_306_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a discover_V2) (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA new_A) (UseN species_N)))) forTwoYears_Adv)))",
        "Smith discovered new species for two years",
    ),
    (
        "fracas_306_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a discover_V2) (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA new_A) (UseN species_N))))))",
        "Smith discovered new species",
    ),
    (
        "fracas_307_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (AdvVP (ComplSlash (SlashV2a send_V2) (DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN progress_N) (UseN report_N)))) everyMonth_Adv) in1994_Adv)))",
        "ITEL sent a progress report every month in 1994",
    ),
    (
        "fracas_307_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a send_V2) (DetCN (DetQuant IndefArt NumSg) (CompoundCN (UseN progress_N) (UseN report_N)))) inJuly1994_Adv)))",
        "ITEL sent a progress report in July 1994",
    ),
    (
        "fracas_308_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (AdvVP (UseV write_V) (PrepNP to_Prep (DetCN (DetQuant IndefArt NumSg) (UseN representativeMasc_N)))) everyWeek_Adv)))",
        "Smith wrote to a representative every week",
    ),
    (
        # Added in a later round (problem 319): "paid the mortgage
        # interest on the office for eight years" - drops the "before
        # APCOM bought its present office building" event-anchoring
        # entirely (the real theorem never ties yearsPrev/yearsPresent to
        # any event-ordering structure, only to these two literal
        # durations), same "ignore the premise's extra wrapper" move as
        # 258's own event-anchoring simplification.
        "fracas_319_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN apcom_PN) (AdvVP (ComplSlash (SlashV2a pay_V2) (DetCN (DetQuant DefArt NumSg) (AdvCN (CompoundCN (UseN mortgage_N) (UseN interest_N)) (PrepNP on_Prep (DetCN (DetQuant DefArt NumSg) (UseN office_N)))))) forEightYears_Adv)))",
        "APCOM paid the mortgage interest on the office for eight years",
    ),
    (
        "fracas_319_hypothesis",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (UsePN apcom_PN) (AdvVP (ComplSlash (SlashV2a pay_V2) (DetCN (DetQuant DefArt NumSg) (CompoundCN (UseN mortgage_N) (UseN interest_N)))) forMoreThanTenYears_Adv)))",
        "APCOM has paid the mortgage interest for more than ten years",
    ),
    (
        # Added in a later round (problem 321): "has visited Florence
        # twice" / "will visit Florence twice" - "visit" stands in for
        # the idiomatic "been to" (`be_V` isn't in scope as a plain
        # intransitive in this dictionary, checked directly), semantically
        # equivalent for this id's own purposes.
        "fracas_321_premise",
        "linearize UttS (UseCl (TTAnt TPres AAnter) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a visit_V2) (UsePN florence_PN)) twice_Adv)))",
        "Smith has visited Florence twice",
    ),
    (
        "fracas_321_hypothesis",
        "linearize UttS (UseCl (TTAnt TFut ASimul) PPos (PredVP (UsePN smith_PN) (AdvVP (ComplSlash (SlashV2a visit_V2) (UsePN florence_PN)) twice_Adv)))",
        "Smith will visit Florence twice",
    ),
]

# FraCaS Section 8 (Verbs), problems 326-333 (Section8/Batch1.lean) -
# the shortest section, testing the imperfective paradox (a perfective
# accomplishment/achievement entails culmination via an assumed
# connecting fact; the progressive doesn't), interval containment, and
# plural-subject conjunction/collective predicates. Self-declares
# mtalk_PN (ITEL's own invented product), in1990_Adv, and
# from1988to1992_Adv (fixed one-off adverbials, same reasoning as
# Section 7's own). Every other word already exists in DictEngAbs.
# Progressive premises (327/329's "was building"/"was winning") are
# paraphrased to plain past, reusing 326/328's own premise trees, same
# "Idiom's ProgrVP is unavailable" reasoning as Sections 3/7. 333's
# "there was a group of people that met" drops the existential-there
# construction (Idiom again) for the plain "a group of people met".
# Nothing added to translate.py, same reasoning as Sections 5-7 (the
# assumed-connecting-fact/interval-arithmetic content here isn't
# something the generic CN/VP-fusion translator would do justice to).
_SECTION8_TENSED_CHECKS = [
    (
        "fracas_326_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a build_V2) (UsePN mtalk_PN)) in1993_Adv)))",
        "ITEL built MTALK in 1993",
    ),
    (
        "fracas_326_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a finish_V2) (UsePN mtalk_PN)) in1993_Adv)))",
        "ITEL finished MTALK in 1993",
    ),
    (
        "fracas_328_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (AdvVP (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))) (PrepNP from_Prep (UsePN apcom_PN))) in1993_Adv)))",
        "ITEL won the contract from APCOM in 1993",
    ),
    (
        "fracas_328_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt NumSg) (UseN contract_N))) in1993_Adv)))",
        "ITEL won a contract in 1993",
    ),
    (
        "fracas_330_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a own_V2) (UsePN apcom_PN)) from1988to1992_Adv)))",
        "ITEL owned APCOM from 1988 to 1992",
    ),
    (
        "fracas_330_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a own_V2) (UsePN apcom_PN)) in1990_Adv)))",
        "ITEL owned APCOM in 1990",
    ),
    (
        "fracas_331_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (ConjNP and_Conj (BaseNP (UsePN smith_PN) (UsePN jones_PN))) (ComplSlash (SlashV2a leave_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "Smith and Jones left the meeting",
    ),
    (
        "fracas_331_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2a leave_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "Smith left the meeting",
    ),
    (
        "fracas_332_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a leave_V2) (DetCN (DetQuant DefArt NumSg) (UseN meeting_N)))))",
        "Jones left the meeting",
    ),
    (
        "fracas_333_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (ConjNP and_Conj (ConsNP (UsePN smith_PN) (BaseNP (UsePN anderson_PN) (UsePN jones_PN)))) (UseV meet_V)))",
        "Smith , Anderson and Jones met",
    ),
    (
        "fracas_333_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant IndefArt NumSg) (AdvCN (UseN group_N) (PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (UseN person_N))))) (UseV meet_V)))",
        "a group of people met",
    ),
]

# FraCaS Section 9 (Attitudes), problems 334-346 (Section9/Batch1.lean)
# - the final FraCaS section: factive "knew" vs. non-factive "believed"
# (334/335), implicative "managed to" vs. non-implicative "tried to"
# (336/337), literal truth-functional "it is true/false that" (338/339),
# perception-verb ("see") opacity to inferred material (340/341),
# factivity (342), and extensionality/distribution (343-346). No new
# self-declared words at all this section - every word (know_VS,
# believe_VS, manage_VV, try_VV, true_A, false_A, see_V2V, answer_V2,
# phone_N, heart_N, beat_V, when_Subj, helen_PN, department_N,
# secretary_N, copy_N, cross_out_V2, crucial_A, clause_N, make_V2,
# chairman_N) already exists in DictEngAbs.
#
# SentAP (Adjective) + EmbedS (Sentence) - both already extended -
# cover "it is true/false that S" directly ("good that she is here").
# SlashV2V (Verb, already extended) covers "saw X do Y" the same way
# SlashV2/SlashV2a cover plain transitive complements.
#
# One genuine, uniform dictionary quirk confirmed directly (not
# assumed): DictEng's own `see_V2V = mkV2V (IrregEng.see_V) noPrep
# to_Prep` hardcodes a TO-infinitive marker, so every "saw X [VP]"
# sentence here comes out "saw X TO [VP]" ("Smith saw Jones to sign the
# contract") rather than the bare infinitive real perception-verb usage
# takes ("Smith saw Jones sign the contract") - accepted as the
# achievable rendering, the same "don't fight a confirmed dictionary
# quirk" precedent as IdRP's own fixed "that" (Section 3) or only_Predet's
# own fixed "only" (Section 2).
#
# 345/346's own premises (a single "saw" complement conjoining two
# DIFFERENT embedded subjects - "Jones sign the contract and his
# secretary make a copy") are paraphrased as two full repeated "Smith
# saw ..." clauses joined by ConjS, since SlashV2V's own gap is a
# single NP, not a conjoinable list of (subject, VP) pairs - truth-
# conditionally identical to FraCaS's own elliptical original. 346's
# own hypothesis ("Smith either saw ... or saw ...") reuses 346's
# premise tree directly, matching Lean's own `id` proof exactly.
#
# 344's hypothesis ("There is someone whom Helen saw answer the phone")
# is skipped - the same "relativizing a quantificational pronoun NP"
# gap as Section 4's 173/174 and Section 7's 308 (this grammar's
# RelCN-based relatives only relativize CNs, not NPs like "someone").
#
# Nothing added to translate.py, same reasoning as Sections 5-8 (the
# assumed-connecting-fact/factivity content here isn't something the
# generic CN/VP-fusion translator would do justice to).
_SECTION9_TENSED_CHECKS = [
    (
        "fracas_334_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplVS know_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))) in1992_Adv))))))",
        "Smith knew that ITEL had won the contract in 1992",
    ),
    (
        "fracas_334_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))) in1992_Adv)))",
        "ITEL won the contract in 1992",
    ),
    (
        "fracas_335_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplVS believe_VS (UseCl (TTAnt TPast AAnter) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))) in1992_Adv))))))",
        "Smith believed that ITEL had won the contract in 1992",
    ),
    (
        "fracas_336_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplVV manage_VV (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))) in1992_Adv)))",
        "ITEL managed to win the contract in 1992",
    ),
    (
        "fracas_337_premise",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplVV try_VV (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))) in1992_Adv)))",
        "ITEL tried to win the contract in 1992",
    ),
    (
        "fracas_338_premise",
        "linearize PredVP (UsePron it_Pron) (UseComp (CompAP (SentAP (PositA true_A) (EmbedS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))) in1992_Adv)))))))",
        "it is true that ITEL won the contract in 1992",
    ),
    (
        "fracas_339_premise",
        "linearize PredVP (UsePron it_Pron) (UseComp (CompAP (SentAP (PositA false_A) (EmbedS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN itel_PN) (AdvVP (ComplSlash (SlashV2a win_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N))) in1992_Adv)))))))",
        "it is false that ITEL won the contract in 1992",
    ),
    (
        "fracas_340_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2V see_V2V (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))) (UsePN jones_PN))))",
        "Smith saw Jones to sign the contract",
    ),
    (
        "fracas_340_premise2",
        "linearize UttS (AdvS (SubjS if_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN heart_N)) (UseV beat_V))))",
        "if Jones signed the contract his heart beat",
    ),
    (
        "fracas_341_premise2",
        "linearize UttS (AdvS (SubjS when_Subj (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN heart_N)) (UseV beat_V))))",
        "when Jones signed the contract his heart beat",
    ),
    (
        "fracas_340_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2V see_V2V (UseV beat_V)) (DetCN (DetQuant (GenNP (UsePN jones_PN)) NumSg) (UseN heart_N)))))",
        "Smith saw Jones's heart to beat",
    ),
    (
        "fracas_342_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN jones_PN) (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))))",
        "Jones signed the contract",
    ),
    (
        "fracas_343_premise2",
        "linearize PredVP (UsePN jones_PN) (UseComp (CompNP (DetCN (DetQuant DefArt NumSg) (AdvCN (UseN chairman_N) (PrepNP of_Prep (UsePN itel_PN))))))",
        "Jones is the chairman of ITEL",
    ),
    (
        "fracas_343_hypothesis",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2V see_V2V (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))) (DetCN (DetQuant DefArt NumSg) (AdvCN (UseN chairman_N) (PrepNP of_Prep (UsePN itel_PN)))))))",
        "Smith saw the chairman of ITEL to sign the contract",
    ),
    (
        "fracas_344_premise1",
        "linearize UttS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN helen_PN) (ComplSlash (SlashV2V see_V2V (ComplSlash (SlashV2a answer_V2) (DetCN (DetQuant DefArt NumSg) (UseN phone_N)))) (DetCN (DetQuant DefArt NumSg) (AdvCN (UseN chairman_N) (PrepNP of_Prep (DetCN (DetQuant DefArt NumSg) (UseN department_N))))))))",
        "Helen saw the chairman of the department to answer the phone",
    ),
    (
        "fracas_344_premise2",
        "linearize PredVP (DetCN (DetQuant DefArt NumSg) (AdvCN (UseN chairman_N) (PrepNP of_Prep (DetCN (DetQuant DefArt NumSg) (UseN department_N))))) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) (UseN person_N))))",
        "the chairman of the department is a person",
    ),
    (
        "fracas_345_premise",
        "linearize UttS (ConjS and_Conj (BaseS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2V see_V2V (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))) (UsePN jones_PN)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2V see_V2V (ComplSlash (SlashV2a make_V2) (DetCN (DetQuant IndefArt NumSg) (UseN copy_N)))) (DetCN (DetQuant (PossPron he_Pron) NumSg) (UseN secretary_N)))))))",
        "Smith saw Jones to sign the contract and Smith saw his secretary to make a copy",
    ),
    (
        "fracas_346_premise",
        "linearize UttS (ConjS or_Conj (BaseS (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2V see_V2V (ComplSlash (SlashV2a sign_V2) (DetCN (DetQuant DefArt NumSg) (UseN contract_N)))) (UsePN jones_PN)))) (UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN smith_PN) (ComplSlash (SlashV2V see_V2V (ComplSlash (SlashV2a cross_out_V2) (DetCN (DetQuant DefArt NumSg) (AdjCN (PositA crucial_A) (UseN clause_N))))) (UsePN jones_PN))))))",
        "Smith saw Jones to sign the contract or Smith saw Jones to cross out the crucial clause",
    ),
]

# Hypothesis trees for problems whose premise(s) already had a
# confirmed tree above but whose hypothesis never did - closing that
# gap is what scripts/gen_gf_cross_check.py's own generated file
# (GFCrossCheckBatch.lean) needs to cross-check more problems fully
# end to end, rather than just their premises. Each one reuses the
# exact restrictor/VP subtrees the corresponding premise(s) already
# confirmed above (so translate.py's own predicate naming - a pure
# function of an English-word subtree - comes out identical on both
# sides), recombined with whichever quantifier/subject the real
# fracas_NNN theorem's own hypothesis actually needs. Confirmed via
# this project's local GF toolchain before being added here (not
# merely asserted) - see gf/NOTES.md for how that toolchain was set up.
BASE_CHECKS += [
    (
        "fracas_001_hypothesis",
        "linearize PredVP (DetCN (DetQuant IndefArt NumSg) (UseN italian_N)) "
        "(ComplSlash (SlashV2a become_V2) (DetCN worlds_Det (AdjCN (PositA greatest_A) (UseN tenor_N))))",
        "an Italian becomes the world's greatest tenor",
    ),
    (
        "fracas_004_hypothesis",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA italian_A) (UseN tenor_N))) "
        "(ComplVV want_VV (UseComp (CompAP (PositA great_A))))",
        "some Italian tenors want to be great",
    ),
    (
        "fracas_007_hypothesis",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA swedish_A)))",
        "some great tenors are Swedish",
    ),
    (
        "fracas_008_hypothesis",
        "linearize PredVP (DetCN many_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA german_A)))",
        "many great tenors are German",
    ),
    (
        "fracas_009_hypothesis",
        "linearize PredVP (DetCN several_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA british_A)))",
        "several great tenors are British",
    ),
    (
        "fracas_010_hypothesis",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA italian_A)))",
        "some great tenors are Italian",
    ),
    (
        "fracas_011_hypothesis",
        "linearize PredVP (DetCN aFew_Det (AdjCN (PositA great_A) (UseN tenor_N))) "
        "(ComplSlash (SlashV2a sing_V2) (MassNP (AdjCN (PositA popular_A) (UseN music_N))))",
        "a few great tenors sing popular music",
    ),
    (
        "fracas_015_hypothesis",
        "linearize PredVP (DetCN somePl_Det (UseN tenor_N)) "
        "(ComplSlash (SlashV2a take_V2) (AdvNP (MassNP (UseN part_N)) "
        "(PrepNP in_Prep (DetCN (DetQuant DefArt NumSg) (UseN concert_N)))))",
        "some tenors take part in the concert",
    ),
    (
        "fracas_018_hypothesis",
        "linearize PredVP (DetCN every_Det (UseN european_N)) "
        "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) (PrepNP within_Prep (UsePN europe_PN))))",
        "every European can travel freely within Europe",
    ),
    (
        "fracas_021_hypothesis",
        "linearize PredVP (PredetNP all_Predet (AdvNP (DetCN (DetQuant IndefArt NumPl) (UseN resident_N)) "
        "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN member_N) (UseN state_N)))))) "
        "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) (PrepNP within_Prep (UsePN europe_PN))))",
        "all residents of member states can travel freely within Europe",
    ),
    (
        "fracas_026_hypothesis",
        "linearize PredVP (DetCN most_Det (UseN european_N)) "
        "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) (PrepNP within_Prep (UsePN europe_PN))))",
        "most Europeans can travel freely within Europe",
    ),
    (
        "fracas_027_hypothesis",
        "linearize PredVP (DetCN aFew_Det (CompoundCN (UseN committee_N) (UseN member_N))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN scandinavia_PN))))",
        "a few committee members are from Scandinavia",
    ),
    (
        "fracas_049_hypothesis",
        "linearize PredVP (DetCN somePl_Det (UseN scandinavian_N)) "
        "(ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))",
        "some Scandinavians win a Nobel prize",
    ),
    (
        "fracas_097_hypothesis",
        "linearize PredVP (DetCN (DetQuant IndefArt NumPl) (CompoundCN (UseN software_N) (UseN fault_N))) "
        "(AdvVP (PassV2 blame_V2) (PrepNP for_Prep (DetCN (DetQuant DefArt NumSg) "
        "(CompoundCN (UseN system_N) (UseN failure_N)))))",
        "software faults are blamed for the system failure",
    ),
    (
        "fracas_006_hypothesis",
        "linearize PredVP (DetCN somePl_Det (AdjCN (AdAP really_AdA (PositA great_A)) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA modest_A)))",
        "some really great tenors are modest",
    ),
    (
        "fracas_014_hypothesis",
        "linearize PredVP (UsePN pavarotti_PN) (UseComp (CompNP (DetCN (DetQuant IndefArt NumSg) "
        "(RelCN (AdjCN (PositA leading_A) (UseN tenor_N)) "
        "(UseRCl (TTAnt TPres ASimul) PPos (RelVP IdRP (AdvVP (UseV come_V) cheap_Adv)))))))",
        "Pavarotti is a leading tenor that comes cheap",
    ),
    (
        "fracas_002_premise2",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA italian_A) (UseN man_N))) "
        "(UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA great_A) (UseN tenor_N)))))",
        "some Italian men are great tenors",
    ),
    (
        "fracas_002_hypothesis",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA italian_A) (UseN man_N))) "
        "(ComplVV want_VV (UseComp (CompCN (AdjCN (PositA great_A) (UseN tenor_N)))))",
        "some Italian men want to be great tenors",
    ),
    (
        "fracas_003_premise2",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA italian_A) (UseN man_N))) "
        "(UseComp (CompNP (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA great_A) (UseN tenor_N)))))",
        "some Italian men are great tenors",
    ),
    (
        "fracas_003_hypothesis",
        "linearize PredVP (DetCN somePl_Det (AdjCN (PositA italian_A) (UseN man_N))) "
        "(ComplVV want_VV (UseComp (CompCN (AdjCN (PositA great_A) (UseN tenor_N)))))",
        "some Italian men want to be great tenors",
    ),
    (
        "fracas_005_hypothesis",
        "linearize PredVP (DetCN somePl_Det (AdjCN (AdAP really_AdA (PositA ambitious_A)) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA italian_A)))",
        "some really ambitious tenors are Italian",
    ),
    (
        "fracas_013_premise1",
        "linearize PredVP (DetCN every_Det (AdjCN (PositA leading_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA excellent_A)))",
        "every leading tenor is excellent",
    ),
    (
        "fracas_013_hypothesis",
        "linearize PredVP (DetCN every_Det (AdjCN (PositA leading_A) (UseN tenor_N))) "
        "(UseComp (CompAP (PositA indispensable_A)))",
        "every leading tenor is indispensable",
    ),
    (
        "fracas_017_hypothesis",
        "linearize PredVP (DetCN (DetQuant IndefArt NumSg) (UseN irishman_N)) "
        "(ComplSlash (SlashV2a win_V2) (DetCN (DetQuant IndefArt NumSg) (UseN nobelPrize_N)))",
        "an Irishman wins a Nobel prize",
    ),
    (
        "fracas_019_premise2",
        "linearize PredVP (DetCN every_Det (UseN european_N)) (UseComp (CompCN (UseN person_N)))",
        "every European is a person",
    ),
    (
        "fracas_019_premise3",
        f"linearize PredVP {_relative_subject('every_Det', 'person_N')} {_CAN_TRAVEL_FREELY_VP}",
        "every person that has the right to live in Europe can travel freely within Europe",
    ),
    (
        "fracas_019_hypothesis",
        "linearize PredVP (DetCN every_Det (UseN european_N)) "
        "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) (PrepNP within_Prep (UsePN europe_PN))))",
        "every European can travel freely within Europe",
    ),
    (
        "fracas_020_premise2",
        "linearize PredVP (DetCN every_Det (UseN european_N)) (UseComp (CompCN (UseN person_N)))",
        "every European is a person",
    ),
    (
        "fracas_020_premise3",
        f"linearize PredVP {_relative_subject('every_Det', 'person_N')} {_CAN_TRAVEL_FREELY_VP}",
        "every person that has the right to live in Europe can travel freely within Europe",
    ),
    (
        "fracas_020_hypothesis",
        "linearize PredVP (DetCN every_Det (UseN european_N)) "
        "(ComplVV can_VV (AdvVP (AdvVP (UseV travel_V) (PositAdvAdj free_A)) (PrepNP within_Prep (UsePN europe_PN))))",
        "every European can travel freely within Europe",
    ),
    (
        "fracas_055_hypothesis",
        "linearize PredVP (DetCN somePl_Det (UseN delegate_N)) "
        "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN survey_N))) "
        "(PrepNP on_Prep (MassNP (UseN time_N))))",
        "some delegates finish the survey on time",
    ),
    (
        "fracas_057_hypothesis",
        "linearize PredVP (DetCN somePl_Det (UseN delegate_N)) "
        "(ComplSlash (SlashV2a get_V2) (AdvNP (PPartNP (DetCN (DetQuant DefArt NumPl) (UseN result_N)) publish_V2) "
        "(PrepNP in_Prep (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA major_A) "
        "(AdjCN (PositA national_A) (UseN newspaper_N)))))))",
        "some delegates get the results published in major national newspapers",
    ),
    (
        "fracas_059_hypothesis",
        "linearize PredVP (DetCN somePl_Det (CompoundCN (UseN committee_N) (UseN member_N))) "
        "(UseComp (CompAdv (PrepNP from_Prep (UsePN scandinavia_PN))))",
        "some committee members are from Scandinavia",
    ),
    (
        "fracas_063_hypothesis",
        "linearize PredVP (DetCN (DetQuant IndefArt (NumCard (AdNum at_least_AdN "
        "(NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))))))) (UseN commissioner_N)) "
        "(AdvVP (ComplSlash (SlashV2a spend_V2) (MassNP (UseN time_N))) (PrepNP at_Prep (MassNP (UseN home_N))))",
        "at least three commissioners spend time at home",
    ),
    (
        "fracas_069_premise2",
        "linearize PredVP (PredetNP all_Predet (AdvNP (DetCN (DetQuant IndefArt NumPl) (UseN resident_N)) "
        "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA major_A) "
        "(AdjCN (PositA western_A) (UseN country_N))))))) "
        "(UseComp (CompNP (AdvNP (DetCN (DetQuant IndefArt NumPl) (UseN resident_N)) "
        "(PrepNP of_Prep (DetCN (DetQuant IndefArt NumPl) (AdjCN (PositA western_A) (UseN country_N)))))))",
        "all residents of major Western countries are residents of Western countries",
    ),
    (
        "fracas_038_premise",
        "linearize PredVP (DetCN (DetQuant no_Quant NumSg) (UseN delegate_N)) "
        "(ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N)))",
        "no delegate finishes the report",
    ),
    (
        "fracas_038_hypothesis",
        "linearize PredVP (DetCN someSg_Det (UseN delegate_N)) "
        "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))) "
        "(PrepNP on_Prep (MassNP (UseN time_N))))",
        "some delegate finishes the report on time",
    ),
    (
        "fracas_070_premise",
        "linearize PredVP (DetCN (DetQuant no_Quant NumSg) (UseN delegate_N)) "
        "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))) "
        "(PrepNP on_Prep (MassNP (UseN time_N))))",
        "no delegate finishes the report on time",
    ),
    (
        "fracas_070_hypothesis",
        "linearize PredVP (DetCN someSg_Det (AdjCN (PositA scandinavian_A) (UseN delegate_N))) "
        "(AdvVP (ComplSlash (SlashV2a finish_V2) (DetCN (DetQuant DefArt NumSg) (UseN report_N))) "
        "(PrepNP on_Prep (MassNP (UseN time_N))))",
        "some Scandinavian delegate finishes the report on time",
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
    + _SECTION3_TENSED_CHECKS
    + _SECTION4_TENSED_CHECKS
    + _SECTION5_TENSED_CHECKS
    + _SECTION6_TENSED_CHECKS
    + _SECTION7_TENSED_CHECKS
    + _SECTION8_TENSED_CHECKS
    + _SECTION9_TENSED_CHECKS
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
