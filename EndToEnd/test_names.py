#!/usr/bin/env python3
"""Tests for the name check (`names.py`), on the parse trees of the
sentences it exists for. The MED trees are recorded here as strings (the
held-out grammar that parsed them is not built in CI); the FraCaS problems
are parsed with the pipeline's own grammar, as `gen_claims.py` does.

Run from the repository root: `python3 EndToEnd/test_names.py` (needs the
`gf` binary and the compiled EndToEnd/FraCaSEndToEnd.pgf and
FraCaSParse.pgf, like gen_claims.py).
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "gf"))

import readings  # noqa: E402,F401  (fills translate.NAME_MARKERS, as the pipeline does)
import gen_claims  # noqa: E402
import names  # noqa: E402
import translate  # noqa: E402
from translate import parse_tree  # noqa: E402

# MED 2718: "Tom said he didn't drink black coffee."
SAID_NOT = parse_tree(
    "UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN tom_PN) (ComplVSBare say_VS (UseCl (TTAnt TPast ASimul) "
    "PNeg (PredVP (UsePron he_Pron) (ComplSlash (SlashV2a drink_V2) (MassNP (AdjCN (PositA black_A) "
    "(UseN coffee_N))))))))")
DRANK = parse_tree(
    "UseCl (TTAnt TPast ASimul) PPos (PredVP (UsePN tom_PN) (ComplSlash (SlashV2a drink_V2) "
    "(MassNP (AdjCN (PositA black_A) (UseN coffee_N)))))")
DRINKS = parse_tree(
    "UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN tom_PN) (ComplSlash (SlashV2a drink_V2) "
    "(MassNP (AdjCN (PositA black_A) (UseN coffee_N)))))")
# MED 4882: "Every alien who did not throw balls is hairy." / "... who threw balls ..."
WHO_NOT = parse_tree(
    "PredVP (DetCN every_Det (RelCN (UseN alienFem_N) (UseRCl (TTAnt TPast ASimul) UncNeg (RelVP who_RP "
    "(ComplSlash (SlashV2a throw_V2) (DetCN (DetQuant IndefArt NumPl) (UseN ball_N))))))) "
    "(UseComp (CompAP (PositA hairy_A)))")
WHO = parse_tree(
    "PredVP (DetCN every_Det (RelCN (UseN alienFem_N) (UseRCl (TTAnt TPast ASimul) PPos (RelVP who_RP "
    "(ComplSlash (SlashV2a throw_V2) (DetCN (DetQuant IndefArt NumPl) (UseN ball_N))))))) "
    "(UseComp (CompAP (PositA hairy_A)))")
# MED 5067: "Pete believes he is a spider." / MED 1355: "Tom is no longer a kid."
BELIEVES = parse_tree(
    "PredVP (UsePN pete_PN) (ComplVSBare believe_VS (UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePron he_Pron) "
    "(UseComp (CompCN (UseN spider_N))))))")
NO_LONGER = parse_tree("PredVP (UsePN tom_PN) (AdVVP no_longer_AdV (UseComp (CompCN (UseN kid_N))))")
# The progressive and the passive (FraCaS 327's "was building MTALK"; "was impressed")
BUILDING = parse_tree("ProgrVP (ComplSlash (SlashV2a build_V2) (UsePN mtalk_PN))")
BUILT = parse_tree("ComplSlash (SlashV2a build_V2) (UsePN mtalk_PN)")
IMPRESSED = parse_tree("PassV2 impress_V2")
IMPRESS = parse_tree("UseV impress_V")


class LostWords(unittest.TestCase):
    """A name that leaves a word out of its phrase, shared with a phrase
    that has that word, is a clash."""

    def test_said_and_negated_complement(self):
        # the outer verb phrase and the one inside it are both drinkBlackCoffee
        clash = names.clashes([SAID_NOT], {"drinkBlackCoffee"})
        self.assertIn("drinkBlackCoffee", clash)
        self.assertIn(("PNeg", "he_Pron", "say_VS"), clash["drinkBlackCoffee"])

    def test_negated_relative_clause(self):
        clash = names.clashes([WHO_NOT], {"throwBall"})
        self.assertEqual(clash.get("throwBall"), [(), ("UncNeg",)])

    def test_believes(self):
        self.assertIn("spider", names.clashes([BELIEVES], {"spider"}))

    def test_no_longer(self):
        self.assertIn("kid", names.clashes([NO_LONGER], {"kid"}))

    def test_only_used_names_count(self):
        self.assertEqual(names.clashes([SAID_NOT], {"somethingElse"}), {})


class DeliberateOmissions(unittest.TestCase):
    """What `DELIBERATE` lets a name leave out is not a difference."""

    def test_tense(self):
        self.assertEqual(names.clashes([DRANK, DRINKS], {"drinkBlackCoffee"}), {})

    def test_positive_relative_clause(self):
        self.assertEqual(names.clashes([WHO], {"throwBall"}), {})

    def test_articles_and_number(self):
        self.assertEqual(names.lost(parse_tree("DetCN (DetQuant IndefArt NumPl) (UseN ball_N)")), ())


class Constructions(unittest.TestCase):
    """A construction with no word of its own counts when its mark is
    missing from the name."""

    def test_progressive_marked(self):
        # the pipeline marks the progressive, so the names differ
        self.assertNotEqual(names._name(BUILDING), names._name(BUILT))
        self.assertEqual(names.clashes([BUILDING, BUILT], {names._name(BUILT)}), {})

    def test_progressive_unmarked(self):
        saved = dict(translate.NAME_MARKERS)
        try:
            translate.NAME_MARKERS.clear()
            self.assertEqual(names._name(BUILDING), names._name(BUILT))
            self.assertIn("buildMtalk", names.clashes([BUILDING, BUILT], {"buildMtalk"}))
        finally:
            translate.NAME_MARKERS.update(saved)

    def test_passive(self):
        self.assertEqual(names._name(IMPRESSED), names._name(IMPRESS))
        self.assertEqual(names.lost(IMPRESSED), ("PassV2",))
        self.assertIn("impress", names.clashes([IMPRESSED, IMPRESS], {"impress"}))
        self.assertEqual(names.clashes([IMPRESSED], {"impress"}), {})


class Pipeline(unittest.TestCase):
    """End to end, on FraCaS: the check refuses 119 and nothing it reached
    before is affected by it here."""

    def _assemble(self, idn):
        problems = {i: (p, h) for i, p, h, _a in gen_claims.load_problems()}
        premises, hypothesis = problems[idn]
        sentences = [(f"premise {k + 1}", p) for k, p in enumerate(premises)] + [("hypothesis", hypothesis)]
        return gen_claims.assemble(idn, sentences)

    def test_119_refused(self):
        claims, reason = self._assemble(119)
        self.assertIsNone(claims)
        self.assertIn("useWorkstation", reason)

    def test_1_reached(self):
        claims, _reason = self._assemble(1)
        self.assertIsNotNone(claims)


if __name__ == "__main__":
    unittest.main()
