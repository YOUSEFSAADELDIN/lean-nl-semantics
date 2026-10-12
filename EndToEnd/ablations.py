#!/usr/bin/env python3
"""Soundness ablations: which of the pipeline's safeguards prevent wrong
answers, measured by switching each one off and re-scoring.

The pipeline answers "yes"/"no" only when it can prove it, but several of
its design choices exist because, without them, it proved things FraCaS
says do not follow. This script regenerates the claims with one safeguard
switched off at a time (each in its own process, patching the pipeline's
modules there and nowhere else) and writes the problems whose claims
change to `EndToEnd/Ablations.lean`, with `EndToEnd/ablations.json`
recording what changed. `EndToEnd/AblationScan.lean` scores every claim
of the baseline and of each ablation individually in CI, and
`ablation_report.py` turns that log into wrong-answer counts.

The ablations of the reading rule (one reading instead of every reading,
or FraCaS-style "yes if any reading") need no new claims: they are
computed from the baseline's per-claim results.

Run: `python3 EndToEnd/ablations.py` (needs the gf binary and the
compiled parse grammar, like gen_claims.py). Do not hand-edit its output.
"""
from __future__ import annotations

import json
import pickle
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT_LEAN = HERE / "Ablations.lean"
OUT_JSON = HERE / "ablations.json"


def _no_presupposition():
    """A hypothesis's "no" claim no longer has to establish what the
    hypothesis presupposes ("one of the female commissioners" presupposes
    female commissioners)."""
    import gen_claims
    original = gen_claims.translate_cl_reading

    def patched(*args, **kwargs):
        tr, side, times, extras = original(*args, **kwargs)
        return tr, side, times, {**extras, "presuppositions": []}

    gen_claims.translate_cl_reading = patched


def _coarse_names():
    """Predicate names from content words only: an object's determiner or
    numeral ("a lot of time", "ten orders") and the progressive's marker
    drop out of the name."""
    import background
    import gen_claims
    import readings
    import translate
    original = translate._leaf_words

    def coarse(t, keep_det=False):
        return original(t, False)

    for module in (translate, readings, background, gen_claims):
        if hasattr(module, "_leaf_words"):
            module._leaf_words = coarse
    translate.NAME_MARKERS.clear()


def _no_telicity():
    """Background knowledge treats every verb phrase as not culminating:
    a durative ("for two hours") and the progressive delete from any verb
    phrase, and the rules that need a culminating event do not fire."""
    import background
    background._telic = lambda vp: False


def _no_parse_filters():
    """The ranker keeps every parse (no well-formedness filters: anaphoric
    "one", fragments, clause modifiers, empty noun phrases)."""
    import parse_rank
    parse_rank.well_formed = lambda tree: True


def _no_pronoun_guard():
    """An object pronoun nothing resolves is no longer refused (it drops
    out of the predicate's name)."""
    import gen_claims
    gen_claims._unresolved_object_pronoun = lambda t: False


def _no_lexical_exclusions():
    """Background knowledge deletes every adjective and adverb, including
    non-subsective ones ("former") and non-veridical ones ("allegedly")."""
    import background
    background.NON_SUBSECTIVE.clear()
    background.NON_VERIDICAL.clear()


# name -> (Lean namespace, patch, whether it changes parsing)
def _no_name_check():
    """A name may stand for two different phrases (`names.py`'s check is
    not run)."""
    import gen_claims
    gen_claims.name_clashes = lambda trees, used: {}


ABLATIONS = {
    "no_presupposition": ("NoPresupposition", _no_presupposition, False),
    "coarse_names": ("CoarseNames", _coarse_names, False),
    "no_telicity": ("NoTelicity", _no_telicity, False),
    "no_parse_filters": ("NoParseFilters", _no_parse_filters, True),
    "no_pronoun_guard": ("NoPronounGuard", _no_pronoun_guard, False),
    "no_lexical_exclusions": ("NoLexicalExclusions", _no_lexical_exclusions, False),
    "no_name_check": ("NoNameCheck", _no_name_check, False),
}


def _worker(name: str, cache_in: str, cache_out: str, result: str) -> None:
    """Generate every problem's claims with ablation `name` applied
    ("baseline": none), in this process only."""
    sys.path.insert(0, str(HERE))
    sys.path.insert(0, str(ROOT / "gf"))
    import gen_claims
    if name != "baseline":
        ABLATIONS[name][1]()
    if cache_in:
        gen_claims._parse_cache.update(pickle.loads(Path(cache_in).read_bytes()))
    out = {}
    for idn, premises, hypothesis, answer in gen_claims.load_problems():
        sentences = [(f"premise {i + 1}", p) for i, p in enumerate(premises)]
        sentences.append(("hypothesis", hypothesis))
        claims, reason = gen_claims.assemble(idn, sentences)
        out[idn] = {"answer": answer, "claims": claims, "skip": reason}
    if cache_out:
        Path(cache_out).write_bytes(pickle.dumps(gen_claims._parse_cache))
    Path(result).write_text(json.dumps(out))


def _run(name: str, tmp: Path, cache_in: str = "", cache_out: str = "") -> dict:
    result = tmp / f"{name}.json"
    subprocess.run([sys.executable, __file__, "--worker", name, cache_in, cache_out, str(result)], check=True)
    return {int(k): v for k, v in json.loads(result.read_text()).items()}


def _claim_defs(idn: int, c: dict) -> list[str]:
    lines = []
    for i, asg in enumerate(c["assignments"]):
        for kind in ("yes", "no", "bk_yes", "bk_no"):
            lines.append(f"def fracas_{idn:03d}_{kind}_{i} : Prop :=\n  {asg[kind]}")
            lines.append("")
    return lines


def _registry(namespace: str, rows: list[tuple[int, str, dict]], bk: bool) -> list[str]:
    prefix = "bk_" if bk else ""

    def names(idn, c, kind):
        return [f"``{namespace}.fracas_{idn:03d}_{prefix}{kind}_{i}" for i in range(len(c["assignments"]))]

    body = ",\n".join(
        f"  ({idn}, .{answer}, [{', '.join(names(idn, c, 'yes'))}], [{', '.join(names(idn, c, 'no'))}])"
        for idn, answer, c in rows
    )
    return [body] if body else []


def main() -> None:
    with tempfile.TemporaryDirectory() as d:
        tmp = Path(d)
        cache = str(tmp / "parses.pickle")
        baseline = _run("baseline", tmp, cache_out=cache)
        results = {name: _run(name, tmp, cache_in="" if parsing else cache)
                   for name, (_ns, _patch, parsing) in ABLATIONS.items()}

    manifest = {"reached": sorted(i for i, v in baseline.items() if v["claims"]), "ablations": {}}
    lines = [
        "-- Generated by EndToEnd/ablations.py - do not hand-edit; re-run it.",
        "import LeanNLSemantics.FraCaS.Types",
        "import LeanNLSemantics.FraCaS.Section1.GQ",
        "import LeanNLSemantics.FraCaS.Section2.Plurals",
        "import EndToEnd.Quantifiers",
        "",
        "/-!",
        "# Soundness ablations: claims with one safeguard switched off",
        "",
        "For each ablation (see `EndToEnd/ablations.py` for what each one",
        "switches off), the problems whose claims differ from",
        "`EndToEnd/Claims.lean`'s. Every other problem's claims are the",
        "baseline's. Scored by `EndToEnd/AblationScan.lean`.",
        "-/",
        "",
        "namespace FraCaS.EndToEnd.Ablations",
        "open FraCaS.Section1 FraCaS.Section2",
        "",
    ]
    for name, (namespace, patch, _parsing) in ABLATIONS.items():
        ablated = results[name]
        changed, reached, lost = [], [], []
        for idn, base in baseline.items():
            new = ablated[idn]
            if new["claims"] is None:
                if base["claims"] is not None:
                    lost.append(idn)
                continue
            if base["claims"] is None:
                reached.append(idn)
            elif new["claims"]["assignments"] != base["claims"]["assignments"]:
                changed.append(idn)
        manifest["ablations"][name] = {
            "description": " ".join(patch.__doc__.split()),
            "changed": changed, "newly_reached": reached, "no_longer_reached": lost,
        }
        rows = [(idn, ablated[idn]["answer"], ablated[idn]["claims"]) for idn in sorted(changed + reached)]
        lines += [f"/-! ## `{name}`: {' '.join(patch.__doc__.split())} -/", "", f"namespace {namespace}", ""]
        for idn, _answer, c in rows:
            lines += _claim_defs(idn, c)
        lines += [
            "/-- The ablation's changed and newly reached problems, as in `EndToEnd.registry`. -/",
            "def registry : List (Nat × Answer × List Lean.Name × List Lean.Name) := [",
            *_registry(f"Ablations.{namespace}", rows, bk=False),
            "]",
            "",
            "/-- The same, with background knowledge. -/",
            "def registryBk : List (Nat × Answer × List Lean.Name × List Lean.Name) := [",
            *_registry(f"Ablations.{namespace}", rows, bk=True),
            "]",
            "",
            f"end {namespace}",
            "",
        ]
    Registry = "List (Nat × Answer × List Lean.Name × List Lean.Name)"
    lines += [
        "/-- Every ablation: its name, and its registries without and with",
        "background knowledge. -/",
        f"def all : List (String × {Registry} × {Registry}) := [",
        ",\n".join(f'  ("{name}", {ns}.registry, {ns}.registryBk)' for name, (ns, _p, _q) in ABLATIONS.items()),
        "]",
        "",
        "end FraCaS.EndToEnd.Ablations",
        "",
    ]
    OUT_LEAN.write_text("\n".join(lines))
    OUT_JSON.write_text(json.dumps(manifest, indent=1) + "\n")
    for name, m in manifest["ablations"].items():
        print(f"{name}: {len(m['changed'])} changed, {len(m['newly_reached'])} newly reached, "
              f"{len(m['no_longer_reached'])} no longer reached")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--worker":
        _worker(*sys.argv[2:6])
    else:
        main()
