# Provenance: fracas.xml

- **Original**: Cooper et al., "Using the Framework," FraCaS deliverable
  D16 (LRE 62-051r), January 1996.
- **This XML transcription**: Bill MacCartney (`wcmac@cs.stanford.edu`),
  346 problems. Its own intro comment states: "If you benefit from my
  work, please give me appropriate credit" — public domain with credit
  requested, per his downloads page.
- **Canonical location**: `nlp.stanford.edu/~wcmac/downloads/fracas.xml`
  — unreachable from the sandboxed session that built the rest of this
  scaffold (network policy blocks that host; see the repo README's
  history).
- **Actually fetched from**: a byte-identical mirror at
  `raw.githubusercontent.com/kovvalsky/LangPro/master/FraCaS_dataset/fracas.xml`
  (LangPro is Kovvalsky & Moot's published NLI system; the file matches
  MacCartney's own description exactly — 346 `<problem>` entries, answer
  distribution 203 yes / 33 no / 98 unknown / 12 undef, matching the
  file's own header claims), fetched 2026-09-25. Verify against the
  canonical URL directly if you have network access to it and want to
  confirm the mirror hasn't drifted — it shouldn't have; this file hasn't
  changed since MacCartney published it.
- **Not modified**: `fracas.xml` here is the file as fetched, byte for
  byte. Don't hand-edit it; write a separate parser/transcription step
  (see `FraCaS/Types.lean`) instead, so provenance stays traceable.

## Schema (from the file's own DTD comment)

Each `<problem id="NNN" fracas_answer="yes|no|unknown|undef">` has one or
more `<p idx="k">` premises, a `<q>` (the original question form,
informational only), an `<h>` (MacCartney's declarative hypothesis —
this is what `FraCaS.Problem.hypothesis` should hold, not `<q>`), and an
`<a>` (free-text answer). Four problems (276, 305, 309, 310) have no `<h>`
per the file's own intro comment; skip them rather than force-fitting.
`fracas_nonstandard="true"` marks 41 problems whose source answer wasn't
literally "Yes"/"No"/"Don't know".
