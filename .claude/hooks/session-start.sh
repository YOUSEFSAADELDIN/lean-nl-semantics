#!/bin/bash
# Builds a local GF/RGL toolchain so gf/run_gf_tests.py and gf/translate.py
# can be checked directly in this session, instead of only via a CI push
# (see .github/workflows/build.yml's own build-gf job, which this mirrors).
#
# Only worth doing in a remote/web session (a fresh container with no
# toolchain already installed) - a local Claude Code session on a
# contributor's own machine either already has one set up or should set
# it up their own way.
set -euo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

GF_CORE_COMMIT="378bfe691041878ca9fadd4697f1e58dc1620931"
GF_RGL_TAG="20260403"
GF_LIBS_DIR="$HOME/gf-libs"
WORK_DIR="$HOME/.cache/gf-toolchain"

mkdir -p "$HOME/.local/bin" "$WORK_DIR"

# cabal's secure-repository (TUF) signature check fails against
# hackage.haskell.org through this environment's egress proxy - plain
# package downloads work fine once it's disabled. Idempotent: only
# rewritten if not already set this way.
mkdir -p "$HOME/.cabal"
if ! grep -q "secure: False" "$HOME/.cabal/config" 2>/dev/null; then
  cat > "$HOME/.cabal/config" <<'CABALCFG'
repository hackage.haskell.org
  url: http://hackage.haskell.org/
  secure: False
CABALCFG
fi

# 1. Build gf-core (the `gf` binary itself) if not already present.
if ! "$HOME/.local/bin/gf" --version >/dev/null 2>&1; then
  rm -rf "$WORK_DIR/gf-core"
  git clone --quiet https://github.com/GrammaticalFramework/gf-core.git "$WORK_DIR/gf-core"
  (cd "$WORK_DIR/gf-core" && git checkout --quiet "$GF_CORE_COMMIT")
  cabal update
  (cd "$WORK_DIR/gf-core" && cabal install --installdir="$HOME/.local/bin" --install-method=copy --overwrite-policy=always)
fi

export PATH="$HOME/.local/bin:$PATH"

# 2. Build gf-rgl (the resource grammar library - every language, not
# just English; Setup.sh's own design, not this script's) if not
# already present.
if [ ! -d "$GF_LIBS_DIR/alltenses" ]; then
  rm -rf "$WORK_DIR/gf-rgl"
  git clone --quiet https://github.com/GrammaticalFramework/gf-rgl.git "$WORK_DIR/gf-rgl"
  (cd "$WORK_DIR/gf-rgl" && git checkout --quiet "$GF_RGL_TAG" && ./Setup.sh --dest="$GF_LIBS_DIR")
fi

# 3. Build DictEngAbs/DictEng (the RGL's general English dictionary,
# used by gf/FraCaSLogic.gf) - deliberately NOT part of Setup.sh's own
# build output, see gf/FraCaSLogic.gf's own comment on why.
if [ ! -f "$GF_LIBS_DIR/alltenses/DictEngAbs.gfo" ]; then
  (cd "$WORK_DIR/gf-rgl" && gf --batch --quiet --gf-lib-path="$GF_LIBS_DIR" \
    --no-pmcfg --gfo-dir="$GF_LIBS_DIR/alltenses" \
    src/english/DictEngAbs.gf src/english/DictEng.gf)
fi

# Persist for the rest of the session: gf/run_gf_tests.py itself reads
# GF_LIB_PATH (defaulting to ~/gf-libs, so this is only needed if a
# future change ever moves GF_LIBS_DIR), and every gf/translate.py or
# manual `gf -make ... FraCaSLogicEng.gf` invocation needs `gf` on PATH.
echo "export PATH=\"$HOME/.local/bin:\$PATH\"" >> "$CLAUDE_ENV_FILE"
echo "export GF_LIB_PATH=\"$GF_LIBS_DIR\"" >> "$CLAUDE_ENV_FILE"
