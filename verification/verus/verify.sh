#!/usr/bin/env bash
# Check the proofs with the pinned Verus release, installing it under $VERUS_HOME (default ~/.verus) if missing.
#
#     verification/verus/verify.sh            # all modules
#     verification/verus/verify.sh gf2_64     # one module (and the modules it uses)
set -euo pipefail

# The release, and the Rust toolchain it is built against (its `version.json`).
VERUS_RELEASE=0.2026.10.04.426d8b0
VERUS_TOOLCHAIN=1.98.1

home="${VERUS_HOME:-$HOME/.verus}/verus-$VERUS_RELEASE"
if [ ! -x "$home/verus-x86-linux/verus" ]; then
  mkdir -p "$home"
  curl -fsSL -o "$home/verus.zip" \
    "https://github.com/verus-lang/verus/releases/download/release/$VERUS_RELEASE/verus-$VERUS_RELEASE-x86-linux.zip"
  unzip -q "$home/verus.zip" -d "$home"
  rm "$home/verus.zip"
fi
rustup toolchain install "$VERUS_TOOLCHAIN" --profile minimal --no-self-update >/dev/null 2>&1
export PATH="$home/verus-x86-linux:$PATH"

cd "$(dirname "$0")"
threads=(--num-threads "${VERUS_THREADS:-4}")
if [ $# -gt 0 ]; then
  cargo verus focus -- "${threads[@]}" --verify-module "$1"
else
  cargo verus verify -- "${threads[@]}"
fi
