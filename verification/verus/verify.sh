#!/usr/bin/env bash
# Check the proofs with the pinned Verus release, installing it under $VERUS_HOME (default ~/.verus) if missing.
#
#     verification/verus/verify.sh                   # all modules, every configuration
#     verification/verus/verify.sh gf2_64            # one module (and the modules it uses), every configuration
#     VERUS_CONFIGS="portable neon" verification/verus/verify.sh   # some configurations
#
# The kernels pick their SIMD arm with `cfg(target_feature)`, so Verus sees one arm per build. Each configuration
# below is one build, with the flags of a CPU class production targets (the CI legs' flags): together they check
# every arm, the portable one included. The NEON ones are cross-checked from this host with `--target`.
set -euo pipefail

# The release, and the Rust toolchain it is built against (its `version.json`).
VERUS_RELEASE=0.2026.10.04.426d8b0
VERUS_TOOLCHAIN=1.98.1

# name | target triple | RUSTFLAGS
CONFIGS=(
  "portable|x86_64-unknown-linux-gnu|-C target-cpu=x86-64"
  "haswell|x86_64-unknown-linux-gnu|-C target-cpu=haswell"
  "avx2-vpclmulqdq|x86_64-unknown-linux-gnu|-C target-cpu=x86-64-v3 -C target-feature=+vpclmulqdq,+pclmulqdq"
  "avx2-gfni|x86_64-unknown-linux-gnu|-C target-cpu=x86-64-v3 -C target-feature=+gfni,+vpclmulqdq,+pclmulqdq,+aes"
  "avx512|x86_64-unknown-linux-gnu|-C target-cpu=x86-64-v4 -C target-feature=+avx512vbmi,+vpclmulqdq,+pclmulqdq,+gfni,+aes"
  "neon|aarch64-unknown-linux-gnu|-C target-cpu=neoverse-n2 -C target-feature=+aes,+sha3"
  "neon-no-sha3|aarch64-unknown-linux-gnu|-C target-feature=+aes"
)

home="${VERUS_HOME:-$HOME/.verus}/verus-$VERUS_RELEASE"
if [ ! -x "$home/verus-x86-linux/verus" ]; then
  mkdir -p "$home"
  curl -fsSL -o "$home/verus.zip" \
    "https://github.com/verus-lang/verus/releases/download/release/$VERUS_RELEASE/verus-$VERUS_RELEASE-x86-linux.zip"
  unzip -q "$home/verus.zip" -d "$home"
  rm "$home/verus.zip"
fi
rustup toolchain install "$VERUS_TOOLCHAIN" --profile minimal --no-self-update >/dev/null 2>&1
rustup target add --toolchain "$VERUS_TOOLCHAIN" aarch64-unknown-linux-gnu >/dev/null 2>&1
export PATH="$home/verus-x86-linux:$PATH"

cd "$(dirname "$0")"
threads=(--num-threads "${VERUS_THREADS:-4}")
selected="${VERUS_CONFIGS:-}"
target_root="${CARGO_TARGET_DIR:-target/verus}"
# `cargo verus focus` can replay a cached root-package result with different forwarded module arguments.
# Keep each requested module separate from other focus queries and from the whole-crate proof.
scope=all
if [ $# -gt 0 ]; then
  scope="focus/$1"
fi
for config in "${CONFIGS[@]}"; do
  IFS='|' read -r name triple flags <<<"$config"
  if [ -n "$selected" ] && [[ " $selected " != *" $name "* ]]; then
    continue
  fi
  echo "== $name ($flags)"
  # Isolate the ISA flags and proof selection, while reusing each selection's dependency cache.
  export RUSTFLAGS="$flags" CARGO_TARGET_DIR="$target_root/$name/$scope"
  if [ $# -gt 0 ]; then
    cargo verus focus --target "$triple" -- "${threads[@]}" --verify-module "$1"
  else
    cargo verus verify --target "$triple" -- "${threads[@]}"
  fi
done
