#!/usr/bin/env bash
# Regenerate the block specifications of the image's functions (`Rv64Verifier/Blocks/F<index>.lean`) with
# `lake exe rv64-gen`. With no argument, the files already present (those the proofs import); with `--all`, every
# function; with `--check`, fail if a present file differs from what the generator writes now.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build rv64-gen >/dev/null
mode=${1:-}
n=$(grep -c '^  ("' Rv64Verifier/Image.lean)
status=0
for i in $(seq 0 $((n - 1))); do
  out=Rv64Verifier/Blocks/F$i.lean
  if [ "$mode" != --all ] && [ ! -f "$out" ]; then continue; fi
  if [ "$mode" = --check ]; then
    tmp=$(mktemp)
    .lake/build/bin/rv64-gen "$i" "$tmp" >/dev/null
    sed -i.bak "s/^namespace Rv64Verifier.Blocks\..*/namespace Rv64Verifier.Blocks.F$i/; s/^end Rv64Verifier.Blocks\..*/end Rv64Verifier.Blocks.F$i/" "$tmp"
    cmp -s "$tmp" "$out" || { echo "stale: $out"; status=1; }
    rm -f "$tmp" "$tmp.bak"
  else
    .lake/build/bin/rv64-gen "$i" "$out" >/dev/null
  fi
done
exit $status
