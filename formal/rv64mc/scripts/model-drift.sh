#!/usr/bin/env bash
# Fails when a Rust file that `Rv64mc/Model/` mirrors has changed since the commit `Rv64mc/Model.lean`
# names. After a change: bring the mirror (and its proof) in step with the new Rust, then update the
# pinned commit in `Model.lean` and the hashes below (`model-drift.sh --print` prints them).
set -euo pipefail

root="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$root"

# sha256 of each mirrored file, at the pinned commit.
pinned='
763e6c35e086f64eb7a3aed24c3f12f44dfbc4e0722baec65eb27fb6670ae5e4  crates/verifier/src/field.rs
818b6f50e654bc49002351c26b2b9cfdb264fc5bb8acbc33e478b4e78428d3e4  crates/verifier/src/multilinear.rs
c277f6a003acd68235efae8425009051970c10a2ff71badfbd9cdae8d2848486  crates/verifier/src/hash.rs
02403bf41c1159523ad2f2a600a811f2eeafea06ce3da8601b999b5f33c41a64  crates/verifier/src/merkle.rs
f9961452b7fa2a73a063624fb6ee12d9f88f6132a328d2ed58a19c78d5f65ca7  crates/verifier/src/transcript.rs
'

if [ "${1:-}" = "--print" ]; then
  printf '%s\n' "$pinned" | awk 'NF == 2 { print $2 }' | xargs sha256sum
  exit 0
fi

if printf '%s\n' "$pinned" | sed '/^$/d' | sha256sum --check --quiet; then
  echo "model-drift: the mirrored Rust files are as pinned"
else
  echo "model-drift: a mirrored Rust file changed; update its mirror, then the pin" >&2
  exit 1
fi
