#!/usr/bin/env bash
# Regenerates every file written from the guest, in dependency order, after a change to the guest
# (`crates/rec_aggregation/guests/`), to its compiler, or to `formal/leanvm-rev`:
#
#   scripts/regen-guest.sh            # write
#   scripts/regen-guest.sh --check    # write nothing, fail on the first stale file (as check-all.sh does)
#
# Run from anywhere; it works in lean_vm. Each step's generator reads only what the steps before it
# wrote, so a step that fails names what to fix before the rest can run. Not regenerated here:
# `LeanVM/Guest/B1/Tables/Vt/*T.lean` (`scripts/b1c-vt`, by hand from its own dump) and the
# verifier fixtures (`scripts/export-verifier-fixtures-rust.sh`, after a protocol change).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
check=()
[ "${1:-}" = --check ] && check=(--check)
step() { printf '\n==> [%dm%02ds] %s\n' $((SECONDS / 60)) $((SECONDS % 60)) "$*"; }
capped() { (ulimit -v "${LEAN_VMEM_KB:-40000000}"; exec "$@"); }

step "guest-export: bytecode, source, programs (from leanVM's sources)"
cargo build --release --manifest-path scripts/guest-export/Cargo.toml
capped scripts/guest-export/target/release/guest-export . "${check[@]}"

# The three Lean generators import the data the export wrote; each is built after the step before it.
for exe in guest-core guest-cert guest-memory; do
  step "$exe"
  lake build "$exe"
  capped ".lake/build/bin/$exe" "${check[@]}"
  if [ "$exe" = guest-core ]; then
    step "the names' modulus (CoreNames)"
    python3 -I scripts/core-names-modulus "${check[@]}"
  fi
done

step "count families (scripts/count)"
if [ ${#check[@]} -eq 0 ]; then
  python3 -I scripts/count/gen.py . all
  python3 -I scripts/count/vsos.py .
else
  echo "(checked by the build: a stale count module fails its decide +kernel)"
fi

step "decoder tables and their chunks"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
lake build LeanVM.Cost.Decoder.GuestTables LeanVM.Guest.Glob
capped lake env lean scripts/decoder-tables-inputs.lean > "$tmp/in.txt"
for k in entries rows split; do sed -n "s/^$k: //p" "$tmp/in.txt" > "$tmp/$k.txt"; done
python3 -I scripts/decoder-tables --entries "$tmp/entries.txt" "${check[@]}"
python3 -I scripts/decoder-table-chunks --row-lengths "$tmp/rows.txt" --split-lengths "$tmp/split.txt" "${check[@]}"

step "done: build with python3 -I ../lake-build.py . LeanVM LeanVMTests (or --dev while adapting proofs)"
