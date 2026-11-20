#!/usr/bin/env bash
# Builds the guest, copies its ELF to out/gen.elf, lifts it with machine-checked's `decompile --to lean --proved` and
# writes Rv64mc/Gen with gen.py, then prints which templates changed.
#
#   scripts/regen.sh [--check] [--elf ELF]
#
# --check writes nothing (neither out/gen.elf nor Rv64mc/Gen) and exits 1 if a generated file would change.
# --elf takes an ELF already built instead of building the guest (it must be linked as guest/build.rs links it).
# DECOMPILE names the decompile binary (default: the pinned machine-checked's, built by `lake build decompile`).
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
check=0
elf=
while [ $# -gt 0 ]; do
  case $1 in
    --check) check=1 ;;
    --elf) elf=$(realpath "$2"); shift ;;
    *) echo "usage: $0 [--check] [--elf ELF]" >&2; exit 2 ;;
  esac
  shift
done
decompile=${DECOMPILE:-$here/.lake/packages/machine-checked/.lake/build/bin/decompile}
[ -x "$decompile" ] || { echo "no decompile at $decompile: run \`lake build decompile\` in $here or set DECOMPILE" >&2; exit 1; }
if [ -z "$elf" ]; then
  "$here/scripts/nostd-verifier.sh" >/dev/null
  (cd "$here/guest" && timeout 1800 cargo build --release 2>&1 | grep -v "is not a recognized" | tail -3)
  elf=$here/guest/target/riscv64im-unknown-none-elf/release/verifier-rv64
fi
python3 -I "$here/scripts/check-relocs.py" "$elf"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
timeout 600 "$decompile" --to lean --proved "$elf" "$tmp/mc" Img
cd "$here"
if [ $check = 1 ]; then
  cmp -s "$elf" out/gen.elf || echo "out/gen.elf would change"
  python3 -I scripts/gen.py --elf "$elf" --mc "$tmp/mc/Img" --check
  exit
fi
[ -f Rv64mc/Gen/hashes.tsv ] && cp Rv64mc/Gen/hashes.tsv "$tmp/old-hashes.tsv" || : > "$tmp/old-hashes.tsv"
mkdir -p out
cp "$elf" out/gen.elf
python3 -I scripts/gen.py --elf out/gen.elf --mc "$tmp/mc/Img"
python3 -I scripts/gen.py --diff "$tmp/old-hashes.tsv" Rv64mc/Gen/hashes.tsv
