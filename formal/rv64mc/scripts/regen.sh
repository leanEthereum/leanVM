#!/usr/bin/env bash
# Builds the guest from scratch, lifts it with machine-checked's `decompile --to lean --proved` and writes Rv64mc/Gen
# with gen.py, then prints which templates changed.
#
#   scripts/regen.sh [--check] [--elf ELF]
#
# The guest is built in a fresh directory under out/ (a copy of guest/'s sources and config, the no_std copy of
# $VERIFIER_SRC, default crates/verifier, and an empty target dir), removed afterwards, so the ELF is a function of the
# sources and the config alone. Its sha256 is written to image.sha256 and the ELF to out/canon.elf and out/gen.elf
# (the one Words.lean's check reads).
# --check writes nothing and exits 1 if the ELF's sha256 is not image.sha256's or a generated file would change.
# --elf takes an ELF already built instead (it must be linked as guest/build.rs links it); image.sha256 and
# out/canon.elf are then left alone.
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
mkdir -p "$here/out"
tmp=$(mktemp -d "$here/out/regen.XXXXXX")
trap 'rm -rf "${tmp:?}"' EXIT
built=0
if [ -z "$elf" ]; then
  b=$tmp/guest
  mkdir -p "$b"
  (cd "$here/guest" && cp -r .cargo Cargo.toml Cargo.lock build.rs link.x rust-toolchain.toml src "$b/")
  "$here/scripts/nostd-verifier.sh" "$b/verifier-nostd" >/dev/null
  # The guest's own rustflags and no others: Cargo merges `target.<cfg>.rustflags` from every config above the build
  # directory and from CARGO_HOME (the repository's adds `-C target-cpu=native`, which changes the code), and the
  # environment variable replaces them all.
  flags=$(python3 -I -c 'import sys, tomllib
c = tomllib.load(open(sys.argv[1], "rb"))
print("\x1f".join(c["target"]["riscv64im-unknown-none-elf"]["rustflags"]))' "$b/.cargo/config.toml")
  (cd "$b" && CARGO_ENCODED_RUSTFLAGS=$flags CARGO_TARGET_DIR=$b/target timeout 1800 cargo build --release 2>&1 | tail -1)
  elf=$tmp/verifier-rv64
  cp "$b/target/riscv64im-unknown-none-elf/release/verifier-rv64" "$elf"
  rm -rf "${b:?}"
  built=1
fi
python3 -I "$here/scripts/check-relocs.py" "$elf"
sha=$(sha256sum "$elf" | cut -d' ' -f1)
echo "image sha256 $sha"
timeout 600 "$decompile" --to lean --proved "$elf" "$tmp/mc" Img >/dev/null
cd "$here"
if [ $check = 1 ]; then
  status=0
  if [ $built = 1 ] && [ "$sha" != "$(cut -d' ' -f1 image.sha256)" ]; then
    echo "the image's sha256 is not image.sha256's ($(cut -d' ' -f1 image.sha256))"
    status=1
  fi
  cmp -s "$elf" out/gen.elf || { echo "out/gen.elf would change"; status=1; }
  python3 -I scripts/gen.py --elf "$elf" --mc "$tmp/mc/Img" --check || status=1
  exit $status
fi
[ -f Rv64mc/Gen/hashes.tsv ] && cp Rv64mc/Gen/hashes.tsv "$tmp/old-hashes.tsv" || : > "$tmp/old-hashes.tsv"
cp "$elf" out/gen.elf
if [ $built = 1 ]; then
  cp "$elf" out/canon.elf
  echo "$sha  verifier-rv64" > image.sha256
fi
python3 -I scripts/gen.py --elf out/gen.elf --mc "$tmp/mc/Img"
python3 -I scripts/gen.py --diff "$tmp/old-hashes.tsv" Rv64mc/Gen/hashes.tsv
