#!/usr/bin/env bash
# Benchmark `lean_sphincs::verify` across compiler flags against the proved assembly `sphincs_verify`.
# Runs on native Linux x86-64 or AArch64, verifying only accepted signatures (8 distinct keys/messages).
#
# Usage:
#   formal/native/run/bench-sphincs.sh
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project=$(dirname "$here")
root=$(cd "$project/../.." && pwd)

if [[ -z ${RUSTUP_TOOLCHAIN:-} && -f "$project/rustc/rust-toolchain.toml" ]]; then
  RUSTUP_TOOLCHAIN=$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$project/rustc/rust-toolchain.toml")
  export RUSTUP_TOOLCHAIN
fi

arch=$(uname -m)
case $arch in
  x86_64)
    asm=$project/rustc/asm/signatures-x86_64.s
    bindings_flags=(-C target-cpu=x86-64 -C target-feature=+avx2,+pclmulqdq)
    baseline_flags=(-C target-cpu=x86-64)
    nosimd_flags=(-C target-cpu=x86-64 -C target-feature=-sse,-sse2)
    ;;
  aarch64 | arm64)
    asm=$project/rustc/asm/signatures-aarch64.s
    bindings_flags=(-C target-cpu=generic)
    baseline_flags=(-C target-cpu=generic)
    nosimd_flags=(-C target-cpu=generic -C target-feature=-neon)
    ;;
  *)
    echo "unsupported host architecture: $arch" >&2
    exit 2
    ;;
esac

out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
objcopy=$(clang --print-prog-name=llvm-objcopy)

echo "host: $arch ($(rustc --version))"
echo "asm:  $asm"
echo

build_rust() {
  local name=$1; shift
  local d=$out/$name
  mkdir -p "$d"
  rustc --edition 2024 -C opt-level=3 "$@" --crate-type rlib --crate-name keccak256 --cfg 'feature="std"' \
    -L dependency="$d" --out-dir "$d" "$root/crates/keccak256/src/lib.rs" 2>/dev/null
  rustc --edition 2024 -C opt-level=3 "$@" --crate-type rlib --crate-name lean_sphincs --cfg 'feature="std"' \
    --extern keccak256="$d/libkeccak256.rlib" -L dependency="$d" --out-dir "$d" "$root/crates/lean_sphincs/src/lib.rs" 2>/dev/null
  rustc --edition 2024 -C opt-level=3 --extern lean_sphincs="$d/liblean_sphincs.rlib" \
    -L dependency="$d" -o "$d/bench" "$here/bench_sphincs.rs"
  echo "[$name]"
  "$d/bench"
}

build_proved() {
  local name=$1; shift
  local d=$out/$name
  mkdir -p "$d"
  clang -c "$asm" -o "$d/sigs.o"
  "$objcopy" --keep-global-symbol=sphincs_verify "$d/sigs.o"
  cp "$out/bindings"/lib*.rlib "$d/"
  rustc --edition 2024 -C opt-level=3 "$@" --cfg 'feature="proved_asm"' \
    --extern lean_sphincs="$d/liblean_sphincs.rlib" -L dependency="$d" -C "link-arg=$d/sigs.o" \
    -o "$d/bench" "$here/bench_sphincs.rs"
  echo "[$name]"
  "$d/bench"
}

build_rust bindings "${bindings_flags[@]}"
build_rust native -C target-cpu=native
if [[ $arch == x86_64 ]]; then
  build_rust baseline_sse2 "${baseline_flags[@]}"
fi
build_rust no_simd "${nosimd_flags[@]}"
build_proved proved_asm_default
if [[ $arch == x86_64 ]]; then
  build_proved proved_asm_no_relax -C link-arg=-Wl,--no-relax
fi
