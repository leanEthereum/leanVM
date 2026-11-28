#!/usr/bin/env bash
# The deployed signature verifiers and the no_std leanVM verifier compiled by rustc to x86-64 and AArch64 assembly.
# `signatures.rs` exports `xmss_verify` and `sphincs_verify`; `vm/src/lib.rs` exports `leanvm_verify`.
# `run/check.sh` links the output, byte for byte the same in every checkout.
#
# Usage, from anywhere:
#   rustc/build.sh            # full asm/*.s, vm/asm/*.s and one SHA256SUMS
#   rustc/build.sh --check    # rebuilds twice and checks hashes and committed assembly
#
# Needs rustup with the toolchain of `rust-toolchain.toml` and the four targets below (`rustup target add`).
#
# Plain rustc, not cargo: cargo derives each crate's `-C metadata` (which every symbol name hashes) from the
# dependency's absolute path when it lies outside the workspace, as the deployed crates do here, and it would apply the
# repository's `.cargo/config.toml` (`target-cpu=native`). Here every crate's metadata is its name, every source path is
# relative to the repository, the sysroot and the output directory are remapped, nothing is incremental, and the
# target CPU is the baseline. Signatures use musl targets, the harness's libc; the VM uses no_std targets without SIMD.
# `-C lto=fat` on the static library with one codegen unit makes the assembly one module holding exactly what the
# export reaches. The no_std entry crate aborts on panic; `-C panic=abort` leaves out unwinding tables.
# `runtime.rs` supplies the required global allocator, trapping if the allocation-free verifier ever allocates.
#
# No SIMD or floating-point registers: the signature crates use `-neon` on AArch64 and `-sse,-sse2` on x86-64.
# The VM's targets already disable them. Kraken models general-purpose registers only. rustc warns that musl's ABI
# wants those features: no floating-point value crosses any function boundary here, so the ABI is not affected. The
# entry crate defines `memcpy` and `memset` itself (`mem.rs`), so the assembly holds every instruction a
# verification runs. The raw assembly is the artifact (`run/check.sh` assembles it): rustc's own object is not emitted, as
# rustc 1.99.1's object and assembly code generation differ under fat LTO.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../../.." && pwd)

RUSTUP_TOOLCHAIN=$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$here/rust-toolchain.toml")
export RUSTUP_TOOLCHAIN
unset RUSTC_BOOTSTRAP RUSTC_WRAPPER RUSTFLAGS

# Sources relative to the repository, copied into both reproducibility check trees.
sources=(crates/keccak256/src crates/lean_xmss/src crates/lean_sphincs/src formal/native/rustc/xmss.rs formal/native/rustc/sphincs.rs formal/native/rustc/mem.rs formal/native/rustc/runtime.rs formal/native/rustc/signatures.rs)

# build SRC OUT: writes the signatures assembly and its shared hashes.
build() {
  local src=$1 out=$2 deps sysroot program asm target arch cpu crate entry
  local targets flags arch_flags
  deps=$(mktemp -d)
  sysroot=$(rustc --print sysroot)
  for program in signatures; do
    asm=$out/asm crate=signatures entry=formal/native/rustc/signatures.rs
    targets=(x86_64-unknown-linux-musl aarch64-unknown-linux-musl)
    mkdir -p "$asm"
    for target in "${targets[@]}"; do
      arch=${target%%-*}
      arch_flags=()
      case $arch in
        # LLVM 23's `.prefalign` is unsupported by the harness's assembler.
        x86_64) cpu=x86-64 arch_flags=(-C llvm-args=-align-all-functions=4 -C target-feature=-sse,-sse2) ;;
        aarch64) cpu=generic arch_flags=(-C target-feature=-neon) ;;
      esac
      flags=(
        --edition 2024 --target "$target" -C target-cpu="$cpu"
        -C opt-level=3 -C codegen-units=1 -C panic=abort -C debuginfo=0 -C debug-assertions=no -C overflow-checks=no
        --remap-path-prefix="$src/=" --remap-path-prefix="$sysroot=/sysroot" --remap-path-prefix="$deps/=" --remap-path-prefix="$asm/="
        "${arch_flags[@]}"
      )
      (
        cd "$src"
        mkdir -p "$deps/$target"
        flags+=(-L dependency="$deps/$target" --out-dir "$deps/$target")
        rustc "${flags[@]}" --crate-type rlib --crate-name keccak256 -C metadata=keccak256 crates/keccak256/src/lib.rs
        for dependency in lean_xmss lean_sphincs; do
          rustc "${flags[@]}" --crate-type rlib --crate-name "$dependency" -C metadata="$dependency" \
            --extern keccak256="$deps/$target/libkeccak256.rlib" "crates/$dependency/src/lib.rs"
        done
        rustc "${flags[@]}" --crate-type staticlib --crate-name "$crate" -C metadata="$crate" -C lto=fat \
          --extern "lean_xmss=$deps/$target/liblean_xmss.rlib" \
          --extern "lean_sphincs=$deps/$target/liblean_sphincs.rlib" \
          --emit "link=$deps/$target/libsignatures.a,asm=$asm/signatures-$arch.s" "$entry"
      )
    done
  done
  rm -rf "$deps"
  (
    cd "$out"
    sha256sum asm/signatures-{aarch64,x86_64}.s
  ) >"$out/SHA256SUMS"
}

case ${1:-} in
  "")
    build "$root" "$here"
    cat "$here/SHA256SUMS"
    ;;
  --check)
    scratch=$(mktemp -d)
    trap 'rm -rf "$scratch"' EXIT
    status=0
    # Two checkouts at different depths, each with its own output directory.
    for tree in "$scratch/a" "$scratch/b/deeper/tree"; do
      for path in "${sources[@]}"; do
        mkdir -p "$(dirname "$tree/$path")"
        cp -R "$root/$path" "$tree/$path"
      done
      build "$tree" "$tree.artifacts"
      if diff "$here/SHA256SUMS" "$tree.artifacts/SHA256SUMS"; then
        echo "$tree: identical to SHA256SUMS"
      else
        echo "$tree: DIFFERS from SHA256SUMS" >&2
        status=1
      fi
      for asm in asm; do
        if ! diff -r "$here/$asm" "$tree.artifacts/$asm"; then
          echo "$tree/$asm: DIFFERS from committed assembly" >&2
          status=1
        fi
      done
    done
    exit $status
    ;;
  *)
    echo "usage: $0 [--check]" >&2
    exit 2
    ;;
esac
