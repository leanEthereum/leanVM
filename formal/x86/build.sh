#!/usr/bin/env bash
# Builds the binary the x86 proofs are about, `fv_entry` for AVX2 with VPCLMULQDQ and GFNI (the stable prover's x86 lanes
# need both; without them it runs several times slower), at target/fv/fv_entry, on an x86-64 Linux host with a nightly
# toolchain and its `rust-src`. Panics abort at once (no unwinding, no formatting); no auto-vectorization or
# unrolling, so the binary's loops are the source's; static addresses, so a table of function pointers holds the
# functions' addresses; libc called through the PLT, so those calls are direct; no tracing spans; built for size
# but the crates whose speed it needs (the field lanes, the Keccak permutation and GKR, the transcript, the pool).
set -euo pipefail
cd "$(dirname "$0")/../.."

flags=(
  -C target-cpu=haswell -C target-feature=+vpclmulqdq,+gfni
  -C relocation-model=static -C link-arg=-no-pie -Z plt=yes
  -Z unstable-options -C panic=immediate-abort -C force-unwind-tables=no
  -C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false
  -C llvm-args=-unroll-threshold=0 -C llvm-args=-unroll-full-max-count=1
)
small=()
for crate in verifier aggregation isa claims lean_xmss lean_sphincs lean_da fv_entry stable_lean_vm_core stable_pcs; do
  small+=(--config "profile.release.package.$crate.opt-level=\"s\"")
done
RUSTFLAGS="${flags[*]}" CARGO_PROFILE_RELEASE_LTO=fat \
  cargo +nightly build --release -p fv_entry --bin fv_entry --features fv "${small[@]}" \
  --target x86_64-unknown-linux-gnu -Z build-std=std,panic_abort --target-dir target/fv-build
mkdir -p target/fv
cp target/fv-build/x86_64-unknown-linux-gnu/release/fv_entry target/fv/fv_entry
