#!/bin/sh
# Build every guest and refresh the ELF files the host's tests load (guests/elf/).
# Needs a nightly toolchain with rust-src, which rust-toolchain.toml asks rustup for.
set -e
cd "$(dirname "$0")"
cargo build --release
for guest in fibonacci blake2s hash numbers preimage; do
  cp "target/riscv64im-unknown-none-elf/release/$guest" "elf/$guest.elf"
done
