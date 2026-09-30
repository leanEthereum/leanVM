#!/bin/sh
# Build every guest and refresh its checked-in ELF file (programs/<name>/<name>.elf), which the tests load.
# Each guest is its own workspace, with its own toolchain file (nightly with rust-src) and cargo config;
# they share one target directory, so `core` and the runtime (sdk/) are built once.
set -e
cd "$(dirname "$0")"
for guest in */guest; do
  name=${guest%/guest}
  (cd "$guest" && cargo build --release --target-dir ../../target)
  cp "target/riscv64im-unknown-none-elf/release/$name" "$name/$name.elf"
done
