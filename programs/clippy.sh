#!/bin/sh
# Lint each standalone guest with its RISC-V toolchain and target configuration.
set -eu
cd "$(dirname "$0")"
for guest in */guest; do
  # recverify builds std for its own target with a pinned nightly (recverify/README.md).
  [ "$guest" = recverify/guest ] && continue
  (cd "$guest" && cargo clippy --release --locked --target-dir ../../target -- -D warnings)
done
