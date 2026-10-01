#!/bin/sh
# Lint each standalone guest with its RISC-V toolchain and target configuration.
set -eu
cd "$(dirname "$0")"
for guest in */guest; do
  (cd "$guest" && cargo clippy --release --locked --target-dir ../../target -- -D warnings)
done
