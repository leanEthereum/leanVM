#!/usr/bin/env bash
# Builds the guest against a copy of crates/verifier at $1 (default: crates/verifier) and copies the ELF to $2.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
VERIFIER_SRC=${1:-$root/crates/verifier} "$here/nostd-verifier.sh" >/dev/null
cd "$here/../guest"
timeout 1800 cargo build --release 2>&1 | grep -v "is not a recognized" | tail -3
cp target/riscv64im-unknown-none-elf/release/verifier-rv64 "$2"
