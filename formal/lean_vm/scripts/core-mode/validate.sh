#!/usr/bin/env bash
# The core-mode residuals checked on honest executions: a regression check of their truth, not a proof.
#
# usage (from formal/lean_vm, CORE_MODE_CACHE set as for infer.py): scripts/core-mode/validate.sh DIR [--keep]
#
# Makes 17 executions with the stable executor's `DBG_JUMP_DUMP` (the guest-export cases: leaves and nodes with
# leanXMSS, leanSPHINCS and blobs at rate 1; and the CLI's recursion at leaf rates 2 to 4) into DIR (reused when
# DIR already holds them), then runs `validate.py --emit` (every residual of every emitted certificate, `emitc.py`'s
# features, in `CRes.Holds`'s semantics) and `validate.py --all` (every residual of the inference, all features).
# Exits nonzero if either finds a false residual. About 10 min cold (two release builds), 6 min warm; DIR needs
# about 1 GB.
set -euo pipefail
dir=${1:?usage: validate.sh DIR}
here=$(cd "$(dirname "$0")" && pwd)
lean_vm=$(cd "$here/../.." && pwd)
root=$(cd "$lean_vm/../.." && pwd)
mkdir -p "$dir"
dir=$(cd "$dir" && pwd)
if ! ls "$dir"/run.*.jumps > /dev/null 2>&1; then
  (cd "$lean_vm" && LEANVM_DIR="$root" LEANVM_EXEC_BENCH=1 DBG_JUMP_DUMP="$dir/run" LEANVM_GUEST_DIFF="$dir/diff" \
    LEANVM_GUEST_EXEC="$dir/exec" cargo test --release --manifest-path scripts/guest-export/Cargo.toml --lib \
    guest_diff -- --ignored)
fi
if ! ls "$dir"/c3.*.jumps > /dev/null 2>&1; then
  cd "$root"
  cargo build --release -p leanvm-cli
  DBG_JUMP_DUMP="$dir/c1" cargo leanvm --prover stable recursion --n 2 --xmss-per-leaf 30 --sphincs-per-leaf 3 \
    --blobs-per-leaf 2 --leaf-log-inv-rate 2
  DBG_JUMP_DUMP="$dir/c2" cargo leanvm --prover stable recursion --n 3 --xmss-per-leaf 10 --leaf-log-inv-rate 3
  DBG_JUMP_DUMP="$dir/c3" cargo leanvm --prover stable recursion --n 2 --xmss-per-leaf 0 --blobs-per-leaf 4 \
    --leaf-log-inv-rate 4
fi
cd "$lean_vm"
rc=0
python3 -I scripts/core-mode/validate.py --emit "$dir/*.jumps" || rc=1
python3 -I scripts/core-mode/validate.py --all "$dir/*.jumps" || rc=1
exit $rc
