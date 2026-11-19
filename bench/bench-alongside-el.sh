#!/usr/bin/env bash
# The 16-to-1 recursion of bench.sh, 5 times on 4 cores, while an execution client (bench/el-load) validates mainnet
# blocks without pause on 4 others. Pick one CPU per physical core, of the same kind (performance cores on a hybrid CPU).
# Usage: [LEAN_CPUS=0-3] [EL_CPUS=4-7] bench/bench-alongside-el.sh [stable|experimental]
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .build
EL_LOG=.build/el-load.log

cargo build --release -p leanvm-bench
cargo build --release --manifest-path bench/el-load/Cargo.toml

# The execution client, once it has validated each block (and written its database file, on the first run).
taskset -c "${EL_CPUS:-4-7}" bench/el-load/target/release/el-load bench/el-load/fixtures .build/el-load.db >"$EL_LOG" &
EL=$!
trap 'kill $EL 2>/dev/null' EXIT
until grep -q Mgas/s "$EL_LOG"; do kill -0 $EL || exit 1; sleep 1; done

taskset -c "${LEAN_CPUS:-0-3}" "${CARGO_TARGET_DIR:-target}"/release/leanvm-bench --prover "${1:-experimental}" recursion \
  --n 16 --xmss-per-leaf 1400 --leaf-log-inv-rate 2 --log-inv-rate 1 --repeat 5 --threads 4
echo "execution client meanwhile: $(tail -n 1 "$EL_LOG")"
