#!/usr/bin/env bash
# The 16-to-1 recursion of bench.sh, 5 times in a row on 4 cores, while an execution client works without pause on 4
# others: el-load (bench/el-load) validates mainnet blocks as a stateless reth node does, with its database I/O, each of
# its 4 workers starting the next block as soon as it is done.
# Usage: [LEAN_CPUS=0,1,2,3] [EL_CPUS=4,5,6,7] bench/bench-alongside-el.sh [stable|experimental] [log file]
# By default leanVM gets the first 4 performance cores and the execution client the next 4, one thread per physical core.
set -euo pipefail

PROVER=${1:-experimental}
cd "$(dirname "$0")/.."
mkdir -p .build
LOG="${2:-$PWD/.build/bench-alongside-el-$(date +%Y%m%d-%H%M%S).log}"
EL=bench/el-load/target/release/el-load
DB=$PWD/.build/el-load.db

# 1. Prepare: build, check the blocks, write the database file (once), pick the cores.
cargo build --release -p leanvm-bench
cargo build --release --manifest-path bench/el-load/Cargo.toml
"$EL" check bench/el-load/fixtures | tee -a "$LOG"
"$EL" run bench/el-load/fixtures --slots 1 --slot-ms 0 --db "$DB" >/dev/null && sync

# The CPUs of a kernel CPU list ("0-3,8"), one per physical core.
cores() {
  local part cpu siblings
  for part in ${1//,/ }; do
    for cpu in $(seq "${part%-*}" "${part#*-}"); do
      siblings=$(cat "/sys/devices/system/cpu/cpu$cpu/topology/thread_siblings_list")
      if [ "${siblings%%[,-]*}" = "$cpu" ]; then echo "$cpu"; fi
    done
  done
}
P=($(cores "$(cat /sys/devices/cpu_core/cpus 2>/dev/null || cat /sys/devices/system/cpu/online)"))
[ ${#P[@]} -ge 8 ] || [ -n "${LEAN_CPUS:-}" -a -n "${EL_CPUS:-}" ] ||
  { echo "fewer than 8 performance cores: set LEAN_CPUS and EL_CPUS" >&2; exit 1; }
LEAN_CPUS=${LEAN_CPUS:-$(IFS=,; echo "${P[*]:0:4}")}
EL_CPUS=${EL_CPUS:-$(IFS=,; echo "${P[*]:4:4}")}
echo "leanVM on CPUs $LEAN_CPUS, the execution client on CPUs $EL_CPUS" | tee -a "$LOG"

# 2. The execution client, without pause on its cores.
EL_OUT=$(mktemp)
taskset -c "$EL_CPUS" "$EL" run bench/el-load/fixtures --slot-ms 0 --workers 4 --db "$DB" >"$EL_OUT" &
EL_PID=$!
trap 'kill $EL_PID 2>/dev/null; rm -f "$EL_OUT"' EXIT

# 3. The 16-to-1 recursion, 5 times, on leanVM's cores: its 16 leaves of 1400 leanXMSS are proven once, first.
taskset -c "$LEAN_CPUS" target/release/leanvm-bench --prover "$PROVER" recursion --n 16 --xmss-per-leaf 1400 \
  --leaf-log-inv-rate 2 --log-inv-rate 1 --repeat 5 --threads 4 2>&1 | tee -a "$LOG"

kill $EL_PID
awk '{gas += $3; ms += $6} END {if (ms) printf "execution client meanwhile: %d slots of 200M gas, %.0f Mgas/s\n", NR, gas / ms / 1e3}' \
  "$EL_OUT" | tee -a "$LOG"
echo "Full output: $LOG"
