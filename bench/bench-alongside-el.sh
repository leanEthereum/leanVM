#!/usr/bin/env bash
# Times leanVM's 16-to-1 aggregation (as in bench.sh) while an execution client runs on other cores.
#
# - leanVM: 4 cores, 4 threads, the 16-to-1 aggregation 5 times (its 16 leaves are proven once before, untimed).
# - Execution client (bench/el-load): the 4 other cores, validating mainnet blocks back to back as reth does, on 16
#   threads, so that while some wait for the disk the others keep the 4 cores busy.
# - Cores: 8 physical cores (EIP-7870's minimum; fewer is an error). With x performance cores among them, leanVM gets
#   ceil(x / 2) and the execution client the rest; efficiency cores fill each side up to 4.
# - macOS cannot pin a process to cores: there, both run with 4 threads each, wherever macOS puts them (16 threads
#   would take 16 cores).
#
# Usage: [LEAN_CPUS=0,1,2,3] [EL_CPUS=4,5,6,7] bench/bench-alongside-el.sh [stable|experimental]   (CPUs: Linux only)
set -euo pipefail

if [ "$(uname)" = Darwin ]; then
  P=$(sysctl -n hw.perflevel0.physicalcpu 2>/dev/null || sysctl -n hw.physicalcpu)
  E=$(sysctl -n hw.perflevel1.physicalcpu 2>/dev/null || echo 0)
  [ $((P + E)) -ge 8 ] || { echo "$((P + E)) physical cores, fewer than EIP-7870's 8" >&2; exit 1; }
  LEAN_PIN="" EL_PIN="" EL_THREADS=4
  echo "$P performance and $E efficiency cores; leanVM and the execution client unpinned"
else
  # One CPU per physical core, of those in a kernel CPU list ("0-3,8").
  cores() {
    local part
    lscpu -p=cpu,core,socket | grep -v '^#' | awk -F, '!seen[$2","$3]++ {print $1}' |
      grep -Fx -f <(for part in ${1//,/ }; do seq "${part%-*}" "${part#*-}"; done) || true
  }
  P=($(cores "$(cat /sys/devices/cpu_core/cpus 2>/dev/null || cat /sys/devices/system/cpu/online)"))
  E=($(cores "$(cat /sys/devices/cpu_atom/cpus 2>/dev/null || true)"))
  [ $((${#P[@]} + ${#E[@]})) -ge 8 ] ||
    { echo "$((${#P[@]} + ${#E[@]})) physical cores, fewer than EIP-7870's 8" >&2; exit 1; }
  X=$((${#P[@]} < 8 ? ${#P[@]} : 8))
  LP=$(((X + 1) / 2))
  LEAN=("${P[@]:0:LP}" "${E[@]:0:4-LP}")
  EL=("${P[@]:LP:X-LP}" "${E[@]:4-LP:4-X+LP}")
  LEAN_CPUS=${LEAN_CPUS:-$(IFS=,; echo "${LEAN[*]}")}
  EL_CPUS=${EL_CPUS:-$(IFS=,; echo "${EL[*]}")}
  LEAN_PIN="taskset -c $LEAN_CPUS" EL_PIN="taskset -c $EL_CPUS" EL_THREADS=16
  echo "leanVM on CPUs $LEAN_CPUS, the execution client on CPUs $EL_CPUS"
fi

cd "$(dirname "$0")/.."
mkdir -p .build
EL_LOG=.build/el-load.log

echo "==> 1/4 building leanvm-bench and el-load"
cargo build --release -p leanvm-bench
cargo build --release --manifest-path bench/el-load/Cargo.toml

echo "==> 2/4 starting the execution client: writing its 16 GiB database file (first run only), validating each block"
$EL_PIN bench/el-load/target/release/el-load bench/el-load/fixtures .build/el-load.db $EL_THREADS >"$EL_LOG" &
EL_PID=$!
trap 'kill $EL_PID 2>/dev/null' EXIT
until grep -q Mgas/s "$EL_LOG"; do kill -0 $EL_PID || exit 1; sleep 1; done
echo "    all $(grep -c valid "$EL_LOG") blocks valid; the execution client now runs without pause"

echo "==> 3/4 leanVM: proving the 16 leaves (untimed), then the 16-to-1 aggregation 5 times"
$LEAN_PIN "${CARGO_TARGET_DIR:-target}"/release/leanvm-bench --prover "${1:-experimental}" recursion \
  --n 16 --xmss-per-leaf 1400 --leaf-log-inv-rate 2 --log-inv-rate 1 --repeat 5 --threads 4
echo "==> 4/4 done; the execution client meanwhile: $(tail -n 1 "$EL_LOG")"
