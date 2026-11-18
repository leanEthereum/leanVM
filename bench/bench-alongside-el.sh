#!/usr/bin/env bash
# The 16-to-1 recursion of bench.sh, at 4 threads, while an execution client's load runs alongside it: el-load
# validates mainnet blocks as a stateless reth node does (bench/el-load), a slot's worth of gas per slot over 4 workers.
# One run per core configuration below; prints the proving time and the execution client's slot times for each.
# Usage: [EL_GAS_PER_SLOT=200000000] [EL_SLOT_MS=12000] [EL_DB=.build/el-load.db] [EL_DB_GIB=16] [EL_DB_MISS=1]
#        bench/bench-alongside-el.sh [stable|experimental] [log file]
# EL_SLOT_MS=0 runs the slots back to back, so the execution client works throughout the proofs. Each block also does a
# node's database I/O on EL_DB (written once, EL_DB_GIB GiB), its cache missing an EL_DB_MISS share of the accounts and
# slots the block touches; EL_DB= leaves the database out.
set -uo pipefail

PROVER=${1:-experimental}
cd "$(dirname "$0")/.."
mkdir -p .build
LOG="${2:-$PWD/.build/bench-alongside-el-$(date +%Y%m%d-%H%M%S).log}"
GAS=${EL_GAS_PER_SLOT:-200000000}
SLOT_MS=${EL_SLOT_MS:-12000}
DB=${EL_DB-$PWD/.build/el-load.db}
DB_ARGS=()
[ -n "$DB" ] && DB_ARGS=(--db "$DB" --db-gib "${EL_DB_GIB:-16}" --db-miss "${EL_DB_MISS:-1}")
TARGET=${CARGO_TARGET_DIR:-target}
OUT=$(mktemp)
EL_OUT=$(mktemp)
RESULTS=$(mktemp)
EL_PID=
trap 'rm -f "$OUT" "$EL_OUT" "$RESULTS"; [ -n "$EL_PID" ] && kill "$EL_PID" 2>/dev/null' EXIT

cargo build --release -p leanvm-bench || exit 1
cargo build --release --manifest-path bench/el-load/Cargo.toml || exit 1
EL=bench/el-load/target/release/el-load
"$EL" check bench/el-load/fixtures | tee -a "$LOG" || exit 1
# The database file is written on first use; written and flushed here, it disturbs no measurement.
if [ -n "$DB" ]; then "$EL" run bench/el-load/fixtures --slots 1 --slot-ms 0 "${DB_ARGS[@]}" >/dev/null && sync; fi

# Expands a kernel CPU list ("0-3,8") into one CPU per word.
cpus() { local part; for part in ${1//,/ }; do seq "${part%-*}" "${part#*-}"; done | tr '\n' ' '; }
# The first $2 CPUs of a list, comma separated.
take() { echo $1 | tr ' ' '\n' | head -n "$2" | paste -sd, -; }
# The next $2 after the first $3.
skip_take() { echo $1 | tr ' ' '\n' | tail -n +$(($3 + 1)) | head -n "$2" | paste -sd, -; }

# Performance and efficiency cores on a hybrid Intel CPU; elsewhere every CPU counts as a performance one.
P=$(cpus "$(cat /sys/devices/cpu_core/cpus 2>/dev/null || cat /sys/devices/system/cpu/online)")
E=$(cpus "$(cat /sys/devices/cpu_atom/cpus 2>/dev/null || true)")
echo "performance CPUs: $P; efficiency CPUs: ${E:-none}; $GAS gas per slot, slots of $SLOT_MS ms; database: ${DB:-none}" | tee -a "$LOG"

# name | leanVM's CPUs | the execution client's CPUs ("" for none, "any" for unpinned)
CONFIGS=(
  "leanVM alone, 4 P|$(take "$P" 4)|"
  "leanVM alone, unpinned|any|"
  "both unpinned|any|any"
  "4 P leanVM, 4 P EL|$(take "$P" 4)|$(skip_take "$P" 4 4)"
  "4 P leanVM, EL unpinned|$(take "$P" 4)|any"
)
[ -n "$E" ] && CONFIGS+=(
  "4 P leanVM, 4 E EL|$(take "$P" 4)|$(take "$E" 4)"
  "4 E leanVM, 4 P EL|$(take "$E" 4)|$(take "$P" 4)"
  "leanVM unpinned, 4 E EL|any|$(take "$E" 4)"
)

# The prefix that pins a command to CPUs, none for "any". taskset execs the command, so `$!` is the command's own PID.
on() { [ "$1" = any ] || echo "taskset -c $1"; }

for config in "${CONFIGS[@]}"; do
  IFS='|' read -r name lean el <<<"$config"
  echo "=== $name: leanVM on ${lean}, EL on ${el:-nothing} ===" | tee -a "$LOG"
  EL_PID=
  : >"$EL_OUT"
  if [ -n "$el" ]; then
    $(on "$el") "$EL" run bench/el-load/fixtures --gas-per-slot "$GAS" --slot-ms "$SLOT_MS" --workers 4 "${DB_ARGS[@]}" >"$EL_OUT" &
    EL_PID=$!
  fi
  $(on "$lean") "$TARGET/release/leanvm-bench" --prover "$PROVER" recursion --n 16 --xmss-per-leaf 1400 \
    --leaf-log-inv-rate 2 --log-inv-rate 1 --repeat 3 --threads 4 --cooldown 5 2>&1 | tee "$OUT" | tee -a "$LOG"
  [ -n "$EL_PID" ] && kill "$EL_PID" && wait "$EL_PID" 2>/dev/null
  cat "$EL_OUT" >>"$LOG"
  time=$(grep -E 'proving time +:' "$OUT" | tail -1 | sed 's/^[^:]*://' | grep -oE '[0-9.,]+ s( ± [0-9.]+%)?' | head -1)
  slots=$(grep -oE 'in [0-9.]+ ms' "$EL_OUT" | awk '{print $2}' | sort -n |
    awk '{v[NR] = $1} END {if (NR) printf "%d slots, median %.0f ms, max %.0f ms", NR, v[int((NR + 1) / 2)], v[NR]; else printf "none"}')
  printf '| %s | %s | %s |\n' "$name" "${time:-failed}" "$slots" >>"$RESULTS"
  echo | tee -a "$LOG"
done

{
  echo "| configuration | 16-to-1 proving time ($PROVER, 4 threads) | EL slots ($GAS gas, 4 workers) |"
  echo "| --- | --- | --- |"
  cat "$RESULTS"
} | tee -a "$LOG"
echo "Full output: $LOG"
