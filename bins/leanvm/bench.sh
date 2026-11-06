#!/usr/bin/env bash
# Runs leanXMSS aggregation and 16-to-1 recursion at 4 and 8 threads and at the default pool ("full"), and prints a table of
# proving time and peak RSS per benchmark and thread count.
# Usage: [BENCH_THREADS="4 8 full"] bins/leanvm/bench.sh [log file]   (default: .build/bench-<timestamp>.log)
set -uo pipefail

cd "$(dirname "$0")/../.."
mkdir -p .build
LOG="${1:-$PWD/.build/bench-$(date +%Y%m%d-%H%M%S).log}"
RESULTS=$(mktemp)
OUT=$(mktemp)
trap 'rm -f "$RESULTS" "$OUT"' EXIT

# Proving time (mean and spread) and peak RSS of the proving process (for recursion, not its
# leaf subprocess), from the CLI's report line.
measure() {
  local line
  line=$(grep -E 'proving time +:' "$OUT" | tail -1)
  [ -z "$line" ] && { printf 'failed\tfailed'; return; }
  printf '%s\t%s' \
    "$(echo "$line" | sed 's/^[^:]*://' | grep -oE '[0-9.,]+ s( ± [0-9.]+%)?' | head -1)" \
    "$(echo "$line" | grep -oE 'peak memory [0-9.,]+' | awk '{gsub(/,/, "", $3); printf "%.2f GiB", $3}')"
}

run() {
  local label=$1 threads=$2; shift 2
  local pool=(env LEANVM_NUM_THREADS="$threads")
  [ "$threads" = full ] && pool=(env -u LEANVM_NUM_THREADS)
  echo "=== ${pool[*]:1} leanvm $* --cooldown 5 ===" | tee -a "$LOG"
  "${pool[@]}" "${CARGO_TARGET_DIR:-target}/release/leanvm" "$@" --cooldown 5 2>&1 | tee "$OUT" | tee -a "$LOG"
  printf '%s\t%s\t%s\n' "$label" "$threads" "$(measure)" >>"$RESULTS"
  echo | tee -a "$LOG"
}

read -ra THREADS <<<"${BENCH_THREADS:-4 8 full}"

cargo build --release -p leanvm-cli || exit 1

for t in "${THREADS[@]}"; do
  run "aggregate, 1500 leanXMSS, rate 2" "$t" aggregate --xmss 1500 --log-inv-rate 2 --repeat 3
done
for t in "${THREADS[@]}"; do
  run "recursion 16 to 1, 1500 leanXMSS/leaf, leaf rate 2, rate 1" "$t" \
    recursion --n 16 --xmss-per-leaf 1500 --leaf-log-inv-rate 2 --log-inv-rate 1 --repeat 3
done

# One row per benchmark, a time and a RAM column per thread count.
awk -F'\t' -v threads="${THREADS[*]}" '
  !($1 in seen) { seen[$1] = 1; rows[++n] = $1 }
  { t[$1, $2] = $3; m[$1, $2] = $4 }
  END {
    k = split(threads, th, " "); C = 1 + 2 * k
    cell[0, 1] = "benchmark"
    for (i = 1; i <= k; i++) { cell[0, 2 * i] = th[i] " threads: time"; cell[0, 2 * i + 1] = th[i] " threads: RAM" }
    for (r = 1; r <= n; r++) {
      b = rows[r]; cell[r, 1] = b
      for (i = 1; i <= k; i++) { cell[r, 2 * i] = t[b, th[i]]; cell[r, 2 * i + 1] = m[b, th[i]] }
    }
    for (r = 0; r <= n; r++) for (c = 1; c <= C; c++) {
      l = length(cell[r, c]); if (cell[r, c] ~ /±/) l -= length("±") - 1   # bytes in some awks
      len[r, c] = l; if (l > w[c]) w[c] = l
    }
    for (r = 0; r <= n; r++) {
      line = "|"
      for (c = 1; c <= C; c++) {
        pad = sprintf("%" (w[c] - len[r, c]) "s", "")
        line = line " " (c == 1 ? cell[r, c] pad : pad cell[r, c]) " |"
      }
      print line
      if (r == 0) { line = "|"; for (c = 1; c <= C; c++) { d = sprintf("%" (w[c] + 2) "s", ""); gsub(/ /, "-", d); line = line d "|" } print line }
    }
  }' "$RESULTS" | tee -a "$LOG"

echo
echo "Proving time is the mean of the measured passes; RAM is the proving process's peak RSS (for recursion, leaves excluded)."
echo "Full output: $LOG"
