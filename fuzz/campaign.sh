#!/usr/bin/env bash
# One command for a dedicated machine: the supervised campaign over every target, and optionally libFuzzer jobs on the
# cheap byte-level targets beside it, both reading and writing the same corpus under $OUT.
#
#   fuzz/campaign.sh [--duration 24h] [--jobs N] [--libfuzzer-jobs M] [--out DIR] [-- extra `leanvm-fuzz run` args]
#
# libFuzzer needs `cargo install cargo-fuzz` and a nightly toolchain; with --libfuzzer-jobs 0 (the default) it is not used.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT=fuzz-out
DURATION=""
JOBS=""
LIBFUZZER_JOBS=0
SLICE=1800
EXTRA=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out) OUT=$2; shift 2 ;;
    --duration) DURATION=$2; shift 2 ;;
    --jobs) JOBS=$2; shift 2 ;;
    --libfuzzer-jobs) LIBFUZZER_JOBS=$2; shift 2 ;;
    --libfuzzer-slice) SLICE=$2; shift 2 ;;
    --) shift; EXTRA=("$@"); break ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done
mkdir -p "$OUT"
cargo build --profile fuzz -p leanvm-fuzz
BIN=target/fuzz/leanvm-fuzz

ARGS=(run --out "$OUT")
[[ -n "$DURATION" ]] && ARGS+=(--duration "$DURATION")
[[ -n "$JOBS" ]] && ARGS+=(--jobs "$JOBS")
"$BIN" "${ARGS[@]}" "${EXTRA[@]}" &
SUPERVISOR=$!
trap 'kill $SUPERVISOR 2>/dev/null; kill $(jobs -p) 2>/dev/null; wait' EXIT INT TERM

if [[ "$LIBFUZZER_JOBS" -gt 0 ]]; then
  # The cheap targets: where coverage guidance pays and a case is microseconds.
  mapfile -t TARGETS < <("$BIN" list | awk '$2 == "cheap" {print $1}')
  (cd fuzz && ./sync-targets.sh && cargo +nightly fuzz build -O --debug-assertions)
  END=$(( $(date +%s) + $(echo "${DURATION:-0}" | sed 's/s$//;s/m$/*60/;s/h$/*3600/;s/d$/*86400/' | bc) ))
  for ((j = 0; j < LIBFUZZER_JOBS; j++)); do
    (
      i=$j
      while [[ -z "$DURATION" || $(date +%s) -lt $END ]]; do
        t=${TARGETS[$((i % ${#TARGETS[@]}))]}
        mkdir -p "$OUT/corpus/$t" "$OUT/libfuzzer/$t"
        (cd fuzz && cargo +nightly fuzz run -O --debug-assertions "$t" "../$OUT/corpus/$t" -- \
          -max_total_time="$SLICE" -artifact_prefix="../$OUT/libfuzzer/$t/" -print_final_stats=1) \
          >> "$OUT/libfuzzer/$t/log.txt" 2>&1 || true
        i=$((i + LIBFUZZER_JOBS))
      done
    ) &
  done
fi
wait $SUPERVISOR
