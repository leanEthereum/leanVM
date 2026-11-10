#!/usr/bin/env bash
# How much would the fuzzer notice? Disable one check at a time, rebuild, fuzz the targets that should catch it, and say
# which mutants survive: a check whose removal no target notices is a blind spot of the fuzzer, or a check something
# else already enforces. Either way a human should look.
#
#   fuzz/mutants.sh [--subject verifier|guest] [--duration 240] [--jobs 2] [--threads 2] [--targets <prefixes>]
#                   [--only <id substring>] [--list]
#
# `verifier` (the default) disables each `require` and `transcript.checked()` guard of crates/verifier
# (`mutate_verifier.py`) and fuzzes the soundness targets. `guest` neutralizes each explicit check of the recursion guest
# (`mutate_guest.py`) and fuzzes the guest and aggregation targets; every mutant rebuilds its own child fixtures, so a
# guest sweep takes many hours and belongs on a dedicated machine.
#
# Works on a copy of the working tree under target/mutants, with its own build directory: neither the tree nor a
# running campaign's binary is touched. Results accumulate in target/mutants/results.tsv; a mutant already there is
# skipped, so an interrupted sweep resumes.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WORK=${MUTANTS_DIR:-$ROOT/target/mutants}
SUBJECT=verifier
DURATION=240
JOBS=2
THREADS=2
TARGETS=""
ONLY=""
LIST=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --subject) SUBJECT=$2; shift 2 ;;
    --duration) DURATION=$2; shift 2 ;;
    --jobs) JOBS=$2; shift 2 ;;
    --threads) THREADS=$2; shift 2 ;;
    --targets) TARGETS=$2; shift 2 ;;
    --only) ONLY=$2; shift 2 ;;
    --list) LIST=1; shift ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done

case "$SUBJECT" in
  verifier) SRC=crates/verifier/src; MUTATOR=mutate_verifier.py; FEATURES="--no-default-features --features soundness"
            TARGETS=${TARGETS:-soundness-} ;;
  guest) SRC=crates/rec_aggregation/guests/lean_ethereum.py; MUTATOR=mutate_guest.py; FEATURES=""
         TARGETS=${TARGETS:-guest-,aggregat} ;;
  *) echo "unknown subject $SUBJECT" >&2; exit 2 ;;
esac
WORK=$WORK/$SUBJECT
TREE=$WORK/tree
mkdir -p "$WORK/out"
rsync -a --delete --exclude /target --exclude /.git --exclude /fuzz/target --exclude /fuzz-out "$ROOT/" "$TREE/"
MUTANTS=$(python3 -I "$ROOT/fuzz/$MUTATOR" list "$TREE/$SRC")
if [[ $LIST == 1 ]]; then
  echo "$MUTANTS"
  exit 0
fi

export CARGO_TARGET_DIR=$WORK/target
BIN=$CARGO_TARGET_DIR/fuzz/leanvm-fuzz
RESULTS=$WORK/results.tsv
touch "$RESULTS"
restore() { if [[ -d "$ROOT/$SRC" ]]; then rsync -a "$ROOT/$SRC/" "$TREE/$SRC/"; else cp "$ROOT/$SRC" "$TREE/$SRC"; fi; }
trap restore EXIT

# The unmutated build first: a sweep is only meaningful if it finds nothing.
(cd "$TREE" && cargo build --quiet --profile fuzz -p leanvm-fuzz $FEATURES)
echo "$MUTANTS" | while IFS=$'\t' read -r id location kind code; do
  [[ -n "$ONLY" && "$id" != *"$ONLY"* ]] && continue
  grep -q "^$id	\(KILLED\|SURVIVED\|unbuildable\)" "$RESULTS" && continue
  restore
  python3 -I "$ROOT/fuzz/$MUTATOR" apply "$TREE/$SRC" "$id"
  out=$WORK/out/$(echo "$id" | tr ':/' '__')
  rm -rf "$out"
  if ! (cd "$TREE" && cargo build --quiet --profile fuzz -p leanvm-fuzz $FEATURES 2>"$WORK/build.log"); then
    verdict=unbuildable
    killer=""
  else
    n_targets=$("$BIN" list | awk -v p="$TARGETS" 'BEGIN{split(p, a, ",")} {for (i in a) if (index($1, a[i]) == 1) {print; break}}' | wc -l)
    slice=$(( DURATION * JOBS / (n_targets > 0 ? n_targets : 1) ))
    LEANVM_NUM_THREADS=$THREADS "$BIN" run --targets "$TARGETS" --out "$out" --duration "${DURATION}s" \
      --jobs "$JOBS" --threads "$THREADS" --slice $(( slice > 20 ? slice : 20 )) > "$out.log" 2>&1 || true
    killer=$("$BIN" report --out "$out" | grep -m1 -E '^\[(critical|high|medium)' | sed 's/  */ /g' || true)
    # A sweep that fuzzed nothing proves nothing: say so rather than call the mutant a survivor.
    cases=$(awk 'NR > 2 && $2 ~ /^[0-9]+$/ {n += $2} END {print n + 0}' "$out/stats.txt" 2>/dev/null || echo 0)
    if [[ -n "$killer" ]]; then
      verdict=KILLED
    elif [[ "$cases" -eq 0 ]]; then
      verdict=NORUN
      killer="no case ran: see $out.log"
    else
      verdict=SURVIVED
      killer="$cases cases"
    fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$id" "$verdict" "$location" "$code" "$killer" | tee -a "$RESULTS"
done
restore
echo
echo "killed $(grep -c $'\tKILLED\t' "$RESULTS" || true), survived $(grep -c $'\tSURVIVED\t' "$RESULTS" || true), did not run $(grep -c $'\tNORUN\t' "$RESULTS" || true), unbuildable $(grep -c $'\tunbuildable\t' "$RESULTS" || true): $RESULTS"
grep $'\tSURVIVED\t' "$RESULTS" | cut -f1,4 || true
