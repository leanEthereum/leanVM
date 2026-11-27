#!/usr/bin/env bash
# Run a Lean command (lake build, lake env lean) in one of a fixed number of host-wide slots, under a memory cap,
# so that any number of workers can share one host without running more Lean processes than it can hold.
#
#   campaign/scripts/lean-slot.sh [--timeout SECS] lake build Rv64mc.Proof.Foo.BarT
#   campaign/scripts/lean-slot.sh --timeout 1800 lake env lean Rv64mc/Proof/Foo/BarT.lean
#
# Run it from formal/rv64mc. It waits for a free slot (and for LEAN_SLOT_MIN_FREE GB of available memory), then runs
# the command under `systemd-run --user --scope -p MemoryMax=$LEAN_SLOT_MEM` with LEAN_ABORT_ON_PANIC=1 and a timeout,
# and exits with the command's status. Every worker on the host must use the same LEAN_SLOT_DIR.
#
# LEAN_SLOTS (default 2), LEAN_SLOT_MEM (14G), LEAN_SLOT_MIN_FREE (10, in GB), LEAN_SLOT_DIR
# (${XDG_RUNTIME_DIR:-/tmp}/rv64mc-lean-slots). Without systemd, set LEAN_SLOT_NOSCOPE=1 to run without the cap.
set -u
slots=${LEAN_SLOTS:-2}
mem=${LEAN_SLOT_MEM:-14G}
min_free=${LEAN_SLOT_MIN_FREE:-10}
dir=${LEAN_SLOT_DIR:-${XDG_RUNTIME_DIR:-/tmp}/rv64mc-lean-slots}
secs=3600
if [ "${1:-}" = --timeout ]; then secs=$2; shift 2; fi
[ $# -gt 0 ] || { echo "usage: lean-slot.sh [--timeout SECS] <command...>" >&2; exit 2; }
mkdir -p "$dir"

avail_gb() { awk '/MemAvailable/ { print int($2 / 1048576) }' /proc/meminfo; }

waited=0
while :; do
  for ((k = 0; k < slots; k++)); do
    exec {fd}>"$dir/slot$k"
    if flock -n "$fd"; then
      if [ "$(avail_gb)" -ge "$min_free" ]; then
        [ "$waited" -gt 0 ] && echo "lean-slot: slot $k after ${waited}s" >&2
        if [ "${LEAN_SLOT_NOSCOPE:-0}" = 1 ]; then
          LEAN_ABORT_ON_PANIC=1 timeout "$secs" "$@"
        else
          systemd-run --user --scope -q -p MemoryMax="$mem" --setenv=LEAN_ABORT_ON_PANIC=1 \
            env LEAN_ABORT_ON_PANIC=1 timeout "$secs" "$@"
        fi
        rc=$?
        exec {fd}>&-
        exit "$rc"
      fi
    fi
    exec {fd}>&-
  done
  sleep 5
  waited=$((waited + 5))
done
