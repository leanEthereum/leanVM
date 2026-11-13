#!/usr/bin/env bash
# Regenerates every file written from the guest, in dependency order, after a change to the guest
# (`crates/rec_aggregation/guests/`), to its compiler, or to `formal/leanvm-rev`:
#
#   scripts/regen-guest.sh                 # write
#   scripts/regen-guest.sh --check         # write nothing, fail on the first stale file
#   scripts/regen-guest.sh --from STEP     # resume at STEP: export core changes vt cert memory whir count tables decoder
#   scripts/regen-guest.sh --jobs N        # the Lean builds' job cap (lake-build.py's --jobs)
#
# Run from anywhere; it works in lean_vm. Each step's generator reads only what the steps before it
# wrote, so a step that fails names what to fix before the rest can run, and `--from` resumes there.
# The `changes` step (`scripts/guest-changes`) lists the functions whose bodies changed, were added or
# were removed since the last export, with the hand-written modules that read them: the proofs to
# adapt. Not regenerated here: the verifier fixtures (`scripts/export-verifier-fixtures-rust.sh`,
# after a protocol change) and the fold rounds' table (`scripts/whir-fold-table`, after a change to
# WHIR's folding).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
check=() from=export jobs=()
while [ $# -gt 0 ]; do
  case $1 in
    --check) check=(--check) ;;
    --from) from=$2; shift ;;
    --jobs) jobs=(--jobs "$2"); shift ;;
    *) echo "usage: scripts/regen-guest.sh [--check] [--from STEP] [--jobs N]" >&2; exit 2 ;;
  esac
  shift
done
steps=(export core changes vt cert memory whir count tables decoder)
case " ${steps[*]} " in *" $from "*) ;; *) echo "unknown step $from: one of ${steps[*]}" >&2; exit 2 ;; esac
step() { printf '\n==> [%dm%02ds] %s\n' $((SECONDS / 60)) $((SECONDS % 60)) "$*"; }
capped() { (ulimit -v "${LEAN_VMEM_KB:-40000000}"; exec "$@"); }
started=
run() { [ -n "$started" ] || [ "$1" = "$from" ] && started=1; [ -n "$started" ]; }

if run export; then
  step "export: bytecode, source, programs (guest-export, from leanVM's sources)"
  # The core IR before the change, for the `changes` step.
  if [ ${#check[@]} -eq 0 ]; then
    rm -rf .lake/guest-before && mkdir -p .lake/guest-before/Data && cp LeanVM/Guest/Data/Core*.lean .lake/guest-before/Data/
    if [ -d LeanVM/Guest/Fn ]; then cp -R LeanVM/Guest/Fn .lake/guest-before/Fn; fi
    if [ -d LeanVM/Guest/Pack ]; then cp -R LeanVM/Guest/Pack .lake/guest-before/Pack; fi
  fi
  cargo build --release --manifest-path scripts/guest-export/Cargo.toml
  capped scripts/guest-export/target/release/guest-export . "${check[@]}"
fi

# The Lean generators import the data the export wrote; each is built after the step before it.
gen() {
  lake build "$1"
  capped ".lake/build/bin/$1" "${check[@]}"
}

if run core; then
  step "core: the core IR (guest-core)"
  gen guest-core
  step "core: the names' modulus (CoreNames)"
  python3 -I scripts/core-names-modulus "${check[@]}"
  step "core: where verify_sub's obligations sit (VsAt)"
  python3 -I scripts/vs-at "${check[@]}"
fi

if run changes && [ ${#check[@]} -eq 0 ] && [ -d .lake/guest-before ]; then
  step "changes: the functions whose bodies changed, and the modules that read them (guest-changes)"
  python3 -I scripts/guest-changes .lake/guest-before
fi

if run vt; then
  step "vt: verify_tables' templates and their twins (scripts/b1c-vt/all.py)"
  python3 -I scripts/b1c-vt/all.py "${check[@]}"
fi

if run cert; then
  step "cert: the certificates (guest-cert)"
  gen guest-cert
fi

if run memory; then
  step "memory: the memory layer's checks (guest-memory)"
  gen guest-memory
fi

if run whir; then
  step "whir: the stacked opening's templates and walks (whir-data, whir-mat-plan, walk-known-all, whir-queries)"
  python3 -I scripts/whir-data "${check[@]}"
  python3 -I scripts/whir-mat-plan "${check[@]}"
  python3 -I scripts/walk-known-all "${check[@]}"
  if [ ${#check[@]} -eq 0 ]; then
    python3 -I scripts/whir-queries/all.py .
  else
    python3 -I scripts/check-in-place whir-queries python3 -I scripts/whir-queries/all.py .
  fi
fi

if run count; then
  step "count families (scripts/count)"
  if [ ${#check[@]} -eq 0 ]; then
    python3 -I scripts/count/gen.py . all
    python3 -I scripts/count/vsos.py .
  else
    python3 -I scripts/check-in-place count/gen.py python3 -I scripts/count/gen.py . all
    python3 -I scripts/check-in-place count/vsos.py python3 -I scripts/count/vsos.py .
  fi
fi

if run tables; then
  step "tables: open_stacked's call tables (scripts/whir-tables.lean)"
  python3 -I ../lake-build.py . LeanVM.Guest.Fast.WhirTemplate LeanVM.Guest.B1.Opening.QueriesT LeanVM.Guest.Memory.GuestCallees "${jobs[@]}"
  capped lake env lean --run scripts/whir-tables.lean "${check[@]}"
fi

if run decoder; then
  # The tables are written from the guest's entries, and their chunks from the tables just written.
  step "decoder tables and their chunks"
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  python3 -I ../lake-build.py . LeanVM.Guest.Glob "${jobs[@]}"
  capped lake env lean scripts/decoder-tables-entries.lean | sed -n "s/^entries: //p" > "$tmp/entries.txt"
  python3 -I scripts/decoder-tables --entries "$tmp/entries.txt" "${check[@]}"
  python3 -I ../lake-build.py . LeanVM.Cost.Decoder.GuestTables "${jobs[@]}"
  capped lake env lean scripts/decoder-tables-inputs.lean > "$tmp/in.txt"
  for k in rows split; do sed -n "s/^$k: //p" "$tmp/in.txt" > "$tmp/$k.txt"; done
  python3 -I scripts/decoder-table-chunks --row-lengths "$tmp/rows.txt" --split-lengths "$tmp/split.txt" "${check[@]}"
fi

step "done: adapt the proofs guest-changes listed, then python3 -I ../lake-build.py . LeanVM LeanVMTests (formal/AGENTS.md, Changing the spec)"
