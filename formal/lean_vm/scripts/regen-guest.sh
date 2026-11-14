#!/usr/bin/env bash
# Regenerates every file written from the guest, in dependency order, after a change to the guest
# (`crates/rec_aggregation/guests/`), to its compiler, or to `formal/leanvm-rev`:
#
#   scripts/regen-guest.sh                 # write
#   scripts/regen-guest.sh --check         # write nothing, fail if any file is stale
#   scripts/regen-guest.sh --from STEP     # resume at STEP: export core changes vt cert mode bridge memory whir count tables decoder
#   scripts/regen-guest.sh --jobs N        # the Lean builds' job cap (lake-build.py's --jobs)
#
# Run from anywhere; it works in lean_vm. Each step's generator reads only what the steps before it
# wrote, so a step that fails names what to fix before the rest can run, and `--from` resumes there.
# `--check` writes nothing, so every generator reads the tree as it is: the export and the Lean builds
# the checks need go first, then every check runs at once, each one's output printed when all are
# done, and every stale file is reported, not only the first.
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
steps=(export core changes vt cert mode bridge memory whir count tables decoder)
case " ${steps[*]} " in *" $from "*) ;; *) echo "unknown step $from: one of ${steps[*]}" >&2; exit 2 ;; esac
step() { printf '\n==> [%dm%02ds] %s\n' $((SECONDS / 60)) $((SECONDS % 60)) "$*"; }
capped() { (ulimit -v "${LEAN_VMEM_KB:-40000000}"; exec "$@"); }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# A Lean build: skipped under `--check`, which builds every target first (`prebuild`).
built=
lakebuild() { [ -n "$built" ] || python3 -I ../lake-build.py . "$@" "${jobs[@]}"; }

# The Lean generators import the data the export wrote; each is built after the step before it.
gen() {
  lakebuild "$1"
  capped ".lake/build/bin/$1" "${check[@]}"
}

# A generator without a check mode of its own, run as one under `--check` (`scripts/check-in-place`).
in_place() {
  local name=$1; shift
  if [ ${#check[@]} -eq 0 ]; then "$@"; else python3 -I scripts/check-in-place "$name" "$@"; fi
}

# Each step's parts, and the Lean targets they run.
parts_export=(export) targets_export=()
parts_core=(core_ir core_names core_vsat) targets_core=(guest-core)
parts_changes=(changes) targets_changes=()
parts_vt=(vt) targets_vt=()
parts_cert=(cert) targets_cert=(guest-cert)
parts_mode=(mode) targets_mode=()
parts_bridge=(bridge) targets_bridge=()
parts_memory=(memory) targets_memory=(guest-memory)
parts_whir=(whir_data whir_mat_plan walk_known whir_queries) targets_whir=(guest-core)
parts_count=(count_gen count_vsos) targets_count=()
parts_tables=(tables) targets_tables=(LeanVM.Guest.Fast.WhirTemplate LeanVM.Guest.B1.Opening.QueriesT
  LeanVM.Guest.Memory.GuestCallees)
parts_decoder=(decoder) targets_decoder=(LeanVM.Guest.Glob LeanVM.Cost.Decoder.GuestTables)

part_export() {
  step "export: bytecode, source, programs (guest-export, from leanVM's sources)"
  # The core IR before the change, for the `changes` step.
  if [ ${#check[@]} -eq 0 ]; then
    rm -rf .lake/guest-before && mkdir -p .lake/guest-before/Data && cp LeanVM/Guest/Data/Core*.lean .lake/guest-before/Data/
    if [ -d LeanVM/Guest/Fn ]; then cp -R LeanVM/Guest/Fn .lake/guest-before/Fn; fi
    if [ -d LeanVM/Guest/Pack ]; then cp -R LeanVM/Guest/Pack .lake/guest-before/Pack; fi
  fi
  cargo build --release --manifest-path scripts/guest-export/Cargo.toml
  capped scripts/guest-export/target/release/guest-export . "${check[@]}"
}

part_core_ir() {
  step "core: the core IR (guest-core)"
  gen guest-core
}

part_core_names() {
  step "core: the names' modulus (CoreNames)"
  python3 -I scripts/core-names-modulus "${check[@]}"
}

part_core_vsat() {
  step "core: where verify_sub's obligations sit (VsAt)"
  python3 -I scripts/vs-at "${check[@]}"
}

part_changes() {
  [ ${#check[@]} -eq 0 ] && [ -d .lake/guest-before ] || return 0
  step "changes: the functions whose bodies changed, and the modules that read them (guest-changes)"
  python3 -I scripts/guest-changes .lake/guest-before
}

part_vt() {
  step "vt: verify_tables' templates and their twins (scripts/b1c-vt/all.py)"
  python3 -I scripts/b1c-vt/all.py "${check[@]}"
}

part_cert() {
  step "cert: the certificates (guest-cert)"
  gen guest-cert
}

part_mode() {
  step "mode: the mode walk's signatures and checks (scripts/mode-cert/gen.py)"
  python3 -I scripts/mode-cert/gen.py "${check[@]}"
  step "mode: the residuals by family (scripts/mode-cert/res.py)"
  python3 -I scripts/mode-cert/res.py "${check[@]}"
}

part_bridge() {
  step "bridge: the hint bridge's prefix checks (scripts/bridge-cert/gen.py)"
  python3 -I scripts/bridge-cert/gen.py "${check[@]}"
  step "bridge: the hint bridge's alignment checks (scripts/bridge-cert/align.py)"
  python3 -I scripts/bridge-cert/align.py "${check[@]}"
}

part_memory() {
  step "memory: the memory layer's checks (guest-memory)"
  gen guest-memory
}

part_whir_data() {
  step "whir: the stacked opening's templates (whir-data)"
  python3 -I scripts/whir-data "${check[@]}"
}

part_whir_mat_plan() {
  step "whir: the matrices' plan (whir-mat-plan)"
  python3 -I scripts/whir-mat-plan "${check[@]}"
}

part_walk_known() {
  step "whir: the walks' obligations (walk-known-all)"
  python3 -I scripts/walk-known-all "${check[@]}"
}

part_whir_queries() {
  step "whir: the query walks and the opening's specializations (whir-queries)"
  in_place whir-queries python3 -I scripts/whir-queries/all.py .
}

part_count_gen() {
  step "count families (scripts/count/gen.py)"
  in_place count/gen.py python3 -I scripts/count/gen.py . all
}

part_count_vsos() {
  step "count families (scripts/count/vsos.py)"
  in_place count/vsos.py python3 -I scripts/count/vsos.py .
}

part_tables() {
  step "tables: open_stacked's call tables (scripts/whir-tables.lean)"
  lakebuild "${targets_tables[@]}"
  capped lake env lean --run scripts/whir-tables.lean "${check[@]}"
}

part_decoder() {
  # The tables are written from the guest's entries, and their chunks from the tables just written.
  step "decoder tables and their chunks"
  local d=$tmp/decoder
  mkdir -p "$d"
  lakebuild LeanVM.Guest.Glob
  capped lake env lean scripts/decoder-tables-entries.lean | sed -n "s/^entries: //p" > "$d/entries.txt"
  python3 -I scripts/decoder-tables --entries "$d/entries.txt" "${check[@]}"
  lakebuild LeanVM.Cost.Decoder.GuestTables
  capped lake env lean scripts/decoder-tables-inputs.lean > "$d/in.txt"
  for k in rows split; do sed -n "s/^$k: //p" "$d/in.txt" > "$d/$k.txt"; done
  python3 -I scripts/decoder-table-chunks --row-lengths "$d/rows.txt" --split-lengths "$d/split.txt" "${check[@]}"
}

selected=() started=
for s in "${steps[@]}"; do
  [ "$s" = "$from" ] && started=1
  [ -n "$started" ] && selected+=("$s")
done

if [ ${#check[@]} -eq 0 ]; then
  for s in "${selected[@]}"; do
    eval "parts=(\"\${parts_$s[@]}\")"
    for p in "${parts[@]}"; do "part_$p"; done
  done
  step "done: adapt the proofs guest-changes listed, then python3 -I ../lake-build.py . LeanVM LeanVMTests (formal/AGENTS.md, Changing the spec)"
  exit 0
fi

# The parts given, at once, each one's output printed in order when all are done; those that fail are
# added to `failed`.
failed=()
run_parts() {
  local p i pids=() names=("$@")
  for p in "${names[@]}"; do
    ("part_$p") > "$tmp/$p.out" 2>&1 & pids+=($!)
  done
  for i in "${!names[@]}"; do
    wait "${pids[$i]}" || failed+=("${names[$i]}")
    cat "$tmp/${names[$i]}.out"
  done
}

# The export builds leanVM's Rust and no other check reads it: it goes first, alone.
if [ "${selected[0]}" = export ]; then
  run_parts export
  selected=("${selected[@]:1}")
fi
targets=() parts=()
for s in "${selected[@]}"; do
  eval "targets+=(\${targets_$s[@]+\"\${targets_$s[@]}\"}); parts+=(\"\${parts_$s[@]}\")"
done
if [ ${#targets[@]} -gt 0 ]; then
  step "the checks' Lean builds: $(printf '%s\n' "${targets[@]}" | sort -u | tr '\n' ' ')"
  python3 -I ../lake-build.py . $(printf '%s\n' "${targets[@]}" | sort -u) "${jobs[@]}"
fi
built=1
run_parts "${parts[@]}"
if [ ${#failed[@]} -gt 0 ]; then
  echo "error: stale or failed: ${failed[*]}" >&2
  exit 1
fi
step "done: every file derived from the guest is current"
