#!/usr/bin/env bash
# Regenerates every file written from the guest, in dependency order, after a change to the guest
# (`guests/`) or to its compiler:
#
#   scripts/regen-guest.sh                 # write
#   scripts/regen-guest.sh --check         # write nothing, fail if any file is stale
#   scripts/regen-guest.sh --from STEP     # resume at STEP: export core whir changes cert memory decoder complete core-mode
#   scripts/regen-guest.sh --jobs N        # the Lean builds' job cap (lake-build.py's --jobs)
#
# Run from anywhere; it works in lean_vm. Each step's generator reads only what the steps before it
# wrote, so a step that fails names what to fix before the rest can run, and `--from` resumes there.
# Writing, the parts whose inputs are written run at once (`after_<part>`, below).
# `--check` writes nothing, so every generator reads the tree as it is: the export and the Lean builds
# the checks need go first, then every check runs at once, each one's output printed when all are
# done, and every stale file is reported, not only the first.
# The `changes` step (`scripts/guest-changes`) lists the functions whose bodies changed, were added or
# were removed since the last export, with the hand-written modules that read them: the proofs to
# adapt. Not regenerated here: the verifier fixtures (`scripts/export-verifier-fixtures-rust.sh`,
# before the differential tests) and the fold rounds' table (`scripts/whir-fold-table`, after a change to
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
steps=(export core whir changes cert memory decoder complete core-mode)
case " ${steps[*]} " in *" $from "*) ;; *) echo "unknown step $from: one of ${steps[*]}" >&2; exit 2 ;; esac
step() { printf '\n==> [%dm%02ds] %s\n' $((SECONDS / 60)) $((SECONDS % 60)) "$*"; }
capped() { ([ "$(uname)" = Darwin ] || ulimit -v "${LEAN_VMEM_KB:-40000000}" || exit; exec "$@"); }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# The core IR's parse, shared by the core route's generators; their shared computations, made once while what they
# read is unchanged (`scripts/core-mode/memo.py`).
export CORE_MODE_CACHE=$tmp/core-mode.pkl CORE_MEMO=$tmp/memo
# A Lean build: skipped under `--check`, which builds every target first. One at a time
# (`$tmp/lake.lock`): the parts run at once.
built=
# flock(1) on fd 9, which macOS lacks: the lock is on the shared open file, held until the subshell exits.
lock9() { python3 -I -c 'import fcntl; fcntl.flock(9, fcntl.LOCK_EX)'; }
lakebuild() { [ -n "$built" ] || (lock9; python3 -I ../lake-build.py . "$@" ${jobs[@]+"${jobs[@]}"}) 9>"$tmp/lake.lock"; }

# The Lean generators import the data the export wrote; each is built after the step before it.
gen() {
  lakebuild "$1"
  capped ".lake/build/bin/$1" ${check[@]+"${check[@]}"}
}

# Each step's parts, and the Lean targets they run.
parts_export=(export) targets_export=()
parts_core=(core_ir core_names core_vsat core_valnames core_gtab core_vswins core_mwins) targets_core=(guest-core)
parts_whir=(whir_data whir_mat_plan whir_queries stack_data stack_data_complete whir_tables) targets_whir=(guest-core)
parts_changes=(changes) targets_changes=()
parts_cert=(cert walk_known) targets_cert=(guest-cert)
parts_memory=(memory count_words) targets_memory=(guest-memory)
parts_decoder=(decoder) targets_decoder=(LeanVM.Guest.Glob LeanVM.Cost.Decoder.GuestTables)
parts_complete=(cert_c count_cycles) targets_complete=(guest-cert)
parts_core_mode=(bridge_align bridge_checks core_mode_fnreg core_mode_anylink core_mode_carry core_mode_termcall core_mode_monocall
  core_mode_pows core_mode_glue core_mode_sigc core_mode) targets_core_mode=()

part_export() {
  step "export: bytecode, source, programs (guest-export, from leanVM's sources)"
  # The core IR before the change, for the `changes` step.
  # None on a fresh checkout, where the generated files are not there yet.
  if [ ${#check[@]} -eq 0 ]; then
    rm -rf .lake/guest-before
    if compgen -G "LeanVM/Guest/Data/Core*.lean" > /dev/null; then
      mkdir -p .lake/guest-before/Data && cp LeanVM/Guest/Data/Core*.lean .lake/guest-before/Data/
      if [ -d LeanVM/Guest/Fn ]; then cp -R LeanVM/Guest/Fn .lake/guest-before/Fn; fi
      if [ -d LeanVM/Guest/Pack ]; then cp -R LeanVM/Guest/Pack .lake/guest-before/Pack; fi
    fi
  fi
  cargo build --release --manifest-path scripts/guest-export/Cargo.toml
  capped scripts/guest-export/target/release/guest-export . ${check[@]+"${check[@]}"}
}

part_core_ir() {
  step "core: the core IR (guest-core)"
  gen guest-core
}

part_core_names() {
  step "core: the names' modulus (CoreNames)"
  python3 -I scripts/core-names-modulus ${check[@]+"${check[@]}"}
}

part_core_valnames() {
  step "core: the value names the proofs cite (scripts/val-names/gen.py)"
  python3 -I scripts/val-names/gen.py ${check[@]+"${check[@]}"}
}

part_core_gtab() {
  step "core: the digit tables of powers of g (scripts/gtab)"
  python3 -I scripts/gtab ${check[@]+"${check[@]}"}
}

# A generator with no check mode of its own runs as one on a copy of the tree (`check-in-place`).
in_place() {
  local name=$1; shift
  if [ ${#check[@]} -eq 0 ]; then "$@"; else python3 -I scripts/check-in-place "$name" "$@"; fi
}

part_whir_data() {
  step "whir: the stacked opening's templates (whir-data)"
  python3 -I scripts/whir-data ${check[@]+"${check[@]}"}
}

part_whir_mat_plan() {
  step "whir: the matrices' plan (whir-mat-plan)"
  python3 -I scripts/whir-mat-plan ${check[@]+"${check[@]}"}
}

part_whir_queries() {
  step "whir: the query windows' and the queries' specializations (whir-queries)"
  in_place whir-queries python3 -I scripts/whir-queries/all.py .
}

part_stack_data() {
  step "whir: the stack selectors' specializations (stack-data)"
  python3 -I scripts/stack-data ${check[@]+"${check[@]}"}
}

part_stack_data_complete() {
  step "whir: the column selectors' completeness, every specialization (stack-data-complete)"
  python3 -I scripts/stack-data-complete ${check[@]+"${check[@]}"}
}

# `open_stacked`'s call tables for the guest decoder's reader, from the template and the
# specializations' table (`Fast/WhirTables.lean`, checked by `Fast/WhirCalls.lean`).
part_whir_tables() {
  step "whir: open_stacked's call tables (scripts/whir-tables.lean)"
  lakebuild LeanVM.Guest.Fast.WhirTemplate LeanVM.Guest.B1.Opening.QueriesLoops LeanVM.Guest.Data.Names
  if [ ${#check[@]} -eq 0 ]; then
    (lock9; capped lake env lean scripts/whir-tables.lean) 9>"$tmp/lake.lock"
  else
    (lock9; WHIR_TABLES_CHECK=1 capped lake env lean scripts/whir-tables.lean) 9>"$tmp/lake.lock"
  fi
}

part_core_vswins() {
  step "core: verify_sub's windows (scripts/vs-windows)"
  python3 -I scripts/vs-windows ${check[@]+"${check[@]}"}
}

part_core_mwins() {
  step "core: main's windows (scripts/main-windows)"
  python3 -I scripts/main-windows ${check[@]+"${check[@]}"}
}

part_core_vsat() {
  step "core: where verify_sub's obligations sit (VsAt)"
  python3 -I scripts/vs-at ${check[@]+"${check[@]}"}
}

# The soundness certificates and their kernel checks only (`--k`): the completeness data the full run writes
# (`B2C/`, `Data/Plumb`, ...) feed the core route's modules, at tag `formal-bus-archive`.
part_cert() {
  step "cert: the certificates (guest-cert --k)"
  lakebuild guest-cert
  capped .lake/build/bin/guest-cert --k ${check[@]+"${check[@]}"}
}

# The walks' obligations, one conjunct per function the certificates hand something on at its cuts
# (`Checked.oblFns`, which `cert` writes).
part_walk_known() {
  step "cert: the walks' obligations (walk-known-all)"
  python3 -I scripts/walk-known-all ${check[@]+"${check[@]}"}
}

# The guest decoder's literal tables from the guest's entries and certificates, then their chunked
# checks from the tables just written (`Cost/Decoder/GuestTables.lean`, `GuestLanes.lean`,
# `DecoderSize/`, `Bounds/Decoder/GuestLocs/`).
part_decoder() {
  step "decoder: the decoder's tables and their chunks (decoder-tables, decoder-table-chunks)"
  local d=$tmp/decoder
  mkdir -p "$d"
  lakebuild LeanVM.Guest.Glob
  (lock9; capped lake env lean scripts/decoder-tables-entries.lean) 9>"$tmp/lake.lock" | sed -n "s/^entries: //p" > "$d/entries.txt"
  python3 -I scripts/decoder-tables --entries "$d/entries.txt" ${check[@]+"${check[@]}"}
  lakebuild LeanVM.Cost.Decoder.GuestTables
  (lock9; capped lake env lean scripts/decoder-tables-inputs.lean) 9>"$tmp/lake.lock" > "$d/in.txt"
  sed -n "s/^rows: //p" "$d/in.txt" > "$d/rows.txt"
  python3 -I scripts/decoder-table-chunks --row-lengths "$d/rows.txt" ${check[@]+"${check[@]}"}
}

# The completeness data and checks beside the soundness files (`--c`, which writes `--k`'s files again,
# byte for byte): `Pack/<dir>/B2CData`, `Data/{Plumb, CplParts, Snaps, CplArms}`, `B2C/{Cplw, Shared,
# Chained, Eq}`, B2's completeness reads them.
part_cert_c() {
  step "complete: the completeness data and checks (guest-cert --c)"
  lakebuild guest-cert
  capped .lake/build/bin/guest-cert --c ${check[@]+"${check[@]}"}
}

part_memory() {
  step "memory: the core functions' names and callees (scripts/guest-callees)"
  python3 -I scripts/guest-callees ${check[@]+"${check[@]}"}
  step "memory: the memory layer's checks (guest-memory)"
  gen guest-memory
}

# The words certificates on the aligned allocator (`Memory/GuestWordsA/`), from the core IR and the frame sizes.
part_count_words() {
  step "memory: the words certificates on the aligned allocator (scripts/count/words.py, hand.py)"
  [ ${#check[@]} -eq 0 ] || return 0
  python3 -I scripts/count/words.py .
  python3 -I scripts/count/hand.py .
}

# The instruction counts by opcode with hand functions (`Memory/GuestCnt{W,H,Z}/`), from the core IR and the plumbing's
# `pmax` the completeness data hold.
part_count_cycles() {
  step "complete: the instruction counts with hand functions (scripts/count/cycles.py)"
  [ ${#check[@]} -eq 0 ] || return 0
  python3 -I scripts/count/cycles.py .
}

# The core route (`git show formal-bus-archive:formal/notes/core-mode.md`): the hint bridge's alignment, then each
# function's registries, powers of g, glue and signature, then its heap certificate, pairing, frame walk, route data,
# the loops' check and the certificates' assembly. A function with no contract written or in its rule file gets its
# frame layout's cells and no heap facts (`sigc.py --minimal`).
core_mode_py() {
  local s=$1; shift
  python3 -I "scripts/$s" "$@" ${check[@]+"${check[@]}"}
}

# The bridge reads B2's completeness data (`Pack/*/B2CData.lean`, the `complete` step).
part_bridge_align() {
  step "core-mode: the hint bridge's alignment checks (scripts/bridge-cert/align.py)"
  core_mode_py bridge-cert/align.py
  step "core-mode: the program's alignment assembled (scripts/bridge-cert/progal.py)"
  core_mode_py bridge-cert/progal.py
}

part_bridge_checks() {
  step "core-mode: the jump cells checked (scripts/bridge-cert/jumpcells.py)"
  core_mode_py bridge-cert/jumpcells.py
  step "core-mode: the allocation track checked (scripts/bridge-cert/alloc.py)"
  core_mode_py bridge-cert/alloc.py
  step "core-mode: the computed hints checked (scripts/bridge-cert/pair.py)"
  core_mode_py bridge-cert/pair.py
  step "core-mode: the witness hints checked (scripts/bridge-cert/wit.py)"
  core_mode_py bridge-cert/wit.py
  step "core-mode: the frame hints' flags checked (scripts/bridge-cert/fral.py)"
  core_mode_py bridge-cert/fral.py
}

part_core_mode_fnreg() {
  step "core-mode: each function's own routing facts and families registered (scripts/core-mode/fnreg.py)"
  core_mode_py core-mode/fnreg.py
}

part_core_mode_anylink() {
  step "core-mode: the claim list's callees linked to its table (scripts/core-mode/anylink.py)"
  core_mode_py core-mode/anylink.py
}

part_core_mode_carry() {
  step "core-mode: the facts carried down to callees (scripts/core-mode/carry.py)"
  core_mode_py core-mode/carry.py
  core_mode_py core-mode/carrynz.py
}

part_core_mode_termcall() {
  step "core-mode: the call sites carrying their callees' exponent bounds (scripts/core-mode/termcall.py)"
  core_mode_py core-mode/termcall.py
}

part_core_mode_monocall() {
  step "core-mode: the gap walk's checks (scripts/core-mode/monocall.py)"
  core_mode_py core-mode/monocall.py
}

part_core_mode_pows() {
  step "core-mode: each function's powers of g (scripts/core-mode/pows.py)"
  core_mode_py core-mode/pows.py
}

part_core_mode_glue() {
  step "core-mode: the functions' ties to their global index (scripts/core-mode/glue.py)"
  core_mode_py core-mode/glue.py
}

part_core_mode_sigc() {
  step "core-mode: each function's signature (scripts/core-mode/sigc.py --minimal)"
  core_mode_py core-mode/sigc.py --minimal
}

part_core_mode() {
  local t0=$SECONDS
  step "core-mode: bodies with calls (scripts/core-mode/callc.py)"
  core_mode_py core-mode/callc.py --emit
  step "core-mode: loop helpers (scripts/core-mode/loopcc.py)"
  core_mode_py core-mode/loopcc.py --emit
  step "core-mode: heap certificates (scripts/core-mode/heap.py)"
  core_mode_py core-mode/heap.py --emit LeanVM/Guest/CoreMode/Gen
  step "core-mode: pairings (scripts/core-mode/pair.py)"
  core_mode_py core-mode/pair.py --emit
  step "core-mode: frame walks (scripts/core-mode/frame_gen.py)"
  in_place core-mode/frame_gen.py python3 -I scripts/core-mode/frame_gen.py
  step "core-mode: route data (scripts/core-mode/core.py)"
  core_mode_py core-mode/core.py
  step "core-mode: the loops' termination check (scripts/core-mode/loopcheck.py)"
  core_mode_py core-mode/loopcheck.py
  step "core-mode: the certificates, the end theorem's assembly (scripts/core-mode/certs.py)"
  core_mode_py core-mode/certs.py
  local d=$((SECONDS - t0))
  printf 'core-mode: the route generated in %dm%02ds\n' $((d / 60)) $((d % 60))
}

part_changes() {
  [ ${#check[@]} -eq 0 ] && [ -d .lake/guest-before ] || return 0
  step "changes: the functions whose bodies changed, and the modules that read them (guest-changes)"
  python3 -I scripts/guest-changes .lake/guest-before
}

selected=() started=
for s in "${steps[@]}"; do
  [ "$s" = "$from" ] && started=1
  [ -n "$started" ] && selected+=("$s")
done

# Writing, each part starts once the parts whose output it reads are done (`after_<part>`, parts of the
# steps not selected counting as done), so independent parts run at once; the Lean generators' builds
# first (`exes`), together. A part's output is printed when it ends; a part whose inputs failed does not run.
after_exes=(export) after_core_ir=(exes) after_core_names=(core_ir) after_core_vsat=(core_ir) after_core_vswins=(core_ir) after_core_mwins=(core_ir)
after_core_valnames=(core_ir) after_changes=(core_ir) after_cert=(core_names core_vsat core_valnames changes)
after_whir_data=(core_ir) after_whir_mat_plan=(whir_data) after_whir_queries=(core_ir) after_stack_data=(core_ir) after_stack_data_complete=(core_ir)
after_walk_known=(cert) after_decoder=(cert)
after_whir_tables=(whir_data whir_queries cert)
after_cert_c=(cert) after_count_cycles=(cert_c) after_memory=(core_ir) after_count_words=(core_ir cert)
after_bridge_align=(cert_c) after_bridge_checks=(bridge_align count_words)
after_core_mode_fnreg=(bridge_align) after_core_mode_anylink=(bridge_align) after_core_mode_pows=(bridge_align)
after_core_mode_glue=(bridge_align) after_core_mode_sigc=(bridge_align) after_core_mode_carry=(bridge_align)
after_core_mode_termcall=(bridge_align)
after_core_mode_monocall=(bridge_align)
after_core_mode=(bridge_checks core_mode_fnreg core_mode_anylink core_mode_carry core_mode_termcall core_mode_monocall
  core_mode_pows core_mode_glue core_mode_sigc memory)
part_exes() {
  step "exes: the core IR's generator (guest-core)"
  lakebuild guest-core
}

if [ ${#check[@]} -eq 0 ]; then
  # the core IR's generator built early only when the core IR is written
  todo=()
  case " ${selected[*]} " in *" core "*) todo=(exes) ;; esac
  for s in "${selected[@]}"; do eval "todo+=(\"\${parts_${s//-/_}[@]}\")"; done
  pids=() failed=()
  for p in "${todo[@]}"; do
    (
      # however the part ends, the parts waiting on it see it end
      trap '[ -e "$tmp/$p.ok" ] || touch "$tmp/$p.failed"' EXIT
      eval "deps=(\${after_$p[@]+\"\${after_$p[@]}\"})"
      for d in ${deps[@]+"${deps[@]}"}; do
        case " ${todo[*]} " in *" $d "*) ;; *) continue ;; esac
        until [ -e "$tmp/$d.ok" ] || [ -e "$tmp/$d.failed" ]; do sleep 1; done
        [ -e "$tmp/$d.ok" ] || exit 1
      done
      # not in an `if`'s condition, where `set -e` would not stop the part at its first failing command
      set +e
      (set -e; "part_$p") > "$tmp/$p.out" 2>&1
      rc=$?
      set -e
      if [ "$rc" -eq 0 ]; then touch "$tmp/$p.ok"; else exit 1; fi
    ) & pids+=($!)
  done
  for i in "${!todo[@]}"; do
    wait "${pids[$i]}" || failed+=("${todo[$i]}")
    [ -e "$tmp/${todo[$i]}.out" ] && cat "$tmp/${todo[$i]}.out"
  done
  if [ ${#failed[@]} -gt 0 ]; then
    echo "error: failed: ${failed[*]}" >&2
    exit 1
  fi
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
  v=${s//-/_}
  eval "targets+=(\${targets_$v[@]+\"\${targets_$v[@]}\"}); parts+=(\"\${parts_$v[@]}\")"
done
if [ ${#targets[@]} -gt 0 ]; then
  step "the checks' Lean builds: $(printf '%s\n' "${targets[@]}" | sort -u | tr '\n' ' ')"
  python3 -I ../lake-build.py . $(printf '%s\n' "${targets[@]}" | sort -u) ${jobs[@]+"${jobs[@]}"}
fi
built=1
run_parts "${parts[@]}"
if [ ${#failed[@]} -gt 0 ]; then
  echo "error: stale or failed: ${failed[*]}" >&2
  exit 1
fi
step "done: every file derived from the guest is current"
