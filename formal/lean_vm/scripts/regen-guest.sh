#!/usr/bin/env bash
# Regenerates every file written from the guest, in dependency order, after a change to the guest
# (`guests/`) or to its compiler:
#
#   scripts/regen-guest.sh                 # write
#   scripts/regen-guest.sh --check         # write nothing, fail if any file is stale
#   scripts/regen-guest.sh --from STEP     # resume at STEP: export core changes vt cert bridge core-mode memory res whir count tables decoder
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
steps=(export core changes vt cert bridge core-mode memory res whir count tables decoder)
case " ${steps[*]} " in *" $from "*) ;; *) echo "unknown step $from: one of ${steps[*]}" >&2; exit 2 ;; esac
step() { printf '\n==> [%dm%02ds] %s\n' $((SECONDS / 60)) $((SECONDS % 60)) "$*"; }
capped() { ([ "$(uname)" = Darwin ] || ulimit -v "${LEAN_VMEM_KB:-40000000}" || exit; exec "$@"); }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# The core IR's parse, shared by the core-mode generators; their pairings, computed once while what they
# read is unchanged (`scripts/core-mode/memo.py`).
export CORE_MODE_CACHE=$tmp/core-mode.pkl CORE_MEMO=$tmp/memo

# A Lean build: skipped under `--check`, which builds every target first (`prebuild`). One at a time
# (`$tmp/lake.lock`): the parts run at once, and a Lean run of built modules (`leanrun`) waits for no
# build to be writing them.
built=
# flock(1) on fd 9, which macOS lacks: the lock is on the shared open file, held until the subshell exits.
lock9() { python3 -I -c 'import fcntl; fcntl.flock(9, fcntl.LOCK_EX)'; }
lakebuild() { [ -n "$built" ] || (lock9; python3 -I ../lake-build.py . "$@" ${jobs[@]+"${jobs[@]}"}) 9>"$tmp/lake.lock"; }
leanrun() { (lock9; capped lake env lean "$@") 9>"$tmp/lake.lock"; }

# The Lean generators import the data the export wrote; each is built after the step before it.
gen() {
  lakebuild "$1"
  capped ".lake/build/bin/$1" ${check[@]+"${check[@]}"}
}

# A generator without a check mode of its own, run as one under `--check` (`scripts/check-in-place`).
in_place() {
  local name=$1; shift
  if [ ${#check[@]} -eq 0 ]; then "$@"; else python3 -I scripts/check-in-place "$name" "$@"; fi
}

# Each step's parts, and the Lean targets they run.
parts_export=(export) targets_export=()
parts_core=(core_ir core_names core_vsat core_valnames) targets_core=(guest-core)
parts_changes=(changes) targets_changes=()
parts_vt=(vt) targets_vt=()
parts_cert=(cert) targets_cert=(guest-cert)
parts_core_mode=(core_mode_fnreg core_mode_anylink core_mode_sigc core_mode_pows core_mode_glue core_mode)
targets_core_mode=()
parts_bridge=(bridge_align bridge_checks) targets_bridge=()
parts_memory=(memory) targets_memory=(guest-memory)
parts_res=(res) targets_res=()
parts_whir=(whir_data whir_mat_plan walk_known whir_queries) targets_whir=(guest-core)
parts_count=(count_gen count_vsos count_loops) targets_count=()
parts_tables=(tables) targets_tables=(LeanVM.Guest.Fast.WhirTemplate LeanVM.Guest.B1.Opening.QueriesT
  LeanVM.Guest.Memory.GuestCallees)
parts_decoder=(decoder) targets_decoder=(LeanVM.Guest.Glob LeanVM.Cost.Decoder.GuestTables)

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

part_core_vsat() {
  step "core: where verify_sub's obligations sit (VsAt)"
  python3 -I scripts/vs-at ${check[@]+"${check[@]}"}
}

part_changes() {
  [ ${#check[@]} -eq 0 ] && [ -d .lake/guest-before ] || return 0
  step "changes: the functions whose bodies changed, and the modules that read them (guest-changes)"
  python3 -I scripts/guest-changes .lake/guest-before
}

part_vt() {
  step "vt: verify_tables' templates and their twins (scripts/b1c-vt/all.py)"
  python3 -I scripts/b1c-vt/all.py ${check[@]+"${check[@]}"}
}

part_cert() {
  step "cert: the certificates (guest-cert)"
  gen guest-cert
}

# The core route (`formal/notes/core-mode.md`): its functions' signatures, heap certificates, pairings, frame
# walks and route data. Every function keeps its signature (its contract, by hand in its rule file
# `scripts/core-mode/fn/<f>.py`, or as written) and its frame walk takes its facts from the frame layout and its own
# walk. A function's own routing rules are in its rule file (`scripts/core-mode/fnrules.py`).
# After `bridge`: the route data reads the bridge's alignment links (`Bridge/ProgAl/Link*`). The first five read only
# the core IR, the compiled data, the alignment and the rule files, and write apart: they run at once, the rest after.
part_core_mode_fnreg() {
  step "core-mode: each function's own routing facts and families registered (scripts/core-mode/fnreg.py)"
  python3 -I scripts/core-mode/fnreg.py ${check[@]+"${check[@]}"}
}

part_core_mode_anylink() {
  step "core-mode: the claim list's callees linked to its table (scripts/core-mode/anylink.py)"
  python3 -I scripts/core-mode/anylink.py ${check[@]+"${check[@]}"}
}

part_core_mode_sigc() {
  step "core-mode: each function's signature (scripts/core-mode/sigc.py)"
  python3 -I scripts/core-mode/sigc.py ${check[@]+"${check[@]}"}
}

part_core_mode_pows() {
  step "core-mode: each function's powers of g (scripts/core-mode/pows.py)"
  python3 -I scripts/core-mode/pows.py ${check[@]+"${check[@]}"}
}

part_core_mode_glue() {
  step "core-mode: the functions' ties to their global index (scripts/core-mode/glue.py)"
  python3 -I scripts/core-mode/glue.py ${check[@]+"${check[@]}"}
}

part_core_mode() {
  step "core-mode: bodies with calls (scripts/core-mode/callc.py)"
  python3 -I scripts/core-mode/callc.py --emit ${check[@]+"${check[@]}"}
  step "core-mode: loop helpers (scripts/core-mode/loopcc.py)"
  python3 -I scripts/core-mode/loopcc.py --emit ${check[@]+"${check[@]}"}
  step "core-mode: heap certificates (scripts/core-mode/heap.py)"
  python3 -I scripts/core-mode/heap.py --emit LeanVM/Guest/CoreMode/Gen ${check[@]+"${check[@]}"}
  step "core-mode: pairings (scripts/core-mode/pair.py)"
  python3 -I scripts/core-mode/pair.py --emit ${check[@]+"${check[@]}"}
  step "core-mode: frame walks (scripts/core-mode/frame_gen.py)"
  in_place core-mode/frame_gen.py python3 -I scripts/core-mode/frame_gen.py
  step "core-mode: route data (scripts/core-mode/core.py)"
  python3 -I scripts/core-mode/core.py ${check[@]+"${check[@]}"}
  step "core-mode: the core route's certificates, the end theorem's assembly (scripts/core-mode/certs.py)"
  python3 -I scripts/core-mode/certs.py ${check[@]+"${check[@]}"}
}

# What the core route reads of the bridge (`core-mode`'s glue, pairings and route data): its alignment.
part_bridge_align() {
  step "bridge: the hint bridge's alignment checks (scripts/bridge-cert/align.py)"
  python3 -I scripts/bridge-cert/align.py ${check[@]+"${check[@]}"}
  step "bridge: the program's alignment assembled (scripts/bridge-cert/progal.py)"
  python3 -I scripts/bridge-cert/progal.py ${check[@]+"${check[@]}"}
}

part_bridge_checks() {
  step "bridge: the jump cells checked (scripts/bridge-cert/jumpcells.py)"
  python3 -I scripts/bridge-cert/jumpcells.py ${check[@]+"${check[@]}"}
  step "bridge: the computed hints paired (scripts/bridge-cert/pair.py)"
  python3 -I scripts/bridge-cert/pair.py ${check[@]+"${check[@]}"}
  step "bridge: the witness cells checked (scripts/bridge-cert/wit.py)"
  python3 -I scripts/bridge-cert/wit.py ${check[@]+"${check[@]}"}
  step "bridge: the allocation hints checked (scripts/bridge-cert/alloc.py)"
  python3 -I scripts/bridge-cert/alloc.py ${check[@]+"${check[@]}"}
}

part_memory() {
  step "memory: the memory layer's checks (guest-memory)"
  gen guest-memory
}

part_res() {
  step "res: the monotone claim lists' callers (scripts/core-mode/monocall.py)"
  python3 -I scripts/core-mode/monocall.py ${check[@]+"${check[@]}"}
  step "res: facts carried down to callees (scripts/core-mode/carry.py)"
  python3 -I scripts/core-mode/carry.py ${check[@]+"${check[@]}"}
  step "res: check_opening_terminal's callers (scripts/core-mode/termcall.py)"
  python3 -I scripts/core-mode/termcall.py ${check[@]+"${check[@]}"}
}

part_whir_data() {
  step "whir: the stacked opening's templates (whir-data)"
  python3 -I scripts/whir-data ${check[@]+"${check[@]}"}
}

part_whir_mat_plan() {
  step "whir: the matrices' plan (whir-mat-plan)"
  python3 -I scripts/whir-mat-plan ${check[@]+"${check[@]}"}
}

part_walk_known() {
  step "whir: the walks' obligations (walk-known-all)"
  python3 -I scripts/walk-known-all ${check[@]+"${check[@]}"}
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

# After `count/gen.py`, which writes the `Memory/GuestCallees.lean` it reads.
part_count_loops() {
  step "count: the loop helpers' entries (scripts/core-mode/loopcheck.py)"
  python3 -I scripts/core-mode/loopcheck.py ${check[@]+"${check[@]}"}
}

part_tables() {
  step "tables: open_stacked's call tables (scripts/whir-tables.lean)"
  lakebuild "${targets_tables[@]}"
  leanrun --run scripts/whir-tables.lean ${check[@]+"${check[@]}"}
}

part_decoder() {
  # The tables are written from the guest's entries, and their chunks from the tables just written.
  step "decoder tables and their chunks"
  local d=$tmp/decoder
  mkdir -p "$d"
  lakebuild LeanVM.Guest.Glob
  leanrun scripts/decoder-tables-entries.lean | sed -n "s/^entries: //p" > "$d/entries.txt"
  python3 -I scripts/decoder-tables --entries "$d/entries.txt" ${check[@]+"${check[@]}"}
  lakebuild LeanVM.Cost.Decoder.GuestTables
  leanrun scripts/decoder-tables-inputs.lean > "$d/in.txt"
  sed -n "s/^rows: //p" "$d/in.txt" > "$d/rows.txt"
  python3 -I scripts/decoder-table-chunks --row-lengths "$d/rows.txt" ${check[@]+"${check[@]}"}
}

selected=() started=
for s in "${steps[@]}"; do
  [ "$s" = "$from" ] && started=1
  [ -n "$started" ] && selected+=("$s")
done

# Writing, each part starts once the parts whose output it reads are done (`after_<part>`, parts of the
# steps not selected counting as done), so independent parts run at once; the Lean generators' builds
# first (`exes`), together. A part's output is printed when it ends; a part whose inputs failed does not run.
after_exes=(export) after_core_ir=(exes) after_core_names=(core_ir) after_core_vsat=(core_ir) after_core_valnames=(core_ir)
after_changes=(core_ir)
after_vt=(core_ir) after_cert=(core_names core_vsat core_valnames changes vt) after_memory=(core_ir core_valnames)
after_bridge_align=(cert) after_bridge_checks=(bridge_align)
after_core_mode_fnreg=(bridge_align) after_core_mode_anylink=(bridge_align) after_core_mode_sigc=(bridge_align)
after_core_mode_pows=(bridge_align) after_core_mode_glue=(bridge_align)
after_core_mode=(core_mode_fnreg core_mode_anylink core_mode_sigc core_mode_pows core_mode_glue)
after_res=(core_mode bridge_checks) after_whir_data=(cert) after_whir_mat_plan=(whir_data)
after_walk_known=(whir_mat_plan) after_whir_queries=(walk_known) after_count_gen=(whir_queries memory cert)
after_count_vsos=(count_gen) after_count_loops=(count_vsos core_mode) after_tables=(count_vsos) after_decoder=(cert)
part_exes() {
  step "exes: the core IR's generator (guest-core)"
  # guest-core alone: guest-cert and guest-memory import the data its run writes (`Data/NameStrings`), each built
  # in its own step
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
