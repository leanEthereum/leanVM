#!/usr/bin/env bash
# Builds and checks the statement package and the five proof projects as .github/workflows/lean.yml
# does, one after another, each in its own directory with its own manifest, then lean_vm against
# this repository's Rust (`leanvm`, which needs cargo). `lake build` at the root runs it.
#
#   ./check-all.sh [lean] [vectors] [statement] [common] [lean_xmss] [lean_sphincs] [lean_da] [lean_vm] [leanvm]
#   (default: all seven; `lean` is the first six, built together first, `vectors` is `leanvm`)
#
# The compiled checks and `lean` run under a virtual-memory cap of LEAN_VMEM_KB (default 40 GB);
# `lake` itself cannot, as it reserves about 1 GB of address space per job: every build runs in
# `lake-build.py`, which admits its modules by memory within a systemd scope.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
log=$(mktemp -d)
trap 'rm -rf "$log"' EXIT

step() { printf '\n==> [%dm%02ds] %s\n' $((SECONDS / 60)) $((SECONDS % 60)) "$*"; }
fail() { echo "error: $*" >&2; exit 1; }
capped() { (ulimit -v "${LEAN_VMEM_KB:-40000000}"; exec "$@"); }

# No proof escape outside comments (`tools/escape-scan.py`: `sorry`, `admit`, `native_decide`,
# `+native`, `unsafe`, `implemented_by`, `#exit`, an `axiom` declaration, and the ways to skip the
# kernel that `#print axioms` cannot see); `.lean` files only, so `lake-build.py`'s `--dev`, which
# names `skipKernelTC`, is exempt. The CI runs the same script.
done_once=" "  # what already ran: `together` runs every project's scan and cache first
once() { case $done_once in *" $1 "*) return 1 ;; esac; done_once+="$1 "; }

no_escapes() {
  once "escapes:$1" || return 0
  step "$1: forbid proof escapes"
  if ! python3 -I tools/escape-scan.py "$1"; then
    fail "$1: proof escape"
  fi
}

# `lake exe cache get` in $1, once per run.
cache_get() {
  once "cache:$1" || return 0
  (cd "$1" && lake exe cache get)
}

# `lake build` in $1, its modules admitted by memory (`lake-build.py`), then no deprecation warning
# from the modules matching $2. Its last step, a plain `lake build`, replays a cached module's
# warnings, so the log lists every one.
build() {
  step "$1: build, its modules admitted by memory"
  python3 -I lake-build.py "$1" 2>&1 | tee "$log/build.txt"
  if grep -E "^warning: $2.*has been deprecated" "$log/build.txt"; then
    fail "$1: deprecated API"
  fi
}

# Each theorem after the module $2 depends on Lean's three axioms only, asked from outside.
axioms() {
  local dir=$1 module=$2 t; shift 2
  step "$dir: axiom footprint"
  { echo "import $module"; for t in "$@"; do echo "#print axioms $t"; done; } > "$log/axioms.lean"
  (cd "$dir" && capped lake env lean "$log/axioms.lean") | tee "$log/axioms.txt"
  for t in "$@"; do
    grep -qF "'$t' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log/axioms.txt" \
      || fail "$dir: $t depends on more axioms"
  done
}

# The statement: definitions and end statements only, importing Mathlib, VCVio, CompPoly and itself.
# Its generated guest data is heavy, so its modules are admitted by memory.
lakefiles() {
  once lakefiles || return 0
  step "lakefiles: no option that skips the kernel"
  if grep -nE 'skipKernelTC|debug\.' $(ls lakefile.lean */lakefile.toml */lakefile.lean 2>/dev/null); then
    fail "a lakefile sets an option that skips the kernel"
  fi
}

statement() {
  no_escapes Statement
  lakefiles
  step "Statement: imports only Mathlib, VCVio, CompPoly and itself"
  if grep -rnE '^(public )?(meta )?import ' --include='*.lean' --exclude-dir=.lake Statement \
      | grep -vE ':[0-9]+:(public )?(meta )?import (Mathlib|VCVio|CompPoly|Statement)\.'; then
    fail "Statement imports more than Mathlib, VCVio, CompPoly and itself"
  fi
  cache_get Statement
  step "Statement: build, its modules admitted by memory"
  python3 -I lake-build.py Statement
}

common() {
  no_escapes common
  cache_get common
  build common 'Common'
  axioms common Common Common.indifferentiability Common.transfer Common.transfer2 \
    Common.keccak256_indifferentiable Common.keccak256_transfer Common.keccak256_transfer2 \
    Common.SufCma.rpm_le_romB Common.SufCma.stronglyUnforgeable_of_romBoundAdv \
    Common.SeedDuplex.duplex_le Common.SeedDuplex.duplex_ge
}

lean_xmss() {
  no_escapes lean_xmss
  cache_get lean_xmss
  build lean_xmss '(LeanXmss|XmssSecurity)'
  axioms lean_xmss XmssSecurity XmssSecurity.leanXmss_rom_adversary_bound \
    XmssSecurity.leanXmss_rpm_security
}

lean_sphincs() {
  no_escapes lean_sphincs
  cache_get lean_sphincs
  # The kernel-checked tables (`decide +kernel`) are the heavy modules, each within about 3 GB.
  build lean_sphincs '(Sphincs|FORS)/'
  axioms lean_sphincs Sphincs Sphincs.leanSphincsStronglyUnforgeable FORS.Lifetimes.h26_layered_adversary FORS.h26_layered
}

# LeanDA's security: Benedikt Wagner's framework, theorems and proofs (b-wagn/fv-pq-da), ported
# and instantiated with LeanDA.
lean_da() {
  no_escapes lean_da
  cache_get lean_da
  build lean_da '(LeanDa|PqDas)'
  axioms lean_da LeanDa LeanDa.leanDa_perfectlyComplete_rpm LeanDa.leanDa_positionBinding \
    LeanDa.leanDa_codeBinding LeanDa.checker_sound LeanDa.commitCodewords_eq_commitCells \
    LeanDa.dualCodeword_eq_dualCodewordAt LeanDa.membershipChallengeM_id \
    LeanDa.leanDa_positionBinding_rpm LeanDa.leanDa_codeBinding_rpm \
    LeanDa.leanDa_codeBinding_rpm_bound
}

# Every lean_vm executable, in one build.
EXES=(node-vectors guest-core guest-cert guest-memory scheme-vectors guest-diff leanvm-verify wire-diff leanvm-prove)

# The six projects' targets and lean_vm's executables in one build from lean_vm, whose workspace holds the other
# five, so that their modules build beside lean_vm's instead of one project after another. The projects' own builds
# below then find everything built and replay its warnings.
together() {
  local p
  lakefiles
  for p in Statement common lean_xmss lean_sphincs lean_da lean_vm; do
    no_escapes "$p"
    cache_get "$p"
  done
  step "all six projects: one build, its modules admitted by memory"
  python3 -I lake-build.py lean_vm LeanVM LeanVMTests "${EXES[@]}" @statement/Statement @common/Common \
    @lean-xmss-security/LeanXmss @lean-xmss-security/XmssSecurity @lean-xmss-security/+XmssSecurity.Tests.QueryBudget \
    @lean-sphincs-security/Sphincs @lean-sphincs-security/FORS @lean-da-security/LeanDa
}

executables() {
  step "lean_vm: the executables"
  (cd lean_vm && lake build "${EXES[@]}")
}

lean_vm() {
  no_escapes lean_vm
  cache_get lean_vm
  # Fails on any warning and on an axiom footprint beyond Lean's three (`LeanVM.lean`).
  step "lean_vm: build, its modules admitted by memory"
  python3 -I lake-build.py lean_vm LeanVM LeanVMTests
  axioms lean_vm LeanVM LeanVM.theorems_hold LeanVM.corollaries_hold \
    LeanVM.Wire.roundTrip LeanVM.Wire.oneEncoding LeanVM.Wire.proveWithHash_wireDecodable
  executables
  # The compiled checks are independent: run together, each one's output printed when all are done.
  step "lean_vm: the Rust vectors' costly checks, and the guest's core IR, certificates, memory-layer checks and decoder tables current"
  local k pids=() names=(node-vectors guest-core guest-cert guest-memory decoder-tables)
  (cd lean_vm && capped .lake/build/bin/node-vectors) > "$log/node-vectors.out" 2>&1 & pids+=($!)
  for k in guest-core guest-cert guest-memory; do
    (cd lean_vm && capped ".lake/build/bin/$k" --check) > "$log/$k.out" 2>&1 & pids+=($!)
  done
  # The decoder tables' inputs evaluated from the build just made (`decoder-tables-inputs.lean`: one line each).
  (
    (cd lean_vm && capped lake env lean scripts/decoder-tables-inputs.lean) > "$log/decoder.txt"
    for k in entries rows split; do sed -n "s/^$k: //p" "$log/decoder.txt" > "$log/$k.txt"; done
    python3 -I lean_vm/scripts/decoder-tables --entries "$log/entries.txt" --check
    python3 -I lean_vm/scripts/decoder-table-chunks --row-lengths "$log/rows.txt" --split-lengths "$log/split.txt" --check
  ) > "$log/decoder-tables.out" 2>&1 & pids+=($!)
  local i failed=()
  for i in "${!pids[@]}"; do
    wait "${pids[$i]}" || failed+=("${names[$i]}")
    printf -- '--- %s\n' "${names[$i]}"
    cat "$log/${names[$i]}.out"
  done
  [ ${#failed[@]} -eq 0 ] || fail "lean_vm: ${failed[*]} failed"
}

# Against this repository's Rust: the guest's data is the one leanVM's sources give, and the Lean and Rust verifiers, and
# the Lean and Rust wire encodings, agree on the fixtures and their mutations.
leanvm() {
  command -v cargo > /dev/null || fail "leanvm: needs cargo; name the other projects to skip it"
  executables
  step "leanvm: the guest's data is leanVM's"
  cargo build --release --manifest-path lean_vm/scripts/guest-export/Cargo.toml
  capped lean_vm/scripts/guest-export/target/release/guest-export lean_vm --check
  step "leanvm: the fold rounds' table is the prover's (whir-fold-table)"
  cargo run --release --manifest-path lean_vm/scripts/whir-fold-table/Cargo.toml -- \
    lean_vm/LeanVM/Protocol/ToArkLib/Whir/AffineCombinerDeployedTable.lean --check
  step "leanvm: the honest hints are the Rust's, and the guest runs on them (guest-diff)"
  local gd
  gd=$(mktemp -d)
  (cd lean_vm && LEANVM_GUEST_DIFF="$gd" cargo test --release \
    --manifest-path scripts/guest-export/Cargo.toml --lib guest_diff -- --ignored)
  (cd lean_vm && capped .lake/build/bin/guest-diff "$gd"/*.txt)
  rm -rf "$gd"
  # verification only; key generation and signing are run by hand (`scheme-vectors --xmss-sign`,
  # lean_sphincs' `lake exe signature-kat`)
  step "leanvm: EthLib's vectors on the statement's verifiers, compiled (scheme-vectors)"
  (cd lean_vm && capped .lake/build/bin/scheme-vectors)
  step "leanvm: Rust-vs-Lean differential"
  cargo build --release --manifest-path lean_vm/scripts/rust-verifier-cli/Cargo.toml
  (cd lean_vm && python3 -I scripts/fuzz-verifier.py tests/fixtures/verifier --jobs 4)
  # Every fixture's wire proof (`proof.wire`, `Proof::to_bytes`) and the Rust test's vector, and their
  # mutations: the same verdicts and decoded proofs, and the round trip through `Proof.toBytes`.
  step "leanvm: the proof's wire encoding, Lean against Rust (wire-diff)"
  cargo build --release --manifest-path lean_vm/scripts/wire-diff/Cargo.toml
  (cd lean_vm && python3 -I scripts/wire-diff.py tests/fixtures/verifier --jobs 8)
  step "leanvm: the statement's honest prover's proofs, Lean-made, against both verifiers (prover-diff)"
  local pd
  pd=$(mktemp -d)
  lean_vm/scripts/export-prover-traces-rust.sh "$pd" > /dev/null
  (cd lean_vm && python3 -I scripts/prover-diff.py "$pd" --mutations 40 --jobs 4 --identical \
    --expected tests/fixtures/verifier)
  rm -rf "$pd"
}

# `lean`: the six Lean projects; `vectors`: the checks against leanVM's Rust.
projects=()
for p in "$@"; do
  case $p in
    lean) projects+=(together statement common lean_xmss lean_sphincs lean_da lean_vm) ;;
    vectors) projects+=(leanvm) ;;
    *) projects+=("$p") ;;
  esac
done
[ ${#projects[@]} -gt 0 ] || projects=(together statement common lean_xmss lean_sphincs lean_da lean_vm leanvm)
for p in "${projects[@]}"; do
  case $p in
    together | statement | common | lean_xmss | lean_sphincs | lean_da | lean_vm | leanvm) "$p" ;;
    *) fail "unknown project $p" ;;
  esac
done
step "all checks passed: ${projects[*]}"
