#!/usr/bin/env bash
# The rustc-compiled verifiers (leanXMSS's, leanSPHINCS's and leanVM's, as x86-64 or AArch64 machine code) against the crates
# `lean_xmss`, `lean_sphincs` and `verifier`: natively on a host of the architecture, else under QEMU user mode.
#
# Usage, from anywhere:
#   run/check.sh                            # x86-64, rustc assemblies in `rustc/asm/` and `rustc/vm/asm/`
#   run/check.sh --arch arm                 # AArch64 rustc assemblies
#   run/check.sh --rustc [--arch x86|arm]    # explicit rustc selection, also the default and only mode
#   run/check.sh [--arch x86|arm] [--xmss FILE] [--sphincs FILE] [--vm FILE] [ASM...]
#                                           # given assembly files, exporting `xmss_verify`, `sphincs_verify` and
#                                           # `leanvm_verify`; positional paths match CHECK_SCHEMES in order (or
#                                           # xmss, sphincs, vm when three are passed); an absent or empty argument
#                                           # uses the corresponding rustc assembly
#   CHECK_SCHEMES=vm run/check.sh           # some schemes (`xmss`, `sphincs`, `vm`; the default all three)
#   CHECK_VM_FIXTURES=DIR                   # the leanVM verifier fixtures to use, an earlier
#                                           # `formal/lean_vm/scripts/export-verifier-fixtures-rust.sh DIR`; without
#                                           # it, scheme `vm` exports them to the output directory first
# The cases, the assembly and the harness go to a fresh temporary directory, or to $CHECK_OUT when set; the script
# prints it. The exit code is 0 when every case gives the crate's answer.
#
# Needs cargo and rustc with the target `x86_64-unknown-linux-musl` or `aarch64-unknown-linux-musl` (the harness is
# static, linked by rustc's own `rust-lld`, so no C toolchain or sysroot of the target), clang and its `llvm-objcopy`
# to assemble, and for AArch64 on another host `qemu-aarch64-static` (or $QEMU_AARCH64) on the PATH.
#
# `reference/` (a Cargo project of its own) writes the cases: EthLib's verify vectors, fresh keys and signatures, and
# signatures changed in one place (a flipped bit in the message, the public key, the randomizer, a chain value, a path
# node, a FORS secret or path node, a counter, the leaf index; another key), each as the scheme's input words
# (`rustc/xmss.rs`, `rustc/sphincs.rs`) with what the crate's `verify` returns; for leanVM, each
# fixture's proof and copies of its wire cut, extended or with a bit flipped in each field (`reference/src/vm.rs`),
# plus mutated public inputs, mutated valid bytecodes and adversarial malformed wire encodings, with what the crate
# `verifier` returns. `harness.rs`, linked with the assembled verifiers, lays out each case's context (and for leanVM
# the areas `rustc/vm/src/lib.rs` asks for), runs each case with guards immediately before and after the exact
# payload in separate placements, and compares its result with that bit. The signature prefix is inaccessible in
# the guard-before placement. The summary counts each placement and each defensive VM rejection separately.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project=$(dirname "$here")

arch=x86
declare -A named_given=()
paths=()
while [[ $# -gt 0 ]]; do
  case $1 in
    --arch) arch=${2:-}; shift 2 || { echo "--arch needs x86 or arm" >&2; exit 2; } ;;
    --arch=*) arch=${1#--arch=}; shift ;;
    --rustc) shift ;;
    --xmss) named_given[xmss]=${2:-}; shift 2 || { echo "--xmss needs a path" >&2; exit 2; } ;;
    --xmss=*) named_given[xmss]=${1#--xmss=}; shift ;;
    --sphincs) named_given[sphincs]=${2:-}; shift 2 || { echo "--sphincs needs a path" >&2; exit 2; } ;;
    --sphincs=*) named_given[sphincs]=${1#--sphincs=}; shift ;;
    --vm) named_given[vm]=${2:-}; shift 2 || { echo "--vm needs a path" >&2; exit 2; } ;;
    --vm=*) named_given[vm]=${1#--vm=}; shift ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) paths+=("$1"); shift ;;
  esac
done
[[ ${#paths[@]} -le 3 ]] || { echo "at most three assembly files, XMSS.S, SPHINCS.S and VM.S" >&2; exit 2; }

case $arch in
  x86)
    triple=x86_64-unknown-linux-musl
    machine=x86_64
    qemu=${QEMU_X86_64:-qemu-x86_64-static}
    rustc_xmss=$project/rustc/asm/signatures-x86_64.s
    rustc_sphincs=$project/rustc/asm/signatures-x86_64.s
    rustc_vm=$project/rustc/vm/asm/vm-x86_64.s
    ;;
  arm)
    triple=aarch64-unknown-linux-musl
    machine=aarch64
    qemu=${QEMU_AARCH64:-qemu-aarch64-static}
    rustc_xmss=$project/rustc/asm/signatures-aarch64.s
    rustc_sphincs=$project/rustc/asm/signatures-aarch64.s
    rustc_vm=$project/rustc/vm/asm/vm-aarch64.s
    ;;
  *) echo "unknown architecture $arch, not x86 or arm" >&2; exit 2 ;;
esac
runner=()
[[ $(uname -m) == "$machine" ]] || runner=("$qemu")

read -r -a schemes <<<"${CHECK_SCHEMES:-xmss sphincs vm}"
declare -A defaults=([xmss]="$rustc_xmss" [sphincs]="$rustc_sphincs" [vm]="$rustc_vm")
declare -A given=([xmss]="" [sphincs]="" [vm]="")
if [[ ${#paths[@]} -gt 0 ]]; then
  if [[ ${#paths[@]} -le ${#schemes[@]} ]]; then
    for i in "${!paths[@]}"; do
      given[${schemes[$i]}]=${paths[$i]}
    done
  else
    given[xmss]=${paths[0]:-}
    given[sphincs]=${paths[1]:-}
    given[vm]=${paths[2]:-}
  fi
fi
for k in "${!named_given[@]}"; do
  given[$k]=${named_given[$k]}
done

# Pin the harness's rustc toolchain to `rustc/rust-toolchain.toml` unless caller overrides it.
if [[ -z ${RUSTUP_TOOLCHAIN:-} && -f "$project/rustc/rust-toolchain.toml" ]]; then
  RUSTUP_TOOLCHAIN=$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$project/rustc/rust-toolchain.toml")
  export RUSTUP_TOOLCHAIN
fi

out=${CHECK_OUT:-$(mktemp -d)}
mkdir -p "$out"
out=$(realpath "$out")
echo "outputs in $out"

fixtures=()
if [[ " ${schemes[*]} " == *" vm "* ]]; then
  if [[ -n ${CHECK_VM_FIXTURES:-} ]]; then
    fixtures=("$(realpath "$CHECK_VM_FIXTURES")")
  else
    echo "exporting the leanVM verifier fixtures"
    if ! "$project/../lean_vm/scripts/export-verifier-fixtures-rust.sh" "$out/fixtures" >"$out/fixtures.log" 2>&1; then
      tail -40 "$out/fixtures.log"
      exit 1
    fi
    fixtures=("$out/fixtures")
  fi
fi

echo "building the case generator"
cargo build --release --quiet --manifest-path "$here/reference/Cargo.toml"
"$here/reference/target/release/reference" "$out" "${fixtures[@]}"

link=()
for scheme in "${schemes[@]}"; do
  case $scheme in
    xmss | sphincs | vm) ;;
    *) echo "unknown scheme $scheme" >&2; exit 2 ;;
  esac
  asm=$(realpath "${given[$scheme]:-${defaults[$scheme]}}")
  echo "assembling $asm"
  clang --target="$triple" -c -o "$out/$scheme.o" "$asm"
  # Only this entry stays global: the combined signature assembly also exports the other entry and core symbols.
  entry=${scheme/#vm/leanvm}_verify
  "$(clang --print-prog-name=llvm-objcopy)" --keep-global-symbol="$entry" "$out/$scheme.o"
  link+=(--cfg "$scheme" -C "link-arg=$out/$scheme.o")
done

echo "building the harness for $triple"
rustc --edition 2024 -C opt-level=1 --target "$triple" -C linker=rust-lld --check-cfg 'cfg(xmss, sphincs, vm)' \
  "${link[@]}" -o "$out/harness" "$here/harness.rs"

total=0
bad=0
run_case() {
  local name=$1 placement=$2
  shift 2
  local rc=0 count failures
  timeout 600 "${runner[@]}" "$out/harness" "--guard-$placement" "$@" \
    >"$out/$name.$placement.log" 2>"$out/$name.$placement.err" || rc=$?
  cat "$out/$name.$placement.log"
  count=$(grep -cE '^(ok|MISMATCH) ' "$out/$name.$placement.log" || true)
  failures=$(grep -c '^MISMATCH ' "$out/$name.$placement.log" || true)
  if [[ $rc -ne 0 && $failures -eq 0 ]]; then
    count=$((count + 1))
    failures=1
  fi
  total=$((total + count))
  bad=$((bad + failures))
  if [[ $rc -ne 0 && $rc -ne 1 ]]; then
    echo "$name ($placement): HARNESS ERROR (exit $rc): $(cat "$out/$name.$placement.err")"
  fi
  [[ -s $out/$name.$placement.err ]] || rm -f "$out/$name.$placement.err"
}
for placement in after before; do
  echo "running with guard pages immediately $placement payloads"
  if [[ " ${schemes[*]} " == *" vm "* ]]; then
    run_case vm_preconditions "$placement" --vm-preconditions
  fi
  while read -r name; do
    [[ " ${schemes[*]} " == *" ${name%%_*} "* ]] || continue
    run_case "$name" "$placement" "$out/$name.case"
  done <"$out/cases.list"
done

echo
echo "$((total - bad)) of $total cases agree on $arch; outputs in $out"
[[ $bad -eq 0 ]]
