#!/usr/bin/env bash
# The native verifiers (leanXMSS's, leanSPHINCS's and leanVM's, as x86-64 or AArch64 machine code) against the crates
# `lean_xmss`, `lean_sphincs` and `verifier`: natively on a host of the architecture, else under QEMU user mode.
#
# Usage, from anywhere:
#   run/check.sh                            # x86-64, the default schemes printed by `lake exe emit-x64` (formal/native)
#   run/check.sh --arch arm                 # AArch64, printed by `lake exe emit-arm` (formal/native)
#   run/check.sh [--arch x86|arm] XMSS.S [SPHINCS.S [VM.S]]
#                                           # given assembly files, exporting `xmss_verify`, `sphincs_verify` and
#                                           # `leanvm_verify`; an absent or empty argument is printed by the
#                                           # architecture's emitter
#   CHECK_SCHEMES=vm run/check.sh           # some schemes (`xmss`, `sphincs`, `vm`; the default all three)
#   CHECK_VM_FIXTURES=DIR                   # the leanVM verifier fixtures to use, an earlier
#                                           # `formal/lean_vm/scripts/export-verifier-fixtures-rust.sh DIR`; without
#                                           # it, scheme `vm` exports them to the output directory first
# The cases, the assembly and the harness go to a fresh temporary directory, or to $CHECK_OUT when set; the script
# prints it. The exit code is 0 when every case gives the crate's answer.
#
# Needs cargo and rustc with the target `x86_64-unknown-linux-musl` or `aarch64-unknown-linux-musl` (the harness is
# static, linked by rustc's own `rust-lld`, so no C toolchain or sysroot of the target), clang to assemble, and for
# AArch64 on another host `qemu-aarch64-static` (or $QEMU_AARCH64) on the PATH.
#
# `reference/` (a Cargo project of its own) writes the cases: EthLib's verify vectors, fresh keys and signatures, and
# signatures changed in one place (a flipped bit in the message, the public key, the randomizer, a chain value, a path
# node, a FORS secret or path node, a counter, the leaf index; another key), each as the scheme's input words
# (`Native/Xmss/Layout.lean`, `Native/Sphincs/Layout.lean`) with what the crate's `verify` returns; for leanVM, each
# fixture's proof and copies of its wire cut, extended or with a bit flipped in each field (`reference/src/vm.rs`),
# with what the crate `verifier` returns. `harness.rs`, linked with the assembled verifiers, lays out each case's
# context (and for leanVM the areas `NativeVm/Input.lean` asks for), runs the verifier on it and compares its result
# with that bit.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project=$(dirname "$here")

arch=x86
paths=()
while [[ $# -gt 0 ]]; do
  case $1 in
    --arch) arch=${2:-}; shift 2 || { echo "--arch needs x86 or arm" >&2; exit 2; } ;;
    --arch=*) arch=${1#--arch=}; shift ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) paths+=("$1"); shift ;;
  esac
done
[[ ${#paths[@]} -le 3 ]] || { echo "at most three assembly files, XMSS.S, SPHINCS.S and VM.S" >&2; exit 2; }

case $arch in
  x86)
    triple=x86_64-unknown-linux-musl
    machine=x86_64
    emitter=(lake exe emit-x64)
    qemu=${QEMU_X86_64:-qemu-x86_64-static}
    ;;
  arm)
    triple=aarch64-unknown-linux-musl
    machine=aarch64
    emitter=(lake exe emit-arm)
    qemu=${QEMU_AARCH64:-qemu-aarch64-static}
    ;;
  *) echo "unknown architecture $arch, not x86 or arm" >&2; exit 2 ;;
esac
runner=()
[[ $(uname -m) == "$machine" ]] || runner=("$qemu")

read -r -a schemes <<<"${CHECK_SCHEMES:-xmss sphincs vm}"
declare -A given=([xmss]=${paths[0]:-} [sphincs]=${paths[1]:-} [vm]=${paths[2]:-})

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
  if [[ -n ${given[$scheme]} ]]; then
    asm=$(realpath "${given[$scheme]}")
  else
    echo "emitting $scheme.S"
    asm=$out/$scheme.S
    if ! (cd "$project" && "${emitter[@]}" "$scheme" "$asm" >"$out/emit-$scheme.log" 2>&1); then
      tail -40 "$out/emit-$scheme.log"
      exit 1
    fi
  fi
  echo "assembling $asm"
  clang --target="$triple" -c -o "$out/$scheme.o" "$asm"
  link+=(--cfg "$scheme" -C "link-arg=$out/$scheme.o")
done

echo "building the harness for $triple"
rustc --edition 2024 -C opt-level=1 --target "$triple" -C linker=rust-lld --check-cfg 'cfg(xmss, sphincs, vm)' \
  "${link[@]}" -o "$out/harness" "$here/harness.rs"

total=0
bad=0
while read -r name; do
  [[ " ${schemes[*]} " == *" ${name%%_*} "* ]] || continue
  total=$((total + 1))
  rc=0
  timeout 600 "${runner[@]}" "$out/harness" "$out/$name.case" 2>"$out/$name.err" || rc=$?
  if [[ $rc -ne 0 ]]; then
    bad=$((bad + 1))
    if [[ $rc -ne 1 ]]; then
      echo "$name: HARNESS ERROR (exit $rc): $(cat "$out/$name.err")"
    fi
  fi
  [[ -s $out/$name.err ]] || rm -f "$out/$name.err"
done <"$out/cases.list"

echo
echo "$((total - bad)) of $total cases agree on $arch; outputs in $out"
[[ $bad -eq 0 ]]
