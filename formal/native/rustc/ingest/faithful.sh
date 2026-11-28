#!/usr/bin/env bash
# The programs elaborated from committed assembly are rustc's: each program (NativeRustcArm.{Xmss,Sphincs}.code,
# NativeRustcX64.{Xmss,Sphincs}.code, NativeRustcVmArm.Vm.code, NativeRustcVmX64.Vm.code), printed by Kraken's
# printer (`print-rustc-code-arm` and `print-rustc-code-x64`, which add only section and alignment directives)
# and assembled, has the bytes and relocations of rustc's assembly (rustc/asm/signatures-
# aarch64.s, rustc/asm/signatures-x86_64.s, rustc/vm/asm/vm-aarch64.s, rustc/vm/asm/vm-x86_64.s;
# rustc/build.sh builds them when missing)
# assembled the same way, in every core function, and the data they refer to (compare.py says how relocations and
# data are compared, and the one encoding it allows to differ). The panic entries, traps in the ingested programs,
# are not compared. Reachability and parsing are checked, not trusted: the comparison trusts Kraken's printers,
# the assembler and compare.py.
#
# Usage, from anywhere: rustc/ingest/faithful.sh
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
native=$(cd "$here/../.." && pwd)
out=$native/rustc/asm

vmout=$native/rustc/vm/asm
for asm in "$out"/signatures-{aarch64,x86_64}.s "$vmout"/vm-{aarch64,x86_64}.s; do
  [ -f "$asm" ] || { "$native/rustc/build.sh" >&2; break; }
done

(cd "$native" && lake build -q print-rustc-code-arm print-rustc-code-x64 >&2)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
status=0
for scheme in xmss sphincs vm; do
  for arch in arm x64; do
    case $scheme-$arch in
      vm-arm) target=aarch64-unknown-linux-musl rustc=$vmout/vm-aarch64.s ;;
      vm-x64) target=x86_64-unknown-linux-musl rustc=$vmout/vm-x86_64.s ;;
      *-arm) target=aarch64-unknown-linux-musl rustc=$out/signatures-aarch64.s ;;
      *-x64) target=x86_64-unknown-linux-musl rustc=$out/signatures-x86_64.s ;;
    esac
    "$native/.lake/build/bin/print-rustc-code-$arch" "$scheme" "$tmp/$scheme-$arch-ingested.s"
    clang --target=$target -c "$tmp/$scheme-$arch-ingested.s" -o "$tmp/$scheme-$arch-ingested.o"
    clang --target=$target -c "$rustc" -o "$tmp/$scheme-$arch-rustc.o"
    entry=${scheme/#vm/leanvm}_verify
    python3 "$here/compare.py" --entry "$entry" "$tmp/$scheme-$arch-rustc.o" "$tmp/$scheme-$arch-ingested.o" || status=1
  done
done
exit $status
