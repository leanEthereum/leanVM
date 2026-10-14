#!/usr/bin/env bash
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../.." && pwd)
tools="$here/.tools/aeneas"
"$here/bootstrap.sh"
generator="$here/.tools/aeneas-source/src/_build/default/main.exe"
if [[ ! -x "$generator" ]]; then
    "$here/bootstrap-tool.sh"
fi
export PATH="$tools:$PATH"
export CARGO_BUILD_JOBS=2 LEAN_NUM_THREADS=2
export RUSTFLAGS='-C target-cpu=x86-64'
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$here/.tools/target}"
surface=${1:-statement}
aeneas_args=(-backend lean -namespace PcsSource -emit-json -no-progress-bar)
case "$surface" in
    statement)
        dest="$here/llbc"
        generated="$here/WhirAeneas/Generated"
        args=(--start-from pcs::stack_open::check_statement)
        cargo_args=(--lib --release)
        ;;
    verifier)
        dest="$here/llbc/verifier"
        generated="$here"
        args=(--start-from pcs::whir::verify::verify_with_basis --include primitives --include fiat_shamir)
        cargo_args=(--lib --release)
        aeneas_args+=(-subdir WhirAeneas/Generated/Verifier -split-files -all-computable)
        ;;
    native)
        dest="$here/failures/native"
        generated="$dest/generated"
        args=(--start-from-if-exists pcs::stack_open::tests::verify_instance --include primitives --include fiat_shamir --include parallel)
        cargo_args=(--lib --tests --release)
        ;;
    *) printf 'unknown extraction surface: %s\n' "$surface" >&2; exit 2 ;;
esac
mkdir -p "$dest" "$generated"
cd "$root/crates/pcs"
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 charon cargo --preset=aeneas "${args[@]}" --dest-file "$dest/pcs.llbc" -- "${cargo_args[@]}"
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 "$generator" "${aeneas_args[@]}" -dest "$generated" "$dest/pcs.llbc"
