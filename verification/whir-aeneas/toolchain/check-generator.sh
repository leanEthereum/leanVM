#!/usr/bin/env bash
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
formal=$(CDPATH= cd -- "$here/.." && pwd)
charon="$formal/.tools/aeneas/charon"
generator="$formal/.tools/aeneas-source/src/_build/default/main.exe"
[[ -x "$charon" && -x "$generator" ]] || { printf 'Run bootstrap.sh and bootstrap-tool.sh first.\n' >&2; exit 2; }
work=$(mktemp -d /tmp/whir-generator-repro.XXXXXX)
trap 'rm -rf -- "$work"' EXIT
run_heavy() {
    flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 "$@"
}
export LEAN_NUM_THREADS=2 CARGO_BUILD_JOBS=2
cd "$formal"
run_heavy env RUSTUP_TOOLCHAIN=nightly-2026-09-17 "$charon" rustc --preset=aeneas --dest-file "$work/copy_parents.llbc" -- "$here/tests/copy_parents.rs" --crate-name copy_parents --crate-type lib --edition=2024
run_heavy "$generator" -backend lean -no-progress-bar -dest "$work" "$work/copy_parents.llbc"
run_heavy lake env lean "$work/CopyParents.lean"
run_heavy env RUSTUP_TOOLCHAIN=nightly-2026-09-17 "$charon" rustc --preset=aeneas --monomorphize --start-from unused_impl_metadata::roundtrip_word --dest-file "$work/unused_impl_metadata.llbc" -- "$here/tests/unused_impl_metadata.rs" --crate-name unused_impl_metadata --crate-type lib --edition=2024
run_heavy "$generator" -backend lean -all-computable -no-progress-bar -dest "$work" "$work/unused_impl_metadata.llbc"
run_heavy lake env lean "$work/UnusedImplMetadata.lean"
run_heavy python3 "$here/tests/check_unused_impl_metadata.py" "$generator" "$work/unused_impl_metadata.llbc"
printf 'Generated parent-field and guarded metadata reproducers check under Lean 4.34.\n'
