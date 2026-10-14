#!/usr/bin/env bash
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
release=nightly-2026.10.09-d119a47
archive="$here/.tools/$release.tar.gz"
tools="$here/.tools/aeneas"
backend="$here/.tools/backend-4.34"
mkdir -p "$here/.tools"
if [[ ! -x "$tools/aeneas" || ! -f "$backend/lakefile.lean" ]]; then
    if [[ ! -f "$archive" ]]; then
        curl -fL "https://github.com/AeneasVerif/aeneas/releases/download/$release/aeneas-linux-x86_64.tar.gz" -o "$archive"
    fi
    printf '%s  %s\n' 5f2204baaaef68f98422b762403cb06d3d6cc9e164db74b619051e81524cac54 "$archive" | sha256sum -c -
    if [[ ! -x "$tools/aeneas" ]]; then
        mkdir -p "$tools"
        tar -xzf "$archive" -C "$tools"
    fi
    if [[ ! -f "$backend/lakefile.lean" ]]; then
        mkdir -p "$backend"
        tar -xzf "$archive" -C "$backend" --strip-components=2 --exclude='backends/lean/.lake' backends/lean
    fi
fi
printf '%s  %s\n' 853a2caa4bdb825229ec7ca10ed2abca965593d9e4faeb59747c2a03e793cb5f "$tools/aeneas" cccbb77cd02c34677fd30f152938b15d8f35574292d25086b7ea8cf359774a72 "$tools/charon" 888096bc2471ca8e959b5e04eeb2eb2c4c879f2983fdd7afc4a6d42921bc2594 "$tools/charon-driver" | sha256sum -c -
for patch in backend-lean-4.31-shifts.patch backend-lean-4.31-iterator-alias.patch backend-lean-4.31-string-kernel.patch backend-lean-4.34.patch backend-lean-4.34-stdlib.patch backend-lean-4.34-vector.patch backend-lean-4.34-coinductive.patch backend-lean-4.34-bvify-tests.patch backend-lean-4.34-rendered-examples.patch backend-lean-4.34-slice.patch backend-lean-4.34-tactic-api.patch backend-lean-4.34-test-compat.patch; do
    if ! git -C "$backend" apply --reverse --check "$here/$patch" 2>/dev/null; then
        git -C "$backend" apply --check "$here/$patch"
        git -C "$backend" apply "$here/$patch"
    fi
done
case "${1:-}" in
    '') ;;
    build)
        export ELAN_TOOLCHAIN=leanprover/lean4:v4.34.0 LEAN_NUM_THREADS=2 CARGO_BUILD_JOBS=2
        cd "$here"
        flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 lake exe cache get
        flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 lake build Aeneas AeneasMeta
        ;;
    *) printf 'unknown bootstrap action: %s\n' "$1" >&2; exit 2 ;;
esac
