#!/bin/sh
# Keep the Go CI build matrix aligned with the native archive directories.
set -eu

repo_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
workflow="$repo_dir/.github/workflows/ci.yml"

assert_contains() {
    grep -F -- "$1" "$workflow" >/dev/null
}

assert_contains 'uses: mlugg/setup-zig@v2'
assert_contains 'version: 0.15.2'
assert_contains 'version: 0.16.0'
assert_contains 'cargo install cargo-zigbuild --locked'
assert_contains 'target: x86_64-unknown-linux-gnu'
assert_contains 'target: aarch64-unknown-linux-gnu'
assert_contains 'target: universal2-apple-darwin'
assert_contains 'stage-static.sh ${{ matrix.platform.target }} ${{ matrix.platform.archive_dir }}'
assert_contains 'lipo bindings/go/internal/native/darwin_universal/liblean_pq_native.a -verify_arch arm64 x86_64'
assert_contains 'target: x86_64-pc-windows-gnu'
assert_contains 'archive_dir: bindings/go/internal/native/windows_amd64'
