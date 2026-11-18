#!/bin/sh
# Build and stage one cross-compiled static bridge archive for cgo consumers and release packaging.
#
# Builds only the staticlib crate type: built alongside the cdylib and rlib, the archive is about
# three times larger. universal2-apple-darwin is built per architecture and combined with lipo,
# so it needs a macOS host.
set -eu

if [ "$#" -ne 2 ]; then
    echo "usage: $0 RUST_TARGET STAGING_DIRECTORY" >&2
    exit 64
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/../../.." && pwd)
rust_target=$1
archive_dir=$2
target_dir=${CARGO_TARGET_DIR:-"$repo_dir/target"}

build_static() {
    cargo-zigbuild rustc --manifest-path "$repo_dir/bindings/native/Cargo.toml" --release \
        --target "$1" --crate-type staticlib
}

mkdir -p "$archive_dir"
if [ "$rust_target" = universal2-apple-darwin ]; then
    build_static x86_64-apple-darwin
    build_static aarch64-apple-darwin
    lipo -create -output "$archive_dir/liblean_pq_native.a" \
        "$target_dir/x86_64-apple-darwin/release/liblean_pq_native.a" \
        "$target_dir/aarch64-apple-darwin/release/liblean_pq_native.a"
    chmod 0644 "$archive_dir/liblean_pq_native.a"
else
    build_static "$rust_target"
    install -m 0644 "$target_dir/$rust_target/release/liblean_pq_native.a" "$archive_dir/liblean_pq_native.a"
fi
