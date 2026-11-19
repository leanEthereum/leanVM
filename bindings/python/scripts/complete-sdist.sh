#!/bin/sh
# Add the two files outside its crates that a py-lean-pq source distribution built by
# `maturin sdist` needs:
#
# - guests/lean_ethereum.py: the sdist carries the leanVM crates as path dependencies, and maturin
#   packages each one's crate directory, but the `aggregation` crate also compiles in the guest
#   from the repository root, so a wheel built from the sdist fails without it.
# - .cargo/config.toml, a copy of bindings/.cargo/config.toml: the portable x86_64 baseline with
#   AVX2 and PCLMULQDQ, without which a wheel built from the sdist has neither and proves slowly.
#   At the sdist's root, it applies to the build that pip runs there.
set -eu

if [ "$#" -ne 1 ]; then
    echo "usage: $0 SDIST" >&2
    exit 64
fi

sdist=$(CDPATH= cd -- "$(dirname -- "$1")" && pwd)/$(basename -- "$1")
repo_dir=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
name=$(basename -- "$sdist" .tar.gz)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

tar -xzf "$sdist" -C "$work"
test -f "$work/$name/PKG-INFO"
test -f "$work/$name/crates/aggregation/src/guest.rs"
mkdir -p "$work/$name/guests"
cp "$repo_dir/guests/lean_ethereum.py" "$work/$name/guests/"
mkdir -p "$work/$name/.cargo"
cp "$repo_dir/bindings/.cargo/config.toml" "$work/$name/.cargo/"
tar -czf "$sdist" -C "$work" "$name"
echo "added guests/lean_ethereum.py and .cargo/config.toml to $sdist"
