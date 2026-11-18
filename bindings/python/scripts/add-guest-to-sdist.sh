#!/bin/sh
# Add leanVM's guest program to a py-lean-pq source distribution built by `maturin sdist`.
#
# The sdist carries the leanVM crates as path dependencies, and maturin packages each one's crate
# directory. The `aggregation` crate also compiles in guests/lean_ethereum.py from the repository
# root (outside its crate), so a wheel built from the sdist fails without this file.
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
tar -czf "$sdist" -C "$work" "$name"
echo "added guests/lean_ethereum.py to $sdist"
