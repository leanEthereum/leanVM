#!/bin/sh
# Add bindings/.cargo/config.toml to a py-lean-pq source distribution built by `maturin sdist`, as
# .cargo/config.toml at its root: the portable x86_64 baseline with AVX2 and PCLMULQDQ, without
# which a wheel built from the sdist has neither and signs slowly. At the sdist's root, it applies
# to the build that pip runs there.
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
mkdir -p "$work/$name/.cargo"
cp "$repo_dir/bindings/.cargo/config.toml" "$work/$name/.cargo/"
tar -czf "$sdist" -C "$work" "$name"
echo "added .cargo/config.toml to $sdist"
