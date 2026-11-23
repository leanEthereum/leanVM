#!/bin/sh
# Stage the Nim package's release archives: one stripped native archive per supported target, named
# lean-pq-native-TARGET.a as lean_pq/abi.nim downloads it from the release on a package's first
# build. Releases attach them; they never enter git.
#
# NATIVE_ROOT holds one directory per target, each with liblean_pq_native.a: x86_64-linux-gnu,
# aarch64-linux-gnu, universal-macos, x86_64-windows-gnu (the zig-native release archives, under
# the target names lean_pq/abi.nim uses). A release stages all four (the workflow checks each
# "staged" line); CI stages the one it built.
set -eu

if [ "$#" -ne 2 ]; then
    echo "usage: $0 NATIVE_ROOT OUTPUT_DIRECTORY" >&2
    exit 64
fi

native_root=$(CDPATH= cd -- "$1" && pwd)
output=$2

if [ -e "$output" ]; then
    echo "$output already exists" >&2
    exit 1
fi
mkdir -p "$output"
output=$(CDPATH= cd -- "$output" && pwd)
strip="$(CDPATH= cd -- "$(dirname -- "$0")/../../native/scripts" && pwd)/strip-archive.sh"
staged=0
for target in x86_64-linux-gnu aarch64-linux-gnu universal-macos x86_64-windows-gnu; do
    source="$native_root/$target/liblean_pq_native.a"
    if [ ! -f "$source" ]; then
        continue
    fi
    destination="$output/lean-pq-native-$target.a"
    install -m 0644 "$source" "$destination"
    sh "$strip" --strip-debug "$destination"
    echo "staged $target"
    echo "$target: $(wc -c < "$source") bytes, $(wc -c < "$destination") stripped"
    staged=$((staged + 1))
done
if [ "$staged" -eq 0 ]; then
    echo "no liblean_pq_native.a found under $native_root" >&2
    exit 1
fi
