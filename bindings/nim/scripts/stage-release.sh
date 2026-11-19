#!/bin/sh
# Stage the Nim package's release archives: one stripped native archive per supported target, named
# lean-pq-native-TARGET.a as lean_pq/abi.nim downloads it from the release on a package's first
# build. Releases attach them; they never enter git.
#
# NATIVE_ROOT holds one directory per target, each with liblean_pq_native.a: x86_64-linux-gnu,
# aarch64-linux-gnu, universal-macos, x86_64-windows-gnu (the zig-native release archives, under
# the target names lean_pq/abi.nim uses). A release stages all four (the workflow checks each
# "staged" line); CI stages the one it built.
#
# LLVM_STRIP and LLVM_AR name the LLVM tools (default llvm-strip and llvm-ar).
set -eu

if [ "$#" -ne 2 ]; then
    echo "usage: $0 NATIVE_ROOT OUTPUT_DIRECTORY" >&2
    exit 64
fi

native_root=$(CDPATH= cd -- "$1" && pwd)
output=$2
llvm_strip=${LLVM_STRIP:-llvm-strip}
llvm_ar=${LLVM_AR:-llvm-ar}

if [ -e "$output" ]; then
    echo "$output already exists" >&2
    exit 1
fi
mkdir -p "$output"
output=$(CDPATH= cd -- "$output" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Drops debug information from every object in a static archive. Universal
# macOS archives are stripped whole; other archives member by member, because llvm-strip rejects
# the short import members the Windows archive carries.
strip_archive() {
    archive=$1
    if [ "$(od -An -tx1 -N4 "$archive" | tr -d ' \n')" = cafebabe ]; then
        "$llvm_strip" --strip-debug "$archive"
        return
    fi
    members=$("$llvm_ar" t "$archive" | grep '\.o$')
    if [ -n "$(printf '%s\n' "$members" | sort | uniq -d)" ]; then
        echo "$archive has duplicate object names" >&2
        exit 1
    fi
    rm -rf "$work/members"
    mkdir "$work/members"
    # shellcheck disable=SC2086 # Rust's member names contain no whitespace.
    (
        cd "$work/members"
        "$llvm_ar" x "$archive" $members
        "$llvm_strip" --strip-debug $members
        "$llvm_ar" r "$archive" $members
    )
}

staged=0
for target in x86_64-linux-gnu aarch64-linux-gnu universal-macos x86_64-windows-gnu; do
    source="$native_root/$target/liblean_pq_native.a"
    if [ ! -f "$source" ]; then
        continue
    fi
    destination="$output/lean-pq-native-$target.a"
    install -m 0644 "$source" "$destination"
    strip_archive "$destination"
    echo "staged $target"
    echo "$target: $(wc -c < "$source") bytes, $(wc -c < "$destination") stripped"
    staged=$((staged + 1))
done
if [ "$staged" -eq 0 ]; then
    echo "no liblean_pq_native.a found under $native_root" >&2
    exit 1
fi
