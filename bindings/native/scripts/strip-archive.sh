#!/bin/sh
# Drop debug information from static bridge archives, in place. Universal macOS archives are
# stripped whole; others member by member, because llvm-strip rejects the short import members the
# Windows archive carries.
#
# Uses rustup's llvm-tools (`rustup component add llvm-tools`) unless LLVM_STRIP and LLVM_AR are set.
set -eu

if [ "$#" -eq 0 ]; then
    echo "usage: $0 ARCHIVE..." >&2
    exit 64
fi

llvm_bin="$(rustc --print sysroot)/lib/rustlib/$(rustc -vV | sed -n 's/^host: //p')/bin"
llvm_strip=${LLVM_STRIP:-$llvm_bin/llvm-strip}
llvm_ar=${LLVM_AR:-$llvm_bin/llvm-ar}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

for archive in "$@"; do
    archive=$(CDPATH= cd -- "$(dirname -- "$archive")" && pwd)/$(basename -- "$archive")
    if [ "$(od -An -tx1 -N4 "$archive" | tr -d ' \n')" = cafebabe ]; then
        "$llvm_strip" --strip-debug "$archive"
        continue
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
done
