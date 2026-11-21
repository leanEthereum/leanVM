#!/bin/sh
# Strip static bridge archives in place: drop the LLVM bitcode that Rust's prebuilt
# compiler_builtins objects carry, which Go refuses in a cgo linker input since Go 1.27, and with
# --strip-debug, debug information too. Universal macOS archives are stripped whole; others member
# by member, because llvm-objcopy rejects the short import members the Windows archive carries.
# llvm-objcopy, not llvm-strip: llvm-strip also drops every symbol unless told to strip something.
#
# Uses rustup's llvm-tools (`rustup component add llvm-tools`) unless LLVM_OBJCOPY and LLVM_AR are
# set.
set -eu

# The bitcode sections, as ELF and COFF name them and as Mach-O does (segment __LLVM). Naming a
# section a file lacks is no error, so every archive takes all four.
flags="--remove-section=.llvmbc --remove-section=.llvmcmd"
flags="$flags --remove-section=__LLVM,__bitcode --remove-section=__LLVM,__cmdline"
if [ "${1-}" = --strip-debug ]; then
    flags="$flags --strip-debug"
    shift
fi
if [ "$#" -eq 0 ]; then
    echo "usage: $0 [--strip-debug] ARCHIVE..." >&2
    exit 64
fi

llvm_bin="$(rustc --print sysroot)/lib/rustlib/$(rustc -vV | sed -n 's/^host: //p')/bin"
llvm_objcopy=${LLVM_OBJCOPY:-$llvm_bin/llvm-objcopy}
llvm_ar=${LLVM_AR:-$llvm_bin/llvm-ar}
if [ ! -x "$llvm_objcopy" ] || [ ! -x "$llvm_ar" ]; then
    echo "$llvm_objcopy or $llvm_ar is missing: run rustup component add llvm-tools" >&2
    exit 1
fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

for archive in "$@"; do
    archive=$(CDPATH= cd -- "$(dirname -- "$archive")" && pwd)/$(basename -- "$archive")
    if [ "$(od -An -tx1 -N4 "$archive" | tr -d ' \n')" = cafebabe ]; then
        # shellcheck disable=SC2086 # The flags contain no whitespace.
        "$llvm_objcopy" $flags "$archive"
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
        for member in $members; do
            "$llvm_objcopy" $flags "$member"
        done
        "$llvm_ar" r "$archive" $members
    )
done
