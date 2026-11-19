#!/bin/sh
# Install leanvm-sidecar, the process the leanVM bindings aggregate through, as ROOT/bin/leanvm-sidecar
# (ROOT defaults to ~/.leanvm): the release binary for this platform, or with --build one built from
# source for this CPU, which proves faster (needs Rust).
#
#   curl -fsSL https://raw.githubusercontent.com/leanEthereum/leanVM/main/bindings/scripts/install-sidecar.sh | sh -s -- [--version X.Y.Z] [--build] [--root ROOT]
#
# --version picks the bindings release (default: the latest); use the bindings' own version.
# LEANVM_SIDECAR_RELEASES replaces the release download URL, for mirrors and tests.
set -eu

repo=leanEthereum/leanVM
version=
build=
root=$HOME/.leanvm
while [ "$#" -gt 0 ]; do
    case $1 in
        --version) version=${2:?--version takes X.Y.Z}; shift 2 ;;
        --build) build=1; shift ;;
        --root) root=${2:?--root takes a directory}; shift 2 ;;
        *) echo "usage: install-sidecar.sh [--version X.Y.Z] [--build] [--root ROOT]" >&2; exit 64 ;;
    esac
done

if [ -z "$version" ]; then
    version=$(curl -fsSL "https://api.github.com/repos/$repo/releases?per_page=100" |
        sed -n 's/.*"tag_name": *"bindings-v\([0-9.]*\)".*/\1/p' | head -n 1)
    [ -n "$version" ] || { echo "found no bindings release; pass --version" >&2; exit 1; }
fi
mkdir -p "$root/bin"
binary=$root/bin/leanvm-sidecar

if [ -n "$build" ]; then
    command -v cargo >/dev/null || { echo "--build needs Rust: https://rustup.rs" >&2; exit 1; }
    RUSTFLAGS="-C target-cpu=native" cargo install --locked --force --root "$root" \
        --git "https://github.com/$repo" --tag "bindings-v$version" leanvm-sidecar --features experimental_prover
else
    case $(uname -s)-$(uname -m) in
        Linux-x86_64)
            # The release binary needs AVX2 and PCLMULQDQ.
            if ! grep -q ' avx2' /proc/cpuinfo || ! grep -q ' pclmulqdq' /proc/cpuinfo; then
                echo "this CPU lacks AVX2 or PCLMULQDQ: rerun with --build" >&2
                exit 1
            fi
            asset=leanvm-sidecar-x86_64-linux ;;
        Linux-aarch64 | Linux-arm64) asset=leanvm-sidecar-aarch64-linux ;;
        Darwin-arm64) asset=leanvm-sidecar-aarch64-macos ;;
        *) echo "no prebuilt sidecar for $(uname -s) $(uname -m): rerun with --build" >&2; exit 1 ;;
    esac
    releases=${LEANVM_SIDECAR_RELEASES:-https://github.com/$repo/releases/download}
    curl -fsSL -o "$binary.part" "$releases/bindings-v$version/$asset"
    chmod +x "$binary.part"
    mv "$binary.part" "$binary"
fi

echo "installed $binary ($version)"
echo "run it: mkdir -p -m 700 ~/.leanvm && $binary --socket ~/.leanvm/sidecar.sock"
