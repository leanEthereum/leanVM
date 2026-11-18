#!/bin/sh
# Build the lean-pq shared library for one platform bundled in the Java jar and stage it as
# NATIVE_DIR/PLATFORM/<library>, the layout `-PleanPqNativeDir=NATIVE_DIR` expects.
#   linux-x86_64, linux-aarch64: cargo-zigbuild against glibc 2.17 (needs Zig and cargo-zigbuild)
#   macos-universal:             x86_64 + arm64 slices joined with lipo (needs a macOS host)
#   windows-x86_64:              x86_64-pc-windows-gnu (needs a Windows host with MinGW-w64's gcc and
#                                objdump on PATH; run it from Git Bash)
set -eu

if [ "$#" -ne 2 ]; then
    echo "usage: $0 linux-x86_64|linux-aarch64|macos-universal|windows-x86_64 NATIVE_DIR" >&2
    exit 64
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/../../.." && pwd)
manifest="$repo_dir/bindings/native/Cargo.toml"
target_dir=${CARGO_TARGET_DIR:-"$repo_dir/target"}
platform=$1
out_dir="$2/$platform"

case "$platform" in
    linux-x86_64 | linux-aarch64 | macos-universal | windows-x86_64) ;;
    *)
        echo "unsupported platform: $platform" >&2
        exit 64
        ;;
esac

mkdir -p "$out_dir"
case "$platform" in
    linux-*)
        # Rust target triples without the glibc suffix, so .cargo/config.toml's per-target rustflags apply.
        rust_target=x86_64-unknown-linux-gnu
        if [ "$platform" = linux-aarch64 ]; then rust_target=aarch64-unknown-linux-gnu; fi
        cargo zigbuild --manifest-path "$manifest" --release --target "$rust_target.2.17"
        install -m 0644 "$target_dir/$rust_target/release/liblean_pq_native.so" "$out_dir/liblean_pq_native.so"
        newest=$(objdump -T "$out_dir/liblean_pq_native.so" | grep -o 'GLIBC_[0-9.]*' | sed 's/^GLIBC_//' | sort -uV | tail -n 1)
        if [ "$(printf '%s\n2.17\n' "$newest" | sort -V | tail -n 1)" != 2.17 ]; then
            echo "liblean_pq_native.so needs GLIBC_$newest, above the 2.17 baseline" >&2
            exit 1
        fi
        echo "newest glibc symbol version: GLIBC_$newest"
        ;;
    macos-universal)
        for target in x86_64-apple-darwin aarch64-apple-darwin; do
            cargo build --manifest-path "$manifest" --release --target "$target"
        done
        lipo -create -output "$out_dir/liblean_pq_native.dylib" \
            "$target_dir/x86_64-apple-darwin/release/liblean_pq_native.dylib" \
            "$target_dir/aarch64-apple-darwin/release/liblean_pq_native.dylib"
        lipo "$out_dir/liblean_pq_native.dylib" -verify_arch x86_64 arm64
        ;;
    windows-x86_64)
        cargo build --manifest-path "$manifest" --release --target x86_64-pc-windows-gnu
        install -m 0644 "$target_dir/x86_64-pc-windows-gnu/release/lean_pq_native.dll" "$out_dir/lean_pq_native.dll"
        # The DLL may import only what every Windows 10+ install ships: System32 DLLs and API sets.
        # MinGW runtime DLLs (libgcc, libwinpthread, libstdc++) and the Visual C++ redistributable
        # are not part of Windows, even where a build machine has copies in System32.
        dlls=$(objdump -p "$out_dir/lean_pq_native.dll" | sed -n 's/^[[:space:]]*DLL Name: //p' | tr -d '\r')
        if [ -z "$dlls" ]; then
            echo "objdump listed no DLL imports for lean_pq_native.dll" >&2
            exit 1
        fi
        system32="$(cygpath -u "${SYSTEMROOT:-C:\\Windows}")/System32"
        echo "lean_pq_native.dll imports:"
        foreign=0
        for dll in $dlls; do
            case $(printf '%s' "$dll" | tr '[:upper:]' '[:lower:]') in
                libgcc* | libwinpthread* | libstdc++* | vcruntime* | msvcp* | msvcr[0-9]* | concrt* | vcomp*) shipped=no ;;
                api-ms-win-* | ext-ms-win-*) shipped=yes ;;
                *) if [ -f "$system32/$dll" ]; then shipped=yes; else shipped=no; fi ;;
            esac
            echo "  $dll"
            if [ "$shipped" = no ]; then
                echo "lean_pq_native.dll imports $dll, which Windows does not ship" >&2
                foreign=1
            fi
        done
        if [ "$foreign" -ne 0 ]; then exit 1; fi
        ;;
esac
echo "staged $(ls "$out_dir")"
