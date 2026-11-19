#!/bin/sh
# Assemble the Zig package tarball that consumers add with `zig fetch --save URL`.
#
# NATIVE_ROOT holds one directory per bundled target, each with liblean_pq_native.a:
# x86_64-linux-gnu, aarch64-linux-gnu, universal-macos, x86_64-windows-gnu (the names build.zig
# selects from).
set -eu

if [ "$#" -ne 3 ]; then
    echo "usage: $0 VERSION NATIVE_ROOT OUTPUT_TARBALL" >&2
    exit 64
fi

version=$1
native_root=$2
output=$3
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
package_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)

case $version in
    *[!0-9.]* | '' | .* | *. | *..*)
        echo "version must look like 1.2.3, got '$version'" >&2
        exit 64
        ;;
esac

stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT
root="$stage/lean-pq-zig-$version"
mkdir -p "$root/native"

cp "$package_dir/build.zig" "$package_dir/README.md" "$root/"
cp "$package_dir/../../LICENSE-MIT" "$package_dir/../../LICENSE-APACHE" "$root/"
cp -R "$package_dir/include" "$package_dir/src" "$root/"
sed -e "s/^    \.version = \"[^\"]*\",$/    .version = \"$version\",/" \
    -e 's/^    \.paths = \.{ \(.*\) },$/    .paths = .{ \1, "native", "LICENSE-MIT", "LICENSE-APACHE" },/' \
    "$package_dir/build.zig.zon" > "$root/build.zig.zon"
grep -q "^    \.version = \"$version\",$" "$root/build.zig.zon"
grep -q '"native", "LICENSE-MIT", "LICENSE-APACHE" },$' "$root/build.zig.zon"

bundled=0
for target in x86_64-linux-gnu aarch64-linux-gnu universal-macos x86_64-windows-gnu; do
    if [ -f "$native_root/$target/liblean_pq_native.a" ]; then
        mkdir -p "$root/native/$target"
        install -m 0644 "$native_root/$target/liblean_pq_native.a" "$root/native/$target/liblean_pq_native.a"
        echo "bundled $target"
        bundled=$((bundled + 1))
    fi
done
if [ "$bundled" -eq 0 ]; then
    echo "no liblean_pq_native.a found under $native_root" >&2
    exit 1
fi

mkdir -p "$(dirname -- "$output")"
tar -C "$stage" -czf "$output" "lean-pq-zig-$version"
echo "wrote $output"
