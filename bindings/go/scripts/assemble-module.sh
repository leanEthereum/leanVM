#!/bin/sh
# Assemble the published Go module: the committed bindings/go tree plus one stripped native archive
# per supported platform, as the module proxy files leanvm.org serves (never committed to git).
#
# NATIVE_ROOT holds the zig-native release archives: x86_64-linux-gnu, aarch64-linux-gnu,
# universal-macos and x86_64-windows-gnu, each with liblean_pq_native.a.
#
# OUTPUT_DIRECTORY/proxy receives the module's list, .info, .mod and .zip in the GOPROXY layout,
# usable as GOPROXY=file://...
set -eu

if [ "$#" -ne 3 ]; then
    echo "usage: $0 VERSION NATIVE_ROOT OUTPUT_DIRECTORY" >&2
    exit 64
fi

version=$1
native_root=$(CDPATH= cd -- "$2" && pwd)
output=$3
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/../../.." && pwd)
module=leanvm.org/go

case $version in
    *[!0-9.]* | '' | .* | *. | *..*)
        echo "version must look like 1.2.3, got '$version'" >&2
        exit 64
        ;;
esac

if [ -e "$output" ]; then
    echo "$output already exists" >&2
    exit 1
fi
mkdir -p "$output"
output=$(CDPATH= cd -- "$output" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
tree="$work/zip/$module@v$version"

git -C "$repo_dir" archive HEAD bindings/go | tar -x -C "$work"
mkdir -p "$(dirname -- "$tree")"
mv "$work/bindings/go" "$tree"
# The licenses live at the repository root; the module needs its own copy (pkg.go.dev requires one).
cp "$repo_dir/LICENSE-MIT" "$repo_dir/LICENSE-APACHE" "$tree/"
for pair in x86_64-linux-gnu:linux_amd64 aarch64-linux-gnu:linux_arm64 \
    universal-macos:darwin_universal x86_64-windows-gnu:windows_amd64; do
    source="$native_root/${pair%%:*}/liblean_pq_native.a"
    destination="$tree/internal/native/${pair#*:}/liblean_pq_native.a"
    mkdir -p "$(dirname -- "$destination")"
    install -m 0644 "$source" "$destination"
    sh "$repo_dir/bindings/native/scripts/strip-archive.sh" --strip-debug "$destination"
    echo "staged ${pair#*:}: $(wc -c < "$source") bytes, $(wc -c < "$destination") stripped"
done

# The module proxy's files for this version. Every file in a module zip sits under MODULE@VERSION/.
versions="$output/proxy/$module/@v"
mkdir -p "$versions"
(cd "$work/zip" && find . -type f | LC_ALL=C sort | sed 's|^\./||' | zip -q -X -@ "$versions/v$version.zip")
cp "$tree/go.mod" "$versions/v$version.mod"
printf '{"Version":"v%s","Time":"%s"}\n' "$version" "$(git -C "$repo_dir" log -1 --format=%cI)" > "$versions/v$version.info"
printf 'v%s\n' "$version" > "$versions/list"

# Fetch the module from these files exactly as the go command will from leanvm.org, which enforces
# the module zip's rules and limits.
(
    cd "$work"
    GOMODCACHE="$work/modcache" GOPROXY="file://$output/proxy" GOSUMDB=off GOFLAGS=-modcacherw \
        go mod download -json "$module@v$version"
)

zip="$versions/v$version.zip"
unzip -l "$zip"
unpacked=$(unzip -l "$zip" | tail -n 1 | awk '{print $1}')
echo "module zip: $(wc -c < "$zip") bytes compressed, $unpacked bytes uncompressed"
# Go rejects module zips over 500 MiB; keep well clear of that.
if [ "$unpacked" -gt $((250 * 1024 * 1024)) ]; then
    echo "the module is over 250 MiB uncompressed" >&2
    exit 1
fi
