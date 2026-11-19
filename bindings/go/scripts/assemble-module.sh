#!/bin/sh
# Assemble the published Go module: the committed bindings/go tree plus one stripped native archive
# per supported platform, as the module proxy files leanvm.org serves (never committed to git).
#
# NATIVE_ROOT holds the zig-native release archives: x86_64-linux-gnu, aarch64-linux-gnu,
# universal-macos and x86_64-windows-gnu, each with liblean_pq_native.a.
#
# OUTPUT_DIRECTORY/proxy receives the module's list, .info, .mod and .zip in the GOPROXY layout,
# usable as GOPROXY=file://...
#
# LLVM_STRIP and LLVM_AR name the LLVM tools (default llvm-strip and llvm-ar).
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
llvm_strip=${LLVM_STRIP:-llvm-strip}
llvm_ar=${LLVM_AR:-llvm-ar}

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

# Drops debug information from every object in a static archive. Universal macOS archives are
# stripped whole; other archives member by member, because llvm-strip rejects the short import
# members the Windows archive carries.
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
    strip_archive "$destination"
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
