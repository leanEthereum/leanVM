#!/bin/sh
# Assemble the published Go module: the committed bindings/go tree plus one stripped native archive
# per supported platform, committed alone on a parentless commit tagged bindings/go/vVERSION.
#
# NATIVE_ROOT holds the zig-native release archives: x86_64-linux-gnu, aarch64-linux-gnu,
# universal-macos and x86_64-windows-gnu, each with liblean_pq_native.a.
#
# OUTPUT_DIRECTORY receives:
#   repo/              scratch repository holding the tagged commit
#   go-module.bundle   git bundle of the tag, for pushing it from another job
#   proxy/             the module as `go mod download` fetches it from that tag, usable as
#                      GOPROXY=file://...
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
module=github.com/ethereum/lean-pq-bindings/bindings/go
tag=bindings/go/v$version
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
tree="$output/repo"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

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

git -c init.defaultBranch=module init -q "$tree"
git -C "$repo_dir" archive HEAD bindings/go | tar -x -C "$tree"
# The licenses live at the repository root; the module needs its own copy (pkg.go.dev requires one).
cp "$repo_dir/LICENSE-MIT" "$repo_dir/LICENSE-APACHE" "$tree/bindings/go/"
for pair in x86_64-linux-gnu:linux_amd64 aarch64-linux-gnu:linux_arm64 \
    universal-macos:darwin_universal x86_64-windows-gnu:windows_amd64; do
    source="$native_root/${pair%%:*}/liblean_pq_native.a"
    destination="$tree/bindings/go/internal/native/${pair#*:}/liblean_pq_native.a"
    mkdir -p "$(dirname -- "$destination")"
    install -m 0644 "$source" "$destination"
    strip_archive "$destination"
    echo "staged ${pair#*:}: $(wc -c < "$source") bytes, $(wc -c < "$destination") stripped"
done

source_commit=$(git -C "$repo_dir" rev-parse HEAD)
git -C "$tree" add -A -f
GIT_AUTHOR_NAME='github-actions[bot]' \
    GIT_AUTHOR_EMAIL='41898282+github-actions[bot]@users.noreply.github.com' \
    GIT_AUTHOR_DATE=$(git -C "$repo_dir" log -1 --format=%cI) \
    GIT_COMMITTER_NAME='github-actions[bot]' \
    GIT_COMMITTER_EMAIL='41898282+github-actions[bot]@users.noreply.github.com' \
    GIT_COMMITTER_DATE=$(git -C "$repo_dir" log -1 --format=%cI) \
    git -C "$tree" commit -q -m "Go module $module v$version" -m "Built from $source_commit."
git -C "$tree" tag "$tag"
git -C "$tree" bundle create -q "$output/go-module.bundle" "refs/tags/$tag"
echo "tagged $tag at $(git -C "$tree" rev-parse HEAD)"

# Fetch the module from the tag exactly as the Go proxy will, with the repository URL redirected to
# the scratch repository. The go command enforces the module zip limits here.
(
    cd "$work"
    GOMODCACHE="$work/modcache" GOPROXY=direct GOSUMDB=off GOFLAGS=-modcacherw \
        GIT_CONFIG_COUNT=1 \
        GIT_CONFIG_KEY_0="url.file://$tree.insteadOf" \
        GIT_CONFIG_VALUE_0=https://github.com/ethereum/lean-pq-bindings \
        go mod download -json "$module@v$version"
)
mv "$work/modcache/cache/download" "$output/proxy"

zip="$output/proxy/$module/@v/v$version.zip"
unzip -l "$zip"
unpacked=$(unzip -l "$zip" | tail -n 1 | awk '{print $1}')
echo "module zip: $(wc -c < "$zip") bytes compressed, $unpacked bytes uncompressed"
# Go rejects module zips over 500 MiB; keep well clear of that.
if [ "$unpacked" -gt $((250 * 1024 * 1024)) ]; then
    echo "the module is over 250 MiB uncompressed" >&2
    exit 1
fi
