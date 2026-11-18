#!/bin/sh
# Assemble the published Nimble package: this binding's package files plus one stripped native
# archive per supported platform, committed alone at the root of a parentless commit tagged
# bindings/nim/vVERSION. `nimble install`, a `requires` line and a nimbus-build-system submodule all
# consume that tag, so none of them needs a Rust toolchain.
#
# NATIVE_ROOT holds one directory per bundled target, each with liblean_pq_native.a:
# x86_64-linux-gnu, aarch64-linux-gnu, universal-macos, x86_64-windows-gnu (the zig-native release
# archives, under the directory names lean_pq/abi.nim selects from).
#
# OUTPUT_DIRECTORY receives:
#   repo/               scratch repository holding the tagged commit
#   nim-package.bundle  git bundle of the tag, for pushing it from another job
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
package_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
repo_dir=$(CDPATH= cd -- "$package_dir/../.." && pwd)
tag=bindings/nim/v$version
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

git -c init.defaultBranch=package init -q "$tree"
cp -R "$package_dir/lean_pq.nim" "$package_dir/lean_pq" "$package_dir/include" \
    "$package_dir/README.md" "$tree/"
cp "$repo_dir/LICENSE-MIT" "$repo_dir/LICENSE-APACHE" "$tree/"
cmp "$repo_dir/bindings/native/include/lean_pq_native.h" "$tree/include/lean_pq_native.h"
sed -e "s/^version\( *\)= \"[^\"]*\".*$/version\1= \"$version\"/" \
    "$package_dir/lean_pq.nimble" > "$tree/lean_pq.nimble"
grep -q "^version *= \"$version\"$" "$tree/lean_pq.nimble"

# A release bundles all four targets (the workflow checks each "bundled" line); CI packages the one
# it built.
bundled=0
for target in x86_64-linux-gnu aarch64-linux-gnu universal-macos x86_64-windows-gnu; do
    source="$native_root/$target/liblean_pq_native.a"
    if [ ! -f "$source" ]; then
        continue
    fi
    destination="$tree/native/$target/liblean_pq_native.a"
    mkdir -p "$(dirname -- "$destination")"
    install -m 0644 "$source" "$destination"
    strip_archive "$destination"
    echo "bundled $target"
    echo "$target: $(wc -c < "$source") bytes, $(wc -c < "$destination") stripped"
    bundled=$((bundled + 1))
done
if [ "$bundled" -eq 0 ]; then
    echo "no liblean_pq_native.a found under $native_root" >&2
    exit 1
fi

source_commit=$(git -C "$repo_dir" rev-parse HEAD)
git -C "$tree" add -A -f
GIT_AUTHOR_NAME='github-actions[bot]' \
    GIT_AUTHOR_EMAIL='41898282+github-actions[bot]@users.noreply.github.com' \
    GIT_AUTHOR_DATE=$(git -C "$repo_dir" log -1 --format=%cI) \
    GIT_COMMITTER_NAME='github-actions[bot]' \
    GIT_COMMITTER_EMAIL='41898282+github-actions[bot]@users.noreply.github.com' \
    GIT_COMMITTER_DATE=$(git -C "$repo_dir" log -1 --format=%cI) \
    git -C "$tree" commit -q -m "Nimble package lean_pq v$version" -m "Built from $source_commit."
git -C "$tree" tag "$tag"
git -C "$tree" bundle create -q "$output/nim-package.bundle" "refs/tags/$tag"
git -C "$tree" ls-tree -r -l --abbrev HEAD
echo "tagged $tag at $(git -C "$tree" rev-parse HEAD)"
