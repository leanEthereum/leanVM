#!/bin/sh
# Prove the package works as a Nimble dependency with no Rust toolchain: a fresh package requires
# this tree's bindings/nim at tag bindings-vVERSION through the GitHub URL (redirected to a scratch
# repository), its first build downloads the archive from NATIVE_DIR (the release's
# lean-pq-native-TARGET.a files, from stage-release.sh), and it builds and runs the README example.
set -eu

if [ "$#" -ne 2 ]; then
    echo "usage: $0 NATIVE_DIR VERSION" >&2
    exit 64
fi

native_dir=$(CDPATH= cd -- "$1" && pwd)
version=$2
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/../../.." && pwd)
readme="$script_dir/../README.md"
project=$(mktemp -d)
trap 'rm -rf "$project"' EXIT

# The tagged repository: this commit's bindings/nim, at the path the requirement names.
git -c init.defaultBranch=main init -q "$project/repo"
git -C "$repo_dir" archive HEAD bindings/nim | tar -x -C "$project/repo"
git -C "$project/repo" add -A
git -C "$project/repo" -c user.name=consumer -c user.email=consumer@example.com commit -q -m tree
git -C "$project/repo" tag "bindings-v$version"

# Git and curl on Windows need drive-letter file URLs, not the shell's POSIX paths.
if command -v cygpath >/dev/null 2>&1; then
    package_url="file:///$(cygpath -m "$project/repo")"
    native_url="file:///$(cygpath -m "$native_dir")"
else
    package_url="file://$project/repo"
    native_url="file://$native_dir"
fi

if command -v cargo >/dev/null 2>&1 || command -v rustc >/dev/null 2>&1; then
    echo "a Rust toolchain is on PATH; this check must run without one" >&2
    exit 1
fi

nim --version | head -n 1
nimble --version | head -n 1

export GIT_CONFIG_COUNT=1
export GIT_CONFIG_KEY_0="url.$package_url.insteadOf"
export GIT_CONFIG_VALUE_0=https://github.com/leanEthereum/leanVM

mkdir "$project/consumer"
cd "$project/consumer"
mkdir src
# The README's install line, at the version under test (a dry run's 0.0.0 is not in the README).
grep -q '^requires "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v[0-9.]*"$' "$readme"
requirement="https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v$version"
cat > consumer.nimble <<EOF
version = "0.1.0"
author = "consumer"
description = "lean_pq consumer smoke test"
license = "MIT"
srcDir = "src"
bin = @["consumer"]

requires "nim >= 2.2.12"
requires "$requirement"
EOF

# The README's example is the program: it asserts its own results.
sed -n '/^## Example$/,/^## /p' "$readme" | sed -n '/^```nim$/,/^```$/p' | sed '1d;$d' > src/consumer.nim
test -s src/consumer.nim

nimble --nimbleDir:"$project/nimbledir" -y build -d:release --mm:refc --threads:on -d:leanPqNativeUrl="$native_url"
# The archive the first build downloaded into the installed package.
ls -l "$project"/nimbledir/pkgs2/lean_pq-*/native/*/liblean_pq_native.a
if [ -f consumer.exe ]; then ./consumer.exe; else ./consumer; fi
echo "consumer built and ran against lean_pq v$version"
