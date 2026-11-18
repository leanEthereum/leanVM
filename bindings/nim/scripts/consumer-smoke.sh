#!/bin/sh
# Prove an assembled package works as a Nimble dependency with no Rust toolchain: a fresh package
# requires the tag through the GitHub URL, redirected to PACKAGE_REPO (the scratch repository from
# assemble-package.sh), and builds and runs the README example.
set -eu

if [ "$#" -ne 2 ]; then
    echo "usage: $0 PACKAGE_REPO VERSION" >&2
    exit 64
fi

package_repo=$(CDPATH= cd -- "$1" && pwd)
version=$2
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
readme="$script_dir/../README.md"
project=$(mktemp -d)
trap 'rm -rf "$project"' EXIT

# Git on Windows needs a drive-letter file URL, not the shell's POSIX path.
if command -v cygpath >/dev/null 2>&1; then
    package_url="file:///$(cygpath -m "$package_repo")"
else
    package_url="file://$package_repo"
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

cd "$project"
mkdir src
# The README's install line, at the version under test (a dry run's 0.0.0 is not in the README).
grep -q '^requires "https://github.com/leanEthereum/leanVM#bindings/nim/v[0-9.]*"$' "$readme"
requirement="https://github.com/leanEthereum/leanVM#bindings/nim/v$version"
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

nimble --nimbleDir:"$project/nimbledir" -y build -d:release --mm:refc --threads:on
if [ -f consumer.exe ]; then ./consumer.exe; else ./consumer; fi
echo "consumer built and ran against lean_pq v$version"
