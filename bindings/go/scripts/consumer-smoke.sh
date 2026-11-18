#!/bin/sh
# Prove an assembled module works as a dependency with no Rust toolchain: a fresh module fetches it
# from PROXY_DIR (a GOPROXY=file:// tree from assemble-module.sh) and runs the README example.
set -eu

if [ "$#" -ne 2 ]; then
    echo "usage: $0 PROXY_DIR VERSION" >&2
    exit 64
fi

proxy=$(CDPATH= cd -- "$1" && pwd)
version=$2
module=github.com/ethereum/lean-pq-bindings/bindings/go
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
readme="$script_dir/../README.md"
project=$(mktemp -d)
trap 'rm -rf "$project"' EXIT

# Go on Windows needs a drive-letter file URL, not the shell's POSIX path.
if command -v cygpath >/dev/null 2>&1; then
    proxy_url="file:///$(cygpath -m "$proxy")"
else
    proxy_url="file://$proxy"
fi

if command -v cargo >/dev/null 2>&1 || command -v rustc >/dev/null 2>&1; then
    echo "a Rust toolchain is on PATH; this check must run without one" >&2
    exit 1
fi

export GOPROXY="$proxy_url"
# Versions under test are not in the public checksum database yet.
export GONOSUMDB=github.com/ethereum/lean-pq-bindings
export CGO_ENABLED=1
go version
echo "C compiler: $(go env CC)"

cd "$project"
go mod init example.com/consumer
go get "$module@v$version"

# The README's example is the program; it exits non-zero on any error.
sed -n '/^## Example$/,$p' "$readme" | sed -n '/^```go$/,/^```$/p' | sed '1d;$d' > main.go
test -s main.go

# -ldflags=-v logs the external link command, which shows the platform's link line.
binary=consumer$(go env GOEXE)
if ! go build -ldflags=-v -o "$binary" . 2> build.log; then
    cat build.log >&2
    exit 1
fi
grep '^host link:' build.log
"./$binary"
echo "consumer built and ran against $module@v$version"
