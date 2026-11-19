#!/bin/sh
# Start a leanvm-sidecar in the background for the aggregation tests, wait until it listens, and
# print the environment they read (LEANVM_SIDECAR_SOCKET, LEANVM_SIDECAR_BIN), one line each, as
# $GITHUB_ENV takes them.
set -eu

if [ "$#" -ne 2 ]; then
    echo "usage: $0 SIDECAR_BINARY DIRECTORY" >&2
    exit 64
fi

binary=$(CDPATH= cd -- "$(dirname -- "$1")" && pwd)/$(basename -- "$1")
mkdir -p "$2"
chmod 700 "$2"
directory=$(CDPATH= cd -- "$2" && pwd)
chmod +x "$binary"
nohup "$binary" --socket "$directory/s.sock" > "$directory/sidecar.log" 2>&1 &
pid=$!
# The socket appears once the sidecar has warmed up.
waited=0
while [ ! -S "$directory/s.sock" ]; do
    if ! kill -0 "$pid" 2>/dev/null || [ "$waited" -ge 600 ]; then
        kill "$pid" 2>/dev/null || true
        cat "$directory/sidecar.log" >&2
        exit 1
    fi
    sleep 1
    waited=$((waited + 1))
done
echo "LEANVM_SIDECAR_SOCKET=$directory/s.sock"
echo "LEANVM_SIDECAR_BIN=$binary"
