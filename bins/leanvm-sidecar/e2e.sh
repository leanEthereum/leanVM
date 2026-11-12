#!/usr/bin/env bash
# End-to-end run of leanvm-sidecar through one language's client:
#
#   e2e.sh <rust|go|java|ts> <threads> [aggregate-log-inv-rate=2] [recurse-log-inv-rate=1]
#
# Starts the server with <threads> prover threads, aggregates 16 batches of 1500 leanXMSS
# signatures one after the other, then recurses the 16 proofs into one. Each step prints its
# request, its response and the time it took, as the client sees it.
#
# The signatures are testdata/signatures-24000.bin: 24000 signers, each signing one of 4 messages;
# examples/gen_signatures.rs regenerates the file if it is missing. Java uses the JDK on PATH, or
# else the eclipse-temurin:21-jdk container through docker. TypeScript needs node, npm and a C
# compiler (clients/typescript/build.sh).
set -euo pipefail

usage() {
    sed -n '2,4p' "$0" >&2
    exit 2
}
[[ $# -ge 2 && $# -le 4 ]] || usage
lang=$1
threads=$2
aggregate_rate=${3:-2}
recurse_rate=${4:-1}
[[ $lang == rust || $lang == go || $lang == java || $lang == ts ]] || usage

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
cd "$root"
work=$root/target/leanvm-sidecar
signatures=$here/testdata/signatures-24000.bin
channel=/dev/shm/leanvm-e2e-$$
mkdir -p "$work"

cargo build --release -p leanvm-sidecar -p leanvm_sidecar_client --examples --bins
if [[ ! -f $signatures ]]; then
    echo "generating 24000 signatures into $signatures"
    mkdir -p "$here/testdata"
    target/release/examples/gen_signatures 24000 "$signatures.tmp"
    mv "$signatures.tmp" "$signatures"
fi

# Build the runner before the server starts, so the timings hold no compilation.
case $lang in
rust) runner=(target/release/examples/e2e) ;;
go)
    (cd "$here/clients/go" && go build -o "$work/e2e-go" ./e2e)
    runner=("$work/e2e-go")
    ;;
java)
    if command -v javac >/dev/null; then
        javac -d "$work/java" "$here"/clients/java/leanvmsidecar/*.java
        runner=(java -cp "$work/java" leanvmsidecar.E2e)
    else
        jdk=(docker run --rm -u "$(id -u):$(id -g)" -v /dev/shm:/dev/shm -v "$root:$root" -w "$root" eclipse-temurin:21-jdk)
        "${jdk[@]}" javac -d "$work/java" "$here"/clients/java/leanvmsidecar/Client.java "$here"/clients/java/leanvmsidecar/E2e.java
        runner=("${jdk[@]}" java -cp "$work/java" leanvmsidecar.E2e)
    fi
    ;;
ts)
    "$here/clients/typescript/build.sh"
    runner=(node "$here/clients/typescript/dist/e2e.js")
    ;;
esac

rm -f "$channel"
target/release/leanvm-sidecar --path "$channel" --threads "$threads" --arena-mib 256 &
server=$!
trap 'kill $server 2>/dev/null || true; wait $server 2>/dev/null || true; rm -f "$channel"' EXIT

# The server creates the channel once the prover is warm.
until [[ -f $channel ]]; do
    kill -0 $server 2>/dev/null || { echo "leanvm-sidecar exited" >&2; exit 1; }
    sleep 0.1
done

echo "client $lang, $threads threads, aggregate rate $aggregate_rate, recurse rate $recurse_rate"
"${runner[@]}" "$channel" "$signatures" "$aggregate_rate" "$recurse_rate"
