#!/usr/bin/env bash
# End-to-end run of leanvm-sidecar through one language's client:
#
#   e2e.sh <rust|go|java|ts|nim> <threads> [--signatures N] [--aggregate-rate R] [--recurse-rate R]
#
#   --signatures      signatures per batch, 1 to 1500 (default 1440)
#   --aggregate-rate  log_inv_rate of the aggregations (default 2)
#   --recurse-rate    log_inv_rate of the recursion (default 1)
#
# Starts the server with <threads> prover threads, aggregates 16 batches of leanXMSS signatures
# one after the other, then recurses the 16 proofs into one and verifies it. Each step
# prints its request, its response and the time it took, as the client sees it.
#
# The signatures are testdata/signatures-24000.bin: 24000 signers, each signing one of 4 messages;
# examples/gen_signatures.rs regenerates the file if it is missing. Java uses the JDK on PATH, or
# else the eclipse-temurin:21-jdk container through docker. TypeScript needs node, npm and a C
# compiler (clients/typescript/build.sh). Nim uses the nim on PATH, or else the nimlang/nim:2.2.0
# container through docker.
set -euo pipefail

usage() {
    sed -n '2,8p' "$0" >&2
    exit 2
}
[[ $# -ge 2 ]] || usage
lang=$1
threads=$2
shift 2
per_batch=1440
aggregate_rate=2
recurse_rate=1
while [[ $# -gt 0 ]]; do
    [[ $# -ge 2 ]] || usage
    case $1 in
    --signatures) per_batch=$2 ;;
    --aggregate-rate) aggregate_rate=$2 ;;
    --recurse-rate) recurse_rate=$2 ;;
    *) usage ;;
    esac
    shift 2
done
# The test file holds 16 batches of at most 1500.
[[ $per_batch =~ ^[0-9]+$ ]] && ((per_batch >= 1 && per_batch <= 1500)) || usage
[[ $lang == rust || $lang == go || $lang == java || $lang == ts || $lang == nim ]] || usage

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
nim)
    build=(nim c -d:release --hints:off --nimcache:"$work/nimcache" -o:"$work/e2e-nim" "$here/clients/nim/e2e.nim")
    if command -v nim >/dev/null; then
        "${build[@]}"
        runner=("$work/e2e-nim")
    else
        # Built against the container's libc, so run there too.
        box=(docker run --rm -u "$(id -u):$(id -g)" -e HOME=/tmp -v /dev/shm:/dev/shm -v "$root:$root" -w "$root" nimlang/nim:2.2.0)
        "${box[@]}" "${build[@]}"
        runner=("${box[@]}" "$work/e2e-nim")
    fi
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

echo "client $lang, $threads threads, $per_batch signatures per batch, aggregate rate $aggregate_rate, recurse rate $recurse_rate"
"${runner[@]}" "$channel" "$signatures" "$aggregate_rate" "$recurse_rate" "$per_batch"
