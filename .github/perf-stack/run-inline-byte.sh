#!/bin/bash
set -euo pipefail
mkdir -p /tmp/inline-byte-binaries
export RUSTFLAGS='-C target-cpu=native'
export CARGO_NET_GIT_FETCH_WITH_CLI=true
for spec in 'before:ee8267e6d1a939cf5c5789608a8cd27fd5ffd1d0' 'after:e38b2673cfdde783b2797c8c09030b185d7799e7'; do
 IFS=: read -r label revision <<< "$spec"
 git checkout -f "$revision"
 cargo build --release --locked -p leanvm-cli
 cp target/release/leanvm "/tmp/inline-byte-binaries/$label"
done
lscpu
for round in 1 2 3; do
 if [[ "$round" == 2 ]]; then labels=(after before); else labels=(before after); fi
 for label in "${labels[@]}"; do
  printf '\nROUND %s REVISION %s\n' "$round" "$label"
  LEANVM_NUM_THREADS=1 "/tmp/inline-byte-binaries/$label" --cooldown 0 leanxmss --n 100 --repeat 1 --tracing
 done
done
