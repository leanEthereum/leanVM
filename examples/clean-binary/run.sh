#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

if (( $# > 1 )); then
    echo "usage: bash run.sh [instances, default 1024]" >&2
    exit 2
fi
n="${1:-1024}"
out=artifacts
mkdir -p "$out"

python3 - "$n" "$out/inputs.json" <<'PY'
import json, random, sys
n, path = int(sys.argv[1]), sys.argv[2]
rng = random.Random(1)
word = lambda: f"{rng.getrandbits(32):08x}"
instances = [{"h": [word() for _ in range(8)], "m": [word() for _ in range(16)]} for _ in range(n)]
json.dump({"instances": instances}, open(path, "w"))
PY

(
    cd clean
    lake build clean_export
    lake exe clean_export r1cs "../$out/circuit.r1cs"
    lake exe clean_export witness "../$out/inputs.json" "../$out/witness.bin"
)
cargo +1.97 build --release -p binary-spartan-cli
cli=../../target/release/binary-spartan
"$cli" prove "$out/circuit.r1cs" "$out/witness.bin" --self-check --repeat 3
"$cli" prove "$out/circuit.r1cs" "$out/witness.bin" --spark --self-check --repeat 3
