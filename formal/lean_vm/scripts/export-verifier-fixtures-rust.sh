#!/usr/bin/env bash
# Prove small guest programs with the leanVM Rust prover and write each proof in the
# format the Python verifier and the `verifier` crate read (`python-verifier/verifier.py`,
# `Proof.load` and `main`; `crates/verifier/src/transcript.rs`, `Proof::load`; and
# `crates/leanvm_core/tests/verifiers/python_verifier.rs`, `encode` and `test_python_verifier`,
# at leanVM 127510d14c98ade4e8a97646c44fa7f1ff5e752d):
#
#   bytecode.bin          the bytecode table, little-endian 64-bit words;
#   public_input.bin      the public input's two halves, 16 bytes each (c0, c1 little-endian);
#   stream.bin            the raw scalar stream, 24-byte little-endian E elements;
#   merkle_openings.bin   every opening in order: its leaf words, then its sibling digests.
#
# The proof is the RAW proof: the wire proof's scalar stream, and the Merkle path of every query
# the Rust `verify` walked (`verifier::Summary::merkle_paths`), written exactly as `encode` in
# python_verifier.rs writes them. The guests are that test's program at smaller loop counts and
# crates/lean_compiler/tests/programs/fibonacci.py, read from the source tree. Every proof is
# verified by the Rust `cpu::verify` before it is written and by the Python verifier
# before the script returns. The fixtures are consumed by scripts/fuzz-verifier.py, which runs
# the Lean and the Rust verifier on them and on mutations of them.
#
# Usage: scripts/export-verifier-fixtures-rust.sh <output dir> [--corpus]
#
# With `--corpus`, the fixtures are instead every program of crates/lean_compiler/tests/programs
# that declares its public input (with its `# witness` annotations), and the chain at 16, 1000 and
# 5000 loop steps, each at the four rates: the differential fuzzing corpus (not committed).
#
# The prover and the verifiers are those of the containing leanVM commit. Requires `cargo` and
# `python3`.
set -euo pipefail

checkout="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
out="${1:?usage: $0 <output dir> [--corpus]}"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/src" "$out"
out="$(cd "$out" && pwd)"
cp "$checkout/Cargo.lock" "$work/Cargo.lock"
# The workspace's `target-cpu=native`, so that the prover runs its vectorized kernels.
mkdir -p "$work/.cargo"
cp "$checkout/.cargo/config.toml" "$work/.cargo/config.toml"

cat > "$work/Cargo.toml" <<EOF
[package]
name = "export-verifier-fixtures"
version = "0.0.0"
edition = "2024"

[workspace]

[dependencies]
leanvm_core = { path = "$checkout/crates/leanvm_core" }
lean_compiler = { path = "$checkout/crates/lean_compiler" }
primitives = { path = "$checkout/crates/primitives" }
verifier = { path = "$checkout/crates/verifier" }

[profile.release]
lto = "thin"
codegen-units = 1
EOF

cat > "$work/src/main.rs" <<'EOF'
use lean_compiler::{compile, parse, parse_const, parse_with_replacements};
use leanvm_core::cpu::{Program, prove, public_input_bytes, verify};
use primitives::field::{F64, F192, g_pow};
use std::collections::BTreeMap;
use std::path::Path;

// The program of crates/leanvm_core/tests/verifiers/python_verifier.rs, its loop count a parameter.
const CHAIN: &str = r#"
from snark_lib import *

LOOP_STEPS = LOOP_STEPS_PLACEHOLDER

def mix(value, tag):
    # A JUMP condition is K-valued (a g-power here), never an arbitrary word.
    if tag == 0:
        return value
    return value * GEN + value

def main():
    seed = [5, 7]
    digest = StackBuf(2)
    blake2s(seed, seed, digest)

    chain = HeapBuf(LOOP_STEPS + 1)
    chain[1] = digest[0]
    for index in mul_range(1, GEN ** LOOP_STEPS):
        chain[index * GEN] = mix(chain[index] + index, index) + index

    public = GEN ** 0
    public[1] = chain[GEN ** LOOP_STEPS]
    public[GEN] = mix(digest[1], GEN ** 0)
    return
"#;

// The public input the program computes (python_verifier.rs, `public_input`).
fn chain_public_input(loop_steps: usize) -> [F192; 2] {
    use leanvm_core::hash_flock::{FINAL_FLAG, IV, PINNED_T, compression, digest, metadata};

    let seed = [F64(5), F64::ZERO, F64(7), F64::ZERO];
    let metadata = metadata(PINNED_T, FINAL_FLAG, 0);
    let digest = digest(&compression(seed, seed, IV, metadata));
    let digest = [
        F192::new(digest[0].0, digest[1].0, 0),
        F192::new(digest[2].0, digest[3].0, 0),
    ];
    let mut value = digest[0];
    let mut index = F192::ONE;
    let generator = F192::from(g_pow(1));
    for _ in 0..loop_steps {
        let candidate = value + index;
        let product = candidate * generator;
        value = (if product == F192::ZERO {
            candidate
        } else {
            product + candidate
        }) + index;
        index *= generator;
    }
    [value, digest[1] * generator + digest[1]]
}

fn chain(loop_steps: usize) -> (Program, [F192; 2]) {
    let replacements = BTreeMap::from([("LOOP_STEPS_PLACEHOLDER".to_string(), loop_steps.to_string())]);
    let ast = parse_with_replacements(CHAIN, &replacements).expect("parse zkDSL program");
    (compile(&ast), chain_public_input(loop_steps))
}

// crates/lean_compiler/tests/programs/fibonacci.py, whose header gives its public input.
fn fibonacci(checkout: &Path) -> (Program, [F192; 2]) {
    let source = std::fs::read_to_string(checkout.join("crates/lean_compiler/tests/programs/fibonacci.py"))
        .expect("read fibonacci.py");
    assert!(source.contains("# public_input: GEN ** 89, GEN ** 89"));
    let ast = parse_with_replacements(&source, &BTreeMap::new()).expect("parse zkDSL program");
    let out = F192::from(g_pow(89));
    (compile(&ast), [out, out])
}

// A program of crates/lean_compiler/tests/programs with its `# public_input:` and `# witness`
// annotations, read as crates/lean_compiler/tests/suite/py_source.rs reads them; `None` for a
// program without a declared public input.
fn suite_program(path: &Path) -> Option<(Program, [F192; 2])> {
    let source = std::fs::read_to_string(path).expect("read suite program");
    let header = source.lines().find_map(|line| line.trim().strip_prefix("# public_input:"))?;
    let parts: Vec<&str> = header.split(',').collect();
    assert_eq!(parts.len(), 2, "public input of {}", path.display());
    let public_input = [parse_const(parts[0]).expect("public input"), parse_const(parts[1]).expect("public input")];
    let ast = parse(&source).expect("parse suite program");
    let mut program = compile(&ast);
    let mut streams: BTreeMap<String, Vec<Vec<F192>>> = BTreeMap::new();
    for rest in source.lines().filter_map(|line| line.trim().strip_prefix("# witness ")) {
        let (name, values) = rest.split_once(':').expect("`# witness` needs `name: values`");
        let entry = values.split(',').map(|v| parse_const(v).expect("witness value")).collect();
        streams.entry(name.trim().to_string()).or_default().push(entry);
    }
    for (stream, entries) in streams {
        program.set_witness(stream, entries);
    }
    Some((program, public_input))
}

// The corpus: every suite program with a declared public input, and the chain at three sizes, each
// at the four rates.
fn corpus(checkout: &Path) -> Vec<(String, (Program, [F192; 2]), usize)> {
    let mut programs: Vec<(String, Box<dyn Fn() -> (Program, [F192; 2])>)> = Vec::new();
    let directory = checkout.join("crates/lean_compiler/tests/programs");
    let mut paths: Vec<_> = std::fs::read_dir(&directory)
        .expect("suite programs")
        .map(|entry| entry.expect("directory entry").path())
        .filter(|path| path.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    for path in paths {
        if suite_program(&path).is_some() {
            let name = path.file_stem().unwrap().to_string_lossy().replace('_', "-");
            programs.push((name, Box::new(move || suite_program(&path).unwrap())));
        }
    }
    for steps in [16usize, 1000, 5000] {
        programs.push((format!("chain{steps}"), Box::new(move || chain(steps))));
    }
    let mut fixtures = Vec::new();
    for (name, make) in &programs {
        for rate in 1..=4usize {
            fixtures.push((format!("{name}-rate{rate}"), make(), rate));
        }
    }
    fixtures
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let checkout = Path::new(&args[1]);
    let out = Path::new(&args[2]);
    let fixtures = if args.get(3).is_some_and(|flag| flag == "--corpus") {
        corpus(checkout)
    } else {
        vec![
            ("chain4-rate1".to_string(), chain(4), 1usize),
            ("chain300-rate2".to_string(), chain(300), 2),
            ("fibonacci-rate4".to_string(), fibonacci(checkout), 4),
        ]
    };
    for (name, (program, public_input), log_inv_rate) in fixtures {
        let directory = out.join(&name);
        std::fs::create_dir_all(&directory).expect("create fixture directory");
        let (proof, stats) = prove(&program, public_input, log_inv_rate).expect("prove");
        let summary = verify(&program, &public_input, &proof).expect("honest proof verifies");
        let table: Vec<u8> = leanvm_core::cpu::layout::bytecode_table(&program.prog)
            .iter()
            .flat_map(|w| w.0.to_le_bytes())
            .collect();
        std::fs::write(directory.join("bytecode.bin"), &table).expect("write bytecode");
        std::fs::write(directory.join("public_input.bin"), public_input_bytes(&public_input))
            .expect("write public input");
        // python_verifier.rs, `encode`.
        let stream: Vec<u8> = proof
            .stream
            .iter()
            .flat_map(|scalar| [scalar.c0, scalar.c1, scalar.c2])
            .flat_map(u64::to_le_bytes)
            .collect();
        let mut openings = Vec::new();
        for path in &summary.merkle_paths {
            openings.extend(path.leaf.iter().flat_map(|word| word.to_bytes()));
            openings.extend(path.siblings.iter().flatten());
        }
        std::fs::write(directory.join("stream.bin"), stream).expect("write scalar stream");
        std::fs::write(directory.join("merkle_openings.bin"), openings).expect("write Merkle openings");
        println!(
            "{name}: {} instructions, {} cycles, {} scalars, {} openings",
            program.prog.len(),
            stats.cycles,
            proof.stream.len(),
            summary.merkle_paths.len(),
        );
    }
}
EOF

cargo run --quiet --release --manifest-path "$work/Cargo.toml" --target-dir "$checkout/target" \
  -- "$checkout" "$out" ${2:+"$2"}

for directory in "$out"/*/; do
  printf '%s: ' "$(basename "$directory")"
  python3 -I "$checkout/python-verifier/verifier.py" "$directory/bytecode.bin" \
    "$directory/public_input.bin" "$directory/stream.bin" "$directory/merkle_openings.bin"
done
