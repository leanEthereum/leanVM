#!/usr/bin/env bash
# Prove small guest programs with the leanVM Rust prover and write each proof in the formats the
# verifiers read (the Lean verifier, `cli/LeanvmVerify.lean`; `crates/verifier`'s `Proof`, as
# `scripts/rust-verifier-cli` reads it; `crates/fiat_shamir/src/wire.rs`, `Proof::to_bytes`).
#
# Usage: scripts/export-rust.sh fixtures|traces <output dir> [--corpus]
# (`export-verifier-fixtures-rust.sh` and `export-prover-traces-rust.sh` name the two modes.)
#
# Per case directory, in both modes:
#
#   bytecode.bin          the bytecode table, little-endian 64-bit words;
#   public_input.bin      the public input's two halves, 16 bytes each (c0, c1 little-endian);
#   stream.bin            the scalar stream, 24-byte little-endian E elements;
#   merkle_phases.bin     the Merkle openings in the `verifier` crate's structure
#                         (`Proof::merkle_openings: Vec<Vec<MerklePath>>`), every number
#                         little-endian: the phase count (u32); per phase its path count (u32);
#                         per path its leaf_index (u64), its leaf's length (u32) and words (u64),
#                         its sibling count (u32) and siblings (32 bytes each);
#   proof.wire            the proof's one wire encoding, `Proof::to_bytes` (pruned phases).
#
# and in `traces` mode, for the Lean prover's differential test (`lake exe leanvm-prove`,
# `scripts/prover-diff.py`), the execution by the Rust interpreter (`Program::execute`):
#
#   memory.bin            the execution's memory, 24 bytes per cell (three limbs, little-endian);
#   trace.txt             `<log2 cells> <instructions executed> <rate>`;
#   rust.txt              the Rust prover's wall time in seconds.
#
# The proof is the honest proof of the Rust `prove`, its Merkle paths unpruned
# (`leanvm_core::cpu::scalar_proof`). The guests (`fixed`) are the program of
# crates/leanvm_core/tests/verifiers/fixture.rs at 4, 300 and 1000 loop steps,
# crates/lean_compiler/tests/programs/fibonacci.py, and eight more programs of that suite, three
# at each of the four rates, read from the source tree. Every proof is verified by the Rust
# `cpu::verify` before it is written, and `Proof::from_bytes` must give it back from `proof.wire`.
# In `fixtures` mode `scripts/rust-verifier-cli` must also accept it from the written files before
# the script returns; the fixtures are consumed by scripts/fuzz-verifier.py, which runs the Lean
# and the Rust verifier on them and on mutations of them. In `traces` mode a program the Rust
# interpreter or prover refuses is skipped.
#
# With `--corpus`, the cases are instead every program of crates/lean_compiler/tests/programs
# that declares its public input (with its `# witness` annotations), and the chain at 16, 1000 and
# 5000 loop steps, each at the four rates: the differential fuzzing corpus (not committed).
#
# The prover and the verifiers are this repository's. Requires `cargo`.
set -euo pipefail

usage="usage: $0 fixtures|traces <output dir> [--corpus]"
mode="${1:?$usage}"
case "$mode" in fixtures | traces) ;; *) echo "$usage" >&2; exit 2 ;; esac
out="${2:?$usage}"
checkout="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"

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
name = "export-rust"
version = "0.0.0"
edition = "2024"

[workspace]

[dependencies]
leanvm_core = { path = "$checkout/crates/leanvm_core" }
lean_compiler = { path = "$checkout/crates/lean_compiler" }
primitives = { path = "$checkout/crates/primitives" }
verifier = { path = "$checkout/crates/verifier" }
fiat_shamir = { path = "$checkout/crates/fiat_shamir" }

[profile.release]
lto = "thin"
codegen-units = 1
EOF

# The chain program and the suite's header readers, from the tests that define them.
cat > "$work/src/main.rs" <<EOF
#[allow(dead_code)]
#[path = "$checkout/crates/leanvm_core/tests/verifiers/fixture.rs"]
mod fixture;
#[allow(dead_code, unused_imports)]
#[path = "$checkout/crates/lean_compiler/tests/suite/py_source.rs"]
mod py_source;
EOF

cat >> "$work/src/main.rs" <<'EOF'
use fixture::chain;
use lean_compiler::{compile, parse};
use leanvm_core::cpu::{Program, prove, public_input_bytes, scalar_proof, verify};
use primitives::field::F192;
use std::path::Path;

// A program of crates/lean_compiler/tests/programs with its `# public_input:` and `# witness`
// annotations; `None` for a program without a declared public input.
fn suite_program(path: &Path) -> Option<(Program, [F192; 2])> {
    let source = std::fs::read_to_string(path).expect("read suite program");
    let public_input = py_source::public_input(&source)?;
    let mut program = compile(&parse(&source).expect("parse suite program"));
    for (stream, entries) in py_source::witness(&source) {
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

// The fixed cases: three per rate, the chain at three loop counts and suite programs that hash
// (`hash_*`, `wots_walk`), branch (`conditionals`, `match_arms`), read hints (`hint`), allocate
// (`heapbuf_dyn`) and unroll (`unroll`).
fn fixed(checkout: &Path) -> Vec<(String, (Program, [F192; 2]), usize)> {
    let suite = |name: &str| {
        suite_program(&checkout.join(format!("crates/lean_compiler/tests/programs/{name}.py")))
            .expect("a suite program with a declared public input")
    };
    vec![
        ("chain4-rate1".to_string(), chain(4), 1usize),
        ("wots-walk-rate1".to_string(), suite("wots_walk"), 1),
        ("hash-slices-rate1".to_string(), suite("hash_slices"), 1),
        ("chain300-rate2".to_string(), chain(300), 2),
        ("conditionals-rate2".to_string(), suite("conditionals"), 2),
        ("heapbuf-dyn-rate2".to_string(), suite("heapbuf_dyn"), 2),
        ("hash-heap-chain-rate3".to_string(), suite("hash_heap_chain"), 3),
        ("match-arms-rate3".to_string(), suite("match_arms"), 3),
        ("chain1000-rate3".to_string(), chain(1000), 3),
        ("fibonacci-rate4".to_string(), suite("fibonacci"), 4),
        ("hint-rate4".to_string(), suite("hint"), 4),
        ("unroll-rate4".to_string(), suite("unroll"), 4),
    ]
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let checkout = Path::new(&args[1]);
    let traces = args[2] == "traces";
    let out = Path::new(&args[3]);
    let fixtures = if args.get(4).is_some_and(|flag| flag == "--corpus") {
        corpus(checkout)
    } else {
        fixed(checkout)
    };
    for (name, (program, public_input), log_inv_rate) in fixtures {
        let directory = out.join(&name);
        std::fs::create_dir_all(&directory).expect("create case directory");
        let exec = if traces {
            match program.execute(public_input) {
                Ok(exec) => Some(exec),
                Err(_) => {
                    println!("{name}: no execution, skipped");
                    continue;
                }
            }
        } else {
            None
        };
        let start = std::time::Instant::now();
        let (proof, stats) = match prove(&program, public_input, log_inv_rate) {
            Ok(r) => r,
            Err(_) if traces => {
                println!("{name}: the Rust prover refuses it, skipped");
                continue;
            }
            Err(e) => panic!("prove: {e:?}"),
        };
        let seconds = start.elapsed().as_secs_f64();
        verify(&program, &public_input, &proof).expect("honest proof verifies");
        let wire = proof.to_bytes();
        assert!(fiat_shamir::transcript::Proof::from_bytes(&wire) == Some(proof.clone()), "the wire round trip");
        let scalar = scalar_proof(&proof);
        let table: Vec<u8> = leanvm_core::cpu::layout::bytecode_table(&program.prog)
            .iter()
            .flat_map(|w| w.0.to_le_bytes())
            .collect();
        std::fs::write(directory.join("bytecode.bin"), &table).expect("write bytecode");
        std::fs::write(directory.join("public_input.bin"), public_input_bytes(&public_input))
            .expect("write public input");
        // The stream as 24-byte little-endian elements, three limbs each.
        let stream: Vec<u8> = proof
            .stream
            .iter()
            .flat_map(|scalar| [scalar.c0, scalar.c1, scalar.c2])
            .flat_map(u64::to_le_bytes)
            .collect();
        let u32_bytes = |n: usize| u32::try_from(n).expect("a count fits in u32").to_le_bytes();
        let mut phases = Vec::new();
        phases.extend(u32_bytes(scalar.merkle_openings.len()));
        for phase in &scalar.merkle_openings {
            phases.extend(u32_bytes(phase.len()));
            for path in phase {
                phases.extend(path.leaf_index.to_le_bytes());
                phases.extend(u32_bytes(path.leaf.len()));
                phases.extend(path.leaf.iter().flat_map(|word| word.to_bytes()));
                phases.extend(u32_bytes(path.siblings.len()));
                phases.extend(path.siblings.iter().flatten());
            }
        }
        std::fs::write(directory.join("stream.bin"), stream).expect("write scalar stream");
        std::fs::write(directory.join("merkle_phases.bin"), phases).expect("write Merkle phases");
        std::fs::write(directory.join("proof.wire"), &wire).expect("write the wire proof");
        let Some(exec) = exec else {
            println!(
                "{name}: {} instructions, {} cycles, {} scalars, {} phases, {} openings, {} wire bytes",
                program.prog.len(),
                stats.cycles,
                proof.stream.len(),
                scalar.merkle_openings.len(),
                scalar.merkle_openings.iter().map(Vec::len).sum::<usize>(),
                wire.len(),
            );
            continue;
        };
        let memory: Vec<u8> = (0..exec.mem.len())
            .map(|i| exec.mem.word(i))
            .flat_map(|w| [w.c0, w.c1, w.c2])
            .flat_map(u64::to_le_bytes)
            .collect();
        std::fs::write(directory.join("memory.bin"), memory).expect("write memory");
        let log_mem = exec.mem.len().trailing_zeros();
        std::fs::write(directory.join("trace.txt"), format!("{log_mem} {} {log_inv_rate}\n", exec.cycles))
            .expect("write trace");
        std::fs::write(directory.join("rust.txt"), format!("{seconds}\n")).expect("write time");
        println!(
            "{name}: {} instructions, 2^{log_mem} cells, {} cycles, Rust prover {seconds:.3} s",
            program.prog.len(),
            stats.cycles,
        );
    }
}
EOF

cargo run --quiet --release --manifest-path "$work/Cargo.toml" --target-dir "$checkout/target" \
  -- "$checkout" "$mode" "$out" ${3:+"$3"}

[ "$mode" = fixtures ] || exit 0
# Every fixture as the fuzz's Rust side reads it, from its files.
cargo build --quiet --release --manifest-path "$checkout/formal/lean_vm/scripts/rust-verifier-cli/Cargo.toml"
for directory in "$out"/*/; do
  printf '%s: ' "$(basename "$directory")"
  "$checkout/formal/lean_vm/scripts/rust-verifier-cli/target/release/leanvm-rust-verify" \
    "$directory/bytecode.bin" "$directory/public_input.bin" "$directory/stream.bin" \
    "$directory/merkle_phases.bin"
done
