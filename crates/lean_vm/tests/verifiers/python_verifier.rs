//! Pins `python-verifier/verifier.py` against `lean_vm::cpu::verify`: the same
//! protocol is written out in Rust, in Python, and in zkDSL, so any protocol
//! change must land in all three, and this is what catches the Python one
//! drifting.

use fiat_shamir::transcript::RawProof;
use lean_compiler::{compile, parse_with_replacements};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};
use std::collections::BTreeMap;
use std::path::Path;
use std::process::{Command, Output};
use std::time::Instant;

const SOURCE: &str = r#"
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
    sha3(seed, seed, digest)

    chain = HeapBuf(LOOP_STEPS + 1)
    chain[1] = digest[0]
    for index in mul_range(1, GEN ** LOOP_STEPS):
        chain[index * GEN] = mix(chain[index] + index, index) + index

    public = GEN ** 0
    public[1] = chain[GEN ** LOOP_STEPS]
    public[GEN] = mix(digest[1], GEN ** 0)
    return
"#;

const LOOP_STEPS: usize = 16_384;

/// Write `raw` as the two files Python reads and run the verifier on it: the
/// scalar stream as 24-byte little-endian elements, and every opening's leaf
/// words followed by its sibling digests. Neither file carries a length, the
/// reader deriving every leaf width and tree height from the protocol it is
/// replaying.
fn python_verify(directory: &Path, bytecode: &Path, public_input: &Path, raw: &RawProof) -> Output {
    let mut stream = Vec::new();
    for scalar in &raw.stream {
        for limb in [scalar.c0, scalar.c1, scalar.c2] {
            stream.extend(limb.to_le_bytes());
        }
    }
    let mut openings = Vec::new();
    for opening in &raw.merkle {
        for word in &opening.leaf_data {
            openings.extend(word.0.to_le_bytes());
        }
        for digest in &opening.path {
            openings.extend(digest);
        }
    }
    let stream_path = directory.join("stream.bin");
    let openings_path = directory.join("merkle_openings.bin");
    std::fs::write(&stream_path, stream).expect("write scalar stream");
    std::fs::write(&openings_path, openings).expect("write Merkle openings");
    Command::new("python3")
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py"))
        .arg(bytecode)
        .arg(public_input)
        .arg(stream_path)
        .arg(openings_path)
        .output()
        .expect("run native Python verifier")
}

fn public_input() -> [F192; 2] {
    let seed = [F64(5), F64::ZERO, F64(7), F64::ZERO];
    let bytes: Vec<u8> = seed.iter().chain(&seed).flat_map(|w| w.0.to_le_bytes()).collect();
    let hash = primitives::keccak::hash(&bytes);
    let digest: [F64; 4] = std::array::from_fn(|i| F64(u64::from_le_bytes(hash[8 * i..8 * i + 8].try_into().unwrap())));
    let digest = [
        F192::new(digest[0].0, digest[1].0, 0),
        F192::new(digest[2].0, digest[3].0, 0),
    ];
    let mut value = digest[0];
    let mut index = F192::ONE;
    let generator = F192::from(g_pow(1));
    for _ in 0..LOOP_STEPS {
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

#[test]
fn test_python_verifier() {
    let replacements = BTreeMap::from([("LOOP_STEPS_PLACEHOLDER".to_string(), LOOP_STEPS.to_string())]);
    let ast = parse_with_replacements(SOURCE, &replacements).expect("parse zkDSL program");
    let program = compile(&ast);
    let public_input = public_input();
    let (proof, stats) = prove(&program, public_input, 1).unwrap();
    // Python reads the RAW proof: same protocol, each query carrying its own
    // full Merkle path instead of one octopus over the batch. A Rust verify
    // expands the wire form, so the pruning is written once.
    let raw = verify(&program, &public_input, &proof)
        .expect("honest proof verifies")
        .raw;

    let directory = std::env::temp_dir().join(format!("leanvm-python-verifier-test-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("create test directory");
    let bytecode_path = directory.join("bytecode.bin");
    let public_input_path = directory.join("public_input.bin");
    let encoded = bincode::serialize(&proof).expect("serialize proof");
    // The statement the verifier takes is the bytecode multilinear plus 256 bits
    // of public input, not a structured program.
    let table: Vec<u8> = lean_vm::cpu::layout::bytecode_table(&program.prog)
        .iter()
        .flat_map(|w| w.0.to_le_bytes())
        .collect();
    std::fs::write(&bytecode_path, &table).expect("write bytecode");
    let pi: Vec<u8> = public_input
        .iter()
        .flat_map(|v| [v.c0.to_le_bytes(), v.c1.to_le_bytes()].concat())
        .collect();
    std::fs::write(&public_input_path, &pi).expect("write public input");

    let verification_started = Instant::now();
    let output = python_verify(&directory, &bytecode_path, &public_input_path, &raw);
    let verification_time = verification_started.elapsed();
    assert!(
        output.status.success(),
        "native Python verification failed:\n{}",
        String::from_utf8_lossy(&output.stderr),
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "verification succeeded",);

    let mut malformed_announcement = proof.clone();
    malformed_announcement.stream[0].c1 = 1;
    assert!(verify(&program, &public_input, &malformed_announcement).is_err());
    let mut raw_announcement = raw.clone();
    raw_announcement.stream[0].c1 = 1;
    let output = python_verify(&directory, &bytecode_path, &public_input_path, &raw_announcement);
    assert!(!output.status.success(), "Python accepted a noncanonical announcement");

    let mut malformed_root = proof.clone();
    let root_offset = lean_vm::tables::N_TABLES + 2;
    malformed_root.stream[root_offset].c2 = 1;
    assert!(verify(&program, &public_input, &malformed_root).is_err());
    let mut raw_root = raw.clone();
    raw_root.stream[root_offset].c2 = 1;
    let output = python_verify(&directory, &bytecode_path, &public_input_path, &raw_root);
    assert!(
        !output.status.success(),
        "Python accepted a noncanonical commitment root"
    );

    println!(
        "zkDSL compiled to {} instructions; proved {} cycles in {} bytes; Python verified in {:.2?}",
        program.prog.len(),
        stats.cycles,
        encoded.len(),
        verification_time,
    );
    std::fs::remove_dir_all(directory).expect("remove test directory");
}
