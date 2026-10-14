//! Pins `python-verifier/verifier.py` against `leanvm_core::cpu::prove` and the
//! `verifier` crate: the same protocol is written out in Rust, in Python, and in
//! zkDSL, so any protocol change must land in all three, and this is what
//! catches the Python one drifting.

use lean_compiler::{compile, parse_with_replacements};
use leanvm_core::cpu::{Program, Proof, Stats, prove, verify};
use primitives::field::{F64, F192, g_pow};
use std::collections::BTreeMap;
use std::path::Path;
use std::process::{Command, Output};
use std::sync::OnceLock;
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

/// The raw proof as the two encodings the other verifiers read: the scalar
/// stream as 24-byte little-endian elements, and every query's own opening, its
/// leaf words followed by its sibling digests. Neither carries a length, the
/// reader deriving every leaf width and tree height from the protocol it is
/// replaying.
pub(crate) fn encode(stream: &[F192], paths: &[verifier::MerklePath]) -> (Vec<u8>, Vec<u8>) {
    let limbs = stream.iter().flat_map(|scalar| [scalar.c0, scalar.c1, scalar.c2]);
    let mut openings = Vec::new();
    for path in paths {
        openings.extend(path.leaf.iter().flat_map(|word| word.to_bytes()));
        openings.extend(path.siblings.iter().flatten());
    }
    (limbs.flat_map(u64::to_le_bytes).collect(), openings)
}

/// Write the raw proof as the two files Python reads and run the verifier on it.
fn python_verify(directory: &Path, bytecode: &Path, public_input: &Path, stream: &[F192]) -> Output {
    let (stream, openings) = encode(stream, &fixture().summary.merkle_paths);
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
    let digest = leanvm_core::vmhash::compress(seed, seed);
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

/// One honest proof of the program above, shared by the tests of both verifiers.
pub(crate) struct Fixture {
    pub program: Program,
    pub public_input: [F192; 2],
    pub proof: Proof,
    pub stats: Stats,
    /// What verifying it leaves. Its paths, with the proof's stream, are the RAW
    /// proof: same protocol, each query carrying its own full Merkle path
    /// instead of one octopus over the batch. The `verifier` crate expands the
    /// wire form, so the pruning is written once.
    pub summary: verifier::Summary,
}

impl Fixture {
    /// The statement the other verifiers take: the bytecode multilinear plus
    /// 256 bits of public input, not a structured program.
    pub fn bytecode_table(&self) -> Vec<u64> {
        let table = leanvm_core::cpu::layout::bytecode_table(&self.program.prog);
        table.iter().map(|word| word.0).collect()
    }
}

pub(crate) fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let replacements = BTreeMap::from([("LOOP_STEPS_PLACEHOLDER".to_string(), LOOP_STEPS.to_string())]);
        let ast = parse_with_replacements(SOURCE, &replacements).expect("parse zkDSL program");
        let program = compile(&ast);
        let public_input = public_input();
        let (proof, stats) = prove(&program, public_input, 1).unwrap();
        let summary = verify(&program, &public_input, &proof).expect("honest proof verifies");
        Fixture {
            program,
            public_input,
            proof,
            stats,
            summary,
        }
    })
}

#[test]
fn test_python_verifier() {
    let Fixture {
        program,
        public_input,
        proof,
        stats,
        ..
    } = fixture();

    let directory = std::env::temp_dir().join(format!("leanvm-python-verifier-test-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("create test directory");
    let bytecode_path = directory.join("bytecode.bin");
    let public_input_path = directory.join("public_input.bin");
    let encoded = bincode::serialize(proof).expect("serialize proof");
    let table: Vec<u8> = fixture()
        .bytecode_table()
        .into_iter()
        .flat_map(u64::to_le_bytes)
        .collect();
    std::fs::write(&bytecode_path, &table).expect("write bytecode");
    let public_input_bytes = leanvm_core::cpu::public_input_bytes(public_input);
    std::fs::write(&public_input_path, public_input_bytes).expect("write public input");

    let verification_started = Instant::now();
    let output = python_verify(&directory, &bytecode_path, &public_input_path, &proof.stream);
    let verification_time = verification_started.elapsed();
    assert!(
        output.status.success(),
        "native Python verification failed:\n{}",
        String::from_utf8_lossy(&output.stderr),
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "verification succeeded",);

    println!(
        "zkDSL compiled to {} instructions; proved {} cycles in {} bytes; Python verified in {:.2?}",
        program.prog.len(),
        stats.cycles,
        encoded.len(),
        verification_time,
    );
    std::fs::remove_dir_all(directory).expect("remove test directory");
}
