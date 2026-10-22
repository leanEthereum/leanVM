//! Pins `python-verifier/verifier.py` against `leanvm_core::cpu::prove` and the
//! `verifier` crate: the same protocol is written out in Rust, in Python, and in
//! zkDSL, so any protocol change must land in all three, and this is what
//! catches the Python one drifting.

use lean_compiler::{compile, parse_with_replacements};
use leanvm_core::cpu::{Program, Stats, prove, public_input_bytes, verify};
use leanvm_core::tables::N_TABLES;
use primitives::field::{F192, g_pow};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::OnceLock;
use std::time::Instant;
use verifier::{Bytecode, Proof, VerifierError, verify_execution};

const SOURCE: &str = r#"
from snark_lib import *

LOOP_STEPS = LOOP_STEPS_PLACEHOLDER

def mix(value, tag):
    # A JUMP condition is K-valued (a g-power here), never an arbitrary word.
    if tag == 0:
        return value
    return value * GEN + value

def main():
    # 160 bytes: two blocks, the second read in the odd layout.
    digest = StackBuf(2)
    keccak_cells([5, 7, 5, 7, 5, 7, 5, 7, 5, 7], digest)

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

/// Write the statement and the raw proof with `stream` as the files Python reads, and start the verifier on them.
fn spawn_python(directory: &Path, stream: &[F192]) -> Child {
    let fixture = fixture();
    std::fs::create_dir_all(directory).expect("create test directory");
    let table = fixture
        .bytecode_table()
        .into_iter()
        .flat_map(u64::to_le_bytes)
        .collect();
    let (stream, openings) = encode(stream, &fixture.summary.merkle_paths);
    let files = [
        ("bytecode.bin", table),
        ("public_input.bin", public_input_bytes(&fixture.public_input).to_vec()),
        ("stream.bin", stream),
        ("merkle_openings.bin", openings),
    ];
    let mut command = Command::new("python3");
    command.arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py"));
    for (name, bytes) in files {
        let path = directory.join(name);
        std::fs::write(&path, bytes).expect("write verifier input");
        command.arg(path);
    }
    command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run native Python verifier")
}

fn test_directory(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("leanvm-python-verifier-{name}-{}", std::process::id()))
}

fn public_input() -> [F192; 2] {
    let message: Vec<u8> = [5u64, 7]
        .repeat(5)
        .into_iter()
        .flat_map(|v| [v, 0])
        .flat_map(u64::to_le_bytes)
        .collect();
    let digest = primitives::hash::hash(&message);
    let word = |i: usize| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap());
    let digest = [F192::new(word(0), word(1), 0), F192::new(word(2), word(3), 0)];
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
    pub proof: leanvm_core::cpu::Proof,
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
        program, proof, stats, ..
    } = fixture();
    let directory = test_directory("honest");
    let verification_started = Instant::now();
    let output = spawn_python(&directory, &proof.stream)
        .wait_with_output()
        .expect("wait for the Python verifier");
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
        bincode::serialize(proof).expect("serialize proof").len(),
        verification_time,
    );
    std::fs::remove_dir_all(directory).expect("remove test directory");
}

/// Both verifiers reject a tampered scalar at the same check: a high limb on an announced size and on the commitment
/// root, and each check of the Keccak reduction tripped by the scalar it reads last.
#[test]
fn tampers_fail_the_same_check() {
    let fixture = fixture();
    let keccak = fixture.summary.keccak_scalars.clone();
    // The reduction opens with the committed outputs' claim, then the first layer's 47 product coefficients, and its
    // last layer ends on three evaluations. The output opening follows (a slot sumcheck of 6 rounds, two scalars a
    // round, then the word), then the input opening (4 rounds, 6 rounds, the 64 slices).
    let input_opening = 2 * (4 + 6) + 64;
    let output_opening = 2 * 6 + 1;
    let cases = [
        (0, VerifierError::AnnouncedHighLimb),
        (N_TABLES + 2, VerifierError::DigestHalf),
        (keccak.start + 47, VerifierError::KeccakProduct),
        (
            keccak.end - input_opening - output_opening - 1,
            VerifierError::KeccakLayer,
        ),
        (keccak.end - input_opening - 1, VerifierError::KeccakOutputOpening),
        (keccak.end - 1, VerifierError::KeccakInputOpening),
    ];

    let bytecode = Bytecode::new(&fixture.bytecode_table());
    let public_input = public_input_bytes(&fixture.public_input);
    let directory = test_directory("tampered");
    let runs: Vec<Child> = cases
        .iter()
        .map(|&(position, error)| {
            let mut stream = fixture.proof.stream.clone();
            stream[position] += F192::new(0, 0, 1);
            let (bytes, openings) = encode(&stream, &fixture.summary.merkle_paths);
            let proof = Proof::load(&bytes, &openings).expect("load the tampered proof");
            assert_eq!(
                verify_execution(&bytecode, &public_input, &proof),
                Err(error),
                "scalar {position}"
            );
            spawn_python(&directory.join(position.to_string()), &stream)
        })
        .collect();
    for ((position, error), run) in cases.into_iter().zip(runs) {
        let output = run.wait_with_output().expect("wait for the Python verifier");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success() && stderr.contains(&format!("verification failed: {error}")),
            "Python did not fail on `{error}` at scalar {position}:\n{stderr}"
        );
    }
    std::fs::remove_dir_all(directory).expect("remove test directory");
}
