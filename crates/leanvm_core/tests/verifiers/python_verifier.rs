//! Pins `python-verifier/verifier.py` against `leanvm_core::cpu::prove` and the
//! `verifier` crate: the same protocol is written out in Rust, in Python, and in
//! zkDSL, so any protocol change must land in all three, and this is what
//! catches the Python one drifting.

use lean_compiler::{compile, parse_with_replacements};
use leanvm_core::cpu::{Program, prove, public_input_bytes, scalar_proof, verify};
use primitives::field::{F128, g_pow};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::OnceLock;
use verifier::{Bytecode, E, Proof, VerifierError, verify_execution};

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

/// Write the statement and the proof as the files Python reads (its `--help` gives their layout), and start the
/// verifier on them.
fn spawn_python(directory: &Path, proof: &Proof) -> Child {
    let fixture = fixture();
    std::fs::create_dir_all(directory).expect("create test directory");
    let table = fixture
        .bytecode_table()
        .into_iter()
        .flat_map(u64::to_le_bytes)
        .collect();
    let mut openings = Vec::new();
    for path in proof.merkle_openings.iter().flatten() {
        openings.extend(path.leaf_index.to_le_bytes());
        openings.extend(path.leaf.iter().flat_map(|word| word.to_bytes()));
        openings.extend(path.siblings.iter().flatten());
    }
    let files = [
        ("bytecode.bin", table),
        ("public_input.bin", public_input_bytes(&fixture.public_input).to_vec()),
        (
            "stream.bin",
            proof
                .stream
                .iter()
                .flat_map(|scalar| [scalar.c0, scalar.c1])
                .flat_map(u64::to_le_bytes)
                .collect(),
        ),
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

/// The run's verdict: its output if it succeeded, its errors if not.
fn verdict(run: Child) -> String {
    let output = run.wait_with_output().expect("wait for the Python verifier");
    let text = if output.status.success() {
        output.stdout
    } else {
        output.stderr
    };
    String::from_utf8_lossy(&text).trim().to_string()
}

fn test_directory(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("leanvm-python-verifier-{name}-{}", std::process::id()))
}

fn public_input() -> [F128; 2] {
    let message: Vec<u8> = [5u64, 7]
        .repeat(5)
        .into_iter()
        .flat_map(|v| [v, 0])
        .flat_map(u64::to_le_bytes)
        .collect();
    let digest = primitives::hash::hash(&message);
    let word = |i: usize| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap());
    let digest = [F128::new(word(0), word(1)), F128::new(word(2), word(3))];
    let mut value = digest[0];
    let mut index = F128::ONE;
    let generator = F128::from(g_pow(1));
    for _ in 0..LOOP_STEPS {
        let candidate = value + index;
        let product = candidate * generator;
        value = (if product == F128::ZERO {
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
    pub public_input: [F128; 2],
    pub proof: leanvm_core::cpu::Proof,
    /// What verifying it leaves.
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
        let (proof, _) = prove(&program, public_input, 1).unwrap();
        let summary = verify(&program, &public_input, &proof).expect("honest proof verifies");
        Fixture {
            program,
            public_input,
            proof,
            summary,
        }
    })
}

/// Both verifiers accept the proof at every rate: each walks other rows of the tabulated query counts and another
/// ladder of level rates.
#[test]
fn test_python_verifier() {
    let fixture = fixture();
    let bytecode = Bytecode::new(&fixture.bytecode_table());
    let public_input = public_input_bytes(&fixture.public_input);
    let directory = test_directory("honest");
    let runs: Vec<Child> = (1..=4)
        .map(|log_inv_rate| {
            let proof = match log_inv_rate {
                1 => scalar_proof(&fixture.proof),
                _ => scalar_proof(&prove(&fixture.program, fixture.public_input, log_inv_rate).unwrap().0),
            };
            verify_execution(&bytecode, &public_input, &proof).expect("the proof verifies");
            spawn_python(&directory.join(log_inv_rate.to_string()), &proof)
        })
        .collect();
    for (log_inv_rate, run) in (1..).zip(runs) {
        assert_eq!(verdict(run), "verification succeeded", "rate {log_inv_rate}");
    }
    std::fs::remove_dir_all(directory).expect("remove test directory");
}

/// Both verifiers reject a tampered scalar at the same check: a high limb on an announced size, and each check of the
/// Keccak reduction tripped by the scalar it reads last.
#[test]
fn tampers_fail_the_same_check() {
    let fixture = fixture();
    // The reduction's stream: the committed outputs' claim, then each layer opening on its product polynomial and
    // ending on three evaluations. The output opening follows (a slot sumcheck, then the word), then the input opening
    // (a sumcheck over a pack's instances, one over the slot, then the slices). A degree-3 sumcheck sends two
    // scalars a round.
    const PRODUCT_COEFFICIENTS: usize = 47; // a product of two degree-23 embeddings
    const PACK_BITS: usize = 4; // sixteen instances a pack
    const SLOT_BITS: usize = 6; // 25 lanes of the 2 segments' states
    const SLICES: usize = 64;
    let keccak = fixture.summary.keccak_scalars.clone();
    let input_opening = 2 * (PACK_BITS + SLOT_BITS) + SLICES;
    let output_opening = 2 * SLOT_BITS + 1;
    let cases = [
        (0, VerifierError::AnnouncedHighLimb),
        (keccak.start + PRODUCT_COEFFICIENTS, VerifierError::KeccakProduct),
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
            let mut proof = scalar_proof(&fixture.proof);
            proof.stream[position] += E::new(0, 1);
            assert_eq!(
                verify_execution(&bytecode, &public_input, &proof),
                Err(error),
                "scalar {position}"
            );
            spawn_python(&directory.join(position.to_string()), &proof)
        })
        .collect();
    for ((position, error), run) in cases.into_iter().zip(runs) {
        assert_eq!(
            verdict(run),
            format!("verification failed: {error}"),
            "scalar {position}"
        );
    }
    std::fs::remove_dir_all(directory).expect("remove test directory");
}
