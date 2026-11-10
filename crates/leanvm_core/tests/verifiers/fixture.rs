//! One honest proof of a small zkDSL program, shared by the verifier tests: a two-block Keccak and a
//! loop of field arithmetic, long enough that every table and the Keccak reduction are exercised.

use lean_compiler::{compile, parse_with_replacements};
use leanvm_core::cpu::{Program, prove, public_input_bytes, verify};
use primitives::field::{F192, g_pow};
use std::collections::BTreeMap;
use std::sync::OnceLock;
use verifier::Bytecode;

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

/// The program above at `loop_steps` loop steps, and the public input it computes. Also the chain cases of
/// `formal/lean_vm/scripts/export-rust.sh`, which includes this file.
pub(crate) fn chain(loop_steps: usize) -> (Program, [F192; 2]) {
    let replacements = BTreeMap::from([("LOOP_STEPS_PLACEHOLDER".to_string(), loop_steps.to_string())]);
    let ast = parse_with_replacements(SOURCE, &replacements).expect("parse zkDSL program");
    (compile(&ast), public_input(loop_steps))
}

fn public_input(loop_steps: usize) -> [F192; 2] {
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

/// One honest proof of the program above.
pub(crate) struct Fixture {
    pub program: Program,
    pub public_input: [F192; 2],
    pub proof: leanvm_core::cpu::Proof,
    /// What verifying it leaves.
    pub summary: verifier::Summary,
    /// The statement the verifiers take, not a structured program: the bytecode multilinear and the public input's
    /// 256 bits.
    pub bytecode: Bytecode,
    pub public_input_bytes: [u8; 32],
}

pub(crate) fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let (program, public_input) = chain(LOOP_STEPS);
        let (proof, _) = prove(&program, public_input, 1).unwrap();
        let summary = verify(&program, &public_input, &proof).expect("honest proof verifies");
        let table = leanvm_core::cpu::layout::bytecode_table(program.prog());
        let bytecode = Bytecode::new(&table.iter().map(|word| word.0).collect::<Vec<_>>());
        Fixture {
            public_input_bytes: public_input_bytes(&public_input),
            program,
            public_input,
            proof,
            summary,
            bytecode,
        }
    })
}
