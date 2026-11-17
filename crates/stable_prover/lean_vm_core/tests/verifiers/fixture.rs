//! One honest proof of a small zkDSL program, shared by the verifier tests: a two-block Keccak and a
//! loop of field arithmetic, long enough that every table and the Keccak reduction are exercised.

use isa::Program;
use lean_vm_core::cpu::{prove, public_input_bytes, verify};
use primitives::field::{F128, g_pow};
use std::sync::OnceLock;

/// The program `chain.py` at `loop_steps` loop steps, as the Lean back end compiled it (`lake exe guest-backend
/// export programs`, at each of `guest-export`'s `CHAIN_STEPS`).
fn compiled(loop_steps: usize) -> &'static str {
    macro_rules! at {
        ($($n:literal),*) => {
            match loop_steps {
                $($n => include_str!(concat!("../../../../zkdsl_compiler/tests/suite/lean_backend/chain", $n, ".txt")),)*
                _ => panic!("no compiled chain at {loop_steps} steps: add it to `CHAIN_STEPS` in guest-export"),
            }
        };
    }
    at!(4, 16, 300, 1000, 5000, 16384)
}

const LOOP_STEPS: usize = 16_384;

/// The program at `loop_steps` loop steps, and the public input it computes. Also the chain cases of
/// `formal/lean_vm/scripts/export-rust.sh`, which includes this file.
pub(crate) fn chain(loop_steps: usize) -> (Program, [F128; 2]) {
    let program = Program::__from_text(compiled(loop_steps)).expect("the compiled chain program loads");
    (program, public_input(loop_steps))
}

fn public_input(loop_steps: usize) -> [F128; 2] {
    let message: Vec<u8> = [5u64, 7]
        .repeat(5)
        .into_iter()
        .flat_map(|v| [v, 0])
        .flat_map(u64::to_le_bytes)
        .collect();
    let digest: [F128; 2] = fiat_shamir::merkle::hash_to_scalars(&primitives::hash::hash(&message));
    let mut value = digest[0];
    let mut index = F128::ONE;
    let generator = F128::from(g_pow(1));
    for _ in 0..loop_steps {
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

/// One honest proof of the program above.
pub(crate) struct Fixture {
    pub program: Program,
    pub public_input: [F128; 2],
    pub proof: lean_vm_core::cpu::Proof,
    /// What verifying it leaves.
    pub summary: verifier::Summary,
    /// The public input as the verifiers take it, its 256 bits.
    pub public_input_bytes: [u8; 32],
}

pub(crate) fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let (program, public_input) = chain(LOOP_STEPS);
        let (proof, _) = prove(&program, &[], public_input, 1).unwrap();
        let summary = verify(&program, &public_input, &proof).expect("honest proof verifies");
        Fixture {
            public_input_bytes: public_input_bytes(&public_input),
            program,
            public_input,
            proof,
            summary,
        }
    })
}
