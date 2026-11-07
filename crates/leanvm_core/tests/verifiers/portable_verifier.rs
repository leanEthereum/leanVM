//! Pins the portable `verifier` crate's replay, on the proof the Python verifier is pinned on.

use crate::python_verifier::fixture;
use leanvm_core::cpu::{public_input_bytes, scalar_proof};
use verifier::{Bytecode, replay_unchecked};

/// The replay reads out of an honest proof what verifying it leaves.
#[test]
fn replay_reads_the_summary_unchecked() {
    let fixture = fixture();
    let bytecode = Bytecode::new(&fixture.bytecode_table());
    let public_input = public_input_bytes(&fixture.public_input);
    assert_eq!(
        replay_unchecked(&bytecode, &public_input, &scalar_proof(&fixture.proof)).as_ref(),
        Ok(&fixture.summary)
    );
}
