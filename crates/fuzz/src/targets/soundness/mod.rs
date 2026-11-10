//! The `soundness` group: a malicious prover against the native verifier. Each target starts from an honest proof of
//! a small program ([`fixtures`]) and changes one thing a verifier must notice: the proof's bytes, a transcript
//! message the prover then stays consistent with, the witness before it is committed, or the statement. Accepting
//! any of them is Critical.

use crate::{Cost, Ctx, Finding, Target, catch};
use leanvm_core::cpu::{CpuError, Proof};

pub mod determinism;
pub mod dos;
pub mod fixtures;
pub mod keccak_batch;
pub mod proof_mutate;
pub mod replay;
pub mod transcript_tamper;
pub mod witness_tamper;
pub mod wrong_statement;

pub static TARGETS: &[&Target] = &[
    &Target {
        name: "soundness-proof-mutate",
        about: "structured edits of an honest proof's stream and Merkle openings: verify rejects every changed proof, and neither verify nor replay panics",
        cost: Cost::Medium,
        run: proof_mutate::run,
    },
    &Target {
        name: "soundness-transcript-tamper",
        about: "a prover forging one or several transcript messages (announced sizes, root, GKR, sumchecks, Keccak, WHIR, nonces) and staying Fiat-Shamir consistent after: verify rejects",
        cost: Cost::Medium,
        run: transcript_tamper::run,
    },
    &Target {
        name: "soundness-witness-tamper",
        about: "adversarial witness edits before commitment (single words, padding rows, coordinated memory lies, zeroed counts, row swaps): a proof verifies only if the edited witness still satisfies the relation",
        cost: Cost::Medium,
        run: witness_tamper::run,
    },
    &Target {
        name: "soundness-wrong-statement",
        about: "an honest proof against another public input or bytecode, and proofs by a prover whose Program carries a stale IV: verify rejects",
        cost: Cost::Medium,
        run: wrong_statement::run,
    },
    &Target {
        name: "soundness-replay-consistency",
        about: "replay_unchecked returns verify's Summary on honest proofs, never panics on mutated ones, and fails exactly where verify fails structurally",
        cost: Cost::Medium,
        run: replay::run,
    },
    &Target {
        name: "soundness-determinism",
        about: "a program proven twice is byte-identical, and its digest agrees across processes and thread counts",
        cost: Cost::Medium,
        run: determinism::run,
    },
    &Target {
        name: "soundness-verifier-dos",
        about: "a garbage proof announcing sizes up to the caps, repaired round after round to walk deeper: replay_unchecked and verify stay within a budget linear in the proof, and never accept it",
        cost: Cost::Medium,
        run: dos::run,
    },
    &Target {
        name: "soundness-keccak-batch",
        about: "verify_keccak_batch accepts an honest standalone Keccak batch and rejects forged messages, tampered committed states and wrong shapes",
        cost: Cost::Medium,
        run: keccak_batch::run,
    },
];

/// `verify`, a panic turned into a Medium finding keyed by where it was raised.
pub fn verify_caught(
    fixture: &fixtures::Fixture,
    proof: &Proof,
    context: &str,
) -> Result<Result<verifier::Summary, CpuError>, Finding> {
    catch(|| fixture.verify(proof)).map_err(|(m, l)| Finding::panic(&m, &l).in_context(context))
}

/// `replay_unchecked` on `proof` against `fixture`'s statement, a panic a Medium finding.
pub fn replay_caught(
    fixture: &fixtures::Fixture,
    proof: &Proof,
    context: &str,
) -> Result<Result<verifier::Summary, verifier::VerifierError>, Finding> {
    let table: Vec<u64> = leanvm_core::cpu::bytecode_table(fixture.program.prog())
        .iter()
        .map(|w| w.0)
        .collect();
    let bytecode = verifier::Bytecode::new(&table);
    let pi = leanvm_core::cpu::public_input_bytes(&fixture.public_input);
    let proof = leanvm_core::cpu::scalar_proof(proof);
    catch(|| verifier::replay_unchecked(&bytecode, &pi, &proof))
        .map_err(|(m, l)| Finding::panic(&m, &l).in_context(context))
}

/// Note the verdict on a forgery, and fail with a Critical finding when it was accepted.
pub fn must_reject(
    ctx: &Ctx,
    verdict: Result<verifier::Summary, CpuError>,
    key: impl Into<String>,
    detail: impl FnOnce() -> String,
) -> Result<(), Finding> {
    match verdict {
        Ok(_) => Err(Finding::critical(key, detail())),
        Err(e) => {
            ctx.note(format!("rejected {}", fixtures::error_name(&e)));
            Ok(())
        }
    }
}
