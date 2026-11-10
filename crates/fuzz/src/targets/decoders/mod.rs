//! The `decoders` group: every byte string a peer can send (VM proofs, aggregates, signatures, keys, blobs), decoded
//! from real encodings mutated and from garbage. Decoding never panics, and a decode is canonical: the one encoding of
//! what it returns is the input.

use crate::programs::{self, Spec};
use crate::{Cost, Target, catch};
use leanvm_core::cpu::{Program, Proof};
use primitives::field::F192;
use std::sync::OnceLock;

mod aggregate;
mod lean_da;
mod proof;
mod signatures;

pub static TARGETS: &[&Target] = &[
    &Target {
        name: "decode-proof",
        about: "VM proof bytes, mutated honest encodings and garbage: no panic, every decode re-encodes to its input, a changed proof never verifies",
        cost: Cost::Cheap,
        run: proof::run,
    },
    &Target {
        name: "decode-aggregate",
        about: "aggregate bytes with adversarial claims: no panic, decode round-trips, verify never panics and never accepts a garbage VM proof",
        cost: Cost::Medium,
        run: aggregate::run,
    },
    &Target {
        name: "decode-signatures",
        about: "leanXMSS and leanSPHINCS keys and signatures from bytes: round trips, no panic, and one flipped bit of a real signature, key or message is refused",
        cost: Cost::Cheap,
        run: signatures::run,
    },
    &Target {
        name: "lean-da",
        about: "LeanDA commit on edge-sized payloads: errors not panics, deterministic, systematic, a codeword, the tree a plain rebuild gives, and the verifier's challenge",
        cost: Cost::Medium,
        run: lean_da::run,
    },
];

/// An honest proof of a corpus program, its statement and its encoding.
pub struct Honest {
    pub name: &'static str,
    pub program: Program,
    pub public_input: [F192; 2],
    pub proof: Proof,
    pub bytes: Vec<u8>,
}

/// A few small corpus programs proven once per process: the fixtures the decoders mutate. Empty if none proves,
/// which `dsl-corpus` reports, not this group.
pub fn honest() -> &'static [Honest] {
    static HONEST: OnceLock<Vec<Honest>> = OnceLock::new();
    HONEST.get_or_init(|| {
        let mut specs: Vec<&'static Spec> = programs::provable().into_iter().filter(|s| !s.slow).collect();
        specs.sort_by_key(|s| s.source.len());
        specs
            .into_iter()
            .take(3)
            .enumerate()
            .filter_map(|(i, spec)| {
                catch(|| {
                    let program = spec.compile().ok()?;
                    let (run, pi) = programs::execute(&program, spec.public_input);
                    if !run.ok()?.unconstrained_reads.is_empty() {
                        return None;
                    }
                    let rate = leanvm_core::pcs::MIN_LOG_INV_RATE + i % 2;
                    let (proof, _) = leanvm_core::cpu::prove(&program, pi, rate).ok()?;
                    let bytes = proof.to_bytes();
                    Some(Honest {
                        name: spec.name,
                        program,
                        public_input: pi,
                        proof,
                        bytes,
                    })
                })
                .ok()
                .flatten()
            })
            .collect()
    })
}
