//! `soundness-verifier-dos`: what a peer's proof can make a verifier spend. `aggregate` replays every untrusted child
//! with `replay_unchecked` before anything checks it, and a node verifies what peers send, so neither may cost more
//! than a bound linear in the proof's own size, whatever sizes it announces.
//!
//! The adversary announces sizes up to the verifier's caps, then repairs whatever stopped the walk: a stream that ran
//! out grows by random scalars, a missing Merkle phase is borrowed from the honest proof, a surplus one dropped. Round
//! after round the garbage proof goes deeper, each walk measured against the budget, so the deepest and largest walk an
//! attacker can buy is the one held to it.

use super::fixtures::{self, Fixture};
use crate::resources::{measure, within};
use crate::{Ctx, Finding, Outcome, Source};
use leanvm_core::cpu::{bytecode_table, public_input_bytes, scalar_proof};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Duration;
use verifier::{Bytecode, E, VerifierError};

/// The most scalars the adversary grows a stream to: a proof a few tens of MiB long.
const MAX_SCALARS: usize = 1 << 20;
/// A walk may hold this much beyond what the proof itself takes, and take this long. A real denial of service is
/// orders of magnitude past both; the slack absorbs a loaded machine.
const BASE_BYTES: usize = 1 << 29;
const PER_PROOF_BYTE: usize = 64;
const MAX_TIME: Duration = Duration::from_secs(30);

fn bytecode(fixture: &'static Fixture) -> Arc<Bytecode> {
    static CACHE: OnceLock<Mutex<HashMap<usize, Arc<Bytecode>>>> = OnceLock::new();
    let mut cache = CACHE.get_or_init(Default::default).lock().unwrap();
    cache
        .entry(fixture as *const Fixture as usize)
        .or_insert_with(|| {
            let table: Vec<u64> = bytecode_table(fixture.program.prog()).iter().map(|w| w.0).collect();
            Arc::new(Bytecode::new(&table))
        })
        .clone()
}

fn random_scalar(src: &mut Source) -> E {
    let x = src.f128();
    E::new(x.c0, x.c1)
}

/// An announced row count or log size, biased to the caps the verifier enforces and just past them.
fn big(src: &mut Source, cap_log: u32) -> u64 {
    match src.below(5) {
        0 => 1 << src.below(cap_log as usize + 1),
        1 => (1u64 << src.below(cap_log as usize + 1)) + 1,
        2 => (1u64 << cap_log) - src.below(3) as u64,
        3 => (1u64 << cap_log) + src.below(3) as u64,
        _ => src.u64() % (1u64 << cap_log),
    }
}

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let Some((fixture, _rate, honest)) = fixtures::draw(src)? else {
        return Ok(());
    };
    let bytecode = bytecode(fixture);
    let public_input = public_input_bytes(&fixture.public_input);
    let honest_proof = scalar_proof(&honest.proof);
    let mut proof = honest_proof.clone();

    // The announcement: log memory, six row counts, the rate.
    let past_the_caps = |e: &Result<verifier::Summary, VerifierError>| {
        matches!(
            e,
            Err(VerifierError::AnnouncedTableSizes | VerifierError::CommittedSize | VerifierError::AnnouncedHighLimb)
        )
    };
    match src.below(5) {
        4 => {
            // The largest announcement the size checks admit, found by bisection on one size: the costliest walk
            // that is not refused at the door.
            let i = src.below(7);
            let (mut lo, mut hi) = (proof.stream[i].c0, if i == 0 { 64 } else { 1u64 << 33 });
            while lo + 1 < hi {
                let mid = lo + (hi - lo) / 2;
                proof.stream[i] = E::new(mid, 0);
                if past_the_caps(&verifier::replay_unchecked(&bytecode, &public_input, &proof)) {
                    hi = mid;
                } else {
                    lo = mid;
                }
            }
            proof.stream[i] = E::new(lo, 0);
            ctx.note(format!("announce: size {i} at the largest admitted"));
        }
        0 => {
            proof.stream[0] = E::new(big(src, 6).min(40), 0);
            for t in 1..7 {
                proof.stream[t] = E::new(big(src, 32), 0);
            }
            ctx.note("announce: every size large");
        }
        1 => {
            let t = src.range(1, 6);
            proof.stream[t] = E::new(big(src, 33), 0);
            ctx.note("announce: one table large");
        }
        2 => {
            proof.stream[0] = E::new(src.range(10, 40) as u64, 0);
            ctx.note("announce: memory size");
        }
        _ => ctx.note("announce: honest sizes"),
    }
    if src.chance(1, 4) {
        proof.stream[7] = E::new(src.range(1, 4) as u64, 0);
    }

    for round in 0..src.range(1, 16) {
        let proof_bytes = proof.stream.len() * 16
            + proof
                .merkle_openings
                .iter()
                .flatten()
                .map(|p| 8 + 8 * p.leaf.len() + 32 * p.siblings.len())
                .sum::<usize>();
        let budget = BASE_BYTES + PER_PROOF_BYTE * proof_bytes;
        let (replayed, usage) = measure(|| verifier::replay_unchecked(&bytecode, &public_input, &proof));
        within("replay_unchecked of an adversarial proof", usage, budget, MAX_TIME)?;
        let (verified, usage) = measure(|| verifier::verify_execution(&bytecode, &public_input, &proof));
        within("verify_execution of an adversarial proof", usage, budget, MAX_TIME)?;
        if verified.is_ok() && proof != honest_proof {
            return Err(Finding::critical(
                "soundness-verifier-dos: a garbage proof verifies",
                format!("round {round}, announced {:?}", &proof.stream[..8]),
            ));
        }
        let error = match replayed {
            Ok(_) => {
                ctx.note("replay walked to the end");
                break;
            }
            Err(e) => e,
        };
        ctx.note(format!(
            "round {}: {}",
            round.min(4),
            fixtures::verifier_error_name(&error)
        ));
        match error {
            VerifierError::StreamExhausted if proof.stream.len() < MAX_SCALARS => {
                let grow = proof.stream.len().clamp(64, MAX_SCALARS - proof.stream.len());
                let fill = src.below(3);
                for _ in 0..grow {
                    let x = match fill {
                        0 => E::new(0, 0),
                        1 => random_scalar(src),
                        _ => honest_proof.stream[src.below(honest_proof.stream.len())],
                    };
                    proof.stream.push(x);
                }
            }
            VerifierError::MerkleOpeningMissing if !honest_proof.merkle_openings.is_empty() => {
                let phase = &honest_proof.merkle_openings[src.below(honest_proof.merkle_openings.len())];
                proof.merkle_openings.push(phase.clone());
            }
            VerifierError::MerkleNotConsumed => {
                proof.merkle_openings.pop();
            }
            _ => break,
        }
    }
    Ok(())
}
