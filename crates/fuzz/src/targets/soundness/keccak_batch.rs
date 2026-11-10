//! `soundness-keccak-batch`: `verifier::verify_keccak_batch` against a standalone batch proof, a batch of random
//! permutations committed alone and reduced by `keccak_gkr`, built here from the crate's public pieces as its
//! `batch_bench` does (which sits behind the `bench` feature). The honest proof must verify; a forged message, a
//! tampered committed state (with the prover's layers kept or rebuilt from the edit), an output claim of other
//! inputs, and the right proof under another shape or rate must not.

use crate::mutate_proof::perturb;
use crate::{Ctx, Finding, Outcome, Source, catch};
use fiat_shamir::transcript::{Proof, ProverState};
use keccak_gkr::{OutputClaim, Shape, Witness};
use leanvm_core::cpu::tamper::transcript;
use pcs::whir::{INITIAL_FOLDING_FACTOR, commit, config_for_rate};
use primitives::field::F64;
use std::cell::Cell;
use std::rc::Rc;

const LABEL: &[u8] = b"keccak-gkr-batch";
const LANES: usize = 25;
/// Depths (rounds between committed states) that divide the 24 rounds.
const DEPTHS: [usize; 7] = [1, 2, 3, 4, 6, 8, 12];

/// How the prover lies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Lie {
    Honest,
    /// One scalar of the stream, `fiat_shamir::tamper`.
    Message,
    /// A committed word changed after the witness was generated; the prover's layers are the honest ones.
    State,
    /// The same, the prover's layers rebuilt from the edited commitment.
    StateRebuilt,
    /// A word of the slots no state occupies.
    Spare,
    /// The output claim of a batch one lane away.
    Claim,
    /// The honest proof checked under another shape or rate.
    Statement,
}

struct Batch {
    shape: Shape,
    inputs: Vec<[u64; LANES]>,
    rate: usize,
}

fn prove(batch: &Batch, lie: Lie, src: &mut Source) -> Option<Proof> {
    let shape = batch.shape;
    let mu = shape.stack_log();
    let config = config_for_rate(mu, batch.rate).ok()?;
    let mut committed = vec![F64::ZERO; 1 << mu];
    let mut witness = Witness::generate(shape, &batch.inputs, &mut committed);
    let states = shape.slots() * shape.n();
    match lie {
        Lie::State | Lie::StateRebuilt => {
            let slot = src.below(shape.slots());
            let step = if src.chance(3, 4) {
                src.below(batch.inputs.len())
            } else {
                src.below(shape.n())
            };
            committed[slot * shape.n() + step] += F64(1 << src.below(64));
            if lie == Lie::StateRebuilt {
                witness = Witness::from_committed(shape, batch.inputs.len(), &committed);
            }
        }
        Lie::Spare if states < committed.len() => {
            let i = src.range(states, committed.len() - 1);
            committed[i] += F64(1 << src.below(64));
        }
        _ => {}
    }
    let statement = [shape.n_log(), shape.depth(), batch.rate, 0].map(|w| F64(w as u64));
    let mut ps = ProverState::new(fiat_shamir::digest_words(&primitives::hash::hash(LABEL)), statement);
    let (commitment, prover_data) = commit(&committed, mu, INITIAL_FOLDING_FACTOR, batch.rate);
    ps.add_root(&commitment.root);
    let instance = ps.sample_vec(shape.n_log());
    let output = if lie == Lie::Claim {
        let mut other = batch.inputs.clone();
        let j = src.below(other.len());
        other[j][src.below(LANES)] ^= 1 << src.below(64);
        OutputClaim::of_inputs(shape, &other, instance)
    } else {
        OutputClaim::of_inputs(shape, &batch.inputs, instance)
    };
    ps.add_scalars(&output.lanes);
    let openings = witness.prove(&mut ps, &committed, &output);
    let (ring, outputs) = openings.into_pcs_claims(0);
    let points: Vec<_> = outputs.into_iter().collect();
    pcs::stack_open::open_batch_mixed_whir_stacked(&mut ps, mu, committed, prover_data, &config, &points, &ring);
    Some(ps.into_proof())
}

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let n = if src.chance(3, 4) {
        src.range(1, 512)
    } else {
        src.range(513, 1100)
    };
    let depth = DEPTHS[src.below(DEPTHS.len())];
    let rate = crate::programs::log_inv_rate(src);
    let shape = Shape::new(n, depth);
    if !(verifier_bounds()).contains(&shape.stack_log()) {
        ctx.note("shape outside the stacked window");
        return Ok(());
    }
    let seed = src.u64();
    let mut rng = crate::Rng::new(seed);
    let inputs: Vec<[u64; LANES]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    let batch = Batch { shape, inputs, rate };
    let lie = [
        Lie::Honest,
        Lie::Message,
        Lie::State,
        Lie::StateRebuilt,
        Lie::Spare,
        Lie::Claim,
        Lie::Statement,
    ][src.weighted(&[2, 4, 3, 3, 1, 2, 2])];
    ctx.note(format!("{lie:?} depth {depth}"));
    let detail = format!("{n} permutations, depth {depth}, rate {rate}, lie {lie:?}");

    let changed = Rc::new(Cell::new(lie != Lie::Message));
    if lie == Lie::Message {
        // The stream's length is the honest proof's: prove once to learn it.
        let len = prove(&batch, Lie::Honest, src).map_or(0, |p| p.stream.len());
        let at = if src.chance(1, 4) {
            src.below(2 + LANES)
        } else {
            src.below(len.max(1))
        };
        let delta_src = src.u64();
        let seen = changed.clone();
        transcript::arm(Box::new(move |i, x| {
            if i != at {
                return x;
            }
            let y = perturb(x, &mut Source::from_seed(delta_src));
            if y != x {
                seen.set(true);
            }
            y
        }));
    }
    let proved = catch(|| prove(&batch, lie, src));
    transcript::disarm();
    let proof = match proved {
        Ok(Some(proof)) => proof,
        Ok(None) => {
            ctx.note("no WHIR configuration");
            return Ok(());
        }
        Err(_) => {
            ctx.note(format!("{lie:?} prover panicked"));
            return Ok(());
        }
    };
    if !changed.get() {
        return Ok(());
    }
    let proof = leanvm_core::cpu::scalar_proof(&proof);
    let iv = primitives::hash::hash(LABEL);
    let (log_steps, mut depth_v, mut rate_v, mut log_v) = (shape.n_log(), depth, rate, shape.n_log());
    if lie == Lie::Statement {
        match src.below(3) {
            0 => depth_v = DEPTHS[(DEPTHS.iter().position(|&d| d == depth).unwrap() + src.range(1, 6)) % DEPTHS.len()],
            1 => rate_v = 1 + (rate + src.range(0, 2)) % 4,
            _ => log_v = log_steps + 1,
        }
    }
    let verdict = catch(|| verifier::verify_keccak_batch(&iv, log_v, depth_v, rate_v, &proof))
        .map_err(|(m, l)| Finding::panic(&m, &l).in_context("soundness-keccak-batch"))?;
    match (lie, verdict) {
        (Lie::Honest, Ok(())) => Ok(()),
        (Lie::Honest, Err(e)) => Err(Finding::high(
            format!(
                "soundness-keccak-batch: an honest batch proof is rejected: {}",
                super::fixtures::verifier_error_name(&e)
            ),
            detail,
        )),
        (Lie::Spare, Ok(())) => {
            ctx.note("spare slots unbound, as expected");
            Ok(())
        }
        (lie, Err(e)) => {
            ctx.note(format!("{lie:?} rejected {}", super::fixtures::verifier_error_name(&e)));
            Ok(())
        }
        (lie, Ok(())) => Err(Finding::critical(
            format!("soundness-keccak-batch: a {lie:?} forgery verifies"),
            format!("{detail}; checked as log_steps {log_v}, depth {depth_v}, rate {rate_v}"),
        )),
    }
}

/// The stacked sizes `verify_keccak_batch` admits.
fn verifier_bounds() -> std::ops::RangeInclusive<usize> {
    leanvm_core::pcs::MIN_MU..=leanvm_core::pcs::MAX_MU
}
