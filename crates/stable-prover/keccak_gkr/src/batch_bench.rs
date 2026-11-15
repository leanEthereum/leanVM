//! The standalone batch benchmark of the `hash_batch` bench target and the tests: witness, commitment, reduction and
//! opening of `n` random permutations, then verification. Where a pass's time goes is its span tree.

use bench::{Metric, Plan, Timing, bencher_json};
use pcs::Committed;
use primitives::field::{F64, F128Unreduced};
use primitives::multilinear::eq_table;
use primitives::{pretty_integer, test_rng::Rng, transcript::ProverState};

use crate::keccak::LANES;
use crate::{Openings, OutputClaim, Shape, Witness};

const LABEL: &[u8] = b"keccak-gkr-batch";

/// The timings and proof size of one run of [`run`].
pub struct Report {
    shape: Shape,
    /// A whole pass, the witness included.
    prove: Timing,
    verify: Timing,
    stream_len: usize,
    merkle_bytes: usize,
}

/// Prove `n` random permutations, a state committed every `depth` rounds, with one warmup pass then `plan.repeat`
/// measured ones, and verify the proof. The output is not committed: a claim on it is bound in the transcript, as the
/// VM's memory bus does.
pub fn run(n: usize, depth: usize, log_inv_rate: usize, plan: Plan) -> Report {
    let shape = Shape::new(n, depth);
    let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15 ^ n as u64);
    let inputs: Vec<[u64; LANES]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();

    let (proof, prove) = plan.warm_then_measure(|final_pass| {
        let _quiet = (!final_pass).then(bench::suppress_tracing);
        let _span = tracing::info_span!("Keccak GKR prove", n).entered();
        let mut committed = vec![F64(0); 1 << shape.stack_log()];
        let witness = tracing::info_span!("Witness").in_scope(|| Witness::generate(shape, &inputs, &mut committed));
        let mut ps = batch_transcript(LABEL, shape, log_inv_rate);
        let commitment = pcs::commit(&mut ps, &committed, shape.stack_log(), log_inv_rate);
        let output = tracing::info_span!("Output claim").in_scope(|| output_claim(&mut ps, shape, &inputs));
        ps.add_scalars(&output.lanes);
        let openings = witness.prove(&mut ps, &committed, &output);
        open_commitment(&mut ps, commitment, committed, openings);
        ps.into_proof()
    });

    let iv = primitives::hash::hash(LABEL);
    let (_, verify) = Plan::new(plan.repeat, 0).measure_quiet(|_| {
        verifier::verify_keccak_batch(&iv, shape.n_log(), shape.depth(), log_inv_rate, &proof)
            .expect("the batch proof verifies");
    });

    Report {
        shape,
        prove,
        verify,
        stream_len: proof.stream.len(),
        merkle_bytes: proof.to_bytes().len() - 16 * proof.stream.len(),
    }
}

impl Report {
    /// The proving time in Bencher Metric Format, which is what CI compares.
    pub fn json(&self) -> String {
        let name = format!("keccak-hash-batch-{}", self.shape.n());
        bencher_json(&[(name, vec![("latency", Metric::nanoseconds(&self.prove))])])
    }

    pub fn print(&self) {
        let n = self.shape.n();
        let prove_s = self.prove.mean();
        println!(
            "\nKeccak GKR batch proving, {} permutations, a state committed every {} rounds",
            pretty_integer(n),
            self.shape.depth()
        );
        println!(
            "  {:<32}: {:>8.1} ms{}",
            "prove (witness included)",
            prove_s * 1e3,
            self.prove.spread()
        );
        println!("  {:<32}: {:>8.1} ms", "verify", self.verify.mean() * 1e3);
        println!(
            "  {:<32}: {:>14} permutations/s{}",
            "throughput",
            pretty_integer((n as f64 / prove_s).round() as u64),
            self.prove.spread()
        );
        let proof_bytes = 16 * self.stream_len + self.merkle_bytes;
        println!(
            "  {:<32}: {:>11.1} KiB  ({} scalars, {:.1} KiB of Merkle openings)",
            "proof size",
            proof_bytes as f64 / 1024.0,
            self.stream_len,
            self.merkle_bytes as f64 / 1024.0
        );
    }
}

/// The transcript of a batch proved alone, as `verifier::verify_keccak_batch` reads it: seeded
/// from `label` and, as its public input, the shape and the PCS rate.
pub(crate) fn batch_transcript(label: &[u8], shape: Shape, log_inv_rate: usize) -> ProverState {
    let iv = fiat_shamir::digest_words(&primitives::hash::hash(label));
    let statement = [shape.n_log(), shape.depth(), log_inv_rate, 0].map(|w| w as u64);
    ProverState::new(iv, statement)
}

/// The true claim on the batch of `inputs`, padded with all-zero inputs, at the instance drawn after its grind: the
/// point pins the committed middle states, a multilinear identity of degree `n_log` in it. The caller binds the lanes.
pub(crate) fn output_claim(ps: &mut ProverState, shape: Shape, inputs: &[[u64; LANES]]) -> OutputClaim {
    ps.grind(fiat_shamir::grinding_bits(shape.n_log() as u128));
    let instance = ps.sample_vec(shape.n_log());
    let permute = |mut state: [u64; LANES]| {
        primitives::hash::keccak_f(&mut state);
        state
    };
    let padding = permute([0; LANES]);
    let eq = eq_table(&instance);
    let lanes = parallel::fold_reduce(
        shape.n(),
        || [F128Unreduced::ZERO; LANES],
        |acc, i| {
            let output = inputs.get(i).map_or(padding, |&x| permute(x));
            for (acc, word) in acc.iter_mut().zip(output) {
                *acc ^= eq[i].mul_base_unreduced(F64(word));
            }
        },
        |mut a, b| {
            for (a, b) in a.iter_mut().zip(b) {
                *a ^= b;
            }
            a
        },
    );
    OutputClaim {
        instance,
        lanes: lanes.map(F128Unreduced::reduce),
    }
}

/// Discharge the reduction's openings and the OOD sample's claim, after them, against the commitment to `stack`, which
/// holds the committed states alone.
pub(crate) fn open_commitment(ps: &mut ProverState, committed: Committed, stack: Vec<F64>, openings: Openings) {
    let (ring, outputs) = openings.into_pcs_claims(0);
    pcs::open(ps, committed, stack, outputs.as_slice(), &ring);
}
