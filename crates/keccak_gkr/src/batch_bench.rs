//! The standalone batch benchmark, shared by the `hash_batch` bench target and `cargo leanvm hash`:
//! witness, commitment, reduction and opening of `n` random permutations, then verification.

use std::time::Instant;

use bench::{Metric, Plan, Timing, bencher_json};
use fiat_shamir::transcript::{Proof, ProverState};
use pcs::stack_open::StackClaim;
use pcs::whir::{INITIAL_FOLDING_FACTOR, ProverConfig, ProverData, commit, config_for_rate};
use primitives::{
    field::{F64, F128},
    pretty_integer,
    test_rng::Rng,
};

use crate::{Openings, OutputClaim, Shape, Witness};

const LABEL: &[u8] = b"keccak-gkr-batch";

/// The timings and proof size of one run of [`run`].
pub struct Report {
    shape: Shape,
    /// Witness, commit, output claim, reduction, opening, whole pass.
    stages: [Timing; 6],
    verify: Timing,
    stream_len: usize,
    merkle_bytes: usize,
}

/// Prove `n` random permutations, a state committed every `depth` rounds, with one warmup pass
/// then `plan.repeat` measured ones, and verify the proof. The output is not committed: a claim
/// on it is bound in the transcript, as the VM's memory bus does.
pub fn run(n: usize, depth: usize, log_inv_rate: usize, plan: Plan) -> Report {
    let shape = Shape::new(n, depth);
    let mu = shape.stack_log();
    let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15 ^ n as u64);
    let inputs: Vec<[u64; 25]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    let config = config_for_rate(mu, log_inv_rate).expect("WHIR configuration");

    let prove_pass = || {
        let _span = tracing::info_span!("Keccak GKR prove", n).entered();
        let t_pass = Instant::now();
        let t = Instant::now();
        // SAFETY: the witness generator writes every word.
        let mut committed = unsafe { primitives::uninit_vec::<F64>(1 << mu) };
        let witness = tracing::info_span!("Witness").in_scope(|| Witness::generate(shape, &inputs, &mut committed));
        let witness_s = t.elapsed().as_secs_f64();

        let mut ps = batch_transcript(LABEL, shape, log_inv_rate);
        let t = Instant::now();
        let (prover_data, ood) = commit_stack(&mut ps, shape, &committed, log_inv_rate);
        let commit_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let instance = batch_instance(&mut ps, shape);
        let output = tracing::info_span!("Output claim").in_scope(|| OutputClaim::of_inputs(shape, &inputs, instance));
        ps.add_scalars(&output.lanes);
        let output_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let openings = witness.prove(&mut ps, &committed, &output);
        let gkr_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        open_commitment(&mut ps, shape, committed, prover_data, &config, openings, ood);
        let open_s = t.elapsed().as_secs_f64();

        (
            ps.into_proof(),
            [
                witness_s,
                commit_s,
                output_s,
                gkr_s,
                open_s,
                t_pass.elapsed().as_secs_f64(),
            ],
        )
    };

    let mut stages: [Timing; 6] = std::array::from_fn(|_| Timing::default());
    let mut warm = true;
    let (transcript, _) = plan.warm_then_measure(|final_pass| {
        let _quiet = (!final_pass).then(bench::suppress_tracing);
        let (proof, secs) = prove_pass();
        if !std::mem::take(&mut warm) {
            for (timing, s) in stages.iter_mut().zip(secs) {
                timing.push(s);
            }
        }
        proof
    });

    let proof = scalar_proof(&transcript);
    let iv = primitives::hash::hash(LABEL);
    let (_, verify) = Plan::new(plan.repeat, 0).measure_quiet(|_| {
        verifier::verify_keccak_batch(&iv, shape.n_log(), shape.depth(), log_inv_rate, &proof)
            .expect("the batch proof verifies");
    });

    let merkle_bytes = transcript.to_bytes().len() - 16 * transcript.stream.len();
    Report {
        shape,
        stages,
        verify,
        stream_len: transcript.stream.len(),
        merkle_bytes,
    }
}

impl Report {
    /// The proving time in Bencher Metric Format, which is what CI compares.
    pub fn json(&self) -> String {
        let name = format!("keccak-hash-batch-{}", self.shape.n());
        bencher_json(&[(name, vec![("latency", Metric::nanoseconds(&self.stages[5]))])])
    }

    pub fn print(&self) {
        let [witness, commit, output, gkr, open, pass] = &self.stages;
        let pass_s = pass.mean();
        let line = |name: &str, t: &Timing| {
            println!(
                "  {name:<32}: {:>8.1} ms{} {:>6.1}%",
                t.mean() * 1e3,
                t.spread(),
                100.0 * t.mean() / pass_s
            );
        };
        let n = self.shape.n();
        println!(
            "\nKeccak GKR batch proving, {} permutations, a state committed every {} rounds",
            pretty_integer(n),
            self.shape.depth()
        );
        line("witness", witness);
        line("commit", commit);
        line("output claim", output);
        line("layers and openings", gkr);
        line("pcs opening", open);
        println!("  ------------------------------------------");
        println!(
            "  {:<32}: {:>8.1} ms{}",
            "prove TOTAL (witness included)",
            pass_s * 1e3,
            pass.spread()
        );
        println!("  {:<32}: {:>8.1} ms", "verify", self.verify.mean() * 1e3);
        println!(
            "  {:<32}: {:>14} permutations/s{}",
            "throughput",
            pretty_integer((n as f64 / pass_s).round() as u64),
            pass.spread()
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
    let statement = [shape.n_log(), shape.depth(), log_inv_rate, 0].map(|w| F64(w as u64));
    ProverState::new(iv, statement)
}

/// Commit to `stack`, send the root and take its OOD sample ([`pcs::ood`]): what precedes the output claim.
pub(crate) fn commit_stack(
    ps: &mut ProverState,
    shape: Shape,
    stack: &[F64],
    log_inv_rate: usize,
) -> (ProverData, StackClaim) {
    let (commitment, prover_data) = commit(stack, shape.stack_log(), INITIAL_FOLDING_FACTOR, log_inv_rate);
    ps.add_root(&commitment.root);
    let ood = pcs::ood::ood_sample(ps, stack, shape.stack_log());
    (prover_data, ood)
}

/// The instance a batch's output is claimed at, after its grind: the point pins the committed middle states, a
/// multilinear identity of degree `n_log` in it.
pub(crate) fn batch_instance(ps: &mut ProverState, shape: Shape) -> Vec<F128> {
    ps.grind(fiat_shamir::grinding_bits(shape.n_log() as u128));
    ps.sample_vec(shape.n_log())
}

/// Discharge the reduction's openings and the OOD sample's claim, after them, against the commitment to `stack`, which
/// holds the committed states alone.
pub(crate) fn open_commitment(
    ps: &mut ProverState,
    shape: Shape,
    stack: Vec<F64>,
    prover_data: ProverData,
    config: &ProverConfig,
    openings: Openings,
    ood: StackClaim,
) {
    let (ring, outputs) = openings.into_pcs_claims(0);
    let points: Vec<_> = outputs.into_iter().chain([ood]).collect();
    pcs::stack_open::open_batch_mixed_whir_stacked(ps, shape.stack_log(), stack, prover_data, config, &points, &ring);
}

/// The proof in the `verifier` crate's types: the same limbs, digests and leaf words.
pub(crate) fn scalar_proof(proof: &Proof) -> verifier::Proof {
    let path = |path: &fiat_shamir::merkle::MerklePath| verifier::MerklePath {
        leaf_index: path.leaf_index,
        leaf: path.leaf.iter().map(|word| verifier::K(word.0)).collect(),
        siblings: path.siblings.clone(),
    };
    let openings = proof.merkle.iter().map(|phase| phase.iter().map(path).collect());
    verifier::Proof {
        stream: proof.stream.iter().map(|x| verifier::E::new(x.c0, x.c1)).collect(),
        merkle_openings: openings.collect(),
    }
}
