//! The standalone batch benchmark, shared by the `hash_batch` bench target and `cargo leanvm hash`:
//! witness, commitment, reduction and opening of `n` random permutations, then verification.

use std::time::Instant;

use bench::{Metric, Plan, Timing, bencher_json};
use fiat_shamir::transcript::Proof;
use pcs::whir::{INITIAL_FOLDING_FACTOR, commit, config_for_rate};
use primitives::{field::F64, pretty_integer, test_rng::Rng};

use crate::{OutputClaim, Shape, Witness};

const LABEL: &[u8] = b"keccak-gkr-batch";

/// The timings and proof size of one run of [`run`].
pub struct Report {
    shape: Shape,
    /// Witness, commit, reduction, opening, whole pass.
    stages: [Timing; 5],
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
        let mut committed = unsafe { primitives::uninit_vec::<F64>(crate::committed_len(shape)) };
        let witness = tracing::info_span!("Witness").in_scope(|| Witness::generate(shape, &inputs, &mut committed));
        let witness_s = t.elapsed().as_secs_f64();

        let mut ps = crate::batch_transcript(LABEL, shape, log_inv_rate);
        let t = Instant::now();
        let (commitment, prover_data) = commit(&committed, mu, INITIAL_FOLDING_FACTOR, log_inv_rate);
        ps.add_root(&commitment.root);
        let commit_s = t.elapsed().as_secs_f64();

        let output = OutputClaim::of_inputs(shape, &inputs, ps.sample_vec(shape.n_log()));
        ps.add_scalars(&output.lanes);
        let t = Instant::now();
        let openings = crate::prove(&mut ps, &witness, &committed, &output);
        let gkr_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        crate::open_commitment(&mut ps, shape, &committed, &prover_data, &config, openings);
        let open_s = t.elapsed().as_secs_f64();

        (
            ps.into_proof(),
            [witness_s, commit_s, gkr_s, open_s, t_pass.elapsed().as_secs_f64()],
        )
    };

    let mut stages: [Timing; 5] = std::array::from_fn(|_| Timing::default());
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

    let merkle_bytes = transcript
        .merkle
        .iter()
        .map(|m| 8 * m.leaf_data.iter().map(Vec::len).sum::<usize>() + 32 * m.sibling_hashes.len())
        .sum();
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
        bencher_json(&[(name, vec![("latency", Metric::nanoseconds(&self.stages[4]))])])
    }

    pub fn print(&self) {
        let [witness, commit, gkr, open, pass] = &self.stages;
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
        let proof_bytes = 24 * self.stream_len + self.merkle_bytes;
        println!(
            "  {:<32}: {:>11.1} KiB  ({} scalars, {:.1} KiB of Merkle openings)",
            "proof size",
            proof_bytes as f64 / 1024.0,
            self.stream_len,
            self.merkle_bytes as f64 / 1024.0
        );
    }
}

/// The wire proof in the `verifier` crate's types: the same limbs, digests and row words.
fn scalar_proof(proof: &Proof) -> verifier::Proof {
    let batches = proof.merkle.iter().map(|paths| verifier::PrunedMerklePaths {
        leaf_data: paths
            .leaf_data
            .iter()
            .map(|row| row.iter().map(|word| verifier::K(word.0)).collect())
            .collect(),
        sibling_hashes: paths.sibling_hashes.clone(),
    });
    verifier::Proof {
        stream: proof
            .stream
            .iter()
            .map(|x| verifier::E::new(x.c0, x.c1, x.c2))
            .collect(),
        merkle_openings: verifier::MerkleOpenings::Pruned(batches.collect()),
    }
}
