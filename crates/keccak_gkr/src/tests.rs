use fiat_shamir::transcript::{Proof, ProverState};
use primitives::field::F192;
use primitives::multilinear::eq_table;
use primitives::test_rng::Rng;

use crate::keccak::{BITS, LANES, along, iota_bit};
use crate::protocol::{Claim, first_claim};
use crate::prover::prove_layer;
use crate::witness::{BLOCK_LEN, BLOCK_WORDS, Shape, Witness};

/// The sliced state after `round` rounds.
pub(crate) fn state_after(witness: &Witness, round: usize) -> Vec<u64> {
    let blocks = witness.shape.n_blocks();
    if round == 0 {
        return (0..blocks).flat_map(|g| witness.input(g).to_vec()).collect();
    }
    let u: Vec<u64> = (0..blocks).flat_map(|g| witness.layer(round, g).to_vec()).collect();
    let mut out = vec![0u64; u.len()];
    for (block, out) in u
        .as_chunks::<BLOCK_LEN>()
        .0
        .iter()
        .zip(out.as_chunks_mut::<BLOCK_LEN>().0)
    {
        for j in 0..BITS {
            for w in 0..BLOCK_WORDS {
                let chi = block[j * BLOCK_WORDS + w]
                    ^ (!block[along(j, 1) * BLOCK_WORDS + w] & block[along(j, 2) * BLOCK_WORDS + w]);
                out[j * BLOCK_WORDS + w] = if j < 64 && iota_bit(round, j) { !chi } else { chi };
            }
        }
    }
    out
}

/// A claim's value, from its definition.
pub(crate) fn evaluate(shape: Shape, states: &[Vec<u64>], claim: &Claim) -> F192 {
    let eq = eq_table(&claim.point);
    let mut acc = F192::ZERO;
    for (segment, state) in states.iter().enumerate() {
        for (g, block) in state.as_chunks::<BLOCK_LEN>().0.iter().enumerate() {
            for j in 0..BITS {
                let mut inner = F192::ZERO;
                for w in 0..BLOCK_WORDS {
                    let word = block[j * BLOCK_WORDS + w];
                    for p in 0..4 {
                        let pack = 4 * w + p + 32 * (g + shape.n_blocks() * segment);
                        for i in 0..16 {
                            if word >> (16 * p + i) & 1 == 1 {
                                inner += eq[pack] * claim.mu[i];
                            }
                        }
                    }
                }
                acc += inner * claim.weights[j];
            }
        }
    }
    acc
}

/// The prover's layers end on a claim the committed inputs satisfy.
fn layers_round_trip(n_instances: usize, depth: usize) {
    let mut rng = Rng::new(21 + depth as u64);
    let inputs: Vec<[u64; LANES]> = (0..n_instances)
        .map(|_| std::array::from_fn(|_| rng.next_u64()))
        .collect();
    let shape = Shape::new(n_instances, depth);
    let mut committed = vec![primitives::field::F64(0); crate::committed_len(shape)];
    let witness = Witness::generate(shape, &inputs, &mut committed);
    let outputs: Vec<_> = (0..shape.segments())
        .map(|m| state_after(&witness, depth * (m + 1)))
        .collect();
    let segment_inputs: Vec<_> = (0..shape.segments())
        .map(|m| state_after(&witness, depth * m))
        .collect();

    let mut ps = ProverState::from_label(b"keccak-gkr-test");
    let (r_low, point, r_lane) = (ps.sample_vec(4), ps.sample_vec(shape.y_vars()), ps.sample_vec(5));
    let mut claim = first_claim(shape, F192::ZERO, &r_low, point, &r_lane);
    claim.value = evaluate(shape, &outputs, &claim);
    let mut scratch = crate::prover::Scratch::new(shape);
    for step in 0..depth {
        claim = prove_layer(&mut ps, &witness, &mut scratch, step, &claim);
    }
    assert_eq!(
        claim.value,
        evaluate(shape, &segment_inputs, &claim),
        "the prover's last claim holds"
    );
}

#[test]
fn layers_reduce_outputs_to_inputs() {
    layers_round_trip(700, 8);
}

#[test]
fn one_segment_and_two_blocks() {
    layers_round_trip(1024, 24);
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

const LABEL: &[u8] = b"keccak-gkr-test";

fn verify(shape: Shape, proof: &Proof) -> Result<(), verifier::VerifierError> {
    let iv = primitives::hash::hash(LABEL);
    let log_inv_rate = pcs::whir::LOG_INV_RATE_0;
    verifier::verify_keccak_batch(&iv, shape.n_log(), shape.depth(), log_inv_rate, &scalar_proof(proof))
}

/// A proof of the batch `inputs`, its output claim offset by `lane_error` in one lane.
fn prove(shape: Shape, inputs: &[[u64; LANES]], committed: &[primitives::field::F64], lane_error: F192) -> Proof {
    use pcs::whir::{INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, commit, config_for_rate};

    let mut honest = vec![primitives::field::F64(0); crate::committed_len(shape)];
    let witness = Witness::generate(shape, inputs, &mut honest);
    let config = config_for_rate(shape.stack_log(), LOG_INV_RATE_0).expect("WHIR configuration");
    let mut ps = crate::batch_transcript(LABEL, shape, LOG_INV_RATE_0);
    let (commitment, prover_data) = commit(committed, shape.stack_log(), INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
    ps.add_root(&commitment.root);
    let mut output = crate::OutputClaim::of_inputs(shape, inputs, ps.sample_vec(shape.n_log()));
    output.lanes[7] += lane_error;
    ps.add_scalars(&output.lanes);
    let openings = crate::prove(&mut ps, &witness, committed, &output);
    if lane_error == F192::ZERO && committed == honest {
        // Each opening is what the commitment scheme means by it.
        let mut stack = committed.to_vec();
        stack.resize(1 << shape.stack_log(), primitives::field::F64(0));
        assert_eq!(openings.outputs.is_some(), shape.segments() > 1);
        if let Some(outputs) = &openings.outputs {
            assert_eq!(
                outputs.value,
                primitives::multilinear::mle_eval(&stack, &outputs.point),
                "outputs"
            );
        }
        let slices = pcs::ring_switch::fold_1b_rows(&stack, &eq_table(&openings.inputs.point));
        assert!(slices == openings.inputs.slices, "inputs");
    }
    crate::open_commitment(&mut ps, shape, committed, &prover_data, &config, openings);
    ps.into_proof()
}

fn end_to_end(n_instances: usize, depth: usize) {
    let mut rng = Rng::new(77);
    let inputs: Vec<[u64; LANES]> = (0..n_instances)
        .map(|_| std::array::from_fn(|_| rng.next_u64()))
        .collect();
    let shape = Shape::new(n_instances, depth);
    let mut committed = vec![primitives::field::F64(0); crate::committed_len(shape)];
    Witness::generate(shape, &inputs, &mut committed);
    let proof = prove(shape, &inputs, &committed, F192::ZERO);
    verify(shape, &proof).expect("an honest proof verifies");
    for at in (2..proof.stream.len()).step_by(proof.stream.len() / 31 + 1) {
        let mut bad = proof.clone();
        bad.stream[at] += F192::ONE;
        assert!(verify(shape, &bad).is_err(), "scalar {at}");
    }
}

#[test]
fn proof_verifies_against_the_commitment() {
    end_to_end(600, 8);
    end_to_end(1024, 24);
    // The VM's depth, over enough blocks that the input opening folds more than one run.
    end_to_end(8192, 12);
    end_to_end(8192, 6);
}

/// A committed state that does not follow the permutation is rejected, whichever state it
/// is, and so is an output claim the inputs do not give: the honest prover run on a column
/// with one bit flipped, or on a perturbed claim, fails the reduction or the commitment's
/// opening.
#[test]
fn a_broken_committed_state_is_rejected() {
    let mut rng = Rng::new(78);
    let inputs: Vec<[u64; LANES]> = (0..600).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    let shape = Shape::new(inputs.len(), 6);
    let mut committed = vec![primitives::field::F64(0); crate::committed_len(shape)];
    Witness::generate(shape, &inputs, &mut committed);
    let accepts = |committed: &[primitives::field::F64], lane_error: F192| {
        verify(shape, &prove(shape, &inputs, committed, lane_error)).is_ok()
    };
    assert!(accepts(&committed, F192::ZERO), "the honest column");
    // A lane of the input and of each state between.
    for slot in [3, 30, 60, 80, 99] {
        let mut bad = committed.clone();
        bad[slot * shape.n() + 17].0 ^= 1 << 40;
        assert!(!accepts(&bad, F192::ZERO), "slot {slot}");
    }
    assert!(!accepts(&committed, F192::ONE), "the output");
}
