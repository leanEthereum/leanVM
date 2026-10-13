use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::F192;
use primitives::multilinear::eq_table;
use primitives::test_rng::Rng;

use crate::keccak::{BITS, LANES, along, iota_bit};
use crate::protocol::{Claim, first_claim, verify_layer};
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
    ps.add_scalar(claim.value);
    let mut scratch = crate::prover::Scratch::new(shape);
    for step in 0..depth {
        claim = prove_layer(&mut ps, &witness, &mut scratch, step, &claim);
    }
    assert_eq!(
        claim.value,
        evaluate(shape, &segment_inputs, &claim),
        "the prover's last claim holds"
    );
    let proof = ps.into_proof();

    let verify = |proof: &fiat_shamir::transcript::Proof| {
        let mut vs = VerifierState::from_label(b"keccak-gkr-test", proof);
        let (r_low, point, r_lane) = (vs.sample_vec(4), vs.sample_vec(shape.y_vars()), vs.sample_vec(5));
        let value = vs.next_scalar().ok()?;
        let mut claim = first_claim(shape, value, &r_low, point, &r_lane);
        for step in 0..depth {
            claim = verify_layer(&mut vs, shape, step, &claim).ok()?;
        }
        vs.finish().ok()?;
        Some(claim)
    };
    assert_eq!(verify(&proof), Some(claim), "the verifier reaches the same claim");

    // Any changed scalar is rejected, or leaves a claim the inputs do not satisfy.
    for at in (0..proof.stream.len()).step_by(proof.stream.len() / 23 + 1) {
        let mut bad = proof.clone();
        bad.stream[at] += F192::ONE;
        if let Some(claim) = verify(&bad) {
            assert_ne!(claim.value, evaluate(shape, &segment_inputs, &claim), "scalar {at}");
        }
    }
}

#[test]
fn layers_reduce_outputs_to_inputs() {
    layers_round_trip(700, 8);
}

#[test]
fn one_segment_and_two_blocks() {
    layers_round_trip(1024, 24);
}

fn end_to_end(n_instances: usize, depth: usize) {
    use pcs::whir::{INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, commit, config_for_rate};

    let mut rng = Rng::new(77);
    let inputs: Vec<[u64; LANES]> = (0..n_instances)
        .map(|_| std::array::from_fn(|_| rng.next_u64()))
        .collect();
    let shape = Shape::new(n_instances, depth);
    let mut committed = vec![primitives::field::F64(0); crate::committed_len(shape)];
    let witness = Witness::generate(shape, &inputs, &mut committed);
    let config = config_for_rate(shape.stack_log(), LOG_INV_RATE_0).expect("WHIR configuration");

    let mut ps = ProverState::from_label(b"keccak-gkr-test");
    let (commitment, prover_data) = commit(&committed, shape.stack_log(), INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
    ps.add_root(&commitment.root);
    let openings = crate::prove(&mut ps, &witness, &committed);
    // Each opening is what the commitment scheme means by it.
    let mut stack = committed.clone();
    stack.resize(1 << shape.stack_log(), primitives::field::F64(0));
    assert_eq!(
        openings.outputs.value,
        primitives::multilinear::mle_eval(&stack, &openings.outputs.point),
        "outputs"
    );
    let slices = pcs::ring_switch::fold_1b_rows(&stack, &eq_table(&openings.inputs.point));
    assert!(slices == openings.inputs.slices, "inputs");
    crate::open_commitment(&mut ps, shape, &committed, &prover_data, &config, openings);
    let proof = ps.into_proof();

    let verify = |proof: &fiat_shamir::transcript::Proof| {
        let mut vs = VerifierState::from_label(b"keccak-gkr-test", proof);
        let root = vs.next_root().ok()?;
        let openings = crate::verify(&mut vs, shape).ok()?;
        crate::verify_commitment(&mut vs, shape, &config, &root, &openings).ok()?;
        vs.finish().ok()
    };
    {
        let mut vs = VerifierState::from_label(b"keccak-gkr-test", &proof);
        let root = vs.next_root().unwrap();
        let openings = crate::verify(&mut vs, shape).expect("layers and openings");
        crate::verify_commitment(&mut vs, shape, &config, &root, &openings).expect("commitment");
        vs.finish().unwrap();
    }
    assert!(verify(&proof).is_some(), "an honest proof verifies");
    for at in (2..proof.stream.len()).step_by(proof.stream.len() / 31 + 1) {
        let mut bad = proof.clone();
        bad.stream[at] += F192::ONE;
        assert!(verify(&bad).is_none(), "scalar {at}");
    }
}

#[test]
fn proof_verifies_against_the_commitment() {
    end_to_end(600, 8);
    end_to_end(512, 12);
}
