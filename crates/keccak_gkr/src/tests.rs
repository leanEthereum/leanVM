use fiat_shamir::transcript::{Proof, ProverState};
use primitives::field::F192;
use primitives::multilinear::eq_table;
use primitives::test_rng::Rng;
use verifier::VerifierError;

use crate::batch_bench::{batch_transcript, open_commitment, scalar_proof};
use crate::keccak::{BITS, LANES, LOCAL_VARS};
use crate::open::state_words;
use crate::protocol::{Claim, first_claim};
use crate::prover::prove_layer;
use crate::rmfe::PROD_BITS;
use crate::witness::{BLOCK, BLOCK_LEN, BLOCK_WORDS, Extent, Shape, Witness, block};

/// The sliced state after `round` rounds.
fn state_after(witness: &Witness, round: usize) -> Vec<u64> {
    (0..witness.shape.n_blocks())
        .flat_map(|g| (0..BITS).flat_map(move |j| state_words(witness, round, g, j)))
        .collect()
}

/// A claim's value, from its definition.
fn evaluate(shape: Shape, states: &[Vec<u64>], claim: &Claim) -> F192 {
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
    let mut committed = vec![primitives::field::F64(0); 1 << shape.stack_log()];
    let witness = Witness::generate(shape, &inputs, &mut committed);
    let outputs: Vec<_> = (0..shape.segments())
        .map(|m| state_after(&witness, depth * (m + 1)))
        .collect();
    let segment_inputs: Vec<_> = (0..shape.segments())
        .map(|m| state_after(&witness, depth * m))
        .collect();

    let mut ps = ProverState::from_label(b"keccak-gkr-test");
    let (r_low, point, r_lane) = (ps.sample_vec(4), ps.sample_vec(shape.y_vars()), ps.sample_vec(5));
    let mut claim = first_claim(shape, &r_low, point, &r_lane);
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

const LABEL: &[u8] = b"keccak-gkr-test";

fn verify(shape: Shape, proof: &Proof) -> Result<(), VerifierError> {
    let iv = primitives::hash::hash(LABEL);
    let log_inv_rate = pcs::whir::LOG_INV_RATE_0;
    verifier::verify_keccak_batch(&iv, shape.n_log(), shape.depth(), log_inv_rate, &scalar_proof(proof))
}

/// A proof of the batch `inputs`, its output claim offset by `lane_error` in one lane.
fn prove(shape: Shape, inputs: &[[u64; LANES]], committed: &[primitives::field::F64], lane_error: F192) -> Proof {
    use pcs::whir::{INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, commit, config_for_rate};

    let mut honest = vec![primitives::field::F64(0); 1 << shape.stack_log()];
    let witness = Witness::generate(shape, inputs, &mut honest);
    let config = config_for_rate(shape.stack_log(), LOG_INV_RATE_0).expect("WHIR configuration");
    let mut ps = batch_transcript(LABEL, shape, LOG_INV_RATE_0);
    let (commitment, prover_data) = commit(committed, shape.stack_log(), INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
    ps.add_root(&commitment.root);
    let mut output = crate::OutputClaim::of_inputs(shape, inputs, ps.sample_vec(shape.n_log()));
    output.lanes[7] += lane_error;
    ps.add_scalars(&output.lanes);
    let openings = witness.prove(&mut ps, committed, &output);
    // The states must be the honest ones; what rides the spare slots past them is free.
    if lane_error == F192::ZERO && committed[..shape.slots() * shape.n()] == honest[..shape.slots() * shape.n()] {
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
    open_commitment(&mut ps, shape, committed, &prover_data, &config, openings);
    ps.into_proof()
}

/// The Keccak check that rejects a change to stream scalar `at`, if the reduction reads it:
/// after the root come the output lanes and the committed outputs' value, which the first
/// layer's product check meets, then the layers, then the two openings.
fn keccak_check(shape: Shape, at: usize) -> Option<VerifierError> {
    let committed = usize::from(shape.segments() > 1);
    let layer = PROD_BITS + 2 * shape.y_vars() + 3 * LOCAL_VARS + 3;
    let layers = 2 + LANES + committed;
    let outputs = layers + shape.depth() * layer;
    let inputs = outputs + committed * (2 * shape.slot_log() + 1);
    let end = inputs + 2 * (4 + shape.slot_log()) + 64;
    Some(match at {
        _ if at < 2 || at >= end => return None,
        _ if at < layers => VerifierError::KeccakProduct,
        _ if at < outputs && (at - layers) % layer < PROD_BITS => VerifierError::KeccakProduct,
        _ if at < outputs => VerifierError::KeccakLayer,
        _ if at < inputs => VerifierError::KeccakOutputOpening,
        _ => VerifierError::KeccakInputOpening,
    })
}

fn end_to_end(n_instances: usize, depth: usize) {
    let mut rng = Rng::new(77);
    let inputs: Vec<[u64; LANES]> = (0..n_instances)
        .map(|_| std::array::from_fn(|_| rng.next_u64()))
        .collect();
    let shape = Shape::new(n_instances, depth);
    let mut committed = vec![primitives::field::F64(0); 1 << shape.stack_log()];
    Witness::generate(shape, &inputs, &mut committed);
    // Other columns ride the slots the states leave free (§cpu). The reduction weighs nothing
    // there, but its openings are claims on the whole committed block, so they have to fold
    // whatever sits in them: junk here, and the checks against the commitment below are what
    // say the fold did.
    for word in &mut committed[shape.slots() * shape.n()..] {
        *word = primitives::field::F64(rng.next_u64());
    }
    let proof = prove(shape, &inputs, &committed, F192::ZERO);
    verify(shape, &proof).expect("an honest proof verifies");
    for at in (2..proof.stream.len()).step_by(proof.stream.len() / 31 + 1) {
        let mut bad = proof.clone();
        bad.stream[at] += F192::ONE;
        let err = verify(shape, &bad).expect_err("a changed scalar is rejected");
        if let Some(check) = keccak_check(shape, at) {
            assert_eq!(err, check, "scalar {at}");
        }
    }
}

/// Both openings are claims on the whole committed block, so the spare slots the reduction folds
/// have to be the ones that were committed: a prover that folds any other word is rejected, which
/// is what lets other columns ride there at all.
#[test]
fn spare_slots_must_be_the_committed_ones() {
    use pcs::whir::{INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, commit, config_for_rate};

    let mut rng = Rng::new(81);
    let (n, depth) = (600, 12);
    let inputs: Vec<[u64; LANES]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    let shape = Shape::new(n, depth);
    let states = shape.slots() * shape.n();
    let mut committed = vec![primitives::field::F64(0); 1 << shape.stack_log()];
    let witness = Witness::generate(shape, &inputs, &mut committed[..states]);
    for word in &mut committed[states..] {
        *word = primitives::field::F64(rng.next_u64());
    }
    // One word of the spare slots apart from what the commitment holds.
    let mut folded = committed.clone();
    folded[states] = primitives::field::F64(folded[states].0 ^ 1);

    let config = config_for_rate(shape.stack_log(), LOG_INV_RATE_0).expect("WHIR configuration");
    let mut ps = batch_transcript(LABEL, shape, LOG_INV_RATE_0);
    let (commitment, prover_data) = commit(&committed, shape.stack_log(), INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
    ps.add_root(&commitment.root);
    let output = crate::OutputClaim::of_inputs(shape, &inputs, ps.sample_vec(shape.n_log()));
    ps.add_scalars(&output.lanes);
    let openings = witness.prove(&mut ps, &folded, &output);
    open_commitment(&mut ps, shape, &committed, &prover_data, &config, openings);
    verify(shape, &ps.into_proof()).expect_err("a spare slot that was not committed is rejected");
}

#[test]
fn proof_verifies_against_the_commitment() {
    end_to_end(600, 8);
    end_to_end(1024, 24);
    // The VM's depth, over enough blocks that the input opening folds more than one run.
    end_to_end(8192, 12);
    end_to_end(8192, 6);
}

/// The witness of every block run, the padding ones included.
fn dense(shape: Shape, inputs: &[[u64; LANES]]) -> Witness {
    let mut extent = Extent::new(0, shape.n_blocks());
    for g in 0..shape.n_blocks() {
        let inputs = &inputs[(g * BLOCK).min(inputs.len())..((g + 1) * BLOCK).min(inputs.len())];
        // SAFETY: each block's slot, written once.
        unsafe { block(shape.depth(), inputs, extent.slot(g), |_, _, _| {}) };
    }
    // SAFETY: every block was written just above.
    unsafe { Witness::from_extents(shape, vec![extent], shape.n_blocks(), None) }
}

/// The padding block, run once for the blocks after the last input, proves what running each
/// of them does, whichever variables the boundary between them falls on.
#[test]
fn padding_proves_as_the_blocks_it_stands_for() {
    let mut rng = Rng::new(79);
    for (n, depth) in [(0, 12), (300, 24), (1100, 8), (2600, 12), (4700, 6)] {
        let inputs: Vec<[u64; LANES]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
        let shape = Shape::new(n, depth);
        let mut committed = vec![primitives::field::F64(0); 1 << shape.stack_log()];
        let padded = Witness::generate(shape, &inputs, &mut committed);
        let stream = |witness: &Witness| {
            let mut ps = ProverState::from_label(LABEL);
            let output = crate::OutputClaim::of_inputs(shape, &inputs, ps.sample_vec(shape.n_log()));
            ps.add_scalars(&output.lanes);
            let openings = witness.prove(&mut ps, &committed, &output);
            (openings, ps.into_proof())
        };
        assert!(stream(&padded) == stream(&dense(shape, &inputs)), "{n} instances");
    }
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
    let mut committed = vec![primitives::field::F64(0); 1 << shape.stack_log()];
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
