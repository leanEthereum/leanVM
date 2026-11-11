use fiat_shamir::transcript::{Proof, ProverState};
use primitives::field::F128;
use primitives::multilinear::eq_table;
use primitives::test_rng::Rng;
use verifier::VerifierError;

use crate::batch_bench::{batch_instance, batch_transcript, commit_stack, open_commitment, scalar_proof};
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
fn evaluate(shape: Shape, states: &[Vec<u64>], claim: &Claim) -> F128 {
    let eq = eq_table(&claim.point);
    let mut acc = F128::ZERO;
    for (segment, state) in states.iter().enumerate() {
        for (g, block) in state.as_chunks::<BLOCK_LEN>().0.iter().enumerate() {
            for j in 0..BITS {
                let mut inner = F128::ZERO;
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
fn prove(shape: Shape, inputs: &[[u64; LANES]], committed: &[primitives::field::F64], lane_error: F128) -> Proof {
    use pcs::whir::{LOG_INV_RATE_0, config_for_rate};

    let mut honest = vec![primitives::field::F64(0); 1 << shape.stack_log()];
    let witness = Witness::generate(shape, inputs, &mut honest);
    let config = config_for_rate(shape.stack_log(), LOG_INV_RATE_0).expect("WHIR configuration");
    let mut ps = batch_transcript(LABEL, shape, LOG_INV_RATE_0);
    let (prover_data, ood) = commit_stack(&mut ps, shape, committed, LOG_INV_RATE_0);
    let mut output = crate::OutputClaim::of_inputs(shape, inputs, batch_instance(&mut ps, shape));
    output.lanes[7] += lane_error;
    ps.add_scalars(&output.lanes);
    let openings = witness.prove(&mut ps, committed, &output);
    // The states must be the honest ones; what rides the spare slots past them is free.
    if lane_error == F128::ZERO && committed[..shape.slots() * shape.n()] == honest[..shape.slots() * shape.n()] {
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
        assert!(openings.inputs.slices == slices, "inputs");
    }
    open_commitment(&mut ps, shape, committed.to_vec(), prover_data, &config, openings, ood);
    ps.into_proof()
}

/// The Keccak check that rejects a change to stream scalar `at`, if one meets it before any grind does (a grind of
/// few bits may still pass a changed transcript, so what catches those is left open). After the root, the OOD sample's
/// nonce and value and the instance's nonce come the output lanes, the segment and lane nonce, the committed
/// outputs' value, which the first layer's product check meets, then the layers, then the two openings. A round is
/// its scalars and its nonce, and a grind of zero bits sends none.
fn keccak_check(shape: Shape, at: usize) -> Option<VerifierError> {
    let nonce = |numerator: usize| usize::from(fiat_shamir::grinding_bits(numerator as u128) > 0);
    let committed = usize::from(shape.segments() > 1);
    // A sumcheck round of degree 2 or 3 sends two scalars; the bit position's, of degree 3 with no eq factor, three.
    let (round2, round3) = (2 + nonce(2), 2 + nonce(3));
    let layer = PROD_BITS + nonce(PROD_BITS - 1) + round3 * shape.y_vars() + (round3 + 1) * LOCAL_VARS + 3 + nonce(2);
    let first = 2 + 1 + 1 + nonce(shape.n_log()) + LANES + nonce(shape.seg_log() + 5);
    let layers = first + committed;
    let outputs = layers + shape.depth() * layer;
    let word = outputs + committed * round2 * shape.slot_log();
    let inputs = word + committed;
    let slices = inputs + round2 * (4 + shape.slot_log());
    let in_layer = at.wrapping_sub(layers) % layer;
    Some(match at {
        _ if (first..layers).contains(&at) => VerifierError::KeccakProduct,
        _ if (layers..outputs).contains(&at) && in_layer < PROD_BITS => VerifierError::KeccakProduct,
        _ if (layers..outputs).contains(&at) && (layer - 3 - nonce(2)..layer - nonce(2)).contains(&in_layer) => {
            VerifierError::KeccakLayer
        }
        _ if (word..inputs).contains(&at) => VerifierError::KeccakOutputOpening,
        _ if (slices..slices + 64).contains(&at) => VerifierError::KeccakInputOpening,
        _ => return None,
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
    let proof = prove(shape, &inputs, &committed, F128::ZERO);
    verify(shape, &proof).expect("an honest proof verifies");
    for at in (2..proof.stream.len()).step_by(proof.stream.len() / 31 + 1) {
        let mut bad = proof.clone();
        bad.stream[at] += F128::ONE;
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
    use pcs::whir::{LOG_INV_RATE_0, config_for_rate};

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
    let (prover_data, ood) = commit_stack(&mut ps, shape, &committed, LOG_INV_RATE_0);
    let output = crate::OutputClaim::of_inputs(shape, &inputs, batch_instance(&mut ps, shape));
    ps.add_scalars(&output.lanes);
    let openings = witness.prove(&mut ps, &folded, &output);
    open_commitment(&mut ps, shape, committed, prover_data, &config, openings, ood);
    verify(shape, &ps.into_proof()).expect_err("a spare slot that was not committed is rejected");
}

/// The OOD sample's value is a claim the opening discharges: a prover that sends a wrong one is rejected there.
#[test]
fn a_wrong_ood_value_fails_the_opening() {
    use pcs::stack_open::StackClaim;
    use pcs::whir::{INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, commit, config_for_rate};
    use pcs::whir_config::OOD_GRINDING_BITS;

    let mut rng = Rng::new(83);
    let (n, depth) = (600, 12);
    let inputs: Vec<[u64; LANES]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    let shape = Shape::new(n, depth);
    let mut committed = vec![primitives::field::F64(0); 1 << shape.stack_log()];
    let witness = Witness::generate(shape, &inputs, &mut committed);

    let config = config_for_rate(shape.stack_log(), LOG_INV_RATE_0).expect("WHIR configuration");
    let mut ps = batch_transcript(LABEL, shape, LOG_INV_RATE_0);
    let (commitment, prover_data) = commit(&committed, shape.stack_log(), INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
    ps.add_root(&commitment.root);
    ps.grind(OOD_GRINDING_BITS);
    let low_point = ps.sample_vec(shape.stack_log());
    let value = primitives::multilinear::mle_eval(&committed, &low_point) + F128::ONE;
    ps.add_scalar(value);
    let ood = StackClaim::Point {
        offset: 0,
        low_point,
        value,
    };
    let output = crate::OutputClaim::of_inputs(shape, &inputs, batch_instance(&mut ps, shape));
    ps.add_scalars(&output.lanes);
    let openings = witness.prove(&mut ps, &committed, &output);
    open_commitment(&mut ps, shape, committed, prover_data, &config, openings, ood);
    assert_eq!(verify(shape, &ps.into_proof()), Err(VerifierError::WhirTerminal));
}

#[test]
fn proof_verifies_against_the_commitment() {
    end_to_end(600, 8);
    end_to_end(2048, 24);
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
        unsafe { block(shape.depth(), inputs, Some(extent.slot(g)), |_, _, _| {}) };
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
            let output = crate::OutputClaim::of_inputs(shape, &inputs, batch_instance(&mut ps, shape));
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
    let accepts = |committed: &[primitives::field::F64], lane_error: F128| {
        verify(shape, &prove(shape, &inputs, committed, lane_error)).is_ok()
    };
    assert!(accepts(&committed, F128::ZERO), "the honest column");
    // A lane of the input and of each state between.
    for slot in [3, 30, 60, 80, 99] {
        let mut bad = committed.clone();
        bad[slot * shape.n() + 17].0 ^= 1 << 40;
        assert!(!accepts(&bad, F128::ZERO), "slot {slot}");
    }
    assert!(!accepts(&committed, F128::ONE), "the output");
}

/// An extent whose size would wrap is refused, not allocated short.
#[test]
#[should_panic(expected = "fit in memory")]
fn an_extent_too_large_to_address_is_refused() {
    Extent::new(0, 1 << 55);
}
