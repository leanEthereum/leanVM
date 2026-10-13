//! A GKR proof of batched Keccak-f\[1600\], one layer per round.
//!
//! # Statement
//!
//! The prover commits a state every `depth` rounds, as lanes: `24 / depth` segments, each a
//! committed input and a committed output `depth` rounds later, for every instance of the batch.
//! Nothing between two committed states is committed. The proof is that every segment of every
//! instance follows the permutation.
//!
//! # Claims
//!
//! A claim ([`protocol::Claim`]) is a weighted sum of the bits of one state per segment. An
//! instance index splits into a pack (its high bits) and one of the pack's sixteen instances,
//! and the weight of a bit is a product of four: `eq` of a point at the pack and segment, a
//! weight per bit position, and a weight per instance of the pack.
//!
//! The verifier opens with a random such claim on the committed outputs: a random combination of
//! their lanes as words, bit `z` of a lane weighing `x^z`, at a random instance and segment.
//! Those weights are a basis of the word field over the bits, so the combination vanishes on no
//! nonzero difference of two bit tables. `depth` layers turn the claim into one on the committed
//! inputs, and both end as openings of the commitment ([`open`]): the first as the committed
//! words at one point, the last as their 64 bit slices at another. The outputs are committed
//! before the first claim is drawn, so a batch that breaks the permutation anywhere makes the
//! first claim false of what the inputs imply, except with the probability a nonzero
//! multilinear vanishes at a random point.
//!
//! # A layer
//!
//! A round is `chi` after a linear map. On the state `u` the linear map produces, `chi` sets
//! position `j` to `u[j] + (1 + u[j + 1]) * u[j + 2]`, with `j + k` the position `k` columns
//! along. A claim on a round's output becomes one on its input in six steps
//! ([`protocol::verify_layer`]):
//!
//! 1. **Product polynomial.** Sixteen bits embed in a binary polynomial of degree at most 23, in
//!    such a way that a fixed linear map sends a product of two embeddings to the embedding of
//!    the bitwise AND ([`rmfe`]). Embedding every pack of `u`, `chi` becomes one polynomial
//!    product per pack and position. The prover sends the claim's weighted sum of those
//!    products, a polynomial `U` of 47 coefficients, and the verifier checks that the linear map
//!    takes it to the claimed value.
//! 2. **Evaluation.** The verifier draws `s`. A wrong `U` differs from the true one at `s`, and
//!    at `s` a pack is a single field element, so `U(s)` is a sum over packs and positions of
//!    products of two field elements: a sumcheck claim.
//! 3. **Packs.** A sumcheck binds the pack and the segment.
//! 4. **Positions.** A second sumcheck binds the position, the claim's position weights being
//!    one more multilinear factor of its summand. It leaves `u` at the positions `0`, `1` and `2`
//!    columns along from one point, and the weights at that point, which the verifier computes.
//! 5. **Batching.** A random combination makes the three one claim on `u`, at the instance
//!    weights `s` gives: the value at `s` of each instance's embedding.
//! 6. **Linear map.** The claim on `u` is the claim on the round's input under the transposed
//!    map, with no interaction.
//!
//! The position weights of every claim after the first are therefore the transposed linear map
//! applied to a combination of three shifted `eq` tables of one point. A verifier that cannot
//! afford 1600 weights a layer evaluates them from the two points alone, as the recursion guest
//! does: `eq` factors into a lane table and a slice table, the map moves lanes and rotates
//! slices, and a rotation of one `eq` table against another is a carry chain over six bits.
//!
//! `iota` flips known positions, which shifts a claim by a constant the verifier adds.
//!
//! # Soundness
//!
//! Every step loses at most a polynomial's degree over the field size: 46 for step 2, three per
//! round of steps 3 and 4, two for step 5. The openings add two per round. With `n` instances
//! and `depth` layers that is below `(depth + 1) * (130 + 3 log n)` over `2^192`, next to the
//! commitment scheme's own error.
//!
//! # Prover
//!
//! The witness holds every round's `u` sliced by bit position, 64 instances to a word
//! ([`witness`]). A layer walks it three times ([`prover`]): once for `U`, once for the first
//! four rounds of step 3, which are sums of products of bit-level combinations of packs, and
//! once to fold those four rounds' challenges into field elements. Everything after `s` is
//! arithmetic in the power basis of `s`, where a pack's value is its embedding's bits and a
//! weighted sum is a carry-less product ([`basis`], [`power`]).

use fiat_shamir::transcript::{Receiver, Transmitter};

pub mod basis;
pub mod keccak;
pub mod kernels;
pub mod open;
pub mod power;
pub mod protocol;
pub mod prover;
pub mod rmfe;
pub mod witness;

#[cfg(test)]
mod tests;

pub use open::{Opening, Openings, WordOpening};
pub use protocol::VerifyError;
pub use witness::{Shape, Witness};

use keccak::LANE_VARS;
use primitives::field::F192;
use protocol::{first_claim, verify_layer};

/// Reduce "the committed states follow Keccak-f" to two openings of the commitment.
/// `committed` is what [`Witness::generate`] wrote.
pub fn prove(ps: &mut impl Transmitter, witness: &Witness, committed: &[primitives::field::F64]) -> Openings {
    let shape = witness.shape;
    let (r_low, point, r_lane) = (
        ps.sample_vec(4),
        ps.sample_vec(shape.y_vars()),
        ps.sample_vec(LANE_VARS),
    );
    let instance = [&r_low[..], &point[..shape.pack_vars()]].concat();
    let mut first = first_claim(shape, F192::ZERO, &r_low, point, &r_lane);
    let (folded, value) =
        tracing::info_span!("Outputs").in_scope(|| open::output_claim(shape, committed, &instance, &first));
    first.value = value;
    ps.add_scalar(value);

    let mut claim = first.clone();
    let mut scratch = prover::Scratch::new(shape);
    for step in 0..shape.depth {
        claim = tracing::info_span!("Layer", step)
            .in_scope(|| prover::prove_layer(ps, witness, &mut scratch, step, &claim));
    }
    let _span = tracing::info_span!("Openings").entered();
    let outputs = open::open_outputs(ps, shape, &instance, &first, folded);
    let inputs = open::open_inputs(ps, witness, &claim);
    Openings { outputs, inputs }
}

/// Mirror of [`prove`]. The caller checks the two openings against the commitment.
pub fn verify(vs: &mut impl Receiver, shape: Shape) -> Result<Openings, VerifyError> {
    let (r_low, point, r_lane) = (
        vs.sample_vec(4),
        vs.sample_vec(shape.y_vars()),
        vs.sample_vec(LANE_VARS),
    );
    let instance = [&r_low[..], &point[..shape.pack_vars()]].concat();
    let value = vs.next_scalar()?;
    let first = first_claim(shape, value, &r_low, point, &r_lane);
    let mut claim = first.clone();
    for step in 0..shape.depth {
        claim = verify_layer(vs, shape, step, &claim)?;
    }
    let outputs = open::verify_outputs(vs, shape, &instance, &first)?;
    let inputs = open::verify_inputs(vs, shape, &claim)?;
    Ok(Openings { outputs, inputs })
}

/// The words of a stack holding the committed states alone.
pub fn committed_len(shape: Shape) -> usize {
    1 << shape.stack_log()
}

/// Discharge the two openings against the commitment to `stack`, which holds the committed
/// states alone.
pub fn open_commitment(
    ps: &mut impl Transmitter,
    shape: Shape,
    stack: &[primitives::field::F64],
    prover_data: &pcs::whir::ProverData,
    config: &pcs::whir::ProverConfig,
    openings: Openings,
) {
    let ring = pcs::stack_open::RingSwitchOpen {
        offset: 0,
        qflock_vars: shape.stack_log(),
        claims: vec![pcs::stack_open::RingSwitchClaim {
            suffix_point: openings.inputs.point,
            s_hat_v: Some(openings.inputs.slices),
        }],
    };
    let points = [word_claim(openings.outputs)];
    pcs::stack_open::open_batch_mixed_whir_stacked(ps, shape.stack_log(), stack, prover_data, config, &points, &ring);
}

fn word_claim(opening: WordOpening) -> pcs::stack_open::StackClaim {
    pcs::stack_open::StackClaim::Point {
        offset: 0,
        low_point: opening.point,
        value: opening.value,
    }
}

/// Mirror of [`open_commitment`].
pub fn verify_commitment(
    vs: &mut impl Receiver,
    shape: Shape,
    config: &pcs::whir::VerifierConfig,
    root: &pcs::merkle::Hash,
    openings: &Openings,
) -> Result<(), pcs::whir::VerifyError> {
    let ring = pcs::stack_open::RingSwitchVerify {
        offset: 0,
        qflock_vars: shape.stack_log(),
        claims: vec![pcs::stack_open::RingSwitchVerifyClaim {
            suffix_point: &openings.inputs.point,
            s_hat_v: openings.inputs.slices.as_slice().try_into().expect("64 slices"),
        }],
    };
    pcs::stack_open::verify_opening_batch_mixed_whir_stacked(
        vs,
        config,
        shape.stack_log(),
        1 << pcs::whir::INITIAL_FOLDING_FACTOR,
        root,
        &[word_claim(openings.outputs.clone())],
        &ring,
    )
}
