//! A GKR proof of batched Keccak-f\[1600\], one layer per round.
//!
//! Credit: Hashcaster 2 (<https://github.com/levs57/hashcaster2>)
//!
//! # Statement
//!
//! The prover commits a state every `depth` rounds, as lanes: the input of each of the
//! `24 / depth` segments, for every instance of the batch. A segment's output is the next
//! segment's committed input, except the last segment's, which is the permutation's output and is
//! not committed: the caller holds a claim on it ([`OutputClaim`]), in the VM the memory bus's
//! claim on the `KECCAK` table's output lanes. Nothing between two committed states is committed.
//! The proof is that every segment of every instance follows the permutation, the last one ending
//! where the caller's claim says.
//!
//! # Claims
//!
//! A claim (`protocol::Claim`) is a weighted sum of the bits of one state per segment. An
//! instance index splits into a pack (its high bits) and one of the pack's sixteen instances,
//! and the weight of a bit is a product of four: `eq` of a point at the pack and segment, a
//! weight per bit position, and a weight per instance of the pack.
//!
//! The first claim is on every segment's output at the caller's instance point: a random
//! combination of their lanes as words, bit `z` of a lane weighing `x^z`, at a random segment.
//! Those weights are a basis of the word field over the bits, so the combination vanishes on no
//! nonzero difference of two bit tables. Its value is the committed outputs' part, which the
//! prover sends, plus the last segment's, which the caller's lane values give. `depth` layers turn
//! the claim into one on the committed inputs, and both end as openings of the commitment
//! (`open`): the committed outputs as words at one point, the inputs as their 64 bit slices at
//! another. The caller's instance point is a challenge drawn after the commitment, and the
//! claim's segment and lane challenges after the caller's lane values are bound, so a batch that breaks the permutation anywhere makes the first claim
//! false of what the inputs imply, except with the probability a nonzero multilinear vanishes at
//! a random point.
//!
//! # A layer
//!
//! A round is `chi` after a linear map. On the state `u` the linear map produces, `chi` sets
//! position `j` to `u[j] + (1 + u[j + 1]) * u[j + 2]`, with `j + k` the position `k` columns
//! along. A claim on a round's output becomes one on its input in six steps (the
//! verifier's are `crates/verifier`'s `keccak.rs`, the prover's `prover::prove_layer`):
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
//! round of steps 3 and 4, two for step 5. The first claim's challenges add one per variable, the
//! openings two per round. With `n` instances, `S` segment variables and `L` slot variables,
//! that is at most `depth (69 + 3 S + 3 log n) + log n + S + 4 L + 13` over `2^192`, next to the
//! commitment scheme's own error. At the VM's depth of 12 it is the `(37 log n + 902) / 2^192`
//! derived in `doc/leanvm` Annex C (`keccak:soundness`).
//!
//! # Prover
//!
//! The witness holds every round's `u` sliced by bit position, 64 instances to a word
//! ([`witness`]). A layer walks it three times (`prover`): once for `U`, once for the first
//! four rounds of step 3, which are sums of products of bit-level combinations of packs, and
//! once to fold those four rounds' challenges into field elements. Everything after `s` is
//! arithmetic in the power basis of `s`, where a pack's value is its embedding's bits and a
//! weighted sum is a carry-less product (`basis`, `power`).

use fiat_shamir::transcript::ProverState;
use keccak::LANE_VARS;
use primitives::field::{F64, F192, F192Unreduced};
use primitives::multilinear::eq_table;
use protocol::{Claim, dot, first_claim};

mod basis;
#[cfg(feature = "bench")]
pub mod batch_bench;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq"))]
mod clmul;
mod keccak;
pub mod kernels;
mod open;
mod power;
mod protocol;
mod prover;
pub mod rmfe;
pub mod witness;

#[cfg(test)]
mod tests;

pub use keccak::iota_bit;
pub use open::{Opening, Openings, WordOpening};
pub use witness::{Shape, Witness};

/// A claim on the permutation's output, from outside the reduction: `lanes[l]` is lane `l` of
/// the output state, as words over the instances, evaluated at `instance` (an instance index's
/// low four variables first). Both must be bound to the transcript before [`Witness::prove`]
/// runs, the point being a challenge drawn after the commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutputClaim {
    pub instance: Vec<F192>,
    pub lanes: [F192; keccak::LANES],
}

impl OutputClaim {
    /// The true claim at `instance` on the batch of `inputs`, padded with all-zero inputs, by
    /// running the permutation: what a caller without a claim of its own (a test, a benchmark)
    /// binds and passes.
    pub fn of_inputs(shape: Shape, inputs: &[[u64; keccak::LANES]], instance: Vec<F192>) -> Self {
        let permute = |mut state: [u64; keccak::LANES]| {
            primitives::hash::keccak_f(&mut state);
            state
        };
        let padding = permute([0; keccak::LANES]);
        let eq = eq_table(&instance);
        let lanes = parallel::fold_reduce(
            shape.n(),
            || [F192Unreduced::ZERO; keccak::LANES],
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
        Self {
            instance,
            lanes: lanes.map(F192Unreduced::reduce),
        }
    }
}

/// The first claim, valued at the last segment's part only: the caller's lanes, at the claim's
/// segment and lane weights.
fn first(shape: Shape, output: &OutputClaim, segment: Vec<F192>, r_lane: &[F192]) -> Claim {
    assert_eq!(output.instance.len(), shape.n_log);
    let point = [&output.instance[4..], &segment[..]].concat();
    let mut claim = first_claim(shape, &output.instance[..4], point, r_lane);
    let last = eq_table(&segment)[shape.segments() - 1];
    claim.value = last * dot(&eq_table(r_lane)[..keccak::LANES], &output.lanes);
    claim
}

impl Witness {
    /// Reduce "the committed states follow Keccak-f, to an output satisfying `output`" to
    /// openings of the commitment. `committed` is the WHOLE committed block, spare slots and
    /// all, not just the states [`Witness::generate`] wrote: the openings it leaves are claims
    /// on all of it, so they fold whatever rides those slots (§cpu).
    pub fn prove(&self, ps: &mut ProverState, committed: &[F64], output: &OutputClaim) -> Openings {
        let shape = self.shape;
        assert_eq!(
            committed.len(),
            1 << shape.stack_log(),
            "the openings are claims on the whole committed block"
        );
        let (segment, r_lane) = (ps.sample_vec(shape.seg_log()), ps.sample_vec(LANE_VARS));
        let mut first = first(shape, output, segment, &r_lane);
        let instance = &output.instance;
        let (folded, committed_value) =
            tracing::info_span!("Outputs").in_scope(|| open::output_claim(shape, committed, instance, &first));
        if shape.segments() > 1 {
            ps.add_scalar(committed_value);
        }
        first.value += committed_value;

        let mut claim = first.clone();
        let mut scratch = prover::Scratch::new(shape);
        for step in 0..shape.depth {
            claim = tracing::info_span!("Layer", step)
                .in_scope(|| prover::prove_layer(ps, self, &mut scratch, step, &claim));
        }
        let _span = tracing::info_span!("Openings").entered();
        let outputs =
            (shape.segments() > 1).then(|| open::open_outputs(ps, shape, instance, &first, committed_value, folded));
        let inputs = open::open_inputs(ps, self, committed, &claim);
        Openings { outputs, inputs }
    }
}
