//! A GKR proof of batched Keccak-f\[1600\], one layer per round: `doc/leanvm` Annex C, checked by
//! `crates/verifier`'s `keccak.rs`.
//!
//! Credit: Hashcaster 2 (<https://github.com/levs57/hashcaster2>)
//!
//! The prover commits a state every `depth` rounds, as lanes: the input of each of the `24 / depth` segments, for
//! every instance of the batch. The last segment's output is not committed: the caller holds a claim on it
//! ([`OutputClaim`]), in the VM the memory bus's claim on the `KECCAK` table's output lanes. A random combination of
//! the segments' outputs goes through `depth` layers, one per round, to a claim on their committed inputs, and both
//! end as openings of the commitment ([`Openings`]): the protocol of Annex C (`keccak:statement`,
//! `keccak:segments`), whose soundness is `keccak:soundness`.
//!
//! # Prover
//!
//! The witness holds every round's state before `chi`, sliced by bit position: a word is one position of 64
//! instances, a block one of 512 ([`witness`]). A layer (`layer.rs`, whose steps the items name) walks it three
//! times:
//!
//! - `product.rs`, step 1: each product meets its position's weight bit by bit, as byte maps of the weights;
//! - `skip.rs`, the first four rounds of step 3, over the sixteen packs of half a block: the summand at every point
//!   of `{0, 1, infinity}^4` they read, where a product of two packs and its weight as a polynomial in `s` are
//!   carry-less products;
//! - `table.rs`, the rest of step 3: one field element per half block and position, the packs folded at those four
//!   rounds' challenges, a table each round folds in half.
//!
//! Step 4 runs on tables of the 1600 positions. The blocks past the last input all equal the padding block, which
//! every pass walks once, at their summed weight.

use keccak::{LANE_VARS, LANES};
use primitives::field::{F64, F128, F128Unreduced};
use primitives::multilinear::eq_table;
use primitives::transcript::ProverState;
use protocol::first_claim;

#[cfg(feature = "bench")]
pub mod batch_bench;
mod keccak;
mod kernels;
mod layer;
mod open;
mod product;
mod protocol;
mod skip;
mod table;
pub mod witness;

#[cfg(test)]
mod tests;

pub use keccak::iota_bit;
pub use open::Openings;
pub use witness::{Shape, Witness};

/// A claim on the permutation's output, from outside the reduction: `lanes[l]` is lane `l` of the output state, as
/// words over the instances, evaluated at `instance` (an instance index's low four variables first). Both must be
/// bound to the transcript before [`Witness::prove`] runs, the point being a challenge drawn after the commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutputClaim {
    pub instance: Vec<F128>,
    pub lanes: [F128; LANES],
}

impl OutputClaim {
    /// The true claim at `instance` on the batch of `inputs`, padded with all-zero inputs, by running the
    /// permutation: what a caller without a claim of its own (a test, a benchmark) binds and passes.
    pub fn of_inputs(shape: Shape, inputs: &[[u64; LANES]], instance: Vec<F128>) -> Self {
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
        Self {
            instance,
            lanes: lanes.map(F128Unreduced::reduce),
        }
    }
}

impl Witness {
    /// Reduce "the committed states follow Keccak-f, to an output satisfying `output`" to openings of the
    /// commitment, as `crates/verifier`'s `verify_keccak` reads it. `committed` is the whole committed block, its
    /// state slots the ones this witness was built from or wrote: the openings are claims on all of it, so they fold
    /// whatever rides the spare slots (`lean_vm_core::cpu::keccak_value`).
    pub fn prove(&self, ps: &mut ProverState, committed: &[F64], output: &OutputClaim) -> Openings {
        let shape = self.shape;
        assert_eq!(output.instance.len(), shape.n_log);
        assert_eq!(
            committed.len(),
            1 << shape.stack_log(),
            "the openings are claims on the whole committed block"
        );
        // One message, the segment then the lane: the first claim is multilinear in them.
        ps.grind(fiat_shamir::grinding_bits((shape.seg_log() + LANE_VARS) as u128));
        let segment = ps.sample_vec(shape.seg_log());
        let r_lane = ps.sample_vec(LANE_VARS);
        let first = first_claim(&output.instance, &segment, &r_lane);
        // The last segment's output is the caller's, and the prover sends the committed ones' part.
        let (words, committed_value) =
            tracing::info_span!("Outputs").in_scope(|| open::output_words(shape, committed, &output.instance, &first));
        if shape.segments() > 1 {
            ps.add_scalar(committed_value);
        }

        let mut tables = table::Tables::new(shape);
        let mut claim = first.clone();
        for step in 0..shape.depth {
            claim =
                tracing::info_span!("Layer", step).in_scope(|| layer::prove_layer(ps, self, step, &claim, &mut tables));
        }
        drop(tables);

        let _span = tracing::info_span!("Openings").entered();
        let outputs = (shape.segments() > 1).then(|| open::open_outputs(ps, shape, &output.instance, &first, words));
        let inputs = open::open_inputs(ps, shape, committed, &claim);
        Openings { outputs, inputs }
    }
}
