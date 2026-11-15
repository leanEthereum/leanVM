//! The witness commitment (§sec:stacking, §annex:pcs): the stacked `K`-valued witness, committed by WHIR and
//! opened over `E`. One opening discharges every claim of the proof: the claims `q̂(point_j) = value_j`, folded by
//! random `γ`s into one weight the verifier evaluates itself, and the Keccak reduction's ring-switched claim
//! ([`::pcs::stack_open`]).
//!
//! The stack is `2^μ` words, but past the placed columns it is zero, and lane `l` of the level-0 interleaving is the
//! contiguous block `q[l·2^(μ-LOG_BATCH)..]`: only [`crate::witness::StackShape::n_lanes`] lanes are encoded, and the
//! absent ones lead every leaf image, one sponge state every leaf shares.
//!
//! Every supported rate uses Johnson list decoding with OOD binding ([`::pcs::whir::SECURITY_BITS`]). Level 0 takes
//! its OOD sample right after its root ([`::pcs::ood`]), each deeper commitment one inside the opening.

use primitives::field::F64;
use primitives::transcript::ProverState;

use ::pcs::ood::ood_sample;
use ::pcs::stack_open::open_batch_mixed_whir_stacked;
pub use ::pcs::stack_open::{RingSwitchOpen, StackClaim as SlotClaim};
use ::pcs::whir::{ProverData, commit as whir_commit, config_for_rate};

/// `log2` of the lanes a Merkle leaf holds, which is also WHIR's initial folding factor: the level-0 commitment is
/// reused by the opening, so the two are one knob.
pub(crate) const LOG_BATCH: usize = ::pcs::whir::INITIAL_FOLDING_FACTOR;
/// The rate the test suite and the benchmarks prove at. Not a default: every entry point takes `log_inv_rate`.
pub const TEST_LOG_INV_RATE: usize = ::pcs::whir::LOG_INV_RATE_0;
/// The `log_inv_rate` values a WHIR configuration can be derived for.
pub use ::pcs::whir::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};
/// The committed stack's log-size bounds, the protocol's.
pub use verifier::{MAX_STACKED_LOG, MIN_STACKED_LOG};

/// A committed witness and what opening it needs. The witness itself stays the caller's, who hands it back to
/// [`open`].
pub struct Committed {
    /// The codeword and Merkle tree.
    prover_data: ProverData,
    /// `log2` of the stack, in words.
    mu: usize,
    log_inv_rate: usize,
    /// The OOD sample's claim ([`::pcs::ood`]), which the opening discharges after the caller's.
    ood: SlotClaim,
}

/// Commit the stack's committed lanes `witness` (its zero tail past them is neither encoded nor hashed, and the
/// commitment is the full stack's), bind the root, and take the OOD sample.
pub fn commit(
    ps: &mut ProverState,
    witness: &[F64],
    shape: crate::witness::StackShape,
    log_inv_rate: usize,
) -> Committed {
    let mu = shape.mu;
    assert!(mu >= MIN_STACKED_LOG, "a stack is at least 2^{MIN_STACKED_LOG} words");
    assert_eq!(
        witness.len(),
        shape.committed_len(),
        "the witness is the committed lanes"
    );
    let (commitment, prover_data) = whir_commit(witness, mu, LOG_BATCH, log_inv_rate);
    ps.add_root(&commitment.root);
    let ood = ood_sample(ps, witness, mu);
    Committed {
        prover_data,
        mu,
        log_inv_rate,
        ood,
    }
}

/// Open the committed witness `q` on the point claims `points`, then the OOD sample's, and on the Keccak reduction's
/// ring-switched claim `ring`, in one stacked WHIR. Nothing is bound here but the opening's own messages: every
/// claim's value rode the stream or follows from the statement and earlier challenges. The opening frees the
/// codeword and the tree once the level-0 queries are answered.
pub fn open(ps: &mut ProverState, c: Committed, q: Vec<F64>, points: &[SlotClaim], ring: &RingSwitchOpen) {
    assert_eq!(
        q.len() % (1 << (c.mu - LOG_BATCH)),
        0,
        "the witness is whole committed lanes"
    );
    assert!(q.len() <= 1 << c.mu, "the witness fits the announced size");
    let cfg = config_for_rate(c.mu, c.log_inv_rate)
        .unwrap_or_else(|e| panic!("whir config for mu={}, log_inv_rate={}: {e}", c.mu, c.log_inv_rate));
    let points = [points, &[c.ood]].concat();
    open_batch_mixed_whir_stacked(ps, c.mu, q, c.prover_data, &cfg, &points, ring)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What lets all three verifiers check a plain range instead of re-deriving the ladder: every size in the window
    /// is configurable at every rate.
    #[test]
    fn supported_window_is_configurable() {
        for rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
            for mu in MIN_STACKED_LOG..=MAX_STACKED_LOG {
                assert!(config_for_rate(mu, rate).is_ok(), "mu={mu} rate={rate}");
            }
        }
    }
}
