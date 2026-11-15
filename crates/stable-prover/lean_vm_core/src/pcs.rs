//! The witness commitment (§sec:stacking, §annex:pcs): the stacked `K`-valued witness, committed by WHIR and
//! opened over `E`. One opening discharges every claim of the proof: the claims `q̂(point_j) = value_j`, folded by
//! random `γ`s into one weight the verifier evaluates itself, and the Keccak reduction's ring-switched claim
//! ([`::pcs::open`]).
//!
//! The stack is `2^μ` words, but past the placed columns it is zero, and lane `l` of the level-0 interleaving is the
//! contiguous block `q[l·2^(μ-LOG_BATCH)..]`: only [`crate::witness::StackShape::n_lanes`] lanes are encoded, and the
//! absent ones lead every leaf image, one sponge state every leaf shares.
//!
//! Every supported rate uses Johnson list decoding with OOD binding ([`verifier::SECURITY_BITS`]). Level 0 takes
//! its OOD sample right after its root ([`::pcs::commit`]), each deeper commitment one inside the opening.

use ::pcs::Committed;
use primitives::field::F64;
use primitives::transcript::ProverState;

pub use ::pcs::{StackClaim as SlotClaim, open};

/// `log2` of the lanes a Merkle leaf holds, which is also WHIR's initial folding factor: the level-0 commitment is
/// reused by the opening, so the two are one knob.
pub(crate) const LOG_BATCH: usize = ::pcs::whir::INITIAL_FOLDING_FACTOR;
/// The rate the test suite and the benchmarks prove at. Not a default: every entry point takes `log_inv_rate`.
pub const TEST_LOG_INV_RATE: usize = 1;
/// The `log_inv_rate` values a WHIR configuration can be derived for.
pub use ::pcs::whir::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};
/// The committed stack's log-size bounds, the protocol's.
pub use verifier::{MAX_STACKED_LOG, MIN_STACKED_LOG};

/// Commit the stack's committed lanes `witness` (its zero tail past them is neither encoded nor hashed, and the
/// commitment is the full stack's), bind the root, and take the OOD sample. The witness itself stays the caller's,
/// who hands it back to [`open`].
pub fn commit(
    ps: &mut ProverState,
    witness: &[F64],
    shape: crate::witness::StackShape,
    log_inv_rate: usize,
) -> Committed {
    ::pcs::commit(ps, witness, shape.mu, log_inv_rate)
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
                assert!(verifier::derive_config(mu, rate).is_ok(), "mu={mu} rate={rate}");
            }
        }
    }
}
