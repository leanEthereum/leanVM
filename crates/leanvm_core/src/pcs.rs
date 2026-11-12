//! Witness commitment: an inner-product PCS committing over `K = F_{2^64}` and
//! opening over `E = F_{2^128}` (doc §sec:stacking, §annex:pcs), through **WHIR**. An
//! opening proves `Σ_x q(x)·W(x) = C` against any verifier-evaluable `E`-valued
//! weight `W` (a point evaluation `q̂(r)` is `W = eq(r,·)`). A batch of claims
//! `q̂(point_j) = value_j` folds with random `γ`s into one weight and target,
//! opened in a single WHIR run: the verifier evaluates the weight itself,
//! so it never travels. The Keccak reduction's ring-switched `q_keccak` claim joins the same batch
//! ([`::pcs::stack_open`]).
//!
//! The stacked witness is `2^μ` words, but its tail past the placed columns is
//! zero, and the L0 interleaving makes that tail whole lanes: lane `l` is the
//! contiguous block `q[l·2^(μ-LOG_BATCH) ..)`, so only
//! [`crate::witness::StackShape::n_lanes`] of them are ever encoded, and the
//! opening's dense weight, its first `LOG_BATCH` rounds and the stack allocation
//! shrink with them. A leaf image is still `2^LOG_BATCH` words, the absent lanes
//! contributing the zeros their codeword would have been, but they LEAD the image:
//! their whole 136-byte blocks are one sponge state every leaf shares, so the
//! committer absorbs them once rather than once per leaf, and at most the image's tail
//! rides the proof.
//!
//! Security: every supported rate ([`MIN_LOG_INV_RATE`]..=[`MAX_LOG_INV_RATE`]) uses
//! Johnson list decoding with OOD binding and round-by-round soundness
//! ([`::pcs::whir::SECURITY_BITS`]). L0 takes its OOD sample right after its root
//! ([`::pcs::ood`]); each deeper commitment takes one inside the opening, after its own grind. The base-field
//! commitment only shrinks the level-0 symbols to 8 bytes; every random
//! ingredient is sampled from `E`.

use crate::transcript::ProverState;
use primitives::field::F64;

use ::pcs::ood::ood_sample;
use ::pcs::stack_open::open_batch_mixed_whir_stacked;
pub use ::pcs::stack_open::{RingSwitchClaim, RingSwitchOpen, StackClaim as SlotClaim};
use ::pcs::whir::ProverConfig;
use ::pcs::whir::{ProverData, commit as whir_commit, config_for_rate};

/// Row-batch lanes `2^LOG_BATCH`: the Merkle leaf width (`2^LOG_BATCH` F64
/// = 512 bytes/leaf) IS WHIR's INITIAL folding factor: the L0 commit is
/// reused, so the two are one knob ([`::pcs::whir::INITIAL_FOLDING_FACTOR`]).
/// Larger ⇒ far fewer Merkle nodes to hash at the cost of fatter query openings.
pub(crate) const LOG_BATCH: usize = ::pcs::whir::INITIAL_FOLDING_FACTOR;
/// The rate the test suite and the benchmarks prove at. Not a default: every
/// entry point takes `log_inv_rate` explicitly, and a caller has to choose.
pub const TEST_LOG_INV_RATE: usize = ::pcs::whir::LOG_INV_RATE_0;
/// The `log_inv_rate` values a WHIR configuration can be derived for.
pub use ::pcs::whir::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};
// The PCS and the bus argument both target `SECURITY_BITS`.
const _: () = assert!(::pcs::whir::SECURITY_BITS == crate::SECURITY_BITS as usize);
/// The committed stack's log-size bounds, the protocol's.
pub use verifier::{MAX_STACKED_LOG, MIN_STACKED_LOG};

/// The shared WHIR config for a `2^μ`-word witness, memoized per `(μ, log_inv_rate)`.
fn whir_config(mu: usize, log_inv_rate: usize) -> std::sync::Arc<ProverConfig> {
    use std::collections::HashMap;
    use std::sync::{Arc, Mutex, OnceLock};
    type Cache = Mutex<HashMap<(usize, usize), Arc<ProverConfig>>>;
    static CACHE: OnceLock<Cache> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut map = cache.lock().expect("whir config cache poisoned");
    Arc::clone(map.entry((mu, log_inv_rate)).or_insert_with(|| {
        assert!(
            mu >= MIN_STACKED_LOG,
            "witness must be ≥ 2^{MIN_STACKED_LOG} elements (padded by placements_of)"
        );
        let config = config_for_rate(mu, log_inv_rate)
            .unwrap_or_else(|e| panic!("whir config for mu={mu}, log_inv_rate={log_inv_rate}: {e}"));
        Arc::new(config)
    }))
}

/// A committed `K`-valued witness plus the data needed to open it. The witness
/// itself is not retained (the caller still owns it and passes it back to
/// [`open`]), so committing costs no extra full-trace copy.
pub struct Committed {
    /// Codeword + Merkle tree retained for opening. Public so the single stacked
    /// WHIR opening (which also discharges the Keccak reduction's claims on
    /// this same commitment, §keccak) can reuse it.
    pub prover_data: ProverData,
    /// `log2` of the witness length in F64 words.
    pub mu: usize,
    /// L0 inverse-rate logarithm bound into the transcript before this commitment.
    pub log_inv_rate: usize,
    /// The OOD sample's claim ([`::pcs::ood`]), which the opening discharges after the caller's.
    pub ood: SlotClaim,
}

/// Commit a `K`-valued witness of `2^μ` words (`μ ≥ MIN_STACKED_LOG`, from
/// [`crate::witness::placements_of`]), bind its root into the transcript
/// before any challenge is sampled, and take its OOD sample ([`::pcs::ood`]).
///
/// `witness` is the stack truncated to the lane blocks that carry data
/// ([`crate::witness::StackShape::committed_len`]); the zero tail past them is
/// neither encoded nor hashed, and the resulting commitment is the same one the
/// full `2^μ` witness would have produced.
pub fn commit(
    ps: &mut ProverState,
    witness: &[F64],
    shape: crate::witness::StackShape,
    log_inv_rate: usize,
) -> Committed {
    let mu = shape.mu;
    assert!(
        mu >= MIN_STACKED_LOG,
        "witness must be ≥ 2^{MIN_STACKED_LOG} elements (padded by placements_of)"
    );
    assert_eq!(
        witness.len(),
        shape.committed_len(),
        "witness must be the committed lanes"
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

// The batching challenges are just `sample()`d inside the stacked opener: every
// claim they combine is already bound: the values rode the stream
// (`add_scalar`) during the bus / constraint sub-protocols or, for the
// public-input claims, are functions of the seeded statement and a prior
// challenge, the points are prior challenges, and the offsets are public
// (reconstructed identically from the announced layout).

/// Open the committed witness: discharge the `points` (leanVM's bus / constraint /
/// public-input claims and the Keccak reduction's point claim, as block-sparse
/// slot evaluations) AND the reduction's ring-switched claim (`ring`) in ONE stacked WHIR.
/// The points become the opener's `point_claims`; the opening's Merkle data
/// rides the transcript's phase list, not the scalar stream. The commitment root
/// was already bound by [`commit`], and the point *values* either rode the
/// stream or derive from the statement and prior challenges, so nothing extra
/// is bound here.
///
/// There is no plain (non-ring-switch) path: the witness ALWAYS carries a `q_keccak`
/// sub-block (§cpu), so every opening is stacked.
///
/// The OOD sample's claim follows `points`. The opening consumes the commitment: it frees the codeword and tree once
/// the L0 queries are answered.
pub fn open(ps: &mut ProverState, c: Committed, q: Vec<F64>, points: &[SlotClaim], ring: &RingSwitchOpen) {
    let lane_block = 1usize << (c.mu - LOG_BATCH);
    assert_eq!(q.len() % lane_block, 0, "witness must be whole committed lanes");
    assert!(q.len() <= 1usize << c.mu, "witness must fit the announced size");
    let cfg = whir_config(c.mu, c.log_inv_rate);
    let points = [points, &[c.ood]].concat();
    open_batch_mixed_whir_stacked(ps, c.mu, q, c.prover_data, &cfg, &points, ring)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What lets all three verifiers check a plain range instead of re-deriving
    /// the ladder: every size in the window is configurable at every rate.
    #[test]
    fn supported_window_is_configurable() {
        for rate in ::pcs::whir::MIN_LOG_INV_RATE..=::pcs::whir::MAX_LOG_INV_RATE {
            for mu in MIN_STACKED_LOG..=MAX_STACKED_LOG {
                assert!(config_for_rate(mu, rate).is_ok(), "mu={mu} rate={rate}");
            }
        }
    }
}
