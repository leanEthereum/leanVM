//! Picking the prover a case proves on: the campaign exercises both trees.

use crate::Source;
pub use exp_leanvm_core::ExperimentalProver;
pub use leanvm_core::StableProver;

/// The compat aggregate on the prover `src` picks: `false` stable, `true` experimental.
pub fn aggregate_pick(
    experimental: bool,
    children: &[rec_aggregation::fuzzing::EthereumProof],
    raw_lean_xmss: Vec<(lean_xmss::LeanXmssPublicKey, lean_xmss::Message, lean_xmss::LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(
        lean_sphincs::LeanSphincsPublicKey,
        lean_sphincs::Message,
        lean_sphincs::LeanSphincsSignature,
    )>,
    blobs: &[u64],
    declare: Option<&rec_aggregation::fuzzing::EthereumClaims>,
    log_inv_rate: usize,
) -> Result<rec_aggregation::fuzzing::EthereumProof, rec_aggregation::fuzzing::AggregationError> {
    if experimental {
        rec_aggregation::fuzzing::aggregate_compat::<ExperimentalProver>(
            children,
            raw_lean_xmss,
            raw_lean_sphincs,
            blobs,
            declare,
            log_inv_rate,
        )
    } else {
        rec_aggregation::fuzzing::aggregate_compat::<StableProver>(
            children,
            raw_lean_xmss,
            raw_lean_sphincs,
            blobs,
            declare,
            log_inv_rate,
        )
    }
}

/// The prover this case proves on, as `src` picks it.
pub fn prover(src: &mut Source) -> bool {
    src.prover()
}
