// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Stacked batch-mixed opening for the F64-committed PCS.
//!
//! The committed witness is a stack of `2^log_n` [`F64`] words (committed via
//! [`super::whir::commit`], which only encodes and only transmits the lane blocks
//! that carry data: every claim lives inside them and the weight is zero past
//! them), and one WHIR run discharges
//!
//! - **point claims** ([`StackClaim`]): plain multilinear evaluations of
//!   aligned sub-slices of the stack (a `Point` claim's weight is
//!   `eq(low_point, .)` supported on `[offset, offset + 2^|low_point|)`; a
//!   `Strided` claim freezes the low `stride_log` in-block coords to `slot`'s
//!   bits, so its weight is nonzero only at `offset + slot + j * 2^stride_log`),
//! - **ring-switched claims** ([`RingSwitchOpen`]): bit-MLE evaluation claims
//!   on the packed sub-block `q_keccak = stack[offset .. offset + 2^qkeccak_vars]`,
//!   reduced per claim by [`super::ring_switch::prove_prepare`] and the
//!   deferred finish path to an inner-product
//!   claim `<q_keccak, rs_eq_ind> = sumcheck_claim` against the transparent
//!   E-valued weight `rs_eq_ind`.
//!
//! All claims are lambda-folded into ONE combined weight `b_stack` over the
//! whole stack plus one `target`, then proved by
//! [`super::whir::recursive_prover_with_basis`]. A verifier recomputes the
//! target from the claims and evaluates `MLE(b_stack)` once, at the final fold
//! point, from the closed form under "The combined weight".
//!
//! ## Transcript order
//!
//! Sample the shared linear map, then one batching challenge for both claim families, then run WHIR. The caller already bound each claim's slices and value through the transcript, so none is observed again here.
//!
//! ## The combined weight
//!
//! With `sel = offset >> qkeccak_vars` the selector coords of the q_keccak slice,
//! the lifted weight at a full-stack point `x = (x_lo, x_hi)` (split at
//! `qkeccak_vars`, LSB-first) is
//!
//! ```text
//! b(x) = eq(sel, x_hi) * sum_i lambda^i * MLE(rs_eq_ind_i)(x_lo)
//!      + sum_j lambda^(n_rs + j) * eq(claim_j, x)
//! ```
//!
//! which is exactly what the dense `b_stack` scatter produces (each claim's
//! weight lives on its aligned slice, so scattering the low-dimensional eq /
//! rs_eq_ind tensor at the slice offset IS multiplying by the boolean
//! selector eq).
//!
//! Both families take DISJOINT power ranges of ONE challenge, as the table
//! sumcheck's xi ranges do, so every claim carries a distinct power (the
//! batching step of `thm:rbr`).

use fiat_shamir::transcript::ProverState;
use primitives::field::{F64, F192, powers};

use super::ring_switch;
use super::whir::{ProverConfig, ProverData};

mod basis;

// ---------------------------------------------------------------------------
// Claim types
// ---------------------------------------------------------------------------

/// An owning point claim folded into the stacked mixed opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackClaim {
    /// `eq(low_point, .)` on the aligned slice
    /// `[offset, offset + 2^|low_point|)`; `offset` must be a multiple of
    /// `2^|low_point|`.
    Point {
        offset: usize,
        low_point: Vec<F192>,
        value: F192,
    },
    /// A boolean-selector claim on a packed column: the low `stride_log`
    /// in-block coords are frozen to `slot`'s bits (so the weight is nonzero
    /// only at `offset + slot + j * 2^stride_log`) and `point` is the high
    /// part. Equivalent to a `Point` with `low_point = slot_bits ++ point`,
    /// folded in `O(2^|point|)` instead of `O(2^(stride_log + |point|))`.
    /// `offset` must be a multiple of `2^(stride_log + |point|)` and
    /// `slot < 2^stride_log`.
    Strided {
        offset: usize,
        slot: usize,
        stride_log: usize,
        point: Vec<F192>,
        value: F192,
    },
}

impl StackClaim {
    #[inline]
    pub fn value(&self) -> F192 {
        match self {
            StackClaim::Point { value, .. } | StackClaim::Strided { value, .. } => *value,
        }
    }
}

/// One ring-switched claim on the q_keccak sub-block: the 64 bit-slice MLEs of
/// q_keccak at `suffix_point` (see [`super::ring_switch`]), which has
/// `qkeccak_vars` coords.
///
/// `s_hat_v` holds those 64 values. The caller transmits and checks them itself
/// (the Keccak reduction sends them and checks them against its last claim), so this
/// layer only binds them to the commitment. `None` asks the prover to fold the slices from the witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchClaim {
    pub suffix_point: Vec<F192>,
    pub s_hat_v: Option<Vec<F192>>,
}

/// Prover-side bundle of the ring-switched claims discharged in the same
/// stacked opening as the [`StackClaim`]s. Each claim may carry its
/// precomputed `s_hat_v`.
#[derive(Clone, Debug)]
pub struct RingSwitchOpen {
    /// q_keccak's offset inside the committed stack; must be a multiple of
    /// `2^qkeccak_vars` (an aligned slice).
    pub offset: usize,
    /// log2 of q_keccak's length in F64 words; the opener slices
    /// `q_keccak = stack[offset .. offset + 2^qkeccak_vars]` (no separate copy).
    pub qkeccak_vars: usize,
    pub claims: Vec<RingSwitchClaim>,
}

// ---------------------------------------------------------------------------
// Claim support
// ---------------------------------------------------------------------------

/// The b_stack range a claim's weight is supported on. Every range is an
/// aligned dyadic interval (the offset asserts below), so two of them are
/// nested or disjoint and never partially overlap. `Strided` reports its whole
/// block rather than the strided positions inside it, which is conservative in
/// the direction that matters: it only ever makes a later claim accumulate.
fn claim_range(claim: &StackClaim) -> (usize, usize) {
    match claim {
        StackClaim::Point { offset, low_point, .. } => (*offset, *offset + (1usize << low_point.len())),
        StackClaim::Strided {
            offset,
            stride_log,
            point,
            ..
        } => (*offset, *offset + (1usize << (stride_log + point.len()))),
    }
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Open the committed `F64` stack: discharge every `point_claims` slice
/// evaluation AND the ring-switched q_keccak claims (`ring`) in ONE WHIR
/// run, reusing the caller's [`super::whir::commit`] output as L0.
///
/// `stack` is the committed message (the caller retains it; it is not stored in
/// [`ProverData`]): the `2^log_n`-word stack truncated to the lane blocks that
/// carry data, so every claim must live inside it and the padding past it is
/// exactly the weight's zero region. `config.initial_k` / `config.log_inv_rates[0]`
/// must match the commit's `log_batch_size` / `log_inv_rate` (enforced by shape
/// asserts inside the WHIR prover).
pub fn open_batch_mixed_whir_stacked(
    ps: &mut ProverState,
    log_n: usize,
    stack: &[F64],
    prover_data: &ProverData,
    config: &ProverConfig,
    point_claims: &[StackClaim],
    ring: &RingSwitchOpen,
) {
    let qkeccak_len = 1usize << ring.qkeccak_vars;
    assert!(
        ring.offset.is_multiple_of(qkeccak_len),
        "q_keccak offset must be 2^qkeccak_vars-aligned"
    );
    assert!(
        ring.offset + qkeccak_len <= stack.len(),
        "q_keccak slice must fit inside the stack"
    );
    assert!(
        point_claims.iter().all(|c| claim_range(c).1 <= stack.len()),
        "every claim must live inside the committed lanes"
    );
    assert!(
        !ring.claims.is_empty(),
        "stacked PCS opening carries at least one ring-switched claim"
    );
    let span = tracing::info_span!("Ring switch").entered();

    // 1. Ring-switch reduction: prepare every claim's s_hat_v (the caller bound
    //    them upstream), then sample one shared linear map.
    let qkeccak = &stack[ring.offset..ring.offset + qkeccak_len];
    let mut rs_states = Vec::with_capacity(ring.claims.len());
    for claim in &ring.claims {
        assert_eq!(
            claim.suffix_point.len(),
            ring.qkeccak_vars,
            "ring-switch suffix point must have qkeccak_vars coords"
        );
        rs_states.push(ring_switch::prove_prepare(
            qkeccak,
            &claim.suffix_point,
            claim.s_hat_v.as_deref(),
        ));
    }
    let map_challenges = ring_switch::sample_map_challenges(ps);
    let coordinate_weights = ring_switch::build_coordinate_weights(&map_challenges);

    // 2. The ONE batching challenge both families take disjoint power ranges of. Nothing is
    //    observed first: every claim value reached the caller through a binding stream read, so
    //    the challenge already depends on all of them (`leanvm_core::pcs::open`).
    let lambdas = powers(ps.sample(), ring.claims.len() + point_claims.len());
    let (lambdas_rs, lambdas_pd) = lambdas.split_at(ring.claims.len());

    let rs_outputs: Vec<_> = rs_states
        .into_iter()
        .zip(lambdas_rs.iter().copied())
        .map(|(state, lambda)| ring_switch::prove_finish_deferred(state, &coordinate_weights, lambda))
        .collect();
    drop(span);

    // 3. Combined target and lifted stack weight b_stack: the lambda-weighted
    //    rs_eq_ind sum scattered at the q_keccak slice, plus the point-claim
    //    eq tensors scattered at their offsets.
    let target = rs_outputs
        .iter()
        .fold(F192::ZERO, |acc, out| acc + out.batched_sumcheck_claim)
        + point_claims
            .iter()
            .zip(lambdas_pd)
            .fold(F192::ZERO, |sum, (claim, &lambda)| sum + lambda * claim.value());

    // The lifted weight is built and consumed in one pass: each lane window is
    // filled from the ring-switch outputs and the point claims, then feeds
    // round 0's message while it is still hot, so nothing re-reads the buffer.
    let lane_block = 1usize << (log_n - config.initial_k);
    let (b_stack, message) = tracing::info_span!("Basis")
        .in_scope(|| basis::build(stack, lane_block, point_claims, lambdas_pd, ring, &rs_outputs));

    // 4. One WHIR over the full stack against the combined claim (the
    //    stack is borrowed by the prover; no copy).
    super::whir::recursive_prover_with_prepared_basis(
        config,
        log_n,
        stack,
        b_stack,
        target,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        Some(message),
        ps,
    );
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    #[test]
    fn fused_basis_matches_dense_weights() {
        let mut rng = Rng::new(0xBA515);
        for (lane_vars, lanes) in [(6usize, 1usize), (6, 3), (10, 15), (10, 37)] {
            let lane_block = 1 << lane_vars;
            let stack: Vec<F64> = (0..lanes * lane_block).map(|_| F64(rng.next_u64())).collect();
            let qkeccak_vars = lane_vars + usize::from(lanes > 1);
            let qkeccak_len = 1 << qkeccak_vars;
            let offset = if stack.len() >= 2 * qkeccak_len { qkeccak_len } else { 0 };
            let ring = RingSwitchOpen {
                offset,
                qkeccak_vars,
                claims: (0..2)
                    .map(|_| RingSwitchClaim {
                        suffix_point: rng.ext_vec(qkeccak_vars),
                        s_hat_v: None,
                    })
                    .collect(),
            };
            let coordinates = rng.ext_vec(192);
            let rs_outputs: Vec<_> = ring
                .claims
                .iter()
                .map(|claim| {
                    let state =
                        ring_switch::prove_prepare(&stack[offset..offset + qkeccak_len], &claim.suffix_point, None);
                    ring_switch::prove_finish_deferred(state, &coordinates, rng.ext())
                })
                .collect();
            let mut claims: Vec<_> = [
                (offset, qkeccak_vars),
                ((lanes - 1) * lane_block, lane_vars),
                (8, 3),
                (0, 0),
            ]
            .into_iter()
            .map(|(offset, vars)| StackClaim::Point {
                offset,
                low_point: rng.ext_vec(vars),
                value: rng.ext(),
            })
            .collect();
            for stride_log in [0, 1, 3, qkeccak_vars - 1, qkeccak_vars] {
                claims.push(StackClaim::Strided {
                    offset,
                    slot: (1 << stride_log) - 1,
                    stride_log,
                    point: rng.ext_vec(qkeccak_vars - stride_log),
                    value: rng.ext(),
                });
            }
            let lambdas = rng.ext_vec(claims.len());
            // Oracle: the dense weight written out naively, one eq entry at a
            // time, so it shares no code with the fused build under test.
            let mut expected = vec![F192::ZERO; stack.len()];
            ring_switch::combine_deferred_chunk(&rs_outputs, 0, &mut expected[offset..offset + qkeccak_len]);
            for (claim, &lambda) in claims.iter().zip(&lambdas) {
                let (base, stride_log, point) = match claim {
                    StackClaim::Point { offset, low_point, .. } => (*offset, 0, low_point.as_slice()),
                    StackClaim::Strided {
                        offset,
                        slot,
                        stride_log,
                        point,
                        ..
                    } => (*offset + *slot, *stride_log, point.as_slice()),
                };
                for j in 0..1usize << point.len() {
                    let w = point.iter().enumerate().fold(lambda, |w, (i, &p_i)| {
                        w * if (j >> i) & 1 == 1 { p_i } else { F192::ONE + p_i }
                    });
                    expected[base + (j << stride_log)] += w;
                }
            }
            let (actual, message) = basis::build(&stack, lane_block, &claims, &lambdas, &ring, &rs_outputs);
            assert_eq!(&*actual, expected, "lane_vars={lane_vars}, lanes={lanes}");
            let (_, expected_message) = super::super::whir::build_initial_basis(&stack, lane_block, |start, dst| {
                dst.copy_from_slice(&expected[start..start + dst.len()]);
            });
            assert_eq!(message, expected_message);
        }
    }
}
