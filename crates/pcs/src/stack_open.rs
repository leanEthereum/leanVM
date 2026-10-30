// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Stacked batch-mixed opening for the F64-committed PCS.
//!
//! The committed witness is a stack of `2^log_n` [`F64`] words (committed via
//! [`super::whir::commit`], which only encodes and only transmits the lane blocks
//! that carry data: every claim lives inside them and the weight is zero past
//! them), and one WHIR run discharges
//!
//! - **point claims** ([`StackClaim`]): plain multilinear evaluations of
//!   aligned sub-slices of the stack (a claim's weight is `eq(low_point, .)`
//!   supported on `[offset, offset + 2^|low_point|)`),
//! - **ring-switched claims** ([`RingSwitchOpen`]): bit-MLE evaluation claims
//!   on the packed sub-block `q_keccak = stack[offset .. offset + 2^qkeccak_vars]`,
//!   reduced per claim by [`super::ring_switch::prove_prepare`] and the
//!   deferred finish path to an inner-product
//!   claim `<q_keccak, rs_eq_ind> = sumcheck_claim` against the transparent
//!   E-valued weight `rs_eq_ind`.
//!
//! All claims are lambda-folded into ONE combined weight `b_stack` over the
//! whole stack plus one `target`, then proved by
//! `whir::recursive_prover_with_prepared_basis`. The weight is never
//! materialized over the stack: the lane rounds run on its terms (see the `basis`
//! module), and only the one lane block that survives them is built. A verifier recomputes
//! the target from the claims and evaluates `MLE(b_stack)` once, at the final fold
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
//! which is exactly what a dense `b_stack` scatter would produce (each claim's
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

pub(crate) use basis::Terms;

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
}

impl StackClaim {
    #[inline]
    pub fn value(&self) -> F192 {
        let StackClaim::Point { value, .. } = self;
        *value
    }

    /// The aligned dyadic range of the stack its weight is supported on.
    fn range(&self) -> (usize, usize) {
        let StackClaim::Point { offset, low_point, .. } = self;
        (*offset, *offset + (1usize << low_point.len()))
    }
}

/// One ring-switched claim on the q_keccak sub-block: the 64 bit-slice MLEs of
/// q_keccak at `suffix_point` (see [`super::ring_switch`]), which has
/// `qkeccak_vars` coords, the same for every claim.
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
    pub claims: Vec<RingSwitchClaim>,
}

impl RingSwitchOpen {
    /// log2 of q_keccak's length in F64 words, its claims' point length; the
    /// opener slices `q_keccak = stack[offset .. offset + 2^qkeccak_vars]` (no
    /// separate copy).
    pub fn qkeccak_vars(&self) -> usize {
        self.claims.first().map_or(0, |claim| claim.suffix_point.len())
    }
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Open the committed `F64` stack: discharge every `point_claims` slice
/// evaluation AND the ring-switched q_keccak claims (`ring`) in ONE WHIR
/// run, reusing the caller's [`super::whir::commit`] output as L0.
///
/// `stack` is the committed message (not stored in [`ProverData`]), consumed: it goes once nothing reads it, after
/// the lane rounds or, when the commit kept no codeword, after the L0 open. It is the `2^log_n`-word stack truncated
/// to the lane blocks that
/// carry data, so every claim must live inside it and the padding past it is
/// exactly the weight's zero region. `config.initial_k` / `config.log_inv_rates[0]`
/// must match the commit's `log_batch_size` / `log_inv_rate` (enforced by shape
/// asserts inside the WHIR prover).
pub fn open_batch_mixed_whir_stacked(
    ps: &mut ProverState,
    log_n: usize,
    stack: Vec<F64>,
    prover_data: ProverData,
    config: &ProverConfig,
    point_claims: &[StackClaim],
    ring: &RingSwitchOpen,
) {
    let qkeccak_len = 1usize << ring.qkeccak_vars();
    assert!(
        ring.offset.is_multiple_of(qkeccak_len),
        "q_keccak offset must be 2^qkeccak_vars-aligned"
    );
    assert!(
        ring.offset + qkeccak_len <= stack.len(),
        "q_keccak slice must fit inside the stack"
    );
    assert!(
        point_claims.iter().all(|c| c.range().1 <= stack.len()),
        "every claim must live inside the committed lanes"
    );
    let span = tracing::info_span!("Ring switch").entered();

    // 1. Ring-switch reduction: prepare every claim's s_hat_v (the caller bound
    //    them upstream), then sample one shared linear map.
    let qkeccak = &stack[ring.offset..ring.offset + qkeccak_len];
    let mut rs_states = Vec::with_capacity(ring.claims.len());
    for claim in &ring.claims {
        assert_eq!(
            claim.suffix_point.len(),
            ring.qkeccak_vars(),
            "every ring-switch suffix point must have qkeccak_vars coords"
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
    //    eq tensors scattered at their offsets (the weight itself stays factored).
    let target = rs_outputs
        .iter()
        .fold(F192::ZERO, |acc, out| acc + out.batched_sumcheck_claim)
        + point_claims
            .iter()
            .zip(lambdas_pd)
            .fold(F192::ZERO, |sum, (claim, &lambda)| sum + lambda * claim.value());

    // The lane rounds run on the weight's terms and a projection of the stack onto them, so the
    // lifted weight over the stack is never built.
    let lane_vars = log_n - config.initial_k;
    let rings: Vec<_> = rs_outputs.into_iter().map(|output| output.weight).collect();
    let initial_basis = tracing::info_span!("Basis")
        .in_scope(|| basis::initial_basis(&stack, lane_vars, point_claims, lambdas_pd, ring, &rings));

    // 4. One WHIR over the full stack against the combined claim (the
    //    prover takes the stack; no copy).
    super::whir::recursive_prover_with_prepared_basis(config, log_n, stack, initial_basis, target, prover_data, ps);
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    use crate::whir::{SumcheckMessage, SumcheckProver};

    /// `(u_0, u_2)` of the pairs of blocks `(2i, 2i + 1)`, a last odd block against zeros.
    fn blocks_msg(f: &[F192], b: &[F192], block: usize) -> SumcheckMessage {
        let (mut u_0, mut u_2) = (F192::ZERO, F192::ZERO);
        for (f, b) in f.chunks(2 * block).zip(b.chunks(2 * block)) {
            for x in 0..block {
                let (f0, b0) = (f[x], b[x]);
                let (f1, b1) = (
                    f.get(block + x).copied().unwrap_or(F192::ZERO),
                    b.get(block + x).copied().unwrap_or(F192::ZERO),
                );
                u_0 += f0 * b0;
                u_2 += (f0 + f1) * (b0 + b1);
            }
        }
        SumcheckMessage { u_0, u_2 }
    }

    /// `(u_0, u_2)` of the adjacent pairs `(2j, 2j + 1)`.
    fn adjacent_msg(f: &[F192], b: &[F192]) -> SumcheckMessage {
        let (mut u_0, mut u_2) = (F192::ZERO, F192::ZERO);
        for (f, b) in f.as_chunks::<2>().0.iter().zip(b.as_chunks::<2>().0.iter()) {
            u_0 += f[0] * b[0];
            u_2 += (f[0] + f[1]) * (b[0] + b[1]);
        }
        SumcheckMessage { u_0, u_2 }
    }

    /// One lane round: block `2j` and block `2j + 1` fold into block `j` as `x0 + r (x0 + x1)`,
    /// a last odd block against zeros.
    fn fold_blocks(x: &[F192], block: usize, r: F192) -> Vec<F192> {
        x.chunks(2 * block)
            .flat_map(|pair| (0..block).map(move |i| (pair[i], pair.get(block + i).copied().unwrap_or(F192::ZERO))))
            .map(|(x0, x1)| x0 + r * (x0 + x1))
            .collect()
    }

    /// The lane rounds of a projected basis must send the messages of the naive lane rounds on
    /// the dense weight and leave the same witness, weight and next message, across claims inside
    /// one lane and spanning lanes, strides above the lane bit, shared and distinct points, and a
    /// q_keccak ring both spanning lanes and selected by lane bits.
    #[test]
    fn projected_lane_rounds_match_the_naive_dense_rounds() {
        const LANE_ROUNDS: usize = 6;
        let mut rng = Rng::new(0xBA515);
        for (lane_vars, lanes, qkeccak_vars) in [
            (6usize, 1usize, 6usize),
            (6, 3, 7),
            (8, 13, 10),
            (8, 13, 8),
            (8, 5, 6),
            (10, 37, 12),
            (12, 5, 13),
            // Sixteen blocks a lane: the claims' sums run eight blocks at a time.
            (14, 3, 15),
        ] {
            let lane_block = 1usize << lane_vars;
            let stack: Vec<F64> = (0..lanes * lane_block).map(|_| F64(rng.next_u64())).collect();
            let qkeccak_len = 1usize << qkeccak_vars;
            for offset in [0, qkeccak_len] {
                if offset + qkeccak_len > stack.len() {
                    continue;
                }
                let ring = RingSwitchOpen {
                    offset,
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
                let last_lane = (lanes - 1) * lane_block;
                let shared = rng.ext_vec(lane_vars);
                let mut shapes = vec![
                    (offset, qkeccak_vars, None),
                    (offset, qkeccak_vars, None),
                    (last_lane, lane_vars, Some(shared.clone())),
                    (0, lane_vars, Some(shared)),
                    (last_lane, lane_vars, None),
                    (8, 3, None),
                    (8, 3, None),
                    (0, 0, None),
                    (last_lane + 4, 2, None),
                ];
                for spanned in 1..=2 {
                    if lanes >= 1 << spanned {
                        shapes.push((0, lane_vars + spanned, None));
                    }
                }
                let claims: Vec<_> = shapes
                    .into_iter()
                    .map(|(offset, vars, point)| StackClaim::Point {
                        offset,
                        low_point: point.unwrap_or_else(|| rng.ext_vec(vars)),
                        value: rng.ext(),
                    })
                    .collect();
                let lambdas = rng.ext_vec(claims.len());

                // Oracle: the dense weight written out naively, one eq entry at a time.
                let mut dense = vec![F192::ZERO; stack.len()];
                ring_switch::combine_deferred_chunk(&rs_outputs, &mut dense[offset..offset + qkeccak_len]);
                for (claim, &lambda) in claims.iter().zip(&lambdas) {
                    let StackClaim::Point { offset, low_point, .. } = claim;
                    for j in 0..1usize << low_point.len() {
                        let w = low_point.iter().enumerate().fold(lambda, |w, (i, &p_i)| {
                            w * if (j >> i) & 1 == 1 { p_i } else { F192::ONE + p_i }
                        });
                        dense[offset + j] += w;
                    }
                }

                let rings: Vec<_> = rs_outputs.iter().map(|output| output.weight.clone()).collect();
                let projected = basis::initial_basis(&stack, lane_vars, &claims, &lambdas, &ring, &rings);
                let target = rng.ext();
                let (mut prover, msg) = SumcheckProver::new(stack.clone(), projected, target, lane_block);
                let context =
                    format!("lane_vars={lane_vars}, lanes={lanes}, qkeccak_vars={qkeccak_vars}, offset={offset}");
                let mut f: Vec<F192> = stack.iter().map(|&word| F192::from(word)).collect();
                assert_eq!(msg, blocks_msg(&f, &dense, lane_block), "{context}, round 0");
                for round in 1..=LANE_ROUNDS {
                    let r = rng.ext();
                    let last = round == LANE_ROUNDS;
                    f = fold_blocks(&f, lane_block, r);
                    dense = fold_blocks(&dense, lane_block, r);
                    let want = if last {
                        adjacent_msg(&f, &dense)
                    } else {
                        blocks_msg(&f, &dense, lane_block)
                    };
                    assert_eq!(prover.fold_lane(r, last), want, "{context}, round {round}");
                }
                assert_eq!(prover.f_ext(), f, "{context}, witness");
                assert_eq!(prover.basis(), &dense[..], "{context}, weight");
            }
        }
    }
}
