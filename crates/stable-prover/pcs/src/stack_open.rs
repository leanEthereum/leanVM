// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The stacked opening: every claim on the committed stack in one WHIR opening (Annex B's Open).
//!
//! The stack is `2^log_n` [`F64`] words, committed by [`crate::whir::commit`], of which only the lane blocks that
//! carry data are held, zero past them. The claims are
//!
//! - **point claims** ([`StackClaim`]): multilinear evaluations of aligned slices of the stack, the weight
//!   `eq(low_point, .)` on `[offset, offset + 2^|low_point|)`, which may reach past the committed lanes;
//! - **ring-switched claims** ([`RingSwitchOpen`]): the bit slices of the slice `q_keccak` at a suffix point, each
//!   reduced by [`crate::ring_switch`] to the claim `<q_keccak, Phi(eq(point, .))>`.
//!
//! After one grind, the prover samples the ring switch's map and then one batching challenge `lambda`, of which the
//! ring claims take the first powers and the point claims the next: the running claim is
//! `sum_k lambda^k c_k` against `W = sum_k lambda^k W_k` (the batching step of `thm:rbr`). The caller bound every
//! claim's slices and value through the transcript already, so none is observed here. `W` stays factored
//! (`basis`), and level 0's fold rounds run on its terms (`whir_lanes`).

use primitives::field::{F64, F128, powers};
use primitives::multilinear::eq_table;
use primitives::transcript::ProverState;

use crate::ring_switch::{self, RingWeight, transpose_s_hat};
use crate::whir::{self, ProverConfig, ProverData};
use crate::whir_config::{BATCH_GRINDING_BITS, MAX_STACKED_CLAIMS};
use crate::whir_lanes::LaneRounds;

mod basis;

pub(crate) use basis::{LOW_VARS, Terms};

/// A point claim on the stack: `eq(low_point, .)` on the aligned slice `[offset, offset + 2^|low_point|)`; `offset`
/// must be a multiple of `2^|low_point|`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackClaim {
    pub offset: usize,
    pub low_point: Vec<F128>,
    pub value: F128,
}

/// One ring-switched claim on `q_keccak`: its 64 bit slices at `suffix_point`, which has `qkeccak_vars` coordinates.
///
/// The caller sends and checks the slices itself (the Keccak reduction checks them against its last claim), so the
/// opening only binds them to the commitment. `None` asks the prover to fold them from the witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchClaim {
    pub suffix_point: Vec<F128>,
    pub s_hat_v: Option<Vec<F128>>,
}

/// The ring-switched claims, all on the slice `q_keccak = stack[offset..offset + 2^qkeccak_vars]`, `offset` a multiple
/// of its length.
#[derive(Clone, Debug)]
pub struct RingSwitchOpen {
    pub offset: usize,
    pub claims: Vec<RingSwitchClaim>,
}

impl RingSwitchOpen {
    /// `log_2` of `q_keccak`'s length in words: its claims' point length.
    pub(crate) fn qkeccak_vars(&self) -> usize {
        self.claims.first().map_or(0, |claim| claim.suffix_point.len())
    }
}

/// Open the committed stack at every point claim and every ring-switched claim, in one WHIR opening against the
/// commitment `prover_data` ([`crate::whir::commit`] at `config`'s level-0 fold and rate).
///
/// `stack` is the committed message, the `2^log_n`-word stack truncated to the lane blocks that carry data; the
/// opening frees it once level 0's rounds no longer read it.
pub fn open_batch_mixed_whir_stacked(
    ps: &mut ProverState,
    log_n: usize,
    stack: Vec<F64>,
    prover_data: ProverData,
    config: &ProverConfig,
    point_claims: &[StackClaim],
    ring: &RingSwitchOpen,
) {
    let qkeccak = 1usize << ring.qkeccak_vars();
    assert!(ring.offset.is_multiple_of(qkeccak), "q_keccak is aligned");
    assert!(ring.offset + qkeccak <= stack.len(), "q_keccak lies inside the stack");
    for StackClaim { offset, low_point, .. } in point_claims {
        assert!(
            offset + (1 << low_point.len()) <= 1 << log_n,
            "every claim lies inside the stack"
        );
    }
    assert!(ring.claims.len() + point_claims.len() <= MAX_STACKED_CLAIMS);
    let span = tracing::info_span!("Ring switch").entered();
    let slices: Vec<[F128; 64]> = ring
        .claims
        .iter()
        .map(|claim| {
            assert_eq!(
                claim.suffix_point.len(),
                ring.qkeccak_vars(),
                "every ring claim is on q_keccak"
            );
            match &claim.s_hat_v {
                Some(slices) => slices.as_slice().try_into().expect("one slice per bit"),
                None => {
                    let q = &stack[ring.offset..ring.offset + qkeccak];
                    ring_switch::fold_1b_rows(q, &eq_table(&claim.suffix_point))
                }
            }
        })
        .collect();
    // One grind covers the map's challenges and lambda: one verifier message.
    ps.grind(BATCH_GRINDING_BITS);
    let phi = ring_switch::coordinate_weights(&std::array::from_fn(|_| ps.sample()));
    let lambdas = powers(ps.sample(), ring.claims.len() + point_claims.len());
    let (ring_lambdas, point_lambdas) = lambdas.split_at(ring.claims.len());

    // A ring claim's value is `sum_w Phi(b_w) t_w` over its transposed slices.
    let mut target = F128::ZERO;
    for (slices, &lambda) in slices.iter().zip(ring_lambdas) {
        target += lambda
            * transpose_s_hat(slices)
                .iter()
                .zip(phi)
                .map(|(&t, w)| w.mul_base(t))
                .sum::<F128>();
    }
    for (StackClaim { value, .. }, &lambda) in point_claims.iter().zip(point_lambdas) {
        target += lambda * *value;
    }
    let rings: Vec<RingWeight> = ring
        .claims
        .iter()
        .zip(ring_lambdas)
        .map(|(claim, &lambda)| RingWeight {
            phi: phi.map(|w| lambda * w),
            point: claim.suffix_point.clone(),
        })
        .collect();
    drop(span);

    let lane_vars = log_n - config.folds[0];
    let (terms, a) = tracing::info_span!("Basis")
        .in_scope(|| basis::initial_basis(log_n, lane_vars, point_claims, point_lambdas, ring.offset, &rings));
    whir::open(ps, config, LaneRounds::new(stack, terms, a), target, prover_data);
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    use crate::ring_switch::RingFold;
    use crate::whir::{Dense, FoldChallenges, FoldRounds};

    /// The level-0 rounds on the factored weight send the tables of the dense rounds on the transposed stack and dense
    /// weight, and leave the same lane and weight, across claims inside one lane and spanning lanes, strides above the
    /// lane bit, shared and distinct points, one over the whole stack past its lanes, runs of equal blocks, and a
    /// q_keccak ring both spanning lanes and selected by lane bits.
    #[test]
    fn projected_lane_rounds_match_the_dense_rounds() {
        const LANE_ROUNDS: usize = 6;
        let mut rng = Rng::new(0xBA515);
        for (lane_vars, lanes_count, qkeccak_vars) in [
            (6usize, 1usize, 6usize),
            (6, 3, 7),
            (8, 13, 10),
            (8, 13, 8),
            (8, 5, 6),
            (10, 37, 12),
            (12, 5, 13),
            (14, 3, 15),
            (16, 3, 17),
        ] {
            let lane_block = 1usize << lane_vars;
            let mut stack: Vec<F64> = (0..lanes_count * lane_block).map(|_| F64(rng.next_u64())).collect();
            // Runs of equal blocks, which share their projections.
            for b in (1..stack.len() >> LOW_VARS).filter(|b| b % 4 != 0) {
                stack.copy_within((b - 1) << LOW_VARS..b << LOW_VARS, b << LOW_VARS);
            }
            let qkeccak_len = 1usize << qkeccak_vars;
            for offset in [0, qkeccak_len] {
                if offset + qkeccak_len > stack.len() {
                    continue;
                }
                let rings: Vec<RingWeight> = (0..2)
                    .map(|_| RingWeight {
                        phi: std::array::from_fn(|_| rng.ext()),
                        point: rng.ext_vec(qkeccak_vars),
                    })
                    .collect();
                let last_lane = (lanes_count - 1) * lane_block;
                let shared = rng.ext_vec(lane_vars);
                // Two claims on one low point at separated offsets: a pattern active on some blocks only.
                let separated = rng.ext_vec(10);
                let mut shapes = vec![
                    (1024, 10, Some(separated.clone())),
                    (6144, 10, Some(separated)),
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
                    if lanes_count >= 1 << spanned {
                        shapes.push((0, lane_vars + spanned, None));
                    }
                }
                shapes.retain(|&(offset, vars, _)| offset + (1 << vars) <= stack.len());
                // The whole stack, past the committed lanes.
                shapes.push((0, lane_vars + LANE_ROUNDS, None));
                let claims: Vec<_> = shapes
                    .into_iter()
                    .map(|(offset, vars, point)| StackClaim {
                        offset,
                        low_point: point.unwrap_or_else(|| rng.ext_vec(vars)),
                        value: rng.ext(),
                    })
                    .collect();
                let lambdas = rng.ext_vec(claims.len());

                // Oracle: the dense weight written out naively, one eq entry at a time.
                let mut dense = vec![F128::ZERO; lane_block << LANE_ROUNDS];
                for ring in &rings {
                    RingFold::new(ring.phi, &ring.point).add_chunk(0, &mut dense[offset..offset + qkeccak_len]);
                }
                for (claim, &lambda) in claims.iter().zip(&lambdas) {
                    let StackClaim { offset, low_point, .. } = claim;
                    for j in 0..1usize << low_point.len() {
                        let w = low_point.iter().enumerate().fold(lambda, |w, (i, &p_i)| {
                            w * if (j >> i) & 1 == 1 { p_i } else { F128::ONE + p_i }
                        });
                        dense[offset + j] += w;
                    }
                }

                let (terms, a) =
                    basis::initial_basis(lane_vars + LANE_ROUNDS, lane_vars, &claims, &lambdas, offset, &rings);
                let mut lanes = LaneRounds::new(stack.clone(), terms, a);
                let context =
                    format!("lane_vars={lane_vars}, lanes={lanes_count}, qkeccak_vars={qkeccak_vars}, offset={offset}");
                // The reference: the stack and the weight coefficient by coefficient, lanes interleaved, the stack's
                // absent ones zero.
                let stride = 1usize << LANE_ROUNDS;
                let transpose = |v: &dyn Fn(usize) -> F128| -> Vec<F128> {
                    (0..lane_block * stride)
                        .map(|i| v(i % stride * lane_block + i / stride))
                        .collect()
                };
                let mut reference = Dense {
                    f: transpose(&|i| stack.get(i).map_or(F128::ZERO, |&word| F128::from(word))),
                    w: transpose(&|i| dense[i]),
                    stride,
                };
                for round in 0..LANE_ROUNDS {
                    let ch = FoldChallenges {
                        alpha: rng.ext(),
                        beta: rng.ext(),
                    };
                    assert_eq!(lanes.table(), reference.table(), "{context}, round {round}");
                    reference.fold(&ch);
                    lanes.fold(&ch);
                }
                let (p, w) = lanes.finish();
                assert_eq!(p, reference.f, "{context}, lane");
                assert_eq!(w, reference.w, "{context}, weight");
            }
        }
    }
}
