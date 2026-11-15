// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The commitment to a stack and its opening: every claim on the committed stack in one WHIR opening (Annex B's
//! Open).
//!
//! The stack is `2^log_n` [`F64`] words, of which only the lane blocks that carry data are held, zero past them. The
//! claims are
//!
//! - **point claims** ([`StackClaim`]): multilinear evaluations of aligned slices of the stack, the weight
//!   `eq(low_point, .)` on `[offset, offset + 2^|low_point|)`, which may reach past the committed lanes;
//! - **ring-switched claims** ([`RingSwitchOpen`]): the bit slices of the slice `q_keccak` at a suffix point, each
//!   reduced by [`crate::ring_switch`] to the claim `<q_keccak, Phi(eq(point, .))>`.
//!
//! After one grind, the prover samples the ring switch's map and then one batching challenge `lambda`, of which the
//! ring claims take the first powers and the point claims the next: the weight is `W = sum_k lambda^k W_k` (the
//! batching step of `thm:rbr`). The caller bound every claim's slices and value through the transcript already, so
//! none is observed here. `W` stays factored (`basis`), and level 0's fold rounds run on its terms (`whir_lanes`).

use primitives::field::{F64, F128, powers};
use primitives::multilinear::mle_eval_par;
use primitives::transcript::ProverState;

use crate::ring_switch::{self, RingWeight};
use crate::whir::{self, INITIAL_FOLDING_FACTOR, ProverData};
use crate::whir_lanes::LaneRounds;
use verifier::{BATCH_GRINDING_BITS, MAX_STACKED_CLAIMS, OOD_GRINDING_BITS};

mod basis;

pub(crate) use basis::{LOW_VARS, Terms};

/// A point claim on the stack: `eq(low_point, .)` on the aligned slice `[offset, offset + 2^|low_point|)`; `offset`
/// must be a multiple of `2^|low_point|`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackClaim {
    pub offset: usize,
    pub low_point: Vec<F128>,
}

/// The ring-switched claims, all on the slice `q_keccak = stack[offset..offset + 2^qkeccak_vars]`, `offset` a multiple
/// of its length: per claim, the point of its 64 bit slices, which has `qkeccak_vars` coordinates. The caller sends
/// and checks the slices itself (the Keccak reduction checks them against its last claim), so the opening only binds
/// them to the commitment.
#[derive(Clone, Debug)]
pub struct RingSwitchOpen {
    pub offset: usize,
    pub points: Vec<Vec<F128>>,
}

impl RingSwitchOpen {
    /// `log_2` of `q_keccak`'s length in words: its claims' point length.
    pub(crate) fn qkeccak_vars(&self) -> usize {
        self.points.first().map_or(0, Vec::len)
    }
}

/// A committed stack: the codeword and its Merkle tree, and the OOD sample's claim, which [`open`] discharges last.
pub struct Committed {
    prover_data: ProverData,
    log_n: usize,
    log_inv_rate: usize,
    ood: StackClaim,
}

/// Commit to the `2^log_n`-word stack whose lane blocks that carry data are `stack` at rate `2^-log_inv_rate`, send
/// the root, and take the OOD sample.
///
/// The level-0 commitment takes no OOD points inside the opening, so on its own it binds a list of up to `L_0`
/// stacks. Right after its root comes its OOD sample: grind, sample `z` of the stack's `m` variables, then send the
/// stack's MLE at `z`. Two list members that differ collide there with probability at most `m / q`: the sample fails
/// to bind with at most `C(L_0, 2) m / q`, and every later challenge faces one candidate.
pub fn commit(ps: &mut ProverState, stack: &[F64], log_n: usize, log_inv_rate: usize) -> Committed {
    let prover_data = whir::commit(stack, log_n, log_inv_rate);
    ps.add_root(&prover_data.root());
    ps.grind(OOD_GRINDING_BITS);
    let low_point = ps.sample_vec(log_n);
    ps.add_scalar(tracing::info_span!("OOD").in_scope(|| mle_eval_par(stack, &low_point)));
    Committed {
        prover_data,
        log_n,
        log_inv_rate,
        ood: StackClaim { offset: 0, low_point },
    }
}

/// Open the committed stack at every point claim, then the OOD sample's, and every ring-switched claim, in one WHIR
/// opening.
///
/// `stack` is the committed message, as given to [`commit`]; the opening frees it once level 0's rounds no longer read
/// it.
pub fn open(
    ps: &mut ProverState,
    committed: Committed,
    stack: Vec<F64>,
    point_claims: &[StackClaim],
    ring: &RingSwitchOpen,
) {
    let Committed {
        prover_data,
        log_n,
        log_inv_rate,
        ood,
    } = committed;
    let config = verifier::derive_config(log_n, log_inv_rate)
        .unwrap_or_else(|e| panic!("whir config for log_n={log_n}, log_inv_rate={log_inv_rate}: {e}"));
    let point_claims = [point_claims, &[ood]].concat();
    let qkeccak = 1usize << ring.qkeccak_vars();
    assert!(ring.offset.is_multiple_of(qkeccak), "q_keccak is aligned");
    assert!(ring.offset + qkeccak <= stack.len(), "q_keccak lies inside the stack");
    assert!(
        ring.points.iter().all(|point| point.len() == ring.qkeccak_vars()),
        "every ring claim is on q_keccak"
    );
    for StackClaim { offset, low_point } in &point_claims {
        assert!(
            offset + (1 << low_point.len()) <= 1 << log_n,
            "every claim lies inside the stack"
        );
    }
    assert!(ring.points.len() + point_claims.len() <= MAX_STACKED_CLAIMS);
    // One grind covers the map's challenges and lambda: one verifier message.
    ps.grind(BATCH_GRINDING_BITS);
    let phi = ring_switch::coordinate_weights(&std::array::from_fn(|_| ps.sample()));
    let lambdas = powers(ps.sample(), ring.points.len() + point_claims.len());
    let (ring_lambdas, point_lambdas) = lambdas.split_at(ring.points.len());
    let rings: Vec<RingWeight> = ring
        .points
        .iter()
        .zip(ring_lambdas)
        .map(|(point, &lambda)| RingWeight {
            phi: phi.map(|w| lambda * w),
            point: point.clone(),
        })
        .collect();

    let lane_vars = log_n - INITIAL_FOLDING_FACTOR;
    let (terms, a) = tracing::info_span!("Basis")
        .in_scope(|| basis::initial_basis(log_n, lane_vars, &point_claims, point_lambdas, ring.offset, &rings));
    whir::open(ps, &config, LaneRounds::new(stack, terms, a), prover_data);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring_switch::RingFold;
    use crate::whir::{Dense, FoldChallenges, FoldRounds};
    use primitives::test_rng::Rng;

    /// The OOD value sent is the zero-padded stack's MLE at the sampled point, written out one eq weight at a time.
    #[test]
    fn ood_value_is_the_padded_stack_evaluation() {
        let mut rng = Rng::new(0x919);
        let (log_n, lane_vars) = (16, 10);
        let stack: Vec<F64> = (0..13 << lane_vars).map(|_| F64(rng.next_u64())).collect();
        let mut ps = ProverState::new([1; 4], [2; 4]);
        let StackClaim { offset, low_point } = commit(&mut ps, &stack, log_n, 1).ood;
        assert_eq!((offset, low_point.len()), (0, log_n));
        let naive: F128 = stack
            .iter()
            .enumerate()
            .map(|(j, &word)| {
                let eq = low_point.iter().enumerate().fold(F128::ONE, |w, (i, &p)| {
                    w * if (j >> i) & 1 == 1 { p } else { F128::ONE + p }
                });
                eq.mul_base(word)
            })
            .sum();
        let sent = *ps.into_proof().stream.last().expect("the value is sent last");
        assert_eq!(sent, verifier::E::new(naive.c0, naive.c1));
    }

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
                    })
                    .collect();
                let lambdas = rng.ext_vec(claims.len());

                // Oracle: the dense weight written out naively, one eq entry at a time.
                let mut dense = vec![F128::ZERO; lane_block << LANE_ROUNDS];
                for ring in &rings {
                    RingFold::new(ring.phi, &ring.point).add_chunk(0, &mut dense[offset..offset + qkeccak_len]);
                }
                for (claim, &lambda) in claims.iter().zip(&lambdas) {
                    let StackClaim { offset, low_point } = claim;
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
