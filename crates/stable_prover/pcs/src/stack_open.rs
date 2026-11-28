// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The commitment to a stack and its opening: every claim on the committed stack in one WHIR opening (Annex B's
//! Open).
//!
//! The stack is `2^log_n` [`F64`] words, in lane blocks of `2^lane_vars` words, of which only the blocks that carry
//! data are held, zero past them. The claims are
//!
//! - **point claims** ([`StackClaim`]): multilinear evaluations of aligned slices of the stack, the weight
//!   `eq(low_point, .)` on `[offset, offset + 2^|low_point|)`, which may reach past the committed lanes, or a sum of
//!   such weights under one value;
//! - **ring-switched claims** ([`RingSwitchOpen`]): the bit slices of some aligned slices of the stack, each claim a
//!   scaled sum of pieces, reduced by [`crate::ring_switch`] to the claim `<stack, sum_p Phi(scale_p eq(point_p, .))>`.
//!
//! After one grind, the prover samples the ring switch's map, then `rho` when there are several ring claims, then one
//! batching challenge `lambda`. Ring claim `j` joins the merged ring claim as `rho^j` times itself, inside the map, which
//! is not `E`-linear (`verifier::ring_switch`); the merged ring claim takes `lambda^0` and the point claims the next
//! powers: the weight is `W = sum_k lambda^k W_k` (the batching step of `thm:rbr`). The caller bound every claim's
//! slices and value through the transcript already, so none is observed here. `W` stays factored (`basis`), and level
//! 0's fold rounds run on its terms (`whir_lanes`).

use primitives::field::{F64, F128, powers};
use primitives::multilinear::mle_eval_par;
use primitives::transcript::ProverState;

use crate::ring_switch;
use crate::whir::{self, ProverData};
use crate::whir_lanes::LaneRounds;
use verifier::{BATCH_GRINDING_BITS, INITIAL_FOLDING_FACTOR, MAX_STACKED_CLAIMS, OOD_GRINDING_BITS};

mod basis;

pub(crate) use basis::{LOW_VARS, Terms};

/// A claim on the stack: at one point of an aligned slice, or a sum of such.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackClaim {
    /// `eq(low_point, .)` on the aligned slice `[offset, offset + 2^|low_point|)`; `offset` must be a multiple of
    /// `2^|low_point|`.
    Point { offset: usize, low_point: Vec<F128> },
    /// `sum_p scale_p W_p` over the parts' weights, under one value.
    Sum { parts: Vec<SumPart> },
}

/// One part of a [`StackClaim::Sum`]: a [`StackClaim::Point`] scaled by `scale`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumPart {
    pub offset: usize,
    pub low_point: Vec<F128>,
    pub scale: F128,
}

/// The claims as points, each part of a sum its own, with their batching scalars.
fn flatten(claims: &[StackClaim], lambdas: &[F128]) -> (Vec<StackClaim>, Vec<F128>) {
    let (mut points, mut scales) = (Vec::new(), Vec::new());
    for (claim, &lambda) in claims.iter().zip(lambdas) {
        match claim {
            StackClaim::Sum { parts } => {
                for part in parts {
                    points.push(StackClaim::Point {
                        offset: part.offset,
                        low_point: part.low_point.clone(),
                    });
                    scales.push(lambda * part.scale);
                }
            }
            StackClaim::Point { .. } => {
                points.push(claim.clone());
                scales.push(lambda);
            }
        }
    }
    (points, scales)
}

/// One piece of a ring-switched claim: the bit slices of the aligned slice `stack[offset..offset + 2^|point|]` at
/// `point`, scaled by `scale`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingPiece {
    pub offset: usize,
    pub point: Vec<F128>,
    pub scale: F128,
}

/// A ring-switched claim: the 64 values `s[i] = sum_p scale_p sum_y eq(point_p, y) bit_i(stack[offset_p + y])`. Its
/// weight on piece `p`'s slice is `Phi(scale_p eq(point_p, .))`, `Phi` being `F_2`-linear and the bits in `F_2`. The
/// caller sends and checks the slices itself (the Keccak reduction against its last claim, the link against its row
/// sum-check), so the opening only binds them to the commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchClaim {
    pub pieces: Vec<RingPiece>,
}

impl RingSwitchClaim {
    /// The claim on one slice at `offset`, unscaled.
    pub fn single(offset: usize, point: Vec<F128>) -> Self {
        Self {
            pieces: vec![RingPiece {
                offset,
                point,
                scale: F128::ONE,
            }],
        }
    }
}

/// The ring-switched claims, which share one map.
#[derive(Clone, Debug, Default)]
pub struct RingSwitchOpen {
    pub claims: Vec<RingSwitchClaim>,
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
        ood: StackClaim::Point { offset: 0, low_point },
    }
}

/// Open the committed stack at every ring-switched claim, every point claim, then the OOD sample's, in one WHIR
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
    for piece in ring.claims.iter().flat_map(|claim| &claim.pieces) {
        let len = 1 << piece.point.len();
        assert!(piece.offset.is_multiple_of(len), "a ring piece is aligned");
        assert!(piece.offset + len <= stack.len(), "a ring piece lies inside the stack");
    }
    for claim in &point_claims {
        let parts = match claim {
            StackClaim::Point { offset, low_point } => vec![(*offset, low_point.len())],
            StackClaim::Sum { parts } => parts.iter().map(|p| (p.offset, p.low_point.len())).collect(),
        };
        for (offset, n_vars) in parts {
            assert!(
                offset + (1 << n_vars) <= 1 << log_n,
                "every claim lies inside the stack"
            );
        }
    }
    assert!(usize::from(!ring.claims.is_empty()) + point_claims.len() <= MAX_STACKED_CLAIMS);
    // One grind covers the map's challenges, rho and lambda: one verifier message.
    ps.grind(BATCH_GRINDING_BITS);
    let merging = ring.claims.len() > 1;
    let drawn = ps.sample_packed(ring_switch::MAP_CHALLENGES + usize::from(merging) + 1);
    let challenges = drawn[..ring_switch::MAP_CHALLENGES].try_into().unwrap();
    let rho = if merging {
        drawn[ring_switch::MAP_CHALLENGES]
    } else {
        F128::ONE
    };
    // The merged ring claim takes lambda^0, its claim `j` scaled by rho^j inside the map; the point claims the next
    // powers.
    let maps: Vec<_> = powers(rho, ring.claims.len())
        .into_iter()
        .map(|rho_j| ring_switch::coordinate_weights(&challenges, rho_j))
        .collect();
    let lambdas = powers(drawn[drawn.len() - 1], 1 + point_claims.len());
    let (points, scales) = flatten(&point_claims, &lambdas[1..]);

    let lane_vars = log_n - INITIAL_FOLDING_FACTOR;
    let (terms, a) =
        tracing::info_span!("Basis").in_scope(|| basis::initial_basis(log_n, lane_vars, &points, &scales, ring, &maps));
    whir::open(ps, &config, LaneRounds::new(stack, terms, a), prover_data);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::whir::{Dense, FoldChallenges, FoldRounds};
    use primitives::test_rng::Rng;

    /// `eq(point, j)` over the low `|point|` bits of `j`.
    fn eq_at(point: &[F128], j: usize) -> F128 {
        point.iter().enumerate().fold(F128::ONE, |w, (i, &p)| {
            w * if (j >> i) & 1 == 1 { p } else { F128::ONE + p }
        })
    }

    /// `Phi(v) = sum_(k<64) c_k v^(2^k)` with `c_(8p+b) = f_p g_b^(2^(8p))`: `verifier::ring_switch`'s form of the map.
    fn phi(challenges: &[F128; ring_switch::MAP_CHALLENGES], value: F128) -> F128 {
        let (f, g) = challenges.split_at(8);
        let (mut out, mut power) = (F128::ZERO, value);
        for k in 0..64 {
            let g_b = (0..8 * (k / 8)).fold(g[k % 8], |g, _| g.square());
            out += f[k / 8] * g_b * power;
            power = power.square();
        }
        out
    }

    /// The OOD value sent is the zero-padded stack's MLE at the sampled point, written out one eq weight at a time.
    #[test]
    fn ood_value_is_the_padded_stack_evaluation() {
        let mut rng = Rng::new(0x919);
        let (log_n, lane_vars) = (16, 10);
        let stack: Vec<F64> = (0..13 << lane_vars).map(|_| F64(rng.next_u64())).collect();
        let mut ps = ProverState::new([1; 4], [2; 4]);
        let StackClaim::Point { offset, low_point } = commit(&mut ps, &stack, log_n, 1).ood else {
            panic!("the OOD claim is a point");
        };
        assert_eq!((offset, low_point.len()), (0, log_n));
        let naive: F128 = stack
            .iter()
            .enumerate()
            .map(|(j, &word)| eq_at(&low_point, j).mul_base(word))
            .sum();
        let sent = *ps.into_proof().stream.last().expect("the value is sent last");
        assert_eq!(sent, verifier::E::new(naive.c0, naive.c1));
    }

    /// The level-0 rounds on the factored weight send the tables of the dense rounds on the transposed stack and dense
    /// weight, and leave the same lane and weight. The dense weight is written from `verifier::ring_switch`'s formula,
    /// one entry at a time: `sum_j sum_p Phi(rho^j scale_p eq(point_p, .))` on each piece's slice, plus each claim's
    /// `lambda eq`. The claims: inside one lane and spanning lanes, strides above the lane bit, shared and distinct
    /// points, one over the whole stack past its lanes, sums of points; the rings: two claims on q_keccak, both
    /// spanning lanes and selected by lane bits, merged by `rho`, and a claim of several pieces, some at one point and
    /// in-lane offset in different lanes (one ring), over a stack with runs of equal blocks.
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
                // Two claims on q_keccak, then one of several scaled pieces: q_keccak, a block below it, and columns
                // at one in-lane offset and one point in different lanes, which share a ring.
                let mut ring = RingSwitchOpen {
                    claims: (0..2)
                        .map(|_| RingSwitchClaim::single(offset, rng.ext_vec(qkeccak_vars)))
                        .collect(),
                };
                let other = (offset + qkeccak_len) % stack.len();
                let mut pieces = vec![
                    RingPiece {
                        offset,
                        point: rng.ext_vec(qkeccak_vars),
                        scale: rng.ext(),
                    },
                    RingPiece {
                        offset: other - other % 64,
                        point: rng.ext_vec(6),
                        scale: rng.ext(),
                    },
                ];
                let shared_point = rng.ext_vec(4);
                for lane in 0..lanes_count.min(4) {
                    pieces.push(RingPiece {
                        offset: (lane << lane_vars) + 32,
                        point: shared_point.clone(),
                        scale: rng.ext(),
                    });
                }
                ring.claims.push(RingSwitchClaim { pieces });
                let challenges: [F128; ring_switch::MAP_CHALLENGES] = std::array::from_fn(|_| rng.ext());
                let rho = rng.ext();
                let maps: Vec<_> = powers(rho, ring.claims.len())
                    .into_iter()
                    .map(|rho_j| ring_switch::coordinate_weights(&challenges, rho_j))
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
                let mut claims: Vec<_> = shapes
                    .into_iter()
                    .map(|(offset, vars, point)| StackClaim::Point {
                        offset,
                        low_point: point.unwrap_or_else(|| rng.ext_vec(vars)),
                    })
                    .collect();
                // A sum of two parts at one low point, as the memory term's two limbs.
                let low_point = rng.ext_vec(2);
                claims.push(StackClaim::Sum {
                    parts: vec![
                        SumPart {
                            offset: 4,
                            low_point: low_point.clone(),
                            scale: rng.ext(),
                        },
                        SumPart {
                            offset: 8,
                            low_point,
                            scale: rng.ext(),
                        },
                    ],
                });
                claims.push(StackClaim::Sum {
                    parts: vec![SumPart {
                        offset: 0,
                        low_point: rng.ext_vec(lane_vars),
                        scale: rng.ext(),
                    }],
                });
                let lambdas = rng.ext_vec(claims.len());

                // Oracle: the dense weight written out naively, one entry at a time.
                let mut dense = vec![F128::ZERO; lane_block << LANE_ROUNDS];
                let mut rho_j = F128::ONE;
                for claim in &ring.claims {
                    for piece in &claim.pieces {
                        for y in 0..1usize << piece.point.len() {
                            dense[piece.offset + y] += phi(&challenges, rho_j * piece.scale * eq_at(&piece.point, y));
                        }
                    }
                    rho_j *= rho;
                }
                let mut add_point = |offset: usize, low_point: &[F128], scale: F128| {
                    for j in 0..1usize << low_point.len() {
                        dense[offset + j] += scale * eq_at(low_point, j);
                    }
                };
                for (claim, &lambda) in claims.iter().zip(&lambdas) {
                    match claim {
                        StackClaim::Point { offset, low_point } => add_point(*offset, low_point, lambda),
                        StackClaim::Sum { parts } => {
                            for part in parts {
                                add_point(part.offset, &part.low_point, lambda * part.scale);
                            }
                        }
                    }
                }

                let (points, scales) = flatten(&claims, &lambdas);
                let (terms, a) =
                    basis::initial_basis(lane_vars + LANE_ROUNDS, lane_vars, &points, &scales, &ring, &maps);
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
