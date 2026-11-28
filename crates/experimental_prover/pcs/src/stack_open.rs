// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Every claim on the committed stack in one WHIR opening (Annex B's Open).
//!
//! The stack is `2^log_n` [`F64`] words (committed by [`super::whir::commit`], which encodes only the lane blocks that
//! carry data, the stack being zero past them). The claims are
//!
//! - **point claims** ([`StackClaim`]): multilinear evaluations of aligned slices of the stack, the weight
//!   `eq(low_point, .)` on `[offset, offset + 2^|low_point|)`, which may reach past the committed lanes, or a sum of
//!   such weights under one value;
//! - **ring-switched claims** ([`RingSwitchOpen`]): the bit slices of some aligned slices of the stack, each claim a
//!   scaled sum of pieces, reduced by [`super::ring_switch`] to the claim `<stack, sum_p Phi(scale_p eq(point_p, .))>`.
//!
//! After one grind ([`BATCH_GRINDING_BITS`]), the prover samples the ring switch's map, then `rho` when there are
//! several ring claims, then one batching challenge `lambda`, in one packed draw. Ring claim `j` joins the merged ring
//! claim as `rho^j` times itself, inside the map, which is not `E`-linear (`verifier::ring_switch`); the merged ring
//! claim takes `lambda^0` and the point claims the next powers: the weight is `W = sum_k lambda^k W_k` (the batching
//! step of `thm:rbr`). The caller bound every claim's slices and value through the transcript already, so none is
//! observed here. `W` stays factored (`basis`): level 0's fold rounds run on its terms, and only the one lane block
//! that survives them is built. A verifier evaluates `W`'s multilinear extension once, at the final fold point.

use primitives::field::{F64, F128, powers};
use primitives::transcript::ProverState;

use super::pack::PACKING_WIDTH;
use super::ring_switch;
use super::whir::{ProverConfig, ProverData};
use super::whir_config::MAX_STACKED_CLAIMS;
use verifier::BATCH_GRINDING_BITS;

mod basis;

pub(crate) use basis::{SWEEP, Terms};

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
        low_point: Vec<F128>,
        value: F128,
    },
    /// `sum_p scale_p * eq(low_point_p, .)` on each part's aligned slice, as
    /// [`StackClaim::Point`] places them: one value for several weighted points.
    Sum { parts: Vec<SumPart>, value: F128 },
}

/// One part of a [`StackClaim::Sum`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumPart {
    pub offset: usize,
    pub low_point: Vec<F128>,
    pub scale: F128,
}

impl StackClaim {
    #[inline]
    pub fn value(&self) -> F128 {
        match self {
            StackClaim::Point { value, .. } | StackClaim::Sum { value, .. } => *value,
        }
    }

    /// The end of the stack range its weight is supported on.
    fn end(&self) -> usize {
        match self {
            StackClaim::Point { offset, low_point, .. } => *offset + (1usize << low_point.len()),
            StackClaim::Sum { parts, .. } => parts
                .iter()
                .map(|part| part.offset + (1usize << part.low_point.len()))
                .max()
                .unwrap_or(0),
        }
    }
}

/// The claims as point claims, each part of a sum its own, with their batching scalars.
fn flatten(claims: &[StackClaim], lambdas: &[F128]) -> (Vec<StackClaim>, Vec<F128>) {
    let mut points = Vec::with_capacity(claims.len());
    let mut scales = Vec::with_capacity(claims.len());
    for (claim, &lambda) in claims.iter().zip(lambdas) {
        match claim {
            StackClaim::Point { .. } => {
                points.push(claim.clone());
                scales.push(lambda);
            }
            StackClaim::Sum { parts, .. } => {
                for part in parts {
                    points.push(StackClaim::Point {
                        offset: part.offset,
                        low_point: part.low_point.clone(),
                        value: F128::ZERO,
                    });
                    scales.push(lambda * part.scale);
                }
            }
        }
    }
    (points, scales)
}

/// One piece of a ring-switched claim: the bit-slice MLEs of the aligned
/// sub-block `stack[offset .. offset + 2^|point|]` at `point`, scaled by `scale`.
///
/// `slices`, when the caller has them, are those 64 bit-slices unscaled. They are the
/// projection of the piece's lane onto its ring's terms in level 0's first round, which
/// the prover then takes as given rather than folding the sub-block's bits again. Only a
/// piece inside one lane block can carry them, and they never reach the transcript.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingPiece {
    pub offset: usize,
    pub point: Vec<F128>,
    pub scale: F128,
    pub slices: Option<Vec<F128>>,
}

/// One ring-switched claim: the 64 values `s_hat_v[i] = sum_p scale_p *
/// sum_y eq(point_p, y) * bit_i(stack[offset_p + y])` (see [`super::ring_switch`]).
/// Its weight on piece `p`'s sub-block is `Phi(scale_p * eq(point_p, .))`, valid
/// because `Phi` is `F_2`-linear and the committed bits lie in `F_2`.
///
/// `s_hat_v` holds those 64 values. The caller transmits and checks them itself
/// (the Keccak reduction or the link sends them and checks them against its last claim), so this
/// layer only binds them to the commitment. `None` asks the prover to fold the slices from the witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchClaim {
    pub pieces: Vec<RingPiece>,
    pub s_hat_v: Option<Vec<F128>>,
}

impl RingSwitchClaim {
    /// The claim on one sub-block at `offset`, unscaled.
    pub fn single(offset: usize, point: Vec<F128>, s_hat_v: Option<Vec<F128>>) -> Self {
        Self {
            pieces: vec![RingPiece {
                offset,
                point,
                scale: F128::ONE,
                slices: None,
            }],
            s_hat_v,
        }
    }
}

/// The ring-switched claims discharged in the same opening as the [`StackClaim`]s. Each claim may carry its bound
/// `s_hat_v`. Every claim shares one map's challenges.
#[derive(Clone, Debug, Default)]
pub struct RingSwitchOpen {
    pub claims: Vec<RingSwitchClaim>,
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Open the committed `F64` stack: discharge every `point_claims` slice evaluation and the ring-switched claims
/// (`ring`) in one WHIR run, reusing the caller's [`super::whir::commit`] output as L0.
///
/// `stack` is the committed message (not stored in [`ProverData`]), consumed: it goes once nothing reads it, after
/// the first fold round or, when the commit kept no codeword, after the L0 open. It is the `2^log_n`-word stack truncated
/// to the lane blocks that carry data, zero past them. `config.initial_k` / `config.log_inv_rates[0]`
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
    let pieces = || ring.claims.iter().flat_map(|claim| &claim.pieces);
    for piece in pieces() {
        let len = 1usize << piece.point.len();
        assert!(
            piece.offset.is_multiple_of(len),
            "a ring piece's offset must be 2^|point|-aligned"
        );
        assert!(
            piece.offset + len <= stack.len(),
            "a ring piece must fit inside the stack"
        );
    }
    let lane_vars = log_n - config.initial_k;
    assert!(
        point_claims.iter().all(|c| c.end() <= 1 << log_n),
        "every claim must live inside the stack"
    );
    // The ring claims merge into one.
    assert!(
        usize::from(!ring.claims.is_empty()) + point_claims.len() <= MAX_STACKED_CLAIMS,
        "at most MAX_STACKED_CLAIMS stacked claims"
    );
    let span = tracing::info_span!("Ring switch").entered();

    // 1. Ring-switch reduction: every claim's s_hat_v (the caller bound them upstream), its pieces' scaled sum, then
    //    one shared linear map.
    let s_hat_vs: Vec<[F128; PACKING_WIDTH]> = (ring.claims.iter())
        .map(|claim| match &claim.s_hat_v {
            Some(s_hat_v) => s_hat_v.as_slice().try_into().expect("one slice per packing bit"),
            None => {
                let mut sum = [F128::ZERO; PACKING_WIDTH];
                for piece in &claim.pieces {
                    let slice = &stack[piece.offset..piece.offset + (1usize << piece.point.len())];
                    for (acc, v) in sum.iter_mut().zip(ring_switch::prove_prepare(slice, &piece.point)) {
                        *acc += piece.scale * v;
                    }
                }
                sum
            }
        })
        .collect();
    // One grind covers the map challenges, rho and the batching challenge below: one verifier message, one packed
    // draw. Several ring claims merge into one: claim `j` joins as `rho^j` times itself, inside the map, which is not
    // `E`-linear (`verifier::ring_switch`).
    ps.grind(BATCH_GRINDING_BITS);
    let merging = ring.claims.len() > 1;
    let drawn = ps.sample_packed(ring_switch::MAP_CHALLENGES + usize::from(merging) + 1);
    let map_challenges: [F128; ring_switch::MAP_CHALLENGES] = drawn[..ring_switch::MAP_CHALLENGES].try_into().unwrap();
    let rho = if merging {
        drawn[ring_switch::MAP_CHALLENGES]
    } else {
        F128::ONE
    };

    // 2. The ONE batching challenge: the merged ring claim takes its zeroth power, the point claims the next. Nothing
    //    is observed first: every claim value reached the caller through a binding stream read, so the challenge
    //    already depends on all of them (`lean_vm_core::pcs::open`).
    let lambdas = powers(drawn[drawn.len() - 1], 1 + point_claims.len());
    let lambdas_pd = &lambdas[1..];

    // Ring claim `j`'s map, `v -> Phi(rho^j v)`.
    let maps: Vec<_> = powers(rho, ring.claims.len())
        .into_iter()
        .map(|rho_j| ring_switch::build_coordinate_weights(&map_challenges, rho_j))
        .collect();
    drop(span);

    // 3. The combined target: the ring claims' under their maps, then the point claims' under their powers.
    let target = (s_hat_vs.iter().zip(&maps))
        .map(|(s_hat_v, map)| ring_switch::sumcheck_claim(s_hat_v, map))
        .sum::<F128>()
        + point_claims
            .iter()
            .zip(lambdas_pd)
            .map(|(claim, &lambda)| lambda * claim.value())
            .sum();

    // Level 0's fold rounds run on the weight's terms and projections of lanes onto them, so the
    // lifted weight over the stack is never built.
    let (points, scales) = flatten(point_claims, lambdas_pd);
    let initial_basis = tracing::info_span!("Basis")
        .in_scope(|| basis::initial_basis(&stack, log_n, lane_vars, &points, &scales, ring, &maps));

    // 4. One WHIR over the full stack against the combined claim, the prover taking the stack.
    super::whir::recursive_prover_with_prepared_basis(config, log_n, stack, initial_basis, target, prover_data, ps);
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    use crate::tensor_algebra::DEGREE_E;
    use crate::whir::{Dense, FoldChallenges};
    use crate::whir_lanes::LaneRounds;

    /// The level-0 rounds on a projected basis must send the tables of the dense rounds on the transposed stack and
    /// dense weight, and leave the same lane and weight, across claims inside
    /// one lane and spanning lanes, strides above the lane bit, shared and distinct points, one over the whole stack
    /// past its lanes, a q_keccak ring both spanning lanes and selected by lane bits, and a ring piece whose bit-slices
    /// are given, over a stack with runs of equal blocks.
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
            // Sixteen blocks a lane: the claims' sums run eight blocks at a time.
            (14, 3, 15),
            // Sixty-four blocks a lane: runs of equal blocks cross the projection's sweeps and the lane fold's tasks.
            (16, 3, 17),
        ] {
            let lane_block = 1usize << lane_vars;
            let mut stack: Vec<F64> = (0..lanes_count * lane_block).map(|_| F64(rng.next_u64())).collect();
            // Runs of equal blocks across lane boundaries and the lane fold's tasks, changing in some lanes only.
            let block = 1usize << basis::LOW_VARS;
            for b in (1..stack.len() / block).filter(|&b| b % 5 != 0 && b % 7 != 3) {
                stack.copy_within((b - 1) * block..b * block, b * block);
            }
            let qkeccak_len = 1usize << qkeccak_vars;
            for offset in [0, qkeccak_len] {
                if offset + qkeccak_len > stack.len() {
                    continue;
                }
                // Two claims on q_keccak, and one of two scaled pieces: q_keccak and a sub-block below it.
                let mut ring = RingSwitchOpen {
                    claims: (0..2)
                        .map(|_| RingSwitchClaim::single(offset, rng.ext_vec(qkeccak_vars), None))
                        .collect(),
                };
                let other = (offset + qkeccak_len) % stack.len();
                ring.claims.push(RingSwitchClaim {
                    pieces: vec![
                        RingPiece {
                            offset,
                            point: rng.ext_vec(qkeccak_vars),
                            scale: rng.ext(),
                            slices: None,
                        },
                        RingPiece {
                            offset: other - other % 64,
                            point: rng.ext_vec(6),
                            scale: rng.ext(),
                            slices: None,
                        },
                    ],
                    s_hat_v: None,
                });
                // The small piece's bit-slices given, as the link gives a pointer piece's: the first round takes its
                // lane's projection from them.
                let small = &mut ring.claims[2].pieces[1];
                let eq = primitives::multilinear::eq_table(&small.point);
                let mut slices = vec![F128::ZERO; 64];
                for (y, e) in eq.into_iter().enumerate() {
                    let word = stack[small.offset + y].0;
                    for (i, s) in slices.iter_mut().enumerate() {
                        if word >> i & 1 == 1 {
                            *s += e;
                        }
                    }
                }
                small.slices = Some(slices);
                let coordinates: [F128; DEGREE_E] = std::array::from_fn(|_| rng.ext());
                let maps: Vec<[F128; DEGREE_E]> = (ring.claims.iter())
                    .map(|_| {
                        let scale = rng.ext();
                        coordinates.map(|c| scale * c)
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
                    .map(|(offset, vars, point)| StackClaim::Point {
                        offset,
                        low_point: point.unwrap_or_else(|| rng.ext_vec(vars)),
                        value: rng.ext(),
                    })
                    .collect();
                let lambdas = rng.ext_vec(claims.len());

                // Oracle: the dense weight written out naively, one eq entry at a time.
                let mut dense = vec![F128::ZERO; lane_block << LANE_ROUNDS];
                for (claim, map) in ring.claims.iter().zip(&maps) {
                    for piece in &claim.pieces {
                        let eq = primitives::multilinear::eq_table(&piece.point);
                        for (y, e) in eq.into_iter().enumerate() {
                            dense[piece.offset + y] += ring_switch::apply(map, piece.scale * e);
                        }
                    }
                }
                for (claim, &lambda) in claims.iter().zip(&lambdas) {
                    let StackClaim::Point { offset, low_point, .. } = claim else {
                        unreachable!("the test makes no sums")
                    };
                    for (y, e) in primitives::multilinear::eq_table(low_point).into_iter().enumerate() {
                        dense[offset + y] += lambda * e;
                    }
                }

                let projected = basis::initial_basis(
                    &stack,
                    lane_vars + LANE_ROUNDS,
                    lane_vars,
                    &claims,
                    &lambdas,
                    &ring,
                    &maps,
                );
                let mut lanes = LaneRounds::new(stack.clone(), projected, lane_block, false);
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
                let (p, w, _) = lanes.finish();
                assert_eq!(p, reference.f, "{context}, lane");
                assert_eq!(w, reference.w, "{context}, weight");
            }
        }
    }
}
