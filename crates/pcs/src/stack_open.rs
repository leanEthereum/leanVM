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
//! - **ring-switched claims** ([`RingSwitchClaim`]): bit-MLE evaluation claims
//!   on packed slices of the stack (flock's `q_flock`, the one-hot address bits),
//!   reduced per claim by [`super::ring_switch::prove_prepare`] and the
//!   deferred finish path to an inner-product
//!   claim `<stack, rs_eq_ind> = sumcheck_claim` against the transparent
//!   E-valued weight `rs_eq_ind`, supported on the claim's parts.
//!
//! All claims are lambda-folded into ONE combined weight `b_stack` over the
//! whole stack plus one `target`, then proved by
//! [`super::whir::recursive_prover_with_basis`]. The verifier replays
//! the ring-switch reductions succinctly ([`super::ring_switch::verify_finish`],
//! with no dense `rs_eq_ind`) and drives
//! [`super::whir::recursive_verifier_with_basis_succinct`] with a
//! terminal evaluator that reconstructs `MLE(b_stack)` once, at the final fold
//! point, using closed-form eq / stride selectors and
//! [`super::ring_switch::eval_weight`].
//!
//! ## Transcript order (identical on both sides)
//!
//! Sample the shared linear map, then one batching challenge for both claim families, then run WHIR. The caller already bound each claim's slices and value through the transcript, so none is observed again here.
//!
//! ## The combined weight
//!
//! Part `p` of ring-switched claim `i` sits at the selector coords
//! `sel_p = offset_p >> |z_p|`, so the lifted weight at a full-stack point `x`,
//! split per part into `(x_lo, x_hi)` at `|z_p|` (LSB-first), is
//!
//! ```text
//! b(x) = sum_i lambda^i * sum_p eq(sel_p, x_hi) * MLE(Phi(scale_p * eq(z_p, .)))(x_lo)
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

use crate::merkle::Hash;
use fiat_shamir::transcript::{Receiver, Transmitter};
use primitives::field::{F64, F192, powers};
use primitives::multilinear::eq_eval;

use super::pack::PACKING_WIDTH;
use super::ring_switch;
pub use super::ring_switch::RingSwitchPart;
use super::whir::{ProverConfig, VerifierConfig, VerifyError};
use super::whir::{ProverData, recursive_verifier_with_basis_succinct};

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

/// One ring-switched claim: the 64 slices `s_hat_v[i] = sum_y bit_i(stack[y]) * W(y)`
/// of the weight `W = sum_p scale_p * eq(z_p, .)` its `parts` span (see
/// [`super::ring_switch`]).
///
/// The caller transmits and checks the slices itself (flock sends its family and
/// pins it in its own lincheck terminal), so this layer only binds them to the
/// commitment. `None` asks the prover to fold them from the witness; a verifier
/// always holds them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchClaim {
    pub parts: Vec<RingSwitchPart>,
    pub s_hat_v: Option<Vec<F192>>,
}

/// The ring-switched claims discharged in the same stacked opening as the
/// [`StackClaim`]s, the same statement on both sides.
#[derive(Clone, Debug, Default)]
pub struct RingSwitchOpen {
    pub claims: Vec<RingSwitchClaim>,
}

// ---------------------------------------------------------------------------
// Shared claim folding / evaluation
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

/// The claim's weight `eq(full claim point, x)` at an arbitrary point `x` of
/// the full stack cube. A `Point`'s full point is `[low_point, sel_bits]`, a
/// `Strided`'s is `[slot_bits, point, sel_bits]`; neither is materialized.
fn stack_claim_eq_at(claim: &StackClaim, x: &[F192]) -> F192 {
    match claim {
        StackClaim::Point { offset, low_point, .. } => {
            let n = low_point.len();
            let mut e = eq_eval(low_point, &x[..n]);
            let sel = offset >> n;
            for (k, &xi) in x[n..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            e
        }
        StackClaim::Strided {
            offset,
            slot,
            stride_log,
            point,
            ..
        } => {
            let mut e = F192::ONE;
            for (k, &xi) in x[..*stride_log].iter().enumerate() {
                e *= if (slot >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            let block_vars = stride_log + point.len();
            e *= eq_eval(point, &x[*stride_log..block_vars]);
            let sel = offset >> block_vars;
            for (k, &xi) in x[block_vars..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            e
        }
    }
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Open the committed `F64` stack: discharge every `point_claims` slice
/// evaluation AND the ring-switched q_flock claims (`ring`) in ONE WHIR
/// run, reusing the caller's [`super::whir::commit`] output as L0.
///
/// `stack` is the committed message (the caller retains it; it is not stored in
/// [`ProverData`]): the `2^log_n`-word stack truncated to the lane blocks that
/// carry data, so every claim must live inside it and the padding past it is
/// exactly the weight's zero region. `config.initial_k` / `config.log_inv_rates[0]`
/// must match the commit's `log_batch_size` / `log_inv_rate` (enforced by shape
/// asserts inside the WHIR prover).
pub fn open_batch_mixed_whir_stacked(
    ps: &mut impl Transmitter,
    log_n: usize,
    stack: &[F64],
    prover_data: &ProverData,
    config: &ProverConfig,
    point_claims: &[StackClaim],
    ring: &RingSwitchOpen,
) {
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
    let rs_states: Vec<_> = ring
        .claims
        .iter()
        .map(|claim| ring_switch::prove_prepare(stack, &claim.parts, claim.s_hat_v.as_deref()))
        .collect();
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
    //    rs_eq_ind sum scattered at the q_flock slice, plus the point-claim
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
        .in_scope(|| basis::build(stack, lane_block, point_claims, lambdas_pd, &rs_outputs));

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
// Verifier
// ---------------------------------------------------------------------------

/// Verifier mirror of [`open_batch_mixed_whir_stacked`]: replay the
/// ring-switch reductions succinctly, recompute the combined target, then
/// drive the succinct WHIR verifier with one terminal evaluation of the
/// lifted weight. `log_n` is the committed stack's log size in F64 words and
/// `root` the L0 commitment root ([`super::whir::Commitment::root`]).
pub fn verify_opening_batch_mixed_whir_stacked(
    vs: &mut impl Receiver,
    config: &VerifierConfig,
    log_n: usize,
    n_lanes: usize,
    root: &Hash,
    point_claims: &[StackClaim],
    ring: &RingSwitchOpen,
) -> Result<(), VerifyError> {
    let n_rs = ring.claims.len();
    // Caller (statement) invariants: panic on misuse, like the extension-field layer.
    assert!(n_rs > 0, "stacked PCS opening carries at least one ring-switched claim");
    // Every claim's support must lie inside the cube, or its selector coords would
    // run off the end of the fold point (mirror of the opener's own bound).
    for part in ring.claims.iter().flat_map(|claim| &claim.parts) {
        let len = 1usize << part.suffix_point.len();
        assert!(part.offset.is_multiple_of(len), "a part must be an aligned slice");
        assert!(part.offset + len <= 1usize << log_n);
    }
    fn slices(claim: &RingSwitchClaim) -> &[F192] {
        let s_hat_v = claim.s_hat_v.as_deref().expect("a verifier holds every claim's slices");
        assert_eq!(s_hat_v.len(), PACKING_WIDTH);
        s_hat_v
    }
    assert!(
        point_claims.iter().all(|c| claim_range(c).1 <= 1usize << log_n),
        "every claim must live inside the committed cube"
    );

    // 1. Ring-switch verify: every claim arrives with its 64 slices, bound
    //    upstream by the caller, so nothing is read here. Then sample one
    //    shared map.
    let map_challenges = ring_switch::sample_map_challenges(vs);
    let coordinate_weights = ring_switch::build_coordinate_weights(&map_challenges);
    let coefficients = ring_switch::frobenius_coefficients(&map_challenges);

    // 2. The one batching challenge (see the opener: the caller already bound the claim values),
    //    then fold both families into the target over disjoint power ranges.
    let lambdas = powers(vs.sample(), n_rs + point_claims.len());
    let (lambdas_rs, lambdas_pd) = lambdas.split_at(n_rs);

    let mut target = F192::ZERO;
    for (claim, g) in ring.claims.iter().zip(lambdas_rs.iter()) {
        target += *g * ring_switch::verify_finish(slices(claim), &coordinate_weights);
    }
    for (claim, g) in point_claims.iter().zip(lambdas_pd.iter()) {
        target += *g * claim.value();
    }

    // 3. Evaluate the lifted weight once, at the terminal sumcheck point.
    let eval_b_at = |x: &[F192]| -> F192 {
        let mut acc = F192::ZERO;
        for (claim, g) in ring.claims.iter().zip(lambdas_rs.iter()) {
            let mut rs_part = F192::ZERO;
            for part in &claim.parts {
                let (x_lo, x_hi) = x.split_at(part.suffix_point.len());
                let sel = part.offset >> x_lo.len();
                let mut sel_eq = F192::ONE;
                for (k, &xi) in x_hi.iter().enumerate() {
                    sel_eq *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
                }
                rs_part += sel_eq * ring_switch::eval_weight(&part.suffix_point, x_lo, part.scale, &coefficients);
            }
            acc += *g * rs_part;
        }
        for (claim, g) in point_claims.iter().zip(lambdas_pd.iter()) {
            acc += *g * stack_claim_eq_at(claim, x);
        }
        acc
    };

    recursive_verifier_with_basis_succinct(config, log_n, n_lanes, target, root, eval_b_at, vs)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring_switch::fold_1b_rows;
    use crate::whir::{build_eq_table_ext, commit, default_config, inner_product_base_ext};
    use crate::whir_config::test_config_for;
    use primitives::test_rng::Rng;

    const DOMAIN: &[u8] = b"stack-open-test";

    #[test]
    fn fused_basis_matches_dense_weights() {
        let mut rng = Rng::new(0xBA515);
        for (lane_vars, lanes) in [(6usize, 1usize), (6, 3), (10, 15), (10, 37)] {
            let lane_block = 1 << lane_vars;
            let stack: Vec<F64> = (0..lanes * lane_block).map(|_| F64(rng.next_u64())).collect();
            let qflock_vars = lane_vars + usize::from(lanes > 1);
            let qflock_len = 1 << qflock_vars;
            let offset = if stack.len() >= 2 * qflock_len { qflock_len } else { 0 };
            // Two claims on the q_flock slice, the second also reading a scaled
            // part of its own elsewhere in the stack.
            let mut ring = RingSwitchOpen {
                claims: (0..2)
                    .map(|_| RingSwitchClaim {
                        parts: vec![RingSwitchPart {
                            offset,
                            suffix_point: rng.ext_vec(qflock_vars),
                            scale: F192::ONE,
                        }],
                        s_hat_v: None,
                    })
                    .collect(),
            };
            ring.claims[1].parts.push(RingSwitchPart {
                offset: (lanes - 1) * lane_block,
                suffix_point: rng.ext_vec(lane_vars),
                scale: rng.ext(),
            });
            let coordinates = rng.ext_vec(192);
            let rs_outputs: Vec<_> = ring
                .claims
                .iter()
                .map(|claim| {
                    let state = ring_switch::prove_prepare(&stack, &claim.parts, None);
                    ring_switch::prove_finish_deferred(state, &coordinates, rng.ext())
                })
                .collect();
            let mut claims: Vec<_> = [
                (offset, qflock_vars),
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
            for stride_log in [0, 1, 3, qflock_vars - 1, qflock_vars] {
                claims.push(StackClaim::Strided {
                    offset,
                    slot: (1 << stride_log) - 1,
                    stride_log,
                    point: rng.ext_vec(qflock_vars - stride_log),
                    value: rng.ext(),
                });
            }
            let lambdas = rng.ext_vec(claims.len());
            // Oracle: the dense weight written out naively, one eq entry at a
            // time, so it shares no code with the fused build under test.
            let mut expected = vec![F192::ZERO; stack.len()];
            ring_switch::combine_deferred_chunk(&rs_outputs, 0, &mut expected);
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
            let (actual, message) = basis::build(&stack, lane_block, &claims, &lambdas, &rs_outputs);
            assert_eq!(&*actual, expected, "lane_vars={lane_vars}, lanes={lanes}");
            let (_, expected_message) = super::super::whir::build_initial_basis(&stack, lane_block, |start, dst| {
                dst.copy_from_slice(&expected[start..start + dst.len()]);
            });
            assert_eq!(message, expected_message);
        }
    }

    struct Instance {
        vc: VerifierConfig,
        log_n: usize,
        root: Hash,
        point_claims: Vec<StackClaim>,
        ring_verify: RingSwitchOpen,
        fs: fiat_shamir::transcript::Proof,
    }

    /// Synthetic stack of 2^14 F64 words: three aligned 2^12-word columns
    /// plus a q_flock region (a random bit-witness packed by pack) at the
    /// top slice, padded with random filler. Pool: one point claim per
    /// column at a random E point, one strided claim into q_flock, one
    /// ring-switched claim with plain eq prefix weights.
    ///
    /// q_flock is kept SMALL (2^8 words) so the succinct verifier's residual
    /// cube sits entirely above the q_flock coords (the production regime:
    /// shared tensor prefix folded once, y coords all selector-indicator,
    /// nonempty E-valued selector prefix from ris); the crossing regime is
    /// exercised by `stacked_open_residual_crosses_qflock`.
    fn build_instance(seed: u64) -> Instance {
        let log_n = 14usize;
        let col_vars = 12usize;
        let col_len = 1usize << col_vars;
        let qflock_vars = 8usize;
        let qflock_offset = 3 * col_len;
        let mut rng = Rng::new(seed);

        // Three random columns, the packed bit-witness region, then filler.
        let mut stack: Vec<F64> = (0..3 * col_len).map(|_| F64(rng.next_u64())).collect();
        stack.extend((0..1usize << qflock_vars).map(|_| F64(rng.next_u64())));
        while stack.len() < 1 << log_n {
            stack.push(F64(rng.next_u64()));
        }
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim per column, at a random E point.
        let mut point_claims: Vec<StackClaim> = (0..3)
            .map(|c| {
                let offset = c * col_len;
                let low_point = rng.ext_vec(col_vars);
                let eq = build_eq_table_ext(&low_point);
                let value = inner_product_base_ext(&stack[offset..offset + col_len], &eq);
                StackClaim::Point {
                    offset,
                    low_point,
                    value,
                }
            })
            .collect();

        // One strided claim into the q_flock region: freeze the low 3 in-block
        // coords to slot 5, eq over the remaining coords of the slice.
        {
            let stride_log = 3usize;
            let slot = 5usize;
            let point = rng.ext_vec(qflock_vars - stride_log);
            let eq = build_eq_table_ext(&point);
            let mut value = F192::ZERO;
            for (j, &ej) in eq.iter().enumerate() {
                value += ej.mul_base(stack[qflock_offset + slot + (j << stride_log)]);
            }
            point_claims.push(StackClaim::Strided {
                offset: qflock_offset,
                slot,
                stride_log,
                point,
                value,
            });
        }

        // One ring-switched claim on q_flock (plain eq prefix weights), and one
        // over two scaled parts: the first two columns read as packed bits.
        let whole = |offset: usize, vars: usize, rng: &mut Rng| RingSwitchPart {
            offset,
            suffix_point: rng.ext_vec(vars),
            scale: rng.ext(),
        };
        let parts = [
            vec![RingSwitchPart {
                scale: F192::ONE,
                ..whole(qflock_offset, qflock_vars, &mut rng)
            }],
            vec![whole(0, col_vars, &mut rng), whole(col_len, col_vars, &mut rng)],
        ];
        let slices = |parts: &[RingSwitchPart]| {
            let mut s_hat_v = vec![F192::ZERO; PACKING_WIDTH];
            for part in parts {
                let eq: Vec<F192> = build_eq_table_ext(&part.suffix_point)
                    .iter()
                    .map(|&e| part.scale * e)
                    .collect();
                let slice = &stack[part.offset..part.offset + eq.len()];
                for (acc, v) in s_hat_v.iter_mut().zip(fold_1b_rows(slice, &eq)) {
                    *acc += v;
                }
            }
            s_hat_v
        };
        // The opener folds the first claim's slices itself and is handed the second's.
        let ring = RingSwitchOpen {
            claims: vec![
                RingSwitchClaim {
                    parts: parts[0].clone(),
                    s_hat_v: None,
                },
                RingSwitchClaim {
                    parts: parts[1].clone(),
                    s_hat_v: Some(slices(&parts[1])),
                },
            ],
        };
        // The verifier's copy of the same claims: the slices ride the statement,
        // bound by the caller, as flock binds its family.
        let ring_verify = RingSwitchOpen {
            claims: parts
                .iter()
                .map(|parts| RingSwitchClaim {
                    parts: parts.clone(),
                    s_hat_v: Some(slices(parts)),
                })
                .collect(),
        };

        let pc = test_config_for(log_n);
        // Pin the intended residual regime: the residual cube must sit
        // entirely above the q_flock coords, with at least one selector coord
        // covered by ris (the E-valued sel prefix) and the rest by y bits.
        let yr_log_n = log_n - pc.initial_k - pc.level_ks.iter().sum::<usize>();
        assert!(
            qflock_vars < log_n - yr_log_n,
            "test shape must keep the residual cube above q_flock (yr_log_n = {yr_log_n})"
        );
        let (cm, pd) = commit(&stack, log_n, pc.initial_k, pc.log_inv_rates[0]);
        let mut ps = fiat_shamir::transcript::ProverState::from_label(DOMAIN);
        open_batch_mixed_whir_stacked(&mut ps, log_n, &stack, &pd, &pc, &point_claims, &ring);

        Instance {
            vc: pc,
            log_n,
            root: cm.root,
            point_claims,
            ring_verify,
            fs: ps.into_proof(),
        }
    }

    fn verify_instance(
        inst: &Instance,
        point_claims: &[StackClaim],
        ring: &RingSwitchOpen,
        fs: &fiat_shamir::transcript::Proof,
    ) -> bool {
        let mut vs = fiat_shamir::transcript::VerifierState::from_label(DOMAIN, fs);
        verify_opening_batch_mixed_whir_stacked(
            &mut vs,
            &inst.vc,
            inst.log_n,
            1 << inst.vc.initial_k,
            &inst.root,
            point_claims,
            ring,
        )
        .is_ok()
    }

    #[test]
    fn stacked_open_roundtrip_and_tampering() {
        let inst = build_instance(1);
        assert!(
            verify_instance(&inst, &inst.point_claims, &inst.ring_verify, &inst.fs),
            "honest stacked opening rejected"
        );

        // Wrong point-claim value (dense column claim).
        let mut bad_points = inst.point_claims.clone();
        if let StackClaim::Point { value, .. } = &mut bad_points[0] {
            *value += F192::ONE;
        } else {
            unreachable!()
        }
        assert!(
            !verify_instance(&inst, &bad_points, &inst.ring_verify, &inst.fs),
            "tampered Point value accepted"
        );

        // Wrong strided-claim value.
        let mut bad_points = inst.point_claims.clone();
        if let StackClaim::Strided { value, .. } = &mut bad_points[3] {
            *value += F192::ONE;
        } else {
            unreachable!()
        }
        assert!(
            !verify_instance(&inst, &bad_points, &inst.ring_verify, &inst.fs),
            "tampered Strided value accepted"
        );

        // Wrong ring-switched slice, or a wrong scale on a part: rejected by the
        // ring-switch binding.
        for claim in 0..2 {
            let mut bad_ring = inst.ring_verify.clone();
            bad_ring.claims[claim].s_hat_v.as_mut().unwrap()[7] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
                "tampered ring-switch slice accepted"
            );
        }
        let mut bad_ring = inst.ring_verify.clone();
        bad_ring.claims[1].parts[1].scale += F192::ONE;
        assert!(
            !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
            "tampered part scale accepted"
        );

        // Every scalar the opening sends rides the stream, all of them WHIR's:
        // tampering any of them must be rejected.
        for idx in [17usize, inst.fs.stream.len() - 1] {
            let mut bad_fs = inst.fs.clone();
            bad_fs.stream[idx] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &inst.ring_verify, &bad_fs),
                "tampered stream word {idx} accepted"
            );
        }

        // Shape tamper: a truncated stream must return false, not panic.
        let mut short_fs = inst.fs.clone();
        short_fs.stream.pop();
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.ring_verify, &short_fs),
            "short stream accepted"
        );
    }

    /// Residual cube crossing INTO the q_flock slice (case split = n_ris in the
    /// verifier closure): q_flock occupies half a 2^14 stack (qflock_vars = 13),
    /// and the fallback config's residual cube (yr_log_n = 3) is wider than
    /// the single selector coordinate, so some q_flock coords are covered by
    /// binary y bits and the tensor finish runs with a nonempty suffix.
    #[test]
    fn stacked_open_residual_crosses_qflock() {
        let log_n = 14usize;
        let qflock_vars = 13usize;
        let qflock_offset = 1usize << 13;
        let mut rng = Rng::new(3);

        let mut stack: Vec<F64> = (0..1usize << 13).map(|_| F64(rng.next_u64())).collect();
        stack.extend((0..1usize << qflock_vars).map(|_| F64(rng.next_u64())));
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim on the low column.
        let low_point = rng.ext_vec(12);
        let eq = build_eq_table_ext(&low_point);
        let value = inner_product_base_ext(&stack[..1 << 12], &eq);
        let point_claims = vec![StackClaim::Point {
            offset: 0,
            low_point,
            value,
        }];

        // One ring-switched claim on the wide q_flock.
        let qflock = &stack[qflock_offset..];
        let suffix_point = rng.ext_vec(qflock_vars);
        let s_hat_v = fold_1b_rows(qflock, &build_eq_table_ext(&suffix_point));
        let mut ring = RingSwitchOpen {
            claims: vec![RingSwitchClaim {
                parts: vec![RingSwitchPart {
                    offset: qflock_offset,
                    suffix_point,
                    scale: F192::ONE,
                }],
                // Exercise the precomputed path (transcript must be identical).
                s_hat_v: Some(s_hat_v.clone()),
            }],
        };

        // Fixed fallback config so the residual cube size is known: the
        // crossing regime needs qflock_vars > log_n - yr_log_n.
        let pc = default_config(log_n, 5, 1).unwrap();
        let yr_log_n = log_n - pc.initial_k - pc.level_ks.iter().sum::<usize>();
        assert!(
            qflock_vars > log_n - yr_log_n,
            "test shape must exercise the crossing regime (yr_log_n = {yr_log_n})"
        );

        let (cm, pd) = commit(&stack, log_n, pc.initial_k, pc.log_inv_rates[0]);
        let mut ps = fiat_shamir::transcript::ProverState::from_label(DOMAIN);
        open_batch_mixed_whir_stacked(&mut ps, log_n, &stack, &pd, &pc, &point_claims, &ring);
        let fs = ps.into_proof();

        let mut vs = fiat_shamir::transcript::VerifierState::from_label(DOMAIN, &fs);
        assert!(
            verify_opening_batch_mixed_whir_stacked(
                &mut vs,
                &pc,
                log_n,
                1 << pc.initial_k,
                &cm.root,
                &point_claims,
                &ring
            )
            .is_ok(),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip a slice.
        ring.claims[0].s_hat_v.as_mut().unwrap()[7] += F192::ONE;
        let mut vs = fiat_shamir::transcript::VerifierState::from_label(DOMAIN, &fs);
        assert!(
            verify_opening_batch_mixed_whir_stacked(
                &mut vs,
                &pc,
                log_n,
                1 << pc.initial_k,
                &cm.root,
                &point_claims,
                &ring
            )
            .is_err(),
            "tampered crossing-regime ring slice accepted"
        );
    }
}
