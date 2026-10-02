// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Stacked batch-mixed opening for the F64-committed PCS.
//!
//! The committed witness is a stack of `2^log_n` [`F64`] words (committed via
//! [`super::whir::commit`], which only encodes and only transmits the lane blocks
//! that carry data: every claim lives inside them and the weight is zero past
//! them), and one WHIR run discharges
//!
//! - **point claims** ([`StackClaim`]): multilinear evaluations whose weight is a
//!   sum of aligned [`Term`]s, each `scale · eq(point[..n_vars], j)` at the words
//!   `offset + slot + j · 2^stride_log`. One term over a whole aligned slice is a
//!   plain evaluation of that slice (`slot`, `stride_log` freeze the low in-block
//!   coords of a packed column); several scaled terms are a column whose rows are
//!   committed in several aligned pieces (a jagged column, §sec:jagged), the scales
//!   being what the claim's point puts on each piece,
//! - **ring-switched claims** ([`RingSwitchClaim`]): bit-MLE evaluation claims on
//!   a packed column, its weight the sum of its [`RingTerm`]s `scale · eq(point[..n_vars], ·)`
//!   over aligned pieces of the stack, reduced per claim by
//!   [`super::ring_switch::prove_prepare`] and the deferred finish path to an
//!   inner-product claim `<q, rs_eq_ind> = sumcheck_claim` against the transparent
//!   E-valued weight `rs_eq_ind = Φ(weight)`.
//!
//! All claims are lambda-folded into ONE combined weight `b_stack` over the
//! whole stack plus one `target`, then proved by
//! [`super::whir::recursive_prover_with_basis`]. The verifier replays
//! the ring-switch reductions succinctly ([`super::ring_switch::verify_finish`],
//! with no dense `rs_eq_ind`) and drives
//! [`super::whir::recursive_verifier_with_basis_succinct`] with a
//! terminal evaluator that reconstructs `MLE(b_stack)` once, at the final fold
//! point, using closed-form eq / stride selectors and
//! [`super::ring_switch::eval_rs_eq_terms`].
//!
//! ## Transcript order (identical on both sides)
//!
//! Sample the shared linear map, then one batching challenge for both claim families, then run WHIR. The caller already bound each claim's slices and value through the transcript, so none is observed again here.
//!
//! ## The combined weight
//!
//! A term over `2^n` words at `offset` has selector coords `sel = offset >> n`, and
//! at a full-stack point `x = (x_lo, x_hi)` (split at `n`, LSB-first) it is its
//! low-dimensional weight at `x_lo` times `eq(sel, x_hi)`. So
//!
//! ```text
//! b(x) = sum_i lambda^i * sum_{t in ring claim i} eq(sel_t, x_hi) * MLE(Φ(scale_t · eq(point_i[..n_t], ·)))(x_lo)
//!      + sum_j lambda^(n_rs + j) * sum_{t in claim j} scale_t * eq(sel_t, x_hi) * eq(point_j-term, x_lo)
//! ```
//!
//! which is exactly what the dense `b_stack` scatter produces (each term's
//! weight lives on its aligned slice, so scattering the low-dimensional eq /
//! rs_eq_ind tensor at the slice offset IS multiplying by the boolean
//! selector eq).
//!
//! Both families take DISJOINT power ranges of ONE challenge, as the table
//! sumcheck's xi ranges do, so every claim carries a distinct power (the
//! batching step of `thm:rbr`). A claim's terms share its power.

use crate::merkle::Hash;
use fiat_shamir::transcript::{Receiver, Transmitter};
use primitives::field::{F64, F192, powers};
use primitives::multilinear::eq_eval;

use super::pack::PACKING_WIDTH;
use super::ring_switch;
use super::whir::{ProverConfig, VerifierConfig, VerifyError};
use super::whir::{ProverData, recursive_verifier_with_basis_succinct};

mod basis;

// ---------------------------------------------------------------------------
// Claim types
// ---------------------------------------------------------------------------

/// One aligned piece of a [`StackClaim`]'s weight: `scale · eq(point[..n_vars], j)`
/// at the word `offset + slot + j · 2^stride_log` for every `j < 2^n_vars`, the
/// claim fixing `point`, `slot` and `stride_log`. `offset` must be a multiple of
/// `2^(stride_log + n_vars)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term {
    pub offset: usize,
    pub n_vars: usize,
    pub scale: F192,
}

impl Term {
    /// `scale · eq(sel, x[n..])` for the term's selector `sel = offset >> n`, the
    /// share of its weight the coords above its own `n` contribute at `x`.
    fn selector_at(&self, n: usize, x: &[F192]) -> F192 {
        let sel = self.offset >> n;
        x[n..].iter().enumerate().fold(self.scale, |e, (k, &xi)| {
            e * if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi }
        })
    }
}

/// An owning point claim folded into the stacked mixed opening: the stack against
/// the sum of its terms' weights is `value`. The low `stride_log` in-block coords
/// of every term are frozen to `slot`'s bits, which is how a claim reads one port
/// of a packed column; `slot < 2^stride_log`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackClaim {
    pub point: Vec<F192>,
    pub slot: usize,
    pub stride_log: usize,
    pub terms: Vec<Term>,
    pub value: F192,
}

impl StackClaim {
    /// `eq(low_point, ·)` on the aligned slice `[offset, offset + 2^|low_point|)`.
    pub fn point(offset: usize, low_point: Vec<F192>, value: F192) -> Self {
        Self::strided(offset, 0, 0, low_point, value)
    }

    /// `eq(point, j)` at `offset + slot + j · 2^stride_log`: a [`Self::point`] whose
    /// low `stride_log` coords are `slot`'s bits, folded in `O(2^|point|)`.
    pub fn strided(offset: usize, slot: usize, stride_log: usize, point: Vec<F192>, value: F192) -> Self {
        Self {
            terms: vec![Term {
                offset,
                n_vars: point.len(),
                scale: F192::ONE,
            }],
            point,
            slot,
            stride_log,
            value,
        }
    }

    /// The b_stack range term `t` is supported on: an aligned dyadic interval, so
    /// two of them are nested or disjoint and never partially overlap. It is the
    /// whole strided block rather than the strided positions inside it, which is
    /// conservative in the direction that matters: it only ever makes a later
    /// claim accumulate.
    const fn range(&self, t: &Term) -> (usize, usize) {
        (t.offset, t.offset + (1usize << (self.stride_log + t.n_vars)))
    }

    /// The claim's weight at an arbitrary point `x` of the full stack cube, every
    /// term's full point being `[slot_bits, point[..n_vars], sel_bits]`.
    fn weight_at(&self, x: &[F192]) -> F192 {
        let s = self.stride_log;
        let slot = (0..s).fold(F192::ONE, |e, k| {
            e * if (self.slot >> k) & 1 == 1 {
                x[k]
            } else {
                F192::ONE + x[k]
            }
        });
        let terms = self.terms.iter().fold(F192::ZERO, |acc, t| {
            acc + eq_eval(&self.point[..t.n_vars], &x[s..s + t.n_vars]) * t.selector_at(s + t.n_vars, x)
        });
        slot * terms
    }
}

/// One aligned piece of a ring-switched claim's weight: `scale · eq(suffix_point[..n_vars], ·)`
/// over the `2^n_vars` words from `offset`, which must be a multiple of that.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingTerm {
    pub offset: usize,
    pub n_vars: usize,
    pub scale: F192,
}

/// One ring-switched claim: the 64 bit-slice MLEs of the stack against the weight
/// `Σ_terms` (see [`super::ring_switch`]); one unscaled term over a packed slice
/// is that slice's bit-slice MLEs at `suffix_point`.
///
/// `s_hat_v` holds those 64 values. The caller transmits and checks them itself
/// (flock sends its family and pins it in its own lincheck terminal), so this
/// layer only binds them to the commitment. `None` asks the prover to fold the slices from the witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchClaim {
    pub suffix_point: Vec<F192>,
    pub s_hat_v: Option<Vec<F192>>,
    pub terms: Vec<RingTerm>,
}

/// A verifier claim whose slices were transmitted and checked by the caller.
#[derive(Clone, Debug)]
pub struct RingSwitchVerifyClaim<'a> {
    pub suffix_point: &'a [F192],
    pub s_hat_v: &'a [F192; PACKING_WIDTH],
    pub terms: Vec<RingTerm>,
}

/// One unscaled ring term over the aligned slice `[offset, offset + 2^n_vars)`.
pub fn whole_slice(offset: usize, n_vars: usize) -> Vec<RingTerm> {
    vec![RingTerm {
        offset,
        n_vars,
        scale: F192::ONE,
    }]
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Open the committed `F64` stack: discharge every `point_claims` weighted
/// evaluation AND the ring-switched claims (`rings`) in ONE WHIR
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
    rings: &[RingSwitchClaim],
) {
    for term in rings.iter().flat_map(|claim| &claim.terms) {
        assert!(
            term.offset.is_multiple_of(1usize << term.n_vars),
            "a ring term must be aligned to its size"
        );
    }
    assert!(
        point_claims
            .iter()
            .all(|c| c.terms.iter().all(|t| c.range(t).1 <= stack.len())),
        "every claim must live inside the committed lanes"
    );
    let n_rs = rings.len();
    assert!(n_rs > 0, "stacked PCS opening carries at least one ring-switched claim");
    let span = tracing::info_span!("Ring switch").entered();

    // 1. Ring-switch reduction: prepare every claim's s_hat_v (the caller bound
    //    them upstream), then sample one shared linear map.
    let mut rs_states = Vec::with_capacity(n_rs);
    for claim in rings {
        rs_states.push(ring_switch::prove_prepare(
            stack,
            &claim.suffix_point,
            &claim.terms,
            claim.s_hat_v.as_deref(),
        ));
    }
    let map_challenges = ring_switch::sample_map_challenges(ps);
    let coordinate_weights = ring_switch::build_coordinate_weights(&map_challenges);

    // 2. The ONE batching challenge both families take disjoint power ranges of. Nothing is
    //    observed first: every claim value reached the caller through a binding stream read, so
    //    the challenge already depends on all of them (`leanvm_core::pcs::open`).
    let lambdas = powers(ps.sample(), n_rs + point_claims.len());
    let (lambdas_rs, lambdas_pd) = lambdas.split_at(n_rs);

    let rs_outputs: Vec<_> = rs_states
        .into_iter()
        .zip(lambdas_rs.iter().copied())
        .map(|(state, lambda)| ring_switch::prove_finish_deferred(state, &coordinate_weights, lambda))
        .collect();
    drop(span);

    // 3. Combined target and lifted stack weight b_stack: the lambda-weighted
    //    rs_eq_ind terms scattered at their slices, plus the point-claim
    //    eq tensors scattered at their offsets.
    let target = rs_outputs
        .iter()
        .fold(F192::ZERO, |acc, out| acc + out.batched_sumcheck_claim)
        + point_claims
            .iter()
            .zip(lambdas_pd)
            .fold(F192::ZERO, |sum, (claim, &lambda)| sum + lambda * claim.value);

    // The lifted weight is never stored.
    //
    //     round 0:       each chunk is filled, then feeds the message while hot
    //     lane round 1:  each chunk is filled again, then folded
    //
    // Filling costs less than writing the weight out and reading it back.
    let lane_block = 1usize << (log_n - config.initial_k());
    let weight = basis::StackWeight::new(stack.len(), lane_block, point_claims, lambdas_pd, &rs_outputs);
    let fill = |start: usize, dst: &mut [F192]| weight.fill(start, dst);
    let message = tracing::info_span!("Basis").in_scope(|| super::whir::initial_message(stack, lane_block, &fill));

    // 4. One WHIR over the full stack against the combined claim (the
    //    stack is borrowed by the prover; no copy).
    super::whir::recursive_prover_with_prepared_basis(
        config,
        log_n,
        stack,
        super::whir::Basis::Virtual(&fill),
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
    rings: &[RingSwitchVerifyClaim<'_>],
) -> Result<(), VerifyError> {
    let n_rs = rings.len();
    assert!(n_rs > 0, "stacked PCS opening carries at least one ring-switched claim");
    // Caller (statement) invariants: panic on misuse, like the extension-field layer.
    // Every term's support must lie inside the cube, or its selector coords would run
    // off the end of the fold point (mirror of the opener's own bound).
    for claim in rings {
        for term in &claim.terms {
            assert!(term.n_vars <= claim.suffix_point.len());
            assert!(
                term.offset.is_multiple_of(1usize << term.n_vars),
                "a ring term must be aligned to its size"
            );
            assert!(term.offset + (1usize << term.n_vars) <= 1usize << log_n);
        }
    }
    for claim in point_claims {
        for term in &claim.terms {
            assert!(term.n_vars <= claim.point.len());
            let (start, end) = claim.range(term);
            assert!(start.is_multiple_of(end - start), "a term must be aligned to its size");
            assert!(
                end <= 1usize << log_n,
                "every claim must live inside the committed cube"
            );
        }
    }

    // 1. Ring-switch verify: every claim arrives with its 64 slices, bound
    //    upstream by the caller, so nothing is read here. Then sample one
    //    shared map.
    let map_challenges = ring_switch::sample_map_challenges(vs);
    let coordinate_weights = ring_switch::build_coordinate_weights(&map_challenges);

    // 2. The one batching challenge (see the opener: the caller already bound the claim values),
    //    then fold both families into the target over disjoint power ranges.
    let lambdas = powers(vs.sample(), n_rs + point_claims.len());
    let (lambdas_rs, lambdas_pd) = lambdas.split_at(n_rs);

    let mut target = F192::ZERO;
    for (claim, g) in rings.iter().zip(lambdas_rs.iter()) {
        target += *g * ring_switch::verify_finish(claim.s_hat_v, &coordinate_weights);
    }
    for (claim, g) in point_claims.iter().zip(lambdas_pd.iter()) {
        target += *g * claim.value;
    }

    // Ring claims whose suffix points are prefixes of one longest point share its walk:
    // `eval_rs_eq_terms` serves every prefix of the point it walks, so each walk takes
    // the terms of every claim it covers.
    let mut walks: Vec<(usize, Vec<usize>)> = Vec::new();
    let mut by_length: Vec<usize> = (0..n_rs).collect();
    by_length.sort_by_key(|&i| std::cmp::Reverse(rings[i].suffix_point.len()));
    for i in by_length {
        let point = rings[i].suffix_point;
        match walks
            .iter_mut()
            .find(|(lead, _)| rings[*lead].suffix_point.starts_with(point))
        {
            Some((_, members)) => members.push(i),
            None => walks.push((i, vec![i])),
        }
    }

    // 3. Evaluate the lifted weight once, at the terminal sumcheck point.
    let eval_b_at = |x: &[F192]| -> F192 {
        let mut acc = F192::ZERO;
        for (lead, members) in &walks {
            let shape: Vec<(usize, F192)> = (members.iter())
                .flat_map(|&i| rings[i].terms.iter().map(|t| (t.n_vars, t.scale)))
                .collect();
            let mut values =
                ring_switch::eval_rs_eq_terms(rings[*lead].suffix_point, x, &coordinate_weights, &shape).into_iter();
            for &i in members {
                let rs_part = rings[i]
                    .terms
                    .iter()
                    .zip(values.by_ref())
                    .fold(F192::ZERO, |acc, (t, value)| {
                        let selector = Term {
                            offset: t.offset,
                            n_vars: t.n_vars,
                            scale: F192::ONE,
                        }
                        .selector_at(t.n_vars, x);
                        acc + value * selector
                    });
                acc += lambdas_rs[i] * rs_part;
            }
        }
        for (claim, g) in point_claims.iter().zip(lambdas_pd.iter()) {
            acc += *g * claim.weight_at(x);
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
    use crate::whir::{INITIAL_BASIS_CHUNK, commit, default_config, inner_product_base_ext};
    use crate::whir_config::test_config_for;
    use primitives::multilinear::eq_table;
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
            // A whole-slice ring claim, and one whose weight is split into two scaled
            // pieces at the slice's two ends, as a jagged column's is.
            let rings = [
                whole_slice(offset, qflock_vars),
                vec![
                    RingTerm {
                        offset,
                        n_vars: qflock_vars - 1,
                        scale: rng.ext(),
                    },
                    RingTerm {
                        offset: offset + qflock_len - 1,
                        n_vars: 0,
                        scale: rng.ext(),
                    },
                ],
            ]
            .map(|terms| RingSwitchClaim {
                suffix_point: rng.ext_vec(qflock_vars),
                s_hat_v: None,
                terms,
            });
            let coordinates = rng.ext_vec(192);
            let rs_outputs: Vec<_> = rings
                .iter()
                .map(|claim| {
                    let state = ring_switch::prove_prepare(&stack, &claim.suffix_point, &claim.terms, None);
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
            .map(|(offset, vars)| StackClaim::point(offset, rng.ext_vec(vars), rng.ext()))
            .collect();
            for stride_log in [0, 1, 3, qflock_vars - 1, qflock_vars] {
                claims.push(StackClaim::strided(
                    offset,
                    (1 << stride_log) - 1,
                    stride_log,
                    rng.ext_vec(qflock_vars - stride_log),
                    rng.ext(),
                ));
            }
            let mut jagged = StackClaim::point(offset, rng.ext_vec(qflock_vars), rng.ext());
            jagged.terms = vec![
                Term {
                    offset,
                    n_vars: qflock_vars - 1,
                    scale: rng.ext(),
                },
                Term {
                    offset: offset + qflock_len - 1,
                    n_vars: 0,
                    scale: rng.ext(),
                },
            ];
            claims.push(jagged);
            let lambdas = rng.ext_vec(claims.len());
            // Oracle: the dense weight written out naively, one eq entry at a
            // time, so it shares no code with the fused build under test.
            let mut expected = vec![F192::ZERO; stack.len()];
            ring_switch::combine_deferred_chunk(&rs_outputs, 0, &mut expected);
            for (claim, &lambda) in claims.iter().zip(&lambdas) {
                for term in &claim.terms {
                    let point = &claim.point[..term.n_vars];
                    for j in 0..1usize << point.len() {
                        let w = point.iter().enumerate().fold(lambda * term.scale, |w, (i, &p_i)| {
                            w * if (j >> i) & 1 == 1 { p_i } else { F192::ONE + p_i }
                        });
                        expected[term.offset + claim.slot + (j << claim.stride_log)] += w;
                    }
                }
            }
            // The weight, filled chunk by chunk as the opening reads it.
            let weight = basis::StackWeight::new(stack.len(), lane_block, &claims, &lambdas, &rs_outputs);
            let chunk = lane_block.min(INITIAL_BASIS_CHUNK);
            let mut actual = vec![F192::ZERO; stack.len()];
            for (i, out) in actual.chunks_exact_mut(chunk).enumerate() {
                weight.fill(i * chunk, out);
            }
            assert_eq!(actual, expected, "lane_vars={lane_vars}, lanes={lanes}");
            let message =
                super::super::whir::initial_message(&stack, lane_block, &|start, dst| weight.fill(start, dst));
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
        ring_verify: Vec<RingSwitchClaim>,
        fs: fiat_shamir::transcript::Proof,
    }

    /// The 64 bit-slice values of a ring claim's terms against the stack.
    fn slices_of(stack: &[F64], claim: &RingSwitchClaim) -> Vec<F192> {
        claim.terms.iter().fold(vec![F192::ZERO; PACKING_WIDTH], |mut acc, t| {
            let eq: Vec<F192> = eq_table(&claim.suffix_point[..t.n_vars])
                .iter()
                .map(|&e| t.scale * e)
                .collect();
            let slices = fold_1b_rows(&stack[t.offset..t.offset + (1 << t.n_vars)], &eq);
            for (a, s) in acc.iter_mut().zip(slices) {
                *a += s;
            }
            acc
        })
    }

    /// Synthetic stack of 2^14 F64 words: three aligned 2^12-word columns
    /// plus a q_flock region (a random bit-witness packed by pack) at the
    /// top slice, padded with random filler. Pool: one point claim per
    /// column at a random E point, one strided claim into q_flock, one
    /// claim split into two scaled terms (a jagged column's shape), one
    /// ring-switched claim with plain eq prefix weights and one split likewise.
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
                let eq = eq_table(&low_point);
                let value = inner_product_base_ext(&stack[offset..offset + col_len], &eq);
                StackClaim::point(offset, low_point, value)
            })
            .collect();

        // One strided claim into the q_flock region: freeze the low 3 in-block
        // coords to slot 5, eq over the remaining coords of the slice.
        {
            let stride_log = 3usize;
            let slot = 5usize;
            let point = rng.ext_vec(qflock_vars - stride_log);
            let eq = eq_table(&point);
            let mut value = F192::ZERO;
            for (j, &ej) in eq.iter().enumerate() {
                value += ej.mul_base(stack[qflock_offset + slot + (j << stride_log)]);
            }
            point_claims.push(StackClaim::strided(qflock_offset, slot, stride_log, point, value));
        }

        // One claim of two scaled pieces: the low half of column 1 and one word of
        // column 2.
        {
            let point = rng.ext_vec(col_vars);
            let (a, b) = (rng.ext(), rng.ext());
            let eq = eq_table(&point[..col_vars - 1]);
            let value = a * inner_product_base_ext(&stack[col_len..col_len + col_len / 2], &eq)
                + b.mul_base(stack[2 * col_len + 7]);
            let mut claim = StackClaim::point(col_len, point, value);
            claim.terms = vec![
                Term {
                    offset: col_len,
                    n_vars: col_vars - 1,
                    scale: a,
                },
                Term {
                    offset: 2 * col_len + 7,
                    n_vars: 0,
                    scale: b,
                },
            ];
            point_claims.push(claim);
        }

        // One ring-switched claim on q_flock (plain eq prefix weights), and one
        // of two scaled pieces of it; then, on the filler past it, one whose point
        // is a prefix of theirs, which shares their walk, and one whose point is not.
        let suffix_point = rng.ext_vec(qflock_vars);
        let split = vec![
            RingTerm {
                offset: qflock_offset,
                n_vars: qflock_vars - 2,
                scale: rng.ext(),
            },
            RingTerm {
                offset: qflock_offset + (1 << qflock_vars) - 2,
                n_vars: 1,
                scale: rng.ext(),
            },
        ];
        let past = qflock_offset + (1 << qflock_vars);
        let rings: Vec<RingSwitchClaim> = [
            (suffix_point.clone(), whole_slice(qflock_offset, qflock_vars)),
            (suffix_point.clone(), split),
            (
                suffix_point[..qflock_vars - 1].to_vec(),
                whole_slice(past, qflock_vars - 1),
            ),
            (
                rng.ext_vec(qflock_vars - 2),
                whole_slice(past + (1 << (qflock_vars - 1)), qflock_vars - 2),
            ),
        ]
        .into_iter()
        .map(|(suffix_point, terms)| RingSwitchClaim {
            suffix_point,
            // Exercise the fold path (no precompute).
            s_hat_v: None,
            terms,
        })
        .collect();
        // The verifier's copy of the same claims: the slices ride the statement,
        // bound by the caller, as flock binds its family.
        let ring_verify = rings
            .iter()
            .map(|claim| RingSwitchClaim {
                s_hat_v: Some(slices_of(&stack, claim)),
                ..claim.clone()
            })
            .collect();

        let pc = test_config_for(log_n);
        // Pin the intended residual regime: the residual cube must sit
        // entirely above the q_flock coords, with at least one selector coord
        // covered by ris (the E-valued sel prefix) and the rest by y bits.
        let yr_log_n = log_n - pc.initial_k() - pc.level_ks().iter().sum::<usize>();
        assert!(
            qflock_vars < log_n - yr_log_n,
            "test shape must keep the residual cube above q_flock (yr_log_n = {yr_log_n})"
        );
        let (cm, pd) = commit(&stack, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
        let mut ps = fiat_shamir::transcript::ProverState::from_label(DOMAIN);
        open_batch_mixed_whir_stacked(&mut ps, log_n, &stack, &pd, &pc, &point_claims, &rings);

        Instance {
            vc: pc,
            log_n,
            root: cm.root,
            point_claims,
            ring_verify,
            fs: ps.into_proof(),
        }
    }

    fn verifier_claims(claims: &[RingSwitchClaim]) -> Vec<RingSwitchVerifyClaim<'_>> {
        claims
            .iter()
            .map(|claim| RingSwitchVerifyClaim {
                suffix_point: &claim.suffix_point,
                s_hat_v: claim.s_hat_v.as_deref().unwrap().try_into().unwrap(),
                terms: claim.terms.clone(),
            })
            .collect()
    }

    fn verify_instance(
        inst: &Instance,
        point_claims: &[StackClaim],
        ring_claims: &[RingSwitchClaim],
        fs: &fiat_shamir::transcript::Proof,
    ) -> bool {
        let mut vs = fiat_shamir::transcript::VerifierState::from_label(DOMAIN, fs);
        verify_opening_batch_mixed_whir_stacked(
            &mut vs,
            &inst.vc,
            inst.log_n,
            1 << inst.vc.initial_k(),
            &inst.root,
            point_claims,
            &verifier_claims(ring_claims),
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

        // Wrong values: a dense column claim, a strided one, a two-piece one.
        for (c, what) in [(0, "Point"), (3, "Strided"), (4, "split")] {
            let mut bad_points = inst.point_claims.clone();
            bad_points[c].value += F192::ONE;
            assert!(
                !verify_instance(&inst, &bad_points, &inst.ring_verify, &inst.fs),
                "tampered {what} value accepted"
            );
        }

        // A piece's scale is part of the statement: moving weight between pieces is caught.
        let mut bad_points = inst.point_claims.clone();
        bad_points[4].terms[1].scale += F192::ONE;
        assert!(
            !verify_instance(&inst, &bad_points, &inst.ring_verify, &inst.fs),
            "rescaled piece accepted"
        );

        // Wrong ring-switched slices: rejected by the ring-switch binding. A wrong
        // point is rejected by the weight, shared walk or not.
        for r in 0..inst.ring_verify.len() {
            let mut bad_ring = inst.ring_verify.clone();
            bad_ring[r].s_hat_v.as_mut().unwrap()[7] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
                "tampered ring-switch slice {r} accepted"
            );
            let mut bad_ring = inst.ring_verify.clone();
            bad_ring[r].suffix_point[0] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
                "moved ring-switch point {r} accepted"
            );
        }

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
        let eq = eq_table(&low_point);
        let value = inner_product_base_ext(&stack[..1 << 12], &eq);
        let point_claims = vec![StackClaim::point(0, low_point, value)];

        // One ring-switched claim on the wide q_flock.
        let qflock = &stack[qflock_offset..];
        let suffix_point = rng.ext_vec(qflock_vars);
        let s_hat_v = fold_1b_rows(qflock, &eq_table(&suffix_point));
        let claims = vec![RingSwitchClaim {
            suffix_point,
            // Exercise the precomputed path (transcript must be identical).
            s_hat_v: Some(s_hat_v),
            terms: whole_slice(qflock_offset, qflock_vars),
        }];

        // Fixed fallback config so the residual cube size is known: the
        // crossing regime needs qflock_vars > log_n - yr_log_n.
        let pc = default_config(log_n, 5, 1).unwrap();
        let yr_log_n = log_n - pc.initial_k() - pc.level_ks().iter().sum::<usize>();
        assert!(
            qflock_vars > log_n - yr_log_n,
            "test shape must exercise the crossing regime (yr_log_n = {yr_log_n})"
        );

        let (cm, pd) = commit(&stack, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
        let mut ps = fiat_shamir::transcript::ProverState::from_label(DOMAIN);
        open_batch_mixed_whir_stacked(&mut ps, log_n, &stack, &pd, &pc, &point_claims, &claims);
        let fs = ps.into_proof();

        let mut vs = fiat_shamir::transcript::VerifierState::from_label(DOMAIN, &fs);
        assert!(
            verify_opening_batch_mixed_whir_stacked(
                &mut vs,
                &pc,
                log_n,
                1 << pc.initial_k(),
                &cm.root,
                &point_claims,
                &verifier_claims(&claims)
            )
            .is_ok(),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip a slice.
        let mut bad_claims = claims.clone();
        bad_claims[0].s_hat_v.as_mut().unwrap()[7] += F192::ONE;
        let mut vs = fiat_shamir::transcript::VerifierState::from_label(DOMAIN, &fs);
        assert!(
            verify_opening_batch_mixed_whir_stacked(
                &mut vs,
                &pc,
                log_n,
                1 << pc.initial_k(),
                &cm.root,
                &point_claims,
                &verifier_claims(&bad_claims)
            )
            .is_err(),
            "tampered crossing-regime ring slice accepted"
        );
    }
}
