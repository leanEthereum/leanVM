use std::fmt::Debug;
use std::ops::{Add, Mul};

use backend::*;

use crate::{AirSumcheckSession, OuterSumcheckSession};

// ---------------------------------------------------------------------------
// Front-loaded batched orchestration (see plan_spec.md "Protocol spec")
//
// All tables join at round 0. A table with `n_t` variables is embedded in the
// `n_max`-variable combined sum as a function of its FIRST `n_t` variables,
// constant in the trailing `n_max − n_t` ones, so its claim `s_t` enters the
// combined target with the static weight `w_t = 2^{n_max − n_t}`:
//
//     target₀ = Σ_t w_t · s_t .
//
// Round 0 is the univariate skip: ONE combined coefficient vector
// P(X) = Σ_t w_t · v'_t(X) of degree ≤ (2^K − 1)·d_max is sent IN FULL — the
// verifier's round-0 identity is the weighted window sum
//
//     Σ_{z ∈ D} ê(z) · P(z) == Σ_t w_t · s_t ,
//
// not `h(0) + h(1) = target`, so no coefficient can be elided (this full-vector
// convention is the executable spec mirrored by the python verifier and the
// recursion circuit). The next target is ê(r0) · P(r0).
//
// Linear rounds r = 0 .. n_max − K − 1 then bind one variable each with the
// legacy `h(0) + h(1) = target` identity (c0 elided, reconstructed by the
// verifier):
//   • ACTIVE table (r < n_t − K): contributes w_t · eq-expanded bare poly,
//     exactly the legacy per-round mechanism.
//   • FINISHED table (r ≥ n_t − K): its remaining function is the constant
//     c_t = session.sum() over the m = n_max − K − r unbound variables; its
//     round polynomial is the constant c_t · 2^{m−1} (folded into coeffs[0]),
//     since h(0) + h(1) = c_t · 2^m matches its target share, which halves
//     each round and ends at exactly c_t. Hence the final combined value is
//
//     target_final = Σ_t s_t^final           (NO challenge products),
//
// with s_t^final = ê(r0) · eq(eq_factor_t[..n_t−K], natural_prefix_t) ·
// C_t(col_evals_t) and natural_prefix_t = reverse(linear_challenges[..n_t−K]).
// ---------------------------------------------------------------------------

/// The univariate-skip analogue of the batched AIR sumcheck point: the skip
/// challenge `r0` (binding the K lowest row bits of every table), the Lagrange
/// window weights `L_x(r0)` (the tensor tail of the WHIR opening weights), and
/// the linear-round challenges in round order.
#[derive(Debug, Clone)]
pub struct UniskipAirPoint<EF> {
    pub r0: EF,
    /// `L_x(r0)` for `x ∈ 0..2^K`, in row-bit (window-node) order.
    pub lagrange_weights: Vec<EF>,
    /// Challenges of the linear rounds, in round order (round r binds, for each
    /// table still active, its highest remaining row bit).
    pub linear_challenges: Vec<EF>,
}

impl<EF> UniskipAirPoint<EF> {
    pub fn k(&self) -> usize {
        log2_strict_usize(self.lagrange_weights.len())
    }
}

/// The "natural ordering" opening point of a table's remaining (non-skipped)
/// variables: the reverse of the first `log_n_rows − K` linear challenges
/// (round r binds eq coordinate `n_t − K − 1 − r`, so index-wise pairing with
/// `eq_factor_t[..n_t − K]` requires the reversed prefix).
pub fn natural_prefix_for_session<EF: Copy>(point: &UniskipAirPoint<EF>, log_n_rows: usize) -> Vec<EF> {
    point.linear_challenges[..log_n_rows - point.k()]
        .iter()
        .rev()
        .copied()
        .collect()
}

/// Front-loaded batched AIR sumcheck with a univariate skip round.
/// `sessions` must all be fresh (`rounds_done == 0`) and share the same last-`k`
/// eq coordinates (suffixes of one gkr point). Returns the binding point.
pub fn prove_batched_air_sumcheck_uniskip<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    sessions: &mut [Box<dyn SkipSession<EF> + 'a>],
    k: usize,
) -> UniskipAirPoint<EF> {
    let n_max = sessions.iter().map(|s| s.initial_n_vars()).max().unwrap();
    let max_full_degree = sessions.iter().map(|s| s.bare_degree() + 1).max().unwrap();
    let d_max = sessions.iter().map(|s| s.bare_degree()).max().unwrap();
    let n_skip_coeffs = ((1usize << k) - 1) * d_max + 1;

    let weights: Vec<EF> = sessions
        .iter()
        .map(|s| EF::from_usize(1 << (n_max - s.initial_n_vars())))
        .collect();

    // The skipped eq coordinates are shared: every session's eq factor is a
    // suffix of the same gkr point.
    let eq_top = sessions[0].skip_eq_top(k);
    for s in sessions.iter().skip(1) {
        debug_assert_eq!(s.skip_eq_top(k), eq_top, "sessions must share the skip eq coordinates");
    }

    // Round 0 (skip): combined polynomial P = Σ_t w_t · v'_t, full coefficients.
    let skip_polys: Vec<DensePolynomial<EF>> = sessions.iter_mut().map(|s| s.compute_skip_poly(k)).collect();
    let mut combined_skip = EF::zero_vec(n_skip_coeffs);
    for (poly, &w_t) in skip_polys.iter().zip(&weights) {
        debug_assert!(poly.coeffs.len() <= n_skip_coeffs);
        for (acc, &c) in combined_skip.iter_mut().zip(&poly.coeffs) {
            *acc += w_t * c;
        }
    }
    prover_state.add_extension_scalars(&combined_skip);
    let r0: EF = prover_state.sample();

    let lagrange_weights = lagrange_weights_at::<PF<EF>, EF>(k, r0);
    let e_hat_r0 = e_hat_at(&eq_top, r0);
    for (session, poly) in sessions.iter_mut().zip(&skip_polys) {
        session.process_skip_challenge(k, r0, &lagrange_weights, e_hat_r0, poly);
    }

    // Invariant: the next target is ê(r0)·P(r0) = Σ_t w_t · session.sum().
    let mut running_target = e_hat_r0 * DensePolynomial::new(combined_skip).evaluate(r0);
    debug_assert_eq!(
        running_target,
        sessions
            .iter()
            .zip(&weights)
            .map(|(s, &w)| w * s.sum())
            .fold(EF::ZERO, |a, b| a + b)
    );

    // Linear rounds.
    let n_linear = n_max - k;
    let mut linear_challenges = Vec::with_capacity(n_linear);
    for r in 0..n_linear {
        let mut combined_coeffs = EF::zero_vec(max_full_degree + 1);
        let mut bare_polys: Vec<Option<DensePolynomial<EF>>> = vec![None; sessions.len()];

        for (idx, session) in sessions.iter_mut().enumerate() {
            let n_own = session.initial_n_vars() - k;
            if r < n_own {
                let bare = session.compute_bare_round_poly();
                let full = expand_bare_to_full(&bare.coeffs, session.eq_alpha());
                for (acc, &c) in combined_coeffs.iter_mut().zip(&full) {
                    *acc += weights[idx] * c;
                }
                bare_polys[idx] = Some(bare);
            } else {
                // Finished: constant c_t over the m = n_linear − r remaining
                // variables; round poly = c_t · 2^{m−1} (constant in X).
                combined_coeffs[0] += session.sum() * EF::from_usize(1 << (n_linear - r - 1));
            }
        }

        // h(0) + h(1) = 2·c0 + Σ_{i≥1} c_i must equal the running target.
        debug_assert_eq!(
            combined_coeffs[0].double() + combined_coeffs[1..].iter().copied().sum::<EF>(),
            running_target,
            "front-loading bookkeeping broke at linear round {r}"
        );

        prover_state.add_sumcheck_polynomial(&combined_coeffs, None);
        let challenge = prover_state.sample();
        linear_challenges.push(challenge);

        for (idx, session) in sessions.iter_mut().enumerate() {
            if let Some(bare) = &bare_polys[idx] {
                session.process_challenge(challenge, bare);
            }
        }
        running_target = DensePolynomial::new(combined_coeffs).evaluate(challenge);
    }

    UniskipAirPoint {
        r0,
        lagrange_weights,
        linear_challenges,
    }
}

/// Verifier half of [`prove_batched_air_sumcheck_uniskip`]. Table arrays are in
/// session order; `table_sums` are the per-table claims `s_t`; `eq_top` is the
/// shared last-`k` slice of the gkr point; `table_degrees` are the bare AIR
/// degrees (`Air::degree`), `max_full_degree = max(degree_air) + 1`.
/// Returns the binding point and the final sumcheck target (the caller checks
/// it against `Σ_t ê(r0) · eq(eq_factor_t[..n_t−k], natural_prefix_t) · C_t`).
#[allow(clippy::too_many_arguments)]
pub fn verify_batched_air_sumcheck_uniskip<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    k: usize,
    table_n_vars: &[usize],
    table_degrees: &[usize],
    table_sums: &[EF],
    eq_top: &[EF],
    max_full_degree: usize,
) -> Result<(UniskipAirPoint<EF>, EF), ProofError> {
    assert_eq!(table_n_vars.len(), table_sums.len());
    assert_eq!(table_n_vars.len(), table_degrees.len());
    assert_eq!(eq_top.len(), k);
    let n_max = *table_n_vars.iter().max().unwrap();
    let d_max = *table_degrees.iter().max().unwrap();
    let n_skip_coeffs = ((1usize << k) - 1) * d_max + 1;

    let coeffs = verifier_state.next_extension_scalars_vec(n_skip_coeffs)?;
    let skip_poly = DensePolynomial::new(coeffs);

    // Round-0 identity: Σ_{z ∈ D} ê(z) · P(z) == Σ_t w_t · s_t.
    let e_hat_window = e_hat_on_window(eq_top);
    let window_sum = (0..1usize << k)
        .map(|z| e_hat_window[z] * skip_poly.evaluate(EF::from_usize(z)))
        .fold(EF::ZERO, |a, b| a + b);
    let claimed: EF = table_n_vars
        .iter()
        .zip(table_sums)
        .map(|(&n_t, &s_t)| EF::from_usize(1 << (n_max - n_t)) * s_t)
        .fold(EF::ZERO, |a, b| a + b);
    if window_sum != claimed {
        return Err(ProofError::InvalidProof);
    }

    let r0: EF = verifier_state.sample();
    let target = e_hat_at(eq_top, r0) * skip_poly.evaluate(r0);

    let Evaluation { point, value } = sumcheck_verify(verifier_state, n_max - k, max_full_degree, target, None)?;

    Ok((
        UniskipAirPoint {
            r0,
            lagrange_weights: lagrange_weights_at::<PF<EF>, EF>(k, r0),
            linear_challenges: point.0,
        },
        value,
    ))
}

// Univariate skip round for the batched AIR sumcheck (Gruen, eprint 2024/108 §5-6).
//
// The first `K` sumcheck rounds — which bind the K lowest row-index bits of every
// table — are replaced by ONE univariate round over the integer window
// D = {0, …, 2^K − 1} (see `backend::univariate_skip` for the domain convention:
// the window node for cube point `x` is the integer `x` itself, in row-bit order,
// so the committed column values at the 2^K rows of a block ARE the polynomial
// values on the window).
//
// Per session (table) the prover computes
//
//   v'_t(z) = Σ_{rest} eqᵣ(rest) · C_t( c̃ols(z, rest) )  +  padding term,
//
// where `c̃ols(z, ·)` is the degree-(2^K − 1) univariate extension of the 2^K
// window values of each column, and eqᵣ is the eq weight over the remaining
// n_t − K variables (the LAST K entries of the session's `eq_factor` are
// excluded — they form the kernel ê known to the verifier:
// ê(z) interpolates eq(eq_factor[n−K..], bits(x)) over the window).
//
// All constraint evaluations stay in the BASE field (packed SIMD): the window
// values are committed base-field data and the extended-target values are
// base-field Lagrange combinations of them. This replaces rounds 1..K−1 of the
// legacy schedule, whose folded columns are extension-field (~5× the packed
// base-field throughput on this workload).
//
// Identities (see plan_spec.md):
//   round 0:   Σ_{z ∈ D} ê(z) · v'_t(z) == s_t        (the session's claim)
//   challenge: sum ← ê(r0) · v'_t(r0),  missing_mul_factor ← ê(r0)
// after which the session state is EXACTLY what K legacy rounds would have
// produced (same storage layout, same eq bookkeeping), so the remaining rounds
// run unchanged.
//
// Storage mapping (chunk-bit-reversed columns, see air_sumcheck.rs:10-32):
// rounds 0..K−1 fold storage bits [pivot−K, pivot) inside each 2^pivot chunk,
// so the window value for cube point `x` of rest-position `j = (chunk, o)`
// lives at storage block `bitreverse_K(x)` of that chunk:
//   storage_index(x, j) = (chunk << pivot) | (rev_K(x) << (pivot−K)) | o.
// Collapsing the K block bits (in any z-combination) preserves the legacy
// post-round-K layout: chunks of size 2^{pivot−K} in the same `o` order.

/// Compile-time skip width. The kernels below take `k` as a runtime parameter
/// (so tests can sweep 3..=5); the orchestration layer (T3) uses this constant.
pub const UNIVARIATE_SKIP_K: usize = 4;
pub const SKIP_DOMAIN: usize = 1 << UNIVARIATE_SKIP_K;

/// Storage block (within a 2^pivot chunk) holding the window values of cube
/// point `x`: the K-bit bit-reversal of `x`.
#[inline]
pub const fn skip_block_of_x(x: usize, k: usize) -> usize {
    let mut b = 0;
    let mut i = 0;
    while i < k {
        b |= ((x >> i) & 1) << (k - 1 - i);
        i += 1;
    }
    b
}

pub trait SkipSession<EF: ExtensionField<PF<EF>>>: OuterSumcheckSession<EF> {
    /// The univariate restriction `v'_t` of the session's claim to the skip
    /// window (eq over the REST variables only; excludes ê), in coefficient
    /// form. Requires a fresh session (`rounds_done == 0`).
    fn compute_skip_poly(&mut self, k: usize) -> DensePolynomial<EF> {
        self.compute_skip_poly_forced(k, false)
    }

    /// Test/bench hook: `force_lagrange = true` selects the reference
    /// Lagrange-dot extension kernels instead of the default finite-difference
    /// ones. Both produce bit-identical polynomials (exact field arithmetic);
    /// the toggle exists so the equality tests and the h4 timing gate can
    /// compare them. Not part of the protocol surface.
    #[doc(hidden)]
    fn compute_skip_poly_forced(&mut self, k: usize, force_lagrange: bool) -> DensePolynomial<EF>;

    /// Bind the K skipped variables to `r0`: fold every column `2^k → 1` with
    /// the Lagrange weights `L_x(r0)`, and fast-forward the session state to
    /// `rounds_done = k` (sum, eq factor, missing_mul_factor, padding count).
    fn process_skip_challenge(
        &mut self,
        k: usize,
        r0: EF,
        lagrange_at_r0: &[EF],
        e_hat_r0: EF,
        skip_poly: &DensePolynomial<EF>,
    );

    /// The eq coordinates carried by the skipped variables (shared ê input):
    /// the last `k` entries of the session's eq factor, in `eval_eq` bit order
    /// (entry 0 ↔ the MSB of the cube point / window index).
    fn skip_eq_top(&self, k: usize) -> Vec<EF>;
}

impl<'a, EF, A> SkipSession<EF> for AirSumcheckSession<'a, EF, A>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + Debug + 'static,
    A::ExtraData: AlphaPowers<EF> + AlphaPowersMut<EF> + Debug,
{
    fn compute_skip_poly_forced(&mut self, k: usize, force_lagrange: bool) -> DensePolynomial<EF> {
        assert_eq!(self.rounds_done, 0, "skip round must come first");
        assert_eq!(self.missing_mul_factor, EF::ONE);
        let n = self.initial_n_vars;
        let w = packing_log_width::<EF>();
        let pivot = self.pivot();
        assert!(k >= 1 && k < n && k <= pivot);
        // current_unpadded_len is chunk-aligned at round 0, so whole blocks are
        // either fully active or fully padding.
        assert_eq!(self.current_unpadded_len % (1 << pivot.min(n)), 0);

        let degree = self.computation.degree();
        let nodes = skip_all_nodes::<PF<EF>>(k, degree);
        let n_nodes = nodes.len();
        let window = 1usize << k;

        // eq weights over the REST variables, in storage order (same machinery
        // as the legacy per-round SplitEq, with the K skipped coordinates and
        // no fold coordinate excluded).
        let rest_alphas = self.permuted_alphas(n - k);
        let split_eq = SplitEq::new(&rest_alphas);

        // Lagrange extension matrix: window -> extended targets (reference
        // path only; the default finite-difference path needs no per-node
        // coefficients — the nodes are consecutive integers).
        let lagrange_targets = if force_lagrange {
            lagrange_coeffs_for_targets::<PF<EF>>(k, &nodes[window..])
        } else {
            Vec::new()
        };

        let active_rest = self.current_unpadded_len >> k;
        let total_rest = 1usize << (n - k);

        let raw: Vec<EF> = if n - k > w {
            let group = self.multilinears.by_ref();
            let cols = group
                .as_packed_base()
                .expect("skip round expects base-packed columns")
                .clone();
            debug_assert!(pivot - k >= w);
            match (self.computation.low_degree_air(), force_lagrange) {
                (Some((low_degree, low_n_constraints)), false) => compute_skip_evals_degree_split::<EF, A>(
                    &cols,
                    &self.computation,
                    &self.extra_data,
                    &split_eq,
                    k,
                    pivot,
                    active_rest >> w,
                    &nodes,
                    low_degree,
                    low_n_constraints,
                ),
                (Some((low_degree, low_n_constraints)), true) => compute_skip_evals_degree_split_lagrange::<EF, A>(
                    &cols,
                    &self.computation,
                    &self.extra_data,
                    &split_eq,
                    k,
                    pivot,
                    active_rest >> w,
                    &nodes,
                    &lagrange_targets,
                    low_degree,
                    low_n_constraints,
                ),
                (None, false) => compute_skip_evals_generic::<EF, A>(
                    &cols,
                    &self.computation,
                    &self.extra_data,
                    &split_eq,
                    k,
                    pivot,
                    active_rest >> w,
                    &nodes,
                ),
                (None, true) => compute_skip_evals_generic_lagrange::<EF, A>(
                    &cols,
                    &self.computation,
                    &self.extra_data,
                    &split_eq,
                    k,
                    pivot,
                    active_rest >> w,
                    &nodes,
                    &lagrange_targets,
                ),
            }
        } else if force_lagrange {
            compute_skip_evals_unpacked_lagrange::<EF, A>(
                &self.multilinears.by_ref(),
                &self.computation,
                &self.extra_data,
                &split_eq,
                k,
                pivot,
                active_rest,
                &nodes,
                &lagrange_targets,
            )
        } else {
            compute_skip_evals_unpacked::<EF, A>(
                &self.multilinears.by_ref(),
                &self.computation,
                &self.extra_data,
                &split_eq,
                k,
                pivot,
                active_rest,
                &nodes,
            )
        };

        // Padding blocks repeat the (constraint-constant) last row, so their
        // contribution is z-independent: C_pad · Σ_{padded rest j} eqᵣ(j).
        let padding_contribution = if active_rest < total_rest {
            self.constraints_eval_at_padding * mle_of_zeros_then_ones(active_rest, &rest_alphas)
        } else {
            EF::ZERO
        };

        let values: Vec<(PF<EF>, EF)> = nodes
            .iter()
            .zip(&raw)
            .map(|(&node, &v)| (node, v + padding_contribution))
            .collect();
        debug_assert_eq!(values.len(), n_nodes);
        DensePolynomial::lagrange_interpolation(&values).unwrap()
    }

    fn process_skip_challenge(
        &mut self,
        k: usize,
        r0: EF,
        lagrange_at_r0: &[EF],
        e_hat_r0: EF,
        skip_poly: &DensePolynomial<EF>,
    ) {
        assert_eq!(self.rounds_done, 0);
        assert_eq!(lagrange_at_r0.len(), 1 << k);
        let n = self.initial_n_vars;
        let w = packing_log_width::<EF>();
        let pivot = self.pivot();

        let xb: Vec<usize> = (0..1 << k).map(|x| skip_block_of_x(x, k)).collect();

        if n - k > w {
            let group = self.multilinears.by_ref();
            let cols = group.as_packed_base().expect("skip round expects base-packed columns");
            let log_block_packed = pivot - k - w;
            let log_chunk_packed = pivot - w;
            let block_mask = (1usize << log_block_packed) - 1;
            let lw_packed: Vec<EFPacking<EF>> = lagrange_at_r0.iter().map(|&l| EFPacking::<EF>::from(l)).collect();

            let mut folded: Vec<ArenaVec<EFPacking<EF>>> = vec![ArenaVec::new(); cols.len()];
            parallel::par_chunks_mut(&mut folded, 1, |c, slot| {
                let src = cols[c];
                let out_len = src.len() >> k;
                let mut out: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(out_len) };
                for j_p in 0..out_len {
                    let chunk = j_p >> log_block_packed;
                    let o = j_p & block_mask;
                    let base = (chunk << log_chunk_packed) | o;
                    let mut acc = lw_packed[0] * src[base | (xb[0] << log_block_packed)];
                    for (x, &lw) in lw_packed.iter().enumerate().skip(1) {
                        acc += lw * src[base | (xb[x] << log_block_packed)];
                    }
                    out[j_p] = acc;
                }
                slot[0] = out;
            });
            self.multilinears = MleGroup::Owned(MleGroupOwned::ExtensionPacked(folded));
        } else {
            let group = self.multilinears.by_ref();
            let unpacked = group.unpack();
            let unpacked_ref = unpacked.by_ref();
            let cols = unpacked_ref.as_base().expect("skip round expects base columns");
            let log_block = pivot - k;
            let log_chunk = pivot;
            let block_mask = (1usize << log_block) - 1;

            let mut folded: Vec<ArenaVec<EF>> = vec![ArenaVec::new(); cols.len()];
            parallel::par_chunks_mut(&mut folded, 1, |c, slot| {
                let src = cols[c];
                let out_len = src.len() >> k;
                let mut out: ArenaVec<EF> = unsafe { ArenaVec::uninitialized(out_len) };
                for j in 0..out_len {
                    let chunk = j >> log_block;
                    let o = j & block_mask;
                    let base = (chunk << log_chunk) | o;
                    let mut acc = lagrange_at_r0[0] * src[base | (xb[0] << log_block)];
                    for (x, &lw) in lagrange_at_r0.iter().enumerate().skip(1) {
                        acc += lw * src[base | (xb[x] << log_block)];
                    }
                    out[j] = acc;
                }
                slot[0] = out;
            });
            self.multilinears = MleGroup::Owned(MleGroupOwned::Extension(folded));
        }

        self.sum = e_hat_r0 * skip_poly.evaluate(r0);
        self.missing_mul_factor = e_hat_r0;
        self.rounds_done = k;
        let new_eq_len = self.eq_factor.len() - k;
        self.eq_factor.truncate(new_eq_len);
        debug_assert_eq!(self.current_unpadded_len % (1 << k), 0);
        self.current_unpadded_len >>= k;

        // Mirror the legacy phase-1 → phase-2 transition: if K legacy rounds
        // would have left packed mode, unpack now.
        if self.multilinears.by_ref().is_packed() && !self.in_phase_1() {
            self.multilinears = self.multilinears.by_ref().unpack().as_owned_or_clone().into();
        }
    }

    fn skip_eq_top(&self, k: usize) -> Vec<EF> {
        self.eq_factor[self.eq_factor.len() - k..].to_vec()
    }
}

// ---------------------------------------------------------------------------
// Finite-difference extension (h4, iteration 2).
//
// All three interpolation sites of the skip kernels — column values
// (degree ≤ 2^k − 1, sampled on the window), the degree-split cached state
// (same degree, same nodes), and the low-part accumulator (degree ≤
// low_degree·(2^k − 1), sampled on the first n_low nodes) — are polynomials
// sampled on CONSECUTIVE integer nodes and evaluated at the remaining
// CONSECUTIVE integer nodes (see `skip_all_nodes`: 0, 1, 2, …). Newton forward
// differences evaluate such a polynomial at each next node with `n_rows − 1`
// field ADDS per value row, replacing the `n_rows` Montgomery MULS of a
// Lagrange-coefficient dot. Field adds are exact, so the results are
// BIT-IDENTICAL to the Lagrange path (same unique polynomial, same field
// elements) — pinned by `test_fd_extension_matches_lagrange` and by the entire
// iter-1 test suite, which the FD path must satisfy unchanged.
//
// State convention (right-edge anchored, verified in `fd_tests`):
//   init:    for j in 1..n_rows { for i in 0..n_rows−j { row_i ← row_{i+1} − row_i } }
//            after which row_{n_rows−1} = value at the LAST sampled node and
//            row_{n_rows−1−j} holds the j-th forward difference Δʲ anchored so
//            one advance yields the next node;
//   advance: for i in 1..n_rows { row_i += row_{i−1} } — the value row at the
//            next consecutive node is then row_{n_rows−1}, readable in place.
// Both passes are forward-sequential over the flattened row-major buffer.
// ---------------------------------------------------------------------------

/// In-place right-edge forward-difference triangle over `n_rows` rows of
/// `width` values (`rows[i * width + c]` = value row at the i-th consecutive
/// node). Cost: width · n_rows(n_rows−1)/2 subs, once per group.
#[inline]
fn fd_init_in_place<T: PrimeCharacteristicRing + Copy>(rows: &mut [T], n_rows: usize, width: usize) {
    debug_assert!(rows.len() >= n_rows * width);
    for j in 1..n_rows {
        for idx in 0..(n_rows - j) * width {
            rows[idx] = rows[idx + width] - rows[idx];
        }
    }
}

/// Advances the FD state one node: `width · (n_rows − 1)` adds. The value row
/// at the new node is `rows[(n_rows − 1) * width ..]`.
#[inline]
fn fd_advance<T: PrimeCharacteristicRing + Copy>(rows: &mut [T], n_rows: usize, width: usize) {
    debug_assert!(rows.len() >= n_rows * width);
    for idx in width..n_rows * width {
        let prev = rows[idx - width];
        rows[idx] += prev;
    }
}

/// Gathers, for one packed rest-position `j_p`, the `2^k` window values of all
/// columns into `win` (layout `win[x * n_cols + c]`, contiguous per window
/// node so constraint evals can borrow `&win[x * n_cols..]` directly).
#[inline(always)]
fn gather_window<T: Copy>(cols: &[&[T]], win: &mut [T], j_p: usize, xb: &[usize], log_block: usize, log_chunk: usize) {
    let n_cols = cols.len();
    let block_mask = (1usize << log_block) - 1;
    let chunk = j_p >> log_block;
    let o = j_p & block_mask;
    let base = (chunk << log_chunk) | o;
    for (c, col) in cols.iter().enumerate() {
        for (x, &b) in xb.iter().enumerate() {
            win[x * n_cols + c] = col[base | (b << log_block)];
        }
    }
}

/// Assembles the column point at extended node `e` (0-based beyond the window):
/// `point[c] = Σ_x L[e][x] · win[x * n_cols + c]`.
#[inline(always)]
fn extend_point<EF: ExtensionField<PF<EF>>>(
    win: &[PFPacking<EF>],
    point: &mut [PFPacking<EF>],
    lag_packed: &[PFPacking<EF>],
    n_cols: usize,
) {
    point[..n_cols].fill(PFPacking::<EF>::ZERO);
    for (x, &lw) in lag_packed.iter().enumerate() {
        let row = &win[x * n_cols..(x + 1) * n_cols];
        for (p, &v) in point[..n_cols].iter_mut().zip(row) {
            *p += v * lw;
        }
    }
}

/// Default generic kernel: finite-difference extension (h4). The gathered
/// window buffer doubles as the FD state after the window evals — zero extra
/// per-thread memory vs the Lagrange path, and the value row at each extended
/// node is read in place as the constraint-eval point.
#[allow(clippy::too_many_arguments)]
fn compute_skip_evals_generic<EF, A>(
    cols: &[&[PFPacking<EF>]],
    computation: &A,
    extra_data: &A::ExtraData,
    split_eq: &SplitEq<EF>,
    k: usize,
    pivot: usize,
    active_packed: usize,
    nodes: &[PF<EF>],
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    let w = packing_log_width::<EF>();
    let n_cols = cols.len();
    let window = 1usize << k;
    let n_nodes = nodes.len();
    let log_block = pivot - k - w;
    let log_chunk = pivot - w;
    let xb: Vec<usize> = (0..window).map(|x| skip_block_of_x(x, k)).collect();

    let acc = parallel::map_reduce_with_state(
        active_packed,
        || vec![PFPacking::<EF>::ZERO; window * n_cols], // win, then FD state
        || vec![EFPacking::<EF>::ZERO; n_nodes],
        |win, acc, j_p| {
            let partial_eq = split_eq.get_packed(j_p);
            gather_window(cols, win, j_p, &xb, log_block, log_chunk);
            for x in 0..window {
                let v = computation.eval_packed_base(&win[x * n_cols..(x + 1) * n_cols], extra_data);
                acc[x] += v * partial_eq;
            }
            fd_init_in_place(win, window, n_cols);
            for node_acc in acc[window..n_nodes].iter_mut() {
                fd_advance(win, window, n_cols);
                let v = computation.eval_packed_base(&win[(window - 1) * n_cols..window * n_cols], extra_data);
                *node_acc += v * partial_eq;
            }
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(b) {
                *x += y;
            }
            a
        },
    );

    acc.into_iter()
        .map(|s| EFPacking::<EF>::to_ext_iter([s]).sum::<EF>())
        .collect()
}

/// Reference generic kernel: Lagrange-coefficient dots (iter-1 path). Kept for
/// the h4 timing gate and the bit-identity test.
#[allow(clippy::too_many_arguments)]
fn compute_skip_evals_generic_lagrange<EF, A>(
    cols: &[&[PFPacking<EF>]],
    computation: &A,
    extra_data: &A::ExtraData,
    split_eq: &SplitEq<EF>,
    k: usize,
    pivot: usize,
    active_packed: usize,
    nodes: &[PF<EF>],
    lagrange_targets: &[Vec<PF<EF>>],
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    let w = packing_log_width::<EF>();
    let n_cols = cols.len();
    let window = 1usize << k;
    let n_nodes = nodes.len();
    let log_block = pivot - k - w;
    let log_chunk = pivot - w;
    let xb: Vec<usize> = (0..window).map(|x| skip_block_of_x(x, k)).collect();
    // Per extended node, the 2^k Lagrange coefficients lifted to packed form.
    let lag_packed: Vec<Vec<PFPacking<EF>>> = lagrange_targets
        .iter()
        .map(|row| row.iter().map(|&l| PFPacking::<EF>::from(l)).collect())
        .collect();

    let acc = parallel::map_reduce_with_state(
        active_packed,
        || {
            (
                vec![PFPacking::<EF>::ZERO; window * n_cols], // win
                vec![PFPacking::<EF>::ZERO; n_cols],          // point
            )
        },
        || vec![EFPacking::<EF>::ZERO; n_nodes],
        |(win, point), acc, j_p| {
            let partial_eq = split_eq.get_packed(j_p);
            gather_window(cols, win, j_p, &xb, log_block, log_chunk);
            for x in 0..window {
                let v = computation.eval_packed_base(&win[x * n_cols..(x + 1) * n_cols], extra_data);
                acc[x] += v * partial_eq;
            }
            for (e, lag) in lag_packed.iter().enumerate() {
                extend_point::<EF>(win, point, lag, n_cols);
                let v = computation.eval_packed_base(point, extra_data);
                acc[window + e] += v * partial_eq;
            }
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(b) {
                *x += y;
            }
            a
        },
    );

    acc.into_iter()
        .map(|s| EFPacking::<EF>::to_ext_iter([s]).sum::<EF>())
        .collect()
}

/// Default degree-split kernel: finite-difference extension (h4) at all three
/// interpolation sites — column values (window FD on `win`, in place), the
/// skipped low-block's cached state (degree ≤ 2^k − 1 in z: affine ops on
/// degree-(2^k − 1) column extensions, so its own window-anchored FD cascade
/// advanced in lockstep), and the low-part accumulator (degree ≤
/// low_degree·(2^k − 1), FD over its first n_low values once captured).
#[allow(clippy::too_many_arguments)]
fn compute_skip_evals_degree_split<EF, A>(
    cols: &[&[PFPacking<EF>]],
    computation: &A,
    extra_data: &A::ExtraData,
    split_eq: &SplitEq<EF>,
    k: usize,
    pivot: usize,
    active_packed: usize,
    nodes: &[PF<EF>],
    low_degree: usize,
    low_n_constraints: usize,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
    EFPacking<EF>: PrimeCharacteristicRing
        + Mul<PFPacking<EF>, Output = EFPacking<EF>>
        + Add<PFPacking<EF>, Output = EFPacking<EF>>,
{
    let w = packing_log_width::<EF>();
    let n_cols = cols.len();
    let n_flat = computation.n_columns();
    let window = 1usize << k;
    let n_nodes = nodes.len();
    let n_low = low_degree * (window - 1) + 1;
    debug_assert!(n_low >= window && n_low <= n_nodes);
    let log_block = pivot - k - w;
    let log_chunk = pivot - w;
    let xb: Vec<usize> = (0..window).map(|x| skip_block_of_x(x, k)).collect();

    let acc = parallel::map_reduce_with_state(
        active_packed,
        || {
            (
                vec![PFPacking::<EF>::ZERO; window * n_cols], // win, then column FD state
                vec![Vec::<PFPacking<EF>>::new(); window],    // captured post-block states
                Vec::<PFPacking<EF>>::new(),                  // s_fd: flattened state FD cascade
                Vec::<PFPacking<EF>>::new(),                  // interpolated-state scratch for the folder
                vec![EFPacking::<EF>::ZERO; n_low],           // low evals
                Vec::<EFPacking<EF>>::new(),                  // low_fd: low-part FD cascade (width 1)
            )
        },
        || vec![EFPacking::<EF>::ZERO; n_nodes],
        |(win, states, s_fd, scratch, low_evals, low_fd), acc, j_p| {
            let partial_eq = split_eq.get_packed(j_p);
            gather_window(cols, win, j_p, &xb, log_block, log_chunk);

            // Full evals at the window nodes; capture the post-block state.
            for x in 0..window {
                let pt = &win[x * n_cols..(x + 1) * n_cols];
                let mut folder = ConstraintFolderPacked::new(&pt[..n_flat], &pt[n_flat..], extra_data);
                folder.cached_state = Some(std::mem::take(&mut states[x]));
                Air::eval(computation, &mut folder, extra_data);
                acc[x] += folder.accumulator * partial_eq;
                low_evals[x] = folder.accumulator_low;
                states[x] = folder.cached_state.unwrap();
            }

            // FD cascades anchored on the window: columns (in place on `win`)
            // and the captured post-block states (advanced in lockstep so the
            // anchoring stays consistent; only read beyond n_low).
            fd_init_in_place(win, window, n_cols);
            let state_len = states[0].len();
            s_fd.clear();
            for st in states.iter() {
                debug_assert_eq!(st.len(), state_len);
                s_fd.extend_from_slice(st);
            }
            fd_init_in_place(s_fd, window, state_len);

            // Full evals at the extended nodes that still determine the low part.
            for z in window..n_low {
                fd_advance(win, window, n_cols);
                fd_advance(s_fd, window, state_len);
                let pt = &win[(window - 1) * n_cols..window * n_cols];
                let mut folder = ConstraintFolderPacked::new(&pt[..n_flat], &pt[n_flat..], extra_data);
                Air::eval(computation, &mut folder, extra_data);
                acc[z] += folder.accumulator * partial_eq;
                low_evals[z] = folder.accumulator_low;
            }

            // Low-part FD cascade over its n_low captured values (width 1).
            low_fd.clear();
            low_fd.extend_from_slice(&low_evals[..n_low]);
            fd_init_in_place(low_fd, n_low, 1);

            // High-only evals beyond: skip the low block with the FD-advanced
            // state, and add the FD-advanced low contribution.
            for node_acc in acc[n_low..n_nodes].iter_mut() {
                fd_advance(win, window, n_cols);
                fd_advance(s_fd, window, state_len);
                fd_advance(low_fd, n_low, 1);
                let pt = &win[(window - 1) * n_cols..window * n_cols];

                scratch.clear();
                scratch.extend_from_slice(&s_fd[(window - 1) * state_len..window * state_len]);

                let mut folder = ConstraintFolderPacked::new(&pt[..n_flat], &pt[n_flat..], extra_data);
                folder.skip_low = true;
                folder.cached_state = Some(std::mem::take(scratch));
                folder.low_ci_count = low_n_constraints;
                Air::eval(computation, &mut folder, extra_data);
                *scratch = folder.cached_state.unwrap();

                *node_acc += (folder.accumulator + low_fd[n_low - 1]) * partial_eq;
            }
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(b) {
                *x += y;
            }
            a
        },
    );

    acc.into_iter()
        .map(|s| EFPacking::<EF>::to_ext_iter([s]).sum::<EF>())
        .collect()
}

/// Reference degree-split kernel: Lagrange-coefficient dots (iter-1 path).
#[allow(clippy::too_many_arguments)]
fn compute_skip_evals_degree_split_lagrange<EF, A>(
    cols: &[&[PFPacking<EF>]],
    computation: &A,
    extra_data: &A::ExtraData,
    split_eq: &SplitEq<EF>,
    k: usize,
    pivot: usize,
    active_packed: usize,
    nodes: &[PF<EF>],
    lagrange_targets: &[Vec<PF<EF>>],
    low_degree: usize,
    low_n_constraints: usize,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
    EFPacking<EF>: PrimeCharacteristicRing
        + Mul<PFPacking<EF>, Output = EFPacking<EF>>
        + Add<PFPacking<EF>, Output = EFPacking<EF>>,
{
    let w = packing_log_width::<EF>();
    let n_cols = cols.len();
    let n_flat = computation.n_columns();
    let window = 1usize << k;
    let n_nodes = nodes.len();
    // The low-degree block's constraints have z-degree ≤ low_degree·(2^k − 1),
    // determined by the first `n_low` nodes (full evals there); beyond, the
    // block is skipped: its post-state — degree ≤ 2^k − 1 in z without the low
    // constraints (affine ops on degree-(2^k − 1) column extensions) — is
    // interpolated from the 2^k window states, and the low contribution from
    // the `n_low` captured values.
    let n_low = low_degree * (window - 1) + 1;
    debug_assert!(n_low >= window && n_low <= n_nodes);
    let log_block = pivot - k - w;
    let log_chunk = pivot - w;
    let xb: Vec<usize> = (0..window).map(|x| skip_block_of_x(x, k)).collect();
    let lag_packed: Vec<Vec<PFPacking<EF>>> = lagrange_targets
        .iter()
        .map(|row| row.iter().map(|&l| PFPacking::<EF>::from(l)).collect())
        .collect();
    // Lagrange rows for the low part: first n_low nodes -> remaining nodes.
    let lag_low_packed: Vec<Vec<PFPacking<EF>>> = lagrange_basis_evals(&nodes[..n_low], &nodes[n_low..])
        .into_iter()
        .map(|row| row.into_iter().map(PFPacking::<EF>::from).collect())
        .collect();

    let acc = parallel::map_reduce_with_state(
        active_packed,
        || {
            (
                vec![PFPacking::<EF>::ZERO; window * n_cols], // win
                vec![PFPacking::<EF>::ZERO; n_cols],          // point
                vec![Vec::<PFPacking<EF>>::new(); window],    // captured post-block states
                Vec::<PFPacking<EF>>::new(),                  // interpolated state scratch
                vec![EFPacking::<EF>::ZERO; n_low],           // low evals
            )
        },
        || vec![EFPacking::<EF>::ZERO; n_nodes],
        |(win, point, states, scratch, low_evals), acc, j_p| {
            let partial_eq = split_eq.get_packed(j_p);
            gather_window(cols, win, j_p, &xb, log_block, log_chunk);

            // Full evals at the window nodes; capture the post-block state.
            for x in 0..window {
                let pt = &win[x * n_cols..(x + 1) * n_cols];
                let mut folder = ConstraintFolderPacked::new(&pt[..n_flat], &pt[n_flat..], extra_data);
                folder.cached_state = Some(std::mem::take(&mut states[x]));
                Air::eval(computation, &mut folder, extra_data);
                acc[x] += folder.accumulator * partial_eq;
                low_evals[x] = folder.accumulator_low;
                states[x] = folder.cached_state.unwrap();
            }
            // Full evals at the extended nodes that still determine the low part.
            for e in 0..n_low - window {
                extend_point::<EF>(win, point, &lag_packed[e], n_cols);
                let mut folder = ConstraintFolderPacked::new(&point[..n_flat], &point[n_flat..], extra_data);
                Air::eval(computation, &mut folder, extra_data);
                acc[window + e] += folder.accumulator * partial_eq;
                low_evals[window + e] = folder.accumulator_low;
            }
            // High-only evals beyond: skip the low block with interpolated state,
            // and add the Lagrange-extended low contribution.
            for z in n_low..n_nodes {
                let e = z - window;
                extend_point::<EF>(win, point, &lag_packed[e], n_cols);

                let lag = &lag_packed[e];
                scratch.clear();
                let state_len = states[0].len();
                for i in 0..state_len {
                    let mut s = states[0][i] * lag[0];
                    for (x, st) in states.iter().enumerate().skip(1) {
                        s += st[i] * lag[x];
                    }
                    scratch.push(s);
                }

                let mut folder = ConstraintFolderPacked::new(&point[..n_flat], &point[n_flat..], extra_data);
                folder.skip_low = true;
                folder.cached_state = Some(std::mem::take(scratch));
                folder.low_ci_count = low_n_constraints;
                Air::eval(computation, &mut folder, extra_data);
                *scratch = folder.cached_state.unwrap();

                let mut low_interpolated = EFPacking::<EF>::ZERO;
                for (i, &lc) in lag_low_packed[z - n_low].iter().enumerate() {
                    low_interpolated += low_evals[i] * lc;
                }
                acc[z] += (folder.accumulator + low_interpolated) * partial_eq;
            }
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(b) {
                *x += y;
            }
            a
        },
    );

    acc.into_iter()
        .map(|s| EFPacking::<EF>::to_ext_iter([s]).sum::<EF>())
        .collect()
}

/// Scalar fallback for tables too small for the packed kernel
/// (`n − k ≤ packing_log_width`): full evals at every node, no degree split,
/// finite-difference extension. These tables have at most `2^{w + k}` rows —
/// the cost is negligible.
#[allow(clippy::too_many_arguments)]
fn compute_skip_evals_unpacked<EF, A>(
    group: &MleGroupRef<'_, EF>,
    computation: &A,
    extra_data: &A::ExtraData,
    split_eq: &SplitEq<EF>,
    k: usize,
    pivot: usize,
    active_rest: usize,
    nodes: &[PF<EF>],
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    let window = 1usize << k;
    let n_nodes = nodes.len();
    let log_block = pivot - k;
    let xb: Vec<usize> = (0..window).map(|x| skip_block_of_x(x, k)).collect();
    let block_mask = (1usize << log_block) - 1;

    let unpacked = group.unpack();
    let unpacked_ref = unpacked.by_ref();
    let cols = unpacked_ref.as_base().expect("skip round expects base columns");
    let n_cols = cols.len();

    let mut acc = vec![EF::ZERO; n_nodes];
    let mut win = vec![PF::<EF>::ZERO; window * n_cols];
    for j in 0..active_rest {
        let partial_eq = split_eq.get_unpacked(j);
        let chunk = j >> log_block;
        let o = j & block_mask;
        let base = (chunk << pivot) | o;
        for (c, col) in cols.iter().enumerate() {
            for (x, &b) in xb.iter().enumerate() {
                win[x * n_cols + c] = col[base | (b << log_block)];
            }
        }
        for x in 0..window {
            let v = computation.eval_base(&win[x * n_cols..(x + 1) * n_cols], extra_data);
            acc[x] += partial_eq * v;
        }
        fd_init_in_place(&mut win, window, n_cols);
        for node_acc in acc[window..n_nodes].iter_mut() {
            fd_advance(&mut win, window, n_cols);
            let v = computation.eval_base(&win[(window - 1) * n_cols..window * n_cols], extra_data);
            *node_acc += partial_eq * v;
        }
    }
    acc
}

/// Reference scalar fallback: Lagrange-coefficient dots (iter-1 path).
#[allow(clippy::too_many_arguments)]
fn compute_skip_evals_unpacked_lagrange<EF, A>(
    group: &MleGroupRef<'_, EF>,
    computation: &A,
    extra_data: &A::ExtraData,
    split_eq: &SplitEq<EF>,
    k: usize,
    pivot: usize,
    active_rest: usize,
    nodes: &[PF<EF>],
    lagrange_targets: &[Vec<PF<EF>>],
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    let window = 1usize << k;
    let n_nodes = nodes.len();
    let log_block = pivot - k;
    let xb: Vec<usize> = (0..window).map(|x| skip_block_of_x(x, k)).collect();
    let block_mask = (1usize << log_block) - 1;

    let unpacked = group.unpack();
    let unpacked_ref = unpacked.by_ref();
    let cols = unpacked_ref.as_base().expect("skip round expects base columns");
    let n_cols = cols.len();

    let mut acc = vec![EF::ZERO; n_nodes];
    let mut win = vec![PF::<EF>::ZERO; window * n_cols];
    let mut point = vec![PF::<EF>::ZERO; n_cols];
    for j in 0..active_rest {
        let partial_eq = split_eq.get_unpacked(j);
        let chunk = j >> log_block;
        let o = j & block_mask;
        let base = (chunk << pivot) | o;
        for (c, col) in cols.iter().enumerate() {
            for (x, &b) in xb.iter().enumerate() {
                win[x * n_cols + c] = col[base | (b << log_block)];
            }
        }
        for x in 0..window {
            let v = computation.eval_base(&win[x * n_cols..(x + 1) * n_cols], extra_data);
            acc[x] += partial_eq * v;
        }
        for (e, lag) in lagrange_targets.iter().enumerate() {
            point.fill(PF::<EF>::ZERO);
            for (x, &lw) in lag.iter().enumerate() {
                for (p, &v) in point.iter_mut().zip(&win[x * n_cols..(x + 1) * n_cols]) {
                    *p += v * lw;
                }
            }
            let v = computation.eval_base(&point, extra_data);
            acc[window + e] += partial_eq * v;
        }
    }
    acc
}

#[cfg(test)]
mod fd_tests {
    use super::{fd_advance, fd_init_in_place};
    use backend::*;

    fn horner(coeffs: &[KoalaBear], x: usize) -> KoalaBear {
        let xf = KoalaBear::from_usize(x);
        let mut acc = KoalaBear::ZERO;
        for &c in coeffs.iter().rev() {
            acc = acc * xf + c;
        }
        acc
    }

    /// The FD recurrence reproduces every consecutive node value of a degree-d
    /// polynomial exactly (the classic cascade-direction off-by-one trap).
    #[test]
    fn fd_matches_direct_evaluation() {
        for d in [1usize, 2, 3, 7, 15, 31, 45] {
            let n_rows = d + 1;
            let coeffs: Vec<KoalaBear> = (0..=d).map(|i| KoalaBear::from_usize(7 * i * i + 3 * i + 1)).collect();
            let mut rows: Vec<KoalaBear> = (0..n_rows).map(|i| horner(&coeffs, i)).collect();
            fd_init_in_place(&mut rows, n_rows, 1);
            for next in n_rows..n_rows + 40 {
                fd_advance(&mut rows, n_rows, 1);
                assert_eq!(rows[n_rows - 1], horner(&coeffs, next), "d={d}, node={next}");
            }
        }
    }

    /// width > 1: independent polynomials per lane advance in lockstep.
    #[test]
    fn fd_matches_direct_evaluation_wide() {
        let d = 15usize;
        let width = 3usize;
        let n_rows = d + 1;
        let polys: Vec<Vec<KoalaBear>> = (0..width)
            .map(|c| {
                (0..=d)
                    .map(|i| KoalaBear::from_usize(11 * c * c + 5 * i * i * i + i + 2))
                    .collect()
            })
            .collect();
        let mut rows = vec![KoalaBear::ZERO; n_rows * width];
        for i in 0..n_rows {
            for (c, p) in polys.iter().enumerate() {
                rows[i * width + c] = horner(p, i);
            }
        }
        fd_init_in_place(&mut rows, n_rows, width);
        for next in n_rows..n_rows + 25 {
            fd_advance(&mut rows, n_rows, width);
            for (c, p) in polys.iter().enumerate() {
                assert_eq!(rows[(n_rows - 1) * width + c], horner(p, next), "lane {c}, node {next}");
            }
        }
    }
}
