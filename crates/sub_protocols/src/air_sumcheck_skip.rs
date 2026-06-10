use std::fmt::Debug;
use std::ops::{Add, Mul};

use backend::*;

use crate::{AirSumcheckSession, OuterSumcheckSession};

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
    fn compute_skip_poly(&mut self, k: usize) -> DensePolynomial<EF>;

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
    fn compute_skip_poly(&mut self, k: usize) -> DensePolynomial<EF> {
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

        // Lagrange extension matrix: window -> extended targets.
        let lagrange_targets = lagrange_coeffs_for_targets::<PF<EF>>(k, &nodes[window..]);

        let active_rest = self.current_unpadded_len >> k;
        let total_rest = 1usize << (n - k);

        let raw: Vec<EF> = if n - k > w {
            let group = self.multilinears.by_ref();
            let cols = group
                .as_packed_base()
                .expect("skip round expects base-packed columns")
                .clone();
            debug_assert!(pivot - k >= w);
            match self.computation.low_degree_air() {
                Some((low_degree, low_n_constraints)) => compute_skip_evals_degree_split::<EF, A>(
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
                None => compute_skip_evals_generic::<EF, A>(
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
                &lagrange_targets,
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

/// Gathers, for one packed rest-position `j_p`, the `2^k` window values of all
/// columns into `win` (layout `win[x * n_cols + c]`, contiguous per window
/// node so constraint evals can borrow `&win[x * n_cols..]` directly).
#[inline(always)]
fn gather_window<T: Copy>(
    cols: &[&[T]],
    win: &mut [T],
    j_p: usize,
    xb: &[usize],
    log_block: usize,
    log_chunk: usize,
) {
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
                vec![PFPacking::<EF>::ZERO; window * n_cols],      // win
                vec![PFPacking::<EF>::ZERO; n_cols],               // point
                vec![Vec::<PFPacking<EF>>::new(); window],         // captured post-block states
                Vec::<PFPacking<EF>>::new(),                       // interpolated state scratch
                vec![EFPacking::<EF>::ZERO; n_low],                // low evals
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
/// (`n − k ≤ packing_log_width`): full evals at every node, no degree split.
/// These tables have at most `2^{w + k}` rows — the cost is negligible.
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
