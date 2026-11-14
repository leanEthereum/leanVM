// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The module is the rectangular (f = 64, e = 128) generalization of binius64's
// DP24 ring switch described in the ring-switching-generalized note.

//! Ring-switching reduction for the 64-bit transition: F_2 to K = GF(2^64)
//! packing, opened over E = GF(2^128) = K\[y\]/(y^2 + x*y + 1) ([`F128`]).
//!
//! With f = 64 (packing degree over F_2) and e = 128 (opening degree), this
//! converts one evaluation claim on
//! the bit-witness MLE at an E-point into a WHIR sumcheck claim on the
//! packed multilinear (a `Vec<F64>`, one word per 64 bits, see
//! [`super::pack`]) against a transparent E-valued weight vector
//! `rs_eq_ind`.
//!
//! ## Rectangular shape
//!
//! - `s_hat_v` has 64 entries (one per packing bit), each an E element; its
//!   tensor-algebra transpose `s_hat_u = (t_i)` has 128 K-entries. A random
//!   `F_2`-linear map batches all coordinates directly.
//! - **No "7 = 6 + 1" prefix split**: with 64-bit packing the packed prefix
//!   is exactly the 6-bit skip domain, so every coordinate outside it is an
//!   ordinary suffix coordinate of the packed witness (which has `2^(m-6)`
//!   words).
//! - **The 64 slices come in bound**: `s_hat_v[i] = sum_y eq(r_suffix, y) *
//!   bit_i(packed[y])`, the MLE of the i-th bit-slice at the suffix point, is
//!   supplied by the caller on both sides, which is where it was transmitted
//!   and checked (the Keccak reduction sends them and checks them against its
//!   last claim). This module therefore reads nothing off the stream and only has
//!   to bind the slices to the commitment.
//!
//! ## Protocol (prover)
//!
//! 1. Take the caller's bound `s_hat_v`.
//! 2. Sample sixteen challenges `f_0..f_7, g_0..g_7` in E and define
//!    `Psi(v) = sum_b g_b v^(2^b)` and `Phi(v) = sum_p f_p Psi(v)^(2^(8p))`.
//!    For the coordinate basis `(b_i)`, define `coord_weights[i] = Phi(b_i)`. Transpose
//!    `s_hat_v` to `t_i = s_hat_u[i] in K` (see
//!    `super::tensor_algebra::transpose_s_hat`); the batched target is
//!    `sumcheck_claim = sum_i Phi(b_i) * t_i` (K x E via `mul_base`).
//! 3. Both sides define the transparent weights
//!    `rs_eq_ind[y] = Phi(eq(r_suffix, y))` where `Phi : E -> E` is the
//!    map above. Completeness:
//!    `sum_y rs_eq_ind[y] * packed[y] == sumcheck_claim`, which is exactly
//!    the claim shape [`super::stack_open::open_batch_mixed_whir_stacked`]
//!    proves (with `b_initial = rs_eq_ind`, `target = sumcheck_claim`).
//!    A nonzero discrepancy survives each stage with probability `1 / |E|`, so
//!    the check misses it with probability at most `2 / |E|` before the WHIR
//!    list-size factor.
//!
//! ## Building `rs_eq_ind`
//!
//! The prover keeps each claim as its point and its map, and the opening's
//! basis (`stack_open::basis`) folds them into its terms, so no dense weight is
//! ever built, per claim or combined. A verifier never
//! builds the vector at all: it evaluates its MLE at the WHIR final point from
//! `Phi`'s challenges.

use fiat_shamir::transcript::ProverState;
use primitives::bit_fold::{BLOCK, BitFold};
use primitives::field::xor_into8;
use primitives::field::{F64, F128, mul4};

use super::pack::PACKING_WIDTH;
use super::tensor_algebra::{DEGREE_E, transpose_s_hat};
use super::whir::inner_product_base_ext;
use primitives::multilinear::eq_table_serial;

/// The batching map's challenges: `f_0..f_7`, then `g_0..g_7`.
pub(crate) const MAP_CHALLENGES: usize = 16;

/// The map misses a nonzero error with probability at most this many over `|E|`, one per stage. The WHIR list-size
/// soundness accounting adds it to the batching numerator.
pub(crate) const RING_SWITCH_ERROR_NUMERATOR: usize = 2;

/// The coordinate batching weights: `weights[w] = Phi(b_w)`, where `b_w = x^i·y^j` (`w = 64j + i`)
/// is the `w`-th `F_2`-coordinate basis element of `E` (the order `transpose_s_hat` produces), and
///
/// ```text
/// Psi(v) = sum_{b<8} g_b · v^(2^b),    Phi(v) = sum_{p<8} f_p · Psi(v)^(2^(8p)).
/// ```
///
/// The result is `F_2`-linear, so
/// `sum_w weights[w]·t_w = sum_j x^j·Phi(y_j)` for the row
/// view `y` and the column view `t` of the same tensor-algebra element. That
/// identity is what lets a verifier evaluate the batched claim from `Phi`'s
/// sixteen challenges instead of the 128 weights; the recursion guest does exactly
/// that. Expanding puts one term at every Frobenius exponent `0..64`:
/// `Phi(v) = sum_{k<64} C_k·v^(2^k)` with `C_{8p+b} = f_p·g_b^(2^(8p))`.
///
/// ## Soundness
///
/// Let `delta != 0` be the prover's error on the transposed columns, fixed
/// before the challenges (`s_hat_v` is bound first). The check misses it iff
/// `sum_w Phi(b_w)·delta_w = sum_{k<64} C_k·V_k = 0` with
/// `V_k = sum_w b_w^(2^k)·delta_w`. Writing `w = 64j + i` and `b_w = x^i·Y^j`,
///
/// ```text
/// V_k = R_{0,k} + Y^(2^k)·R_{1,k},   R_{j,k} = sum_{i<64} x^(i·2^k)·delta_{64j+i} in K.
/// ```
///
/// `Y^(2^k)` is not in `K` (squaring is a bijection of `K`, so `Y^(2^k) in K`
/// would force `Y in K`), and `[E:K] = 2`, so `{1, Y^(2^k)}` is a `K`-basis:
/// `V_k = 0` forces both `R_{j,k} = 0`. At fixed `j` those 64 equations say that the polynomial
/// `D_j(U) = sum_{i<64} delta_{64j+i}·U^i`, of degree at most 63, vanishes at
/// `x, x^2, x^4, ..., x^(2^63)`. Those are 64 distinct points, since `x` has
/// degree 64 over `F_2`, so `D_j = 0` and `delta = 0`. Hence some `V_k != 0`.
/// Grouped by `p`, the discrepancy is `sum_p f_p·M_p` with
/// `M_p = sum_b g_b^(2^(8p))·V_{8p+b} = (sum_b g_b·V_{8p+b}^(2^(-8p)))^(2^(8p))`. The Frobenius is a bijection, so for
/// a `p` with some `V_{8p+b} != 0` the inner form is a nonzero linear form in the `g_b`, zero with probability
/// `1 / |E|`, and otherwise the outer one is nonzero in the `f_p`, zero with probability `1 / |E|`:
/// [`RING_SWITCH_ERROR_NUMERATOR`] in all.
///
/// The 64 terms are also the floor: the weights must separate any nonzero
/// error on the 128 transposed `K`-columns, which is `|S|` `E`-equations, i.e.
/// `2·|S|` `K`-equations, in `128` `K`-unknowns, and with `2·|S| < 128` a
/// nonzero error lies in the kernel for EVERY coefficient choice and passes
/// with probability one.
pub(crate) fn build_coordinate_weights(challenges: &[F128; MAP_CHALLENGES]) -> [F128; DEGREE_E] {
    std::array::from_fn(|w| apply_map(coordinate_basis(w), challenges))
}

/// `Phi(value)` of [`build_coordinate_weights`], stage by stage.
fn apply_map(value: F128, challenges: &[F128; MAP_CHALLENGES]) -> F128 {
    let (f, g) = challenges.split_at(MAP_CHALLENGES / 2);
    let mut frobenius = value;
    let mut psi = F128::ZERO;
    for &g_b in g {
        psi += g_b * frobenius;
        frobenius = frobenius.square();
    }
    let mut phi = F128::ZERO;
    for &f_p in f {
        phi += f_p * psi;
        for _ in 0..8 {
            psi = psi.square();
        }
    }
    phi
}

/// Sample the map's challenges, `f_0..f_7` then `g_0..g_7`, after every ring-switch message has
/// been bound.
pub(crate) fn sample_map_challenges(ch: &mut ProverState) -> [F128; MAP_CHALLENGES] {
    std::array::from_fn(|_| ch.sample())
}

// ---------------------------------------------------------------------------
// Building blocks
// ---------------------------------------------------------------------------

/// Compute the slice-MLE vector `s_hat_v` (length 64) from a packed witness
/// and a tensor-expanded suffix point.
///
/// `packed_witness[y] in K` for `y in 0..2^L`; `suffix_tensor` is
/// `eq(r_suffix, .)` over the same range (from
/// [`eq_table_serial`]).
///
/// Output: `s_hat_v[i] = sum_y bit_i(packed_witness[y]) * suffix_tensor[y]`
/// for `i in 0..64` (bit i = polynomial-basis coordinate of the u64).
///
/// A caller whose reduction already produced these passes them in, so this is the reference for tests and the unprepared fallback.
pub fn fold_1b_rows(packed_witness: &[F64], suffix_tensor: &[F128]) -> [F128; PACKING_WIDTH] {
    assert_eq!(packed_witness.len(), suffix_tensor.len());
    parallel::fold_reduce(
        packed_witness.len(),
        || [F128::ZERO; PACKING_WIDTH],
        |acc, i| {
            let w = suffix_tensor[i];
            let mut bits = packed_witness[i].0;
            while bits != 0 {
                acc[bits.trailing_zeros() as usize] += w;
                bits &= bits - 1;
            }
        },
        xor_accs,
    )
}

/// XOR-reduce two per-worker partial accumulators of the bit-slice folds
/// (E addition is XOR, so the reduction order does not matter).
fn xor_accs(mut a: [F128; PACKING_WIDTH], b: [F128; PACKING_WIDTH]) -> [F128; PACKING_WIDTH] {
    for (av, bv) in a.iter_mut().zip(b.iter()) {
        *av += *bv;
    }
    a
}

/// Compute `rs_eq_ind`, the transparent E-valued weight vector over the
/// suffix domain: `rs_eq_ind[y] = Phi(suffix_tensor[y])` where `Phi` sends
/// E-basis bit w to `coordinate_weights[w]`, i.e.
///
/// `rs_eq_ind[y] = sum_w bit_w(suffix_tensor[y]) * coordinate_weights[w]`
///
/// Naive reference: a per-position bit-scan.
#[cfg(test)]
pub fn fold_ext_elems_naive(suffix_tensor: &[F128], coordinate_weights: &[F128; DEGREE_E]) -> Vec<F128> {
    parallel::map_collect(suffix_tensor.len(), |i| {
        let mut bits = u128::from(suffix_tensor[i]);
        let mut acc = F128::ZERO;
        while bits != 0 {
            acc += coordinate_weights[bits.trailing_zeros() as usize];
            bits &= bits - 1;
        }
        acc
    })
}

/// Deferred, lambda-baked ring-switch output used by the stacked opener.
///
/// Keeping the claim's point and its map avoids materializing one full
/// `rs_eq_ind` vector per claim. The map already contains the claim's batching
/// scalar, so combining several claims needs only additions.
pub(crate) struct DeferredRingSwitchOutput {
    pub(crate) batched_sumcheck_claim: F128,
    pub(crate) weight: RingWeight,
}

/// `Phi(eq(point, y))` over a claim's suffix domain, for an F_2-linear `Phi` given by its
/// value on every coordinate basis element of `E`.
#[derive(Clone)]
pub(crate) struct RingWeight {
    weights: [F128; DEGREE_E],
    point: Vec<F128>,
}

/// A [`RingWeight`] ready to fill its values: the factored `eq(point, ·)` and `Phi` as bit folds.
pub(crate) struct RingFold {
    eq_lo: Vec<F128>,
    eq_hi: Vec<F128>,
    /// The weights of a product's 128 bits, to fold 64 products at a time.
    fold: BitFold,
}

/// The `w`-th `F_2`-coordinate basis element of `E`: bits 0..64 are K's power
/// basis, and bits 64..128 shift it by Y.
pub(crate) fn coordinate_basis(w: usize) -> F128 {
    F128::from(1u128 << w)
}

impl RingWeight {
    pub(crate) fn new(weights: [F128; DEGREE_E], point: Vec<F128>) -> Self {
        Self { weights, point }
    }

    /// The tables that fill the weight's values.
    pub(crate) fn fold(&self) -> RingFold {
        let (eq_lo, eq_hi) = build_eq_split_ext(&self.point);
        RingFold {
            eq_lo,
            eq_hi,
            fold: BitFold::new(&self.weights),
        }
    }

    pub(crate) fn point(&self) -> &[F128] {
        &self.point
    }

    /// `Phi(value)`.
    pub(crate) fn apply(&self, value: F128) -> F128 {
        let mut acc = F128::ZERO;
        for (limb, word) in value.to_limbs().into_iter().enumerate() {
            let mut bits = word;
            while bits != 0 {
                acc += self.weights[limb * PACKING_WIDTH + bits.trailing_zeros() as usize];
                bits &= bits - 1;
            }
        }
        acc
    }
}

impl RingFold {
    /// `out[j] += Phi(eq(point, start + j))`.
    pub(crate) fn add_chunk(&self, start: usize, out: &mut [F128]) {
        let block_len = self.eq_lo.len();
        assert!(start + out.len() <= block_len * self.eq_hi.len());
        let mut done = 0;
        while done < out.len() {
            let index = start + done;
            let lo = index % block_len;
            let len = (block_len - lo).min(out.len() - done);
            let e_hi = self.eq_hi[index / block_len];
            self.fold_products(&self.eq_lo[lo..lo + len], e_hi, &mut out[done..done + len]);
            done += len;
        }
    }

    /// `out[j] += Phi(e_lo[j] * e_hi)`, 64 products at a time through the bit fold.
    #[inline]
    fn fold_products(&self, e_lo: &[F128], e_hi: F128, out: &mut [F128]) {
        debug_assert_eq!(e_lo.len(), out.len());
        let mut rows = [[0u64; 2]; BLOCK];
        let mut folded = [F128::ZERO; BLOCK];
        for (e_lo, out) in e_lo.chunks(BLOCK).zip(out.chunks_mut(BLOCK)) {
            let n = e_lo.len();
            let (lo4, lo_r) = e_lo.as_chunks::<4>();
            for (k, e_lo) in lo4.iter().enumerate() {
                for (j, p) in mul4(*e_lo, [e_hi; 4]).into_iter().enumerate() {
                    rows[4 * k + j] = p.to_limbs();
                }
            }
            for (j, &e_lo) in lo_r.iter().enumerate() {
                rows[4 * lo4.len() + j] = (e_lo * e_hi).to_limbs();
            }
            let rows = primitives::cast_slice::<[u64; 2], [u8; 16]>(&rows);
            self.fold.fold_block(&rows[..n], &mut folded);
            let (out8, out_r) = out.as_chunks_mut::<8>();
            for (o, f) in out8.iter_mut().zip(folded.as_chunks::<8>().0) {
                xor_into8(o, f);
            }
            for (o, f) in out_r.iter_mut().zip(&folded[8 * out8.len()..]) {
                *o += *f;
            }
        }
    }
}

/// Finish a ring-switch claim without materializing its dense weight vector.
/// The batching scalar is baked into both the target and the map.
pub(crate) fn prove_finish_deferred(
    state: RingSwitchProveState,
    coordinate_weights: &[F128; DEGREE_E],
    lambda: F128,
) -> DeferredRingSwitchOutput {
    let s_hat_u = transpose_s_hat(&state.s_hat_v);
    let sumcheck_claim = inner_product_base_ext(&s_hat_u, coordinate_weights);
    let scaled_weights = coordinate_weights.map(|x| lambda * x);
    DeferredRingSwitchOutput {
        batched_sumcheck_claim: lambda * sumcheck_claim,
        weight: RingWeight::new(scaled_weights, state.point),
    }
}

/// The dense weight of several deferred claims, accumulated into `out`: the reference for tests.
#[cfg(test)]
pub(crate) fn combine_deferred_chunk(outputs: &[DeferredRingSwitchOutput], out: &mut [F128]) {
    for claim in outputs {
        claim.weight.fold().add_chunk(0, out);
    }
}

/// Split point for the factored eq build: low half sized ~n/2 (min 4, the
/// point where two factor tables beat one full build).
fn split_n_lo(n: usize) -> usize {
    (n / 2).clamp(4.min(n), n)
}

/// Factored eq tensor: `eq(point, y) = eq_lo[y & (2^n_lo - 1)] * eq_hi[y >> n_lo]`
/// (LSB-first indexing, matching `eq_table_serial`). Materializes
/// `2^n_lo + 2^(n - n_lo)` entries instead of `2^n`; field multiplication is
/// exact, so the reconstructed entries are bit-identical to the full build.
fn build_eq_split_ext(point: &[F128]) -> (Vec<F128>, Vec<F128>) {
    let n_lo = split_n_lo(point.len());
    (eq_table_serial(&point[..n_lo]), eq_table_serial(&point[n_lo..]))
}

// ---------------------------------------------------------------------------
// Prover of the reduction
// ---------------------------------------------------------------------------

/// Prover-side scratch carried from [`prove_prepare`] into finalization.
///
/// The two phases exist because one map is shared by every claim, and it can
/// only be sampled once all of them have been sent. So each claim's
/// map-independent work (its slice-MLE vector and its point) has to survive
/// that barrier.
#[derive(Clone)]
pub struct RingSwitchProveState {
    s_hat_v: [F128; PACKING_WIDTH],
    point: Vec<F128>,
}

/// Phase 1 of the ring-switch prover: get `s_hat_v`, the 64 bit-slice values at
/// `suffix_point`, and return the scratch for finalization. The caller samples the
/// possibly shared map afterwards.
///
/// The slices are NOT sent here: the caller has already bound them (the Keccak
/// reduction sends them itself), which is what lets this
/// phase touch no transcript at all. `precomputed_s_hat_v` is `None` only for a
/// caller that wants them folded out of the witness instead.
pub fn prove_prepare(
    packed_witness: &[F64],
    suffix_point: &[F128],
    precomputed_s_hat_v: Option<&[F128]>,
) -> RingSwitchProveState {
    assert_eq!(
        packed_witness.len(),
        1usize << suffix_point.len(),
        "packed witness must have 2^|suffix_point| words"
    );
    let s_hat_v = match precomputed_s_hat_v {
        Some(v) => v.try_into().expect("one slice per packing bit"),
        None => {
            let (eq_lo, eq_hi) = build_eq_split_ext(suffix_point);
            let mask = eq_lo.len() - 1;
            let shift = eq_lo.len().trailing_zeros();
            let full: Vec<F128> = parallel::map_collect(packed_witness.len(), |y| eq_lo[y & mask] * eq_hi[y >> shift]);
            fold_1b_rows(packed_witness, &full)
        }
    };
    RingSwitchProveState {
        s_hat_v,
        point: suffix_point.to_vec(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pack::LOG_PACKING;
    use primitives::test_rng::Rng;

    /// Pack bit `64 * y + i` of `bits` into bit `i` of word `y`.
    fn pack_witness(bits: &[bool]) -> Vec<F64> {
        let word = |c: &[bool]| c.iter().rev().fold(0, |acc, &b| acc << 1 | b as u64);
        bits.chunks(PACKING_WIDTH).map(|c| F64(word(c))).collect()
    }

    #[test]
    fn deferred_batch_matches_materialized_weights() {
        let mut rng = Rng::new(0xdec0_de01_2345_6789);
        let point = rng.ext_vec(10);
        let coordinate_weights = std::array::from_fn(|_| rng.ext());
        let lambdas = [rng.ext(), rng.ext()];
        let states = (0..2)
            .map(|_| RingSwitchProveState {
                s_hat_v: std::array::from_fn(|_| rng.ext()),
                point: point.clone(),
            })
            .collect::<Vec<_>>();

        // Reference: one dense weight vector per claim, combined afterwards.
        let dense_basis = fold_ext_elems_naive(&eq_table_serial(&point), &coordinate_weights);
        let expected_target: F128 = states
            .iter()
            .zip(lambdas)
            .map(|(state, lambda)| {
                lambda * inner_product_base_ext(&transpose_s_hat(&state.s_hat_v), &coordinate_weights)
            })
            .sum();
        let expected_basis = dense_basis
            .iter()
            .map(|&w| (lambdas[0] + lambdas[1]) * w)
            .collect::<Vec<_>>();

        let deferred = states
            .into_iter()
            .zip(lambdas)
            .map(|(state, lambda)| prove_finish_deferred(state, &coordinate_weights, lambda))
            .collect::<Vec<_>>();
        let deferred_target = deferred.iter().map(|out| out.batched_sumcheck_claim).sum::<F128>();
        let mut deferred_basis = vec![F128::ZERO; expected_basis.len()];
        combine_deferred_chunk(&deferred, &mut deferred_basis);

        assert_eq!(deferred_target, expected_target);
        assert_eq!(deferred_basis, expected_basis);
    }

    /// The contract between the native opener and every verifier that batches
    /// from `Phi`'s coefficients (the recursion guest, the Lean
    /// verifier): weighting the COLUMN view by `build_coordinate_weights` must
    /// equal applying `Phi` to the ROW view and combining with `x^j`. If this
    /// drifts, the guest computes a different opening target than the prover.
    #[test]
    fn column_weights_match_the_row_side_linearized_map() {
        let mut rng = Rng::new(0xF00D_BEEF_1234_5678);
        for _ in 0..4 {
            let challenges = std::array::from_fn(|_| rng.ext());
            let s_hat_v: [F128; PACKING_WIDTH] = std::array::from_fn(|_| rng.ext());

            // Column side: sum_w weights[w] * t_w over the transposed K columns.
            let columns = transpose_s_hat(&s_hat_v);
            let lhs = inner_product_base_ext(&columns, &build_coordinate_weights(&challenges));

            // Row side: sum_j x^j * Phi(y_j), the guest's loop.
            let x = F128::new(2, 0);
            let mut rhs = F128::ZERO;
            let mut x_pow = F128::ONE;
            for y in &s_hat_v {
                let phi = apply_map(*y, &challenges);
                rhs += x_pow * phi;
                x_pow *= x;
            }
            assert_eq!(lhs, rhs, "column weights and row-side Phi disagree");
        }
    }

    /// The two-stage evaluation against the expanded form `sum_k C_k·v^(2^k)` with
    /// `C_{8p+b} = f_p·g_b^(2^(8p))`, the coefficient table a verifier builds.
    #[test]
    fn map_expands_to_its_coefficients() {
        let mut rng = Rng::new(0x1234_5678_9abc_def0);
        for _ in 0..4 {
            let challenges: [F128; MAP_CHALLENGES] = std::array::from_fn(|_| rng.ext());
            let (f, g) = challenges.split_at(MAP_CHALLENGES / 2);
            let coefficients: [F128; PACKING_WIDTH] = std::array::from_fn(|k| {
                let mut g_b = g[k % 8];
                for _ in 0..8 * (k / 8) {
                    g_b = g_b.square();
                }
                f[k / 8] * g_b
            });
            let value = rng.ext();
            let mut expanded = F128::ZERO;
            let mut frobenius = value;
            for coefficient in coefficients {
                expanded += coefficient * frobenius;
                frobenius = frobenius.square();
            }
            assert_eq!(apply_map(value, &challenges), expanded);
        }
    }

    /// Reference s_hat_v: brute-force partial evaluation of each bit-column
    /// MLE at the suffix point (direct bit-extract loop, no fold kernel).
    fn s_hat_v_reference(packed: &[F64], suffix_point: &[F128]) -> [F128; PACKING_WIDTH] {
        let eq_suffix = eq_table_serial(suffix_point);
        std::array::from_fn(|i| {
            let mut acc = F128::ZERO;
            for (word, &w) in packed.iter().zip(eq_suffix.iter()) {
                if (word.0 >> i) & 1 == 1 {
                    acc += w;
                }
            }
            acc
        })
    }

    /// s_hat_v[i] must equal the MLE of the i-th bit-slice at the suffix
    /// point; cross-check the fold kernel against a from-the-bits brute
    /// force over the full (prefix + suffix) hypercube.
    #[test]
    fn s_hat_v_matches_bruteforce() {
        let m = 9;
        let mut rng = Rng::new(1);
        let bits = rng.bits(1usize << m);
        let packed = pack_witness(&bits);
        let suffix_point = rng.ext_vec(m - LOG_PACKING);
        let eq_suffix = eq_table_serial(&suffix_point);

        let s_hat_v = fold_1b_rows(&packed, &eq_suffix);

        // From the flat bit layout: column i is z[y * 64 + i].
        for i in 0..PACKING_WIDTH {
            let mut expected = F128::ZERO;
            for (y, &w) in eq_suffix.iter().enumerate() {
                if bits[(y << LOG_PACKING) | i] {
                    expected += w;
                }
            }
            assert_eq!(s_hat_v[i], expected, "bit column {i}");
        }
        assert_eq!(s_hat_v, s_hat_v_reference(&packed, &suffix_point));
    }

    /// The prefix x suffix split factors the bit-MLE, and `prove_prepare`'s
    /// witness fold reproduces the reference slice values.
    #[test]
    fn slices_factor_the_bit_mle() {
        let m = 10;
        let mut rng = Rng::new(2);
        let bits = rng.bits(1usize << m);
        let packed = pack_witness(&bits);
        let point = rng.ext_vec(m);
        let prefix_weights = eq_table_serial(&point[..LOG_PACKING]);
        let suffix_point = &point[LOG_PACKING..];

        let s_ref = s_hat_v_reference(&packed, suffix_point);
        let eq_full = eq_table_serial(&point);
        let mut direct = F128::ZERO;
        for (x, &w) in eq_full.iter().enumerate() {
            if bits[x] {
                direct += w;
            }
        }
        assert_eq!(
            prefix_weights.iter().zip(&s_ref).map(|(&w, &s)| w * s).sum::<F128>(),
            direct,
            "prefix x suffix split must factor the MLE"
        );
        assert_eq!(
            prove_prepare(&packed, suffix_point, None).s_hat_v,
            s_ref,
            "the witness fold must reproduce the reference slices"
        );
    }
}
