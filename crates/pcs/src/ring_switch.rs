// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/binius-zk/binius64 (`eval_rs_eq`), Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The DP24 iterative `eval_rs_eq` is ported from binius64. The module is
// the rectangular (f = 64, e = 192) generalization described in
// the ring-switching-generalized note.

//! Ring-switching reduction for the 64-bit transition: F_2 to K = GF(2^64)
//! packing, opened over E = GF(2^192) (the tower [`F192`]).
//!
//! With f = 64 (packing degree over F_2) and e = 192 (opening degree), this
//! converts one evaluation claim on
//! the bit-witness MLE at an E-point into a WHIR sumcheck claim on the
//! packed multilinear (a `Vec<F64>`, one word per 64 bits, see
//! [`super::pack`]) against a transparent E-valued weight vector
//! `rs_eq_ind`.
//!
//! ## Rectangular shape
//!
//! - `s_hat_v` has 64 entries (one per packing bit), each an E element; its
//!   tensor-algebra transpose `s_hat_u = (t_i)` has 192 K-entries. A random
//!   `F_2`-linear map batches all coordinates directly, without padding them
//!   to a 256-entry Boolean cube.
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
//! 2. Sample six challenges in E and compose the maps
//!    `v <- v + f_t v^(2^d_t)` for `d_t = 32, 16, 8, 4, 2, 1`. For the
//!    coordinate basis `(b_i)`, define `coord_weights[i] = Phi(b_i)`. Transpose
//!    `s_hat_v` to `t_i = s_hat_u[i] in K` (see
//!    `super::tensor_algebra::transpose_s_hat`); the batched target is
//!    `sumcheck_claim = sum_i Phi(b_i) * t_i` (K x E via `mul_base`).
//! 3. Both sides define the transparent weights
//!    `rs_eq_ind[y] = Phi(eq(r_suffix, y))` where `Phi : E -> E` is the
//!    composed map above. Completeness:
//!    `sum_y rs_eq_ind[y] * packed[y] == sumcheck_claim`, which is exactly
//!    the claim shape [`super::stack_open::open_batch_mixed_whir_stacked`]
//!    proves (with `b_initial = rs_eq_ind`, `target = sumcheck_claim`).
//!    A nonzero discrepancy gives a nonzero polynomial in the six challenges;
//!    its total degree is below `2^32`, hence its failure probability is below
//!    `2^-160` before the WHIR list-size factor.
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
use primitives::field::{F64, F192, mul4};

use super::pack::PACKING_WIDTH;
use super::tensor_algebra::{DEGREE_E, transpose_s_hat};
use super::whir::{build_eq_table_ext, inner_product_base_ext};

/// Total degree of the six-challenge composed batching map. This is the
/// conservative degree used by the WHIR list-size soundness accounting.
pub const RING_SWITCH_SOUNDNESS_DEGREE: usize =
    (1usize << 31) + (1usize << 15) + (1usize << 7) + (1usize << 3) + (1usize << 1) + 1;

/// Frobenius shifts in the order in which the two-term maps are composed.
/// Descending order bounds every challenge's exponent by `2^31`.
pub const COMPOSITION_SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];

/// The coordinate batching weights: `weights[w] = Phi(b_w)`, where `b_w` is the
/// `w`-th `F_2`-coordinate basis element of `E` (the order `transpose_s_hat`
/// produces). Starting from `v`, the map composes
///
/// ```text
/// v <- v + f_t · v^(2^shift_t),    shift_t = 32, 16, 8, 4, 2, 1.
/// ```
///
/// The result is `F_2`-linear, so
/// `sum_w weights[w]·t_w = sum_j x^j·Phi(y_j)` for the row
/// view `y` and the column view `t` of the same tensor-algebra element. That
/// identity is what lets a verifier evaluate the batched claim from `Phi`'s
/// six challenges instead of the 192 weights; the recursion guest does exactly
/// that. Expanding the composition puts a distinct monomial at every Frobenius
/// exponent `0..64`: writing `k = sum_p k_p·2^(5-p)` for the binary digits of
/// `k`, the coefficient is `C_k = prod_{p : k_p = 1} f_p^(2^(k mod 2^(5-p)))`,
/// which is what the guest's coefficient table builds. Applying the composed
/// form directly costs only 63 squarings and six multiplications.
///
/// ## Soundness
///
/// Let `delta != 0` be the prover's error on the transposed columns, fixed
/// before the six challenges (`s_hat_v` is bound first). The check misses it iff
/// `sum_w Phi(b_w)·delta_w = sum_{k<64} C_k(f)·V_k = 0` with
/// `V_k = sum_w b_w^(2^k)·delta_w`. Writing `w = 64j + i` and `b_w = x^i·Y^j`,
///
/// ```text
/// V_k = sum_{j<3} (Y^(2^k))^j · R_{j,k},   R_{j,k} = sum_{i<64} x^(i·2^k)·delta_{64j+i} in K.
/// ```
///
/// `Y^(2^k)` is not in `K` (squaring is a bijection of `K`, so `Y^(2^k) in K`
/// would force `Y in K` and `E = K[Y] = K`), and `[E:K] = 3` is prime, so
/// `{1, Y^(2^k), Y^(2·2^k)}` is a `K`-basis: `V_k = 0` forces every
/// `R_{j,k} = 0`. At fixed `j` those 64 equations say that the polynomial
/// `D_j(U) = sum_{i<64} delta_{64j+i}·U^i`, of degree at most 63, vanishes at
/// `x, x^2, x^4, ..., x^(2^63)`. Those are 64 distinct points, since `x` has
/// degree 64 over `F_2`, so `D_j = 0` and `delta = 0`. Hence some `V_k != 0`.
/// The 64 `C_k` are distinct monomials, so the discrepancy is a nonzero
/// polynomial in the challenges. In descending shift order its total degree is
/// [`RING_SWITCH_SOUNDNESS_DEGREE`], below `2^32`.
///
/// The 64 terms are also the floor: the weights must separate any nonzero
/// error on the 192 transposed `K`-columns, which is `|S|` `E`-equations, i.e.
/// `3·|S|` `K`-equations, in `192` `K`-unknowns, and with `3·|S| < 192` a
/// nonzero error lies in the kernel for EVERY coefficient choice and passes
/// with probability one.
pub fn build_coordinate_weights(challenges: &[F192; COMPOSITION_SHIFTS.len()]) -> Vec<F192> {
    (0..DEGREE_E)
        .map(|w| apply_composed_map(coordinate_basis(w), challenges))
        .collect()
}

/// Applies the composed map `Phi` of [`build_coordinate_weights`] to one value.
fn apply_composed_map(mut value: F192, challenges: &[F192; COMPOSITION_SHIFTS.len()]) -> F192 {
    for (&challenge, &shift) in challenges.iter().zip(COMPOSITION_SHIFTS.iter()) {
        let mut frobenius = value;
        for _ in 0..shift {
            frobenius = frobenius.square();
        }
        value += challenge * frobenius;
    }
    value
}

/// Sample the composed map's challenges after every ring-switch message has
/// been bound.
pub fn sample_map_challenges(ch: &mut ProverState) -> [F192; COMPOSITION_SHIFTS.len()] {
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
/// [`build_eq_table_ext`]).
///
/// Output: `s_hat_v[i] = sum_y bit_i(packed_witness[y]) * suffix_tensor[y]`
/// for `i in 0..64` (bit i = polynomial-basis coordinate of the u64).
///
/// A caller whose reduction already produced these passes them in, so this is the reference for tests and the unprepared fallback.
pub fn fold_1b_rows(packed_witness: &[F64], suffix_tensor: &[F192]) -> Vec<F192> {
    assert_eq!(packed_witness.len(), suffix_tensor.len());
    parallel::fold_reduce(
        packed_witness.len(),
        || vec![F192::ZERO; PACKING_WIDTH],
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
fn xor_accs(mut a: Vec<F192>, b: Vec<F192>) -> Vec<F192> {
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
/// Naive reference: a per-position bit-scan over the three 64-bit limbs.
#[cfg(test)]
pub fn fold_ext_elems_naive(suffix_tensor: &[F192], coordinate_weights: &[F192]) -> Vec<F192> {
    assert_eq!(coordinate_weights.len(), DEGREE_E);
    parallel::map_collect(suffix_tensor.len(), |i| {
        let elem = suffix_tensor[i];
        let mut acc = F192::ZERO;
        let mut c0 = elem.c0;
        while c0 != 0 {
            let w = c0.trailing_zeros() as usize;
            acc += coordinate_weights[w];
            c0 &= c0 - 1;
        }
        let mut c1 = elem.c1;
        while c1 != 0 {
            let w = c1.trailing_zeros() as usize;
            acc += coordinate_weights[64 | w];
            c1 &= c1 - 1;
        }
        let mut c2 = elem.c2;
        while c2 != 0 {
            let w = c2.trailing_zeros() as usize;
            acc += coordinate_weights[128 | w];
            c2 &= c2 - 1;
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
    pub(crate) batched_sumcheck_claim: F192,
    pub(crate) weight: RingWeight,
}

/// `Phi(eq(point, y))` over a claim's suffix domain, for an F_2-linear `Phi` given by its
/// value on every coordinate basis element of `E`.
#[derive(Clone)]
pub(crate) struct RingWeight {
    weights: Vec<F192>,
    point: Vec<F192>,
}

/// A [`RingWeight`] ready to fill its values: the factored `eq(point, ·)` and `Phi` as bit folds.
pub(crate) struct RingFold {
    eq_lo: Vec<F192>,
    eq_hi: Vec<F192>,
    /// The weights of a product row's low 128 bits and of its top 64, to fold 64 rows at a time.
    fold: (BitFold, BitFold),
}

/// The `w`-th `F_2`-coordinate basis element of `E`: bits 0..64 are K's power
/// basis, and bits 64/128 shift it by Y / Y^2.
pub(crate) fn coordinate_basis(w: usize) -> F192 {
    match w / PACKING_WIDTH {
        0 => F192::new(1u64 << (w % PACKING_WIDTH), 0, 0),
        1 => F192::new(0, 1u64 << (w % PACKING_WIDTH), 0),
        _ => F192::new(0, 0, 1u64 << (w % PACKING_WIDTH)),
    }
}

impl RingWeight {
    pub(crate) fn new(weights: Vec<F192>, point: Vec<F192>) -> Self {
        assert_eq!(weights.len(), DEGREE_E);
        Self { weights, point }
    }

    /// The tables that fill the weight's values.
    pub(crate) fn fold(&self) -> RingFold {
        let (eq_lo, eq_hi) = build_eq_split_ext(&self.point);
        RingFold {
            eq_lo,
            eq_hi,
            fold: (BitFold::new(&self.weights[..128]), BitFold::new(&self.weights[128..])),
        }
    }

    pub(crate) fn point(&self) -> &[F192] {
        &self.point
    }

    /// `Phi(value)`.
    pub(crate) fn apply(&self, value: F192) -> F192 {
        let mut acc = F192::ZERO;
        for (limb, word) in [value.c0, value.c1, value.c2].into_iter().enumerate() {
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
    pub(crate) fn add_chunk(&self, start: usize, out: &mut [F192]) {
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
    fn fold_products(&self, e_lo: &[F192], e_hi: F192, out: &mut [F192]) {
        debug_assert_eq!(e_lo.len(), out.len());
        let mut head = [[0u64; 2]; BLOCK];
        let mut tail = [0u64; BLOCK];
        let mut folded = [F192::ZERO; BLOCK];
        for (e_lo, out) in e_lo.chunks(BLOCK).zip(out.chunks_mut(BLOCK)) {
            let n = e_lo.len();
            let (lo4, lo_r) = e_lo.as_chunks::<4>();
            let mut put = |i: usize, p: F192| {
                head[i] = [p.c0, p.c1];
                tail[i] = p.c2;
            };
            for (k, e_lo) in lo4.iter().enumerate() {
                for (j, p) in mul4(*e_lo, [e_hi; 4]).into_iter().enumerate() {
                    put(4 * k + j, p);
                }
            }
            for (j, &e_lo) in lo_r.iter().enumerate() {
                put(4 * lo4.len() + j, e_lo * e_hi);
            }
            let head_rows = primitives::cast_slice::<[u64; 2], [u8; 16]>(&head);
            let tail_rows = primitives::cast_slice::<u64, [u8; 8]>(&tail);
            self.fold
                .0
                .fold_block_pair(&self.fold.1, &head_rows[..n], &tail_rows[..n], &mut folded);
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
    coordinate_weights: &[F192],
    lambda: F192,
) -> DeferredRingSwitchOutput {
    let s_hat_u = transpose_s_hat(&state.s_hat_v);
    let sumcheck_claim = inner_product_base_ext(&s_hat_u, coordinate_weights);
    let scaled_weights: Vec<F192> = coordinate_weights.iter().map(|&x| lambda * x).collect();
    DeferredRingSwitchOutput {
        batched_sumcheck_claim: lambda * sumcheck_claim,
        weight: RingWeight::new(scaled_weights, state.point),
    }
}

/// The dense weight of several deferred claims, accumulated into `out`: the reference for tests.
#[cfg(test)]
pub(crate) fn combine_deferred_chunk(outputs: &[DeferredRingSwitchOutput], out: &mut [F192]) {
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
/// (LSB-first indexing, matching `build_eq_table_ext`). Materializes
/// `2^n_lo + 2^(n - n_lo)` entries instead of `2^n`; field multiplication is
/// exact, so the reconstructed entries are bit-identical to the full build.
fn build_eq_split_ext(point: &[F192]) -> (Vec<F192>, Vec<F192>) {
    let n_lo = split_n_lo(point.len());
    (build_eq_table_ext(&point[..n_lo]), build_eq_table_ext(&point[n_lo..]))
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
    s_hat_v: Vec<F192>,
    point: Vec<F192>,
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
    suffix_point: &[F192],
    precomputed_s_hat_v: Option<&[F192]>,
) -> RingSwitchProveState {
    assert_eq!(
        packed_witness.len(),
        1usize << suffix_point.len(),
        "packed witness must have 2^|suffix_point| words"
    );
    let s_hat_v = match precomputed_s_hat_v {
        Some(v) => {
            assert_eq!(v.len(), PACKING_WIDTH);
            v.to_vec()
        }
        None => {
            let (eq_lo, eq_hi) = build_eq_split_ext(suffix_point);
            let mask = eq_lo.len() - 1;
            let shift = eq_lo.len().trailing_zeros();
            let full: Vec<F192> = parallel::map_collect(packed_witness.len(), |y| eq_lo[y & mask] * eq_hi[y >> shift]);
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

    /// Number of Frobenius terms the composed batching map expands to: the
    /// F_2-dimension of `K`.
    const LINEARIZED_TERMS: usize = PACKING_WIDTH;

    #[test]
    fn deferred_batch_matches_materialized_weights() {
        let mut rng = Rng::new(0xdec0_de01_2345_6789);
        let point = rng.ext_vec(10);
        let coordinate_weights = rng.ext_vec(DEGREE_E);
        let lambdas = [rng.ext(), rng.ext()];
        let states = (0..2)
            .map(|_| RingSwitchProveState {
                s_hat_v: rng.ext_vec(PACKING_WIDTH),
                point: point.clone(),
            })
            .collect::<Vec<_>>();

        // Reference: one dense weight vector per claim, combined afterwards.
        let dense_basis = fold_ext_elems_naive(&build_eq_table_ext(&point), &coordinate_weights);
        let expected_target = states.iter().zip(lambdas).fold(F192::ZERO, |acc, (state, lambda)| {
            acc + lambda * inner_product_base_ext(&transpose_s_hat(&state.s_hat_v), &coordinate_weights)
        });
        let expected_basis = dense_basis
            .iter()
            .map(|&w| (lambdas[0] + lambdas[1]) * w)
            .collect::<Vec<_>>();

        let deferred = states
            .into_iter()
            .zip(lambdas)
            .map(|(state, lambda)| prove_finish_deferred(state, &coordinate_weights, lambda))
            .collect::<Vec<_>>();
        let deferred_target = deferred
            .iter()
            .fold(F192::ZERO, |acc, out| acc + out.batched_sumcheck_claim);
        let mut deferred_basis = vec![F192::ZERO; expected_basis.len()];
        combine_deferred_chunk(&deferred, &mut deferred_basis);

        assert_eq!(deferred_target, expected_target);
        assert_eq!(deferred_basis, expected_basis);
    }

    /// The contract between the native opener and every verifier that batches
    /// from `Phi`'s coefficients (the recursion guest, the Python reference
    /// verifier): weighting the COLUMN view by `build_coordinate_weights` must
    /// equal applying `Phi` to the ROW view and combining with `x^j`. If this
    /// drifts, the guest computes a different opening target than the prover.
    #[test]
    fn column_weights_match_the_row_side_linearized_map() {
        let mut rng = Rng::new(0xF00D_BEEF_1234_5678);
        for _ in 0..4 {
            let challenges = std::array::from_fn(|_| rng.ext());
            let s_hat_v = rng.ext_vec(PACKING_WIDTH);

            // Column side: sum_w weights[w] * t_w over the transposed K columns.
            let columns = transpose_s_hat(&s_hat_v);
            let lhs = inner_product_base_ext(&columns, &build_coordinate_weights(&challenges));

            // Row side: sum_j x^j * Phi(y_j), the guest's loop.
            let x = F192::new(2, 0, 0);
            let mut rhs = F192::ZERO;
            let mut x_pow = F192::ONE;
            for y in &s_hat_v {
                let phi = apply_composed_map(*y, &challenges);
                rhs += x_pow * phi;
                x_pow *= x;
            }
            assert_eq!(lhs, rhs, "column weights and row-side Phi disagree");
        }
    }

    /// Expanding the composition must populate every Frobenius exponent exactly
    /// once. Distinct support monomials are the property used by soundness;
    /// pointwise distinct coordinate weights are neither required nor generally
    /// true for every challenge tuple.
    #[test]
    fn composed_map_has_full_frobenius_support() {
        let mut monomials = [None; LINEARIZED_TERMS];
        monomials[0] = Some([0u64; COMPOSITION_SHIFTS.len()]);
        for (stage, &shift) in COMPOSITION_SHIFTS.iter().enumerate() {
            let previous = monomials;
            for (i, exponents) in previous.into_iter().enumerate().take(LINEARIZED_TERMS - shift) {
                if let Some(mut exponents) = exponents {
                    for exponent in &mut exponents {
                        *exponent <<= shift;
                    }
                    exponents[stage] += 1;
                    assert!(monomials[i + shift].replace(exponents).is_none());
                }
            }
        }
        let monomials: std::collections::HashSet<_> = monomials.into_iter().map(Option::unwrap).collect();
        assert_eq!(monomials.len(), LINEARIZED_TERMS);
        assert_eq!(
            monomials.iter().map(|exponents| exponents.iter().sum::<u64>()).max(),
            Some(RING_SWITCH_SOUNDNESS_DEGREE as u64)
        );

        let mut rng = Rng::new(0x1234_5678_9abc_def0);
        let challenges: [F192; COMPOSITION_SHIFTS.len()] = std::array::from_fn(|_| rng.ext());
        let mut coefficients = [F192::ZERO; LINEARIZED_TERMS];
        coefficients[0] = F192::ONE;
        for (&challenge, &shift) in challenges.iter().zip(COMPOSITION_SHIFTS.iter()) {
            let previous = coefficients;
            for (i, mut coefficient) in previous.into_iter().enumerate().take(LINEARIZED_TERMS - shift) {
                if coefficient == F192::ZERO {
                    continue;
                }
                for _ in 0..shift {
                    coefficient = coefficient.square();
                }
                coefficients[i + shift] = challenge * coefficient;
            }
        }
        assert!(coefficients.iter().all(|coefficient| *coefficient != F192::ZERO));

        let value = rng.ext();
        let mut expanded = F192::ZERO;
        let mut frobenius = value;
        for coefficient in coefficients {
            expanded += coefficient * frobenius;
            frobenius = frobenius.square();
        }
        assert_eq!(apply_composed_map(value, &challenges), expanded);
    }

    /// Reference s_hat_v: brute-force partial evaluation of each bit-column
    /// MLE at the suffix point (direct bit-extract loop, no fold kernel).
    fn s_hat_v_reference(packed: &[F64], suffix_point: &[F192]) -> Vec<F192> {
        let eq_suffix = build_eq_table_ext(suffix_point);
        (0..PACKING_WIDTH)
            .map(|i| {
                let mut acc = F192::ZERO;
                for (word, &w) in packed.iter().zip(eq_suffix.iter()) {
                    if (word.0 >> i) & 1 == 1 {
                        acc += w;
                    }
                }
                acc
            })
            .collect()
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
        let eq_suffix = build_eq_table_ext(&suffix_point);

        let s_hat_v = fold_1b_rows(&packed, &eq_suffix);
        assert_eq!(s_hat_v.len(), PACKING_WIDTH);

        // From the flat bit layout: column i is z[y * 64 + i].
        for i in 0..PACKING_WIDTH {
            let mut expected = F192::ZERO;
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
        let prefix_weights = build_eq_table_ext(&point[..LOG_PACKING]);
        let suffix_point = &point[LOG_PACKING..];

        let s_ref = s_hat_v_reference(&packed, suffix_point);
        let eq_full = build_eq_table_ext(&point);
        let mut direct = F192::ZERO;
        for (x, &w) in eq_full.iter().enumerate() {
            if bits[x] {
                direct += w;
            }
        }
        assert_eq!(
            prefix_weights
                .iter()
                .zip(&s_ref)
                .fold(F192::ZERO, |acc, (&w, &s)| acc + w * s),
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
