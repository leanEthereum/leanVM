// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//
// The rectangular (f = 64, e = 192) generalization described in the ring-switching-generalized note.

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
//!   and checked (flock sends its family itself and pins it in its lincheck
//!   terminal). This module therefore reads nothing off the stream and only has
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
//!    the claim shape [`super::whir::recursive_prover_with_basis`]
//!    proves (with `b_initial = rs_eq_ind`, `target = sumcheck_claim`).
//!    A nonzero discrepancy gives a nonzero polynomial in the six challenges;
//!    its total degree is below `2^32`, hence its failure probability is below
//!    `2^-160` before the WHIR list-size factor.
//!
//! ## Prover vs. verifier paths for `rs_eq_ind`
//!
//! - The stacked opening ring-switches one family per opening: its claims' slices combined by powers of one challenge `gamma_rs` before the map is drawn, each claim's scale sitting inside the map, so the claim at `r_suffix` with scale `c` has the weight `Phi(c·eq(r_suffix, y))` on its region (doc `leanvm` Annex A, `rs:family`).
//! - The prover keeps each claim's equality tensor factored, folds it through a
//!   small byte table, and combines the claims directly into one dense PCS
//!   weight. It never materializes a dense vector per claim.
//! - The verifier never materializes the vector: its MLE at the WHIR final point is the closed form of doc `leanvm` Annex A (`rs:weight`), with the Frobenius moved onto the point every claim shares (`rs:cost`), so a claim costs `64 L` E-multiplications and 63 squarings after one precomputation per opening, and claims at prefixes of one point share their products.

use super::pack::PACKING_WIDTH;
use super::tensor_algebra::{DEGREE_E, transpose_s_hat};
use super::whir::inner_product_base_ext;
use fiat_shamir::transcript::Challenger;
use primitives::field::{F64, F192};
use primitives::multilinear::eq_table;

/// Total degree of the six-challenge composed batching map. This is the
/// conservative degree used by the WHIR list-size soundness accounting.
pub const RING_SWITCH_SOUNDNESS_DEGREE: usize =
    (1usize << 31) + (1usize << 15) + (1usize << 7) + (1usize << 3) + (1usize << 1) + 1;

/// Frobenius shifts in the order in which the two-term maps are composed.
/// Descending order bounds every challenge's exponent by `2^31`.
pub const COMPOSITION_SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];

/// Number of Frobenius terms the composed batching map expands to: the `F_2`-dimension of `K`.
pub const LINEARIZED_TERMS: usize = PACKING_WIDTH;

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
/// six challenges instead of the 192 weights. Expanding the composition puts a distinct monomial at every Frobenius
/// exponent `0..64`: writing `k = sum_p k_p·2^(5-p)` for the binary digits of
/// `k`, the coefficient is `C_k = prod_{p : k_p = 1} f_p^(2^(k mod 2^(5-p)))`,
/// which is what `python-verifier`'s coefficient table builds. Applying the composed
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
    // b_w has only bit w set: bits 0..64 are K's power basis, and bits 64/128
    // shift it by Y / Y^2.
    let basis = |w: usize| match w / PACKING_WIDTH {
        0 => F192::new(1u64 << (w % PACKING_WIDTH), 0, 0),
        1 => F192::new(0, 1u64 << (w % PACKING_WIDTH), 0),
        _ => F192::new(0, 0, 1u64 << (w % PACKING_WIDTH)),
    };
    (0..DEGREE_E)
        .map(|w| apply_composed_map(basis(w), challenges))
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
pub fn sample_map_challenges(ch: &mut impl Challenger) -> [F192; COMPOSITION_SHIFTS.len()] {
    std::array::from_fn(|_| ch.sample())
}

// ---------------------------------------------------------------------------
// Building blocks
// ---------------------------------------------------------------------------

/// Standard inner product `sum_i a[i] * b[i]` over E.
pub fn inner_product_ext(a: &[F192], b: &[F192]) -> F192 {
    assert_eq!(a.len(), b.len());
    let mut acc = F192::ZERO;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc += x * y;
    }
    acc
}

/// Compute the slice-MLE vector `s_hat_v` (length 64) from a packed witness
/// and a tensor-expanded suffix point.
///
/// `packed_witness[y] in K` for `y in 0..2^L`; `suffix_tensor` is
/// `eq(r_suffix, .)` over the same range (from
/// the `eq` table builder).
///
/// Output: `s_hat_v[i] = sum_y bit_i(packed_witness[y]) * suffix_tensor[y]`
/// for `i in 0..64` (bit i = polynomial-basis coordinate of the u64).
///
/// The prover takes these from lincheck, so this is the reference for tests and the unprepared fallback.
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
    for (av, bv) in a.iter_mut().zip(b) {
        *av += bv;
    }
    a
}

/// Number of bytes in an E element (= lookup tables for the fold).
const FOLD_N_BYTES: usize = 24;
/// Entries per byte-lookup table.
const FOLD_TABLE_SIZE: usize = 256;

/// Build the 24x256 byte-lookup table for [`fold_ext_elems`]:
/// `table[k * 256 + v] = sum_{bit b set in v} coordinate_weights[k * 8 + b]`.
/// Byte order: bytes 0..8 are the little-endian bytes of `c0` (bits 0..64),
/// bytes 8..16 those of `c1` (bits 64..128), and bytes 16..24 those of `c2`.
fn build_fold_byte_table_ext(coordinate_weights: &[F192]) -> Box<FoldByteTable> {
    assert_eq!(coordinate_weights.len(), DEGREE_E);
    let mut tables: Box<FoldByteTable> = Box::new([[F192::ZERO; FOLD_TABLE_SIZE]; FOLD_N_BYTES]);
    for byte_idx in 0..FOLD_N_BYTES {
        let bit_base = byte_idx * 8;
        for value in 0..FOLD_TABLE_SIZE {
            let mut acc = F192::ZERO;
            for bit_in_byte in 0..8 {
                if (value >> bit_in_byte) & 1 == 1 {
                    acc += coordinate_weights[bit_base + bit_in_byte];
                }
            }
            tables[byte_idx][value] = acc;
        }
    }
    tables
}

/// The byte table as its shape rather than as a flat run: a `u8` cannot index a
/// 256-entry row out of bounds and the row index is a constant of the unrolled
/// loop, so neither lookup carries a bounds check and the row stride folds into
/// the address. Flat, this is 24 bounds checks and 24 stride multiplies per
/// output slot, and the address registers they force live do not fit.
type FoldByteTable = [[F192; FOLD_TABLE_SIZE]; FOLD_N_BYTES];

/// One folded output slot: `sum_{k=0..24} tables[k][byte_k(elem)]`, tree-reduced
/// so the XORs pipeline.
#[inline(always)]
fn fold_one_slot_ext(elem: F192, tables: &FoldByteTable) -> F192 {
    let bytes = [elem.c0.to_le_bytes(), elem.c1.to_le_bytes(), elem.c2.to_le_bytes()];
    let mut acc = F192::ZERO;
    for (word, word_bytes) in bytes.iter().enumerate() {
        for (byte, &value) in word_bytes.iter().enumerate() {
            acc += tables[8 * word + byte][value as usize];
        }
    }
    acc
}

/// A claim's weight `Phi(scale·eq(point, ·))`, kept factored: the split eq
/// tensor, its high half scaled, and the byte table of `Phi` on the
/// coordinates, so combining claims needs only additions.
pub(crate) struct DeferredWeight {
    eq_lo: Vec<F192>,
    eq_hi: Vec<F192>,
    table: Box<FoldByteTable>,
}

/// The weight `Phi(scale·eq(point, ·))` of a claim, without materializing it.
pub(crate) fn deferred_weight(point: &[F192], scale: F192, coordinate_weights: &[F192]) -> DeferredWeight {
    let (eq_lo, mut eq_hi) = build_eq_split_ext(point);
    for e in &mut eq_hi {
        *e *= scale;
    }
    DeferredWeight {
        eq_lo,
        eq_hi,
        table: build_fold_byte_table_ext(coordinate_weights),
    }
}

/// Fold several deferred weights into `out[start..]` of their combined dense
/// basis, accumulating, so `out` arrives zeroed. No per-claim dense vector is
/// allocated or read back. `start` is an offset into the basis, which lets a
/// caller cover it one cache-resident window at a time.
pub(crate) fn combine_deferred_chunk(outputs: &[DeferredWeight], start: usize, out: &mut [F192]) {
    for claim in outputs {
        let block_len = claim.eq_lo.len();
        assert!(start + out.len() <= block_len * claim.eq_hi.len());
        let mut done = 0;
        while done < out.len() {
            let index = start + done;
            let lo = index % block_len;
            let len = (block_len - lo).min(out.len() - done);
            let e_hi = claim.eq_hi[index / block_len];
            for (slot, &e_lo) in out[done..done + len].iter_mut().zip(&claim.eq_lo[lo..lo + len]) {
                *slot += fold_one_slot_ext(e_lo * e_hi, &claim.table);
            }
            done += len;
        }
    }
}

/// Split point for the factored eq build: low half sized ~n/2 (min 4, the
/// point where two factor tables beat one full build).
fn split_n_lo(n: usize) -> usize {
    (n / 2).clamp(4.min(n), n)
}

/// Factored eq tensor: `eq(point, y) = eq_lo[y & (2^n_lo - 1)] * eq_hi[y >> n_lo]`
/// (LSB-first indexing, matching the full `eq` table). Materializes
/// `2^n_lo + 2^(n - n_lo)` entries instead of `2^n`; field multiplication is
/// exact, so the reconstructed entries are bit-identical to the full build.
fn build_eq_split_ext(point: &[F192]) -> (Vec<F192>, Vec<F192>) {
    let n_lo = split_n_lo(point.len());
    (eq_table(&point[..n_lo]), eq_table(&point[n_lo..]))
}

// ---------------------------------------------------------------------------
// Prover / verifier of the reduction
// ---------------------------------------------------------------------------

/// The 64 bit-slice values of `packed_witness` at `suffix_point`, folded out of the witness.
///
/// The prover takes a claim's slices from the reduction that sent them, so this serves a caller that has none.
pub fn slices_at(packed_witness: &[F64], suffix_point: &[F192]) -> Vec<F192> {
    assert_eq!(
        packed_witness.len(),
        1usize << suffix_point.len(),
        "packed witness must have 2^|suffix_point| words"
    );
    let (eq_lo, eq_hi) = build_eq_split_ext(suffix_point);
    let mask = eq_lo.len() - 1;
    let shift = eq_lo.len().trailing_zeros();
    let full: Vec<F192> = parallel::map_collect(packed_witness.len(), |y| eq_lo[y & mask] * eq_hi[y >> shift]);
    fold_1b_rows(packed_witness, &full)
}

/// The family's target: given the shared coordinate weights, `Σ_w Phi(b_w)·t_w`
/// over the transposed slices, which is `Σ_i x^i·Phi(s_i)`. Pair it with the closed-form weight
/// at the WHIR final point, which takes the same map's challenges, so `rs_eq_ind` is never built.
pub fn verify_finish(s_hat_v: &[F192], coordinate_weights: &[F192]) -> F192 {
    inner_product_base_ext(&transpose_s_hat(s_hat_v), coordinate_weights)
}

// ---------------------------------------------------------------------------
// Closed-form evaluation of MLE(rs_eq_ind)
// ---------------------------------------------------------------------------

/// `v^(2^-j)` at index `j`, for `j < 64`. Squaring from `v^(2^128) = v^(2^-64)`, which costs only two Frobenius maps, climbs to `v^(2^-1)` in 63 squarings.
fn inverse_frobenius_ladder(v: F192) -> [F192; LINEARIZED_TERMS] {
    let mut ladder = [v; LINEARIZED_TERMS];
    let mut power = v.frobenius().frobenius();
    for slot in ladder[1..].iter_mut().rev() {
        power = power.square();
        *slot = power;
    }
    ladder
}

/// What every claim weight at a prefix of one query point shares: the query's inverse Frobenius ladders and the map's coefficients shifted to match. Each ring of a stacked opening is evaluated at a prefix of the same terminal point, so one of these serves the whole opening.
pub struct RsEqQuery {
    /// `C_k^(2^-k)` at index `k`, `C_k` the map's Frobenius coefficients.
    coefficients: [F192; LINEARIZED_TERMS],
    /// `1 + q_n^(2^-k)` at `[n][k]`.
    ladders: Vec<[F192; LINEARIZED_TERMS]>,
}

impl RsEqQuery {
    /// Precompute for `query` under the map drawn from `challenges` (those of [`build_coordinate_weights`]).
    pub fn new(challenges: &[F192; COMPOSITION_SHIFTS.len()], query: &[F192]) -> Self {
        // With d_p = COMPOSITION_SHIFTS[p], C_k = prod_{p : k & d_p} f_p^(2^(k mod d_p)), so C_k^(2^-k) = prod_{p : k & d_p} f_p^(2^-(k - k mod d_p)).
        let challenge_ladders = challenges.map(inverse_frobenius_ladder);
        let coefficients = std::array::from_fn(|k| {
            COMPOSITION_SHIFTS
                .iter()
                .zip(&challenge_ladders)
                .filter(|&(&shift, _)| k & shift != 0)
                .map(|(&shift, ladder)| ladder[k - k % shift])
                .reduce(|acc, factor| acc * factor)
                .unwrap_or(F192::ONE)
        });
        let ladders = query
            .iter()
            .map(|&q| inverse_frobenius_ladder(q).map(|power| F192::ONE + power))
            .collect();
        Self { coefficients, ladders }
    }
}

/// The terms `C_k^(2^-k) P_k` of a claim's weight at several prefixes of one suffix point: entry `i` is at `z_vals[..lengths[i]]`, before any scale.
///
/// Doc `leanvm` Annex A (`rs:weight`) gives `MLE(Phi(scale·eq(z, ·)))(q) = sum_{k<64} C_k scale^(2^k) prod_n (1 + z_n^(2^k) + q_n)`.
/// Each factor is `(1 + z_n + q_n^(2^-k))^(2^k)`, so the sum is `sum_k (C_k^(2^-k) scale P_k)^(2^k)` with `P_k = prod_n (1 + z_n + q_n^(2^-k))`.
/// Every Frobenius power falls on the shared query, and the outer powers close by the linearized Horner rule.
///
/// The products `P_k` of a prefix extend to the next coordinate by one product each, so one pass over the longest prefix serves every length. Terms are additive under the closing Horner rule, the Frobenius being additive: claims on one region add their scaled terms and close once.
///
/// Panics if a length exceeds `z_vals` or the query.
pub fn rs_eq_prefix_terms(z_vals: &[F192], query: &RsEqQuery, lengths: &[usize]) -> Vec<[F192; LINEARIZED_TERMS]> {
    let longest = lengths.iter().copied().max().unwrap_or(0);
    assert!(
        longest <= z_vals.len() && longest <= query.ladders.len(),
        "rs_eq_prefix_terms: a prefix is longer than the suffix point or the query"
    );
    let mut out = vec![[F192::ZERO; LINEARIZED_TERMS]; lengths.len()];
    let take = |n: usize, products: &[F192; LINEARIZED_TERMS], out: &mut [[F192; LINEARIZED_TERMS]]| {
        for (slot, _) in out.iter_mut().zip(lengths).filter(|&(_, &len)| len == n) {
            *slot = *products;
        }
    };
    let mut products = query.coefficients;
    take(0, &products, &mut out);
    for (n, (&z, ladder)) in z_vals.iter().zip(&query.ladders).take(longest).enumerate() {
        for (p, &power) in products.iter_mut().zip(ladder) {
            *p *= power + z;
        }
        take(n + 1, &products, &mut out);
    }
    out
}

/// The linearized Horner rule that closes the Frobenius sum: `acc <- acc^2 + term` from the last term down.
pub fn close_rs_eq(terms: &[F192; LINEARIZED_TERMS]) -> F192 {
    let (&last, rest) = terms.split_last().expect("the map has 64 terms");
    rest.iter().rev().fold(last, |acc, &term| acc.square() + term)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkle::Hash;
    use crate::pack::LOG_PACKING;
    use crate::whir::{VerifierConfig, commit, recursive_prover_with_basis, recursive_verifier_with_basis_succinct};
    use crate::whir_config::tests::test_config_for;
    use fiat_shamir::transcript::{Proof, ProverState, VerifierState};
    use primitives::test_util::Rng;
    use std::collections::HashSet;
    use zk_alloc::ArenaVec;

    /// Compute `rs_eq_ind`, the transparent E-valued weight vector over the
    /// suffix domain: `rs_eq_ind[y] = Phi(suffix_tensor[y])` where `Phi` sends
    /// E-basis bit w to `coordinate_weights[w]`, i.e.
    ///
    /// `rs_eq_ind[y] = sum_w bit_w(suffix_tensor[y]) * coordinate_weights[w]`
    ///
    /// Naive reference: a per-position bit-scan over the three 64-bit limbs.
    /// See [`fold_ext_elems`] for the bytewise-table production version.
    fn fold_ext_elems_naive(suffix_tensor: &[F192], coordinate_weights: &[F192]) -> Vec<F192> {
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

    // One claim's weight at the query's prefix of its length.
    fn eval_rs_eq(z_vals: &[F192], scale: F192, query: &RsEqQuery) -> F192 {
        let terms = rs_eq_prefix_terms(z_vals, query, &[z_vals.len()]);
        close_rs_eq(&terms[0].map(|term| term * scale))
    }

    /// Pack bit `64 * y + i` of `bits` into bit `i` of word `y`.
    fn pack_witness(bits: &[bool]) -> Vec<F64> {
        let word = |c: &[bool]| c.iter().rev().fold(0, |acc, &b| acc << 1 | b as u64);
        bits.chunks(PACKING_WIDTH).map(|c| F64(word(c))).collect()
    }

    #[test]
    fn a_family_at_unrelated_points_is_one_ring_switch() {
        let mut rng = Rng::new(0xdec0_de01_2345_6789);
        let n = 9;
        let packed = pack_witness(&rng.bits(1 << (n + LOG_PACKING)));
        let coordinate_weights = build_coordinate_weights(&std::array::from_fn(|_| rng.ext()));
        let gamma_rs = rng.ext();
        let points: Vec<Vec<F192>> = (0..3).map(|_| rng.ext_vec(n)).collect();

        let mut slices = vec![F192::ZERO; PACKING_WIDTH];
        let mut dense = vec![F192::ZERO; packed.len()];
        let mut weights = Vec::new();
        let mut scale = F192::ONE;
        for point in &points {
            for (slot, s) in slices.iter_mut().zip(s_hat_v_reference(&packed, point)) {
                *slot += scale * s;
            }
            let scaled: Vec<F192> = eq_table(point).iter().map(|&e| scale * e).collect();
            for (slot, w) in dense.iter_mut().zip(fold_dense(&scaled, &coordinate_weights)) {
                *slot += w;
            }
            weights.push(deferred_weight(point, scale, &coordinate_weights));
            scale *= gamma_rs;
        }
        let mut combined = vec![F192::ZERO; packed.len()];
        combine_deferred_chunk(&weights, 0, &mut combined);
        assert_eq!(combined, dense);
        assert_eq!(
            inner_product_base_ext(&packed, &combined),
            verify_finish(&slices, &coordinate_weights)
        );
    }

    /// The contract between the native opener and every verifier that batches
    /// from `Phi`'s coefficients (the Python reference verifier): weighting the COLUMN view by `build_coordinate_weights` must
    /// equal applying `Phi` to the ROW view and combining with `x^j`. If this
    /// drifts, that verifier computes a different opening target than the prover.
    #[test]
    fn column_weights_match_the_row_side_linearized_map() {
        let mut rng = Rng::new(0xF00D_BEEF_1234_5678);
        for _ in 0..4 {
            let challenges = std::array::from_fn(|_| rng.ext());
            let s_hat_v = rng.ext_vec(PACKING_WIDTH);

            // Column side: sum_w weights[w] * t_w over the transposed K columns.
            let columns = transpose_s_hat(&s_hat_v);
            let lhs = inner_product_base_ext(&columns, &build_coordinate_weights(&challenges));

            // Row side: sum_j x^j * Phi(y_j).
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
        let monomials: HashSet<_> = monomials.into_iter().map(Option::unwrap).collect();
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

    /// The byte-table fold of a dense tensor: the kernel `combine_deferred_chunk`
    /// runs per slot, without its factored-eq slot generation.
    fn fold_dense(tensor: &[F192], coordinate_weights: &[F192]) -> Vec<F192> {
        let tables = build_fold_byte_table_ext(coordinate_weights);
        tensor.iter().map(|&e| fold_one_slot_ext(e, &tables)).collect()
    }

    /// Reference s_hat_v: brute-force partial evaluation of each bit-column
    /// MLE at the suffix point (direct bit-extract loop, no fold kernel).
    fn s_hat_v_reference(packed: &[F64], suffix_point: &[F192]) -> Vec<F192> {
        let eq_suffix = eq_table(suffix_point);
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
        let eq_suffix = eq_table(&suffix_point);

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

    /// The prefix x suffix split factors the bit-MLE, and `slices_at`'s
    /// witness fold reproduces the reference slice values.
    #[test]
    fn slices_factor_the_bit_mle() {
        let m = 10;
        let mut rng = Rng::new(2);
        let bits = rng.bits(1usize << m);
        let packed = pack_witness(&bits);
        let point = rng.ext_vec(m);
        let prefix_weights = eq_table(&point[..LOG_PACKING]);
        let suffix_point = &point[LOG_PACKING..];

        let s_ref = s_hat_v_reference(&packed, suffix_point);
        let eq_full = eq_table(&point);
        let mut direct = F192::ZERO;
        for (x, &w) in eq_full.iter().enumerate() {
            if bits[x] {
                direct += w;
            }
        }
        assert_eq!(
            inner_product_ext(&prefix_weights, &s_ref),
            direct,
            "prefix x suffix split must factor the MLE"
        );
        assert_eq!(
            slices_at(&packed, suffix_point),
            s_ref,
            "the witness fold must reproduce the reference slices"
        );
    }

    /// The byte-table fold behind `combine_deferred_chunk` must match the naive
    /// bit-scan on arbitrary (not necessarily eq-structured) input.
    #[test]
    fn rs_eq_ind_fast_matches_naive() {
        let mut rng = Rng::new(3);
        let tensor = rng.ext_vec(1usize << 8);
        let coordinate_weights = rng.ext_vec(DEGREE_E);
        assert_eq!(
            fold_dense(&tensor, &coordinate_weights),
            fold_ext_elems_naive(&tensor, &coordinate_weights)
        );
    }

    /// `eval_rs_eq` against the definition: materialize `rs_eq_ind = Phi(c·eq(z, .))` and take its MLE at the query's prefix with the eq table. One precomputed query serves every suffix length up to its own, as in the stacked opening, and one walk of the longest point serves each of its prefixes.
    #[test]
    fn eval_rs_eq_matches_dense() {
        let max_len = 8;
        let mut rng = Rng::new(4);
        for _ in 0..3 {
            let challenges = std::array::from_fn(|_| rng.ext());
            let coordinate_weights = build_coordinate_weights(&challenges);
            let query = rng.ext_vec(max_len);
            let rs_query = RsEqQuery::new(&challenges, &query);
            let lead = rng.ext_vec(max_len);
            let lengths: Vec<usize> = (0..=max_len).rev().collect();
            let prefix_terms = rs_eq_prefix_terms(&lead, &rs_query, &lengths);
            for (&len, terms) in lengths.iter().zip(&prefix_terms) {
                let z = &lead[..len];
                let scale = rng.ext();
                let scaled: Vec<F192> = eq_table(z).iter().map(|&e| scale * e).collect();
                let rs_eq_ind = fold_dense(&scaled, &coordinate_weights);
                let dense = inner_product_ext(&rs_eq_ind, &eq_table(&query[..len]));
                assert_eq!(eval_rs_eq(z, scale, &rs_query), dense, "suffix length {len}");
                assert_eq!(close_rs_eq(&terms.map(|t| t * scale)), dense, "prefix length {len}");
            }
        }
    }

    // -- end-to-end: reduction + whir opening --------------------------

    struct E2e {
        vc: VerifierConfig,
        log_n: usize,
        prefix_weights: Vec<F192>,
        suffix_point: Vec<F192>,
        claim: F192,
        root: Hash,
        rs_s_hat_v: Vec<F192>,
        fs: Proof,
    }

    const E2E_DOMAIN: &[u8] = b"ring-switch-e2e-test";

    /// Full prover pipeline: random bit witness, pack, commit, ring switch
    /// (plain-point eq weights or a caller-supplied generalized weight
    /// vector), then the whir opening on (rs_eq_ind, sumcheck_claim),
    /// all over one continuous transcript.
    fn prove_e2e(m: usize, seed: u64, generalized_weights: bool) -> E2e {
        let mut rng = Rng::new(seed);
        let bits = rng.bits(1usize << m);
        let packed = pack_witness(&bits);
        let log_n = m - LOG_PACKING;
        let pc = test_config_for(log_n);
        let (cm, pd) = commit(&packed, log_n, pc.initial_k(), pc.log_inv_rates()[0]);

        let suffix_point = rng.ext_vec(log_n);
        let prefix_weights: Vec<F192> = if generalized_weights {
            // Synthetic non-eq weights (e.g. standing in for phi_8 Lagrange
            // weights): any 64 E-values work.
            rng.ext_vec(PACKING_WIDTH)
        } else {
            eq_table(&rng.ext_vec(LOG_PACKING))
        };
        let claim = inner_product_ext(&prefix_weights, &s_hat_v_reference(&packed, &suffix_point));

        // One family of one claim: its slices, the map, then its target and its weight at a scale of one.
        let mut ps = ProverState::from_label(E2E_DOMAIN);
        let rs_s_hat_v = slices_at(&packed, &suffix_point);
        let coordinate_weights = build_coordinate_weights(&sample_map_challenges(&mut ps));
        let sumcheck_claim = verify_finish(&rs_s_hat_v, &coordinate_weights);
        let weight = deferred_weight(&suffix_point, F192::ONE, &coordinate_weights);
        let mut rs_eq_ind = vec![F192::ZERO; packed.len()];
        combine_deferred_chunk(&[weight], 0, &mut rs_eq_ind);
        assert_eq!(inner_product_base_ext(&packed, &rs_eq_ind), sumcheck_claim);
        recursive_prover_with_basis(
            &pc,
            log_n,
            &packed,
            ArenaVec::from_slice(&rs_eq_ind),
            sumcheck_claim,
            &pd.codeword,
            &pd.merkle_tree,
            &mut ps,
        );
        E2e {
            vc: pc,
            log_n,
            prefix_weights,
            suffix_point,
            claim,
            root: cm.root,
            rs_s_hat_v,
            fs: ps.into_proof(),
        }
    }

    /// Finish the caller-supplied slices against the shared map: the verifier's
    /// half of the two phases, shared by both paths below. As in production, the
    /// slices ride the statement, tied to `claim` by the caller.
    fn verify_e2e_reduction(
        e: &E2e,
        vs: &mut VerifierState<'_>,
    ) -> Option<([F192; COMPOSITION_SHIFTS.len()], Vec<F192>, F192)> {
        if inner_product_ext(&e.prefix_weights, &e.rs_s_hat_v) != e.claim {
            return None;
        }
        let challenges = sample_map_challenges(vs);
        let coordinate_weights = build_coordinate_weights(&challenges);
        let sumcheck_claim = verify_finish(&e.rs_s_hat_v, &coordinate_weights);
        Some((challenges, coordinate_weights, sumcheck_claim))
    }

    /// Dense verification: rebuild `rs_eq_ind`, and let the whir verifier's
    /// terminal closure evaluate its MLE from the whole table.
    fn verify_e2e_dense(e: &E2e) -> bool {
        let mut vs = VerifierState::from_label(E2E_DOMAIN, &e.fs);
        let Some((_, coordinate_weights, sumcheck_claim)) = verify_e2e_reduction(e, &mut vs) else {
            return false;
        };
        let rs_eq_ind = fold_dense(&eq_table(&e.suffix_point), &coordinate_weights);
        recursive_verifier_with_basis_succinct(
            &e.vc,
            e.log_n,
            1 << e.vc.initial_k(),
            sumcheck_claim,
            &e.root,
            |point| inner_product_ext(&rs_eq_ind, &eq_table(point)),
            &mut vs,
        )
        .is_ok()
    }

    /// Succinct verification: no `rs_eq_ind`, the succinct whir verifier's
    /// terminal closure evaluates its MLE once via `eval_rs_eq`.
    fn verify_e2e_succinct(e: &E2e) -> bool {
        let mut vs = VerifierState::from_label(E2E_DOMAIN, &e.fs);
        let Some((challenges, _, sumcheck_claim)) = verify_e2e_reduction(e, &mut vs) else {
            return false;
        };
        let z = e.suffix_point.clone();
        recursive_verifier_with_basis_succinct(
            &e.vc,
            e.log_n,
            1 << e.vc.initial_k(),
            sumcheck_claim,
            &e.root,
            |point| eval_rs_eq(&z, F192::ONE, &RsEqQuery::new(&challenges, point)),
            &mut vs,
        )
        .is_ok()
    }

    #[test]
    fn end_to_end_plain_point() {
        for (m, seed) in [(13usize, 10u64), (17, 11)] {
            let e = prove_e2e(m, seed, false);
            assert!(verify_e2e_dense(&e), "dense e2e rejected at m={m}");
            assert!(verify_e2e_succinct(&e), "succinct e2e rejected at m={m}");
        }
    }

    #[test]
    fn end_to_end_generalized_weights() {
        let e = prove_e2e(13, 12, true);
        assert!(verify_e2e_dense(&e), "dense e2e (generalized) rejected");
        assert!(verify_e2e_succinct(&e), "succinct e2e (generalized) rejected");
    }

    /// Tampering: a slice flip breaks the caller's claim check; a
    /// claim-preserving forgery (two slices adjusted so the weighted sum is
    /// unchanged) passes that check but diverges the ring-switch target, so the
    /// whir opening must reject it. A tampered claim value, or any whir stream
    /// word, is rejected too. Dense and succinct paths must agree throughout.
    #[test]
    fn end_to_end_rejects_tampering() {
        let e = prove_e2e(13, 13, false);
        let with = |s_hat_v: Vec<F192>, claim: F192, fs: Proof| E2e {
            rs_s_hat_v: s_hat_v,
            vc: e.vc.clone(),
            log_n: e.log_n,
            prefix_weights: e.prefix_weights.clone(),
            suffix_point: e.suffix_point.clone(),
            claim,
            root: e.root,
            fs,
        };

        // Plain slice flip: caught by the claim check.
        let mut s = e.rs_s_hat_v.clone();
        s[5].c1 ^= 1;
        let bad = with(s, e.claim, e.fs.clone());
        assert!(!verify_e2e_dense(&bad), "flipped slice accepted");
        assert!(!verify_e2e_succinct(&bad), "flipped slice accepted (succinct)");

        // Claim-preserving forgery: s'_1 = s_1 + d, s'_0 = s_0 + w_1*d/w_0
        // keeps sum_i w_i s'_i = claim, so the claim check passes; the ring
        // switch must still reject, its target and weights diverging from what
        // the whir proof was built for.
        let mut rng = Rng::new(99);
        let d = rng.ext();
        let (w0, w1) = (e.prefix_weights[0], e.prefix_weights[1]);
        assert!(!w0.is_zero() && !d.is_zero());
        let mut s = e.rs_s_hat_v.clone();
        s[1] += d;
        s[0] += w1 * d * w0.inv();
        let bad = with(s, e.claim, e.fs.clone());
        assert_eq!(
            inner_product_ext(&bad.prefix_weights, &bad.rs_s_hat_v),
            e.claim,
            "forgery must be claim-preserving for this test to bite"
        );
        assert!(!verify_e2e_dense(&bad), "claim-preserving forgery accepted (dense)");
        assert!(
            !verify_e2e_succinct(&bad),
            "claim-preserving forgery accepted (succinct)"
        );

        // Tampered claim value.
        let bad = with(e.rs_s_hat_v.clone(), e.claim + F192::ONE, e.fs.clone());
        assert!(!verify_e2e_dense(&bad), "tampered claim accepted");
        assert!(!verify_e2e_succinct(&bad), "tampered claim accepted (succinct)");

        // Tampered whir stream word.
        let mut fs = e.fs.clone();
        fs.stream[0] += F192::ONE;
        let bad = with(e.rs_s_hat_v.clone(), e.claim, fs);
        assert!(!verify_e2e_dense(&bad), "tampered stream word accepted");
        assert!(!verify_e2e_succinct(&bad), "tampered stream word accepted (succinct)");
    }
}
