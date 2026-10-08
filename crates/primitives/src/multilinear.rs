// CREDIT: https://github.com/succinctlabs/flock (`build_eq` and the skip domain's Lagrange weights), MIT OR Apache-2.0.
//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`). Sumchecks here consume variables from either end, so folding
//! and `eq`-marginalization come in low and high variants. Committed data is
//! `K`-valued (`F64`) while randomness is `E`-valued (`F192`), so the first
//! fold of a committed table also lifts it into `E`.

use crate::{
    F192MixedAccumulator, F192PackedUnreduced, F192Unreduced, Field, PackedFieldExtension, PackedValue,
    PrimeCharacteristicRing,
};
use p3_field::ExtensionField;

use std::mem::MaybeUninit;

use self::PHI_8_TABLE_192 as PHI_8_TABLE;
use crate::{F8, F64, F192};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
use crate::{F192_LANES, F192Packed};
use std::sync::LazyLock;

/// Coefficient lanes selected by the upstream field backend.
type BasePacking = <F64 as Field>::Packing;
/// Extension values stored across those coefficient lanes.
type ExtPacking = <F192 as ExtensionField<F64>>::ExtensionPacking;
/// Number of values covered by one upstream mixed or extension product.
const EXT_LANES: usize = BasePacking::WIDTH;

/// Load a complete group using the extension over `F64`, including the scalar packing.
#[inline]
fn load_extension_lanes(values: &[F192]) -> ExtPacking {
    <ExtPacking as PackedFieldExtension<F64, F192>>::from_ext_slice(values)
}

/// Store every lane using the same coefficient field as the load.
#[inline]
fn store_extension_lanes(values: ExtPacking, out: &mut [F192]) {
    <ExtPacking as PackedFieldExtension<F64, F192>>::to_ext_slice(&values, out);
}

/// Multilinear interpolation in one variable over `E`: `lo + t·(lo+hi)`, the
/// char-2 form of `(1−t)·lo + t·hi`.
#[inline]
pub fn interp(lo: F192, hi: F192, t: F192) -> F192 {
    lo + t * (lo + hi)
}

/// Mixed interpolation: two `K` endpoints against an `E` parameter, one
/// `mul_base` (`lo + t·(lo+hi)` with `lo, hi ∈ K`).
#[inline]
pub fn interp_k(lo: F64, hi: F64, t: F192) -> F192 {
    F192::from(lo) + (t * (lo + hi))
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)`. For Boolean `r`, this is the indicator
/// of `x = r`; for arbitrary `r`, it is the multilinear interpolation weight.
pub fn eq_eval(r: &[F192], x: &[F192]) -> F192 {
    debug_assert_eq!(r.len(), x.len());
    r.iter()
        .zip(x)
        .fold(F192::ONE, |acc, (&ri, &xi)| acc * (F192::ONE + ri + xi))
}

/// The `eq(r, ·)` table over `n = r.len()` variables. See [`fill_eq_table_uninit`].
pub fn eq_table(r: &[F192]) -> Vec<F192> {
    eq_table_seeded(r, F192::ONE)
}

/// The table of `seed * eq(r, .)` over `n = r.len()` variables, in LSB-first order.
pub fn eq_table_seeded(r: &[F192], seed: F192) -> Vec<F192> {
    // One entry per point of the cube: 2^n.
    let len = 1usize << r.len();

    // Filled in place in the spare capacity, so no slot is zeroed first.
    let mut eq = Vec::with_capacity(len);
    fill_eq_table_uninit(r, seed, &mut eq.spare_capacity_mut()[..len]);
    // SAFETY: the fill writes all `len` entries.
    unsafe { eq.set_len(len) };
    eq
}

/// Fill `out` with `seed * eq(r, .)`, in LSB-first order. Every entry is written before it is read.
///
/// A small table doubles a level at a time on the calling thread.
///
/// A large one is a tensor product, written in one parallel pass:
///
/// ```text
///     out[h * 2^L + l] = high[h] * low[l],    low = eq(r[..L]),  high = seed * eq(r[L..])
/// ```
///
/// `low` stays in L1, so each entry costs one product and one store, with no level-by-level rereads.
/// A caller inside a dispatch must keep the table below `EQ_PAR_LEN`.
pub fn fill_eq_table_uninit(r: &[F192], seed: F192, out: &mut [MaybeUninit<F192>]) {
    assert_eq!(out.len(), 1usize << r.len(), "out must have length 2^r.len()");
    if out.len() < EQ_PAR_LEN {
        return fill_eq_doubling(r, seed, out);
    }
    let (r_low, r_high) = r.split_at(EQ_LOW_VARS);
    let low = eq_table(r_low);
    let high = eq_table_seeded(r_high, seed);
    let rows = parallel::recommended_chunk_size(high.len());
    parallel::chunks_mut(out, rows * low.len(), |c, chunk| {
        for (row, &w) in chunk.chunks_exact_mut(low.len()).zip(&high[c * rows..]) {
            let weight = ExtPacking::from(w);
            for (dst, src) in row
                .as_chunks_mut::<EXT_LANES>()
                .0
                .iter_mut()
                .zip(low.as_chunks::<EXT_LANES>().0)
            {
                let product = weight * load_extension_lanes(src);
                let mut values = [F192::ZERO; EXT_LANES];
                store_extension_lanes(product, &mut values);
                dst.write_copy_of_slice(&values);
            }
        }
    });
}

/// Tables below this size are built on the calling thread.
const EQ_PAR_LEN: usize = 1 << 16;

/// The variables of the L1-resident factor of a large `eq` table.
const EQ_LOW_VARS: usize = 10;

/// The level-by-level `eq` build: each level writes the high half from the low half, then rewrites the low half.
///
/// In characteristic 2 the low child is the high child plus the parent, so each pair costs one product.
fn fill_eq_doubling(r: &[F192], seed: F192, out: &mut [MaybeUninit<F192>]) {
    out[0].write(seed);
    for (i, &rk) in r.iter().enumerate() {
        let half = 1usize << i;
        let (lo, hi) = out[..2 * half].split_at_mut(half);
        // SAFETY: the low half was initialized at earlier levels.
        let lo = unsafe { &mut *(lo as *mut [MaybeUninit<F192>] as *mut [F192]) };
        let (lo_packed, lo_tail) = lo.as_chunks_mut::<EXT_LANES>();
        let (hi_packed, hi_tail) = hi.as_chunks_mut::<EXT_LANES>();
        let weight = ExtPacking::from(rk);
        for (l, h) in lo_packed.iter_mut().zip(hi_packed) {
            let product = weight * load_extension_lanes(l);
            let mut values = [F192::ZERO; EXT_LANES];
            store_extension_lanes(product, &mut values);
            h.write_copy_of_slice(&values);
            for (value, product) in l.iter_mut().zip(values) {
                *value += product;
            }
        }
        for (l, h) in lo_tail.iter_mut().zip(hi_tail) {
            let p = *l * rk;
            h.write(p);
            *l += p;
        }
    }
}

/// Below this a parallel dispatch costs more than the fold it replaces.
const PAR_THRESHOLD: usize = 1 << 12;

/// The mixed fold: bind the lowest variable of a `K`-table to an
/// `E`-challenge, producing the `E`-table the remaining rounds fold. One
/// `mul_base` per output entry.
fn fold_low_k(table: &[F64], chi: F192) -> Vec<F192> {
    debug_assert_eq!(table.len() % 2, 0);
    (0..table.len() / 2)
        .map(|i| interp_k(table[2 * i], table[2 * i + 1], chi))
        .collect()
}

/// Bind the highest variable of a `K`-table and lift the result into `E`.
///
/// Eight entries share one batched mixed product ([`mul_base8`]).
pub fn fold_high_k(table: &[F64], chi: F192) -> Vec<F192> {
    debug_assert_eq!(table.len() % 2, 0);
    let (lo, hi) = table.split_at(table.len() / 2);
    let mut out = Vec::with_capacity(lo.len());
    let (out8, out_tail) = out.spare_capacity_mut()[..lo.len()].as_chunks_mut::<8>();
    let ((lo8, lo_tail), (hi8, hi_tail)) = (lo.as_chunks::<8>(), hi.as_chunks::<8>());
    for ((o, l), h) in out8.iter_mut().zip(lo8).zip(hi8) {
        let p = mul_base8(chi, std::array::from_fn(|i| l[i] + h[i]));
        for i in 0..8 {
            o[i].write(F192::from(l[i]) + p[i]);
        }
    }
    for ((o, &l), &h) in out_tail.iter_mut().zip(lo_tail).zip(hi_tail) {
        o.write(interp_k(l, h, chi));
    }
    // SAFETY: both loops together write every entry.
    unsafe { out.set_len(lo.len()) };
    out
}

/// Bind the highest free variable of `table` to `chi` in place: `table[i] =
/// interp(table[i], table[i + half], chi)`. Binding from the top down leaves the
/// low variables, the ones every table of a batch shares, for last.
pub fn fold_high_inplace(table: &mut Vec<F192>, chi: F192) {
    debug_assert_eq!(table.len() % 2, 0);
    let half = table.len() / 2;
    {
        // Split once rather than index twice: indexing reloads the data pointer
        // and length through the container every iteration, since nothing proves
        // they do not alias the elements, and pays a bounds check for it.
        let (lo, hi) = (**table).split_at_mut(half);
        interp_into(lo, hi, chi);
    }
    table.truncate(half);
}

/// `lo[i] = interp(lo[i], hi[i], chi)`, using every lane of the upstream packing.
fn interp_into(lo: &mut [F192], hi: &[F192], chi: F192) {
    let ((lo_packed, lo_tail), (hi_packed, hi_tail)) = (lo.as_chunks_mut::<EXT_LANES>(), hi.as_chunks::<EXT_LANES>());
    let weight = ExtPacking::from(chi);
    for (l, h) in lo_packed.iter_mut().zip(hi_packed) {
        let low = load_extension_lanes(l);
        let high = load_extension_lanes(h);
        store_extension_lanes(low + weight * (low + high), l);
    }
    for (l, h) in lo_tail.iter_mut().zip(hi_tail) {
        *l = interp(*l, *h, chi);
    }
}

/// Marginalize the lowest variable out of an `eq` table (in place). `eq(r_0, 0) +
/// eq(r_0, 1) = 1`, so summing adjacent entries drops `r_0` with no multiplies,
/// versus `2^{n-1}` to rebuild the table.
pub fn shrink_eq_low(table: &mut Vec<F192>) {
    let half = table.len() / 2;
    {
        // Sliced, as in `fold_high_inplace`: reading the pair and writing the
        // sum through one slice drops the per-iteration reload and its bounds
        // check. The write index trails the read, so the in-place walk is sound.
        let t: &mut [F192] = table;
        for i in 0..half {
            let (a, b) = (t[2 * i], t[2 * i + 1]);
            t[i] = a + b;
        }
    }
    table.truncate(half);
}

/// Marginalize the highest variable out of an `eq` table (in place), the
/// [`shrink_eq_low`] counterpart for a top-down sumcheck.
pub fn shrink_eq_high(table: &mut Vec<F192>) {
    let half = table.len() / 2;
    {
        // Sliced, as in `fold_high_inplace`.
        let (lo, hi) = (**table).split_at_mut(half);
        for (l, h) in lo.iter_mut().zip(&*hi) {
            *l += *h;
        }
    }
    table.truncate(half);
}

/// The barycentric weight every node of an aligned `size`-node window of the φ₈ table shares,
/// `1 / ∏_{k≠0} φ₈(k)`. φ₈ is F2-linear on its index, so `nodes[a] + nodes[b] = φ₈(a ^ b)` (the window's
/// offset cancels) and `b ↦ a ^ b` only permutes the window, leaving every node the same product.
/// Computed once for every window size.
pub fn window_denominator(size: usize) -> F192 {
    debug_assert!(size.is_power_of_two() && size <= PHI_8_TABLE.len());
    DENOMINATORS[size.trailing_zeros() as usize]
}

/// Barycentric weights for every power-of-two window, computed once.
static DENOMINATORS: LazyLock<[F192; 9]> = LazyLock::new(|| {
    std::array::from_fn(|log| {
        (1..1 << log)
            .fold(F192::ONE, |product, k| product * PHI_8_TABLE[k])
            .invert_or_zero()
    })
});

/// `scale · Σ_i values[i] · ∏_{k≠i} (p + nodes[k])`, in one pass of three products a node and no
/// inverse; `sum` and `prefix` hold the sum and the product of the differences over the nodes seen so
/// far. For an aligned window of the φ₈ table and `scale = window_denominator(nodes.len())` it is the
/// Lagrange interpolant of `values` at `p`, exact at a node too.
pub fn barycentric_sum(nodes: &[F192], values: &[F192], p: F192, scale: F192) -> F192 {
    debug_assert_eq!(nodes.len(), values.len());
    let (mut sum, mut prefix) = (values[0] * scale, scale);
    for i in 1..nodes.len() {
        prefix *= p + nodes[i - 1];
        sum = sum * (p + nodes[i]) + values[i] * prefix;
    }
    sum
}

/// A polynomial at `point`, by Horner over its coefficients, constant first.
#[inline]
pub fn poly_eval(coeffs: &[F192], point: F192) -> F192 {
    coeffs.iter().rev().fold(F192::ZERO, |acc, &c| acc * point + c)
}

/// Evaluate the MLE of a `K`-valued truth table at an `E`-point (length `log2(len)`).
///
/// The `eq` weights factor into a low and a high table:
///
/// ```text
///     f(point) = sum_h eq(point_high, h) * sum_l eq(point_low, l) * f[h * 2^L + l]
/// ```
///
/// Each row's inner sum uses [`dot_base`] against the grouped low table.
/// The table is read once and never lifted into `E`.
pub fn mle_eval(table: &[F64], point: &[F192]) -> F192 {
    debug_assert_eq!(table.len(), 1 << point.len());
    if point.len() < 3 {
        return match point.split_first() {
            None => F192::from(table[0]),
            Some((&p0, rest)) => fold_ladder(fold_low_k(table, p0), rest),
        };
    }
    let low_vars = point.len().min(MLE_LOW_VARS);
    let low = packed_eq(&point[..low_vars]);
    let rows = table
        .chunks_exact(1 << low_vars)
        .map(|row| dot_base(&low, row))
        .collect();
    fold_ladder(rows, &point[low_vars..])
}

/// [`mle_eval`] with the rows spread over the worker pool.
/// A caller already inside a dispatch must use [`mle_eval`] to avoid nesting.
pub fn mle_eval_par(table: &[F64], point: &[F192]) -> F192 {
    debug_assert_eq!(table.len(), 1 << point.len());
    if table.len() < PAR_THRESHOLD {
        return mle_eval(table, point);
    }
    let low_vars = point.len().min(MLE_LOW_VARS);
    let low = packed_eq(&point[..low_vars]);
    let high = eq_table(&point[low_vars..]);
    let eval = |row: usize| high[row] * (dot_base(&low, &table[row << low_vars..(row + 1) << low_vars]));
    parallel::map_reduce(high.len(), || F192::ZERO, eval, |a, b| a + b)
}

/// The variables of the L1-resident low `eq` table of an MLE evaluation.
const MLE_LOW_VARS: usize = 10;

/// `eq(r, .)` packed eight weights at a time for [`dot_base`]. Needs `r.len() >= 3`.
fn packed_eq(r: &[F192]) -> Vec<[F192; 8]> {
    eq_table(r).as_chunks::<8>().0.to_vec()
}

/// Bind the remaining variables of a half-folded `E`-table, LSB-first.
fn fold_ladder(mut cur: Vec<F192>, point: &[F192]) -> F192 {
    let mut len = cur.len();
    for &p in point {
        len /= 2;
        for i in 0..len {
            cur[i] = interp(cur[2 * i], cur[2 * i + 1], p);
        }
    }
    cur[0]
}

/// The Lagrange weights of the skip domain, the first `2^k_skip` nodes of the φ₈ table, at `z`:
/// `weights[i] = ∏_{k≠i} (z + φ₈(k)) · window_denominator`, by prefix and suffix products of the
/// differences. Linear in the node count, no inverse, and exact at a node.
pub fn skip_lagrange_weights(k_skip: usize, z: F192) -> Vec<F192> {
    let n = 1usize << k_skip;
    let nodes = &PHI_8_TABLE[..n];
    let mut weights = vec![window_denominator(n); n];
    for i in 1..n {
        weights[i] = weights[i - 1] * (z + nodes[i - 1]);
    }
    let mut suffix = z + nodes[n - 1];
    for i in (1..n - 1).rev() {
        weights[i] *= suffix;
        suffix *= z + nodes[i];
    }
    if n > 1 {
        weights[0] *= suffix;
    }
    weights
}

/// The inner product `sum_i a_i * b_i` over `E`.
#[inline]
pub fn inner_product(a: &[F192], b: &[F192]) -> F192 {
    assert_eq!(a.len(), b.len());
    let mut sum = F192PackedUnreduced::default();
    let (a, a_tail) = a.as_chunks::<EXT_LANES>();
    let (b, b_tail) = b.as_chunks::<EXT_LANES>();
    for (a, b) in a.iter().zip(b) {
        sum += load_extension_lanes(a).mul_unreduced(load_extension_lanes(b));
    }
    let mut sum = sum_unreduced(sum);
    for (&a, &b) in a_tail.iter().zip(b_tail) {
        sum += a.mul_unreduced(b);
    }
    sum.reduce()
}

/// The mixed inner product `sum_i e_i * k_i`, with `k` in `K` and `e` in `E`.
#[inline]
pub fn inner_product_base(k: &[F64], e: &[F192]) -> F192 {
    assert_eq!(k.len(), e.len());
    let mut sum = F192MixedAccumulator::new();
    let (e, e_tail) = e.as_chunks::<8>();
    let (k, k_tail) = k.as_chunks::<8>();
    for (e, k) in e.iter().zip(k) {
        sum.add_dot_product(e, k);
    }
    for (&e, &k) in e_tail.iter().zip(k_tail) {
        sum.add_dot_product(&[e], &[k]);
    }
    sum.finish()
}

/// The table `eq(r, .)` as two smaller tables, `eq(r, x) = low[x mod 2^L] * high[x >> L]`.
///
/// - The low table is `eq` over the first `L` variables of `r`, the high table over the rest.
/// - Together they hold `2^L + 2^(n - L)` entries instead of `2^n`.
/// - Products are exact, so every entry equals the full table's.
#[derive(Clone, Debug)]
pub struct SplitEq {
    /// The table over the low `L` variables.
    pub low: Vec<F192>,
    /// The table over the remaining variables.
    pub high: Vec<F192>,
    /// `L`.
    low_log: usize,
}

impl SplitEq {
    /// The split with at most `max_low` low variables.
    pub fn with_low_vars(r: &[F192], max_low: usize) -> Self {
        Self::at_split(r, r.len().min(max_low))
    }

    /// The split with at most `max_high` high variables.
    pub fn with_high_vars(r: &[F192], max_high: usize) -> Self {
        Self::at_split(r, r.len() - r.len().min(max_high))
    }

    fn at_split(r: &[F192], low_log: usize) -> Self {
        Self {
            low: eq_table(&r[..low_log]),
            high: eq_table(&r[low_log..]),
            low_log,
        }
    }

    /// The number of low variables `L`.
    pub const fn low_log(&self) -> usize {
        self.low_log
    }

    /// The number of high variables.
    pub const fn high_log(&self) -> usize {
        self.high.len().trailing_zeros() as usize
    }

    /// `eq(r, x)`.
    #[inline]
    pub fn at(&self, x: usize) -> F192 {
        self.low[x & (self.low.len() - 1)] * self.high[x >> self.low_log]
    }
}

/// `[x^0, x^1, …, x^{n-1}]`: the weights of a random linear combination batched
/// with the powers of one challenge, rather than `n` independent ones.
pub fn powers(x: F192, n: usize) -> Vec<F192> {
    let mut out = Vec::with_capacity(n);
    let mut p = F192::ONE;
    for _ in 0..n {
        out.push(p);
        p *= x;
    }
    out
}

/// `g^i = x^i` in the monomial basis of `K` by square-and-multiply (`O(log i)`).
///
/// A table's tag in the bytecode is `g` raised to its index.
#[inline]
pub fn g_pow(i: usize) -> F64 {
    let mut result = F64::ONE;
    let mut base = G; // x = g
    let mut e = i;
    while e > 0 {
        if e & 1 == 1 {
            result *= base;
        }
        base = base * base;
        e >>= 1;
    }
    result
}

/// The fixed generator `g = x ∈ K`, with `ord(g) = 2^64 - 1` (pinned by a
/// field test), larger than every index any admissible
/// instance uses (the verifier's instance caps, §cpu). For `k < 64`, `g^k` is
/// the monomial `x^k` (bit `k`).
pub const G: F64 = F64::new(2);

/// MLE of the integer column `[base ^ (z << shift)]_z`, entry `z` being the element
/// whose bits are that integer's: `base + Σ_k ζ_k·x^{k+shift}`, linear, since bit `k`
/// contributes the monomial `x^k` (§sec:idxcol). What addresses the registers, RAM
/// and the bytecode: with `base` a multiple of the region's size, the XOR is the sum.
pub fn int_index_mle(base: F64, shift: u32, zeta: &[F192]) -> F192 {
    zeta.iter().enumerate().fold(F192::from(base), |acc, (k, z)| {
        acc + (*z * F64::new(1 << (k as u32 + shift)))
    })
}

/// φ₈(2ᵏ) for k ∈ [0,8): the images of the GF(2⁸) polynomial basis. All in
/// `F64` (`c1 == c2 == 0`).
const PHI_8_BASIS: [u64; 8] = [
    0x0000000000000001,
    0x033ce8beddc8a656,
    0x512620375ed2a108,
    0x0c9e636090aafc01,
    0xba4f3cd82801769c,
    0xba26e7904adb4a47,
    0x467698598926dc01,
    0x4418ae808b28bdd0,
];

const fn build_phi8_table_192() -> [F192; 256] {
    let mut table = [F192::ZERO; 256];
    let mut value = 1;
    while value < table.len() {
        let mut c0 = 0u64;
        let mut bit = 0;
        while bit < PHI_8_BASIS.len() {
            if value & (1 << bit) != 0 {
                c0 ^= PHI_8_BASIS[bit];
            }
            bit += 1;
        }
        table[value] = F192::new([F64::new(c0), F64::new(0), F64::new(0)]);
        value += 1;
    }
    table
}

/// The unique GF(2^8) subfield embedded in F192. It lies in the F64 base, so
/// both higher extension coordinates are zero.
pub static PHI_8_TABLE_192: [F192; 256] = build_phi8_table_192();

#[inline]
pub fn phi8_192(a: F8) -> F192 {
    PHI_8_TABLE_192[a.to_byte() as usize]
}

/// Two independent products.
#[inline]
pub fn mul2(a: [F192; 2], b: [F192; 2]) -> [F192; 2] {
    std::array::from_fn(|i| a[i] * b[i])
}
/// Four independent products.
#[inline]
pub fn mul4(a: [F192; 4], b: [F192; 4]) -> [F192; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    {
        unpack4(pack4(a) * pack4(b))
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    std::array::from_fn(|i| a[i] * b[i])
}
/// Eight products by coefficient-field scalars.
#[inline]
pub fn mul_base8(t: F192, k: [F64; 8]) -> [F192; 8] {
    let width = EXT_LANES;
    let mut out = [F192::ZERO; 8];
    let packed_t = ExtPacking::from(t);
    let done = 8 / width * width;
    for start in (0..done).step_by(width) {
        // One upstream mixed product fills every lane of the selected coefficient packing.
        let coefficients = BasePacking::from_fn(|lane| k[start + lane]);
        store_extension_lanes(packed_t * coefficients, &mut out[start..start + width]);
    }
    for i in done..8 {
        out[i] = t * k[i];
    }
    out
}
/// Mixed inner product in groups of eight, using Plonky3's deferred reduction.
pub fn dot_base(w: &[[F192; 8]], k: &[F64]) -> F192 {
    assert_eq!(k.len(), 8 * w.len());
    let mut sum = F192MixedAccumulator::new();
    for (w, k) in w.iter().zip(k.as_chunks::<8>().0) {
        sum.add_dot_product(w, k);
    }
    sum.finish()
}
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
/// Pack four extension elements, filling wider backend lanes with zero.
pub fn pack4(values: [F192; 4]) -> F192Packed {
    F192Packed::from_ext_fn(|i| values.get(i).copied().unwrap_or(F192::ZERO))
}
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
/// Extract four extension elements.
pub fn unpack4(value: F192Packed) -> [F192; 4] {
    std::array::from_fn(|i| value.extract(i))
}
/// Pack one complete group of extension elements.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
pub fn pack_lanes(values: [F192; F192_LANES]) -> F192Packed {
    F192Packed::from_ext_slice(&values)
}
/// Extract every element of the backend packing.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
pub fn unpack_lanes(value: F192Packed) -> [F192; F192_LANES] {
    std::array::from_fn(|i| value.extract(i))
}
/// Initialize a complete group of scalar output slots.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
pub fn store_packed(values: F192Packed, out: &mut [MaybeUninit<F192>; F192_LANES]) {
    out.write_copy_of_slice(&unpack_lanes(values));
}
/// Sum all extension elements in the backend packing.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
pub fn sum_packed(values: F192Packed) -> F192 {
    unpack_lanes(values).into_iter().sum()
}

/// Sum upstream polynomial lanes while leaving their coefficient reductions deferred.
#[inline]
#[allow(
    clippy::missing_const_for_fn,
    reason = "The upstream SIMD horizontal sum cannot be const."
)]
pub fn sum_unreduced(product: F192PackedUnreduced) -> F192Unreduced {
    #[cfg(any(
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"),
        all(target_arch = "aarch64", target_endian = "little", target_feature = "aes")
    ))]
    {
        product.sum_lanes()
    }
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"),
        all(target_arch = "aarch64", target_endian = "little", target_feature = "aes")
    )))]
    {
        product
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PrimeCharacteristicRing;
    type ReferenceVector = ([u64; 3], [u64; 3], [u64; 3], [u64; 3]);
    const VECTORS: [ReferenceVector; 4] = [
        (
            [0x950e87d7f5606615, 0x2c61275c9e6b6cf8, 0x1f00bca0042db923],
            [0x6dbca290a9eab706, 0x4c10a4fe30cffdda, 0xf26fff4cc4fd394d],
            [0x888a0fc35abaf5f6, 0x68a84cbc132b0649, 0x9fdeaf613003cabe],
            [0x8fba131ad5d46b8c, 0x1c170457f537a805, 0x3632cc098ca15135],
        ),
        (
            [0x6814a2bc786a6d2d, 0xa26b351e6c8042c5, 0x54760e7fbc051c6c],
            [0xd4c08880a5a4666d, 0x29610ae0eed8f1e7, 0xc34bd8e2fe5213e5],
            [0x2ad322ebf2f9043b, 0x8ac800aa67154c80, 0x6d0f76651d3c4d0c],
            [0xcf800ef2b83bb43a, 0xefe1c6cd064dd44c, 0x57dc5c7a60e2981b],
        ),
        (
            [0x6c50afb6e9fb123d, 0x6f28d015a2aa0b9d, 0x4e385994ebac94af],
            [0x194f9545adba52ce, 0xc675ce05588f882f, 0x57de8c051d4b7ef2],
            [0xea6b9f9d23d4a1ff, 0xd82aa6058c431457, 0x5fd4d8fda2f1e74a],
            [0x8f30fe43aa05b396, 0xe3593591eccd9efe, 0x7c5a1b128788c51f],
        ),
        (
            [0xd998efd82733e933, 0x6df216c33f8f3201, 0x11dc6f3fcb57d5d8],
            [0x8860a84722025e05, 0x33176469aa6ef630, 0x607507ebc5b864d7],
            [0xfa3a0d66cdfbc1b3, 0xbd47bd3343aad307, 0xdaf50186477f6a77],
            [0x69c8d8c24f416884, 0x4b597d648a162147, 0x95603a5d95c9512a],
        ),
    ];

    proptest::proptest! {
        #[test]
        fn batched_products_keep_lane_order(a in proptest::prelude::any::<[[u64; 3]; 4]>(), b in proptest::prelude::any::<[[u64; 3]; 4]>()) {
            let a = a.map(|x| F192::new(x.map(F64::new)));
            let b = b.map(|x| F192::new(x.map(F64::new)));
            proptest::prop_assert_eq!(mul4(a, b), std::array::from_fn(|i| a[i] * b[i]));
        }
    }

    #[test]
    fn upstream_fields_preserve_protocol_representation() {
        for (a, b, product, square) in VECTORS {
            let a = F192::new(a.map(F64::new));
            let b = F192::new(b.map(F64::new));
            assert_eq!((a * b).coefficients().map(F64::to_bits), product);
            assert_eq!(a.square().coefficients().map(F64::to_bits), square);
            let bytes: Vec<u8> = a
                .coefficients()
                .iter()
                .flat_map(|x| x.to_bits().to_le_bytes())
                .collect();
            assert_eq!(bincode::serialize(&a).unwrap(), bytes);
            assert_eq!(bincode::deserialize::<F192>(&bytes).unwrap(), a);
            assert_eq!(mul4([a; 4], [b; 4]), [a * b; 4]);
        }
        for (a, b, c) in [
            (0x01090913877ed8ed, 0x66ab35ac2768468f, 0x50c4519dc383744a),
            (0xa7715ae18f12a3b5, 0x05743059f43fa4f5, 0xeb64cd9cd9cda6df),
            (0xbd3efb4705e79ddd, 0x3aff618604de4ae0, 0xc3d7a95fa9cb59bb),
        ] {
            assert_eq!(F64::new(a) * F64::new(b), F64::new(c));
        }
        assert_eq!(std::mem::size_of::<F192>(), 24);
        assert_eq!(std::mem::align_of::<F192>(), std::mem::align_of::<u64>());
    }

    #[test]
    fn protocol_byte_embedding_preserves_products() {
        for a in 0..=255 {
            for b in 0..=255 {
                let (a, b) = (F8::from_byte(a), F8::from_byte(b));
                assert_eq!(phi8_192(a * b), phi8_192(a) * phi8_192(b));
                assert_eq!(phi8_192(a + b), phi8_192(a) + phi8_192(b));
            }
        }
    }

    #[test]
    fn parallel_mle_matches_folding() {
        for n in [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16] {
            let table: Vec<_> = (0..1 << n)
                .map(|i: u64| F64::new(i.wrapping_mul(0x9E37_79B9_7F4A_7C15)))
                .collect();
            // The plain fold, one variable at a time, is the reference.
            let fold = |point: &[F192]| match point.split_first() {
                None => F192::from(table[0]),
                Some((&p0, rest)) => fold_ladder(fold_low_k(&table, p0), rest),
            };
            let point: Vec<_> = (0..n)
                .map(|i| F192::new([F64::new(17 + i), F64::new(231 + 3 * i), F64::new(97 + 7 * i)]))
                .collect();
            assert_eq!(mle_eval(&table, &point), fold(&point));
            assert_eq!(mle_eval_par(&table, &point), fold(&point));
            let point: Vec<_> = (0..n).map(|i| F192::from(F64::new(i % 2))).collect();
            assert_eq!(mle_eval(&table, &point), fold(&point));
            assert_eq!(mle_eval_par(&table, &point), fold(&point));
            // An odd length leaves a scalar tail after the batched folds.
            let chi = point
                .first()
                .copied()
                .unwrap_or(F192::new([F64::ZERO, F64::ONE, F64::ZERO]))
                + F192::new([F64::ZERO, F64::ONE, F64::ZERO]);
            if n > 0 {
                let half = table.len() / 2;
                let want: Vec<_> = (0..half).map(|i| interp_k(table[i], table[i + half], chi)).collect();
                assert_eq!(&*fold_high_k(&table, chi), &want[..]);
                let lifted: Vec<F192> = table.iter().map(|&k| F192::from(k) * chi).collect();
                let mut got = lifted.clone();
                fold_high_inplace(&mut got, chi);
                let want: Vec<_> = (0..half).map(|i| interp(lifted[i], lifted[i + half], chi)).collect();
                assert_eq!(got, want);
            }
        }
    }

    #[test]
    fn split_eq_is_the_eq_table() {
        // Invariant: the two tables weigh every row as the full eq table, and a weighted sum
        // over a range equals the dense one, whether it crosses a high block or not.
        //
        // Fixture state: 14 variables, split 12 low and 2 high, then 7 low and 7 high.
        let r: Vec<F192> = (0..14u64)
            .map(|i| F192::new([F64::new(3 * i + 1), F64::new(i + 7), F64::new(5 * i + 2)]))
            .collect();
        let dense = eq_table(&r);
        for split in [SplitEq::with_low_vars(&r, 12), SplitEq::with_high_vars(&r, 7)] {
            assert_eq!(split.low_log() + split.high_log(), r.len());
            for x in [0, 1, 127, 128, 4095, 4096, 4097, 12_345, (1 << 14) - 1] {
                assert_eq!(split.at(x), dense[x], "x={x}");
            }
        }

        // A split with fewer variables than its cap puts them all on the capped side.
        let short = SplitEq::with_high_vars(&r[..3], 7);
        assert_eq!((short.low_log(), short.high_log()), (0, 3));
    }
}
