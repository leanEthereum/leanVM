// CREDIT: https://github.com/succinctlabs/flock (`build_eq` and `lagrange_weights_naive`), MIT OR Apache-2.0.
//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`). Sumchecks here consume variables from either end, so folding
//! and `eq`-marginalization come in low and high variants. Committed data is
//! `K`-valued (`F64`) while randomness is `E`-valued (`F192`), so the first
//! fold of a committed table also lifts it into `E`.

use std::ops::DerefMut;

use crate::field::{F64, F192, F192Unreduced, PHI_8_TABLE_192 as PHI_8_TABLE};
use zk_alloc::ArenaVec;

/// The one thing the in-place folds need beyond a mutable slice: the ability to
/// drop a suffix. Implemented for `Vec` and `ArenaVec`, so a fold works on either
/// without duplicating the kernel or naming a container in its signature.
pub trait Shrink<T>: DerefMut<Target = [T]> {
    /// Keep the first `len` elements, dropping the rest.
    fn shrink_to(&mut self, len: usize);
}

impl<T> Shrink<T> for Vec<T> {
    #[inline]
    fn shrink_to(&mut self, len: usize) {
        self.truncate(len);
    }
}

impl<T> Shrink<T> for ArenaVec<T> {
    #[inline]
    fn shrink_to(&mut self, len: usize) {
        self.truncate(len);
    }
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
    F192::from(lo) + t.mul_base(lo + hi)
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)`. For Boolean `r`, this is the indicator
/// of `x = r`; for arbitrary `r`, it is the multilinear interpolation weight.
pub fn eq_eval(r: &[F192], x: &[F192]) -> F192 {
    debug_assert_eq!(r.len(), x.len());
    r.iter()
        .zip(x)
        .fold(F192::ONE, |acc, (&ri, &xi)| acc * (F192::ONE + ri + xi))
}

/// The `eq(r, ·)` table over `n = r.len()` variables, expanded a level at a
/// time: each level writes the new high half from the low half and rewrites
/// the low half in place.
///
/// In characteristic 2, the low child is the high child plus the parent, so each pair needs one multiplication. Wide levels are split across threads.
pub fn eq_table(r: &[F192]) -> Vec<F192> {
    let mut eq = vec![F192::ZERO; 1usize << r.len()];
    fill_eq_table(r, &mut eq);
    eq
}

/// Arena-backed [`eq_table`], for the prover's large tables. Identical output.
pub fn eq_table_arena(r: &[F192]) -> ArenaVec<F192> {
    let mut eq = zk_alloc::alloc_uninit(1usize << r.len());
    fill_eq_table_uninit(r, F192::ONE, &mut eq);
    // SAFETY: the doubling recurrence writes every entry.
    unsafe { zk_alloc::assume_init(eq) }
}

fn fill_eq_table(r: &[F192], eq: &mut [F192]) {
    // SAFETY: MaybeUninit has the same layout as F192; the exclusive borrow covers the whole slice.
    let out = unsafe { std::slice::from_raw_parts_mut(eq.as_mut_ptr().cast(), eq.len()) };
    fill_eq_table_uninit(r, F192::ONE, out);
}

/// Fill `out` with `seed * eq(r, .)`, in LSB-first order. Every entry is written before it is read. Wide levels use the worker pool, so a caller inside a dispatch must keep the table below the parallel threshold.
pub fn fill_eq_table_uninit(r: &[F192], seed: F192, out: &mut [std::mem::MaybeUninit<F192>]) {
    assert_eq!(out.len(), 1usize << r.len(), "out must have length 2^r.len()");
    out[0].write(seed);
    for (i, &rk) in r.iter().enumerate() {
        let half = 1usize << i;
        let (lo, hi_rest) = out.split_at_mut(half);
        let hi = &mut hi_rest[..half];
        let build_pair = |lo_x: &mut std::mem::MaybeUninit<F192>, hi_x: &mut std::mem::MaybeUninit<F192>| {
            // SAFETY: the low half was initialized at earlier levels.
            let e = unsafe { lo_x.assume_init_read() };
            let high = e * rk;
            hi_x.write(high);
            lo_x.write(e + high);
        };
        if half < PAR_THRESHOLD {
            lo.iter_mut().zip(hi.iter_mut()).for_each(|(l, h)| build_pair(l, h));
        } else {
            let chunk = parallel::recommended_chunk_size(half);
            parallel::chunks_mut2(lo, hi, chunk, |_, lo_c, hi_c| {
                lo_c.iter_mut().zip(hi_c.iter_mut()).for_each(|(l, h)| build_pair(l, h));
            });
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

/// [`fold_low_k`], fanned out over the pool.
fn fold_low_k_par(table: &[F64], chi: F192) -> Vec<F192> {
    parallel::map_collect(table.len() / 2, |i| interp_k(table[2 * i], table[2 * i + 1], chi))
}

/// Bind the highest variable of a `K`-table and lift the result into `E`.
pub fn fold_high_k(table: &[F64], chi: F192) -> ArenaVec<F192> {
    debug_assert_eq!(table.len() % 2, 0);
    let half = table.len() / 2;
    (0..half).map(|i| interp_k(table[i], table[i + half], chi)).collect()
}

/// Bind the highest free variable of `table` to `chi` in place: `table[i] =
/// interp(table[i], table[i + half], chi)`. Binding from the top down leaves the
/// low variables, the ones every table of a batch shares, for last.
pub fn fold_high_inplace<B: Shrink<F192>>(table: &mut B, chi: F192) {
    debug_assert_eq!(table.len() % 2, 0);
    let half = table.len() / 2;
    {
        // Split once rather than index twice: indexing reloads the data pointer
        // and length through the container every iteration, since nothing proves
        // they do not alias the elements, and pays a bounds check for it.
        let (lo, hi) = (**table).split_at_mut(half);
        for (l, h) in lo.iter_mut().zip(&*hi) {
            *l = interp(*l, *h, chi);
        }
    }
    table.shrink_to(half);
}

/// Marginalize the lowest variable out of an `eq` table (in place). `eq(r_0, 0) +
/// eq(r_0, 1) = 1`, so summing adjacent entries drops `r_0` with no multiplies,
/// versus `2^{n-1}` to rebuild the table.
pub fn shrink_eq_low<B: Shrink<F192>>(table: &mut B) {
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
    table.shrink_to(half);
}

/// Marginalize the highest variable out of an `eq` table (in place), the
/// [`shrink_eq_low`] counterpart for a top-down sumcheck.
pub fn shrink_eq_high<B: Shrink<F192>>(table: &mut B) {
    let half = table.len() / 2;
    {
        // Sliced, as in `fold_high_inplace`.
        let (lo, hi) = (**table).split_at_mut(half);
        for (l, h) in lo.iter_mut().zip(&*hi) {
            *l += *h;
        }
    }
    table.shrink_to(half);
}

/// The one barycentric denominator an aligned `size`-node window of the φ₈ table has: `∏_{k≠0} φ₈(k)`,
/// inverted. φ₈ is F2-linear on its index, so `nodes[a] + nodes[b] = φ₈(a ^ b)` (the window's offset
/// cancels) and `b ↦ a ^ b` only permutes the window, leaving every node the same product.
pub fn window_denominator(size: usize) -> F192 {
    PHI_8_TABLE[1..size]
        .iter()
        .fold(F192::ONE, |acc, &node| acc * node)
        .inv()
}

/// The barycentric weights of `nodes` at `p`: `weights[i] =
/// ∏_{k≠i} (p + nodes[k]) / ∏_{k≠i} (nodes[i] + nodes[k])`. `O(n²)` multiplies
/// and, by `window_denominator`, a single inverse.
///
/// `nodes` must be an aligned window of the φ₈ table, `nodes[a] = nodes[0] + φ₈(a)`, which is what
/// every caller passes: a `2^k` prefix, or one of its cosets.
fn lagrange_weights(nodes: &[F192], p: F192) -> Vec<F192> {
    let n = nodes.len();
    debug_assert!(n.is_power_of_two() && n <= PHI_8_TABLE.len());
    debug_assert!(
        (0..n).all(|a| nodes[a] == nodes[0] + PHI_8_TABLE[a]),
        "not an aligned φ₈ window"
    );
    let denominator = window_denominator(n);
    (0..n)
        .map(|i| {
            let mut num = F192::ONE;
            for k in 0..n {
                if k != i {
                    num *= p + nodes[k];
                }
            }
            num * denominator
        })
        .collect()
}

/// Lagrange evaluation: given distinct `nodes` and a polynomial's `values` there,
/// evaluate the interpolant at `p`. Reads a sumcheck round's univariate (sent as
/// evaluations) at the verifier's challenge.
pub fn lagrange_eval(nodes: &[F192], values: &[F192], p: F192) -> F192 {
    debug_assert_eq!(nodes.len(), values.len());
    lagrange_weights(nodes, p)
        .iter()
        .zip(values)
        .fold(F192::ZERO, |acc, (&w, &v)| acc + v * w)
}

/// A degree-2 polynomial's coefficients from its values at {0, 1, g}.
///
/// `p(0) = c0`, `p(1) = c0+c1+c2` and `p(g) = c0+c1·g+c2·g²` invert to a single
/// multiply by the constant `(g+g²)⁻¹`. Sumcheck rounds travel as coefficients
/// (`fiat_shamir::Transmitter::add_round_poly`), so this is where the prover's
/// per-row accumulator, which is evaluations, becomes one.
#[inline]
pub fn tri_coeffs(evals: [F192; 3]) -> [F192; 3] {
    static INV: std::sync::OnceLock<(F192, F192)> = std::sync::OnceLock::new();
    let &(g, inv) = INV.get_or_init(|| {
        let g = F192::from(crate::field::G);
        (g, (g + g * g).inv())
    });
    let c2 = (evals[0] + evals[2] + g * (evals[0] + evals[1])) * inv;
    [evals[0], evals[0] + evals[1] + c2, c2]
}

/// A polynomial at `point`, by Horner over its coefficients, constant first.
#[inline]
pub fn poly_eval(coeffs: &[F192], point: F192) -> F192 {
    coeffs.iter().rev().fold(F192::ZERO, |acc, &c| acc * point + c)
}

/// Add two 3-coefficient sumcheck accumulators componentwise.
#[inline]
pub fn add3(mut x: [F192; 3], y: [F192; 3]) -> [F192; 3] {
    for i in 0..3 {
        x[i] += y[i];
    }
    x
}

/// XOR two 3-slot deferred-reduction accumulators componentwise (the unreduced
/// counterpart of [`add3`]; XOR IS addition on the unreduced parts).
#[inline]
pub fn xor3(mut x: [F192Unreduced; 3], y: [F192Unreduced; 3]) -> [F192Unreduced; 3] {
    for i in 0..3 {
        x[i] ^= y[i];
    }
    x
}

/// Evaluate the MLE of a `K`-valued truth table at an `E`-point (length
/// `log2(len)`), binding variables LSB-first: the first fold is mixed
/// (`fold_low_k`), the rest pure `E` in place.
pub fn mle_eval(table: &[F64], point: &[F192]) -> F192 {
    debug_assert_eq!(table.len(), 1 << point.len());
    if point.is_empty() {
        return F192::from(table[0]);
    }
    fold_ladder(fold_low_k(table, point[0]), &point[1..], false)
}

/// [`mle_eval`], fanned out over the pool. For an OUTERMOST caller only: a kernel
/// already inside a dispatch must use the scalar [`mle_eval`], since nesting
/// deadlocks. Worth it only for the big fixed tables (the stacked bytecode),
/// where one evaluation is millions of sequential folds.
pub fn mle_eval_par(table: &[F64], point: &[F192]) -> F192 {
    debug_assert_eq!(table.len(), 1 << point.len());
    if point.is_empty() {
        return F192::from(table[0]);
    }
    fold_ladder(fold_low_k_par(table, point[0]), &point[1..], true)
}

/// The MLE of the pointwise product `a·b` at an `E`-point, i.e. `Σ_z eq(point,
/// z)·a(z)·b(z)`. This is NOT `â(point)·b̂(point)`: a product of multilinears is
/// not multilinear, so it has to be summed over the cube. The first fold takes the
/// product in `K` (1 PMULL) and lifts, after which it is [`mle_eval`]'s ladder.
pub fn mle_eval_prod(a: &[F64], b: &[F64], point: &[F192]) -> F192 {
    debug_assert_eq!(a.len(), b.len());
    debug_assert_eq!(a.len(), 1 << point.len());
    if point.is_empty() {
        return F192::from(a[0] * b[0]);
    }
    let chi = point[0];
    let cur = (0..a.len() / 2)
        .map(|i| interp_k(a[2 * i] * b[2 * i], a[2 * i + 1] * b[2 * i + 1], chi))
        .collect();
    fold_ladder(cur, &point[1..], false)
}

/// Bind the remaining variables of a half-folded `E`-table, LSB-first.
fn fold_ladder(mut cur: Vec<F192>, point: &[F192], par: bool) -> F192 {
    let mut len = cur.len();
    for &p in point {
        len /= 2;
        // Out of place while the round is worth a dispatch: an in-place fold
        // reads `cur[2i]` where another task writes `cur[i]`.
        if par && len >= PAR_THRESHOLD {
            let src: &[F192] = &cur;
            cur = parallel::map_collect(len, |i| interp(src[2 * i], src[2 * i + 1], p));
            continue;
        }
        // Keep `p` loop-invariant in the scalar product.
        for i in 0..len {
            cur[i] = interp(cur[2 * i], cur[2 * i + 1], p);
        }
    }
    cur[0]
}

/// Barycentric weights over the first `2^k_skip` nodes of the GF(2^8) subfield.
/// O(2^{2·k_skip}) field multiplies, a one-time cost.
pub fn lagrange_weights_naive(k_skip: usize, z: F192) -> Vec<F192> {
    let ell = 1usize << k_skip;
    assert!(ell <= 256, "k_skip > 8 would exceed PHI_8_TABLE");
    lagrange_weights(&PHI_8_TABLE[..ell], z)
}
