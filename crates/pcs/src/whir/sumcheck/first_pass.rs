//! The first lane rounds from one pass, and the fold of all their lane bits at once.
//!
//! Lane round `j`'s message sums products of the witness and the weight, both
//! folded by the `j` challenges before it. In those challenges each product has
//! degree two per variable, so its sums at the points of `{0, 1, inf}^R` (`inf`
//! the leading coefficient), over every group of `2^R` lanes, determine the
//! messages of rounds `0..R`. One pass over the committed witness accumulates
//! them, each of those messages is interpolated once the challenges before it are
//! drawn, and one more pass folds all `R` lane bits at once (the small-value
//! precomputation of Bagad, Dao, Domb and Thaler, <https://eprint.iacr.org/2025/1117>:
//! the witness is in `K`, so every product is a mixed one).

use super::{Basis, FIRST_PASS_PAR_THRESHOLD, INITIAL_BASIS_CHUNK, PRECOMPUTED_ROUNDS, SumcheckMessage, window};
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
use primitives::field::gf2_64::mul_wide;
use primitives::field::{F64, F192};
use std::ops::Range;

/// Lanes per group, and points of `{0, 1, inf}^R`, `R` being [`PRECOMPUTED_ROUNDS`].
const GROUP: usize = 1 << PRECOMPUTED_ROUNDS;
const GRID: usize = 3usize.pow(PRECOMPUTED_ROUNDS as u32);

/// Grid index of each lane of a group: lane bit `i` is ternary digit `i`, and digit 2 is `inf`.
const LANE_IN_GRID: [usize; GROUP] = {
    let mut index = [0; GROUP];
    let mut lane = 0;
    while lane < GROUP {
        let (mut bits, mut weight) = (lane, 1);
        while bits > 0 {
            index[lane] += (bits & 1) * weight;
            bits >>= 1;
            weight *= 3;
        }
        lane += 1;
    }
    index
};

/// Offsets the first pass extends side by side.
const ROW: usize = 8;

/// Extend values at the lanes' grid points to all of `{0, 1, inf}^R`, one digit at a time:
/// a multilinear's `inf` is the sum of its `0` and `1`.
#[inline(always)]
fn extend_grid<T: Copy, const R: usize>(grid: &mut [T; GRID], add: impl Fn(&T, &T) -> T) {
    let mut stride = 1;
    for i in 0..R {
        for &high in &LANE_IN_GRID[..1 << (R - 1 - i)] {
            let base = 3 * stride * high;
            for at in base..base + stride {
                grid[at + 2 * stride] = add(&grid[at], &grid[at + stride]);
            }
        }
        stride *= 3;
    }
}

/// A row of `ROW` weights, laid out so that both qwords of every 128-bit lane meet a word:
/// lane `j` of `lo` is `[c0, c1]` of weight `2j`, of `hi` the same of weight `2j+1`, and
/// `c2` holds every weight's last coefficient in order.
#[derive(Clone, Copy, Default)]
#[repr(C, align(64))]
struct WeightRow {
    lo: [u64; ROW],
    hi: [u64; ROW],
    c2: [u64; ROW],
}

impl WeightRow {
    /// Pack up to `ROW` weights; the rest are zero.
    #[inline(always)]
    fn pack(w: &[F192]) -> Self {
        let mut row = Self::default();
        for (x, e) in w.iter().enumerate() {
            let pair = if x.is_multiple_of(2) { &mut row.lo } else { &mut row.hi };
            pair[x & !1] = e.c0;
            pair[x | 1] = e.c1;
            row.c2[x] = e.c2;
        }
        row
    }

    #[inline(always)]
    fn add(&self, other: &Self) -> Self {
        let xor = |a: &[u64; ROW], b: &[u64; ROW]| std::array::from_fn(|i| a[i] ^ b[i]);
        Self {
            lo: xor(&self.lo, &other.lo),
            hi: xor(&self.hi, &other.hi),
            c2: xor(&self.c2, &other.c2),
        }
    }
}

/// Unreduced sums of a [`WeightRow`]'s products by words, per coefficient: four 128-bit
/// partial sums, lane `j` as its `[low, high]` qwords.
#[derive(Clone, Copy, Default)]
#[repr(C, align(64))]
struct ProductRow([[u64; ROW]; 3]);

impl ProductRow {
    /// Accumulate the products of `w`'s weights by the words `k`, one by one.
    #[inline(always)]
    fn mul_acc(&mut self, w: &WeightRow, k: &[u64; ROW]) {
        #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
        // SAFETY: both features are enabled at compile time.
        unsafe {
            avx512::mul_acc(self, w, k);
        }
        #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
        for j in 0..ROW / 2 {
            let (even, odd) = (k[2 * j], k[2 * j + 1]);
            let sums = [
                mul_wide(w.lo[2 * j], even) ^ mul_wide(w.hi[2 * j], odd),
                mul_wide(w.lo[2 * j + 1], even) ^ mul_wide(w.hi[2 * j + 1], odd),
                mul_wide(w.c2[2 * j], even) ^ mul_wide(w.c2[2 * j + 1], odd),
            ];
            for (acc, s) in self.0.iter_mut().zip(sums) {
                acc[2 * j] ^= s as u64;
                acc[2 * j + 1] ^= (s >> 64) as u64;
            }
        }
    }

    #[inline(always)]
    fn add(&mut self, other: &Self) {
        for (a, b) in self.0.as_flattened_mut().iter_mut().zip(other.0.as_flattened()) {
            *a ^= b;
        }
    }

    /// The sum of every product.
    fn sum(&self) -> F192 {
        let [c0, c1, c2] = self.0.map(|lanes| {
            let (pairs, _) = lanes.as_chunks::<2>();
            let wide = pairs
                .iter()
                .fold(0u128, |acc, &[lo, hi]| acc ^ (u128::from(hi) << 64 | u128::from(lo)));
            primitives::field::gf2_64::reduce(wide)
        });
        F192::new(c0, c1, c2)
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
mod avx512 {
    use super::{F64, F192, LaneWeight, ProductRow, ROW, WeightRow};
    use core::arch::x86_64::*;

    /// Add `e·b` for eight weights `b`: each coefficient gathered across them, then six CLMULs
    /// against `e·y^k` per coefficient `k`, nothing crossing a lane.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx512f` target features.
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    pub(super) unsafe fn fold_acc(acc: &mut [[u64; ROW]; 6], e: &LaneWeight, b: &[F192; ROW]) {
        // Word `3x + k` of the weights is coefficient `k` of weight `x`; the second permute
        // takes the words past the first sixteen.
        const GATHER: [([i64; ROW], [i64; ROW]); 3] = [
            ([0, 3, 6, 9, 12, 15, 0, 0], [0, 1, 2, 3, 4, 5, 10, 13]),
            ([1, 4, 7, 10, 13, 0, 0, 0], [0, 1, 2, 3, 4, 8, 11, 14]),
            ([2, 5, 8, 11, 14, 0, 0, 0], [0, 1, 2, 3, 4, 9, 12, 15]),
        ];
        // SAFETY: the function carries both features; `b` is twenty-four qwords, and `acc` and `e` are 64-byte aligned.
        unsafe {
            let words = b.as_ptr().cast::<u64>();
            let (w0, w1, w2) = (
                _mm512_loadu_si512(words.cast()),
                _mm512_loadu_si512(words.add(ROW).cast()),
                _mm512_loadu_si512(words.add(2 * ROW).cast()),
            );
            let mut sums = acc.map(|row| _mm512_load_si512(row.as_ptr().cast()));
            for (k, (first, second)) in GATHER.iter().enumerate() {
                let low = _mm512_permutex2var_epi64(w0, _mm512_loadu_si512(first.as_ptr().cast()), w1);
                let kv = _mm512_permutex2var_epi64(low, _mm512_loadu_si512(second.as_ptr().cast()), w2);
                mul_by_words(&mut sums, e, k, kv);
            }
            for (row, s) in acc.iter_mut().zip(sums) {
                _mm512_store_si512(row.as_mut_ptr().cast(), s);
            }
        }
    }

    /// Add `e·f` for eight base words `f`.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx512f` target features.
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    pub(super) unsafe fn fold_base_acc(acc: &mut [[u64; ROW]; 6], e: &LaneWeight, f: &[F64; ROW]) {
        // SAFETY: the function carries both features; `f` is eight qwords, and `acc` and `e` are 64-byte aligned.
        unsafe {
            let mut sums = acc.map(|row| _mm512_load_si512(row.as_ptr().cast()));
            mul_by_words(&mut sums, e, 0, _mm512_loadu_si512(f.as_ptr().cast()));
            for (row, s) in acc.iter_mut().zip(sums) {
                _mm512_store_si512(row.as_mut_ptr().cast(), s);
            }
        }
    }

    /// Add the six products of `e·y^k` by the words `kv`, in [`super::WeightFold`]'s order.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx512f` target features.
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    unsafe fn mul_by_words(sums: &mut [__m512i; 6], e: &LaneWeight, k: usize, kv: __m512i) {
        // SAFETY: the function carries both features; `e` is 64-byte aligned.
        unsafe {
            let t01 = _mm512_load_si512(e.pairs[k].as_ptr().cast());
            let t2 = _mm512_load_si512(e.highs[k].as_ptr().cast());
            // Immediate bit 0 picks the qword of the first operand, bit 4 that of the second.
            let products = [
                _mm512_clmulepi64_epi128::<0x00>(t01, kv),
                _mm512_clmulepi64_epi128::<0x01>(t01, kv),
                _mm512_clmulepi64_epi128::<0x10>(t01, kv),
                _mm512_clmulepi64_epi128::<0x11>(t01, kv),
                _mm512_clmulepi64_epi128::<0x00>(t2, kv),
                _mm512_clmulepi64_epi128::<0x11>(t2, kv),
            ];
            for (s, p) in sums.iter_mut().zip(products) {
                *s = _mm512_xor_si512(*s, p);
            }
        }
    }

    /// Six CLMULs for the row, nothing crossing a lane.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx512f` target features.
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    pub(super) unsafe fn mul_acc(acc: &mut ProductRow, w: &WeightRow, k: &[u64; ROW]) {
        // SAFETY: the function carries both features; both rows are 64-byte aligned, and `k` is eight qwords.
        unsafe {
            let kv = _mm512_loadu_si512(k.as_ptr().cast());
            let (lo, hi, c2) = (
                _mm512_load_si512(w.lo.as_ptr().cast()),
                _mm512_load_si512(w.hi.as_ptr().cast()),
                _mm512_load_si512(w.c2.as_ptr().cast()),
            );
            // Immediate bit 0 picks the qword of the first operand, bit 4 that of the second.
            let sums = [
                _mm512_xor_si512(
                    _mm512_clmulepi64_epi128::<0x00>(lo, kv),
                    _mm512_clmulepi64_epi128::<0x10>(hi, kv),
                ),
                _mm512_xor_si512(
                    _mm512_clmulepi64_epi128::<0x01>(lo, kv),
                    _mm512_clmulepi64_epi128::<0x11>(hi, kv),
                ),
                _mm512_xor_si512(
                    _mm512_clmulepi64_epi128::<0x00>(c2, kv),
                    _mm512_clmulepi64_epi128::<0x11>(c2, kv),
                ),
            ];
            for (lanes, s) in acc.0.iter_mut().zip(sums) {
                let at = lanes.as_mut_ptr().cast();
                _mm512_store_si512(at, _mm512_xor_si512(_mm512_load_si512(at), s));
            }
        }
    }
}

/// The sums of the first pass, from which the first `rounds` lane rounds' messages follow.
pub(crate) struct InitialRounds {
    pub(super) rounds: usize,
    /// `sum f(d) * b(d)` at each `d` of `{0, 1, inf}^rounds`, over every lane group and offset.
    grid: Vec<F192>,
}

impl InitialRounds {
    /// Lane round `j`'s message, given the challenges `rs` of the rounds before it.
    pub(super) fn message(&self, j: usize, rs: &[F192]) -> SumcheckMessage {
        assert!(j < self.rounds && rs.len() == j);
        let low = 3usize.pow(j as u32);
        // Lagrange weights of `{0, 1, inf}^j` at `rs`: a quadratic has `q(r) = q(0)(1+r) + q(1)r + q(inf)(r+r^2)`.
        let mut weights = vec![F192::ONE];
        for &r in rs {
            let at = [F192::ONE + r, r, r * r + r];
            weights = at.iter().flat_map(|&l| weights.iter().map(move |&w| w * l)).collect();
        }
        // Digit `j` is the round's variable, at 0 or inf; the lane bits above it are summed over the cube.
        let [u_0, u_2] = [0, 2].map(|x| {
            let mut sums = vec![F192::ZERO; low];
            for &high in &LANE_IN_GRID[..1 << (self.rounds - 1 - j)] {
                let base = low * (x + 3 * high);
                for (s, &g) in sums.iter_mut().zip(&self.grid[base..base + low]) {
                    *s += g;
                }
            }
            sums.iter().zip(&weights).fold(F192::ZERO, |acc, (&s, &w)| acc + s * w)
        });
        SumcheckMessage { u_0, u_2 }
    }
}

/// The first pass: the grid sums of the first `min(PRECOMPUTED_ROUNDS, initial_k)` lane rounds.
pub(crate) fn initial_rounds(f: &[F64], block: usize, initial_k: usize, b: &Basis<'_>) -> InitialRounds {
    if let Basis::Dense(b) = b {
        assert_eq!(b.len(), f.len());
    }
    assert!(block.is_power_of_two() && f.len().is_multiple_of(block));
    let rounds = PRECOMPUTED_ROUNDS.min(initial_k);
    assert!(rounds >= 1, "at least one lane round");
    let n_lanes = f.len() / block;
    let whole = n_lanes >> rounds << rounds;
    let mut grid = if whole > 0 {
        grid_pass(rounds, f, block, b, 0..whole)
    } else {
        vec![F192::ZERO; 3usize.pow(rounds as u32)]
    };
    // A partial last group is summed over the digits its lanes reach. Past them every
    // lane bit is clear: at 1 the group has nothing, and at 0 and at inf it has those sums.
    if whole < n_lanes {
        let digits = (n_lanes - whole).next_power_of_two().ilog2() as usize;
        let tail = grid_pass(digits, f, block, b, whole..n_lanes);
        let low = tail.len();
        for &high in &LANE_IN_GRID[..1 << (rounds - digits)] {
            let base = low * 2 * high;
            for (g, &t) in grid[base..base + low].iter_mut().zip(&tail) {
                *g += t;
            }
        }
    }
    InitialRounds { rounds, grid }
}

/// The grid sums over `lanes`, `rounds` digits at a time: whole groups, or one group whose
/// missing lanes are zero.
fn grid_pass(rounds: usize, f: &[F64], block: usize, b: &Basis<'_>, lanes: Range<usize>) -> Vec<F192> {
    match rounds {
        0 => grid_pass_with::<0>(f, block, b, lanes),
        1 => grid_pass_with::<1>(f, block, b, lanes),
        2 => grid_pass_with::<2>(f, block, b, lanes),
        3 => grid_pass_with::<3>(f, block, b, lanes),
        4 => grid_pass_with::<4>(f, block, b, lanes),
        _ => unreachable!("at most PRECOMPUTED_ROUNDS digits"),
    }
}

fn grid_pass_with<const R: usize>(f: &[F64], block: usize, b: &Basis<'_>, lanes: Range<usize>) -> Vec<F192> {
    let group = 1 << R;
    let points = 3usize.pow(R as u32);
    // A regenerated weight is filled one aligned chunk at a time, or one whole block below that.
    let chunk = block.min(INITIAL_BASIS_CHUNK);
    let per = block / chunk;
    static ZERO_WORDS: [F64; INITIAL_BASIS_CHUNK] = [F64::ZERO; INITIAL_BASIS_CHUNK];
    static ZERO_WEIGHTS: [F192; INITIAL_BASIS_CHUNK] = [F192::ZERO; INITIAL_BASIS_CHUNK];

    struct Scratch {
        raw: [[F192; INITIAL_BASIS_CHUNK]; GROUP],
        fg: [[u64; ROW]; GRID],
        bg: [WeightRow; GRID],
    }
    type Acc = [ProductRow; GRID];
    // Below a row's width the tail of every row stays zero, and so do its products.
    let width = chunk.min(ROW);
    let task = |scratch: &mut Scratch, acc: &mut Acc, t: usize| {
        let Scratch { raw, fg, bg } = scratch;
        let (g, x0) = (t / per, (t % per) * chunk);
        // A lane past the range is zero.
        let mut fs: [&[F64]; GROUP] = [&ZERO_WORDS[..chunk]; GROUP];
        let mut bs: [&[F192]; GROUP] = [&ZERO_WEIGHTS[..chunk]; GROUP];
        for (l, raw) in raw.iter_mut().enumerate().take(group) {
            let lane = lanes.start + g * group + l;
            if lane < lanes.end {
                let at = lane * block + x0;
                fs[l] = &f[at..at + chunk];
                bs[l] = window(b, raw, at, chunk);
            }
        }
        for x in (0..chunk).step_by(ROW) {
            for l in 0..group {
                for (d, s) in fg[LANE_IN_GRID[l]].iter_mut().zip(&fs[l][x..x + width]) {
                    *d = s.0;
                }
                bg[LANE_IN_GRID[l]] = WeightRow::pack(&bs[l][x..x + width]);
            }
            extend_grid::<_, R>(fg, |a, b| std::array::from_fn(|i| a[i] ^ b[i]));
            extend_grid::<_, R>(bg, WeightRow::add);
            for (a, (k, w)) in acc.iter_mut().zip(fg.iter().zip(bg.iter())).take(points) {
                a.mul_acc(w, k);
            }
        }
    };

    let n_tasks = lanes.len().div_ceil(group) * per;
    let new_scratch = || {
        Box::new(Scratch {
            raw: [[F192::ZERO; INITIAL_BASIS_CHUNK]; GROUP],
            fg: [[0; ROW]; GRID],
            bg: [WeightRow::default(); GRID],
        })
    };
    let new_acc = || Box::new([ProductRow::default(); GRID]);
    let acc = if lanes.len() * block < FIRST_PASS_PAR_THRESHOLD {
        let (mut scratch, mut acc) = (new_scratch(), new_acc());
        for t in 0..n_tasks {
            task(&mut scratch, &mut acc, t);
        }
        acc
    } else {
        parallel::map_reduce_with_state(
            n_tasks,
            new_scratch,
            new_acc,
            |scratch, acc, t| task(scratch, acc, t),
            |mut a, c| {
                for (a, c) in a.iter_mut().zip(c.iter()) {
                    a.add(c);
                }
                a
            },
        )
    };
    acc[..points].iter().map(ProductRow::sum).collect()
}

/// A lane's eq weight `e`, as the fold's products read it: `e·y^k` for each coefficient `k`
/// of the weight it multiplies, `[c0, c1]` in every 128-bit lane of `pairs` and `c2` in every
/// qword of `highs`.
#[derive(Clone, Copy)]
#[repr(C, align(64))]
pub(super) struct LaneWeight {
    pairs: [[u64; ROW]; 3],
    highs: [[u64; ROW]; 3],
}

impl LaneWeight {
    pub(super) fn new(e: F192) -> Self {
        let ey = e * F192::Y;
        let by_coefficient = [e, ey, ey * F192::Y];
        Self {
            pairs: by_coefficient.map(|c| std::array::from_fn(|i| if i.is_multiple_of(2) { c.c0 } else { c.c1 })),
            highs: by_coefficient.map(|c| [c.c2; ROW]),
        }
    }
}

/// Unreduced sums `Σ e·x` over lanes, for a window of up to `INITIAL_BASIS_CHUNK` values.
/// Each row of `ROW` values holds six vectors of four 128-bit sums: coefficients 0 and 1
/// of the even values, the same of the odd ones, then coefficient 2 of both.
#[derive(Clone, Copy, Default)]
#[repr(C, align(64))]
pub(super) struct WeightFold([[[u64; ROW]; 6]; INITIAL_BASIS_CHUNK / ROW]);

/// `xs` by rows of `ROW`, the last one zero-padded.
#[inline(always)]
fn padded_rows<T: Copy + Default>(xs: &[T]) -> impl Iterator<Item = [T; ROW]> + '_ {
    xs.chunks(ROW).map(|c| {
        let mut row = [T::default(); ROW];
        row[..c.len()].copy_from_slice(c);
        row
    })
}

impl WeightFold {
    /// Add `e·b` for one lane's window `b`.
    #[inline]
    pub(super) fn add(&mut self, e: &LaneWeight, b: &[F192]) {
        for (row, b) in self.0.iter_mut().zip(padded_rows(b)) {
            #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
            // SAFETY: both features are enabled at compile time.
            unsafe {
                avx512::fold_acc(row, e, &b);
            }
            #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
            for (x, w) in b.iter().enumerate() {
                for (k, c) in [w.c0, w.c1, w.c2].into_iter().enumerate() {
                    Self::add_products(row, e, k, x, c);
                }
            }
        }
    }

    /// Add `e·f` for one lane's window `f` of base words.
    #[inline]
    pub(super) fn add_base(&mut self, e: &LaneWeight, f: &[F64]) {
        for (row, f) in self.0.iter_mut().zip(padded_rows(f)) {
            #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
            // SAFETY: both features are enabled at compile time.
            unsafe {
                avx512::fold_base_acc(row, e, &f);
            }
            #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
            for (x, w) in f.iter().enumerate() {
                Self::add_products(row, e, 0, x, w.0);
            }
        }
    }

    /// Add the products of word `c` by `e·y^k` to value `x` of `row`.
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    fn add_products(row: &mut [[u64; ROW]; 6], e: &LaneWeight, k: usize, x: usize, c: u64) {
        let (j, slots) = (x / 2 * 2, if x.is_multiple_of(2) { [0, 1, 4] } else { [2, 3, 5] });
        let products = [e.pairs[k][0], e.pairs[k][1], e.highs[k][0]].map(|t| primitives::field::gf2_64::mul_wide(t, c));
        for (s, p) in slots.into_iter().zip(products) {
            row[s][j] ^= p as u64;
            row[s][j + 1] ^= (p >> 64) as u64;
        }
    }

    /// The reduced sums, one per weight of `dst`.
    pub(super) fn write(&self, dst: &mut [F192]) {
        for (x, d) in dst.iter_mut().enumerate() {
            let (row, i) = (&self.0[x / ROW], x % ROW);
            let (j, slots) = (i / 2 * 2, if i.is_multiple_of(2) { [0, 1, 4] } else { [2, 3, 5] });
            let [c0, c1, c2] = slots
                .map(|s| primitives::field::gf2_64::reduce(u128::from(row[s][j + 1]) << 64 | u128::from(row[s][j])));
            *d = F192::new(c0, c1, c2);
        }
    }
}
