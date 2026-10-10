//! The first lane rounds from one pass over the witness, and the fold of all their lane bits at once.
//!
//! # The grid
//!
//! Lane round `j`'s message sums products of the witness and the weight, both folded by the `j` challenges before it.
//!
//! - Group the lanes `2^R` at a time: lane bit `i` of a group is the variable of round `i`.
//! - In those `R` variables, each product of witness and weight has degree at most two in each variable.
//! - So its sums at the `3^R` points of `{0, 1, inf}^R` fix the messages of rounds `0..R`.
//! - `inf` stands for the leading coefficient.
//!
//! One pass over the committed witness accumulates those sums, over every group and word offset.
//! Each message is interpolated once the challenges before it are drawn, and one more pass folds all `R` lane bits.
//!
//! This is the small-value precomputation of Bagad, Dao, Domb and Thaler, <https://eprint.iacr.org/2025/1117>.
//! The witness is in `K`, so every product is a mixed one: a `K` word by an `E` weight.
//!
//! # Kernels
//!
//! - On PMULL targets, the grid's last digit is extended while its products accumulate.
//! - Its zero, one and infinity sums stay in registers across a row's offsets.
//! - So neither the infinity weights nor partial sums take a separate memory pass.
//! - The wider x86 kernels keep their lane-parallel layout.

use super::{FIRST_PASS_PAR_THRESHOLD, INITIAL_BASIS_CHUNK, InitialWeight, PRECOMPUTED_ROUNDS, SumcheckMessage};
#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "pclmulqdq"),
    all(target_arch = "aarch64", target_feature = "aes")
)))]
use primitives::field::gf2_64::mul_wide;
use primitives::field::{F64, F192};
use std::ops::Range;

/// Lanes per group: `2^R`, with `R = PRECOMPUTED_ROUNDS`.
const GROUP: usize = 1 << PRECOMPUTED_ROUNDS;
/// Points of `{0, 1, inf}^R`: `3^R`.
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

/// Word offsets the first pass handles side by side: one row of every grid point.
const ROW: usize = 8;

/// Extends values at the lanes' grid points to all of `{0, 1, inf}^R`, one digit at a time.
///
/// A multilinear's value at `inf` is its leading coefficient, the sum of its values at 0 and 1.
#[inline(always)]
fn extend_grid<T: Copy, const R: usize>(grid: &mut [T; GRID], add: impl Fn(&T, &T) -> T) {
    let mut stride = 1;
    for i in 0..R {
        // Digit `i`: the digits below are already extended and those above are still in `{0, 1}`.
        for &high in &LANE_IN_GRID[..1 << (R - 1 - i)] {
            let base = 3 * stride * high;
            for at in base..base + stride {
                grid[at + 2 * stride] = add(&grid[at], &grid[at + stride]);
            }
        }
        stride *= 3;
    }
}

/// The grid extension's first `digits` digits only, the rest left to the caller.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline(always)]
fn extend_grid_digits<T: Copy, const R: usize>(grid: &mut [T; GRID], digits: usize, add: impl Fn(&T, &T) -> T) {
    let mut stride = 1;
    for i in 0..digits {
        for &high in &LANE_IN_GRID[..1 << (R - 1 - i)] {
            let base = 3 * stride * high;
            for at in base..base + stride {
                grid[at + 2 * stride] = add(&grid[at], &grid[at + stride]);
            }
        }
        stride *= 3;
    }
}

/// Extends one row of the grid and accumulates its products, the last digit extended where its products are made.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline(always)]
fn accumulate_grid<const R: usize>(
    fg: &mut [[u64; ROW]; GRID],
    bg: &mut [WeightRow; GRID],
    acc: &mut [ProductRow; GRID],
) {
    if R > 0 {
        extend_grid_digits::<_, R>(fg, R - 1, |a, b| std::array::from_fn(|i| a[i] ^ b[i]));
        extend_grid_digits::<_, R>(bg, R - 1, WeightRow::add);
        // SAFETY: PMULL is enabled at compile time, `R >= 1`, and the helper stays within the grid.
        unsafe { lanes::finish_grid::<R>(fg, bg, acc) };
        return;
    }
    // No digit: the single point's products, as on the other targets.
    extend_grid::<_, R>(fg, |a, b| std::array::from_fn(|i| a[i] ^ b[i]));
    extend_grid::<_, R>(bg, WeightRow::add);
    for (a, (k, w)) in acc.iter_mut().zip(fg.iter().zip(bg.iter())).take(3usize.pow(R as u32)) {
        a.mul_acc(w, k);
    }
}

/// A row of `ROW` weights, laid out so that both qwords of every 128-bit lane meet a word.
#[derive(Clone, Copy, Default)]
#[repr(C, align(64))]
struct WeightRow {
    /// 128-bit lane `j` is `[c0, c1]` of weight `2j`.
    lo: [u64; ROW],
    /// 128-bit lane `j` is `[c0, c1]` of weight `2j + 1`.
    hi: [u64; ROW],
    /// Every weight's coefficient `c2`, in order.
    c2: [u64; ROW],
}

impl WeightRow {
    /// Packs up to `ROW` weights; the rest are zero.
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

    /// The coefficient-wise sum of two rows.
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

/// Unreduced sums of a weight row's products by words: per coefficient, four 128-bit partial sums.
///
/// Partial sum `j` of a coefficient is its qwords `2j` (low half) and `2j + 1` (high half).
#[derive(Clone, Copy, Default)]
#[repr(C, align(64))]
struct ProductRow([[u64; ROW]; 3]);

impl ProductRow {
    /// Accumulates the products of `w`'s weights by the words `k`, weight `x` by word `x`.
    #[inline(always)]
    fn mul_acc(&mut self, w: &WeightRow, k: &[u64; ROW]) {
        #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
        // SAFETY: both features are enabled at compile time.
        unsafe {
            avx512::mul_acc(self, w, k);
        }
        #[cfg(any(
            all(
                target_arch = "x86_64",
                target_feature = "pclmulqdq",
                not(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))
            ),
            all(target_arch = "aarch64", target_feature = "aes")
        ))]
        // SAFETY: the features of the target's arm are enabled at compile time.
        unsafe {
            lanes::mul_acc::<lanes::Best>(self, w, k);
        }
        #[cfg(not(any(
            all(target_arch = "x86_64", target_feature = "pclmulqdq"),
            all(target_arch = "aarch64", target_feature = "aes")
        )))]
        // Portable: partial sum `j` takes the even word `k[2j]` and the odd word `k[2j + 1]`.
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

    /// Adds another row's sums.
    #[inline(always)]
    fn add(&mut self, other: &Self) {
        for (a, b) in self.0.as_flattened_mut().iter_mut().zip(other.0.as_flattened()) {
            *a ^= b;
        }
    }

    /// The sum of every product, reduced.
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

/// The AVX-512 kernels: four 128-bit lanes per register, nothing crossing a lane.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
mod avx512 {
    use super::{F64, LaneWeight, ProductRow, ROW, WeightRow};
    use core::arch::x86_64::*;

    /// Adds `e * f[x]` to word `x`'s sums for eight base words, into one row of the many-bit fold.
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
            mul_by_words(&mut sums, e, _mm512_loadu_si512(f.as_ptr().cast()));
            for (row, s) in acc.iter_mut().zip(sums) {
                _mm512_store_si512(row.as_mut_ptr().cast(), s);
            }
        }
    }

    /// Adds the six products of `e` by the words `kv`, in the order of the many-bit fold's vectors.
    ///
    /// # Safety
    ///
    /// Requires the `vpclmulqdq` and `avx512f` target features.
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    unsafe fn mul_by_words(sums: &mut [__m512i; 6], e: &LaneWeight, kv: __m512i) {
        // SAFETY: the function carries both features; `e` is 64-byte aligned.
        unsafe {
            let t01 = _mm512_load_si512(e.pairs.as_ptr().cast());
            let t2 = _mm512_load_si512(e.highs.as_ptr().cast());
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

    /// Accumulates the weight row's products by eight words: six carry-less products, nothing crossing a lane.
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

/// The AVX-512 kernels' products on narrower registers, one register of 128-bit lanes at a time.
///
/// - 256-bit VPCLMULQDQ with AVX2, and 128-bit PCLMULQDQ without.
/// - PMULL on aarch64.
///
/// On an AVX-512 target only the tests use it.
#[cfg(any(
    all(target_arch = "x86_64", target_feature = "pclmulqdq"),
    all(target_arch = "aarch64", target_feature = "aes")
))]
#[cfg_attr(all(target_feature = "vpclmulqdq", target_feature = "avx512f"), allow(dead_code))]
mod lanes {
    #[cfg(target_arch = "aarch64")]
    use super::GRID;
    use super::{F64, LaneWeight, ProductRow, ROW, WeightRow};
    #[cfg(target_arch = "aarch64")]
    use core::arch::aarch64::*;
    #[cfg(target_arch = "x86_64")]
    use core::arch::x86_64::*;
    #[cfg(target_arch = "aarch64")]
    use primitives::field::neon::xor3_u64;

    /// Registers of 128-bit lanes and the carry-less product within each lane.
    pub(super) trait Clmul: Copy {
        /// Qwords per register.
        const WORDS: usize;

        /// Loads `WORDS` qwords from `p`.
        ///
        /// # Safety
        ///
        /// `p` must be readable for `WORDS` qwords.
        unsafe fn load(p: *const u64) -> Self;

        /// Stores the register's `WORDS` qwords at `p`.
        ///
        /// # Safety
        ///
        /// `p` must be writable for `WORDS` qwords.
        unsafe fn store(self, p: *mut u64);

        /// In every lane, qword `IMM & 1` of `self` by qword `(IMM >> 4) & 1` of `other` (the x86 immediate).
        fn mul<const IMM: i32>(self, other: Self) -> Self;

        /// The XOR of two registers.
        fn xor(self, other: Self) -> Self;

        /// The XOR of three registers.
        fn xor3(self, b: Self, c: Self) -> Self;
    }

    /// 256-bit VPCLMULQDQ.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    #[cfg_attr(target_feature = "avx512f", allow(dead_code))]
    #[derive(Clone, Copy)]
    pub(super) struct Ymm(__m256i);

    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    impl Clmul for Ymm {
        const WORDS: usize = 4;

        #[inline(always)]
        unsafe fn load(p: *const u64) -> Self {
            // SAFETY: the impl exists only when the crate is built with AVX2.
            // The caller guarantees four readable qwords at `p`, and the load is unaligned.
            Self(unsafe { _mm256_loadu_si256(p.cast()) })
        }

        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            // SAFETY: as for `load`, writable.
            unsafe { _mm256_storeu_si256(p.cast(), self.0) }
        }

        #[inline(always)]
        fn mul<const IMM: i32>(self, other: Self) -> Self {
            // SAFETY: the impl exists only when the crate is built with VPCLMULQDQ and AVX2; registers only.
            Self(unsafe { _mm256_clmulepi64_epi128::<IMM>(self.0, other.0) })
        }

        #[inline(always)]
        fn xor(self, other: Self) -> Self {
            // SAFETY: the impl exists only when the crate is built with AVX2; registers only.
            Self(unsafe { _mm256_xor_si256(self.0, other.0) })
        }

        #[inline(always)]
        fn xor3(self, b: Self, c: Self) -> Self {
            // SAFETY: as for `xor`.
            Self(unsafe { _mm256_xor_si256(_mm256_xor_si256(self.0, b.0), c.0) })
        }
    }

    /// 128-bit PCLMULQDQ.
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    #[cfg_attr(target_feature = "vpclmulqdq", allow(dead_code))]
    #[derive(Clone, Copy)]
    pub(super) struct Xmm(__m128i);

    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    impl Clmul for Xmm {
        const WORDS: usize = 2;

        #[inline(always)]
        unsafe fn load(p: *const u64) -> Self {
            // SAFETY: SSE2 is part of the x86-64 baseline.
            // The caller guarantees two readable qwords at `p`, and the load is unaligned.
            Self(unsafe { _mm_loadu_si128(p.cast()) })
        }

        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            // SAFETY: as for `load`, writable.
            unsafe { _mm_storeu_si128(p.cast(), self.0) }
        }

        #[inline(always)]
        fn mul<const IMM: i32>(self, other: Self) -> Self {
            // SAFETY: the impl exists only when the crate is built with PCLMULQDQ; registers only.
            Self(unsafe { _mm_clmulepi64_si128::<IMM>(self.0, other.0) })
        }

        #[inline(always)]
        fn xor(self, other: Self) -> Self {
            // SAFETY: SSE2 is part of the x86-64 baseline; registers only.
            Self(unsafe { _mm_xor_si128(self.0, other.0) })
        }

        #[inline(always)]
        fn xor3(self, b: Self, c: Self) -> Self {
            // SAFETY: as for `xor`.
            Self(unsafe { _mm_xor_si128(_mm_xor_si128(self.0, b.0), c.0) })
        }
    }

    /// PMULL, with EOR3 where the target has it.
    #[cfg(target_arch = "aarch64")]
    #[derive(Clone, Copy)]
    pub(super) struct Neon(uint64x2_t);

    #[cfg(target_arch = "aarch64")]
    impl Clmul for Neon {
        const WORDS: usize = 2;

        #[inline(always)]
        unsafe fn load(p: *const u64) -> Self {
            // SAFETY: NEON is part of the aarch64 baseline, and the caller guarantees two readable qwords at `p`.
            Self(unsafe { vld1q_u64(p) })
        }

        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            // SAFETY: as for `load`, writable.
            unsafe { vst1q_u64(p, self.0) }
        }

        #[inline(always)]
        fn mul<const IMM: i32>(self, other: Self) -> Self {
            // SAFETY: the impl exists only when the crate is built with `aes`, which carries PMULL; registers only.
            unsafe {
                let product = match IMM {
                    0x00 => vmull_p64(vgetq_lane_u64::<0>(self.0), vgetq_lane_u64::<0>(other.0)),
                    0x01 => vmull_p64(vgetq_lane_u64::<1>(self.0), vgetq_lane_u64::<0>(other.0)),
                    0x10 => vmull_p64(vgetq_lane_u64::<0>(self.0), vgetq_lane_u64::<1>(other.0)),
                    _ => vmull_high_p64(vreinterpretq_p64_u64(self.0), vreinterpretq_p64_u64(other.0)),
                };
                Self(vreinterpretq_u64_p128(product))
            }
        }

        #[inline(always)]
        fn xor(self, other: Self) -> Self {
            // SAFETY: NEON is part of the aarch64 baseline; registers only.
            Self(unsafe { veorq_u64(self.0, other.0) })
        }

        #[inline(always)]
        fn xor3(self, b: Self, c: Self) -> Self {
            // SAFETY: `xor3_u64` issues EOR3 only where the target enables `sha3`; registers only.
            Self(unsafe { xor3_u64(self.0, b.0, c.0) })
        }
    }

    /// Accumulates the weight row's products by eight words as the AVX-512 kernel does, a register at a time.
    ///
    /// # Safety
    ///
    /// Requires the features of `V`.
    #[inline(always)]
    pub(super) unsafe fn mul_acc<V: Clmul>(acc: &mut ProductRow, w: &WeightRow, k: &[u64; ROW]) {
        for c in (0..ROW).step_by(V::WORDS) {
            // SAFETY: `c + V::WORDS <= ROW`, the length of every row read and written.
            unsafe {
                let kv = V::load(k.as_ptr().add(c));
                let (lo, hi, c2) = (
                    V::load(w.lo.as_ptr().add(c)),
                    V::load(w.hi.as_ptr().add(c)),
                    V::load(w.c2.as_ptr().add(c)),
                );
                let [s0, s1, s2] = &mut acc.0;
                for (row, (p, q)) in [
                    (s0, (lo.mul::<0x00>(kv), hi.mul::<0x10>(kv))),
                    (s1, (lo.mul::<0x01>(kv), hi.mul::<0x11>(kv))),
                    (s2, (c2.mul::<0x00>(kv), c2.mul::<0x11>(kv))),
                ] {
                    let at = row.as_mut_ptr().add(c);
                    V::load(at).xor3(p, q).store(at);
                }
            }
        }
    }

    /// Extends the grid's last digit on the fly and accumulates the products at all three of its values.
    ///
    /// Each point's sums stay in registers across the row, and only the first pair of each coefficient holds them.
    /// The other pairs stay zero, so reducing or combining the accumulators reads the layout of the other paths.
    ///
    /// # Safety
    ///
    /// Requires PMULL (the `aes` target feature), and `R >= 1`.
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[inline(always)]
    pub(super) unsafe fn finish_grid<const R: usize>(
        fg: &[[u64; ROW]; GRID],
        bg: &[WeightRow; GRID],
        acc: &mut [ProductRow; GRID],
    ) {
        #[inline(always)]
        fn update(s: (Neon, Neon, Neon), k: Neon, lo: Neon, hi: Neon, c2: Neon) -> (Neon, Neon, Neon) {
            (
                s.0.xor3(lo.mul::<0x00>(k), hi.mul::<0x10>(k)),
                s.1.xor3(lo.mul::<0x01>(k), hi.mul::<0x11>(k)),
                s.2.xor3(c2.mul::<0x00>(k), c2.mul::<0x11>(k)),
            )
        }
        #[inline(always)]
        unsafe fn load(acc: &ProductRow) -> (Neon, Neon, Neon) {
            // SAFETY: every coefficient has a complete pair; only the first pair holds this path's sum.
            unsafe {
                (
                    Neon::load(acc.0[0].as_ptr()),
                    Neon::load(acc.0[1].as_ptr()),
                    Neon::load(acc.0[2].as_ptr()),
                )
            }
        }
        #[inline(always)]
        unsafe fn store(s: (Neon, Neon, Neon), acc: &mut ProductRow) {
            // SAFETY: as for load; remaining pairs stay zero.
            unsafe {
                s.0.store(acc.0[0].as_mut_ptr());
                s.1.store(acc.0[1].as_mut_ptr());
                s.2.store(acc.0[2].as_mut_ptr());
            }
        }
        let stride = 3usize.pow((R - 1) as u32);
        for at in 0..stride {
            // SAFETY: R is in 1..=PRECOMPUTED_ROUNDS; the three points and each pair lie within their rows.
            unsafe {
                let mut s0 = load(&acc[at]);
                let mut s1 = load(&acc[at + stride]);
                let mut s2 = load(&acc[at + 2 * stride]);
                for c in (0..ROW).step_by(2) {
                    let k0 = Neon::load(fg[at].as_ptr().add(c));
                    let k1 = Neon::load(fg[at + stride].as_ptr().add(c));
                    let lo0 = Neon::load(bg[at].lo.as_ptr().add(c));
                    let lo1 = Neon::load(bg[at + stride].lo.as_ptr().add(c));
                    let hi0 = Neon::load(bg[at].hi.as_ptr().add(c));
                    let hi1 = Neon::load(bg[at + stride].hi.as_ptr().add(c));
                    let c20 = Neon::load(bg[at].c2.as_ptr().add(c));
                    let c21 = Neon::load(bg[at + stride].c2.as_ptr().add(c));
                    s0 = update(s0, k0, lo0, hi0, c20);
                    s1 = update(s1, k1, lo1, hi1, c21);
                    // The last digit at `inf`: the sum of its values at 0 and 1, formed in registers.
                    s2 = update(s2, k0.xor(k1), lo0.xor(lo1), hi0.xor(hi1), c20.xor(c21));
                }
                store(s0, &mut acc[at]);
                store(s1, &mut acc[at + stride]);
                store(s2, &mut acc[at + 2 * stride]);
            }
        }
    }

    /// Adds `e * f[x]` to word `x`'s sums for eight base words as the AVX-512 kernel does, a register at a time.
    ///
    /// # Safety
    ///
    /// Requires the features of `V`.
    #[inline(always)]
    pub(super) unsafe fn fold_base_acc<V: Clmul>(acc: &mut [[u64; ROW]; 6], e: &LaneWeight, f: &[F64; ROW]) {
        for c in (0..ROW).step_by(V::WORDS) {
            // SAFETY: as in `mul_acc`; `F64` is a qword.
            unsafe {
                let kv = V::load(f.as_ptr().add(c).cast());
                mul_by_words(acc, e, c, kv);
            }
        }
    }

    /// Adds the six products of `e` by the words `kv` to qwords `c..` of the rows, in the many-bit fold's order.
    ///
    /// # Safety
    ///
    /// Requires the features of `V`, and `c + V::WORDS <= ROW`.
    #[inline(always)]
    unsafe fn mul_by_words<V: Clmul>(acc: &mut [[u64; ROW]; 6], e: &LaneWeight, c: usize, kv: V) {
        // SAFETY: the caller keeps `c + V::WORDS` within every row.
        unsafe {
            let rows = acc.each_mut().map(|row| row.as_mut_ptr().add(c));
            let t01 = V::load(e.pairs.as_ptr().add(c));
            let t2 = V::load(e.highs.as_ptr().add(c));
            let products = [
                t01.mul::<0x00>(kv),
                t01.mul::<0x01>(kv),
                t01.mul::<0x10>(kv),
                t01.mul::<0x11>(kv),
                t2.mul::<0x00>(kv),
                t2.mul::<0x11>(kv),
            ];
            for (at, p) in rows.into_iter().zip(products) {
                V::load(at).xor(p).store(at);
            }
        }
    }

    /// The arm this target dispatches to.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    pub(super) type Best = Ymm;
    /// The arm this target dispatches to.
    #[cfg(all(
        target_arch = "x86_64",
        not(all(target_feature = "vpclmulqdq", target_feature = "avx2"))
    ))]
    pub(super) type Best = Xmm;
    /// The arm this target dispatches to.
    #[cfg(target_arch = "aarch64")]
    pub(super) type Best = Neon;
}

/// The sums of the first pass, from which the first `rounds` lane rounds' messages follow.
pub(crate) struct InitialRounds {
    /// The number of lane rounds the sums cover, `min(PRECOMPUTED_ROUNDS, initial_k)`.
    pub(super) rounds: usize,
    /// `sum f(d) * b(d)` at each point `d` of `{0, 1, inf}^rounds`, over every lane group and word offset.
    ///
    /// Point `d` sits at the index whose ternary digit `i` is digit `i` of `d`, with `inf` as 2.
    grid: Vec<F192>,
}

impl InitialRounds {
    /// Lane round `j`'s message, given the challenges `rs` of the rounds before it.
    ///
    /// # Panics
    ///
    /// Unless `j < rounds` and `rs` holds exactly `j` challenges.
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
///
/// # Panics
///
/// If `block` is not a power of two dividing the witness's length, or if `initial_k` is zero.
pub(super) fn first_pass(f: &[F64], block: usize, initial_k: usize, w: &dyn InitialWeight) -> InitialRounds {
    assert!(block.is_power_of_two() && f.len().is_multiple_of(block));
    let rounds = PRECOMPUTED_ROUNDS.min(initial_k);
    assert!(rounds >= 1, "at least one lane round");
    let n_lanes = f.len() / block;
    // Whole groups first: the lane count rounded down to a multiple of `2^rounds`.
    let whole = n_lanes >> rounds << rounds;
    let mut grid = if whole > 0 {
        grid_pass(rounds, f, block, w, 0..whole)
    } else {
        vec![F192::ZERO; 3usize.pow(rounds as u32)]
    };
    // A partial last group is summed over the digits its lanes reach.
    // Past those digits every lane bit is clear: at 1 the group is empty, and at 0 and at inf it has the tail's sums.
    if whole < n_lanes {
        let digits = (n_lanes - whole).next_power_of_two().ilog2() as usize;
        let tail = grid_pass(digits, f, block, w, whole..n_lanes);
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

/// The grid sums over `lanes` with `rounds` digits: whole groups, or one group whose missing lanes are zero.
///
/// # Panics
///
/// If `rounds` exceeds `PRECOMPUTED_ROUNDS`.
fn grid_pass(rounds: usize, f: &[F64], block: usize, w: &dyn InitialWeight, lanes: Range<usize>) -> Vec<F192> {
    match rounds {
        0 => grid_pass_with::<0>(f, block, w, lanes),
        1 => grid_pass_with::<1>(f, block, w, lanes),
        2 => grid_pass_with::<2>(f, block, w, lanes),
        3 => grid_pass_with::<3>(f, block, w, lanes),
        4 => grid_pass_with::<4>(f, block, w, lanes),
        _ => unreachable!("at most PRECOMPUTED_ROUNDS digits"),
    }
}

/// The grid sums over `lanes` for `R` digits, with `R` known at compile time.
fn grid_pass_with<const R: usize>(f: &[F64], block: usize, w: &dyn InitialWeight, lanes: Range<usize>) -> Vec<F192> {
    let group = 1 << R;
    let points = 3usize.pow(R as u32);
    // The weight is filled one aligned chunk at a time, or one whole block below that.
    let chunk = block.min(INITIAL_BASIS_CHUNK);
    let per = block / chunk;
    static ZERO_WORDS: [F64; INITIAL_BASIS_CHUNK] = [F64::ZERO; INITIAL_BASIS_CHUNK];
    static ZERO_WEIGHTS: [F192; INITIAL_BASIS_CHUNK] = [F192::ZERO; INITIAL_BASIS_CHUNK];

    struct Scratch {
        /// One chunk of filled weights per lane of the group.
        raw: [[F192; INITIAL_BASIS_CHUNK]; GROUP],
        /// Every grid point's words, one row of offsets.
        fg: [[u64; ROW]; GRID],
        /// Every grid point's weights, one row of offsets.
        bg: [WeightRow; GRID],
    }
    type Acc = [ProductRow; GRID];
    // A chunk shorter than a row fills only `width` offsets: the rest of every row stays zero, and so do its products.
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
                w.fill(at, &mut raw[..chunk]);
                bs[l] = &raw[..chunk];
            }
        }
        // Per row of offsets: put each lane at its grid point, extend the grid, accumulate the products.
        for x in (0..chunk).step_by(ROW) {
            for l in 0..group {
                for (d, s) in fg[LANE_IN_GRID[l]].iter_mut().zip(&fs[l][x..x + width]) {
                    *d = s.0;
                }
                bg[LANE_IN_GRID[l]] = WeightRow::pack(&bs[l][x..x + width]);
            }
            #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
            accumulate_grid::<R>(fg, bg, acc);
            #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
            {
                extend_grid::<_, R>(fg, |a, b| std::array::from_fn(|i| a[i] ^ b[i]));
                extend_grid::<_, R>(bg, WeightRow::add);
                for (a, (k, w)) in acc.iter_mut().zip(fg.iter().zip(bg.iter())).take(points) {
                    a.mul_acc(w, k);
                }
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

/// A lane's `eq` weight `e`, laid out for the many-bit fold's products.
#[derive(Clone, Copy)]
#[repr(C, align(64))]
pub(super) struct LaneWeight {
    /// `[c0, c1]` of `e` in every 128-bit lane.
    pairs: [u64; ROW],
    /// `c2` of `e` in every qword.
    highs: [u64; ROW],
}

impl LaneWeight {
    /// The layout of `e`.
    pub(super) fn new(e: F192) -> Self {
        Self {
            pairs: std::array::from_fn(|i| if i.is_multiple_of(2) { e.c0 } else { e.c1 }),
            highs: [e.c2; ROW],
        }
    }
}

/// Unreduced sums `sum_lanes e * f` of base words, for a window of up to `INITIAL_BASIS_CHUNK` words.
///
/// Each row of `ROW` words holds six vectors of four 128-bit sums:
///
/// - vectors 0 and 1: coefficients 0 and 1 of the even words, 128-bit lane `m` for word `2m`;
/// - vectors 2 and 3: the same for the odd words, lane `m` for word `2m + 1`;
/// - vectors 4 and 5: coefficient 2, of the even words, then of the odd words.
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
    /// Adds `e * f[x]` to word `x`'s sums, for one lane's window `f` of base words.
    #[inline]
    pub(super) fn add_base(&mut self, e: &LaneWeight, f: &[F64]) {
        for (row, f) in self.0.iter_mut().zip(padded_rows(f)) {
            #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
            // SAFETY: both features are enabled at compile time.
            unsafe {
                avx512::fold_base_acc(row, e, &f);
            }
            #[cfg(any(
                all(
                    target_arch = "x86_64",
                    target_feature = "pclmulqdq",
                    not(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))
                ),
                all(target_arch = "aarch64", target_feature = "aes")
            ))]
            // SAFETY: the features of the target's arm are enabled at compile time.
            unsafe {
                lanes::fold_base_acc::<lanes::Best>(row, e, &f);
            }
            #[cfg(not(any(
                all(target_arch = "x86_64", target_feature = "pclmulqdq"),
                all(target_arch = "aarch64", target_feature = "aes")
            )))]
            for (x, w) in f.iter().enumerate() {
                Self::add_products(row, e, x, w.0);
            }
        }
    }

    /// Adds the products of `e` by the word `c` to word `x`'s sums in `row`.
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "pclmulqdq"),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    fn add_products(row: &mut [[u64; ROW]; 6], e: &LaneWeight, x: usize, c: u64) {
        let (j, slots) = (x / 2 * 2, if x.is_multiple_of(2) { [0, 1, 4] } else { [2, 3, 5] });
        let products = [e.pairs[0], e.pairs[1], e.highs[0]].map(|t| mul_wide(t, c));
        for (s, p) in slots.into_iter().zip(products) {
            row[s][j] ^= p as u64;
            row[s][j + 1] ^= (p >> 64) as u64;
        }
    }

    /// Writes word `x`'s reduced sum to `dst[x]`, for every word of `dst`.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::whir::sumcheck::tests::Table;
    use primitives::test_util::Rng;

    #[test]
    fn grid_extension_products_match_scalar_definition() {
        // Invariant: each grid point's sum is, per offset, the product of its lanes' summed weights and XORed words.
        /// The product in `K`, bit by bit.
        fn scalar_mul(mut a: u64, mut b: u64) -> u64 {
            let mut p = 0;
            for _ in 0..64 {
                if b & 1 != 0 {
                    p ^= a;
                }
                let carry = a >> 63;
                a <<= 1;
                if carry != 0 {
                    a ^= 0x1b;
                }
                b >>= 1;
            }
            p
        }
        let mut rng = Rng::new(0x671D);
        for rounds in 1..=PRECOMPUTED_ROUNDS {
            for block in [1, 2, 4, 8, 16] {
                for lanes in [1, (1 << rounds) - 1, 1 << rounds, (1 << rounds) + 3] {
                    let f: Vec<F64> = (0..block * lanes).map(|_| F64(rng.next_u64())).collect();
                    let weight = rng.ext_vec(f.len());
                    let table = Table {
                        weight: weight.clone(),
                        block,
                    };
                    let got = first_pass(&f, block, rounds, &table);
                    for (point, &sum) in got.grid.iter().enumerate() {
                        let mut want = F192::ZERO;
                        for start in (0..lanes).step_by(1 << rounds) {
                            for x in 0..block {
                                let (mut k, mut e) = (0, F192::ZERO);
                                for lane in 0..(1 << rounds).min(lanes - start) {
                                    let included = (0..rounds).all(|bit| {
                                        let digit = point / 3usize.pow(bit as u32) % 3;
                                        digit == 2 || digit == (lane >> bit) & 1
                                    });
                                    if included {
                                        k ^= f[(start + lane) * block + x].0;
                                        e += weight[(start + lane) * block + x];
                                    }
                                }
                                want += F192::new(scalar_mul(e.c0, k), scalar_mul(e.c1, k), scalar_mul(e.c2, k));
                            }
                        }
                        assert_eq!(
                            sum, want,
                            "rounds={rounds}, block={block}, lanes={lanes}, point={point}"
                        );
                    }
                }
            }
        }
    }

    #[cfg(any(
        all(target_arch = "x86_64", target_feature = "pclmulqdq"),
        all(target_arch = "aarch64", target_feature = "aes")
    ))]
    #[test]
    fn every_lane_arm_matches_definition() {
        // Invariant: every arm this target compiles accumulates the definition's products, not only the dispatched one.
        fn check<V: lanes::Clmul>(name: &str) {
            let mut rng = Rng::new(0xF125_79A5);
            // The grid pass: the sum of every weight's product by its word.
            let mut acc = ProductRow::default();
            let mut want = F192::ZERO;
            for _ in 0..4 {
                let w = rng.ext_vec(ROW);
                let k: [u64; ROW] = std::array::from_fn(|_| rng.next_u64());
                // SAFETY: the caller compiles `V` only with its features.
                unsafe { lanes::mul_acc::<V>(&mut acc, &WeightRow::pack(&w), &k) };
                want += w.iter().zip(k).fold(F192::ZERO, |s, (w, k)| s + w.mul_base(F64(k)));
            }
            assert_eq!(acc.sum(), want, "{name}: grid pass");

            // The many-bit fold: per word, the sum over lanes of the lane weight times the word.
            let mut fold = WeightFold::default();
            let mut want = [F192::ZERO; ROW];
            for _ in 0..3 {
                let e = rng.ext();
                let f: [F64; ROW] = std::array::from_fn(|_| F64(rng.next_u64()));
                // SAFETY: as above.
                unsafe { lanes::fold_base_acc::<V>(&mut fold.0[0], &LaneWeight::new(e), &f) };
                for x in 0..ROW {
                    want[x] += e.mul_base(f[x]);
                }
            }
            let mut got = [F192::ZERO; ROW];
            fold.write(&mut got);
            assert_eq!(got, want, "{name}: fold of base words");
        }
        #[cfg(target_arch = "x86_64")]
        check::<lanes::Xmm>("pclmulqdq");
        #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
        check::<lanes::Ymm>("vpclmulqdq");
        #[cfg(target_arch = "aarch64")]
        check::<lanes::Neon>("neon");
    }
}
