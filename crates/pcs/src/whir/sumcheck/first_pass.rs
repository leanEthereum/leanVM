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

use super::{
    Basis, BasisFill, FIRST_PASS_PAR_THRESHOLD, INITIAL_BASIS_CHUNK, KEEP_WEIGHT_MAX_THREADS, PRECOMPUTED_ROUNDS,
    SumcheckMessage, window,
};
use parallel::SendPtr;
use primitives::bit_fold;
#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "pclmulqdq"),
    all(target_arch = "aarch64", target_feature = "aes")
)))]
use primitives::field::gf2_64::mul_wide;
use primitives::field::{F64, F192};
use primitives::stream::Stream;
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

/// The AVX-512 kernels' products, one register of 128-bit lanes at a time, on narrower registers: 256-bit VPCLMULQDQ
/// with AVX2, 128-bit PCLMULQDQ without, and PMULL on aarch64.
///
/// On an AVX-512 target only the tests use it.
#[cfg(any(
    all(target_arch = "x86_64", target_feature = "pclmulqdq"),
    all(target_arch = "aarch64", target_feature = "aes")
))]
#[cfg_attr(all(target_feature = "vpclmulqdq", target_feature = "avx512f"), allow(dead_code))]
mod lanes {
    use super::{F64, F192, LaneWeight, ProductRow, ROW, WeightRow};
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

        /// # Safety
        ///
        /// `p` must be readable for `WORDS` qwords.
        unsafe fn load(p: *const u64) -> Self;

        /// # Safety
        ///
        /// `p` must be writable for `WORDS` qwords.
        unsafe fn store(self, p: *mut u64);

        /// The register whose qword `i` is `word(i)`, packed from scalars.
        fn from_words(word: impl Fn(usize) -> u64) -> Self;

        /// In every lane, qword `IMM & 1` of `self` by qword `(IMM >> 4) & 1` of `other` (the x86 immediate).
        fn mul<const IMM: i32>(self, other: Self) -> Self;

        fn xor(self, other: Self) -> Self;

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
            // SAFETY: the impl exists only when the crate is built with AVX2, and the caller guarantees four
            // readable qwords at `p`; the load is unaligned.
            Self(unsafe { _mm256_loadu_si256(p.cast()) })
        }

        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            // SAFETY: as for `load`, writable.
            unsafe { _mm256_storeu_si256(p.cast(), self.0) }
        }

        #[inline(always)]
        fn from_words(word: impl Fn(usize) -> u64) -> Self {
            // SAFETY: the impl exists only when the crate is built with AVX2; registers only.
            Self(unsafe { _mm256_set_epi64x(word(3) as i64, word(2) as i64, word(1) as i64, word(0) as i64) })
        }

        #[inline(always)]
        fn mul<const IMM: i32>(self, other: Self) -> Self {
            // SAFETY: the impl exists only when the crate is built with VPCLMULQDQ and AVX2; registers only.
            Self(unsafe { _mm256_clmulepi64_epi128::<IMM>(self.0, other.0) })
        }

        #[inline(always)]
        fn xor(self, other: Self) -> Self {
            // SAFETY: as for `from_words`.
            Self(unsafe { _mm256_xor_si256(self.0, other.0) })
        }

        #[inline(always)]
        fn xor3(self, b: Self, c: Self) -> Self {
            // SAFETY: as for `from_words`.
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
            // SAFETY: SSE2 is part of the x86-64 baseline, and the caller guarantees two readable qwords at `p`; the
            // load is unaligned.
            Self(unsafe { _mm_loadu_si128(p.cast()) })
        }

        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            // SAFETY: as for `load`, writable.
            unsafe { _mm_storeu_si128(p.cast(), self.0) }
        }

        #[inline(always)]
        fn from_words(word: impl Fn(usize) -> u64) -> Self {
            // SAFETY: SSE2 is part of the x86-64 baseline; registers only.
            Self(unsafe { _mm_set_epi64x(word(1) as i64, word(0) as i64) })
        }

        #[inline(always)]
        fn mul<const IMM: i32>(self, other: Self) -> Self {
            // SAFETY: the impl exists only when the crate is built with PCLMULQDQ; registers only.
            Self(unsafe { _mm_clmulepi64_si128::<IMM>(self.0, other.0) })
        }

        #[inline(always)]
        fn xor(self, other: Self) -> Self {
            // SAFETY: as for `from_words`.
            Self(unsafe { _mm_xor_si128(self.0, other.0) })
        }

        #[inline(always)]
        fn xor3(self, b: Self, c: Self) -> Self {
            // SAFETY: as for `from_words`.
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
        fn from_words(word: impl Fn(usize) -> u64) -> Self {
            // SAFETY: NEON is part of the aarch64 baseline; registers only.
            Self(unsafe { vcombine_u64(vcreate_u64(word(0)), vcreate_u64(word(1))) })
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

    /// The products of the AVX-512 `mul_acc`, a register at a time.
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

    /// The products of the AVX-512 `fold_acc`, a register at a time, each coefficient packed from scalars.
    ///
    /// # Safety
    ///
    /// Requires the features of `V`.
    #[inline(always)]
    pub(super) unsafe fn fold_acc<V: Clmul>(acc: &mut [[u64; ROW]; 6], e: &LaneWeight, b: &[F192; ROW]) {
        for c in (0..ROW).step_by(V::WORDS) {
            let kv = |k: usize| V::from_words(|i| [b[c + i].c0, b[c + i].c1, b[c + i].c2][k]);
            // SAFETY: as in `mul_acc`.
            unsafe { mul_by_words(acc, e, c, [kv(0), kv(1), kv(2)].into_iter().enumerate()) };
        }
    }

    /// The products of the AVX-512 `fold_base_acc`, a register at a time.
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
                mul_by_words(acc, e, c, std::iter::once((0, kv)));
            }
        }
    }

    /// Add the six products of `e·y^k` by the words `kv`, for each `(k, kv)`, to qwords `c..` of the rows, in
    /// [`super::WeightFold`]'s order.
    ///
    /// # Safety
    ///
    /// Requires the features of `V`, and `c + V::WORDS <= ROW`.
    #[inline(always)]
    unsafe fn mul_by_words<V: Clmul>(
        acc: &mut [[u64; ROW]; 6],
        e: &LaneWeight,
        c: usize,
        words: impl Iterator<Item = (usize, V)>,
    ) {
        // SAFETY: the caller keeps `c + V::WORDS` within every row.
        unsafe {
            let [r0, r1, r2, r3, r4, r5] = acc.each_mut().map(|row| row.as_mut_ptr().add(c));
            let (mut s0, mut s1, mut s2) = (V::load(r0), V::load(r1), V::load(r2));
            let (mut s3, mut s4, mut s5) = (V::load(r3), V::load(r4), V::load(r5));
            for (k, kv) in words {
                let t01 = V::load(e.pairs[k].as_ptr().add(c));
                let t2 = V::load(e.highs[k].as_ptr().add(c));
                s0 = s0.xor(t01.mul::<0x00>(kv));
                s1 = s1.xor(t01.mul::<0x01>(kv));
                s2 = s2.xor(t01.mul::<0x10>(kv));
                s3 = s3.xor(t01.mul::<0x11>(kv));
                s4 = s4.xor(t2.mul::<0x00>(kv));
                s5 = s5.xor(t2.mul::<0x11>(kv));
            }
            for (at, s) in [(r0, s0), (r1, s1), (r2, s2), (r3, s3), (r4, s4), (r5, s5)] {
                s.store(at);
            }
        }
    }

    /// The arm this target dispatches to.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    pub(super) type Best = Ymm;
    #[cfg(all(
        target_arch = "x86_64",
        not(all(target_feature = "vpclmulqdq", target_feature = "avx2"))
    ))]
    pub(super) type Best = Xmm;
    #[cfg(target_arch = "aarch64")]
    pub(super) type Best = Neon;
}

/// The sums of the first pass, from which the first `rounds` lane rounds' messages follow.
pub(crate) struct InitialRounds {
    pub(super) rounds: usize,
    /// `sum f(d) * b(d)` at each `d` of `{0, 1, inf}^rounds`, over every lane group and offset.
    grid: Vec<F192>,
}

impl InitialRounds {
    /// Compare every grid element and every kept weight on the real opening, outside timed Basis.
    #[cfg(all(leanvm_basis_staged, leanvm_basis_check))]
    pub(crate) fn assert_matches_virtual(
        &self,
        f: &[F64],
        block: usize,
        initial_k: usize,
        fill: &BasisFill<'_>,
        weights: &[F192],
    ) {
        let (reference, kept) = initial_rounds_kept(f, block, initial_k, fill);
        assert_eq!(self.rounds, reference.rounds);
        assert_eq!(self.grid, reference.grid, "staged grid differs from fused first pass");
        assert_eq!(weights, kept, "staged weights differ from fused first pass");
    }

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
    first_pass(f, block, initial_k, b, None)
}

/// [`initial_rounds`] over a regenerated weight, and the weight the first fold then reads.
///
/// The byte tables always keep the weight. SIMD backends keep it on small pools and refill it on larger ones.
pub(crate) fn initial_rounds_virtual<'a>(
    f: &[F64],
    block: usize,
    initial_k: usize,
    fill: &'a BasisFill<'a>,
) -> (InitialRounds, Basis<'a>) {
    tracing::info!(
        keep_weight = bit_fold::PORTABLE || parallel::num_threads() <= KEEP_WEIGHT_MAX_THREADS,
        kept_bytes = if bit_fold::PORTABLE || parallel::num_threads() <= KEEP_WEIGHT_MAX_THREADS {
            f.len() * size_of::<F192>()
        } else {
            0
        },
        portable_map = bit_fold::PORTABLE,
        "Basis retention"
    );
    if bit_fold::PORTABLE || parallel::num_threads() <= KEEP_WEIGHT_MAX_THREADS {
        let (rounds, kept) = initial_rounds_kept(f, block, initial_k, fill);
        (rounds, Basis::Dense(kept))
    } else {
        (
            first_pass(f, block, initial_k, &Basis::Virtual(fill), None),
            Basis::Virtual(fill),
        )
    }
}

/// [`initial_rounds`] over a regenerated weight, which it also writes out whole.
fn initial_rounds_kept(f: &[F64], block: usize, initial_k: usize, fill: &BasisFill<'_>) -> (InitialRounds, Vec<F192>) {
    let mut kept = tracing::info_span!("Basis kept allocation", bytes = f.len() * size_of::<F192>())
        .in_scope(|| Box::<[F192]>::new_uninit_slice(f.len()));
    let rounds = first_pass(
        f,
        block,
        initial_k,
        &Basis::Virtual(fill),
        Some(SendPtr(kept.as_mut_ptr().cast::<F192>())),
    );
    // SAFETY: the first pass filled every window of every lane of `f` once, and kept each in its slots.
    (rounds, unsafe { kept.assume_init() }.into_vec())
}

/// [`initial_rounds`], writing each window of the weight it reads to `keep` when given.
fn first_pass(f: &[F64], block: usize, initial_k: usize, b: &Basis<'_>, keep: Option<SendPtr<F192>>) -> InitialRounds {
    if let Basis::Dense(b) = b {
        assert_eq!(b.len(), f.len());
    }
    assert!(block.is_power_of_two() && f.len().is_multiple_of(block));
    let rounds = PRECOMPUTED_ROUNDS.min(initial_k);
    assert!(rounds >= 1, "at least one lane round");
    let n_lanes = f.len() / block;
    let whole = n_lanes >> rounds << rounds;
    let mut grid = if whole > 0 {
        grid_pass(rounds, f, block, b, 0..whole, keep)
    } else {
        vec![F192::ZERO; 3usize.pow(rounds as u32)]
    };
    // A partial last group is summed over the digits its lanes reach. Past them every
    // lane bit is clear: at 1 the group has nothing, and at 0 and at inf it has those sums.
    if whole < n_lanes {
        let digits = (n_lanes - whole).next_power_of_two().ilog2() as usize;
        let tail = grid_pass(digits, f, block, b, whole..n_lanes, keep);
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
fn grid_pass(
    rounds: usize,
    f: &[F64],
    block: usize,
    b: &Basis<'_>,
    lanes: Range<usize>,
    keep: Option<SendPtr<F192>>,
) -> Vec<F192> {
    match rounds {
        0 => grid_pass_with::<0>(f, block, b, lanes, keep),
        1 => grid_pass_with::<1>(f, block, b, lanes, keep),
        2 => grid_pass_with::<2>(f, block, b, lanes, keep),
        3 => grid_pass_with::<3>(f, block, b, lanes, keep),
        4 => grid_pass_with::<4>(f, block, b, lanes, keep),
        _ => unreachable!("at most PRECOMPUTED_ROUNDS digits"),
    }
}

fn grid_pass_with<const R: usize>(
    f: &[F64],
    block: usize,
    b: &Basis<'_>,
    lanes: Range<usize>,
    keep: Option<SendPtr<F192>>,
) -> Vec<F192> {
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
                if let Some(keep) = keep {
                    // SAFETY: `keep` holds `f.len()` weights, and no other task fills the window at `at`.
                    Stream::new().copy(unsafe { keep.slice(at, chunk) }, bs[l]);
                }
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
    let _span = tracing::info_span!(
        "Basis grid pass",
        rounds = R,
        group,
        points,
        lanes = lanes.len(),
        block,
        chunk,
        tasks = n_tasks,
        virtual_weight = matches!(b, Basis::Virtual(_)),
        keep_weight = keep.is_some(),
        witness_bytes = lanes.len() * block * size_of::<F64>(),
        weight_bytes = lanes.len() * block * size_of::<F192>(),
        scratch_bytes = size_of::<Scratch>(),
        accumulator_bytes = size_of::<Acc>(),
        grid_rows = n_tasks * chunk.div_ceil(ROW),
        mixed_products = n_tasks * chunk.div_ceil(ROW) * ROW * points,
        clmul_backend = if cfg!(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")) {
            "vpclmul512"
        } else if cfg!(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")) {
            "vpclmul256"
        } else if cfg!(all(target_arch = "x86_64", target_feature = "pclmulqdq")) {
            "pclmul128"
        } else if cfg!(all(target_arch = "aarch64", target_feature = "aes")) {
            "pmull128"
        } else {
            "portable"
        },
    ).entered();
    let new_scratch = || {
        let _span = tracing::info_span!("Basis scratch allocation zero", bytes = size_of::<Scratch>()).entered();
        Box::new(Scratch {
            raw: [[F192::ZERO; INITIAL_BASIS_CHUNK]; GROUP],
            fg: [[0; ROW]; GRID],
            bg: [WeightRow::default(); GRID],
        })
    };
    let new_acc = || tracing::info_span!("Basis accumulator allocation zero", bytes = size_of::<Acc>())
        .in_scope(|| Box::new([ProductRow::default(); GRID]));
    let accumulation_span = tracing::info_span!("Basis fill pack accumulate").entered();
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
    drop(accumulation_span);
    tracing::info_span!("Basis final sum", points)
        .in_scope(|| acc[..points].iter().map(ProductRow::sum).collect())
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
#[derive(Clone, Copy)]
#[cfg_attr(not(leanvm_basis_chunk1024), derive(Default))]
#[repr(C, align(64))]
pub(super) struct WeightFold([[[u64; ROW]; 6]; INITIAL_BASIS_CHUNK / ROW]);

#[cfg(leanvm_basis_chunk1024)]
impl Default for WeightFold {
    fn default() -> Self {
        Self([[[0; ROW]; 6]; INITIAL_BASIS_CHUNK / ROW])
    }
}

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
                lanes::fold_acc::<lanes::Best>(row, e, &b);
            }
            #[cfg(not(any(
                all(target_arch = "x86_64", target_feature = "pclmulqdq"),
                all(target_arch = "aarch64", target_feature = "aes")
            )))]
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
                Self::add_products(row, e, 0, x, w.0);
            }
        }
    }

    /// Add the products of word `c` by `e·y^k` to value `x` of `row`.
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "pclmulqdq"),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    fn add_products(row: &mut [[u64; ROW]; 6], e: &LaneWeight, k: usize, x: usize, c: u64) {
        let (j, slots) = (x / 2 * 2, if x.is_multiple_of(2) { [0, 1, 4] } else { [2, 3, 5] });
        let products = [e.pairs[k][0], e.pairs[k][1], e.highs[k][0]].map(|t| mul_wide(t, c));
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::whir::INITIAL_FOLDING_FACTOR;
    use primitives::test_util::Rng;

    #[test]
    fn the_kept_weight_is_the_filled_one() {
        // Invariant: writing the weight out leaves the sums alone and keeps every word of every lane, partial groups
        // and blocks below one fill chunk included.
        let mut rng = Rng::new(0x6EE9);
        for block in [1, 16, INITIAL_BASIS_CHUNK, 4 * INITIAL_BASIS_CHUNK] {
            for lanes in [1, 3, 5, GROUP - 1, GROUP, GROUP + 1, 37] {
                let f: Vec<F64> = (0..block * lanes).map(|_| F64(rng.next_u64())).collect();
                let weight = rng.ext_vec(f.len());
                let fill = |start: usize, out: &mut [F192]| out.copy_from_slice(&weight[start..start + out.len()]);
                let (rounds, kept) = initial_rounds_kept(&f, block, INITIAL_FOLDING_FACTOR, &fill);
                let expected = initial_rounds(&f, block, INITIAL_FOLDING_FACTOR, &Basis::Dense(weight.clone()));
                assert_eq!(rounds.grid, expected.grid, "block={block}, lanes={lanes}");
                assert_eq!(kept, weight, "block={block}, lanes={lanes}");
            }
        }
    }

    /// Every arm this target compiles accumulates the products of the definition, not only the dispatched one.
    #[cfg(any(
        all(target_arch = "x86_64", target_feature = "pclmulqdq"),
        all(target_arch = "aarch64", target_feature = "aes")
    ))]
    #[test]
    fn every_lane_arm_matches_definition() {
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

            // The many-bit fold: per value, the sum over lanes of the lane weight times the value.
            let mut fold = WeightFold::default();
            let (mut want, mut want_base) = ([F192::ZERO; ROW], [F192::ZERO; ROW]);
            for _ in 0..3 {
                let e = rng.ext();
                let b: [F192; ROW] = std::array::from_fn(|_| rng.ext());
                let f: [F64; ROW] = std::array::from_fn(|_| F64(rng.next_u64()));
                // SAFETY: as above.
                unsafe {
                    lanes::fold_acc::<V>(&mut fold.0[0], &LaneWeight::new(e), &b);
                    lanes::fold_base_acc::<V>(&mut fold.0[1], &LaneWeight::new(e), &f);
                }
                for x in 0..ROW {
                    want[x] += e * b[x];
                    want_base[x] += e.mul_base(f[x]);
                }
            }
            let mut got = [F192::ZERO; 2 * ROW];
            fold.write(&mut got);
            assert_eq!(got[..ROW], want, "{name}: fold");
            assert_eq!(got[ROW..], want_base, "{name}: fold of base words");
        }
        #[cfg(target_arch = "x86_64")]
        check::<lanes::Xmm>("pclmulqdq");
        #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
        check::<lanes::Ymm>("vpclmulqdq");
        #[cfg(target_arch = "aarch64")]
        check::<lanes::Neon>("neon");
    }
}
