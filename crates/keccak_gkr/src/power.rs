//! The field in the power basis of a challenge `s`: an element is its 192 coefficients on
//! `1, s, ..., s^191`, and a product is a carry-less one reduced modulo the minimal polynomial
//! of `s`.
//!
//! The rounds after the bit-level ones stay in this basis. Their tables come out of carry-less
//! sums already in it, and moving every entry to the standard basis would cost more than
//! reducing by a dense modulus does.
//!
//! A table row is laid out by word: word `k` of entry `j` at `k * width + j`.

use primitives::field::F192;
use primitives::field::gf2_64::mul_wide;

use crate::basis::{PolyEval, PowerBasis};

pub type Element = [u64; 3];

/// A row kernel's vector form, where one is compiled and `width` is whole vectors of it, else
/// `portable`. The caller bounds every row.
macro_rules! row_kernel {
    ($width:expr, $kernel:ident($($arg:expr),*), $portable:expr) => {
        cfg_select! {
            all(
                target_arch = "x86_64",
                target_feature = "avx512f",
                target_feature = "avx512bw",
                target_feature = "vpclmulqdq",
                target_feature = "gfni"
            ) => {
                if $width.is_multiple_of(8) {
                    // SAFETY: the features are enabled at compile time, and the caller bounds every row.
                    unsafe { x86::$kernel($($arg),*) }
                } else {
                    $portable
                }
            }
            all(target_arch = "aarch64", target_feature = "aes") => {
                if $width.is_multiple_of(2) {
                    // SAFETY: the feature is enabled at compile time, and the caller bounds every row.
                    unsafe { neon::$kernel($($arg),*) }
                } else {
                    $portable
                }
            }
            _ => $portable,
        }
    };
}

pub struct PowerField {
    pub basis: PowerBasis,
    /// `s^192`, the modulus without its leading term.
    modulus: Element,
    /// `floor(x^384 / modulus)` without its leading term, for Barrett's reduction.
    barrett: Element,
    eval: PolyEval,
}

/// The carry-less product of two elements, six words.
#[inline(always)]
fn mul_wide3(a: &Element, b: &Element) -> [u64; 6] {
    let mut out = [0u64; 6];
    for i in 0..3 {
        for k in 0..3 {
            let p = mul_wide(a[i], b[k]);
            out[i + k] ^= p as u64;
            out[i + k + 1] ^= (p >> 64) as u64;
        }
    }
    out
}

impl PowerField {
    /// `None` when `s` lies in a proper subfield.
    pub fn new(s: F192) -> Option<Self> {
        let basis = PowerBasis::new(s)?;
        let mut power = F192::ONE;
        for _ in 0..192 {
            power *= s;
        }
        let modulus = basis.to_poly(power);
        // Long division of `x^384` by `x^192 + modulus`.
        let mut dividend = [0u64; 7];
        dividend[6] = 1;
        let mut barrett = [0u64; 3];
        for bit in (192..=384).rev() {
            if dividend[bit / 64] >> (bit % 64) & 1 == 1 {
                let shift = bit - 192;
                if shift < 192 {
                    barrett[shift / 64] |= 1 << (shift % 64);
                }
                dividend[bit / 64] ^= 1 << (bit % 64);
                for b in (0..192).filter(|b| modulus[b / 64] >> (b % 64) & 1 == 1) {
                    dividend[(b + shift) / 64] ^= 1 << ((b + shift) % 64);
                }
            }
        }
        Some(Self {
            basis,
            modulus,
            barrett,
            eval: PolyEval::new(s, 24),
        })
    }

    pub fn from_field(&self, a: F192) -> Element {
        self.basis.to_poly(a)
    }

    pub fn to_field(&self, a: &Element) -> F192 {
        self.eval.eval(a)
    }

    /// A polynomial of at most 384 coefficients, modulo the minimal polynomial.
    #[inline(always)]
    pub fn reduce(&self, p: &[u64; 6]) -> Element {
        let high: Element = [p[3], p[4], p[5]];
        // The quotient: `high`, plus the top half of `high * barrett`.
        let t = mul_wide3(&high, &self.barrett);
        let q: Element = [high[0] ^ t[3], high[1] ^ t[4], high[2] ^ t[5]];
        let r = mul_wide3(&q, &self.modulus);
        [p[0] ^ r[0], p[1] ^ r[1], p[2] ^ r[2]]
    }

    #[inline(always)]
    pub fn mul(&self, a: &Element, b: &Element) -> Element {
        self.reduce(&mul_wide3(a, b))
    }

    /// `sum of a[j] * b[j]` and `sum of (a[j] + a'[j]) * (b[j] + b'[j])` over two pairs of rows,
    /// unreduced.
    pub fn dot_pair(&self, a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
        assert!(a.iter().chain(&b).all(|row| row.len() >= 3 * width));
        row_kernel!(width, dot_pair(a, b, width), dot_pair_portable(a, b, width))
    }

    /// `dst[j] = lo[j] + challenge * (lo[j] + hi[j])`.
    pub fn fold_row(&self, dst: &mut [u64], lo: &[u64], hi: &[u64], challenge: &Element, width: usize) {
        assert!(dst.len() >= 3 * width && lo.len() >= 3 * width && hi.len() >= 3 * width);
        row_kernel!(
            width,
            fold_row(self, dst, lo, hi, challenge, width),
            self.fold_row_portable(dst, lo, hi, challenge, width)
        )
    }

    /// `dst[j] = wide[j]` reduced, for a row of four-word polynomials laid out by word.
    pub fn reduce_row(&self, dst: &mut [u64], wide: &[u64], width: usize) {
        assert!(dst.len() >= 3 * width && wide.len() >= 4 * width);
        row_kernel!(
            width,
            reduce_row(self, dst, wide, width),
            self.reduce_row_portable(dst, wide, width)
        )
    }

    pub fn reduce_row_portable(&self, dst: &mut [u64], wide: &[u64], width: usize) {
        for j in 0..width {
            let p = [wide[j], wide[width + j], wide[2 * width + j], wide[3 * width + j], 0, 0];
            set(dst, width, j, &self.reduce(&p));
        }
    }

    /// `dst[j] = a[j] * b[j] + c[j]`.
    pub fn mul_row(&self, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        assert!(dst.len() >= 3 * width && [a, b, c].iter().all(|row| row.len() >= 3 * width));
        row_kernel!(
            width,
            mul_row(self, dst, a, b, c, width),
            self.mul_row_portable(dst, a, b, c, width)
        )
    }

    pub fn mul_row_portable(&self, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        for j in 0..width {
            let (p, c) = (self.mul(&get(a, width, j), &get(b, width, j)), get(c, width, j));
            set(dst, width, j, &[p[0] ^ c[0], p[1] ^ c[1], p[2] ^ c[2]]);
        }
    }

    pub fn fold_row_portable(&self, dst: &mut [u64], lo: &[u64], hi: &[u64], challenge: &Element, width: usize) {
        for j in 0..width {
            let (l, h) = (get(lo, width, j), get(hi, width, j));
            let delta = [l[0] ^ h[0], l[1] ^ h[1], l[2] ^ h[2]];
            let folded = self.mul(challenge, &delta);
            for k in 0..3 {
                dst[k * width + j] = l[k] ^ folded[k];
            }
        }
    }
}

/// Entry `j` of a row.
#[inline(always)]
pub fn get(row: &[u64], width: usize, j: usize) -> Element {
    [row[j], row[width + j], row[2 * width + j]]
}

#[inline(always)]
pub fn set(row: &mut [u64], width: usize, j: usize, value: &Element) {
    for k in 0..3 {
        row[k * width + j] = value[k];
    }
}

pub fn dot_pair_portable(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
    let (mut zero, mut infinity) = ([0u64; 6], [0u64; 6]);
    for j in 0..width {
        let (a0, a1, b0, b1) = (
            get(a[0], width, j),
            get(a[1], width, j),
            get(b[0], width, j),
            get(b[1], width, j),
        );
        let da = [a0[0] ^ a1[0], a0[1] ^ a1[1], a0[2] ^ a1[2]];
        let db = [b0[0] ^ b1[0], b0[1] ^ b1[1], b0[2] ^ b1[2]];
        for (acc, p) in [(&mut zero, mul_wide3(&a0, &b0)), (&mut infinity, mul_wide3(&da, &db))] {
            for (x, y) in acc.iter_mut().zip(p) {
                *x ^= y;
            }
        }
    }
    (zero, infinity)
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512bw",
    target_feature = "vpclmulqdq",
    target_feature = "gfni"
))]
mod x86 {
    use core::arch::x86_64::*;

    use super::*;

    #[inline(always)]
    unsafe fn load3(row: &[u64], width: usize, j: usize) -> [__m512i; 3] {
        unsafe { std::array::from_fn(|k| _mm512_loadu_si512(row.as_ptr().add(k * width + j).cast())) }
    }

    /// The products of eight pairs, as partial sums by word offset: lanes of `out[half][s]` hold
    /// the 128-bit sum of `a[i] * b[k]` over `i + k = s`, for the even or the odd four.
    #[inline(always)]
    unsafe fn partial(a: &[__m512i; 3], b: &[__m512i; 3]) -> [[__m512i; 5]; 2] {
        unsafe {
            let mut out = [[_mm512_setzero_si512(); 5]; 2];
            for i in 0..3 {
                for k in 0..3 {
                    out[0][i + k] = _mm512_xor_si512(out[0][i + k], _mm512_clmulepi64_epi128(a[i], b[k], 0x00));
                    out[1][i + k] = _mm512_xor_si512(out[1][i + k], _mm512_clmulepi64_epi128(a[i], b[k], 0x11));
                }
            }
            out
        }
    }

    #[inline(always)]
    unsafe fn xor3(a: &[__m512i; 3], b: &[__m512i; 3]) -> [__m512i; 3] {
        unsafe { std::array::from_fn(|k| _mm512_xor_si512(a[k], b[k])) }
    }

    pub unsafe fn dot_pair(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
        unsafe {
            let mut acc = [[_mm512_setzero_si512(); 5]; 2];
            for j in (0..width).step_by(8) {
                let (a0, a1, b0, b1) = (
                    load3(a[0], width, j),
                    load3(a[1], width, j),
                    load3(b[0], width, j),
                    load3(b[1], width, j),
                );
                for (acc, p) in acc
                    .iter_mut()
                    .zip([partial(&a0, &b0), partial(&xor3(&a0, &a1), &xor3(&b0, &b1))])
                {
                    for s in 0..5 {
                        acc[s] = _mm512_xor_si512(acc[s], _mm512_xor_si512(p[0][s], p[1][s]));
                    }
                }
            }
            let finish = |acc: &[__m512i; 5]| {
                let mut out = [0u64; 6];
                for s in 0..5 {
                    let mut lanes = [0u128; 4];
                    _mm512_storeu_si512(lanes.as_mut_ptr().cast(), acc[s]);
                    let sum = lanes[0] ^ lanes[1] ^ lanes[2] ^ lanes[3];
                    out[s] ^= sum as u64;
                    out[s + 1] ^= (sum >> 64) as u64;
                }
                out
            };
            (finish(&acc[0]), finish(&acc[1]))
        }
    }

    /// Words of a product from its partial sums by offset, in the low half of each lane: word
    /// `w` is the low half of sum `w` and the high half of sum `w - 1`.
    #[inline(always)]
    unsafe fn word(sums: &[__m512i; 5], w: usize) -> __m512i {
        unsafe {
            let low = if w < 5 { sums[w] } else { _mm512_setzero_si512() };
            let high = if w > 0 {
                _mm512_bsrli_epi128(sums[w - 1], 8)
            } else {
                _mm512_setzero_si512()
            };
            _mm512_xor_si512(low, high)
        }
    }

    /// Reduce four products given by their words in the low half of each lane.
    #[inline(always)]
    unsafe fn reduce(field: &PowerField, p: &[__m512i; 6]) -> [__m512i; 3] {
        unsafe {
            let barrett: [__m512i; 3] = std::array::from_fn(|k| _mm512_set1_epi64(field.barrett[k] as i64));
            let modulus: [__m512i; 3] = std::array::from_fn(|k| _mm512_set1_epi64(field.modulus[k] as i64));
            let high = [p[3], p[4], p[5]];
            // The top three words of `high * barrett`: sums at offsets 2, 3 and 4.
            let mut t = [_mm512_setzero_si512(); 5];
            for (i, k) in [(0, 2), (1, 1), (2, 0), (1, 2), (2, 1), (2, 2)] {
                t[i + k] = _mm512_xor_si512(t[i + k], _mm512_clmulepi64_epi128(high[i], barrett[k], 0x00));
            }
            let q: [__m512i; 3] = std::array::from_fn(|k| _mm512_xor_si512(high[k], word(&t, 3 + k)));
            // The low three words of `q * modulus`: sums at offsets 0, 1 and 2.
            let mut r = [_mm512_setzero_si512(); 5];
            for (i, k) in [(0, 0), (0, 1), (1, 0), (0, 2), (1, 1), (2, 0)] {
                r[i + k] = _mm512_xor_si512(r[i + k], _mm512_clmulepi64_epi128(q[i], modulus[k], 0x00));
            }
            std::array::from_fn(|k| _mm512_xor_si512(p[k], word(&r, k)))
        }
    }

    pub unsafe fn reduce_row(field: &PowerField, dst: &mut [u64], wide: &[u64], width: usize) {
        unsafe {
            let zero = _mm512_setzero_si512();
            for j in (0..width).step_by(8) {
                let w: [__m512i; 4] =
                    std::array::from_fn(|k| _mm512_loadu_si512(wide.as_ptr().add(k * width + j).cast()));
                // The even four in the low half of each lane, then the odd four.
                let reduced: [[__m512i; 3]; 2] = std::array::from_fn(|half| {
                    let at = |x: __m512i| if half == 0 { x } else { _mm512_bsrli_epi128(x, 8) };
                    reduce(field, &[at(w[0]), at(w[1]), at(w[2]), at(w[3]), zero, zero])
                });
                for k in 0..3 {
                    _mm512_storeu_si512(
                        dst.as_mut_ptr().add(k * width + j).cast(),
                        _mm512_unpacklo_epi64(reduced[0][k], reduced[1][k]),
                    );
                }
            }
        }
    }

    pub unsafe fn mul_row(field: &PowerField, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        unsafe {
            for j in (0..width).step_by(8) {
                let sums = partial(&load3(a, width, j), &load3(b, width, j));
                let reduced: [[__m512i; 3]; 2] = std::array::from_fn(|half| {
                    let words: [__m512i; 6] = std::array::from_fn(|w| word(&sums[half], w));
                    reduce(field, &words)
                });
                let c = load3(c, width, j);
                for k in 0..3 {
                    let product = _mm512_unpacklo_epi64(reduced[0][k], reduced[1][k]);
                    _mm512_storeu_si512(
                        dst.as_mut_ptr().add(k * width + j).cast(),
                        _mm512_xor_si512(c[k], product),
                    );
                }
            }
        }
    }

    pub unsafe fn fold_row(
        field: &PowerField,
        dst: &mut [u64],
        lo: &[u64],
        hi: &[u64],
        challenge: &Element,
        width: usize,
    ) {
        unsafe {
            let challenge: [__m512i; 3] = std::array::from_fn(|k| _mm512_set1_epi64(challenge[k] as i64));
            for j in (0..width).step_by(8) {
                let (l, h) = (load3(lo, width, j), load3(hi, width, j));
                let delta = xor3(&l, &h);
                // `delta * challenge` for the even and the odd four.
                let mut sums = [[_mm512_setzero_si512(); 5]; 2];
                for i in 0..3 {
                    for k in 0..3 {
                        sums[0][i + k] =
                            _mm512_xor_si512(sums[0][i + k], _mm512_clmulepi64_epi128(delta[i], challenge[k], 0x00));
                        sums[1][i + k] =
                            _mm512_xor_si512(sums[1][i + k], _mm512_clmulepi64_epi128(delta[i], challenge[k], 0x01));
                    }
                }
                let reduced: [[__m512i; 3]; 2] = std::array::from_fn(|half| {
                    let words: [__m512i; 6] = std::array::from_fn(|w| word(&sums[half], w));
                    reduce(field, &words)
                });
                for k in 0..3 {
                    let folded = _mm512_unpacklo_epi64(reduced[0][k], reduced[1][k]);
                    _mm512_storeu_si512(
                        dst.as_mut_ptr().add(k * width + j).cast(),
                        _mm512_xor_si512(l[k], folded),
                    );
                }
            }
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
mod neon {
    use core::arch::aarch64::*;

    use primitives::field::gf2_64::aarch64::{pmull_hi_asm as mul_hi, pmull_lo_asm as mul_lo};

    use super::*;

    /// Entries `j` and `j + 1` of a row, a lane each, by word.
    #[inline(always)]
    unsafe fn load3(row: &[u64], width: usize, j: usize) -> [uint64x2_t; 3] {
        unsafe { std::array::from_fn(|k| vld1q_u64(row.as_ptr().add(k * width + j))) }
    }

    #[inline(always)]
    unsafe fn xor3(a: &[uint64x2_t; 3], b: &[uint64x2_t; 3]) -> [uint64x2_t; 3] {
        unsafe { std::array::from_fn(|k| veorq_u64(a[k], b[k])) }
    }

    /// The products `a[i] * b[k]` of the listed word pairs, of each lane, as 128-bit sums by
    /// offset `i + k`.
    #[inline(always)]
    unsafe fn partial<const N: usize>(
        a: &[uint64x2_t; 3],
        b: &[uint64x2_t; 3],
        terms: [(usize, usize); N],
    ) -> [[uint64x2_t; 5]; 2] {
        unsafe {
            let mut out = [[vdupq_n_u64(0); 5]; 2];
            for (i, k) in terms {
                out[0][i + k] = veorq_u64(out[0][i + k], mul_lo(a[i], b[k]));
                out[1][i + k] = veorq_u64(out[1][i + k], mul_hi(a[i], b[k]));
            }
            out
        }
    }

    const ALL: [(usize, usize); 9] = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)];

    /// Word `w` of each lane's product: the low half of its sum `w` and the high half of its
    /// sum `w - 1`.
    #[inline(always)]
    unsafe fn word(sums: &[[uint64x2_t; 5]; 2], w: usize) -> uint64x2_t {
        unsafe {
            let low = if w < 5 {
                vzip1q_u64(sums[0][w], sums[1][w])
            } else {
                vdupq_n_u64(0)
            };
            let high = if w > 0 {
                vzip2q_u64(sums[0][w - 1], sums[1][w - 1])
            } else {
                vdupq_n_u64(0)
            };
            veorq_u64(low, high)
        }
    }

    /// Reduce two products, a lane each, given by their six words.
    #[inline(always)]
    unsafe fn reduce(field: &PowerField, p: &[uint64x2_t; 6]) -> [uint64x2_t; 3] {
        unsafe {
            let barrett: [uint64x2_t; 3] = std::array::from_fn(|k| vdupq_n_u64(field.barrett[k]));
            let modulus: [uint64x2_t; 3] = std::array::from_fn(|k| vdupq_n_u64(field.modulus[k]));
            let high = [p[3], p[4], p[5]];
            // The top three words of `high * barrett`, then the low three of `q * modulus`.
            let t = partial(&high, &barrett, [(0, 2), (1, 1), (2, 0), (1, 2), (2, 1), (2, 2)]);
            let q: [uint64x2_t; 3] = std::array::from_fn(|k| veorq_u64(high[k], word(&t, 3 + k)));
            let r = partial(&q, &modulus, [(0, 0), (0, 1), (1, 0), (0, 2), (1, 1), (2, 0)]);
            std::array::from_fn(|k| veorq_u64(p[k], word(&r, k)))
        }
    }

    #[inline(always)]
    unsafe fn store3(row: &mut [u64], width: usize, j: usize, value: &[uint64x2_t; 3]) {
        unsafe {
            for (k, &v) in value.iter().enumerate() {
                vst1q_u64(row.as_mut_ptr().add(k * width + j), v);
            }
        }
    }

    pub unsafe fn dot_pair(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
        unsafe {
            let mut acc = [[vdupq_n_u64(0); 5]; 2];
            for j in (0..width).step_by(2) {
                let (a0, a1, b0, b1) = (
                    load3(a[0], width, j),
                    load3(a[1], width, j),
                    load3(b[0], width, j),
                    load3(b[1], width, j),
                );
                for (acc, p) in acc
                    .iter_mut()
                    .zip([partial(&a0, &b0, ALL), partial(&xor3(&a0, &a1), &xor3(&b0, &b1), ALL)])
                {
                    for s in 0..5 {
                        acc[s] = veorq_u64(acc[s], veorq_u64(p[0][s], p[1][s]));
                    }
                }
            }
            let finish = |acc: &[uint64x2_t; 5]| {
                let mut out = [0u64; 6];
                for (s, &sum) in acc.iter().enumerate() {
                    out[s] ^= vgetq_lane_u64(sum, 0);
                    out[s + 1] ^= vgetq_lane_u64(sum, 1);
                }
                out
            };
            (finish(&acc[0]), finish(&acc[1]))
        }
    }

    pub unsafe fn reduce_row(field: &PowerField, dst: &mut [u64], wide: &[u64], width: usize) {
        unsafe {
            let zero = vdupq_n_u64(0);
            for j in (0..width).step_by(2) {
                let w: [uint64x2_t; 4] = std::array::from_fn(|k| vld1q_u64(wide.as_ptr().add(k * width + j)));
                store3(dst, width, j, &reduce(field, &[w[0], w[1], w[2], w[3], zero, zero]));
            }
        }
    }

    pub unsafe fn mul_row(field: &PowerField, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        unsafe {
            for j in (0..width).step_by(2) {
                let sums = partial(&load3(a, width, j), &load3(b, width, j), ALL);
                let product = reduce(field, &std::array::from_fn(|w| word(&sums, w)));
                store3(dst, width, j, &xor3(&product, &load3(c, width, j)));
            }
        }
    }

    pub unsafe fn fold_row(
        field: &PowerField,
        dst: &mut [u64],
        lo: &[u64],
        hi: &[u64],
        challenge: &Element,
        width: usize,
    ) {
        unsafe {
            let challenge: [uint64x2_t; 3] = std::array::from_fn(|k| vdupq_n_u64(challenge[k]));
            for j in (0..width).step_by(2) {
                let l = load3(lo, width, j);
                let sums = partial(&xor3(&l, &load3(hi, width, j)), &challenge, ALL);
                let folded = reduce(field, &std::array::from_fn(|w| word(&sums, w)));
                store3(dst, width, j, &xor3(&l, &folded));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    #[test]
    fn arithmetic_matches_the_standard_basis() {
        let mut rng = Rng::new(41);
        let field = PowerField::new(rng.ext()).unwrap();
        let width = 16;
        let elements = |rng: &mut Rng| -> (Vec<F192>, Vec<u64>) {
            let values = rng.ext_vec(width);
            let mut row = vec![0u64; 3 * width];
            for (j, &v) in values.iter().enumerate() {
                set(&mut row, width, j, &field.from_field(v));
            }
            (values, row)
        };
        let ((a0, ra0), (a1, ra1), (b0, rb0), (b1, rb1)) = (
            elements(&mut rng),
            elements(&mut rng),
            elements(&mut rng),
            elements(&mut rng),
        );
        assert_eq!(
            field.to_field(&field.mul(&get(&ra0, width, 3), &get(&rb0, width, 5))),
            a0[3] * b0[5]
        );

        let (zero, infinity) = field.dot_pair([&ra0, &ra1], [&rb0, &rb1], width);
        assert_eq!((zero, infinity), dot_pair_portable([&ra0, &ra1], [&rb0, &rb1], width));
        let expected = (0..width).fold(F192::ZERO, |acc, j| acc + a0[j] * b0[j]);
        assert_eq!(field.to_field(&field.reduce(&zero)), expected);
        let expected = (0..width).fold(F192::ZERO, |acc, j| acc + (a0[j] + a1[j]) * (b0[j] + b1[j]));
        assert_eq!(field.to_field(&field.reduce(&infinity)), expected);

        let challenge = rng.ext();
        let (mut fast, mut slow) = (vec![0u64; 3 * width], vec![0u64; 3 * width]);
        field.fold_row(&mut fast, &ra0, &ra1, &field.from_field(challenge), width);
        field.fold_row_portable(&mut slow, &ra0, &ra1, &field.from_field(challenge), width);
        assert_eq!(fast, slow);
        for j in 0..width {
            assert_eq!(
                field.to_field(&get(&fast, width, j)),
                a0[j] + challenge * (a0[j] + a1[j])
            );
        }
        let wide: Vec<u64> = (0..4 * width).map(|_| rng.next_u64()).collect();
        field.reduce_row(&mut fast, &wide, width);
        field.reduce_row_portable(&mut slow, &wide, width);
        assert_eq!(fast, slow);
        field.mul_row(&mut fast, &ra0, &rb0, &rb1, width);
        field.mul_row_portable(&mut slow, &ra0, &rb0, &rb1, width);
        assert_eq!(fast, slow);
        for j in 0..width {
            assert_eq!(field.to_field(&get(&fast, width, j)), a0[j] * b0[j] + b1[j]);
        }
    }
}
