//! The field in the power basis of a challenge `s`: an element is its 128 coefficients on
//! `1, s, ..., s^127`, and a product is a carry-less one reduced modulo the minimal polynomial
//! of `s`.
//!
//! The rounds after the bit-level ones stay in this basis. Their tables come out of carry-less
//! sums already in it, and moving every entry to the standard basis would cost more than
//! reducing by a dense modulus does.
//!
//! A table row is laid out by word: word `k` of entry `j` at `k * width + j`.

use primitives::field::F128;

use crate::basis::{PolyEval, PowerBasis, add_mul};

pub type Element = [u64; 2];

/// A row kernel's vector form, where one is compiled and `width` is whole vectors of it, else
/// `portable`. The caller bounds every row.
macro_rules! row_kernel {
    ($width:expr, $kernel:ident($($arg:expr),*), $portable:expr) => {
        cfg_select! {
            all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq") => {
                if $width.is_multiple_of(x86::STEP) {
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
    /// `s^128`, the modulus without its leading term.
    modulus: Element,
    /// `floor(x^256 / modulus)` without its leading term, for Barrett's reduction.
    barrett: Element,
    eval: PolyEval,
}

/// The carry-less product of two elements, four words.
#[inline(always)]
fn mul_wide2(a: &Element, b: &Element) -> [u64; 4] {
    let mut out = [0u64; 4];
    add_mul(&mut out, a, b);
    out
}

impl PowerField {
    /// `None` when `s` lies in a proper subfield.
    pub fn new(s: F128) -> Option<Self> {
        let basis = PowerBasis::new(s)?;
        let mut power = F128::ONE;
        for _ in 0..128 {
            power *= s;
        }
        let modulus = basis.to_poly(power);
        // Long division of `x^256` by `x^128 + modulus`.
        let mut dividend = [0u64; 5];
        dividend[4] = 1;
        let mut barrett = [0u64; 2];
        for bit in (128..=256).rev() {
            if dividend[bit / 64] >> (bit % 64) & 1 == 1 {
                let shift = bit - 128;
                if shift < 128 {
                    barrett[shift / 64] |= 1 << (shift % 64);
                }
                dividend[bit / 64] ^= 1 << (bit % 64);
                for b in (0..128).filter(|b| modulus[b / 64] >> (b % 64) & 1 == 1) {
                    dividend[(b + shift) / 64] ^= 1 << ((b + shift) % 64);
                }
            }
        }
        Some(Self {
            basis,
            modulus,
            barrett,
            eval: PolyEval::new(s, 16),
        })
    }

    pub fn to_poly(&self, a: F128) -> Element {
        self.basis.to_poly(a)
    }

    pub fn to_field(&self, a: &Element) -> F128 {
        self.eval.eval(a)
    }

    /// A polynomial of at most 256 coefficients, modulo the minimal polynomial.
    #[inline(always)]
    pub fn reduce(&self, p: &[u64; 4]) -> Element {
        let high: Element = [p[2], p[3]];
        // The quotient: `high`, plus the top half of `high * barrett`.
        let t = mul_wide2(&high, &self.barrett);
        let q: Element = [high[0] ^ t[2], high[1] ^ t[3]];
        let r = mul_wide2(&q, &self.modulus);
        [p[0] ^ r[0], p[1] ^ r[1]]
    }

    #[inline(always)]
    pub fn mul(&self, a: &Element, b: &Element) -> Element {
        self.reduce(&mul_wide2(a, b))
    }

    /// `sum of a[j] * b[j]` and `sum of (a[j] + a'[j]) * (b[j] + b'[j])` over two pairs of rows,
    /// unreduced.
    pub fn dot_pair(&self, a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 4], [u64; 4]) {
        assert!(a.iter().chain(&b).all(|row| row.len() >= 2 * width));
        row_kernel!(width, dot_pair(a, b, width), dot_pair_portable(a, b, width))
    }

    /// `dst[j] = lo[j] + challenge * (lo[j] + hi[j])`.
    pub fn fold_row(&self, dst: &mut [u64], lo: &[u64], hi: &[u64], challenge: &Element, width: usize) {
        assert!(dst.len() >= 2 * width && lo.len() >= 2 * width && hi.len() >= 2 * width);
        row_kernel!(
            width,
            fold_row(self, dst, lo, hi, challenge, width),
            self.fold_row_portable(dst, lo, hi, challenge, width)
        )
    }

    /// `dst[j] = wide[j]` reduced, for a row of three-word polynomials laid out by word.
    pub fn reduce_row(&self, dst: &mut [u64], wide: &[u64], width: usize) {
        assert!(dst.len() >= 2 * width && wide.len() >= 3 * width);
        row_kernel!(
            width,
            reduce_row(self, dst, wide, width),
            self.reduce_row_portable(dst, wide, width)
        )
    }

    pub fn reduce_row_portable(&self, dst: &mut [u64], wide: &[u64], width: usize) {
        for j in 0..width {
            let p = [wide[j], wide[width + j], wide[2 * width + j], 0];
            set(dst, width, j, &self.reduce(&p));
        }
    }

    /// `dst[j] = a[j] * b[j] + c[j]`.
    pub fn mul_row(&self, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        assert!(dst.len() >= 2 * width && [a, b, c].iter().all(|row| row.len() >= 2 * width));
        row_kernel!(
            width,
            mul_row(self, dst, a, b, c, width),
            self.mul_row_portable(dst, a, b, c, width)
        )
    }

    pub fn mul_row_portable(&self, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        for j in 0..width {
            let (p, c) = (self.mul(&get(a, width, j), &get(b, width, j)), get(c, width, j));
            set(dst, width, j, &[p[0] ^ c[0], p[1] ^ c[1]]);
        }
    }

    pub fn fold_row_portable(&self, dst: &mut [u64], lo: &[u64], hi: &[u64], challenge: &Element, width: usize) {
        for j in 0..width {
            let (l, h) = (get(lo, width, j), get(hi, width, j));
            let delta = [l[0] ^ h[0], l[1] ^ h[1]];
            let folded = self.mul(challenge, &delta);
            for k in 0..2 {
                dst[k * width + j] = l[k] ^ folded[k];
            }
        }
    }
}

/// Entry `j` of a row.
#[inline(always)]
pub fn get(row: &[u64], width: usize, j: usize) -> Element {
    [row[j], row[width + j]]
}

#[inline(always)]
pub fn set(row: &mut [u64], width: usize, j: usize, value: &Element) {
    for k in 0..2 {
        row[k * width + j] = value[k];
    }
}

pub fn dot_pair_portable(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 4], [u64; 4]) {
    let (mut zero, mut infinity) = ([0u64; 4], [0u64; 4]);
    for j in 0..width {
        let (a0, a1, b0, b1) = (
            get(a[0], width, j),
            get(a[1], width, j),
            get(b[0], width, j),
            get(b[1], width, j),
        );
        let da = [a0[0] ^ a1[0], a0[1] ^ a1[1]];
        let db = [b0[0] ^ b1[0], b0[1] ^ b1[1]];
        for (acc, p) in [(&mut zero, mul_wide2(&a0, &b0)), (&mut infinity, mul_wide2(&da, &db))] {
            for (x, y) in acc.iter_mut().zip(p) {
                *x ^= y;
            }
        }
    }
    (zero, infinity)
}

/// The x86 kernels on a register of [`Vector`](crate::clmul::Vector) lanes, two entries to a lane.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq"))]
mod x86 {
    use super::*;
    use crate::clmul::{V, Vector};

    /// Entries to a register.
    pub const STEP: usize = 2 * V::N;

    #[inline(always)]
    unsafe fn load2(row: &[u64], width: usize, j: usize) -> [V; 2] {
        unsafe { std::array::from_fn(|k| V::load(row.as_ptr().add(k * width + j))) }
    }

    #[inline(always)]
    unsafe fn store2(row: &mut [u64], width: usize, j: usize, value: [V; 2]) {
        for (k, v) in value.into_iter().enumerate() {
            unsafe { V::store(row.as_mut_ptr().add(k * width + j), v) };
        }
    }

    #[inline(always)]
    fn xor2(a: &[V; 2], b: &[V; 2]) -> [V; 2] {
        std::array::from_fn(|k| a[k].xor(b[k]))
    }

    /// The products of the entries, as partial sums by word offset: `out[half][s]` holds the
    /// 128-bit sum of `a[i] * b[k]` over `i + k = s`, for the even or the odd entries. Karatsuba's
    /// three products where the schoolbook takes four, `sa` and `sb` the sums of the two words.
    #[inline(always)]
    fn karatsuba(a: &[V; 2], sa: V, b: &[V; 2], sb: V) -> [[V; 3]; 2] {
        let product = |x: V, y: V| [x.clmul::<0x00>(y), x.clmul::<0x11>(y)];
        let (p0, p1, m) = (product(a[0], b[0]), product(a[1], b[1]), product(sa, sb));
        std::array::from_fn(|h| [p0[h], m[h].xor(p0[h]).xor(p1[h]), p1[h]])
    }

    #[inline(always)]
    fn partial(a: &[V; 2], b: &[V; 2]) -> [[V; 3]; 2] {
        karatsuba(a, a[0].xor(a[1]), b, b[0].xor(b[1]))
    }

    /// Word `w` of a product from its partial sums by offset, in the low word of each lane.
    #[inline(always)]
    fn word(sums: &[V; 3], w: usize) -> V {
        let low = if w < 3 { sums[w] } else { V::zero() };
        let high = if w > 0 { sums[w - 1].high() } else { V::zero() };
        low.xor(high)
    }

    /// Reduce the products given by their words in the low word of each lane.
    #[inline(always)]
    fn reduce(field: &PowerField, p: &[V; 4]) -> [V; 2] {
        let barrett: [V; 2] = std::array::from_fn(|k| V::splat(field.barrett[k]));
        let modulus: [V; 2] = std::array::from_fn(|k| V::splat(field.modulus[k]));
        let high = [p[2], p[3]];
        // The top two words of `high * barrett`: sums at offsets 1 and 2.
        let mut t = [V::zero(); 3];
        for (i, k) in [(0, 1), (1, 0), (1, 1)] {
            t[i + k] = t[i + k].xor(high[i].clmul::<0x00>(barrett[k]));
        }
        let q: [V; 2] = std::array::from_fn(|k| high[k].xor(word(&t, 2 + k)));
        // The low two words of `q * modulus`: sums at offsets 0 and 1.
        let mut r = [V::zero(); 3];
        for (i, k) in [(0, 0), (0, 1), (1, 0)] {
            r[i + k] = r[i + k].xor(q[i].clmul::<0x00>(modulus[k]));
        }
        std::array::from_fn(|k| p[k].xor(word(&r, k)))
    }

    /// [`reduce`] of products of three words, whose high half is their word 2 alone: most of
    /// the products vanish.
    #[inline(always)]
    fn reduce3(field: &PowerField, p: &[V; 3]) -> [V; 2] {
        let q = p[2].xor(p[2].clmul::<0x00>(V::splat(field.barrett[1])).high());
        let r: [V; 2] = std::array::from_fn(|k| q.clmul::<0x00>(V::splat(field.modulus[k])));
        std::array::from_fn(|k| word(&[r[0], r[1], V::zero()], k).xor(p[k]))
    }

    /// The even and the odd entries' reductions, interleaved back.
    #[inline(always)]
    fn reduce_pair(field: &PowerField, sums: &[[V; 3]; 2]) -> [V; 2] {
        let [even, odd] = [0, 1].map(|half| reduce(field, &std::array::from_fn(|w| word(&sums[half], w))));
        std::array::from_fn(|k| even[k].unpacklo(odd[k]))
    }

    pub unsafe fn dot_pair(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 4], [u64; 4]) {
        let mut acc = [[V::zero(); 3]; 2];
        for j in (0..width).step_by(STEP) {
            let (a0, a1, b0, b1) = unsafe {
                (
                    load2(a[0], width, j),
                    load2(a[1], width, j),
                    load2(b[0], width, j),
                    load2(b[1], width, j),
                )
            };
            for (acc, p) in acc
                .iter_mut()
                .zip([partial(&a0, &b0), partial(&xor2(&a0, &a1), &xor2(&b0, &b1))])
            {
                for s in 0..3 {
                    acc[s] = acc[s].xor(p[0][s].xor(p[1][s]));
                }
            }
        }
        let finish = |acc: &[V; 3]| {
            let mut out = [0u64; 4];
            for (s, sum) in acc.iter().enumerate() {
                let sum = sum.sum();
                out[s] ^= sum as u64;
                out[s + 1] ^= (sum >> 64) as u64;
            }
            out
        };
        (finish(&acc[0]), finish(&acc[1]))
    }

    pub unsafe fn reduce_row(field: &PowerField, dst: &mut [u64], wide: &[u64], width: usize) {
        for j in (0..width).step_by(STEP) {
            let w: [V; 3] = std::array::from_fn(|k| unsafe { V::load(wide.as_ptr().add(k * width + j)) });
            let [even, odd] = [0, 1].map(|half| {
                let at = |x: V| if half == 0 { x } else { x.high() };
                reduce3(field, &w.map(at))
            });
            unsafe { store2(dst, width, j, std::array::from_fn(|k| even[k].unpacklo(odd[k]))) };
        }
    }

    pub unsafe fn mul_row(field: &PowerField, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        for j in (0..width).step_by(STEP) {
            let (a, b, c) = unsafe { (load2(a, width, j), load2(b, width, j), load2(c, width, j)) };
            let product = reduce_pair(field, &partial(&a, &b));
            unsafe { store2(dst, width, j, xor2(&c, &product)) };
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
        let challenge: [V; 2] = std::array::from_fn(|k| V::splat(challenge[k]));
        let challenge_sum = challenge[0].xor(challenge[1]);
        for j in (0..width).step_by(STEP) {
            let (l, h) = unsafe { (load2(lo, width, j), load2(hi, width, j)) };
            let delta = xor2(&l, &h);
            let folded = reduce_pair(
                field,
                &karatsuba(&delta, delta[0].xor(delta[1]), &challenge, challenge_sum),
            );
            unsafe { store2(dst, width, j, xor2(&l, &folded)) };
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
    unsafe fn load2(row: &[u64], width: usize, j: usize) -> [uint64x2_t; 2] {
        unsafe { std::array::from_fn(|k| vld1q_u64(row.as_ptr().add(k * width + j))) }
    }

    #[inline(always)]
    unsafe fn xor2(a: &[uint64x2_t; 2], b: &[uint64x2_t; 2]) -> [uint64x2_t; 2] {
        unsafe { std::array::from_fn(|k| veorq_u64(a[k], b[k])) }
    }

    /// The products `a[i] * b[k]` of the listed word pairs, of each lane, as 128-bit sums by
    /// offset `i + k`.
    #[inline(always)]
    unsafe fn partial<const N: usize>(
        a: &[uint64x2_t; 2],
        b: &[uint64x2_t; 2],
        terms: [(usize, usize); N],
    ) -> [[uint64x2_t; 3]; 2] {
        unsafe {
            let mut out = [[vdupq_n_u64(0); 3]; 2];
            for (i, k) in terms {
                out[0][i + k] = veorq_u64(out[0][i + k], mul_lo(a[i], b[k]));
                out[1][i + k] = veorq_u64(out[1][i + k], mul_hi(a[i], b[k]));
            }
            out
        }
    }

    const ALL: [(usize, usize); 4] = [(0, 0), (0, 1), (1, 0), (1, 1)];

    /// Word `w` of each lane's product: the low half of its sum `w` and the high half of its
    /// sum `w - 1`.
    #[inline(always)]
    unsafe fn word(sums: &[[uint64x2_t; 3]; 2], w: usize) -> uint64x2_t {
        unsafe {
            let low = if w < 3 {
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

    /// Reduce two products, a lane each, given by their four words.
    #[inline(always)]
    unsafe fn reduce(field: &PowerField, p: &[uint64x2_t; 4]) -> [uint64x2_t; 2] {
        unsafe {
            let barrett: [uint64x2_t; 2] = std::array::from_fn(|k| vdupq_n_u64(field.barrett[k]));
            let modulus: [uint64x2_t; 2] = std::array::from_fn(|k| vdupq_n_u64(field.modulus[k]));
            let high = [p[2], p[3]];
            // The top two words of `high * barrett`, then the low two of `q * modulus`.
            let t = partial(&high, &barrett, [(0, 1), (1, 0), (1, 1)]);
            let q: [uint64x2_t; 2] = std::array::from_fn(|k| veorq_u64(high[k], word(&t, 2 + k)));
            let r = partial(&q, &modulus, [(0, 0), (0, 1), (1, 0)]);
            std::array::from_fn(|k| veorq_u64(p[k], word(&r, k)))
        }
    }

    #[inline(always)]
    unsafe fn store2(row: &mut [u64], width: usize, j: usize, value: &[uint64x2_t; 2]) {
        unsafe {
            for (k, &v) in value.iter().enumerate() {
                vst1q_u64(row.as_mut_ptr().add(k * width + j), v);
            }
        }
    }

    pub unsafe fn dot_pair(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 4], [u64; 4]) {
        unsafe {
            let mut acc = [[vdupq_n_u64(0); 3]; 2];
            for j in (0..width).step_by(2) {
                let (a0, a1, b0, b1) = (
                    load2(a[0], width, j),
                    load2(a[1], width, j),
                    load2(b[0], width, j),
                    load2(b[1], width, j),
                );
                for (acc, p) in acc
                    .iter_mut()
                    .zip([partial(&a0, &b0, ALL), partial(&xor2(&a0, &a1), &xor2(&b0, &b1), ALL)])
                {
                    for s in 0..3 {
                        acc[s] = veorq_u64(acc[s], veorq_u64(p[0][s], p[1][s]));
                    }
                }
            }
            let finish = |acc: &[uint64x2_t; 3]| {
                let mut out = [0u64; 4];
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
                let w: [uint64x2_t; 3] = std::array::from_fn(|k| vld1q_u64(wide.as_ptr().add(k * width + j)));
                store2(dst, width, j, &reduce(field, &[w[0], w[1], w[2], zero]));
            }
        }
    }

    pub unsafe fn mul_row(field: &PowerField, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        unsafe {
            for j in (0..width).step_by(2) {
                let sums = partial(&load2(a, width, j), &load2(b, width, j), ALL);
                let product = reduce(field, &std::array::from_fn(|w| word(&sums, w)));
                store2(dst, width, j, &xor2(&product, &load2(c, width, j)));
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
            let challenge: [uint64x2_t; 2] = std::array::from_fn(|k| vdupq_n_u64(challenge[k]));
            for j in (0..width).step_by(2) {
                let l = load2(lo, width, j);
                let sums = partial(&xor2(&l, &load2(hi, width, j)), &challenge, ALL);
                let folded = reduce(field, &std::array::from_fn(|w| word(&sums, w)));
                store2(dst, width, j, &xor2(&l, &folded));
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
        let s = rng.ext();
        let field = PowerField::new(s).unwrap();
        let width = 16;
        let elements = |rng: &mut Rng| -> (Vec<F128>, Vec<u64>) {
            let values = rng.ext_vec(width);
            let mut row = vec![0u64; 2 * width];
            for (j, &v) in values.iter().enumerate() {
                set(&mut row, width, j, &field.to_poly(v));
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
        let expected = (0..width).map(|j| a0[j] * b0[j]).sum();
        assert_eq!(field.to_field(&field.reduce(&zero)), expected);
        let expected = (0..width).map(|j| (a0[j] + a1[j]) * (b0[j] + b1[j])).sum();
        assert_eq!(field.to_field(&field.reduce(&infinity)), expected);

        let challenge = rng.ext();
        let (mut fast, mut slow) = (vec![0u64; 2 * width], vec![0u64; 2 * width]);
        field.fold_row(&mut fast, &ra0, &ra1, &field.to_poly(challenge), width);
        field.fold_row_portable(&mut slow, &ra0, &ra1, &field.to_poly(challenge), width);
        assert_eq!(fast, slow);
        for j in 0..width {
            assert_eq!(
                field.to_field(&get(&fast, width, j)),
                primitives::multilinear::interp(a0[j], a1[j], challenge)
            );
        }
        let wide: Vec<u64> = (0..3 * width).map(|_| rng.next_u64()).collect();
        field.reduce_row(&mut fast, &wide, width);
        field.reduce_row_portable(&mut slow, &wide, width);
        assert_eq!(fast, slow);
        let eval = PolyEval::new(s, 24);
        for j in 0..width {
            let p = [wide[j], wide[width + j], wide[2 * width + j]];
            assert_eq!(field.to_field(&get(&fast, width, j)), eval.eval(&p));
        }
        field.mul_row(&mut fast, &ra0, &rb0, &rb1, width);
        field.mul_row_portable(&mut slow, &ra0, &rb0, &rb1, width);
        assert_eq!(fast, slow);
        for j in 0..width {
            assert_eq!(field.to_field(&get(&fast, width, j)), a0[j] * b0[j] + b1[j]);
        }
    }
}
