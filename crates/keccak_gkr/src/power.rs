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

use crate::basis::{PolyEval, PowerBasis, add_mul};

pub type Element = [u64; 3];

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
    add_mul(&mut out, a, b);
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

    pub fn to_poly(&self, a: F192) -> Element {
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

    /// The product of two elements, six words fully reduced: what the rows' products by split
    /// constants are tested against.
    #[cfg(test)]
    pub fn mul(&self, a: &Element, b: &Element) -> Element {
        self.reduce(&mul_wide3(a, b))
    }

    /// [`reduce`](Self::reduce) of a polynomial of four words, whose high half is its word 3 alone.
    #[inline(always)]
    fn reduce4(&self, p: &[u64; 4]) -> Element {
        let q = p[3] ^ (mul_wide(p[3], self.barrett[2]) >> 64) as u64;
        let mut r = [0u64; 4];
        add_mul(&mut r, &[q], &self.modulus);
        [p[0] ^ r[0], p[1] ^ r[1], p[2] ^ r[2]]
    }

    /// The split constants of `c`: `c * x^(64 k)` reduced, for `k` = 0, 1, 2. A product by `c` is
    /// then the sum of the other factor's words times these, four words reduced once, where a
    /// product of two elements is six words and a full reduction. The rows are multiplied this
    /// way: a fold by its challenge, a round's factors by the position weights.
    pub fn split(&self, c: &Element) -> [Element; 3] {
        let c1 = self.reduce4(&[0, c[0], c[1], c[2]]);
        let c2 = self.reduce4(&[0, c1[0], c1[1], c1[2]]);
        [*c, c1, c2]
    }

    /// The split constants of a row's entries, a row each: what [`Self::mul_row`] multiplies by.
    pub fn split_row(&self, row: &[u64], width: usize) -> Vec<u64> {
        let mut out = vec![0u64; 9 * width];
        for j in 0..width {
            for (out, c) in out.chunks_exact_mut(3 * width).zip(self.split(&get(row, width, j))) {
                set(out, width, j, &c);
            }
        }
        out
    }

    /// `a` times the element whose split constants are `split`.
    #[inline(always)]
    fn mul_split(&self, a: &Element, split: &[Element; 3]) -> Element {
        let mut product = [0u64; 4];
        for (&a, c) in a.iter().zip(split) {
            add_mul(&mut product, &[a], c);
        }
        self.reduce4(&product)
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

    /// `dst[j] = a[j] * b[j] + c[j]`, for `a` as its split constants ([`Self::split_row`]).
    pub fn mul_row(&self, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        assert!(a.len() >= 9 * width && [&*dst, b, c].iter().all(|row| row.len() >= 3 * width));
        row_kernel!(
            width,
            mul_row(self, dst, a, b, c, width),
            self.mul_row_portable(dst, a, b, c, width)
        )
    }

    pub fn mul_row_portable(&self, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        for j in 0..width {
            let split = std::array::from_fn(|k| get(&a[3 * k * width..], width, j));
            let (p, c) = (self.mul_split(&get(b, width, j), &split), get(c, width, j));
            set(dst, width, j, &[p[0] ^ c[0], p[1] ^ c[1], p[2] ^ c[2]]);
        }
    }

    pub fn fold_row_portable(&self, dst: &mut [u64], lo: &[u64], hi: &[u64], challenge: &Element, width: usize) {
        let split = self.split(challenge);
        for j in 0..width {
            let (l, h) = (get(lo, width, j), get(hi, width, j));
            let folded = self.mul_split(&[l[0] ^ h[0], l[1] ^ h[1], l[2] ^ h[2]], &split);
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

/// The x86 kernels on a register of [`Vector`](crate::clmul::Vector) lanes, two entries to a lane.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq"))]
mod x86 {
    use super::*;
    use crate::clmul::{V, Vector};

    /// Entries to a register.
    pub const STEP: usize = 2 * V::N;

    #[inline(always)]
    unsafe fn load3(row: &[u64], width: usize, j: usize) -> [V; 3] {
        unsafe { std::array::from_fn(|k| V::load(row.as_ptr().add(k * width + j))) }
    }

    #[inline(always)]
    unsafe fn store3(row: &mut [u64], width: usize, j: usize, value: [V; 3]) {
        for (k, v) in value.into_iter().enumerate() {
            unsafe { V::store(row.as_mut_ptr().add(k * width + j), v) };
        }
    }

    #[inline(always)]
    fn xor3(a: &[V; 3], b: &[V; 3]) -> [V; 3] {
        std::array::from_fn(|k| a[k].xor(b[k]))
    }

    /// The pairwise sums of three words, `0 + 1`, `0 + 2`, `1 + 2`, which [`karatsuba`] multiplies.
    #[inline(always)]
    fn sums(a: &[V; 3]) -> [V; 3] {
        [a[0].xor(a[1]), a[0].xor(a[2]), a[1].xor(a[2])]
    }

    /// The products of the entries, as partial sums by word offset: `out[half][s]` holds the
    /// 128-bit sum of `a[i] * b[k]` over `i + k = s`, for the even or the odd entries. Karatsuba's
    /// six products where the schoolbook takes nine.
    #[inline(always)]
    fn karatsuba(a: &[V; 3], sa: &[V; 3], b: &[V; 3], sb: &[V; 3]) -> [[V; 5]; 2] {
        let product = |x: V, y: V| [x.clmul::<0x00>(y), x.clmul::<0x11>(y)];
        let (p0, p1, p2) = (product(a[0], b[0]), product(a[1], b[1]), product(a[2], b[2]));
        let (m01, m02, m12) = (product(sa[0], sb[0]), product(sa[1], sb[1]), product(sa[2], sb[2]));
        std::array::from_fn(|h| {
            [
                p0[h],
                m01[h].xor(p0[h]).xor(p1[h]),
                m02[h].xor(p0[h]).xor(p1[h]).xor(p2[h]),
                m12[h].xor(p1[h]).xor(p2[h]),
                p2[h],
            ]
        })
    }

    #[inline(always)]
    fn partial(a: &[V; 3], b: &[V; 3]) -> [[V; 5]; 2] {
        karatsuba(a, &sums(a), b, &sums(b))
    }

    /// Word `w` of a product from its partial sums by offset, in the low word of each lane.
    #[inline(always)]
    fn word(sums: &[V; 5], w: usize) -> V {
        let low = if w < 5 { sums[w] } else { V::zero() };
        let high = if w > 0 { sums[w - 1].high() } else { V::zero() };
        low.xor(high)
    }

    /// [`PowerField::reduce4`] of the polynomials given by their words in the low word of each lane.
    #[inline(always)]
    fn reduce4(field: &PowerField, p: &[V; 4]) -> [V; 3] {
        let q = p[3].xor(p[3].clmul::<0x00>(V::splat(field.barrett[2])).high());
        let r: [V; 3] = std::array::from_fn(|k| q.clmul::<0x00>(V::splat(field.modulus[k])));
        std::array::from_fn(|k| word(&[r[0], r[1], r[2], V::zero(), V::zero()], k).xor(p[k]))
    }

    /// The entries of `a` times the elements whose split constants are `split`
    /// ([`PowerField::split`]): word `k` of an entry times constant `k`, summed by word offset for
    /// the even and the odd entries, reduced and interleaved back.
    #[inline(always)]
    fn mul_split(field: &PowerField, a: &[V; 3], split: &[[V; 3]; 3]) -> [V; 3] {
        let mut acc = [[V::zero(); 5]; 2];
        for (a, c) in a.iter().zip(split) {
            for (m, &c) in c.iter().enumerate() {
                acc[0][m] = acc[0][m].xor(a.clmul::<0x00>(c));
                acc[1][m] = acc[1][m].xor(a.clmul::<0x11>(c));
            }
        }
        let [even, odd] = acc.map(|acc| reduce4(field, &std::array::from_fn(|w| word(&acc, w))));
        std::array::from_fn(|k| even[k].unpacklo(odd[k]))
    }

    pub unsafe fn dot_pair(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
        let mut acc = [[V::zero(); 5]; 2];
        for j in (0..width).step_by(STEP) {
            let (a0, a1, b0, b1) = unsafe {
                (
                    load3(a[0], width, j),
                    load3(a[1], width, j),
                    load3(b[0], width, j),
                    load3(b[1], width, j),
                )
            };
            for (acc, p) in acc
                .iter_mut()
                .zip([partial(&a0, &b0), partial(&xor3(&a0, &a1), &xor3(&b0, &b1))])
            {
                for s in 0..5 {
                    acc[s] = acc[s].xor(p[0][s].xor(p[1][s]));
                }
            }
        }
        let finish = |acc: &[V; 5]| {
            let mut out = [0u64; 6];
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
            let w: [V; 4] = std::array::from_fn(|k| unsafe { V::load(wide.as_ptr().add(k * width + j)) });
            let [even, odd] = [0, 1].map(|half| {
                let at = |x: V| if half == 0 { x } else { x.high() };
                reduce4(field, &w.map(at))
            });
            unsafe { store3(dst, width, j, std::array::from_fn(|k| even[k].unpacklo(odd[k]))) };
        }
    }

    pub unsafe fn mul_row(field: &PowerField, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        for j in (0..width).step_by(STEP) {
            // SAFETY: the caller bounds the rows, `a` at three rows, one to each constant, and
            // `width` is whole registers.
            let split = std::array::from_fn(|k| unsafe { load3(&a[3 * k * width..], width, j) });
            let (b, c) = unsafe { (load3(b, width, j), load3(c, width, j)) };
            unsafe { store3(dst, width, j, xor3(&c, &mul_split(field, &b, &split))) };
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
        let split = field.split(challenge).map(|c| c.map(V::splat));
        for j in (0..width).step_by(STEP) {
            let (l, h) = unsafe { (load3(lo, width, j), load3(hi, width, j)) };
            let folded = mul_split(field, &xor3(&l, &h), &split);
            unsafe { store3(dst, width, j, xor3(&l, &folded)) };
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

    /// [`PowerField::reduce4`] of two polynomials, a lane each, given by their four words.
    #[inline(always)]
    unsafe fn reduce4(field: &PowerField, p: &[uint64x2_t; 4]) -> [uint64x2_t; 3] {
        // SAFETY: registers only, and PMULL's feature is enabled at compile time.
        unsafe {
            let barrett = vdupq_n_u64(field.barrett[2]);
            let q = veorq_u64(p[3], vzip2q_u64(mul_lo(p[3], barrett), mul_hi(p[3], barrett)));
            let modulus: [uint64x2_t; 3] = std::array::from_fn(|k| vdupq_n_u64(field.modulus[k]));
            let r = partial(&[q; 3], &modulus, [(0, 0), (0, 1), (0, 2)]);
            std::array::from_fn(|k| veorq_u64(p[k], word(&r, k)))
        }
    }

    /// Two entries of `a`, a lane each, times the elements whose split constants are `split`
    /// ([`PowerField::split`]): word `k` of an entry times constant `k`, summed by word offset.
    #[inline(always)]
    unsafe fn mul_split(field: &PowerField, a: &[uint64x2_t; 3], split: &[[uint64x2_t; 3]; 3]) -> [uint64x2_t; 3] {
        // SAFETY: registers only, and PMULL's feature is enabled at compile time.
        unsafe {
            let mut sums = [[vdupq_n_u64(0); 5]; 2];
            for (&a, c) in a.iter().zip(split) {
                for (m, &c) in c.iter().enumerate() {
                    sums[0][m] = veorq_u64(sums[0][m], mul_lo(a, c));
                    sums[1][m] = veorq_u64(sums[1][m], mul_hi(a, c));
                }
            }
            reduce4(field, &std::array::from_fn(|w| word(&sums, w)))
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
            for j in (0..width).step_by(2) {
                let w: [uint64x2_t; 4] = std::array::from_fn(|k| vld1q_u64(wide.as_ptr().add(k * width + j)));
                store3(dst, width, j, &reduce4(field, &w));
            }
        }
    }

    pub unsafe fn mul_row(field: &PowerField, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        unsafe {
            for j in (0..width).step_by(2) {
                // The caller bounds `a` at three rows, one to each constant.
                let split = std::array::from_fn(|k| load3(&a[3 * k * width..], width, j));
                let product = mul_split(field, &load3(b, width, j), &split);
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
            let split = field.split(challenge).map(|c| c.map(|x| vdupq_n_u64(x)));
            for j in (0..width).step_by(2) {
                let l = load3(lo, width, j);
                let folded = mul_split(field, &xor3(&l, &load3(hi, width, j)), &split);
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
        let (mut fast, mut slow) = (vec![0u64; 3 * width], vec![0u64; 3 * width]);
        field.fold_row(&mut fast, &ra0, &ra1, &field.to_poly(challenge), width);
        field.fold_row_portable(&mut slow, &ra0, &ra1, &field.to_poly(challenge), width);
        assert_eq!(fast, slow);
        for j in 0..width {
            assert_eq!(
                field.to_field(&get(&fast, width, j)),
                primitives::multilinear::interp(a0[j], a1[j], challenge)
            );
        }
        let wide: Vec<u64> = (0..4 * width).map(|_| rng.next_u64()).collect();
        field.reduce_row(&mut fast, &wide, width);
        field.reduce_row_portable(&mut slow, &wide, width);
        assert_eq!(fast, slow);
        let split = field.split_row(&ra0, width);
        field.mul_row(&mut fast, &split, &rb0, &rb1, width);
        field.mul_row_portable(&mut slow, &split, &rb0, &rb1, width);
        assert_eq!(fast, slow);
        for j in 0..width {
            assert_eq!(field.to_field(&get(&fast, width, j)), a0[j] * b0[j] + b1[j]);
        }
    }

    /// The rows multiplied through split constants are the full product, fully reduced: the
    /// kernels and the portable forms, on widths of whole vectors and not, and on multipliers
    /// with every word and none set.
    #[test]
    fn split_constants_multiply_as_the_full_product() {
        let mut rng = Rng::new(43);
        for _ in 0..4 {
            let field = PowerField::new(rng.ext()).unwrap();
            for width in [1, 2, 6, 8, 64, 1600] {
                let mut row = || -> Vec<u64> { (0..3 * width).map(|_| rng.next_u64()).collect() };
                let (lo, hi, b, c) = (row(), row(), row(), row());
                let random = [rng.next_u64(), rng.next_u64(), rng.next_u64()];
                for challenge in [[0; 3], [1, 0, 0], [0, 0, 1 << 63], [u64::MAX; 3], random] {
                    // The fold by `challenge`, and the product by a row that is `challenge` at even entries.
                    let mut a = lo.clone();
                    for j in (0..width).step_by(2) {
                        set(&mut a, width, j, &challenge);
                    }
                    let (mut folded, mut product) = (vec![0u64; 3 * width], vec![0u64; 3 * width]);
                    for j in 0..width {
                        let (l, h) = (get(&lo, width, j), get(&hi, width, j));
                        let p = field.mul(&challenge, &[l[0] ^ h[0], l[1] ^ h[1], l[2] ^ h[2]]);
                        set(&mut folded, width, j, &[l[0] ^ p[0], l[1] ^ p[1], l[2] ^ p[2]]);
                        let (p, c) = (field.mul(&get(&a, width, j), &get(&b, width, j)), get(&c, width, j));
                        set(&mut product, width, j, &[p[0] ^ c[0], p[1] ^ c[1], p[2] ^ c[2]]);
                    }
                    let (mut fast, mut slow) = (vec![0u64; 3 * width], vec![0u64; 3 * width]);
                    field.fold_row(&mut fast, &lo, &hi, &challenge, width);
                    field.fold_row_portable(&mut slow, &lo, &hi, &challenge, width);
                    assert!(fast == folded && slow == folded, "fold, width {width}");
                    let split = field.split_row(&a, width);
                    field.mul_row(&mut fast, &split, &b, &c, width);
                    field.mul_row_portable(&mut slow, &split, &b, &c, width);
                    assert!(fast == product && slow == product, "product, width {width}");
                }
            }
        }
    }
}
