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
use primitives::field::gf2_64::mul_wide;

use crate::basis::{PolyEval, PowerBasis, add_mul};

pub type Element = [u64; 2];

/// A row kernel's vector form, where one is compiled and its first argument (a row's or a run's width) is whole
/// vectors of it, else `portable`. The caller bounds every row.
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
                let (words, bits) = (shift / 64, shift % 64);
                for (i, &m) in modulus.iter().enumerate() {
                    dividend[words + i] ^= m << bits;
                    if bits > 0 {
                        dividend[words + i + 1] ^= m >> (64 - bits);
                    }
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

    /// [`Self::reduce`] of a polynomial of three words, whose high half is its word 2 alone: most of the products
    /// vanish.
    #[inline(always)]
    fn reduce3(&self, p: &[u64; 3]) -> Element {
        let q = p[2] ^ (mul_wide(p[2], self.barrett[1]) >> 64) as u64;
        let mut r = [0u64; 3];
        add_mul(&mut r, &[q], &self.modulus);
        [p[0] ^ r[0], p[1] ^ r[1]]
    }

    /// The split constants of `c`: `c` and `c * x^64`, reduced. A product by `c` is then the other factor's words
    /// times these, three words reduced once, where a product of two elements is four words and a full reduction.
    /// The table's passes multiply this way, by what is fixed for the pass: a fold by its challenge, a round's
    /// factor by the position weights.
    pub fn split(&self, c: &Element) -> [Element; 2] {
        [*c, self.reduce3(&[0, c[0], c[1]])]
    }

    /// The split constants of a row's entries, a row each.
    pub fn split_row(&self, row: &[u64], width: usize) -> Vec<u64> {
        let mut out = vec![0u64; 4 * width];
        for j in 0..width {
            for (out, c) in out.chunks_exact_mut(2 * width).zip(self.split(&get(row, width, j))) {
                set(out, width, j, &c);
            }
        }
        out
    }

    /// `a` times the element whose split constants are `split`.
    #[inline(always)]
    fn mul_split(&self, a: &Element, split: &[Element; 2]) -> Element {
        let mut product = [0u64; 3];
        add_split(&mut product, a, split);
        self.reduce3(&product)
    }

    /// The sums over a quad of rows `t0..t3` that the two rounds folding it into one row take, unreduced. With
    /// `F(t) = sum of B[j] * T2[j]`, where `B[j] = a[j] * T1[j] + c[j]`, reduced, `a` given by its split constants
    /// ([`Self::split_row`]), and `Q` the same without `c`: `F(t0)`, `Q(t0 + t1)`, `F(t2)`, `Q(t2 + t3)`, `F(t1)`,
    /// `Q(t0 + t2)`, `Q(t1 + t3)` and `Q(t0 + t1 + t2 + t3)`. `T1` and `T2` read their row a run of `run` entries
    /// at a time: `T1[r + o] = t[s1 + o]` and `T2[r + o] = t[s2 + o]`, `(s1, s2)` the `r / run`-th of `sources`.
    pub fn quad_sums(
        &self,
        a: &[u64],
        c: &[u64],
        t: [&[u64]; 4],
        width: usize,
        run: usize,
        sources: &[(usize, usize)],
    ) -> [[u64; 4]; 8] {
        assert!(a.len() >= 4 * width && t.iter().chain([&c]).all(|row| row.len() >= 2 * width));
        assert!(width.is_multiple_of(run));
        assert!(sources.len() == width / run && sources.iter().all(|&(s1, s2)| s1.max(s2) + run <= width));
        row_kernel!(
            run,
            quad_sums(self, a, c, t, width, run, sources),
            self.quad_sums_portable(a, c, t, width, run, sources)
        )
    }

    pub fn quad_sums_portable(
        &self,
        a: &[u64],
        c: &[u64],
        t: [&[u64]; 4],
        width: usize,
        run: usize,
        sources: &[(usize, usize)],
    ) -> [[u64; 4]; 8] {
        let mut sums = [[0u64; 4]; 8];
        for (r, &(s1, s2)) in (0..width).step_by(run).zip(sources) {
            for o in 0..run {
                let w = [0, 1].map(|k| get(&a[2 * k * width..], width, r + o));
                let b = t.map(|t| self.mul_split(&get(t, width, s1 + o), &w));
                let y = t.map(|t| get(t, width, s2 + o));
                let terms = quad_terms(b, y, get(c, width, r + o), |a, b| add(&a, &b));
                for (sum, (b, y)) in sums.iter_mut().zip(terms) {
                    add_mul(sum, &b, &y);
                }
            }
        }
        sums
    }

    /// `dst[j] = lo[j] + sum over others of weight * (lo[j] + row[j])`: the rows' sum at weights that sum to one,
    /// `lo` at the weight left out. The products are summed before they are reduced, once.
    pub fn fold_row<const N: usize>(&self, dst: &mut [u64], lo: &[u64], others: [(&[u64], &Element); N], width: usize) {
        assert!(dst.len() >= 2 * width && lo.len() >= 2 * width);
        assert!(others.iter().all(|(row, _)| row.len() >= 2 * width));
        row_kernel!(
            width,
            fold_row(self, dst, lo, others, width),
            self.fold_row_portable(dst, lo, others, width)
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

    pub fn fold_row_portable<const N: usize>(
        &self,
        dst: &mut [u64],
        lo: &[u64],
        others: [(&[u64], &Element); N],
        width: usize,
    ) {
        let others = others.map(|(row, weight)| (row, self.split(weight)));
        for j in 0..width {
            let l = get(lo, width, j);
            let mut product = [0u64; 3];
            for (row, split) in &others {
                add_split(&mut product, &add(&l, &get(row, width, j)), split);
            }
            set(dst, width, j, &add(&l, &self.reduce3(&product)));
        }
    }
}

#[inline(always)]
fn add(a: &Element, b: &Element) -> Element {
    [a[0] ^ b[0], a[1] ^ b[1]]
}

/// `product += a * c`, unreduced, for `c` given by its split constants.
#[inline(always)]
fn add_split(product: &mut [u64; 3], a: &Element, split: &[Element; 2]) {
    for (&a, c) in a.iter().zip(split) {
        add_mul(product, &[a], c);
    }
}

/// The factors whose products [`PowerField::quad_sums`] sums, in its order, from the four rows' `b = a * T1` and
/// `y = T2` at an entry: `c` is in every row's `B`, so not in a sum of two.
#[inline(always)]
fn quad_terms<T: Copy>(b: [T; 4], y: [T; 4], c: T, add: impl Fn(T, T) -> T) -> [(T, T); 8] {
    let (b02, b13, y02, y13) = (add(b[0], b[2]), add(b[1], b[3]), add(y[0], y[2]), add(y[1], y[3]));
    [
        (add(b[0], c), y[0]),
        (add(b[0], b[1]), add(y[0], y[1])),
        (add(b[2], c), y[2]),
        (add(b[2], b[3]), add(y[2], y[3])),
        (add(b[1], c), y[1]),
        (b02, y02),
        (b13, y13),
        (add(b02, b13), add(y02, y13)),
    ]
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
    /// three products where the schoolbook takes four.
    #[inline(always)]
    fn partial(a: &[V; 2], b: &[V; 2]) -> [[V; 3]; 2] {
        let product = |x: V, y: V| [x.clmul::<0x00>(y), x.clmul::<0x11>(y)];
        let (p0, p1, m) = (
            product(a[0], b[0]),
            product(a[1], b[1]),
            product(a[0].xor(a[1]), b[0].xor(b[1])),
        );
        std::array::from_fn(|h| [p0[h], m[h].xor(p0[h]).xor(p1[h]), p1[h]])
    }

    /// Word `w` of a product from its partial sums by offset, in the low word of each lane.
    #[inline(always)]
    fn word(sums: &[V; 3], w: usize) -> V {
        let low = if w < 3 { sums[w] } else { V::zero() };
        let high = if w > 0 { sums[w - 1].high() } else { V::zero() };
        low.xor(high)
    }

    /// [`PowerField::reduce3`] of the polynomials given by their words in the low word of each lane.
    #[inline(always)]
    fn reduce3(field: &PowerField, p: &[V; 3]) -> [V; 2] {
        let q = p[2].xor(p[2].clmul::<0x00>(V::splat(field.barrett[1])).high());
        let r: [V; 2] = std::array::from_fn(|k| q.clmul::<0x00>(V::splat(field.modulus[k])));
        std::array::from_fn(|k| word(&[r[0], r[1], V::zero()], k).xor(p[k]))
    }

    /// `sums += a * c`, for the entries of `a` and the elements `c` whose split constants are `split`
    /// ([`PowerField::split`]): word `k` of an entry times constant `k`, summed by word offset for the even and
    /// the odd entries.
    #[inline(always)]
    fn add_split(sums: &mut [[V; 3]; 2], a: &[V; 2], split: &[[V; 2]; 2]) {
        for (a, c) in a.iter().zip(split) {
            for (m, &c) in c.iter().enumerate() {
                sums[0][m] = sums[0][m].xor(a.clmul::<0x00>(c));
                sums[1][m] = sums[1][m].xor(a.clmul::<0x11>(c));
            }
        }
    }

    /// The even and the odd entries' reductions, interleaved back.
    #[inline(always)]
    fn reduce_pair(field: &PowerField, sums: &[[V; 3]; 2]) -> [V; 2] {
        let [even, odd] = sums.map(|sums| reduce3(field, &std::array::from_fn(|w| word(&sums, w))));
        std::array::from_fn(|k| even[k].unpacklo(odd[k]))
    }

    #[inline(always)]
    fn mul_split(field: &PowerField, a: &[V; 2], split: &[[V; 2]; 2]) -> [V; 2] {
        let mut sums = [[V::zero(); 3]; 2];
        add_split(&mut sums, a, split);
        reduce_pair(field, &sums)
    }

    pub unsafe fn quad_sums(
        field: &PowerField,
        a: &[u64],
        c: &[u64],
        t: [&[u64]; 4],
        width: usize,
        run: usize,
        sources: &[(usize, usize)],
    ) -> [[u64; 4]; 8] {
        let mut acc = [[V::zero(); 3]; 8];
        for (r, &(s1, s2)) in (0..width).step_by(run).zip(sources) {
            for o in (0..run).step_by(STEP) {
                // SAFETY: the caller bounds every row and run, `a` at two rows, one to each constant.
                let (w, c, x, y) = unsafe {
                    (
                        [0, 1].map(|k| load2(&a[2 * k * width..], width, r + o)),
                        load2(c, width, r + o),
                        t.map(|t| load2(t, width, s1 + o)),
                        t.map(|t| load2(t, width, s2 + o)),
                    )
                };
                let b = x.map(|x| mul_split(field, &x, &w));
                for (acc, (b, y)) in acc.iter_mut().zip(quad_terms(b, y, c, |a, b| xor2(&a, &b))) {
                    let p = partial(&b, &y);
                    for s in 0..3 {
                        acc[s] = acc[s].xor(p[0][s].xor(p[1][s]));
                    }
                }
            }
        }
        let finish = |acc: [V; 3]| {
            let mut out = [0u64; 4];
            for (s, sum) in acc.iter().enumerate() {
                let sum = sum.sum();
                out[s] ^= sum as u64;
                out[s + 1] ^= (sum >> 64) as u64;
            }
            out
        };
        acc.map(finish)
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

    pub unsafe fn fold_row<const N: usize>(
        field: &PowerField,
        dst: &mut [u64],
        lo: &[u64],
        others: [(&[u64], &Element); N],
        width: usize,
    ) {
        let others = others.map(|(row, weight)| (row, field.split(weight).map(|c| c.map(V::splat))));
        for j in (0..width).step_by(STEP) {
            let l = unsafe { load2(lo, width, j) };
            let mut sums = [[V::zero(); 3]; 2];
            for (row, split) in &others {
                add_split(&mut sums, &xor2(&l, &unsafe { load2(row, width, j) }), split);
            }
            unsafe { store2(dst, width, j, xor2(&l, &reduce_pair(field, &sums))) };
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

    /// [`PowerField::reduce3`] of two polynomials, a lane each, given by their three words.
    #[inline(always)]
    unsafe fn reduce3(field: &PowerField, p: &[uint64x2_t; 3]) -> [uint64x2_t; 2] {
        unsafe {
            let barrett = vdupq_n_u64(field.barrett[1]);
            let q = veorq_u64(p[2], vzip2q_u64(mul_lo(p[2], barrett), mul_hi(p[2], barrett)));
            let modulus: [uint64x2_t; 2] = std::array::from_fn(|k| vdupq_n_u64(field.modulus[k]));
            let r = partial(&[q; 2], &modulus, [(0, 0), (0, 1)]);
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

    /// `sums += a * c`, for two entries of `a`, a lane each, and the elements `c` whose split constants are
    /// `split` ([`PowerField::split`]): word `k` of an entry times constant `k`, summed by word offset.
    #[inline(always)]
    unsafe fn add_split(sums: &mut [[uint64x2_t; 3]; 2], a: &[uint64x2_t; 2], split: &[[uint64x2_t; 2]; 2]) {
        unsafe {
            for (&a, c) in a.iter().zip(split) {
                for (m, &c) in c.iter().enumerate() {
                    sums[0][m] = veorq_u64(sums[0][m], mul_lo(a, c));
                    sums[1][m] = veorq_u64(sums[1][m], mul_hi(a, c));
                }
            }
        }
    }

    #[inline(always)]
    unsafe fn mul_split(field: &PowerField, a: &[uint64x2_t; 2], split: &[[uint64x2_t; 2]; 2]) -> [uint64x2_t; 2] {
        unsafe {
            let mut sums = [[vdupq_n_u64(0); 3]; 2];
            add_split(&mut sums, a, split);
            reduce3(field, &std::array::from_fn(|w| word(&sums, w)))
        }
    }

    pub unsafe fn quad_sums(
        field: &PowerField,
        a: &[u64],
        c: &[u64],
        t: [&[u64]; 4],
        width: usize,
        run: usize,
        sources: &[(usize, usize)],
    ) -> [[u64; 4]; 8] {
        unsafe {
            let mut acc = [[vdupq_n_u64(0); 3]; 8];
            for (r, &(s1, s2)) in (0..width).step_by(run).zip(sources) {
                for o in (0..run).step_by(2) {
                    // The caller bounds `a` at two rows, one to each constant.
                    let w = [0, 1].map(|k| load2(&a[2 * k * width..], width, r + o));
                    let b = t.map(|t| mul_split(field, &load2(t, width, s1 + o), &w));
                    let y = t.map(|t| load2(t, width, s2 + o));
                    let terms = quad_terms(b, y, load2(c, width, r + o), |a, b| xor2(&a, &b));
                    for (acc, (b, y)) in acc.iter_mut().zip(terms) {
                        let p = partial(&b, &y, ALL);
                        for s in 0..3 {
                            acc[s] = veorq_u64(acc[s], veorq_u64(p[0][s], p[1][s]));
                        }
                    }
                }
            }
            let finish = |acc: [uint64x2_t; 3]| {
                let mut out = [0u64; 4];
                for (s, &sum) in acc.iter().enumerate() {
                    out[s] ^= vgetq_lane_u64(sum, 0);
                    out[s + 1] ^= vgetq_lane_u64(sum, 1);
                }
                out
            };
            acc.map(finish)
        }
    }

    pub unsafe fn reduce_row(field: &PowerField, dst: &mut [u64], wide: &[u64], width: usize) {
        unsafe {
            for j in (0..width).step_by(2) {
                let w: [uint64x2_t; 3] = std::array::from_fn(|k| vld1q_u64(wide.as_ptr().add(k * width + j)));
                store2(dst, width, j, &reduce3(field, &w));
            }
        }
    }

    pub unsafe fn fold_row<const N: usize>(
        field: &PowerField,
        dst: &mut [u64],
        lo: &[u64],
        others: [(&[u64], &Element); N],
        width: usize,
    ) {
        unsafe {
            let others = others.map(|(row, weight)| (row, field.split(weight).map(|c| c.map(|x| vdupq_n_u64(x)))));
            for j in (0..width).step_by(2) {
                let l = load2(lo, width, j);
                let mut sums = [[vdupq_n_u64(0); 3]; 2];
                for (row, split) in &others {
                    add_split(&mut sums, &xor2(&l, &load2(row, width, j)), split);
                }
                let folded = reduce3(field, &std::array::from_fn(|w| word(&sums, w)));
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
        // Runs of eight, `T1` read from the other run and `T2` from its own.
        let sources: Vec<_> = (0..width).step_by(8).map(|r| ((r + 8) % width, r)).collect();
        let split = field.split_row(&ra0, width);
        let rows: [&[u64]; 4] = [&rb0, &rb1, &ra0, &ra1];
        let sums = field.quad_sums(&split, &ra1, rows, width, 8, &sources);
        assert_eq!(sums, field.quad_sums_portable(&split, &ra1, rows, width, 8, &sources));
        // `F`, with the constant, and `Q`, without, of the sum of the rows picked.
        let value = |picked: &[usize], constant: F128| -> F128 {
            let t: Vec<F128> = (0..width)
                .map(|j| picked.iter().map(|&i| [&b0, &b1, &a0, &a1][i][j]).sum())
                .collect();
            (0..width)
                .map(|j| (a0[j] * t[(j + 8) % width] + constant * a1[j]) * t[j])
                .sum()
        };
        let (f, q) = (|i| value(&[i], F128::ONE), |picked| value(picked, F128::ZERO));
        let expected = [
            f(0),
            q(&[0, 1]),
            f(2),
            q(&[2, 3]),
            f(1),
            q(&[0, 2]),
            q(&[1, 3]),
            q(&[0, 1, 2, 3]),
        ];
        assert_eq!(sums.map(|sum| field.to_field(&field.reduce(&sum))), expected);

        let (challenge, weights) = (rng.ext(), rng.ext_vec(2));
        let [c, w0, w1] = [challenge, weights[0], weights[1]].map(|e| field.to_poly(e));
        let (mut fast, mut slow) = (vec![0u64; 2 * width], vec![0u64; 2 * width]);
        field.fold_row(&mut fast, &ra0, [(&ra1[..], &c)], width);
        field.fold_row_portable(&mut slow, &ra0, [(&ra1[..], &c)], width);
        assert_eq!(fast, slow);
        for j in 0..width {
            assert_eq!(
                field.to_field(&get(&fast, width, j)),
                primitives::multilinear::interp(a0[j], a1[j], challenge)
            );
        }
        let others = [(&ra1[..], &c), (&rb0[..], &w0), (&rb1[..], &w1)];
        field.fold_row(&mut fast, &ra0, others, width);
        field.fold_row_portable(&mut slow, &ra0, others, width);
        assert_eq!(fast, slow);
        for j in 0..width {
            let expected =
                a0[j] + challenge * (a0[j] + a1[j]) + weights[0] * (a0[j] + b0[j]) + weights[1] * (a0[j] + b1[j]);
            assert_eq!(field.to_field(&get(&fast, width, j)), expected);
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
    }
}
