//! Eight `F192` lanes held coefficient-major in three AVX-512 registers: register `k`
//! holds coefficient `k` of every lane, so a product is lane-wise and needs no packing.
//!
//! A product is Karatsuba's six CLMULs on the even lanes and six on the odd ones,
//! each CLMUL selecting one qword per 128-bit lane. The even and odd halves come back
//! as 128-bit partials, which interleave into the lanes again for the reduction. A sum
//! that is itself summed across lanes ([`Sum8`]) skips the interleave and the reduction.

use core::arch::x86_64::*;
use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul};

use super::gf2_64::{F64, reduce};
use super::gf2_64x3::F192;
use super::gf2_64x3::x86_64::{fold, reduce_halves512};

/// Eight elements; register `k` is coefficient `k` of lanes `0..8`.
#[derive(Clone, Copy, Debug)]
#[repr(C, align(64))]
pub struct F192x8([__m512i; 3]);

/// The sum over lanes of unreduced products, as four 128-bit partials per coefficient.
#[derive(Clone, Copy, Debug)]
pub struct Sum8([__m512i; 3]);

/// Eight `K` elements in one register.
#[derive(Clone, Copy, Debug)]
pub struct F64x8(__m512i);

/// Per-lane unreduced sums of mixed products `c · k`, `c ∈ E` and `k ∈ K`.
#[derive(Clone, Copy, Debug)]
pub struct Mixed8 {
    even: [__m512i; 3],
    odd: [__m512i; 3],
}

#[inline(always)]
fn xor(a: __m512i, b: __m512i) -> __m512i {
    // SAFETY: the module's cfg enables avx512f.
    unsafe { _mm512_xor_si512(a, b) }
}

#[inline(always)]
fn vector(v: [i64; 8]) -> __m512i {
    // SAFETY: the module's cfg enables avx512f; the array is eight qwords.
    unsafe { _mm512_loadu_si512(v.as_ptr().cast()) }
}

#[inline(always)]
fn load_u64x8(src: *const u64) -> __m512i {
    // SAFETY: callers pass a pointer to eight readable qwords.
    unsafe { _mm512_loadu_si512(src.cast()) }
}

/// Qword `i` of the result is `a[idx[i]]` for `idx[i] < 8`, else `b[idx[i] - 8]`.
#[inline(always)]
fn select(a: __m512i, idx: [i64; 8], b: __m512i) -> __m512i {
    // SAFETY: the module's cfg enables avx512f.
    unsafe { _mm512_permutex2var_epi64(a, vector(idx), b) }
}

/// Qword `i` of the result is `c[idx[i]]` where `mask` has bit `i`, else `src[i]`.
#[inline(always)]
fn select_masked(src: __m512i, mask: u8, idx: [i64; 8], c: __m512i) -> __m512i {
    // SAFETY: the module's cfg enables avx512f.
    unsafe { _mm512_mask_permutexvar_epi64(src, mask, vector(idx), c) }
}

/// The permutes of an eight-element block between its 24 interleaved qwords and the
/// three coefficient registers. Qword `q` of the block is coefficient `q % 3` of
/// element `q / 3`.
const fn aos_to_planes(k: usize) -> ([i64; 8], u8, [i64; 8]) {
    let (mut pair, mut mask, mut third) = ([0i64; 8], 0u8, [0i64; 8]);
    let mut e = 0;
    while e < 8 {
        let q = 3 * e + k;
        if q < 16 {
            pair[e] = q as i64;
        } else {
            mask |= 1 << e;
            third[e] = (q - 16) as i64;
        }
        e += 1;
    }
    (pair, mask, third)
}

const fn planes_to_aos(o: usize) -> ([i64; 8], u8, [i64; 8]) {
    let (mut pair, mut mask, mut third) = ([0i64; 8], 0u8, [0i64; 8]);
    let mut i = 0;
    while i < 8 {
        let q = 8 * o + i;
        let (e, k) = (q / 3, q % 3);
        if k < 2 {
            pair[i] = (e + 8 * k) as i64;
        } else {
            mask |= 1 << i;
            third[i] = e as i64;
        }
        i += 1;
    }
    (pair, mask, third)
}

const LOAD: [([i64; 8], u8, [i64; 8]); 3] = [aos_to_planes(0), aos_to_planes(1), aos_to_planes(2)];
const STORE: [([i64; 8], u8, [i64; 8]); 3] = [planes_to_aos(0), planes_to_aos(1), planes_to_aos(2)];

/// Transpose an 8x8 matrix of qwords: row `r` of the input is column `r` of the output.
#[inline(always)]
fn transpose(r: [__m512i; 8]) -> [__m512i; 8] {
    // SAFETY: the module's cfg enables avx512f.
    unsafe {
        let t: [__m512i; 8] = std::array::from_fn(|i| {
            let (a, b) = (r[i & !1], r[i | 1]);
            if i % 2 == 0 {
                _mm512_unpacklo_epi64(a, b)
            } else {
                _mm512_unpackhi_epi64(a, b)
            }
        });
        // `u[4h + j]`: rows `4h..4h+4` at qwords `j` and `j + 4`.
        let u: [__m512i; 8] = std::array::from_fn(|i| {
            let (h, s, o) = (i / 4, (i / 2) % 2, i % 2);
            let (a, b) = (t[4 * h + o], t[4 * h + 2 + o]);
            if s == 0 {
                _mm512_shuffle_i64x2::<0x88>(a, b)
            } else {
                _mm512_shuffle_i64x2::<0xDD>(a, b)
            }
        });
        std::array::from_fn(|c| {
            let (a, b) = (u[c % 4], u[4 + c % 4]);
            if c < 4 {
                _mm512_shuffle_i64x2::<0x88>(a, b)
            } else {
                _mm512_shuffle_i64x2::<0xDD>(a, b)
            }
        })
    }
}

impl F192x8 {
    #[inline(always)]
    pub fn splat(e: F192) -> Self {
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            Self([
                _mm512_set1_epi64(e.c0 as i64),
                _mm512_set1_epi64(e.c1 as i64),
                _mm512_set1_epi64(e.c2 as i64),
            ])
        }
    }

    /// Eight consecutive elements.
    #[inline(always)]
    pub fn load(src: &[F192; 8]) -> Self {
        let q = src.as_ptr().cast::<u64>();
        // SAFETY: the block is 24 qwords.
        let v = unsafe { [load_u64x8(q), load_u64x8(q.add(8)), load_u64x8(q.add(16))] };
        Self(std::array::from_fn(|k| {
            let (pair, mask, third) = LOAD[k];
            select_masked(select(v[0], pair, v[1]), mask, third, v[2])
        }))
    }

    /// The lanes as eight consecutive elements.
    #[inline(always)]
    pub fn store(self, dst: &mut [F192; 8]) {
        let q = dst.as_mut_ptr().cast::<u64>();
        for (o, &(pair, mask, third)) in STORE.iter().enumerate() {
            let v = select_masked(select(self.0[0], pair, self.0[1]), mask, third, self.0[2]);
            // SAFETY: the block is 24 writable qwords.
            unsafe { _mm512_storeu_si512(q.add(8 * o).cast(), v) };
        }
    }

    pub fn to_array(self) -> [F192; 8] {
        let mut out = [F192::ZERO; 8];
        self.store(&mut out);
        out
    }

    /// Eight runs of eight consecutive elements, transposed: `out[j]` lane `p` is `src[8p + j]`.
    #[inline(always)]
    pub fn load_runs(src: &[F192; 64]) -> [Self; 8] {
        let q = src.as_ptr().cast::<u64>();
        // Block `b` of run `p` is its qwords `8b..8b+8`; transposing a block across runs
        // gives every run's qword `8b + i` in one register.
        // SAFETY: the 64 elements are 192 readable qwords.
        let blocks: [[__m512i; 8]; 3] =
            std::array::from_fn(|b| transpose(std::array::from_fn(|p| load_u64x8(unsafe { q.add(24 * p + 8 * b) }))));
        std::array::from_fn(|j| Self(std::array::from_fn(|k| blocks[(3 * j + k) / 8][(3 * j + k) % 8])))
    }

    /// The even lanes of `a` then of `b`, and the odd lanes of `a` then of `b`.
    #[inline(always)]
    pub fn deinterleave(a: Self, b: Self) -> (Self, Self) {
        const EVEN: [i64; 8] = [0, 2, 4, 6, 8, 10, 12, 14];
        const ODD: [i64; 8] = [1, 3, 5, 7, 9, 11, 13, 15];
        (
            Self(std::array::from_fn(|k| select(a.0[k], EVEN, b.0[k]))),
            Self(std::array::from_fn(|k| select(a.0[k], ODD, b.0[k]))),
        )
    }

    /// The inverse of [`deinterleave`](Self::deinterleave): lanes `a0 b0 a1 b1 …` over two registers.
    #[inline(always)]
    pub fn interleave(a: Self, b: Self) -> (Self, Self) {
        const LO: [i64; 8] = [0, 8, 1, 9, 2, 10, 3, 11];
        const HI: [i64; 8] = [4, 12, 5, 13, 6, 14, 7, 15];
        (
            Self(std::array::from_fn(|k| select(a.0[k], LO, b.0[k]))),
            Self(std::array::from_fn(|k| select(a.0[k], HI, b.0[k]))),
        )
    }

    /// The even-lane and odd-lane unreduced products, y-folded.
    #[inline(always)]
    fn products(self, b: Self) -> ([__m512i; 3], [__m512i; 3]) {
        let [a0, a1, a2] = self.0;
        let [b0, b1, b2] = b.0;
        let xa = [a0, a1, a2, xor(a0, a1), xor(a0, a2), xor(a1, a2)];
        let xb = [b0, b1, b2, xor(b0, b1), xor(b0, b2), xor(b1, b2)];
        // SAFETY: the module's cfg enables avx512f and vpclmulqdq.
        let (even, odd) = unsafe {
            (
                std::array::from_fn::<_, 6, _>(|i| _mm512_clmulepi64_epi128::<0x00>(xa[i], xb[i])),
                std::array::from_fn::<_, 6, _>(|i| _mm512_clmulepi64_epi128::<0x11>(xa[i], xb[i])),
            )
        };
        let [p0, p1, p2, p01, p02, p12] = even;
        let even = fold(p0, p1, p2, p01, p02, p12, xor);
        let [p0, p1, p2, p01, p02, p12] = odd;
        (even, fold(p0, p1, p2, p01, p02, p12, xor))
    }

    /// The lane-wise products, summed over the lanes and left unreduced.
    #[inline(always)]
    pub fn mul_sum(self, b: Self) -> Sum8 {
        let (even, odd) = self.products(b);
        Sum8(std::array::from_fn(|k| xor(even[k], odd[k])))
    }
}

impl Add for F192x8 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self(std::array::from_fn(|k| xor(self.0[k], rhs.0[k])))
    }
}

impl AddAssign for F192x8 {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Mul for F192x8 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        let (even, odd) = self.products(rhs);
        Self(std::array::from_fn(|k| reduce_halves512(even[k], odd[k])))
    }
}

impl Sum8 {
    // SAFETY: an all-zero bit pattern is a valid `__m512i`.
    pub const ZERO: Self = Self(unsafe { std::mem::zeroed() });

    /// The lane sum, reduced.
    #[inline]
    pub fn reduce(self) -> F192 {
        let [c0, c1, c2] = self.0.map(|s| {
            // SAFETY: the module's cfg enables avx512f.
            let words: [u64; 8] = unsafe { std::mem::transmute(s) };
            let (lo, hi) = (
                words[0] ^ words[2] ^ words[4] ^ words[6],
                words[1] ^ words[3] ^ words[5] ^ words[7],
            );
            reduce(u128::from(hi) << 64 | u128::from(lo))
        });
        F192::new(c0, c1, c2)
    }
}

impl BitXor for Sum8 {
    type Output = Self;
    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self {
        Self(std::array::from_fn(|k| xor(self.0[k], rhs.0[k])))
    }
}

impl BitXorAssign for Sum8 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl F64x8 {
    #[inline(always)]
    pub fn new(k: [F64; 8]) -> Self {
        Self::load(&k)
    }

    #[inline(always)]
    pub fn load(k: &[F64; 8]) -> Self {
        Self(load_u64x8(k.as_ptr().cast()))
    }

    #[inline(always)]
    pub fn splat(k: F64) -> Self {
        // SAFETY: the module's cfg enables avx512f.
        Self(unsafe { _mm512_set1_epi64(k.0 as i64) })
    }

    pub fn to_array(self) -> [F64; 8] {
        // SAFETY: both are 64 bytes.
        unsafe { std::mem::transmute(self.0) }
    }
}

impl Mul for F64x8 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        // SAFETY: the module's cfg enables avx512f and vpclmulqdq.
        Self(unsafe {
            reduce_halves512(
                _mm512_clmulepi64_epi128::<0x00>(self.0, rhs.0),
                _mm512_clmulepi64_epi128::<0x11>(self.0, rhs.0),
            )
        })
    }
}

impl Default for Mixed8 {
    fn default() -> Self {
        Self::ZERO
    }
}

impl Mixed8 {
    // SAFETY: an all-zero bit pattern is a valid `__m512i`.
    pub const ZERO: Self = Self {
        even: unsafe { std::mem::zeroed() },
        odd: unsafe { std::mem::zeroed() },
    };

    /// Add `c · k[i]` to lane `i`; `c` is a [`F192x8::splat`].
    #[inline(always)]
    pub fn add(&mut self, c: F192x8, k: F64x8) {
        for i in 0..3 {
            // SAFETY: the module's cfg enables avx512f and vpclmulqdq. Immediate bit 4
            // picks the scalar's odd qword; the splat is the same in both.
            unsafe {
                self.even[i] = xor(self.even[i], _mm512_clmulepi64_epi128::<0x00>(c.0[i], k.0));
                self.odd[i] = xor(self.odd[i], _mm512_clmulepi64_epi128::<0x10>(c.0[i], k.0));
            }
        }
    }

    #[inline(always)]
    pub fn reduce(self) -> F192x8 {
        F192x8(std::array::from_fn(|i| reduce_halves512(self.even[i], self.odd[i])))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    fn elements(rng: &mut Rng) -> [F192; 8] {
        let mut e: [F192; 8] = std::array::from_fn(|_| rng.ext());
        e[3] = F192::new(u64::MAX, u64::MAX, u64::MAX);
        e[5] = F192::ZERO;
        e
    }

    #[test]
    fn lanes_match_scalar() {
        let mut rng = Rng::new(17);
        for _ in 0..200 {
            let (a, b) = (elements(&mut rng), elements(&mut rng));
            let (va, vb) = (F192x8::load(&a), F192x8::load(&b));
            assert_eq!(va.to_array(), a);
            assert_eq!((va * vb).to_array(), std::array::from_fn(|i| a[i] * b[i]));
            assert_eq!((va + vb).to_array(), std::array::from_fn(|i| a[i] + b[i]));
            let dot = (0..8).fold(F192::ZERO, |acc, i| acc + a[i] * b[i]);
            assert_eq!(va.mul_sum(vb).reduce(), dot);
            assert_eq!((va.mul_sum(vb) ^ vb.mul_sum(va)).reduce(), F192::ZERO);
            assert_eq!(F192x8::splat(a[0]).to_array(), [a[0]; 8]);

            let (even, odd) = F192x8::deinterleave(va, vb);
            let both: Vec<F192> = a.iter().chain(&b).copied().collect();
            assert_eq!(even.to_array(), std::array::from_fn(|i| both[2 * i]));
            assert_eq!(odd.to_array(), std::array::from_fn(|i| both[2 * i + 1]));
            let (lo, hi) = F192x8::interleave(even, odd);
            assert_eq!((lo.to_array(), hi.to_array()), (a, b));

            let c = rng.ext();
            let k: [F64; 8] = std::array::from_fn(|_| F64(rng.ext().c0));
            let l: [F64; 8] = std::array::from_fn(|_| F64(rng.ext().c1));
            let mut acc = Mixed8::ZERO;
            acc.add(F192x8::splat(c), F64x8::new(k));
            acc.add(F192x8::splat(a[1]), F64x8::new(k) * F64x8::load(&l));
            let want = std::array::from_fn(|i| c.mul_base(k[i]) + a[1].mul_base(k[i] * l[i]));
            assert_eq!(acc.reduce().to_array(), want);
            assert_eq!((F64x8::new(k) * F64x8::splat(l[0])).to_array(), k.map(|k| k * l[0]));
        }
    }

    #[test]
    fn runs_transpose() {
        let mut rng = Rng::new(5);
        let src: [F192; 64] = std::array::from_fn(|_| rng.ext());
        let runs = F192x8::load_runs(&src);
        for (j, run) in runs.iter().enumerate() {
            assert_eq!(run.to_array(), std::array::from_fn(|p| src[8 * p + j]));
        }
    }
}
