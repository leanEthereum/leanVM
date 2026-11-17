//! Multiplication by `X` in the novel polynomial basis of Annex D: the `beta X` of the affine fold.
//!
//! `X_c = prod_{i: c_i = 1} What_i` and `What_i^2 = What_i + a_i What_(i+1)`, with
//! `a_i = W_(i+1)(beta_(i+1)) / W_i(beta_i)^2`. With `A_t = a_0 ... a_(t-1)` and `t` the trailing zeros of `c`,
//!
//! ```text
//!     (X h)[0] = 0,    (X h)[c] = A_t (h[c - 1] + h[c + 2^t - 1]),
//! ```
//!
//! reading zero past the end of `h`, so `X h` has one coefficient more than `h`. It pulls each entry from two, so
//! any range of it is computed from `h` alone, and an entry at or above `2^mu` only feeds entries at or above `2^mu`.

use std::sync::OnceLock;

use primitives::field::{F64, F64x8, F128, F128x8};

/// A coefficient: `K` or `E`, scaled by the `K` constants `A_t`.
pub(crate) trait Coef: Copy + Send + Sync + std::ops::Add<Output = Self> {
    const ZERO: Self;
    fn scale(self, k: F64) -> Self;
    /// `v[j] * k[j]`, where `k[j]` is one at every odd `j`.
    fn scale8(v: [Self; 8], k: [F64; 8]) -> [Self; 8];

    /// [`mul_x_block`].
    #[inline(always)]
    fn x_block(block: &[Self], first: usize, outside: impl Fn(usize) -> Self, out: &mut [Self]) {
        for (q, out) in out.as_chunks_mut::<8>().0.iter_mut().enumerate() {
            let (s, t0) = sums8(block, q, first, &outside);
            *out = Self::scale8(s, multipliers8(exponents8(t0)));
        }
    }
}

impl Coef for F64 {
    const ZERO: Self = F64::ZERO;
    #[inline(always)]
    fn scale(self, k: F64) -> Self {
        self * k
    }
    #[inline(always)]
    fn scale8(v: [Self; 8], k: [F64; 8]) -> [Self; 8] {
        std::array::from_fn(|j| if j % 2 == 0 { v[j] * k[j] } else { v[j] })
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "vpclmulqdq",
        not(target_feature = "avx512f")
    ))]
    #[inline(always)]
    fn x_block(block: &[Self], first: usize, outside: impl Fn(usize) -> Self, out: &mut [Self]) {
        lanes::x_block_k(block, first, outside, out);
    }
}

impl Coef for F128 {
    const ZERO: Self = F128::ZERO;
    #[inline(always)]
    fn scale(self, k: F64) -> Self {
        self.mul_base(k)
    }
    #[inline(always)]
    fn scale8(v: [Self; 8], k: [F64; 8]) -> [Self; 8] {
        F128x8::from_array(&v)
            .mul_base_unreduced(F64x8::from_array(&k))
            .reduce_lanes()
            .to_array()
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "vpclmulqdq",
        not(target_feature = "avx512f")
    ))]
    #[inline(always)]
    fn x_block(block: &[Self], first: usize, outside: impl Fn(usize) -> Self, out: &mut [Self]) {
        lanes::x_block_e(block, first, outside, out);
    }
}

/// `A_t` for every `t < 64`.
fn constants() -> &'static [F64; 64] {
    static A: OnceLock<[F64; 64]> = OnceLock::new();
    A.get_or_init(|| {
        let roots = crate::whir_induce::eval_sk_at_vks(63);
        let mut a = [F64::ONE; 64];
        for t in 1..64 {
            a[t] = a[t - 1] * roots[t] * roots[t - 1].square().inv();
        }
        a
    })
}

/// The constant `(X h)[c]` scales its two inputs by, `c >= 1`.
#[inline(always)]
pub(crate) fn coeff(c: usize) -> F64 {
    constants()[c.trailing_zeros() as usize]
}

/// `out[i * (stride / step) + m] = (X h_(m step))[first + i]` for every `step`-th lane of `h`, stored column by column
/// (coefficient `c` of lane `l` at `c * stride + l`), over the columns `out` covers.
pub(crate) fn mul_x<T: Coef>(h: &[T], stride: usize, step: usize, first: usize, out: &mut [T]) {
    let width = stride / step;
    debug_assert!(h.len().is_multiple_of(stride) && out.len().is_multiple_of(width));
    let get = |c: usize, m: usize| h.get(c * stride + m * step).copied().unwrap_or(T::ZERO);
    for (i, col) in out.chunks_exact_mut(width).enumerate() {
        let c = first + i;
        if c == 0 {
            col.fill(T::ZERO);
        } else if c & 1 == 1 {
            for (m, o) in col.iter_mut().enumerate() {
                *o = get(c - 1, m) + get(c, m);
            }
        } else {
            let (a, far) = (coeff(c), c + (1 << c.trailing_zeros()) - 1);
            for (m, o) in col.iter_mut().enumerate() {
                *o = (get(c - 1, m) + get(far, m)).scale(a);
            }
        }
    }
}

/// The exponents `t` of the columns `c0 + j` of an aligned eight, `(X h)[c] = A_t s[c]`: the trailing zeros of an even
/// column, zero for an odd one, and `t0` for `c0`.
#[inline(always)]
pub(crate) fn exponents8(t0: usize) -> [usize; 8] {
    [t0, 0, 1, 0, 2, 0, 1, 0]
}

/// `A_t` for each exponent.
#[inline(always)]
pub(crate) fn multipliers8(t: [usize; 8]) -> [F64; 8] {
    let a = constants();
    t.map(|t| a[t])
}

/// `c A_t` for every `t`.
pub(crate) fn multiples(c: F128) -> [F128; 64] {
    constants().map(|a| c.mul_base(a))
}

/// `s[0]` of [`sums8`], and `t0`.
#[inline(always)]
pub(crate) fn head8<T: Coef>(block: &[T], q: usize, first: usize, outside: impl Fn(usize) -> T) -> (T, usize) {
    match (q, first) {
        (0, 0) => (T::ZERO, 0),
        (0, _) => {
            let t = first.trailing_zeros() as usize;
            let far = (1usize << t) - 1;
            (
                outside(first - 1) + block.get(far).copied().unwrap_or_else(|| outside(first + far)),
                t,
            )
        }
        _ => {
            let t = 3 + q.trailing_zeros() as usize;
            (block[8 * q - 1] + block[8 * q + (1 << t) - 1], t)
        }
    }
}

/// The sums `s` of columns `8q..8q + 8` of a block of a lane `h`, `(X h)[c] = A_t s[c]` with `t` from [`exponents8`],
/// and `t0`. `block[i] = h[first + i]`, and `outside(c)` gives the coefficients outside the block that the first column
/// reads; the block's length is a power of two that divides `first`.
#[inline(always)]
pub(crate) fn sums8<T: Coef>(block: &[T], q: usize, first: usize, outside: impl Fn(usize) -> T) -> ([T; 8], usize) {
    let b = &block[8 * q..8 * q + 8];
    let (s0, t0) = head8(block, q, first, outside);
    let s = [
        s0,
        b[0] + b[1],
        b[1] + b[3],
        b[2] + b[3],
        b[3] + b[7],
        b[4] + b[5],
        b[5] + b[7],
        b[6] + b[7],
    ];
    (s, t0)
}

/// [`mul_x`] over one block of one lane `h`: `out[i] = (X h)[first + i]` from `block[i] = h[first + i]`, `outside(c)`
/// giving the coefficients outside the block that the first entry reads. The block's length is a power of two, at least
/// 8, that divides `first`.
pub(crate) fn mul_x_block<T: Coef>(block: &[T], first: usize, outside: impl Fn(usize) -> T, out: &mut [T]) {
    debug_assert!(block.len() >= 8 && block.len().is_power_of_two() && first.is_multiple_of(block.len()));
    debug_assert_eq!(block.len(), out.len());
    T::x_block(block, first, outside, out);
}

/// [`sums8`] and [`mul_x_block`] on two coefficients a register, in the order they lie in memory, where VPCLMULQDQ
/// has no AVX-512 beside it.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    target_feature = "vpclmulqdq",
    not(target_feature = "avx512f")
))]
pub(crate) mod lanes {
    use core::arch::x86_64::*;

    use primitives::field::gf2_64x2::x86_64::reduce_halves256;
    use primitives::field::x4::{F64x2, F64x4, F128x2};
    use primitives::field::{F64, F128};

    use super::{constants, head8};

    /// A register of two coefficients.
    pub(crate) trait Lane2: Copy + std::ops::Add<Output = Self> {
        /// The 128-bit lanes `vperm2i128` picks with immediate `I`.
        fn select<const I: i32>(a: Self, b: Self) -> Self;
    }

    impl Lane2 for F128x2 {
        #[inline(always)]
        fn select<const I: i32>(a: Self, b: Self) -> Self {
            F128x2::select::<I>(a, b)
        }
    }

    impl Lane2 for F64x2 {
        #[inline(always)]
        fn select<const I: i32>(a: Self, b: Self) -> Self {
            F64x2::select::<I>(a, b)
        }
    }

    /// [`super::sums8`] on the registers `[b0 b1, b2 b3, b4 b5, b6 b7]`, with `s0` the low lane of its register.
    #[inline(always)]
    pub(crate) fn sums<L: Lane2>([f01, f23, f45, f67]: [L; 4], s0: L) -> [L; 4] {
        let pair = f01 + L::select::<0x01>(f01, f01);
        [
            L::select::<0x30>(s0, pair),
            L::select::<0x21>(f01, f23) + L::select::<0x11>(f23, f23),
            L::select::<0x21>(f23, f45) + L::select::<0x31>(f67, f45),
            L::select::<0x21>(f45, f67) + L::select::<0x11>(f67, f67),
        ]
    }

    /// Eight `E` coefficients as four registers.
    #[inline(always)]
    pub(crate) fn load8(e: &[F128; 8]) -> [F128x2; 4] {
        let p = e.as_chunks::<2>().0;
        [
            F128x2::load(&p[0]),
            F128x2::load(&p[1]),
            F128x2::load(&p[2]),
            F128x2::load(&p[3]),
        ]
    }

    #[inline(always)]
    pub(crate) fn store8([a, b, c, d]: [F128x2; 4], out: &mut [F128; 8]) {
        let p = out.as_chunks_mut::<2>().0;
        a.store(&mut p[0]);
        b.store(&mut p[1]);
        c.store(&mut p[2]);
        d.store(&mut p[3]);
    }

    /// Eight `K` coefficients as four registers.
    #[inline(always)]
    pub(crate) fn load8_base(k: &[F64; 8]) -> [F64x2; 4] {
        let q = k.as_chunks::<4>().0;
        let ([a, b], [c, d]) = (F64x4::load(&q[0]).spread(), F64x4::load(&q[1]).spread());
        [a, b, c, d]
    }

    /// [`super::mul_x_block`] on `E` coefficients: the odd columns' constant is one, so only the even ones multiply.
    #[inline(always)]
    pub(super) fn x_block_e(block: &[F128], first: usize, outside: impl Fn(usize) -> F128, out: &mut [F128]) {
        let a = constants();
        let k46 = F64x2::new(a[2], a[1]);
        let chunks = block.as_chunks::<8>().0.iter().zip(out.as_chunks_mut::<8>().0);
        for (q, (b, o)) in chunks.enumerate() {
            let (s0, t0) = head8(block, q, first, &outside);
            let s = sums(load8(b), F128x2::new(s0, F128::ZERO));
            let r02 = F128x2::select::<0x20>(s[0], s[1])
                .mul_base_unreduced(F64x2::new(a[t0], a[1]))
                .reduce();
            let r46 = F128x2::select::<0x20>(s[2], s[3]).mul_base_unreduced(k46).reduce();
            let out = [
                F128x2::select::<0x30>(r02, s[0]),
                F128x2::select::<0x31>(r02, s[1]),
                F128x2::select::<0x30>(r46, s[2]),
                F128x2::select::<0x31>(r46, s[3]),
            ];
            store8(out, o);
        }
    }

    /// [`super::mul_x_block`] on `K` coefficients: the even columns' sums in one register, multiplied at once.
    #[inline(always)]
    pub(super) fn x_block_k(block: &[F64], first: usize, outside: impl Fn(usize) -> F64, out: &mut [F64]) {
        let a = constants();
        let chunks = block.as_chunks::<8>().0.iter().zip(out.as_chunks_mut::<8>().0);
        for (q, (b, o)) in chunks.enumerate() {
            let (s0, t0) = head8(block, q, first, &outside);
            // SAFETY: the module's cfg enables avx2 and vpclmulqdq; each access is four whole qwords of a chunk of eight.
            unsafe {
                let (lo, hi) = (
                    _mm256_loadu_si256(b.as_ptr().cast()),
                    _mm256_loadu_si256(b[4..].as_ptr().cast()),
                );
                // `[b0 b4 b2 b6]` and `[b1 b5 b3 b7]`.
                let (u, h) = (_mm256_unpacklo_epi64(lo, hi), _mm256_unpackhi_epi64(lo, hi));
                let odd = _mm256_xor_si256(u, h);
                // `[s0 s4 s2 s6]`: the shuffles cancel in the first qword, where `s0` goes.
                let even = _mm256_xor_si256(
                    _mm256_permute4x64_epi64::<0b01_00_10_00>(h),
                    _mm256_permute4x64_epi64::<0b11_10_11_00>(h),
                );
                let even = _mm256_xor_si256(even, _mm256_zextsi128_si256(_mm_cvtsi64_si128(s0.0 as i64)));
                let m = _mm256_set_epi64x(a[1].0 as i64, a[1].0 as i64, a[2].0 as i64, a[t0].0 as i64);
                let r = reduce_halves256(
                    _mm256_clmulepi64_epi128::<0x00>(even, m),
                    _mm256_clmulepi64_epi128::<0x11>(even, m),
                );
                _mm256_storeu_si256(o.as_mut_ptr().cast(), _mm256_unpacklo_epi64(r, odd));
                _mm256_storeu_si256(o[4..].as_mut_ptr().cast(), _mm256_unpackhi_epi64(r, odd));
            }
        }
    }
}

/// `h[c + 2^t - 1]`, `t` the trailing zeros of the even `c`, or zero past `h`.
#[inline(always)]
fn far<T: Coef>(h: &[T], c: usize) -> T {
    h.get(c + (1 << c.trailing_zeros()) - 1).copied().unwrap_or(T::ZERO)
}

/// `(X h)[c]` for one column, reading zero past `h`.
#[inline]
pub(crate) fn x_at<T: Coef>(h: &[T], c: usize) -> T {
    if c == 0 {
        return T::ZERO;
    }
    let prev = h.get(c - 1).copied().unwrap_or(T::ZERO);
    if c & 1 == 1 {
        prev + h.get(c).copied().unwrap_or(T::ZERO)
    } else {
        (prev + far(h, c)).scale(coeff(c))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntt::AdditiveNttF64;
    use primitives::test_rng::Rng;

    /// `X h` in evaluation form: encode `h` on a domain of `2^log_d` points, multiply each by its point, decode.
    fn by_evaluation(h: &[F64], log_d: usize) -> Vec<F64> {
        let mut data = h.to_vec();
        data.resize(1 << log_d, F64::ZERO);
        let ntt = AdditiveNttF64::standard(log_d);
        ntt.encode_interleaved_in_place(&mut data, 1, 0);
        for (q, v) in data.iter_mut().enumerate() {
            *v *= F64(q as u64);
        }
        ntt.inverse_transform(&mut data);
        data
    }

    fn random_k(rng: &mut Rng, n: usize) -> Vec<F64> {
        (0..n).map(|_| F64(rng.next_u64())).collect()
    }

    /// On `K` and `E` data, one lane and interleaved lanes, whole and in ranges, with a high part.
    #[test]
    fn mul_x_matches_multiplication_in_evaluation_form() {
        let mut rng = Rng::new(0x3);
        for mu in 0..=11 {
            for high in [0usize, 1, 3, 6] {
                let n = (1usize << mu) + high;
                if n + 1 > 2 << mu {
                    continue;
                }
                let h = random_k(&mut rng, n);
                let want = by_evaluation(&h, mu + 1);
                assert!(want[n + 1..].iter().all(|v| v.is_zero()), "mu={mu}, high={high}");
                let mut got = vec![F64(7); n + 1];
                mul_x(&h, 1, 1, 0, &mut got);
                assert_eq!(got, want[..n + 1], "strided, mu={mu}, high={high}");
                for (first, len) in [(0, 1), (1, n), (2, n - 1), (n / 2, n + 1 - n / 2), (n, 1)] {
                    let mut got = vec![F64(7); len];
                    mul_x(&h, 1, 1, first, &mut got);
                    assert_eq!(
                        got,
                        want[first..first + len],
                        "range {first}+{len}, mu={mu}, high={high}"
                    );
                }

                for log_block in 3..=mu {
                    let n_block = 1usize << log_block;
                    for first in (0..1usize << mu).step_by(n_block) {
                        let mut got = vec![F64(7); n_block];
                        let outside = |c: usize| h.get(c).copied().unwrap_or(F64::ZERO);
                        mul_x_block(&h[first..first + n_block], first, outside, &mut got);
                        assert_eq!(got, want[first..first + n_block], "block {first}+{n_block}, mu={mu}");
                    }
                }

                // Interleaved E lanes: each limb of each lane is multiplied on its own.
                let stride = 1usize << (mu % 4);
                let lanes: Vec<[Vec<F64>; 2]> = (0..stride)
                    .map(|_| [random_k(&mut rng, n), random_k(&mut rng, n)])
                    .collect();
                let h: Vec<F128> = (0..n * stride)
                    .map(|i| {
                        let [lo, hi] = &lanes[i % stride];
                        F128::new(lo[i / stride].0, hi[i / stride].0)
                    })
                    .collect();
                let mut got = vec![F128::ONE; (n + 1) * stride];
                mul_x(&h, stride, 1, 0, &mut got);
                for (l, [lo, hi]) in lanes.iter().enumerate() {
                    let (lo, hi) = (by_evaluation(lo, mu + 1), by_evaluation(hi, mu + 1));
                    for c in 0..=n {
                        assert_eq!(
                            got[c * stride + l],
                            F128::new(lo[c].0, hi[c].0),
                            "E lane {l}, column {c}"
                        );
                    }
                }
                let first = n / 2;
                let mut part = vec![F128::ONE; (n + 1 - first) * stride];
                mul_x(&h, stride, 1, first, &mut part);
                assert_eq!(part, got[first * stride..], "E range, mu={mu}, high={high}");

                // Blocks of the first E lane.
                let e: Vec<F128> = h.iter().step_by(stride).copied().collect();
                let want: Vec<F128> = got.iter().step_by(stride).copied().collect();
                for log_block in 3..=mu {
                    let n_block = 1usize << log_block;
                    for first in (0..1usize << mu).step_by(n_block) {
                        let mut part = vec![F128::ONE; n_block];
                        let outside = |c: usize| e.get(c).copied().unwrap_or(F128::ZERO);
                        mul_x_block(&e[first..first + n_block], first, outside, &mut part);
                        assert_eq!(part, want[first..first + n_block], "E block {first}+{n_block}, mu={mu}");
                    }
                }
            }
        }
    }
}
