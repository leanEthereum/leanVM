#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
use super::Weights8;
use super::{F192, F192Unreduced};
use crate::field::gf2_64::F64;
use core::arch::x86_64::*;
use core::mem::MaybeUninit;
use core::mem::transmute;
use core::ops::{Add, BitXor, BitXorAssign, Mul};

/// Two 64-bit words as one register, `lo` in the low qword.
#[inline(always)]
fn pair(lo: u64, hi: u64) -> __m128i {
    // SAFETY: SSE2 is part of the x86-64 baseline.
    unsafe { _mm_set_epi64x(hi as i64, lo as i64) }
}

/// The y-folded Karatsuba product of one pair.
///
/// # Safety
///
/// Requires the `pclmulqdq` target feature.
#[inline]
#[target_feature(enable = "pclmulqdq")]
unsafe fn karatsuba(a: F192, b: F192) -> [__m128i; 3] {
    // Operand registers, as in the module table.
    let (a01, b01) = (pair(a.c0, a.c1), pair(b.c0, b.c1));
    let (at, bt) = (pair(a.c2, a.c0 ^ a.c1), pair(b.c2, b.c0 ^ b.c1));
    // XOR the broadcast c2 into both qwords of r01.
    let a_s = _mm_xor_si128(a01, _mm_unpacklo_epi64(at, at));
    let b_s = _mm_xor_si128(b01, _mm_unpacklo_epi64(bt, bt));
    // The six base products, two per register pair.
    let p0 = _mm_clmulepi64_si128::<0x00>(a01, b01);
    let p1 = _mm_clmulepi64_si128::<0x11>(a01, b01);
    let p02 = _mm_clmulepi64_si128::<0x00>(a_s, b_s);
    let p12 = _mm_clmulepi64_si128::<0x11>(a_s, b_s);
    let p2 = _mm_clmulepi64_si128::<0x00>(at, bt);
    let p01 = _mm_clmulepi64_si128::<0x11>(at, bt);
    fold(p0, p1, p2, p01, p02, p12, |x, y| _mm_xor_si128(x, y))
}

/// Karatsuba recombination and y-fold in one step, for any register width.
///
/// Composing the two linear maps leaves a short XOR network:
///
/// ```text
///     d0 = p0 ^ p1 ^ p2 ^ p12
///     d1 = p0 ^ p01 ^ p12
///     d2 = p0 ^ p1 ^ p02
/// ```
#[inline(always)]
fn fold<V: Copy>(p0: V, p1: V, p2: V, p01: V, p02: V, p12: V, xor: impl Fn(V, V) -> V) -> [V; 3] {
    // Shared by d0 and d1.
    let q = xor(p0, p12);
    [xor(xor(q, p1), p2), xor(q, p01), xor(xor(p0, p1), p02)]
}

/// One unreduced product.
///
/// # Safety
///
/// Requires the `pclmulqdq` target feature.
#[inline]
#[target_feature(enable = "pclmulqdq")]
pub unsafe fn mul_unreduced(a: F192, b: F192) -> F192Unreduced {
    // SAFETY: the function carries pclmulqdq; the reinterprets are between 128-bit values.
    unsafe {
        F192Unreduced {
            coeffs: karatsuba(a, b).map(|d| transmute::<__m128i, [u64; 2]>(d)),
        }
    }
}

/// One unreduced mixed product: three base products from two operand registers.
///
/// # Safety
///
/// Requires the `pclmulqdq` target feature.
#[inline]
#[target_feature(enable = "pclmulqdq")]
pub unsafe fn mul_base_unreduced(a: F192, k: F64) -> F192Unreduced {
    // [c0, c1] and [c2, 0] against [k, 0].
    let a01 = pair(a.c0, a.c1);
    let a2 = _mm_cvtsi64_si128(a.c2 as i64);
    let k = _mm_cvtsi64_si128(k.0 as i64);
    // Immediate 0x01 multiplies the high qword of the first operand by the low qword of the second.
    let products = [
        _mm_clmulepi64_si128::<0x00>(a01, k),
        _mm_clmulepi64_si128::<0x01>(a01, k),
        _mm_clmulepi64_si128::<0x00>(a2, k),
    ];
    // SAFETY: the reinterprets are between 128-bit values.
    unsafe {
        F192Unreduced {
            coeffs: products.map(|p| transmute::<__m128i, [u64; 2]>(p)),
        }
    }
}

/// The batched kernels' lane-wise reduction on one register: qword `i` of the result is the
/// reduction of `hi[i] * x^64 + lo[i]`.
#[inline(always)]
fn reduce_lanes128(lo: __m128i, hi: __m128i) -> __m128i {
    // SAFETY: SSE2 is part of the x86-64 baseline.
    unsafe {
        let spill = _mm_xor_si128(
            _mm_xor_si128(_mm_srli_epi64::<63>(hi), _mm_srli_epi64::<61>(hi)),
            _mm_srli_epi64::<60>(hi),
        );
        let v = _mm_xor_si128(hi, spill);
        let f = _mm_xor_si128(
            _mm_xor_si128(v, _mm_slli_epi64::<1>(v)),
            _mm_xor_si128(_mm_slli_epi64::<3>(v), _mm_slli_epi64::<4>(v)),
        );
        _mm_xor_si128(lo, f)
    }
}

/// One element in two registers, `[c0, c1]` and `[c2, c2]`, for a kernel whose values stay
/// there from load to store, as the aarch64 kernels' `F192x1`; for x86 without the wide
/// CLMUL, where the batched products leave no lanes to fill.
///
/// An [`F192`] is three integer words: its sums run on the integer side, and every product
/// moves its operands over and reduces its result there. These sums, products and reductions
/// stay in vector registers.
#[derive(Clone, Copy)]
pub struct F192x1 {
    c01: __m128i,
    c22: __m128i,
}

/// An unreduced product of [`F192x1`] values, or a sum of them: its three 128-bit coefficients
/// in registers.
#[derive(Clone, Copy)]
pub struct F192x1Unreduced([__m128i; 3]);

impl F192x1 {
    #[inline(always)]
    pub fn new(e: F192) -> Self {
        // SAFETY: SSE2 is part of the x86-64 baseline.
        Self {
            c01: pair(e.c0, e.c1),
            c22: unsafe { _mm_set1_epi64x(e.c2 as i64) },
        }
    }

    /// The element at `e`, loaded into its registers.
    #[inline(always)]
    pub fn load(e: &F192) -> Self {
        let words = (e as *const F192).cast::<u64>();
        // SAFETY: `e` is three words, `c0` and `c1` adjacent under `repr(C)`.
        unsafe {
            Self {
                c01: _mm_loadu_si128(words.cast()),
                c22: _mm_set1_epi64x(*words.add(2) as i64),
            }
        }
    }

    /// Write the element to `out`, which need not be initialized.
    #[inline(always)]
    pub fn store(self, out: &mut MaybeUninit<F192>) {
        let words = out.as_mut_ptr().cast::<u64>();
        // SAFETY: `out` is three words, `c0` and `c1` adjacent under `repr(C)`.
        unsafe {
            _mm_storeu_si128(words.cast(), self.c01);
            _mm_storel_epi64(words.add(2).cast(), self.c22);
        }
    }

    /// The product without the reduction, Karatsuba's six from the registers.
    #[inline(always)]
    pub fn mul_unreduced(self, rhs: Self) -> F192x1Unreduced {
        let ((a01, a22), (b01, b22)) = ((self.c01, self.c22), (rhs.c01, rhs.c22));
        // SAFETY: the module's cfg enables pclmulqdq; the rest is SSE2.
        unsafe {
            // `[c0 + c2, c1 + c2]`, and `c0 + c1` in both qwords.
            let (a_s, b_s) = (_mm_xor_si128(a01, a22), _mm_xor_si128(b01, b22));
            let a_x = _mm_xor_si128(a01, _mm_shuffle_epi32::<0x4E>(a01));
            let b_x = _mm_xor_si128(b01, _mm_shuffle_epi32::<0x4E>(b01));
            F192x1Unreduced(fold(
                _mm_clmulepi64_si128::<0x00>(a01, b01),
                _mm_clmulepi64_si128::<0x11>(a01, b01),
                _mm_clmulepi64_si128::<0x00>(a22, b22),
                _mm_clmulepi64_si128::<0x00>(a_x, b_x),
                _mm_clmulepi64_si128::<0x00>(a_s, b_s),
                _mm_clmulepi64_si128::<0x11>(a_s, b_s),
                |x, y| _mm_xor_si128(x, y),
            ))
        }
    }

    /// The mixed product by a base-field scalar, without the reduction.
    #[inline(always)]
    pub fn mul_base_unreduced(self, k: F64) -> F192x1Unreduced {
        // SAFETY: the module's cfg enables pclmulqdq; the rest is SSE2.
        unsafe {
            let k = _mm_cvtsi64_si128(k.0 as i64);
            F192x1Unreduced([
                _mm_clmulepi64_si128::<0x00>(self.c01, k),
                _mm_clmulepi64_si128::<0x01>(self.c01, k),
                _mm_clmulepi64_si128::<0x00>(self.c22, k),
            ])
        }
    }
}

impl Add for F192x1 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        // SAFETY: SSE2 is part of the x86-64 baseline.
        unsafe {
            Self {
                c01: _mm_xor_si128(self.c01, rhs.c01),
                c22: _mm_xor_si128(self.c22, rhs.c22),
            }
        }
    }
}

impl Mul for F192x1 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        self.mul_unreduced(rhs).reduce()
    }
}

impl F192x1Unreduced {
    #[inline(always)]
    pub fn zero() -> Self {
        // SAFETY: SSE2 is part of the x86-64 baseline.
        Self([unsafe { _mm_setzero_si128() }; 3])
    }

    /// Reduce each coefficient, into the element's two registers.
    #[inline(always)]
    pub fn reduce(self) -> F192x1 {
        let [d0, d1, d2] = self.0;
        // SAFETY: SSE2 is part of the x86-64 baseline.
        unsafe {
            F192x1 {
                c01: reduce_lanes128(_mm_unpacklo_epi64(d0, d1), _mm_unpackhi_epi64(d0, d1)),
                c22: reduce_lanes128(_mm_unpacklo_epi64(d2, d2), _mm_unpackhi_epi64(d2, d2)),
            }
        }
    }
}

impl BitXor for F192x1Unreduced {
    type Output = Self;
    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self {
        let ([a0, a1, a2], [b0, b1, b2]) = (self.0, rhs.0);
        // SAFETY: SSE2 is part of the x86-64 baseline.
        unsafe { Self([_mm_xor_si128(a0, b0), _mm_xor_si128(a1, b1), _mm_xor_si128(a2, b2)]) }
    }
}

impl BitXorAssign for F192x1Unreduced {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl From<F192x1Unreduced> for F192Unreduced {
    #[inline(always)]
    fn from(u: F192x1Unreduced) -> Self {
        Self {
            // SAFETY: the reinterprets are between 128-bit values.
            coeffs: u.0.map(|d| unsafe { transmute::<__m128i, [u64; 2]>(d) }),
        }
    }
}

impl From<F192x1> for F192 {
    #[inline(always)]
    fn from(e: F192x1) -> Self {
        // SAFETY: the reinterprets are between 128-bit values.
        let ([c0, c1], [c2, _]) = unsafe {
            (
                transmute::<__m128i, [u64; 2]>(e.c01),
                transmute::<__m128i, [u64; 2]>(e.c22),
            )
        };
        Self::new(c0, c1, c2)
    }
}

/// Lane-wise base reduction: qword `i` of the result is the reduction of `hi[i] * x^64 + lo[i]`.
///
/// The same shift network as the scalar reduction, applied to every qword at once.
///
/// # Safety
///
/// Requires the `avx2` target feature.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn reduce_lanes256(lo: __m256i, hi: __m256i) -> __m256i {
    // The bits of `hi * 0x1B` shifted past x^63.
    let spill = _mm256_xor_si256(
        _mm256_xor_si256(_mm256_srli_epi64::<63>(hi), _mm256_srli_epi64::<61>(hi)),
        _mm256_srli_epi64::<60>(hi),
    );
    // lo ^ f(hi ^ spill), with f(v) = v ^ v<<1 ^ v<<3 ^ v<<4.
    let v = _mm256_xor_si256(hi, spill);
    let f = _mm256_xor_si256(
        _mm256_xor_si256(v, _mm256_slli_epi64::<1>(v)),
        _mm256_xor_si256(_mm256_slli_epi64::<3>(v), _mm256_slli_epi64::<4>(v)),
    );
    _mm256_xor_si256(lo, f)
}

/// Lane-wise base reduction on eight qwords; see the four-qword version.
///
/// # Safety
///
/// Requires the `avx512f` target feature.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn reduce_lanes512(lo: __m512i, hi: __m512i) -> __m512i {
    // The bits of `hi * 0x1B` shifted past x^63.
    let spill = _mm512_xor_si512(
        _mm512_xor_si512(_mm512_srli_epi64::<63>(hi), _mm512_srli_epi64::<61>(hi)),
        _mm512_srli_epi64::<60>(hi),
    );
    // lo ^ f(hi ^ spill), with f(v) = v ^ v<<1 ^ v<<3 ^ v<<4.
    let v = _mm512_xor_si512(hi, spill);
    let f = _mm512_xor_si512(
        _mm512_xor_si512(v, _mm512_slli_epi64::<1>(v)),
        _mm512_xor_si512(_mm512_slli_epi64::<3>(v), _mm512_slli_epi64::<4>(v)),
    );
    _mm512_xor_si512(lo, f)
}

/// The y-folded Karatsuba products of two pairs, one pair per 128-bit lane.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
unsafe fn karatsuba_vec2(a: [F192; 2], b: [F192; 2]) -> [__m256i; 3] {
    // One coefficient of both elements, in the low qword of each lane.
    let pack = |c: [u64; 2]| _mm256_set_epi64x(0, c[1] as i64, 0, c[0] as i64);
    let (a0, a1, a2) = (pack(a.map(|e| e.c0)), pack(a.map(|e| e.c1)), pack(a.map(|e| e.c2)));
    let (b0, b1, b2) = (pack(b.map(|e| e.c0)), pack(b.map(|e| e.c1)), pack(b.map(|e| e.c2)));
    // One instruction per base product covers both lanes.
    let mul = |x, y| _mm256_clmulepi64_epi128::<0x00>(x, y);
    let xor = |x, y| _mm256_xor_si256(x, y);
    fold(
        mul(a0, b0),
        mul(a1, b1),
        mul(a2, b2),
        mul(xor(a0, a1), xor(b0, b1)),
        mul(xor(a0, a2), xor(b0, b2)),
        mul(xor(a1, a2), xor(b1, b2)),
        xor,
    )
}

/// Two independent products in the two 128-bit lanes of a YMM register.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
pub unsafe fn mul_vec2(a: [F192; 2], b: [F192; 2]) -> [F192; 2] {
    // SAFETY: the function carries both features.
    unsafe {
        let [d0, d1, d2] = karatsuba_vec2(a, b);
        // Lane i of c01 is [c0_i, c1_i]; the low qword of lane i of c2 is c2_i.
        let c01 = reduce_lanes256(_mm256_unpacklo_epi64(d0, d1), _mm256_unpackhi_epi64(d0, d1));
        let c2 = reduce_lanes256(d2, _mm256_unpackhi_epi64(d2, d2));
        let (w01, w2) = (transmute::<__m256i, [u64; 4]>(c01), transmute::<__m256i, [u64; 4]>(c2));
        std::array::from_fn(|i| F192::new(w01[2 * i], w01[2 * i + 1], w2[2 * i]))
    }
}

/// Two independent unreduced products, packed as for the reduced version.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
pub unsafe fn mul_unreduced_vec2(a: [F192; 2], b: [F192; 2]) -> [F192Unreduced; 2] {
    // SAFETY: the function carries both features; lane i of each register is one coefficient.
    unsafe {
        let d = karatsuba_vec2(a, b).map(|d| transmute::<__m256i, [[u64; 2]; 2]>(d));
        std::array::from_fn(|i| F192Unreduced {
            coeffs: [d[0][i], d[1][i], d[2][i]],
        })
    }
}

/// The y-folded Karatsuba products of four pairs, one pair per 128-bit lane.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn karatsuba_vec4(a: [F192; 4], b: [F192; 4]) -> [__m512i; 3] {
    // One coefficient of all four elements, in the low qword of each lane.
    let pack = |c: [u64; 4]| _mm512_set_epi64(0, c[3] as i64, 0, c[2] as i64, 0, c[1] as i64, 0, c[0] as i64);
    let (a0, a1, a2) = (pack(a.map(|e| e.c0)), pack(a.map(|e| e.c1)), pack(a.map(|e| e.c2)));
    let (b0, b1, b2) = (pack(b.map(|e| e.c0)), pack(b.map(|e| e.c1)), pack(b.map(|e| e.c2)));
    // One instruction per base product covers all four lanes.
    let mul = |x, y| _mm512_clmulepi64_epi128::<0x00>(x, y);
    let xor = |x, y| _mm512_xor_si512(x, y);
    fold(
        mul(a0, b0),
        mul(a1, b1),
        mul(a2, b2),
        mul(xor(a0, a1), xor(b0, b1)),
        mul(xor(a0, a2), xor(b0, b2)),
        mul(xor(a1, a2), xor(b1, b2)),
        xor,
    )
}

/// Four independent products in the four 128-bit lanes of a ZMM register.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_vec4(a: [F192; 4], b: [F192; 4]) -> [F192; 4] {
    // SAFETY: the function carries both features.
    unsafe {
        let [d0, d1, d2] = karatsuba_vec4(a, b);
        // Lane i of c01 is [c0_i, c1_i]; the low qword of lane i of c2 is c2_i.
        let c01 = reduce_lanes512(_mm512_unpacklo_epi64(d0, d1), _mm512_unpackhi_epi64(d0, d1));
        let c2 = reduce_lanes512(d2, _mm512_unpackhi_epi64(d2, d2));
        let (w01, w2) = (transmute::<__m512i, [u64; 8]>(c01), transmute::<__m512i, [u64; 8]>(c2));
        std::array::from_fn(|i| F192::new(w01[2 * i], w01[2 * i + 1], w2[2 * i]))
    }
}

/// Four independent unreduced products, packed as for the reduced version.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_unreduced_vec4(a: [F192; 4], b: [F192; 4]) -> [F192Unreduced; 4] {
    // SAFETY: the function carries both features; lane i of each register is one coefficient.
    unsafe {
        let d = karatsuba_vec4(a, b).map(|d| transmute::<__m512i, [[u64; 2]; 4]>(d));
        std::array::from_fn(|i| F192Unreduced {
            coeffs: [d[0][i], d[1][i], d[2][i]],
        })
    }
}
/// The six products of a shared pair of operand registers against eight packed scalars.
///
/// `a` lane `j` meets `k_2j` through `lo` and `k_2j+1` through `hi`.
/// Returns the products of `(a_lo, a_hi)` by `k_2j`, then by `k_2j+1`.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn mul_by_pairs(lo: __m512i, hi: __m512i, c2: __m512i, k: __m512i) -> [__m512i; 6] {
    // Immediate bit 0 picks the qword of the first operand, bit 4 that of the second.
    [
        _mm512_clmulepi64_epi128::<0x00>(lo, k),
        _mm512_clmulepi64_epi128::<0x01>(lo, k),
        _mm512_clmulepi64_epi128::<0x10>(hi, k),
        _mm512_clmulepi64_epi128::<0x11>(hi, k),
        _mm512_clmulepi64_epi128::<0x00>(c2, k),
        _mm512_clmulepi64_epi128::<0x11>(c2, k),
    ]
}

/// Eight mixed products by one scalar.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_base8(t: F192, k: [F64; 8]) -> [F192; 8] {
    // SAFETY: the function carries both features.
    unsafe {
        let mut acc = [_mm512_setzero_si512(); 6];
        mul_base8_add(&mut acc, t, k);
        mul_base8_reduce(acc)
    }
}

/// Add the eight mixed products `t * k[i]` to the six product registers of [`mul_by_pairs`].
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_base8_add(acc: &mut [__m512i; 6], t: F192, k: [F64; 8]) {
    // SAFETY: the function carries both features; `k` is eight qwords.
    unsafe {
        // `t` in every lane: [c0, c1] for both pair registers, [c2, c2] for the last.
        let t01 = _mm512_broadcast_i32x4(pair(t.c0, t.c1));
        let t2 = _mm512_set1_epi64(t.c2 as i64);
        let kv = _mm512_loadu_si512(k.as_ptr().cast());
        for (acc, p) in acc.iter_mut().zip(mul_by_pairs(t01, t01, t2, kv)) {
            *acc = _mm512_xor_si512(*acc, p);
        }
    }
}

/// Reduce the six product registers of [`mul_base8_add`] into the eight sums.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_base8_reduce([e0, e1, o0, o1, e2, o2]: [__m512i; 6]) -> [F192; 8] {
    // SAFETY: the function carries both features.
    unsafe {
        // Gather each product's low and high halves into qword-wise vectors, then reduce.
        let red = |x, y| reduce_lanes512(_mm512_unpacklo_epi64(x, y), _mm512_unpackhi_epi64(x, y));
        let even = transmute::<__m512i, [u64; 8]>(red(e0, e1));
        let odd = transmute::<__m512i, [u64; 8]>(red(o0, o1));
        let c2 = transmute::<__m512i, [u64; 8]>(red(e2, o2));
        std::array::from_fn(|i| {
            let (j, w) = (i / 2, if i % 2 == 0 { &even } else { &odd });
            F192::new(w[2 * j], w[2 * j + 1], c2[i])
        })
    }
}

/// The mixed inner product over packed weights.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features, and `k.len() == 8 * w.len()`.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn dot_base(w: &[Weights8], k: &[F64]) -> F192Unreduced {
    // SAFETY: the function carries both features; `Weights8` is 64-byte aligned, `k` holds 8 qwords per block.
    unsafe {
        let xor = |x, y| _mm512_xor_si512(x, y);
        let mut acc = [_mm512_setzero_si512(); 3];
        for (b, w) in w.iter().enumerate() {
            let kv = _mm512_loadu_si512(k.as_ptr().add(8 * b).cast());
            let (lo, hi, c2) = (
                _mm512_load_si512(w.lo.as_ptr().cast()),
                _mm512_load_si512(w.hi.as_ptr().cast()),
                _mm512_load_si512(w.c2.as_ptr().cast()),
            );
            let [e0, e1, o0, o1, e2, o2] = mul_by_pairs(lo, hi, c2, kv);
            acc = [
                xor(acc[0], xor(e0, o0)),
                xor(acc[1], xor(e1, o1)),
                xor(acc[2], xor(e2, o2)),
            ];
        }
        // Fold the four 128-bit lanes of each sum into one.
        let lanes = acc.map(|a| {
            let half = _mm256_xor_si256(_mm512_castsi512_si256(a), _mm512_extracti64x4_epi64::<1>(a));
            let q = _mm_xor_si128(_mm256_castsi256_si128(half), _mm256_extracti128_si256::<1>(half));
            transmute::<__m128i, [u64; 2]>(q)
        });
        F192Unreduced { coeffs: lanes }
    }
}

/// [`super::MixedSums8`]'s registers on AVX-512: [`mul_by_pairs`]'s six products.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
pub type MixedAcc8 = [__m512i; 6];

/// [`super::F192x4`]'s registers on AVX-512: [`lanes4`]'s form.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
pub type Lanes4 = [__m512i; 2];

/// [`super::F192x4Unreduced`]'s registers on AVX-512: [`mul_lanes4`]'s three coefficients.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
pub type Wide4 = [__m512i; 3];

/// Four elements in lanes: `[c0, c1]` and `[c2, c2]` in lane `i` for element `i`.
///
/// # Safety
///
/// Requires the `avx512f` target feature.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn lanes4(v: [F192; 4]) -> [__m512i; 2] {
    let w = |i: usize| v[i];
    [
        _mm512_set_epi64(
            w(3).c1 as i64,
            w(3).c0 as i64,
            w(2).c1 as i64,
            w(2).c0 as i64,
            w(1).c1 as i64,
            w(1).c0 as i64,
            w(0).c1 as i64,
            w(0).c0 as i64,
        ),
        _mm512_set_epi64(
            w(3).c2 as i64,
            w(3).c2 as i64,
            w(2).c2 as i64,
            w(2).c2 as i64,
            w(1).c2 as i64,
            w(1).c2 as i64,
            w(0).c2 as i64,
            w(0).c2 as i64,
        ),
    ]
}

/// Four consecutive elements, twelve words, into [`lanes4`]'s form.
///
/// # Safety
///
/// Requires the `avx512f` target feature.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn load_lanes4(v: &[F192; 4]) -> [__m512i; 2] {
    let words = v.as_ptr().cast::<i64>();
    // SAFETY: `v` is twelve words, words 0..8 and 8..12.
    let (head, tail) = unsafe {
        (
            _mm512_loadu_si512(words.cast()),
            _mm512_castsi256_si512(_mm256_loadu_si256(words.add(8).cast())),
        )
    };
    // An index of 8 or more takes word `index - 8` of `tail`.
    let c01 = _mm512_set_epi64(10, 9, 7, 6, 4, 3, 1, 0);
    let c22 = _mm512_set_epi64(11, 11, 8, 8, 5, 5, 2, 2);
    [
        _mm512_permutex2var_epi64(head, c01, tail),
        _mm512_permutex2var_epi64(head, c22, tail),
    ]
}

/// [`lanes4`]'s form back to twelve consecutive words, the inverse of [`load_lanes4`].
///
/// # Safety
///
/// Requires the `avx512f` target feature.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn store_lanes4([c01, c22]: [__m512i; 2], out: &mut [MaybeUninit<F192>; 4]) {
    let words = out.as_mut_ptr().cast::<i64>();
    // An index of 8 or more takes word `index - 8` of `c22`.
    let head = _mm512_permutex2var_epi64(c01, _mm512_set_epi64(5, 4, 10, 3, 2, 8, 1, 0), c22);
    let tail = _mm512_permutex2var_epi64(c01, _mm512_set_epi64(0, 0, 0, 0, 14, 7, 6, 12), c22);
    // SAFETY: `out` is twelve words, words 0..8 and 8..12.
    unsafe {
        _mm512_storeu_si512(words.cast(), head);
        _mm256_storeu_si256(words.add(8).cast(), _mm512_castsi512_si256(tail));
    }
}

/// The 4x4 transpose of [`lanes4`] values: lane `j` of `out[i]` is lane `i` of `rows[j]`.
///
/// # Safety
///
/// Requires the `avx512f` target feature.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn transpose_lanes4(rows: [[__m512i; 2]; 4]) -> [[__m512i; 2]; 4] {
    let part = |p: usize| {
        let [a, b, c, d] = rows.map(|r| r[p]);
        // `[a0, a1, b0, b1]`, `[a2, a3, b2, b3]`, and the same of `c` and `d`.
        let (ab01, ab23) = (_mm512_shuffle_i64x2::<0x44>(a, b), _mm512_shuffle_i64x2::<0xEE>(a, b));
        let (cd01, cd23) = (_mm512_shuffle_i64x2::<0x44>(c, d), _mm512_shuffle_i64x2::<0xEE>(c, d));
        [
            _mm512_shuffle_i64x2::<0x88>(ab01, cd01),
            _mm512_shuffle_i64x2::<0xDD>(ab01, cd01),
            _mm512_shuffle_i64x2::<0x88>(ab23, cd23),
            _mm512_shuffle_i64x2::<0xDD>(ab23, cd23),
        ]
    };
    let (c01, c22) = (part(0), part(1));
    std::array::from_fn(|i| [c01[i], c22[i]])
}

/// Lane-wise XOR.
///
/// # Safety
///
/// Requires the `avx512f` target feature.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn xor_lanes<const N: usize>(a: [__m512i; N], b: [__m512i; N]) -> [__m512i; N] {
    std::array::from_fn(|i| _mm512_xor_si512(a[i], b[i]))
}

/// The y-folded Karatsuba products of two [`lanes4`] operands, lane by lane.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_lanes4([a01, a22]: [__m512i; 2], [b01, b22]: [__m512i; 2]) -> [__m512i; 3] {
    // `[c0 + c2, c1 + c2]`, and `c0 + c1` in both qwords (the swap stays in its lane).
    let (a_s, b_s) = (_mm512_xor_si512(a01, a22), _mm512_xor_si512(b01, b22));
    let a_x = _mm512_xor_si512(a01, _mm512_shuffle_epi32::<0x4E>(a01));
    let b_x = _mm512_xor_si512(b01, _mm512_shuffle_epi32::<0x4E>(b01));
    fold(
        _mm512_clmulepi64_epi128::<0x00>(a01, b01),
        _mm512_clmulepi64_epi128::<0x11>(a01, b01),
        _mm512_clmulepi64_epi128::<0x00>(a22, b22),
        _mm512_clmulepi64_epi128::<0x00>(a_x, b_x),
        _mm512_clmulepi64_epi128::<0x00>(a_s, b_s),
        _mm512_clmulepi64_epi128::<0x11>(a_s, b_s),
        |x, y| _mm512_xor_si512(x, y),
    )
}

/// Reduce [`mul_lanes4`]'s products into [`lanes4`]'s form.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn reduce_lanes4([d0, d1, d2]: [__m512i; 3]) -> [__m512i; 2] {
    // SAFETY: the function carries both features.
    unsafe {
        [
            reduce_lanes512(_mm512_unpacklo_epi64(d0, d1), _mm512_unpackhi_epi64(d0, d1)),
            reduce_lanes512(_mm512_unpacklo_epi64(d2, d2), _mm512_unpackhi_epi64(d2, d2)),
        ]
    }
}

/// The sum of the four 128-bit lanes of each of three unreduced coefficient registers: of [`mul_lanes4`]'s lanes, or of an [`F192x8Sum`].
///
/// # Safety
///
/// Requires the `avx512f` target feature.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn sum_lanes4(d: [__m512i; 3]) -> F192Unreduced {
    let coeffs = d.map(|a| {
        let half = _mm256_xor_si256(_mm512_castsi512_si256(a), _mm512_extracti64x4_epi64::<1>(a));
        let q = _mm_xor_si128(_mm256_castsi256_si128(half), _mm256_extracti128_si256::<1>(half));
        // SAFETY: the reinterpret is between 128-bit values.
        unsafe { transmute::<__m128i, [u64; 2]>(q) }
    });
    F192Unreduced { coeffs }
}

// AVX2 with VPCLMULQDQ: the same kernels on two YMM halves, two elements or two sums per
// instruction, so the types above and the callers stay as on AVX-512.

/// [`super::MixedSums8`]'s registers on AVX2: [`mul_by_pairs256`]'s six products for rows
/// `0..4`, then six for rows `4..8`.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
pub type MixedAcc8 = [[__m256i; 6]; 2];

/// [`super::F192x4`]'s registers on AVX2: half `h` holds elements `2h` and `2h + 1`, lane `i`
/// of its two registers being `[c0, c1]` and `[c2, c2]` of element `2h + i`.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
pub type Lanes4 = [[__m256i; 2]; 2];

/// [`super::F192x4Unreduced`]'s registers on AVX2: [`mul_lanes4`]'s three coefficients per half.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
pub type Wide4 = [[__m256i; 3]; 2];

/// The six products of a shared pair of operand registers against four packed scalars, as
/// [`mul_by_pairs`] does against eight.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
unsafe fn mul_by_pairs256(lo: __m256i, hi: __m256i, c2: __m256i, k: __m256i) -> [__m256i; 6] {
    [
        _mm256_clmulepi64_epi128::<0x00>(lo, k),
        _mm256_clmulepi64_epi128::<0x01>(lo, k),
        _mm256_clmulepi64_epi128::<0x10>(hi, k),
        _mm256_clmulepi64_epi128::<0x11>(hi, k),
        _mm256_clmulepi64_epi128::<0x00>(c2, k),
        _mm256_clmulepi64_epi128::<0x11>(c2, k),
    ]
}

/// Add the eight mixed products `t * k[i]` to [`MixedAcc8`].
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
pub unsafe fn mul_base8_add(acc: &mut MixedAcc8, t: F192, k: [F64; 8]) {
    // `t` in both lanes: [c0, c1] for both pair registers, [c2, c2] for the last.
    let t01 = _mm256_broadcastsi128_si256(pair(t.c0, t.c1));
    let t2 = _mm256_set1_epi64x(t.c2 as i64);
    for (half, acc) in acc.iter_mut().enumerate() {
        // SAFETY: the function carries both features; `k` is eight qwords.
        unsafe {
            let kv = _mm256_loadu_si256(k.as_ptr().add(4 * half).cast());
            for (acc, p) in acc.iter_mut().zip(mul_by_pairs256(t01, t01, t2, kv)) {
                *acc = _mm256_xor_si256(*acc, p);
            }
        }
    }
}

/// Reduce [`MixedAcc8`] into the eight sums.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
pub unsafe fn mul_base8_reduce(acc: MixedAcc8) -> [F192; 8] {
    let halves = acc.map(|[e0, e1, o0, o1, e2, o2]| {
        // SAFETY: the function carries both features; the reinterprets are between 256-bit values.
        unsafe {
            // Gather each product's low and high halves into qword-wise vectors, then reduce.
            let red = |x, y| reduce_lanes256(_mm256_unpacklo_epi64(x, y), _mm256_unpackhi_epi64(x, y));
            let even = transmute::<__m256i, [u64; 4]>(red(e0, e1));
            let odd = transmute::<__m256i, [u64; 4]>(red(o0, o1));
            let c2 = transmute::<__m256i, [u64; 4]>(red(e2, o2));
            std::array::from_fn::<F192, 4, _>(|i| {
                let (j, w) = (i / 2, if i % 2 == 0 { &even } else { &odd });
                F192::new(w[2 * j], w[2 * j + 1], c2[i])
            })
        }
    });
    *halves.as_flattened().as_array().unwrap()
}

/// Four elements in [`Lanes4`]'s form.
///
/// # Safety
///
/// Requires the `avx2` target feature.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn lanes4(v: [F192; 4]) -> Lanes4 {
    let half = |a: F192, b: F192| {
        [
            _mm256_set_epi64x(b.c1 as i64, b.c0 as i64, a.c1 as i64, a.c0 as i64),
            _mm256_set_epi64x(b.c2 as i64, b.c2 as i64, a.c2 as i64, a.c2 as i64),
        ]
    };
    [half(v[0], v[1]), half(v[2], v[3])]
}

/// Four consecutive elements, twelve words, into [`Lanes4`]'s form.
///
/// # Safety
///
/// Requires the `avx2` target feature.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn load_lanes4(v: &[F192; 4]) -> Lanes4 {
    let words = v.as_ptr().cast::<i64>();
    // Half `h` is words `6h..6h + 6`: `[c0, c1]` at 0 and 3, `[c2, c2]` from qwords 0 and 3 of
    // the four at 2, picked within their lanes.
    let half = |h: usize| {
        // SAFETY: words `6h..6h + 6` are in `v`.
        unsafe {
            let w = words.add(6 * h);
            let c22 = _mm256_permutevar_pd(_mm256_loadu_pd(w.add(2).cast()), _mm256_set_epi64x(2, 2, 0, 0));
            [_mm256_loadu2_m128i(w.add(3).cast(), w.cast()), _mm256_castpd_si256(c22)]
        }
    };
    [half(0), half(1)]
}

/// [`Lanes4`]'s form back to twelve consecutive words, the inverse of [`load_lanes4`].
///
/// # Safety
///
/// Requires the `avx2` target feature.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn store_lanes4(lanes: Lanes4, out: &mut [MaybeUninit<F192>; 4]) {
    let words = out.as_mut_ptr().cast::<i64>();
    for (h, [c01, c22]) in lanes.into_iter().enumerate() {
        // Words 2..6 of the half: `c2` of its first element, then `c0, c1, c2` of its second.
        let tail = _mm256_blend_epi32::<0xC3>(_mm256_permute4x64_epi64::<0xF8>(c01), c22);
        // SAFETY: words `6h..6h + 6` are in `out`.
        unsafe {
            _mm_storeu_si128(words.add(6 * h).cast(), _mm256_castsi256_si128(c01));
            _mm256_storeu_si256(words.add(6 * h + 2).cast(), tail);
        }
    }
}

/// The 4x4 transpose of [`Lanes4`] values: lane `j` of `out[i]` is lane `i` of `rows[j]`.
///
/// # Safety
///
/// Requires the `avx2` target feature.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn transpose_lanes4(rows: [Lanes4; 4]) -> [Lanes4; 4] {
    // Half `h` of `out[i]` pairs lane `i` of `rows[2h]` with lane `i` of `rows[2h + 1]`.
    let pick = |i: usize, h: usize, p: usize| {
        let (a, b) = (rows[2 * h][i / 2][p], rows[2 * h + 1][i / 2][p]);
        if i.is_multiple_of(2) {
            _mm256_permute2x128_si256::<0x20>(a, b)
        } else {
            _mm256_permute2x128_si256::<0x31>(a, b)
        }
    };
    std::array::from_fn(|i| std::array::from_fn(|h| [pick(i, h, 0), pick(i, h, 1)]))
}

/// Lane-wise XOR.
///
/// # Safety
///
/// Requires the `avx2` target feature.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn xor_lanes<const N: usize>(a: [[__m256i; N]; 2], b: [[__m256i; N]; 2]) -> [[__m256i; N]; 2] {
    std::array::from_fn(|h| std::array::from_fn(|i| _mm256_xor_si256(a[h][i], b[h][i])))
}

/// The y-folded Karatsuba products of two [`Lanes4`] operands, lane by lane.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
pub unsafe fn mul_lanes4(a: Lanes4, b: Lanes4) -> Wide4 {
    std::array::from_fn(|h| {
        let ([a01, a22], [b01, b22]) = (a[h], b[h]);
        // `[c0 + c2, c1 + c2]`, and `c0 + c1` in both qwords (the swap stays in its lane).
        let (a_s, b_s) = (_mm256_xor_si256(a01, a22), _mm256_xor_si256(b01, b22));
        let a_x = _mm256_xor_si256(a01, _mm256_shuffle_epi32::<0x4E>(a01));
        let b_x = _mm256_xor_si256(b01, _mm256_shuffle_epi32::<0x4E>(b01));
        fold(
            _mm256_clmulepi64_epi128::<0x00>(a01, b01),
            _mm256_clmulepi64_epi128::<0x11>(a01, b01),
            _mm256_clmulepi64_epi128::<0x00>(a22, b22),
            _mm256_clmulepi64_epi128::<0x00>(a_x, b_x),
            _mm256_clmulepi64_epi128::<0x00>(a_s, b_s),
            _mm256_clmulepi64_epi128::<0x11>(a_s, b_s),
            |x, y| _mm256_xor_si256(x, y),
        )
    })
}

/// Reduce [`mul_lanes4`]'s products into [`Lanes4`]'s form.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
pub unsafe fn reduce_lanes4(d: Wide4) -> Lanes4 {
    d.map(|[d0, d1, d2]| {
        // SAFETY: the function carries both features.
        unsafe {
            [
                reduce_lanes256(_mm256_unpacklo_epi64(d0, d1), _mm256_unpackhi_epi64(d0, d1)),
                reduce_lanes256(_mm256_unpacklo_epi64(d2, d2), _mm256_unpackhi_epi64(d2, d2)),
            ]
        }
    })
}

/// The sum of the four 128-bit lanes of [`mul_lanes4`]'s coefficients.
///
/// # Safety
///
/// Requires the `avx2` target feature.
#[cfg(all(
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn sum_lanes4([d0, d1]: Wide4) -> F192Unreduced {
    let coeffs = std::array::from_fn(|k| {
        let half = _mm256_xor_si256(d0[k], d1[k]);
        let q = _mm_xor_si128(_mm256_castsi256_si128(half), _mm256_extracti128_si256::<1>(half));
        // SAFETY: the reinterpret is between 128-bit values.
        unsafe { transmute::<__m128i, [u64; 2]>(q) }
    });
    F192Unreduced { coeffs }
}

/// Eight elements in coefficient planes: qword `l` of plane `k` is coefficient `k` of element `l`.
///
/// A product needs no packing: CLMUL immediate 0x00 multiplies the even elements, 0x11 the odd ones.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[derive(Clone, Copy, Debug)]
pub struct F192x8(pub [__m512i; 3]);

/// A sum of [`F192x8`] products, unreduced: every 128-bit lane of plane `k` holds part of coefficient `k`.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[derive(Clone, Copy, Debug)]
pub struct F192x8Sum([__m512i; 3]);

#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
impl F192x8 {
    /// The lane-wise sum.
    ///
    /// # Safety
    ///
    /// Requires the features this impl is compiled with.
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub fn add(self, rhs: Self) -> Self {
        Self([0, 1, 2].map(|k| _mm512_xor_si512(self.0[k], rhs.0[k])))
    }

    /// The y-folded Karatsuba products of the even (`IMM = 0x00`) or odd (`IMM = 0x11`) elements, one per lane.
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    fn karatsuba<const IMM: i32>(self, rhs: Self) -> [__m512i; 3] {
        let ([a0, a1, a2], [b0, b1, b2]) = (self.0, rhs.0);
        let mul = |x, y| _mm512_clmulepi64_epi128::<IMM>(x, y);
        let xor = |x, y| _mm512_xor_si512(x, y);
        fold(
            mul(a0, b0),
            mul(a1, b1),
            mul(a2, b2),
            mul(xor(a0, a1), xor(b0, b1)),
            mul(xor(a0, a2), xor(b0, b2)),
            mul(xor(a1, a2), xor(b1, b2)),
            xor,
        )
    }

    /// The eight lane-wise products.
    ///
    /// # Safety
    ///
    /// Requires the features this impl is compiled with.
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    pub fn mul(self, rhs: Self) -> Self {
        let (even, odd) = (self.karatsuba::<0x00>(rhs), self.karatsuba::<0x11>(rhs));
        // Lane j of `even` is element 2j's product and of `odd` element 2j + 1's: unpacking restores qword order.
        // SAFETY: the function carries both features.
        Self([0, 1, 2].map(|k| unsafe {
            reduce_lanes512(
                _mm512_unpacklo_epi64(even[k], odd[k]),
                _mm512_unpackhi_epi64(even[k], odd[k]),
            )
        }))
    }
}

#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
impl F192x8Sum {
    /// The empty sum.
    ///
    /// # Safety
    ///
    /// Requires the features this impl is compiled with.
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub fn zero() -> Self {
        Self([_mm512_setzero_si512(); 3])
    }

    /// Add the eight lane-wise products of `a` and `b`.
    ///
    /// # Safety
    ///
    /// Requires the features this impl is compiled with.
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    pub fn mul_add(&mut self, a: F192x8, b: F192x8) {
        let (even, odd) = (a.karatsuba::<0x00>(b), a.karatsuba::<0x11>(b));
        for k in 0..3 {
            self.0[k] = _mm512_ternarylogic_epi64::<0x96>(self.0[k], even[k], odd[k]);
        }
    }

    /// The whole sum, its lanes folded together.
    ///
    /// # Safety
    ///
    /// Requires the features this impl is compiled with.
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub fn total(self) -> F192Unreduced {
        // SAFETY: the function carries `avx512f`.
        unsafe { sum_lanes4(self.0) }
    }
}
