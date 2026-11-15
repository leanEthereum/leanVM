//! The lanes in vector registers, with VPCLMULQDQ: four elements to a ZMM register with AVX-512, two to a YMM
//! register with AVX2. An element keeps its memory layout, `[c0, c1]` in one 128-bit lane, so loads and stores are
//! plain moves, and every product and reduction stays inside its 128-bit lane: only the mixed product's spread of
//! the `K` operand and [`Wide8`]'s interleave cross lanes. A product is Karatsuba (three carry-less multiplications,
//! the scarce unit on Zen 5) and a reduction shifts, XORs and one byte lookup.
//!
//! The kernels are written once over the register type `V` and the moves in `v`, each an AVX-512 or an AVX2
//! instruction.

use core::arch::x86_64::*;
use core::mem::transmute;

use super::Linear16;
use crate::field::gf2_64::reduce;
use crate::field::{F64, F128};
use v::V;

#[cfg(not(target_feature = "gfni"))]
pub use super::portable::{ByteMap, map_bytes, transpose_bits};

/// 128-bit lanes in a register.
const W: usize = size_of::<V>() / 16;
/// Registers in eight `E` elements, or eight 128-bit products.
const R: usize = 8 / W;
/// Registers in eight `K` elements.
const Q: usize = R / 2;

/// Eight `K` elements, in memory order.
#[derive(Clone, Copy, Debug)]
pub struct F64x8([V; Q]);

/// Eight `E` elements, in memory order: lane `j` of register `r` is element `W * r + j`.
#[derive(Clone, Copy, Debug)]
pub struct F128x8([V; R]);

/// Eight unreduced `E` sums: register `r` holds the 128-bit coefficients of `y^0` and of `y^1` of the elements
/// [`F128x8`]'s register `r` holds, lane by lane.
#[derive(Clone, Copy, Debug)]
pub struct Acc8([[V; 2]; R]);

/// Eight sums of 128-bit carry-less products: register pair `q` holds those of the even and of the odd lanes of the
/// words register `q` of [`F64x8`] holds, interleaved only when read.
#[derive(Clone, Copy, Debug)]
pub struct Wide8([[V; 2]; Q]);

/// Eight words in registers.
#[inline(always)]
fn regs(x: [u64; 8]) -> [V; Q] {
    // SAFETY: both sides are plain bits of one size.
    unsafe { transmute(x) }
}

/// The eight words of registers.
#[inline(always)]
fn words(x: [V; Q]) -> [u64; 8] {
    // SAFETY: both sides are plain bits of one size.
    unsafe { transmute(x) }
}

/// One product, the scalar [`F128`] multiply: [`karatsuba`] and [`reduce_pair`] on one XMM register.
#[inline(always)]
pub(crate) fn mul(a: F128, b: F128) -> F128 {
    // SAFETY: the module's cfg enables vpclmulqdq and avx2, which imply pclmulqdq and ssse3; each transmute is of 16
    // plain bytes.
    unsafe {
        let (a, b) = (transmute::<F128, __m128i>(a), transmute::<F128, __m128i>(b));
        let sum = |x| _mm_xor_si128(x, _mm_shuffle_epi32::<0x4E>(x));
        let (p0, p1) = (_mm_clmulepi64_si128::<0x00>(a, b), _mm_clmulepi64_si128::<0x11>(a, b));
        let p01 = _mm_clmulepi64_si128::<0x00>(sum(a), sum(b));
        let times_x = _mm_or_si128(_mm_slli_epi64::<1>(p1), _mm_slli_si128::<8>(_mm_srli_epi64::<63>(p1)));
        let d0 = _mm_xor_si128(p0, p1);
        let d1 = _mm_xor_si128(_mm_xor_si128(p01, d0), times_x);
        let (lo, hi) = (_mm_unpacklo_epi64(d0, d1), _mm_unpackhi_epi64(d0, d1));
        let z = _mm_xor_si128(hi, _mm_slli_epi64::<1>(hi));
        let g_spill = _mm_shuffle_epi8(transmute::<[u8; 16], __m128i>(G_SPILL), _mm_srli_epi64::<60>(hi));
        let c = _mm_xor_si128(_mm_xor_si128(lo, z), _mm_xor_si128(_mm_slli_epi64::<3>(z), g_spill));
        transmute::<__m128i, F128>(c)
    }
}

impl F64x8 {
    pub const ZERO: Self = Self([v::ZERO; Q]);

    #[inline(always)]
    pub fn splat(k: F64) -> Self {
        Self([v::splat(k.0, k.0); Q])
    }

    #[inline(always)]
    pub fn from_array(k: &[F64; 8]) -> Self {
        Self(regs(k.map(|k| k.0)))
    }

    #[inline(always)]
    pub fn to_array(self) -> [F64; 8] {
        words(self.0).map(F64)
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|q| v::xor(self.0[q], rhs.0[q])))
    }

    /// The even elements' products in one register and the odd ones' in another, then the reduction puts them back
    /// in memory order.
    #[inline(always)]
    pub(super) fn product(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|q| {
            let (a, b) = (self.0[q], rhs.0[q]);
            reduce_pair([v::clmul::<0x00>(a, b), v::clmul::<0x11>(a, b)])
        }))
    }
}

impl F128x8 {
    pub const ZERO: Self = Self([v::ZERO; R]);

    #[inline(always)]
    pub fn splat(e: F128) -> Self {
        Self([v::splat(e.c0, e.c1); R])
    }

    #[inline(always)]
    pub fn from_array(e: &[F128; 8]) -> Self {
        // SAFETY: both sides are plain bits of one size.
        Self(unsafe { transmute::<[F128; 8], [V; R]>(*e) })
    }

    #[inline(always)]
    pub fn to_array(self) -> [F128; 8] {
        // SAFETY: both sides are plain bits of one size.
        unsafe { transmute::<[V; R], [F128; 8]>(self.0) }
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|r| v::xor(self.0[r], rhs.0[r])))
    }

    /// The eight products, unreduced: three carry-less multiplications per register.
    #[inline(always)]
    pub fn mul_unreduced(self, rhs: Self) -> Acc8 {
        Acc8(core::array::from_fn(|r| karatsuba(self.0[r], rhs.0[r])))
    }

    /// The eight mixed products `self[i] * k[i]`, unreduced: two carry-less multiplications per register, each
    /// coefficient against `k[i]`, spread over both qwords of element `i`'s lane.
    #[inline(always)]
    pub fn mul_base_unreduced(self, k: F64x8) -> Acc8 {
        let k = v::spread(k.0);
        Acc8(core::array::from_fn(|r| {
            [v::clmul::<0x00>(self.0[r], k[r]), v::clmul::<0x11>(self.0[r], k[r])]
        }))
    }
}

impl Acc8 {
    pub const ZERO: Self = Self([[v::ZERO; 2]; R]);

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|r| {
            [v::xor(self.0[r][0], rhs.0[r][0]), v::xor(self.0[r][1], rhs.0[r][1])]
        }))
    }

    /// Every lane reduced.
    #[inline(always)]
    pub fn reduce(self) -> F128x8 {
        F128x8(self.0.map(reduce_pair))
    }

    /// The sum of the eight lanes, reduced once.
    #[inline(always)]
    pub fn sum(self) -> F128 {
        let [d0, d1] = self
            .0
            .into_iter()
            .reduce(|s, x| [v::xor(s[0], x[0]), v::xor(s[1], x[1])])
            .unwrap();
        F128::new(reduce(v::lane_sum(d0)), reduce(v::lane_sum(d1)))
    }
}

impl Wide8 {
    pub const ZERO: Self = Self([[v::ZERO; 2]; Q]);

    /// The eight carry-less products `a[i] * b[i]`.
    #[inline(always)]
    pub fn mul(a: [u64; 8], b: [u64; 8]) -> Self {
        let (a, b) = (regs(a), regs(b));
        Self(core::array::from_fn(|q| {
            [v::clmul::<0x00>(a[q], b[q]), v::clmul::<0x11>(a[q], b[q])]
        }))
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|q| {
            [v::xor(self.0[q][0], rhs.0[q][0]), v::xor(self.0[q][1], rhs.0[q][1])]
        }))
    }

    #[inline(always)]
    pub(super) fn to_array(self) -> [u128; 8] {
        let out: [[V; 2]; Q] = self.0.map(|[even, odd]| v::interleave(even, odd));
        // SAFETY: both sides are plain bits of one size.
        unsafe { transmute::<[[V; 2]; Q], [u128; 8]>(out) }
    }
}

/// The low 64 bits of the eight carry-less products `a[i] * b[i]`: the even and odd products' low qwords, unpacked
/// in place.
#[inline(always)]
pub fn clmul8_low(a: [u64; 8], b: [u64; 8]) -> [u64; 8] {
    let (a, b) = (regs(a), regs(b));
    words(core::array::from_fn(|q| {
        v::unpacklo(v::clmul::<0x00>(a[q], b[q]), v::clmul::<0x11>(a[q], b[q]))
    }))
}

/// A GF(2)-linear map of bytes, as GF2P8AFFINEQB's matrix: bit `c` of byte `7 - k` is bit `k` of the image of bit
/// `c`.
#[cfg(target_feature = "gfni")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteMap {
    matrix: u64,
}

#[cfg(target_feature = "gfni")]
impl ByteMap {
    /// The map sending bit `c` to `images[c]`.
    pub const fn new(images: [u8; 8]) -> Self {
        let mut matrix = 0u64;
        let mut c = 0;
        while c < 8 {
            let mut k = 0;
            while k < 8 {
                matrix |= ((images[c] >> k & 1) as u64) << (c + 8 * (7 - k));
                k += 1;
            }
            c += 1;
        }
        Self { matrix }
    }
}

/// Every byte of `x` through `m`: one affine byte map per register.
#[cfg(target_feature = "gfni")]
#[inline(always)]
pub fn map_bytes(m: &ByteMap, x: [u64; 8]) -> [u64; 8] {
    let matrix = v::splat(m.matrix, m.matrix);
    words(regs(x).map(|x| v::affine(x, matrix)))
}

/// `m` of each 16-bit field of each lane, by nibble lookups: per output byte, the low and the high byte of every
/// field looked up in place, the high one's moved onto the low one, then the four bytes of each image gathered by
/// unpacking.
#[inline(always)]
pub fn map_fields(m: &Linear16, x: [u64; 8]) -> [[u64; 8]; 4] {
    const NIBBLES: u64 = 0x0f0f_0f0f_0f0f_0f0f;
    const LOW_BYTES: u64 = 0x00ff_00ff_00ff_00ff;
    let (nibble, low_bytes) = (v::splat(NIBBLES, NIBBLES), v::splat(LOW_BYTES, LOW_BYTES));
    let mut out = [[v::ZERO; Q]; 4];
    for (q, x) in regs(x).into_iter().enumerate() {
        let (lo, hi) = (v::and(x, nibble), v::and(v::shr::<4>(x), nibble));
        // Byte `o` of each field's image, at the field's low byte.
        let s: [V; 4] = core::array::from_fn(|o| {
            let t = &m.nibbles[o];
            let low = v::xor(v::lookup(t[0], lo), v::lookup(t[1], hi));
            let high = v::xor(v::lookup(t[2], lo), v::lookup(t[3], hi));
            v::and(v::xor(low, v::shr::<8>(high)), low_bytes)
        });
        let (s01, s23) = (v::or(s[0], v::shl::<8>(s[1])), v::or(s[2], v::shl::<8>(s[3])));
        // Per 128-bit lane, the images of its first word's four fields, then of its second word's.
        let (first, second) = (v::unpacklo16(s01, s23), v::unpackhi16(s01, s23));
        let (f01, f23) = (v::unpacklo32(first, second), v::unpackhi32(first, second));
        out[0][q] = v::unpacklo32(f01, v::ZERO);
        out[1][q] = v::unpackhi32(f01, v::ZERO);
        out[2][q] = v::unpacklo32(f23, v::ZERO);
        out[3][q] = v::unpackhi32(f23, v::ZERO);
    }
    out.map(words)
}

/// Eight rows of eight words transposed, as four 4 by 4 blocks of YMM registers.
#[inline(always)]
pub fn transpose_words(rows: &[[u64; 8]; 8]) -> [[u64; 8]; 8] {
    /// The 4 by 4 transpose of the words of four registers.
    #[inline(always)]
    fn transpose4(a: [__m256i; 4]) -> [__m256i; 4] {
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            let (t0, t1) = (_mm256_unpacklo_epi64(a[0], a[1]), _mm256_unpackhi_epi64(a[0], a[1]));
            let (t2, t3) = (_mm256_unpacklo_epi64(a[2], a[3]), _mm256_unpackhi_epi64(a[2], a[3]));
            [
                _mm256_permute2x128_si256::<0x20>(t0, t2),
                _mm256_permute2x128_si256::<0x20>(t1, t3),
                _mm256_permute2x128_si256::<0x31>(t0, t2),
                _mm256_permute2x128_si256::<0x31>(t1, t3),
            ]
        }
    }
    // SAFETY: both sides are plain bits of one size.
    let r = unsafe { transmute::<[[u64; 8]; 8], [[__m256i; 2]; 8]>(*rows) };
    let mut out = [[r[0][0]; 2]; 8];
    for (rb, cb) in [(0, 0), (0, 1), (1, 0), (1, 1)] {
        let t = transpose4(core::array::from_fn(|k| r[4 * rb + k][cb]));
        for (c, t) in t.into_iter().enumerate() {
            out[4 * cb + c][rb] = t;
        }
    }
    // SAFETY: as above.
    unsafe { transmute::<[[__m256i; 2]; 8], [[u64; 8]; 8]>(out) }
}

/// The 8 by 64 bit matrix of `rows` transposed: bit `k` of byte `n` is bit `n` of `rows[k]`. A byte transpose
/// gathers word `c`'s bytes from the rows, last row first, and an affine byte map with each word as its matrix
/// transposes its bits.
#[cfg(target_feature = "gfni")]
#[inline(always)]
pub fn transpose_bits(rows: [u64; 8]) -> [u64; 8] {
    /// In each 128-bit lane, byte `c` of its second word then byte `c` of its first, for each `c`.
    const PAIRS: [u8; 16] = [8, 0, 9, 1, 10, 2, 11, 3, 12, 4, 13, 5, 14, 6, 15, 7];
    /// The bytes of the affine map's source: byte `i` is bit `i` alone.
    const UNITS: u64 = 0x8040_2010_0804_0201;
    // SAFETY: the module's cfg enables avx2 and gfni; both sides of each transmute are plain bits of one size.
    unsafe {
        let [r0, r1] = transmute::<[u64; 8], [__m256i; 2]>(rows);
        let pairs = _mm256_broadcastsi128_si256(transmute::<[u8; 16], __m128i>(PAIRS));
        // Rows 6, 7 | 2, 3 and 4, 5 | 0, 1, each 16-bit field `c` then holding byte `c` of a lane's two rows.
        let p = _mm256_shuffle_epi8(_mm256_permute2x128_si256::<0x31>(r1, r0), pairs);
        let q = _mm256_shuffle_epi8(_mm256_permute2x128_si256::<0x20>(r1, r0), pairs);
        let order = _mm256_setr_epi32(0, 4, 1, 5, 2, 6, 3, 7);
        let words = [_mm256_unpacklo_epi16(p, q), _mm256_unpackhi_epi16(p, q)].map(|w| {
            _mm256_gf2p8affine_epi64_epi8::<0>(_mm256_set1_epi64x(UNITS as i64), _mm256_permutevar8x32_epi32(w, order))
        });
        transmute::<[__m256i; 2], [u64; 8]>(words)
    }
}

/// Sixteen rows of 64 bytes transposed: byte `b` of output `n` is byte `n` of `rows[b]`. Within each 128-bit lane,
/// four rounds of unpacks pair registers 8, 4, 2 and 1 apart; fed the rows in bit-reversed order, they leave
/// register `i` holding column `i`.
#[inline(always)]
pub fn transpose_bytes(rows: &[[u64; 8]; 16]) -> [u128; 64] {
    let r = rows.map(regs);
    let mut out = [[[0u128; W]; 16]; Q];
    for (h, out) in out.iter_mut().enumerate() {
        let mut a: [V; 16] = core::array::from_fn(|b| r[(b as u8).reverse_bits() as usize >> 4][h]);
        for stride in [8, 4, 2, 1] {
            let b = a;
            for i in (0..16).filter(|i| i & stride == 0) {
                (a[i], a[i + stride]) = match stride {
                    8 => (v::unpacklo8(b[i], b[i + 8]), v::unpackhi8(b[i], b[i + 8])),
                    4 => (v::unpacklo16(b[i], b[i + 4]), v::unpackhi16(b[i], b[i + 4])),
                    2 => (v::unpacklo32(b[i], b[i + 2]), v::unpackhi32(b[i], b[i + 2])),
                    _ => (v::unpacklo(b[i], b[i + 1]), v::unpackhi(b[i], b[i + 1])),
                };
            }
        }
        // SAFETY: both sides are plain bits of one size.
        *out = unsafe { transmute::<[V; 16], [[u128; W]; 16]>(a) };
    }
    // Lane `l` of register `i` of part `h` is column `16 (W h + l) + i`.
    core::array::from_fn(|n| out[n / 16 / W][n % 16][n / 16 % W])
}

/// `g(spill)` per top nibble `n` of a high word, in every 128-bit lane: `spill = n ^ n>>1 ^ n>>3` are the bits
/// `g(hi) = hi * (x^4 + x^3 + x + 1)` pushes past x^63, and `g(spill)` fits a byte.
const G_SPILL: [u8; 16] = {
    let mut t = [0u8; 16];
    let mut n = 0;
    while n < 16 {
        let spill = n ^ (n >> 1) ^ (n >> 3);
        t[n] = (spill ^ (spill << 1) ^ (spill << 3) ^ (spill << 4)) as u8;
        n += 1;
    }
    t
};

/// Qword `i` reduced: `lo[i] + hi[i] * x^64` modulo the base polynomial, as [`reduce`] computes it.
///
/// `lo ^ g(hi) ^ g(spill)`, with `g(h) = z ^ z<<3` for `z = h ^ h<<1`, and `g(spill)` one in-lane byte lookup on the
/// top nibble of `hi`.
#[inline(always)]
fn reduce_qwords(lo: V, hi: V) -> V {
    let z = v::xor(hi, v::shl::<1>(hi));
    let g_spill = v::lookup(G_SPILL, v::shr::<60>(hi));
    v::xor(v::xor(lo, z), v::xor(v::shl::<3>(z), g_spill))
}

/// `[d0, d1]` per 128-bit lane, each a coefficient's 128-bit polynomial, reduced to `[c0, c1]`.
#[inline(always)]
fn reduce_pair([d0, d1]: [V; 2]) -> V {
    reduce_qwords(v::unpacklo(d0, d1), v::unpackhi(d0, d1))
}

/// The y-folded Karatsuba product, lane by lane: with `p0 = a0 b0`, `p1 = a1 b1`, `p01 = (a0 + a1)(b0 + b1)` and
/// `y^2 = x y + 1`, the coefficients are `d0 = p0 + p1` and `d1 = p01 + p0 + p1 + x p1`. Both qwords of `a + swap(a)`
/// hold `a0 + a1`, so every product reads one qword of each operand's 128-bit lane.
#[inline(always)]
fn karatsuba(a: V, b: V) -> [V; 2] {
    let (p0, p1) = (v::clmul::<0x00>(a, b), v::clmul::<0x11>(a, b));
    let p01 = v::clmul::<0x00>(v::xor(a, v::swap(a)), v::xor(b, v::swap(b)));
    let d0 = v::xor(p0, p1);
    [d0, v::xor(v::xor(p01, d0), v::times_x(p1))]
}

/// The register moves, each one AVX-512 instruction on a ZMM register or the AVX2 one on a YMM register.
mod v {
    use core::arch::x86_64::*;

    /// `$zmm` with AVX-512, else `$ymm`.
    macro_rules! width {
        ($zmm:expr, $ymm:expr $(,)?) => {
            // SAFETY: the backend's cfg enables avx2 and vpclmulqdq, and the AVX-512 arm's avx512f and avx512bw; the
            // operands are plain vectors.
            unsafe {
                cfg_select! {
                    all(target_feature = "avx512f", target_feature = "avx512bw") => { $zmm }
                    _ => { $ymm }
                }
            }
        };
    }

    cfg_select! {
        all(target_feature = "avx512f", target_feature = "avx512bw") => {
            pub type V = __m512i;

            #[inline(always)]
            pub fn shl<const N: u32>(a: V) -> V {
                // SAFETY: the backend's cfg and this arm's enable avx512f.
                unsafe { _mm512_slli_epi64::<N>(a) }
            }

            #[inline(always)]
            pub fn shr<const N: u32>(a: V) -> V {
                // SAFETY: as `shl`.
                unsafe { _mm512_srli_epi64::<N>(a) }
            }
        }
        _ => {
            pub type V = __m256i;

            #[inline(always)]
            pub fn shl<const N: i32>(a: V) -> V {
                // SAFETY: the backend's cfg enables avx2.
                unsafe { _mm256_slli_epi64::<N>(a) }
            }

            #[inline(always)]
            pub fn shr<const N: i32>(a: V) -> V {
                // SAFETY: as `shl`.
                unsafe { _mm256_srli_epi64::<N>(a) }
            }
        }
    }

    // SAFETY: an all-zero bit pattern is a valid vector.
    pub const ZERO: V = unsafe { core::mem::zeroed() };

    /// `[lo, hi]` in every 128-bit lane.
    #[inline(always)]
    pub fn splat(lo: u64, hi: u64) -> V {
        let (l, h) = (lo as i64, hi as i64);
        width!(_mm512_set_epi64(h, l, h, l, h, l, h, l), _mm256_set_epi64x(h, l, h, l))
    }

    #[inline(always)]
    pub fn xor(a: V, b: V) -> V {
        width!(_mm512_xor_si512(a, b), _mm256_xor_si256(a, b))
    }

    #[inline(always)]
    pub fn and(a: V, b: V) -> V {
        width!(_mm512_and_si512(a, b), _mm256_and_si256(a, b))
    }

    #[inline(always)]
    pub fn or(a: V, b: V) -> V {
        width!(_mm512_or_si512(a, b), _mm256_or_si256(a, b))
    }

    /// The carry-less product of a qword of each 128-bit lane of `a` and one of `b`'s, chosen by `I`.
    #[inline(always)]
    pub fn clmul<const I: i32>(a: V, b: V) -> V {
        width!(_mm512_clmulepi64_epi128::<I>(a, b), _mm256_clmulepi64_epi128::<I>(a, b))
    }

    /// The qwords of each 128-bit lane swapped.
    #[inline(always)]
    pub fn swap(a: V) -> V {
        width!(_mm512_shuffle_epi32::<0x4E>(a), _mm256_shuffle_epi32::<0x4E>(a))
    }

    /// `x * p` for each 128-bit lane `p` of degree at most 126: a one-bit shift across the qwords.
    #[inline(always)]
    pub fn times_x(p: V) -> V {
        width!(
            _mm512_or_si512(
                _mm512_slli_epi64::<1>(p),
                _mm512_bslli_epi128::<8>(_mm512_srli_epi64::<63>(p))
            ),
            _mm256_or_si256(
                _mm256_slli_epi64::<1>(p),
                _mm256_bslli_epi128::<8>(_mm256_srli_epi64::<63>(p))
            ),
        )
    }

    /// Each byte `b < 16` replaced by `table[b]`.
    #[inline(always)]
    pub fn lookup(table: [u8; 16], b: V) -> V {
        // SAFETY: the transmute is of 16 plain bytes.
        let t = unsafe { core::mem::transmute::<[u8; 16], __m128i>(table) };
        width!(
            _mm512_shuffle_epi8(_mm512_broadcast_i32x4(t), b),
            _mm256_shuffle_epi8(_mm256_broadcastsi128_si256(t), b),
        )
    }

    /// Each byte through the matrix of its word in `m`.
    #[cfg(target_feature = "gfni")]
    #[inline(always)]
    pub fn affine(x: V, m: V) -> V {
        width!(
            _mm512_gf2p8affine_epi64_epi8::<0>(x, m),
            _mm256_gf2p8affine_epi64_epi8::<0>(x, m)
        )
    }

    #[inline(always)]
    pub fn unpacklo8(a: V, b: V) -> V {
        width!(_mm512_unpacklo_epi8(a, b), _mm256_unpacklo_epi8(a, b))
    }

    #[inline(always)]
    pub fn unpackhi8(a: V, b: V) -> V {
        width!(_mm512_unpackhi_epi8(a, b), _mm256_unpackhi_epi8(a, b))
    }

    #[inline(always)]
    pub fn unpacklo16(a: V, b: V) -> V {
        width!(_mm512_unpacklo_epi16(a, b), _mm256_unpacklo_epi16(a, b))
    }

    #[inline(always)]
    pub fn unpackhi16(a: V, b: V) -> V {
        width!(_mm512_unpackhi_epi16(a, b), _mm256_unpackhi_epi16(a, b))
    }

    #[inline(always)]
    pub fn unpacklo32(a: V, b: V) -> V {
        width!(_mm512_unpacklo_epi32(a, b), _mm256_unpacklo_epi32(a, b))
    }

    #[inline(always)]
    pub fn unpackhi32(a: V, b: V) -> V {
        width!(_mm512_unpackhi_epi32(a, b), _mm256_unpackhi_epi32(a, b))
    }

    #[inline(always)]
    pub fn unpacklo(a: V, b: V) -> V {
        width!(_mm512_unpacklo_epi64(a, b), _mm256_unpacklo_epi64(a, b))
    }

    #[inline(always)]
    pub fn unpackhi(a: V, b: V) -> V {
        width!(_mm512_unpackhi_epi64(a, b), _mm256_unpackhi_epi64(a, b))
    }

    /// The XOR of the 128-bit lanes.
    #[inline(always)]
    pub fn lane_sum(a: V) -> u128 {
        let x = width!(
            {
                let h = _mm256_xor_si256(_mm512_castsi512_si256(a), _mm512_extracti64x4_epi64::<1>(a));
                _mm_xor_si128(_mm256_castsi256_si128(h), _mm256_extracti128_si256::<1>(h))
            },
            _mm_xor_si128(_mm256_castsi256_si128(a), _mm256_extracti128_si256::<1>(a)),
        );
        // SAFETY: the transmute is of 16 plain bytes.
        unsafe { core::mem::transmute(x) }
    }

    /// Eight `K` elements spread one to a 128-bit lane, in both its qwords: lane `j` of register `r` is
    /// `k[W r + j]`.
    #[inline(always)]
    pub fn spread(k: [V; super::Q]) -> [V; super::R] {
        width!(
            [
                _mm512_permutexvar_epi64(_mm512_setr_epi64(0, 0, 1, 1, 2, 2, 3, 3), k[0]),
                _mm512_permutexvar_epi64(_mm512_setr_epi64(4, 4, 5, 5, 6, 6, 7, 7), k[0]),
            ],
            [
                _mm256_permute4x64_epi64::<0x50>(k[0]),
                _mm256_permute4x64_epi64::<0xFA>(k[0]),
                _mm256_permute4x64_epi64::<0x50>(k[1]),
                _mm256_permute4x64_epi64::<0xFA>(k[1]),
            ],
        )
    }

    /// Products of the even qwords and of the odd ones, one per 128-bit lane, in memory order over two registers.
    #[inline(always)]
    pub fn interleave(even: V, odd: V) -> [V; 2] {
        width!(
            [
                _mm512_permutex2var_epi64(even, _mm512_setr_epi64(0, 1, 8, 9, 2, 3, 10, 11), odd),
                _mm512_permutex2var_epi64(even, _mm512_setr_epi64(4, 5, 12, 13, 6, 7, 14, 15), odd),
            ],
            [
                _mm256_permute2x128_si256::<0x20>(even, odd),
                _mm256_permute2x128_si256::<0x31>(even, odd),
            ],
        )
    }
}
