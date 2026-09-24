//! The x86-64 backends: the scalar kernel, and the AVX2 and AVX-512 batches.

mod gpr;
#[cfg(target_feature = "avx512f")]
mod zmm;

pub(super) use gpr::compress;

// A baseline x86-64 build has only the scalar kernel.
#[cfg(target_feature = "avx2")]
use super::batch::Lanes32;
// Only the AVX-512 digest store needs it.
#[cfg(target_feature = "avx512f")]
use super::OUT_LEN;
#[cfg(target_feature = "avx2")]
use core::arch::x86_64::*;

/// AVX2: eight lanes.
///
/// There is no 32-bit vector rotate before AVX-512.
///
/// The byte-aligned rotations (16, 8) become one `vpshufb`, the others (12, 7) a shift pair.
///
/// On an AVX-512 target only the tests use it.
#[cfg(target_feature = "avx2")]
#[cfg_attr(target_feature = "avx512f", allow(dead_code))]
#[derive(Clone, Copy)]
pub(super) struct Avx2(__m256i);

#[cfg(target_feature = "avx2")]
impl Lanes32 for Avx2 {
    const WIDTH: usize = 8;

    #[inline(always)]
    unsafe fn load(p: *const u32) -> Self {
        Self(unsafe { _mm256_loadu_si256(p.cast()) })
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u32) {
        unsafe { _mm256_storeu_si256(p.cast(), self.0) }
    }
    #[inline(always)]
    fn splat(x: u32) -> Self {
        Self(unsafe { _mm256_set1_epi32(x as i32) })
    }
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Self(unsafe { _mm256_add_epi32(self.0, o.0) })
    }
    #[inline(always)]
    fn xor(self, o: Self) -> Self {
        Self(unsafe { _mm256_xor_si256(self.0, o.0) })
    }
    #[inline(always)]
    fn rotr<const N: u32>(self) -> Self {
        // Byte shuffles rotating each 32-bit lane right by 2 and by 1 bytes, per 16-byte half.
        const ROT16: [i8; 16] = [2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13];
        const ROT8: [i8; 16] = [1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12];
        unsafe {
            let shuf = |m: [i8; 16]| {
                let half = _mm_loadu_si128(m.as_ptr().cast());
                Self(_mm256_shuffle_epi8(self.0, _mm256_set_m128i(half, half)))
            };
            match N {
                16 => shuf(ROT16),
                8 => shuf(ROT8),
                12 => Self(_mm256_or_si256(
                    _mm256_srli_epi32(self.0, 12),
                    _mm256_slli_epi32(self.0, 20),
                )),
                7 => Self(_mm256_or_si256(
                    _mm256_srli_epi32(self.0, 7),
                    _mm256_slli_epi32(self.0, 25),
                )),
                _ => unreachable!("BLAKE2s rotates by 16, 12, 8 or 7"),
            }
        }
    }

    /// Two 8x8 transposes: each block is two `ymm`, words 0..8 and 8..16.
    #[inline(always)]
    unsafe fn transpose(src: *const u8, stride: usize, block: &mut [Self; 16]) {
        unsafe {
            for half in 0..2 {
                let r: [__m256i; 8] =
                    std::array::from_fn(|l| _mm256_loadu_si256(src.add(l * stride + 32 * half).cast()));
                let mut t = [_mm256_setzero_si256(); 8];
                for k in 0..4 {
                    t[2 * k] = _mm256_unpacklo_epi32(r[2 * k], r[2 * k + 1]);
                    t[2 * k + 1] = _mm256_unpackhi_epi32(r[2 * k], r[2 * k + 1]);
                }
                let s: [__m256i; 8] = [
                    _mm256_unpacklo_epi64(t[0], t[2]),
                    _mm256_unpackhi_epi64(t[0], t[2]),
                    _mm256_unpacklo_epi64(t[1], t[3]),
                    _mm256_unpackhi_epi64(t[1], t[3]),
                    _mm256_unpacklo_epi64(t[4], t[6]),
                    _mm256_unpackhi_epi64(t[4], t[6]),
                    _mm256_unpacklo_epi64(t[5], t[7]),
                    _mm256_unpackhi_epi64(t[5], t[7]),
                ];
                for k in 0..4 {
                    let w = 8 * half + k;
                    block[w] = Self(_mm256_permute2x128_si256(s[k], s[k + 4], 0x20));
                    block[w + 4] = Self(_mm256_permute2x128_si256(s[k], s[k + 4], 0x31));
                }
            }
        }
    }
}

/// AVX-512: sixteen lanes, and `vprord` makes every rotation one instruction.
///
/// Two groups run together, so neither waits on its own dependency chain.
#[cfg(target_feature = "avx512f")]
#[derive(Clone, Copy)]
pub(super) struct Avx512(__m512i);

#[cfg(target_feature = "avx512f")]
impl Lanes32 for Avx512 {
    const WIDTH: usize = 16;

    #[inline(always)]
    unsafe fn load(p: *const u32) -> Self {
        Self(unsafe { _mm512_loadu_si512(p.cast()) })
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u32) {
        unsafe { _mm512_storeu_si512(p.cast(), self.0) }
    }
    #[inline(always)]
    fn splat(x: u32) -> Self {
        Self(unsafe { _mm512_set1_epi32(x as i32) })
    }
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Self(unsafe { _mm512_add_epi32(self.0, o.0) })
    }
    #[inline(always)]
    fn xor(self, o: Self) -> Self {
        Self(unsafe { _mm512_xor_si512(self.0, o.0) })
    }
    #[inline(always)]
    fn rotr<const N: u32>(self) -> Self {
        unsafe {
            match N {
                16 => Self(_mm512_ror_epi32(self.0, 16)),
                12 => Self(_mm512_ror_epi32(self.0, 12)),
                8 => Self(_mm512_ror_epi32(self.0, 8)),
                7 => Self(_mm512_ror_epi32(self.0, 7)),
                _ => unreachable!("BLAKE2s rotates by 16, 12, 8 or 7"),
            }
        }
    }

    /// Two groups: 32 state vectors, the whole register file.
    const GROUPS: usize = 2;

    #[inline(always)]
    unsafe fn compress_groups<const G: usize>(h: &mut [[Self; 8]; G], m: [&[Self; 16]; G], t: u64, last: bool) {
        // A lone tail group takes the generic rounds.
        if G != 2 {
            // SAFETY: forwarded from the caller.
            return unsafe { super::batch::compress_groups::<Self, G>(h, m, t, last) };
        }
        // SAFETY: the kernel's layouts, two groups of 8 vectors and two blocks of 16.
        unsafe {
            zmm::compress_x2(
                h.as_mut_ptr().cast(),
                m[0].as_ptr().cast(),
                m[1].as_ptr().cast(),
                t,
                last,
            )
        }
    }

    /// An 8x16 to 16x8 transpose for the digests.
    ///
    /// Two unpack phases leave each digest in two 128-bit lanes:
    ///
    /// ```text
    ///     digest 4L + c    lane L of s[c], then lane L of s[4 + c]
    /// ```
    #[inline(always)]
    unsafe fn store_digests(h: &[Self; 8], out: *mut u8) {
        unsafe {
            let mut s = [_mm512_setzero_si512(); 8];
            for a in 0..2 {
                let (r0, r1, r2, r3) = (h[4 * a].0, h[4 * a + 1].0, h[4 * a + 2].0, h[4 * a + 3].0);
                let lo01 = _mm512_unpacklo_epi32(r0, r1);
                let hi01 = _mm512_unpackhi_epi32(r0, r1);
                let lo23 = _mm512_unpacklo_epi32(r2, r3);
                let hi23 = _mm512_unpackhi_epi32(r2, r3);
                s[4 * a] = _mm512_unpacklo_epi64(lo01, lo23);
                s[4 * a + 1] = _mm512_unpackhi_epi64(lo01, lo23);
                s[4 * a + 2] = _mm512_unpacklo_epi64(hi01, hi23);
                s[4 * a + 3] = _mm512_unpackhi_epi64(hi01, hi23);
            }
            macro_rules! lane {
                ($l:expr, $c:expr) => {{
                    let p = out.add((4 * $l + $c) * OUT_LEN);
                    _mm_storeu_si128(p.cast(), _mm512_extracti32x4_epi32::<$l>(s[$c]));
                    _mm_storeu_si128(p.add(16).cast(), _mm512_extracti32x4_epi32::<$l>(s[4 + $c]));
                }};
            }
            lane!(0, 0);
            lane!(0, 1);
            lane!(0, 2);
            lane!(0, 3);
            lane!(1, 0);
            lane!(1, 1);
            lane!(1, 2);
            lane!(1, 3);
            lane!(2, 0);
            lane!(2, 1);
            lane!(2, 2);
            lane!(2, 3);
            lane!(3, 0);
            lane!(3, 1);
            lane!(3, 2);
            lane!(3, 3);
        }
    }

    /// A 16x16 transpose: each block is exactly one `zmm`.
    ///
    /// ```text
    ///     2 unpack phases           four rows of one column per 128-bit lane
    ///     2 shuffle_i32x4 phases    collect the four row groups
    /// ```
    #[inline(always)]
    unsafe fn transpose(src: *const u8, stride: usize, block: &mut [Self; 16]) {
        unsafe {
            let r: [__m512i; 16] = std::array::from_fn(|l| _mm512_loadu_si512(src.add(l * stride).cast()));
            // Phases 1 and 2: lane L of s[4a + c] holds column 4L + c of rows 4a..4a + 4.
            let mut s = [_mm512_setzero_si512(); 16];
            for a in 0..4 {
                let (r0, r1, r2, r3) = (r[4 * a], r[4 * a + 1], r[4 * a + 2], r[4 * a + 3]);
                let lo01 = _mm512_unpacklo_epi32(r0, r1);
                let hi01 = _mm512_unpackhi_epi32(r0, r1);
                let lo23 = _mm512_unpacklo_epi32(r2, r3);
                let hi23 = _mm512_unpackhi_epi32(r2, r3);
                s[4 * a] = _mm512_unpacklo_epi64(lo01, lo23);
                s[4 * a + 1] = _mm512_unpackhi_epi64(lo01, lo23);
                s[4 * a + 2] = _mm512_unpacklo_epi64(hi01, hi23);
                s[4 * a + 3] = _mm512_unpackhi_epi64(hi01, hi23);
            }
            // Phases 3 and 4: word w is lane w / 4 of the four s entries with c = w % 4.
            //
            // The first shuffles broadcast that lane, then 0x88 keeps lanes 0 and 2 of each half.
            macro_rules! word {
                ($w:expr) => {{
                    const L: i32 = ($w / 4) as i32;
                    const C: usize = ($w % 4) as usize;
                    const IMM_L: i32 = L * 0x55;
                    let p = _mm512_shuffle_i32x4::<IMM_L>(s[C], s[4 + C]);
                    let q = _mm512_shuffle_i32x4::<IMM_L>(s[8 + C], s[12 + C]);
                    block[$w] = Self(_mm512_shuffle_i32x4::<0x88>(p, q));
                }};
            }
            word!(0);
            word!(1);
            word!(2);
            word!(3);
            word!(4);
            word!(5);
            word!(6);
            word!(7);
            word!(8);
            word!(9);
            word!(10);
            word!(11);
            word!(12);
            word!(13);
            word!(14);
            word!(15);
        }
    }
}
