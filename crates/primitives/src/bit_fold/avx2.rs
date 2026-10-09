//! The fold of 64 rows at a time, as two halves of 32 rows, one byte per row in a 256-bit register.
//!
//! ```text
//!     1. transpose   64 rows x CHUNKS bytes  ->  two halves x CHUNKS registers, register j = byte j of 32 rows
//!     2. multiply    out byte o += map[j][o] (register j), for each half
//!     3. transpose   24 registers of output bytes  ->  32 F192 values, for each half
//! ```
//!
//! Both transposes are butterflies of byte unpacks, which work within 128-bit lanes.
//!
//! A round on registers `z` and `z | bit` rotates the lane's byte-offset bits 0..4 with the register bit:
//!
//! ```text
//!     offset bit 0  <-  register bit,    offset bits 1..4  <-  offset bits 0..3,    register bit  <-  offset bit 3
//! ```
//!
//! Loading the registers in bit-reversed order makes every transpose land rows in their natural order.

use core::arch::x86_64::*;
use core::fmt::Debug;

#[cfg(target_feature = "gfni")]
use crate::bits::bit_transpose_64bytes;

use super::{BLOCK, F192};

/// Bytes of an F192.
pub const OUT_BYTES: usize = 24;

/// Rows per register.
pub const HALF: usize = 32;

/// How a target applies a GF(2)-linear map of bytes to a register of 32 of them.
pub trait Product {
    /// One map, prepared.
    type Map: Copy + Debug;
    /// One register of input bytes, prepared.
    type Input: Copy;

    /// The maps of eight weights, one per output byte.
    ///
    /// Map `o` takes an input byte `x` to byte `o` of `sum_{s : bit s of x} w_s`.
    fn maps(w: &[F192; 8]) -> [Self::Map; OUT_BYTES];

    fn input(x: __m256i) -> Self::Input;

    fn product(x: Self::Input, m: &Self::Map) -> __m256i;
}

/// One affine instruction per map: the 8x8 bit matrix of the AVX-512 arm, broadcast.
#[cfg(target_feature = "gfni")]
#[derive(Clone, Copy, Debug)]
pub struct Gfni;

#[cfg(target_feature = "gfni")]
impl Product for Gfni {
    type Map = u64;
    type Input = __m256i;

    /// The affine instruction computes result bit `k` as the parity of `x` against matrix byte `7 - k`.
    /// So matrix byte `7 - k` has bit `s` set when bit `k` of byte `o` of `w_s` is set.
    ///
    /// Per coefficient, the bit transpose of the eight weights' words gives word `o`, byte `k`, bit `s` as exactly
    /// that bit: the matrix is the word with its bytes reversed.
    fn maps(w: &[F192; 8]) -> [u64; OUT_BYTES] {
        let mut out = [0u64; OUT_BYTES];
        for (i, out) in out.as_chunks_mut::<8>().0.iter_mut().enumerate() {
            let words = w.map(|w| [w.c0, w.c1, w.c2][i].to_le_bytes());
            let mut t = [0u8; 64];
            bit_transpose_64bytes(words.as_flattened().try_into().expect("eight words"), &mut t);
            for (m, word) in out.iter_mut().zip(t.as_chunks::<8>().0) {
                *m = u64::from_be_bytes(*word);
            }
        }
        out
    }

    #[inline(always)]
    fn input(x: __m256i) -> __m256i {
        x
    }

    #[inline(always)]
    fn product(x: __m256i, m: &u64) -> __m256i {
        // SAFETY: the impl exists only when the crate is built with AVX2 and GFNI; registers only.
        unsafe { _mm256_gf2p8affine_epi64_epi8::<0>(x, _mm256_set1_epi64x(*m as i64)) }
    }
}

/// Two nibble lookups per map: `vpshufb` reads a 16-entry table per 128-bit lane.
///
/// On a GFNI target only the tests use it.
#[cfg_attr(target_feature = "gfni", allow(dead_code))]
#[derive(Clone, Copy, Debug)]
pub struct Shuffle;

impl Product for Shuffle {
    /// Byte `o` of the subset sums of the low nibble's four weights, then of the high nibble's.
    type Map = [u8; 32];
    /// The low nibbles, then the high ones.
    type Input = [__m256i; 2];

    fn maps(w: &[F192; 8]) -> [[u8; 32]; OUT_BYTES] {
        // Row `16 h + v`: the sum of the weights of nibble `h` that `v` selects, padded to a register.
        let mut rows = [[0u8; 32]; 32];
        for (rows, w) in rows.as_chunks_mut::<16>().0.iter_mut().zip(w.as_chunks::<4>().0) {
            let mut sum = [F192::ZERO; 16];
            for v in 1..16usize {
                let low = v.isolate_lowest_one();
                sum[v] = sum[v ^ low] + w[low.trailing_zeros() as usize];
            }
            for (row, s) in rows.iter_mut().zip(sum) {
                row[..OUT_BYTES].copy_from_slice([s.c0, s.c1, s.c2].map(u64::to_le_bytes).as_flattened());
            }
        }
        // SAFETY: the impl exists only when the crate is built with AVX2.
        unsafe { leading_columns(&rows) }
    }

    #[inline(always)]
    fn input(x: __m256i) -> [__m256i; 2] {
        // SAFETY: the impl exists only when the crate is built with AVX2; registers only.
        unsafe {
            let nibble = _mm256_set1_epi8(0x0F);
            [
                _mm256_and_si256(x, nibble),
                _mm256_and_si256(_mm256_srli_epi16::<4>(x), nibble),
            ]
        }
    }

    #[inline(always)]
    fn product(x: [__m256i; 2], m: &[u8; 32]) -> __m256i {
        // SAFETY: the impl exists only when the crate is built with AVX2, and each load reads 16 of the map's bytes.
        unsafe {
            let lo = _mm256_broadcastsi128_si256(_mm_loadu_si128(m.as_ptr().cast()));
            let hi = _mm256_broadcastsi128_si256(_mm_loadu_si128(m.as_ptr().add(16).cast()));
            _mm256_xor_si256(_mm256_shuffle_epi8(lo, x[0]), _mm256_shuffle_epi8(hi, x[1]))
        }
    }
}

/// The product this target prefers.
#[cfg(target_feature = "gfni")]
pub type Best = Gfni;
#[cfg(not(target_feature = "gfni"))]
pub type Best = Shuffle;

/// Add the products of one input register by eight consecutive maps into eight accumulators.
#[inline(always)]
pub fn accumulate8<P: Product>(acc: &mut [__m256i], x: P::Input, maps: &[P::Map]) {
    for (a, m) in acc[..8].iter_mut().zip(&maps[..8]) {
        // SAFETY: the module is compiled only with AVX2 enabled; registers only.
        *a = unsafe { _mm256_xor_si256(*a, P::product(x, m)) };
    }
}

/// `x` with its low `n` bits reversed.
const fn rev(x: usize, n: u32) -> usize {
    x.reverse_bits() >> (usize::BITS - n)
}

/// One unpack round on the registers that differ in `bit`.
#[inline]
#[target_feature(enable = "avx2")]
fn unpack_round(regs: &mut [__m256i], bit: usize) {
    for z in (0..regs.len()).filter(|z| z & bit == 0) {
        let (u, w) = (regs[z], regs[z | bit]);
        regs[z] = _mm256_unpacklo_epi8(u, w);
        regs[z | bit] = _mm256_unpackhi_epi8(u, w);
    }
}

/// Four unpack rounds: register `z` and lane offset `f` trade places, both bit-reversed.
#[inline]
#[target_feature(enable = "avx2")]
fn transpose16(regs: &mut [__m256i; 16]) {
    for bit in [1, 2, 4, 8] {
        unpack_round(regs, bit);
    }
}

/// A register of two 16-byte lanes, `lo` then `hi`, each the first 16 bytes of its slice.
#[inline]
#[target_feature(enable = "avx2")]
fn pair(lo: &[u8], hi: &[u8]) -> __m256i {
    // SAFETY: each half-load reads the 16 bytes the slicing bounds.
    unsafe { _mm256_loadu2_m128i(hi[..16].as_ptr().cast(), lo[..16].as_ptr().cast()) }
}

/// The registers of 64 rows: `out[h][j]` is byte `j` of rows `32h..32h+32`, in order.
///
/// Sixteen registers of 16-byte lanes take one butterfly. A row of at least 16 bytes is whole lanes, rows `p` and
/// `p + 16` sharing a register, so offset bits 0..4 are byte bits and swap with row bits 0..4. An 8-byte row puts
/// rows `p` and `p + 32` in one lane, so offset bits 0..3 are byte bits and offset bit 3 is row bit 5, the half.
#[inline]
#[target_feature(enable = "avx2")]
fn transpose_rows<const CHUNKS: usize>(rows: &[[u8; CHUNKS]; BLOCK]) -> [[__m256i; CHUNKS]; 2] {
    let mut out = [[_mm256_setzero_si256(); CHUNKS]; 2];
    if CHUNKS == 8 {
        let bytes = rows.as_flattened();
        let mut regs = [_mm256_setzero_si256(); 16];
        for p in (0..16).step_by(2) {
            // Lane l, qword q: row p + 16 l + 32 q, then the same for row p + 1.
            let x = pair(&bytes[8 * p..], &bytes[8 * (p + 16)..]);
            let y = pair(&bytes[8 * (p + 32)..], &bytes[8 * (p + 48)..]);
            regs[rev(p, 4)] = _mm256_unpacklo_epi64(x, y);
            regs[rev(p + 1, 4)] = _mm256_unpackhi_epi64(x, y);
        }
        transpose16(&mut regs);
        for (z, r) in regs.into_iter().enumerate() {
            out[z & 1][rev(z >> 1, 3)] = r;
        }
    } else {
        for g in 0..CHUNKS / 16 {
            for (h, out) in out.iter_mut().enumerate() {
                let mut regs: [__m256i; 16] = std::array::from_fn(|z| {
                    let p = 32 * h + rev(z, 4);
                    pair(&rows[p][16 * g..], &rows[p + 16][16 * g..])
                });
                transpose16(&mut regs);
                for (z, r) in regs.into_iter().enumerate() {
                    out[16 * g + rev(z, 4)] = r;
                }
            }
        }
    }
    out
}

/// Byte `j` of 32 rows, in order, for each of the rows' first 24 bytes: the wide rows of [`transpose_rows`].
#[cfg_attr(target_feature = "gfni", allow(dead_code))]
#[inline]
#[target_feature(enable = "avx2")]
fn leading_columns(rows: &[[u8; 32]; 32]) -> [[u8; 32]; OUT_BYTES] {
    let mut out = [[0u8; 32]; OUT_BYTES];
    for g in 0..2 {
        let mut regs: [__m256i; 16] =
            std::array::from_fn(|z| pair(&rows[rev(z, 4)][16 * g..], &rows[rev(z, 4) + 16][16 * g..]));
        transpose16(&mut regs);
        for (z, r) in regs.into_iter().enumerate() {
            if let Some(out) = out.get_mut(16 * g + rev(z, 4)) {
                // SAFETY: the store fills one 32-byte column.
                unsafe { _mm256_storeu_si256(out.as_mut_ptr().cast(), r) };
            }
        }
    }
    out
}

/// Store 24 registers of output bytes, register `o` holding byte `o` of 32 values, as those 32 values.
///
/// # Safety
///
/// Requires AVX2, which the target enables wherever this is compiled.
#[inline]
#[target_feature(enable = "avx2")]
pub fn store_f192(acc: &[__m256i; OUT_BYTES], out: &mut [F192; HALF]) {
    // Per coefficient, register z holding byte rev(z): three rounds leave lane l of register z with the
    // coefficient of rows 2 rev(z) + 16 l and the next.
    let [c0, c1, c2]: [[__m256i; 8]; 3] = std::array::from_fn(|i| {
        let mut regs = std::array::from_fn(|z| acc[8 * i + rev(z, 3)]);
        for bit in [1, 2, 4] {
            unpack_round(&mut regs, bit);
        }
        regs
    });
    let dst = out.as_mut_ptr().cast::<u8>();
    for z in 0..8 {
        // Two rows per lane: their six qwords in three 16-byte stores.
        let (lo, hi) = (_mm256_unpacklo_epi64(c0[z], c1[z]), _mm256_unpackhi_epi64(c0[z], c1[z]));
        let parts = [lo, _mm256_unpacklo_epi64(c2[z], hi), _mm256_unpackhi_epi64(hi, c2[z])];
        for (l, row) in [2 * rev(z, 3), 2 * rev(z, 3) + 16].into_iter().enumerate() {
            for (k, part) in parts.iter().enumerate() {
                let half = if l == 0 {
                    _mm256_castsi256_si128(*part)
                } else {
                    _mm256_extracti128_si256::<1>(*part)
                };
                // SAFETY: rows `row` and `row + 1` are the 48 bytes at `24 row`, inside the 32 values.
                unsafe { _mm_storeu_si128(dst.add(24 * row + 16 * k).cast(), half) };
            }
        }
    }
}

/// The maps of every input byte.
#[derive(Clone, Debug)]
pub struct Fold<P: Product> {
    /// `maps[24 j + o]` maps input byte `j` to output byte `o`.
    maps: Vec<P::Map>,
}

pub(super) type Imp = Fold<Best>;

/// A block of values byte-sliced: `[h][j]` is byte `j` of values `32h..32h+32`.
pub type Sliced = [[__m256i; OUT_BYTES]; 2];

impl<P: Product> Fold<P> {
    pub fn new(weights: &[F192]) -> Self {
        let bytes: &[[F192; 8]] = weights.as_chunks().0;
        Self {
            maps: bytes.iter().flat_map(P::maps).collect(),
        }
    }

    #[inline]
    pub fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK]) {
        // A short block folds from a zero-padded copy.
        if rows.len() < BLOCK {
            let mut padded = [[0u8; CHUNKS]; BLOCK];
            padded[..rows.len()].copy_from_slice(rows);
            // SAFETY: the module is compiled only with AVX2 enabled.
            return unsafe { self.fold_full::<CHUNKS>(&padded, out) };
        }
        let rows: &[[u8; CHUNKS]; BLOCK] = rows.try_into().expect("a full block");
        // SAFETY: the module is compiled only with AVX2 enabled.
        unsafe { self.fold_full::<CHUNKS>(rows, out) };
    }

    #[inline]
    #[target_feature(enable = "avx2")]
    fn fold_full<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK], out: &mut [F192; BLOCK]) {
        let regs = transpose_rows::<CHUNKS>(rows);
        for (regs, out) in regs.iter().zip(out.as_chunks_mut::<HALF>().0) {
            self.fold_half(regs, out);
        }
    }

    /// The values of 32 rows, from one register per input byte.
    #[inline]
    #[target_feature(enable = "avx2")]
    fn fold_half(&self, regs: &[__m256i], out: &mut [F192; HALF]) {
        let maps: &[[P::Map; OUT_BYTES]] = self.maps.as_chunks().0;
        // Eight output bytes at a time keep their accumulators in registers.
        let mut acc = [_mm256_setzero_si256(); OUT_BYTES];
        for (g, acc) in acc.as_chunks_mut::<8>().0.iter_mut().enumerate() {
            for (&x, m) in regs.iter().zip(maps) {
                accumulate8::<P>(acc, P::input(x), &m[8 * g..]);
            }
        }
        store_f192(&acc, out);
    }

    /// The maps of an F192's 24 bytes.
    pub fn new_f192(weights: &[F192]) -> Self {
        Self::new(weights)
    }

    /// A block of values, each padded to 32 bytes and transposed like rows.
    pub fn slice(xs: &[F192; BLOCK]) -> Sliced {
        let rows: [[u8; 32]; BLOCK] = std::array::from_fn(|i| {
            let mut row = [0u8; 32];
            row[..OUT_BYTES].copy_from_slice([xs[i].c0, xs[i].c1, xs[i].c2].map(u64::to_le_bytes).as_flattened());
            row
        });
        // SAFETY: the module is compiled only with AVX2 enabled.
        let regs = unsafe { transpose_rows::<32>(&rows) };
        regs.map(|r| std::array::from_fn(|j| r[j]))
    }

    /// Add the image of each of `xs` to `out`.
    #[inline]
    pub fn apply_add_f192(&self, xs: &[F192; BLOCK], out: &mut [F192]) {
        self.apply_sliced_add(&Self::slice(xs), out);
    }

    /// Add the image of each value of a sliced block to `out`.
    #[inline]
    pub fn apply_sliced_add(&self, xs: &Sliced, out: &mut [F192]) {
        for (regs, out) in xs.iter().zip(out.chunks_mut(HALF)) {
            let mut image = [F192::ZERO; HALF];
            // SAFETY: the module is compiled only with AVX2 enabled.
            unsafe { self.fold_half(regs, &mut image) };
            for (o, v) in out.iter_mut().zip(image) {
                *o += v;
            }
        }
    }
}
