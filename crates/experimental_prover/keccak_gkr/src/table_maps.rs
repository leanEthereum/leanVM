//! The table pass's rows by byte maps (x86-64 with AVX2): the same rows as embedding each
//! position's packs, weighting them by the folded challenges with carry-less products and reducing.
//!
//! A position's value in a group, `reduce(sum over packs q of embed(pack q) * fold[q])`, is
//! GF(2)-linear in the group's 256 instance bits, so it is a sum of one 8x8 bit matrix per (input
//! byte, output byte): byte `t` of the group's 32 bytes holds bits `8 (t % 2) ..` of pack `t / 2`,
//! and each of its bits maps to the reduced product of one unit embedding by that pack's weight.
//! A block is byte-transposed a register of positions at a time (register `b` = byte `b` of the
//! register's positions), each group then costs `32 * 16` byte maps per register, and the 16
//! output bytes are transposed back to the row's words. A byte map is one GFNI affine product, 512
//! bits wide with AVX-512BW, or without GFNI two `vpshufb` nibble lookups.
//!
//! The scheme is the table fill of hashmancer-keccak's GFNI kernels.

use core::arch::x86_64::*;

use primitives::field::gf2_64::mul_wide;
use verifier::keccak::BITS;

use crate::kernels::GROUP;
use crate::power::PowerField;
use crate::rmfe::RMFE;
use crate::witness::BLOCK_WORDS;

/// Bytes of a group of a position (16 packs of 16 bits), and of a reduced value.
const GROUP_BYTES: usize = 32;
const VALUE_BYTES: usize = 16;

/// The byte maps of one layer's fold weights: `matrices[t][o]` sends byte `t` of a group to byte `o`
/// of its value.
pub struct RowMaps {
    matrices: [[Matrix; VALUE_BYTES]; GROUP_BYTES],
}

impl RowMaps {
    /// From the fold weights `fold[k][q]` (word `k` of pack `q`'s weight, in the power basis).
    pub fn new(field: &PowerField, fold: &[[u64; GROUP]; 2]) -> Self {
        // The value of bit `i` of pack `q` alone, image `16 q + i`: its unit embedding times the pack's
        // weight, reduced, a row of three-word products laid out by word as the carry-less path's.
        const IMAGES: usize = 16 * GROUP;
        let mut wide = vec![0u64; 3 * IMAGES];
        for q in 0..GROUP {
            for (i, &e) in RMFE.emb.iter().enumerate() {
                for (k, w) in fold.iter().enumerate() {
                    let x = mul_wide(u64::from(e), w[q]);
                    wide[k * IMAGES + 16 * q + i] ^= x as u64;
                    wide[(k + 1) * IMAGES + 16 * q + i] ^= (x >> 64) as u64;
                }
            }
        }
        let mut images = vec![0u64; 2 * IMAGES];
        field.reduce_row(&mut images, &wide, IMAGES);
        let bit = |image: usize, n: usize| (images[(n / 64) * IMAGES + image] >> (n % 64)) as u8 & 1;
        // An affine byte map reads output bit `k` off matrix byte `7 - k`: its bit `c` is bit `8 o + k`
        // of the image of input bit `c`.
        let matrices = std::array::from_fn(|t| {
            std::array::from_fn(|o| {
                (0..8).fold(0u64, |m, k| {
                    let row = (0..8).fold(0u8, |row, c| row | bit(16 * (t / 2) + 8 * (t % 2) + c, 8 * o + k) << c);
                    m | u64::from(row) << (8 * (7 - k))
                })
            })
        });
        Self {
            matrices: matrices.map(|m| m.map(matrix)),
        }
    }
}

/// The three in-lane unpack rounds from eight byte planes `$a` (plane `b` byte `n` of a 128-bit lane
/// `L` = byte `b` of position `16 L + n`) to the positions' words: register `m` lane `L` holds positions
/// `16 L + 2 m` and `16 L + 2 m + 1`.
macro_rules! interleave_planes {
    ($a:expr, $lo8:ident, $hi8:ident, $lo16:ident, $hi16:ident, $lo32:ident, $hi32:ident) => {{
        let a = $a;
        // Per lane: bytes, then 16-bit pairs, then 32-bit quads interleave.
        let u: [_; 8] = std::array::from_fn(|i| {
            let (x, y) = (a[2 * (i / 2)], a[2 * (i / 2) + 1]);
            if i % 2 == 0 { $lo8(x, y) } else { $hi8(x, y) }
        });
        // u[2 m + s]: lane L, 16-bit element e = bytes of planes 2m, 2m + 1 for position 16 L + 8 s + e.
        let v: [_; 8] = std::array::from_fn(|i| {
            let (s, half) = (i / 4, i % 4 / 2);
            let (x, y) = if i % 2 == 0 {
                (u[s], u[2 + s])
            } else {
                (u[4 + s], u[6 + s])
            };
            if half == 0 { $lo16(x, y) } else { $hi16(x, y) }
        });
        // v[4 s + 2 h + c]: lane L, 32-bit element e = planes 4c .. 4c + 4 of position 16 L + 8 s + 4 h + e.
        let w: [_; 8] = std::array::from_fn(|i| {
            let (j, hi) = (i / 2, i % 2);
            let (s, h) = (j / 2, j % 2);
            let (x, y) = (v[4 * s + 2 * h], v[4 * s + 2 * h + 1]);
            if hi == 0 { $lo32(x, y) } else { $hi32(x, y) }
        });
        w
    }};
}
#[cfg(target_feature = "gfni")]
pub(crate) use interleave_planes;

cfg_select! {
    all(target_feature = "avx512f", target_feature = "avx512bw", target_feature = "gfni") => {
        /// Positions per register.
        const REGISTER_POSITIONS: usize = 64;

        /// A matrix, broadcast by the affine product's memory operand.
        type Matrix = u64;

        #[inline]
        fn matrix(m: u64) -> Matrix {
            m
        }

        impl RowMaps {
            /// The rows of a block's first `halves` groups: row `h`, word `k` of position `j` at
            /// `rows[h * 2 BITS + k * BITS + j]`.
            pub fn rows(&self, block: &[u64], rows: &mut [u64], halves: usize) {
                assert!(block.len() >= BITS * BLOCK_WORDS && halves <= 2 && rows.len() >= halves * 2 * BITS);
                // SAFETY: AVX-512F/BW and GFNI are enabled at compile time (module cfg); every load reads
                // positions inside `block` and every store writes words inside `rows` (asserted).
                unsafe {
                    for g in 0..BITS / REGISTER_POSITIONS {
                        let y = transpose_position_bytes(block.as_ptr().add(REGISTER_POSITIONS * g * BLOCK_WORDS));
                        for h in 0..halves {
                            let acc = self.accumulate(&y[GROUP_BYTES * h..][..GROUP_BYTES]);
                            for k in 0..2 {
                                let words = byte_planes_to_words(acc[8 * k..][..8].try_into().unwrap());
                                let dst = rows.as_mut_ptr().add(h * 2 * BITS + k * BITS + REGISTER_POSITIONS * g);
                                for (r, w) in words.iter().enumerate() {
                                    _mm512_storeu_si512(dst.add(8 * r).cast(), *w);
                                }
                            }
                        }
                    }
                }
            }

            /// Output byte `o` of the 64 positions: the sum over input bytes `t` of `matrices[t][o]` applied to `y[t]`.
            #[inline]
            #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "gfni")]
            fn accumulate(&self, y: &[__m512i]) -> [__m512i; VALUE_BYTES] {
                let mut acc = [_mm512_setzero_si512(); VALUE_BYTES];
                for t in (0..GROUP_BYTES).step_by(2) {
                    let (x0, x1, m0, m1) = (y[t], y[t + 1], &self.matrices[t], &self.matrices[t + 1]);
                    for (o, a) in acc.iter_mut().enumerate() {
                        let g0 = _mm512_gf2p8affine_epi64_epi8::<0>(x0, _mm512_set1_epi64(m0[o] as i64));
                        let g1 = _mm512_gf2p8affine_epi64_epi8::<0>(x1, _mm512_set1_epi64(m1[o] as i64));
                        *a = _mm512_ternarylogic_epi64::<0x96>(*a, g0, g1);
                    }
                }
                acc
            }
        }

        /// 4x4 transpose of 128-bit lanes: `out[l]` lane `g` = `x[g]` lane `l`.
        #[inline]
        #[target_feature(enable = "avx512f")]
        fn transpose_lanes(x: [__m512i; 4]) -> [__m512i; 4] {
            let t0 = _mm512_shuffle_i64x2::<0b01_00_01_00>(x[0], x[1]);
            let t1 = _mm512_shuffle_i64x2::<0b11_10_11_10>(x[0], x[1]);
            let t2 = _mm512_shuffle_i64x2::<0b01_00_01_00>(x[2], x[3]);
            let t3 = _mm512_shuffle_i64x2::<0b11_10_11_10>(x[2], x[3]);
            [
                _mm512_shuffle_i64x2::<0b10_00_10_00>(t0, t2),
                _mm512_shuffle_i64x2::<0b11_01_11_01>(t0, t2),
                _mm512_shuffle_i64x2::<0b10_00_10_00>(t1, t3),
                _mm512_shuffle_i64x2::<0b11_01_11_01>(t1, t3),
            ]
        }

        /// The 64 bytes of 64 consecutive positions (eight words each, at `p`), transposed: register `b`
        /// byte `n` is byte `b` of position `n`.
        ///
        /// # Safety
        /// `p` is valid for reading 64 positions; AVX-512F/BW.
        #[inline]
        #[target_feature(enable = "avx512f", enable = "avx512bw")]
        unsafe fn transpose_position_bytes(p: *const u64) -> [__m512i; 64] {
            let mut y = [[_mm512_setzero_si512(); 16]; 4];
            for (q, yq) in y.iter_mut().enumerate() {
                for (n, v) in yq.iter_mut().enumerate() {
                    // SAFETY: position `16 q + n` lies inside the caller's 64.
                    *v = unsafe { _mm512_loadu_si512(p.add(BLOCK_WORDS * (16 * q + n)).cast()) };
                }
                // yq[k] lane l byte n = byte 16 l + k of position 16 q + n.
                primitives::bits::transpose_bytes16x16_per_lane512(yq);
            }
            let mut out = [_mm512_setzero_si512(); 64];
            for k in 0..16 {
                // out[16 l + k] lane q = y[q][k] lane l.
                for (l, v) in transpose_lanes([y[0][k], y[1][k], y[2][k], y[3][k]])
                    .into_iter()
                    .enumerate()
                {
                    out[16 * l + k] = v;
                }
            }
            out
        }

        /// Eight byte planes of 64 positions (plane `b` byte `n` = byte `b` of position `n`) as the
        /// positions' words: register `r` holds positions `8 r .. 8 r + 8`.
        #[inline]
        #[target_feature(enable = "avx512f", enable = "avx512bw")]
        fn byte_planes_to_words(a: &[__m512i; 8]) -> [__m512i; 8] {
            let w = interleave_planes!(
                a,
                _mm512_unpacklo_epi8,
                _mm512_unpackhi_epi8,
                _mm512_unpacklo_epi16,
                _mm512_unpackhi_epi16,
                _mm512_unpacklo_epi32,
                _mm512_unpackhi_epi32
            );
            let lo = transpose_lanes([w[0], w[1], w[2], w[3]]);
            let hi = transpose_lanes([w[4], w[5], w[6], w[7]]);
            // lo[L] = positions 16 L .. 16 L + 8, hi[L] = 16 L + 8 .. 16 L + 16.
            [lo[0], hi[0], lo[1], hi[1], lo[2], hi[2], lo[3], hi[3]]
        }
    }
    _ => {
        /// Positions per register.
        const REGISTER_POSITIONS: usize = 32;

        cfg_select! {
            target_feature = "gfni" => {
                /// A matrix in every lane, so that the affine product reads it from memory.
                type Matrix = __m256i;

                fn matrix(m: u64) -> Matrix {
                    // SAFETY: AVX is enabled at compile time (module cfg).
                    unsafe { _mm256_set1_epi64x(m as i64) }
                }

                /// An input register as [`product`] reads it.
                type Input = __m256i;

                #[inline(always)]
                fn input(x: __m256i) -> Input {
                    x
                }

                #[inline(always)]
                fn product(x: Input, m: &Matrix) -> __m256i {
                    // SAFETY: GFNI and AVX are enabled at compile time (module cfg); registers only.
                    unsafe { _mm256_gf2p8affine_epi64_epi8::<0>(x, *m) }
                }
            }
            _ => {
                /// A matrix as two `vpshufb` tables: its images of the low nibbles, then of the high ones.
                type Matrix = [u8; 32];

                fn matrix(m: u64) -> Matrix {
                    // Output bit `k` is the parity of the input against matrix byte `7 - k`.
                    let image = |x: u8| (0..8).fold(0u8, |r, k| r | (((m >> (8 * (7 - k))) as u8 & x).count_ones() as u8 & 1) << k);
                    std::array::from_fn(|i| image(((i % 16) as u8) << (4 * (i / 16))))
                }

                /// An input register as [`product`] reads it: its low nibbles, then its high ones.
                type Input = [__m256i; 2];

                #[inline(always)]
                fn input(x: __m256i) -> Input {
                    // SAFETY: AVX2 is enabled at compile time (module cfg); registers only.
                    unsafe {
                        let nibble = _mm256_set1_epi8(0x0F);
                        [_mm256_and_si256(x, nibble), _mm256_and_si256(_mm256_srli_epi16::<4>(x), nibble)]
                    }
                }

                #[inline(always)]
                fn product(x: Input, m: &Matrix) -> __m256i {
                    // SAFETY: AVX2 is enabled at compile time (module cfg), and each load reads 16 of the
                    // matrix's bytes.
                    unsafe {
                        let lo = _mm256_broadcastsi128_si256(_mm_loadu_si128(m.as_ptr().cast()));
                        let hi = _mm256_broadcastsi128_si256(_mm_loadu_si128(m.as_ptr().add(16).cast()));
                        _mm256_xor_si256(_mm256_shuffle_epi8(lo, x[0]), _mm256_shuffle_epi8(hi, x[1]))
                    }
                }
            }
        }

        impl RowMaps {
            /// The rows of a block's first `halves` groups: row `h`, word `k` of position `j` at
            /// `rows[h * 2 BITS + k * BITS + j]`.
            pub fn rows(&self, block: &[u64], rows: &mut [u64], halves: usize) {
                assert!(block.len() >= BITS * BLOCK_WORDS && halves <= 2 && rows.len() >= halves * 2 * BITS);
                // SAFETY: AVX2 is enabled at compile time (module cfg); every load reads
                // positions inside `block` and every store writes words inside `rows` (asserted).
                unsafe {
                    let mut y = [_mm256_setzero_si256(); GROUP_BYTES];
                    for g in 0..BITS / REGISTER_POSITIONS {
                        for h in 0..halves {
                            let at = BLOCK_WORDS * REGISTER_POSITIONS * g + GROUP_BYTES / 8 * h;
                            transpose_group_bytes(block.as_ptr().add(at), &mut y);
                            for k in 0..2 {
                                let words = byte_planes_to_words(&self.accumulate(&y, k));
                                let dst = rows.as_mut_ptr().add(h * 2 * BITS + k * BITS + REGISTER_POSITIONS * g);
                                for (r, w) in words.iter().enumerate() {
                                    _mm256_storeu_si256(dst.add(4 * r).cast(), *w);
                                }
                            }
                        }
                    }
                }
            }

            /// Output bytes `8 k .. 8 k + 8` of the 32 positions, word `k` of their values: the sums over
            /// input bytes `t` of `matrices[t][o]` applied to `y[t]`. Eight outputs at a time keep the sums
            /// in registers.
            #[inline]
            #[target_feature(enable = "avx2")]
            fn accumulate(&self, y: &[__m256i; GROUP_BYTES], k: usize) -> [__m256i; 8] {
                let mut acc = [_mm256_setzero_si256(); 8];
                for (&x, m) in y.iter().zip(&self.matrices) {
                    let x = input(x);
                    for (a, m) in acc.iter_mut().zip(&m[8 * k..][..8]) {
                        *a = _mm256_xor_si256(*a, product(x, m));
                    }
                }
                acc
            }
        }

        /// The 32 bytes of a group of 32 consecutive positions (eight words apart, from `p`), transposed:
        /// `y[t]` byte `n` is byte `t` of the group of position `n`.
        ///
        /// # Safety
        /// `p` is valid for reading the 32 positions' groups; AVX2.
        #[inline]
        #[target_feature(enable = "avx2")]
        unsafe fn transpose_group_bytes(p: *const u64, y: &mut [__m256i; GROUP_BYTES]) {
            for (l, y) in y.as_chunks_mut::<16>().0.iter_mut().enumerate() {
                // Register `n`: bytes `16 l ..` of positions `n` and `16 + n`.
                *y = std::array::from_fn(|n| {
                    // SAFETY: positions `n` and `16 + n` lie inside the caller's 32.
                    unsafe {
                        _mm256_loadu2_m128i(
                            p.add(BLOCK_WORDS * (16 + n) + 2 * l).cast(),
                            p.add(BLOCK_WORDS * n + 2 * l).cast(),
                        )
                    }
                });
                // y[k] lane i byte n = byte 16 l + k of position 16 i + n.
                primitives::bits::transpose_bytes16x16_per_lane256(y);
            }
        }

        /// Eight byte planes of 32 positions (plane `b` byte `n` = byte `b` of position `n`) as the
        /// positions' words: register `r` holds positions `4 r .. 4 r + 4`.
        #[inline]
        #[target_feature(enable = "avx2")]
        fn byte_planes_to_words(a: &[__m256i; 8]) -> [__m256i; 8] {
            let w = interleave_planes!(
                a,
                _mm256_unpacklo_epi8,
                _mm256_unpackhi_epi8,
                _mm256_unpacklo_epi16,
                _mm256_unpackhi_epi16,
                _mm256_unpacklo_epi32,
                _mm256_unpackhi_epi32
            );
            std::array::from_fn(|r| {
                let (x, y) = (w[2 * (r % 4)], w[2 * (r % 4) + 1]);
                if r < 4 {
                    _mm256_permute2x128_si256::<0x20>(x, y)
                } else {
                    _mm256_permute2x128_si256::<0x31>(x, y)
                }
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use primitives::test_rng::Rng;

    use super::*;
    use crate::basis::carry;
    use crate::kernels::{embed, fold_groups};
    use crate::power::Element;
    use crate::witness::words;

    /// The rows the per-position path builds: embeddings weighted by carry-less products, reduced.
    #[test]
    fn rows_match_the_carry_less_path() {
        let mut rng = Rng::new(0x7AB1E);
        let field = PowerField::new(rng.ext()).expect("a generator");
        // The fold weights: field elements in the power basis, by word.
        let elems: Vec<Element> = (0..GROUP).map(|_| field.to_poly(rng.ext())).collect();
        let fold: [[u64; GROUP]; 2] = std::array::from_fn(|k| std::array::from_fn(|q| elems[q][k]));
        let block: Vec<u64> = (0..BITS * BLOCK_WORDS).map(|_| rng.next_u64()).collect();
        let mut want = vec![0u64; 2 * 2 * BITS];
        let mut wide = vec![0u64; 2 * 3 * BITS];
        for j in 0..BITS {
            let sums = fold_groups(&embed(words(&block, j)), &fold);
            for (h, sum) in sums.iter().enumerate() {
                let sum: [u64; 3] = carry(sum);
                for (k, &w) in sum.iter().enumerate() {
                    wide[h * 3 * BITS + k * BITS + j] = w;
                }
            }
        }
        for h in 0..2 {
            field.reduce_row(
                &mut want[h * 2 * BITS..][..2 * BITS],
                &wide[h * 3 * BITS..][..3 * BITS],
                BITS,
            );
        }
        for halves in [2, 1] {
            let mut got = vec![0u64; 2 * 2 * BITS];
            RowMaps::new(&field, &fold).rows(&block, &mut got, halves);
            assert_eq!(got[..halves * 2 * BITS], want[..halves * 2 * BITS], "{halves} halves");
        }
    }
}
