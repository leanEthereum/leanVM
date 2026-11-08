//! The table pass's rows by GFNI (x86-64 with AVX-512BW and GFNI): the same rows as embedding each
//! position's packs, weighting them by the folded challenges with carry-less products and reducing.
//!
//! A position's value in a group, `reduce(sum over packs q of embed(pack q) * fold[q])`, is
//! GF(2)-linear in the group's 256 instance bits, so it is a sum of one 8x8 bit matrix per (input
//! byte, output byte): byte `t` of the group's 32 bytes holds bits `8 (t % 2) ..` of pack `t / 2`,
//! and each of its bits maps to the reduced product of one unit embedding by that pack's weight.
//! A block is byte-transposed 64 positions at a time (register `b` = byte `b` of the 64 positions),
//! each group then costs `32 * 24` affine products per 64 positions, and the 24 output bytes are
//! transposed back to the row's words.
//!
//! The scheme is the table fill of hashmancer-keccak's GFNI kernels.

use core::arch::x86_64::*;

use primitives::field::gf2_64::mul_wide;

use crate::keccak::BITS;
use crate::kernels::GROUP;
use crate::power::PowerField;
use crate::rmfe::RMFE;
use crate::witness::BLOCK_WORDS;

/// Bytes of a group of a position (16 packs of 16 bits), and of a reduced value.
const GROUP_BYTES: usize = 32;
const _: () = assert!(
    GROUP * crate::rmfe::PACK / 8 == GROUP_BYTES,
    "the group's bytes hold its packs' bits"
);
const VALUE_BYTES: usize = 24;
/// Positions per register.
const REGISTER_POSITIONS: usize = 64;

/// The affine maps of one layer's fold weights: `matrices[t][o]` sends byte `t` of a group to byte `o`
/// of its value.
pub struct RowMaps {
    matrices: [[u64; VALUE_BYTES]; GROUP_BYTES],
}

impl RowMaps {
    /// From the fold weights `fold[k][q]` (word `k` of pack `q`'s weight, in the power basis).
    pub fn new(field: &PowerField, fold: &[[u64; GROUP]; 3]) -> Self {
        // The value of bit `i` of pack `q` alone, image `16 q + i`: its unit embedding times the pack's
        // weight, reduced, a row of four-word products laid out by word as the carry-less path's.
        const IMAGES: usize = 16 * GROUP;
        let mut wide = vec![0u64; 4 * IMAGES];
        for q in 0..GROUP {
            for (i, &e) in RMFE.emb.iter().enumerate() {
                for (k, w) in fold.iter().enumerate() {
                    let x = mul_wide(u64::from(e), w[q]);
                    wide[k * IMAGES + 16 * q + i] ^= x as u64;
                    wide[(k + 1) * IMAGES + 16 * q + i] ^= (x >> 64) as u64;
                }
            }
        }
        let mut images = vec![0u64; 3 * IMAGES];
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
        Self { matrices }
    }

    /// The rows of a block's first `halves` groups: row `h`, word `k` of position `j` at
    /// `rows[h * 3 BITS + k * BITS + j]`.
    pub fn rows(&self, block: &[u64], rows: &mut [u64], halves: usize) {
        assert!(block.len() >= BITS * BLOCK_WORDS && halves <= 2 && rows.len() >= halves * 3 * BITS);
        // SAFETY: AVX-512F/BW and GFNI are enabled at compile time (module cfg); every load reads
        // positions inside `block` and every store writes words inside `rows` (asserted).
        unsafe {
            for g in 0..BITS / REGISTER_POSITIONS {
                let y = transpose_position_bytes(block.as_ptr().add(REGISTER_POSITIONS * g * BLOCK_WORDS));
                for h in 0..halves {
                    let acc = self.accumulate(&y[GROUP_BYTES * h..][..GROUP_BYTES]);
                    for k in 0..3 {
                        let words = byte_planes_to_words(acc[8 * k..][..8].try_into().unwrap());
                        let dst = rows.as_mut_ptr().add(h * 3 * BITS + k * BITS + REGISTER_POSITIONS * g);
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
    // Per 128-bit lane `L` (positions 16 L ..): bytes, then 16-bit pairs, then 32-bit quads interleave.
    let u: [__m512i; 8] = std::array::from_fn(|i| {
        let (x, y) = (a[2 * (i / 2)], a[2 * (i / 2) + 1]);
        if i % 2 == 0 {
            _mm512_unpacklo_epi8(x, y)
        } else {
            _mm512_unpackhi_epi8(x, y)
        }
    });
    // u[2 m + s]: lane L, 16-bit element e = bytes of planes 2m, 2m + 1 for position 16 L + 8 s + e.
    let v: [__m512i; 8] = std::array::from_fn(|i| {
        let (s, half) = (i / 4, i % 4 / 2);
        let (x, y) = (u[s], u[2 + s]);
        let (x, y) = if i % 2 == 0 { (x, y) } else { (u[4 + s], u[6 + s]) };
        if half == 0 {
            _mm512_unpacklo_epi16(x, y)
        } else {
            _mm512_unpackhi_epi16(x, y)
        }
    });
    // v[4 s + 2 h + c]: lane L, 32-bit element e = planes 4c .. 4c + 4 of position 16 L + 8 s + 4 h + e.
    let w: [__m512i; 8] = std::array::from_fn(|i| {
        let (j, hi) = (i / 2, i % 2);
        let (s, h) = (j / 2, j % 2);
        let (x, y) = (v[4 * s + 2 * h], v[4 * s + 2 * h + 1]);
        if hi == 0 {
            _mm512_unpacklo_epi32(x, y)
        } else {
            _mm512_unpackhi_epi32(x, y)
        }
    });
    // w[2 j + e2]: lane L, qword d = position 16 L + 4 j + 2 e2 + d, all eight planes: lane L of
    // w[m] holds positions 16 L + 2 m, 16 L + 2 m + 1.
    let lo = transpose_lanes([w[0], w[1], w[2], w[3]]);
    let hi = transpose_lanes([w[4], w[5], w[6], w[7]]);
    // lo[L] = positions 16 L .. 16 L + 8, hi[L] = 16 L + 8 .. 16 L + 16.
    [lo[0], hi[0], lo[1], hi[1], lo[2], hi[2], lo[3], hi[3]]
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
        {
            let field = PowerField::new(rng.ext()).expect("a generator");
            // The fold weights: field elements in the power basis, by word.
            let elems: Vec<Element> = (0..GROUP).map(|_| field.to_poly(rng.ext())).collect();
            let fold: [[u64; GROUP]; 3] = std::array::from_fn(|k| std::array::from_fn(|q| elems[q][k]));
            let block: Vec<u64> = (0..BITS * BLOCK_WORDS).map(|_| rng.next_u64()).collect();
            let mut want = vec![0u64; 2 * 3 * BITS];
            let mut wide = vec![0u64; 2 * 4 * BITS];
            for j in 0..BITS {
                let sums = fold_groups(&embed(words(&block, j)), &fold);
                for (h, sum) in sums.iter().enumerate() {
                    let sum: [u64; 4] = carry(sum);
                    for (k, &w) in sum.iter().enumerate() {
                        wide[h * 4 * BITS + k * BITS + j] = w;
                    }
                }
            }
            for h in 0..2 {
                field.reduce_row(
                    &mut want[h * 3 * BITS..][..3 * BITS],
                    &wide[h * 4 * BITS..][..4 * BITS],
                    BITS,
                );
            }
            for halves in [2, 1] {
                let mut got = vec![0u64; 2 * 3 * BITS];
                RowMaps::new(&field, &fold).rows(&block, &mut got, halves);
                assert_eq!(got[..halves * 3 * BITS], want[..halves * 3 * BITS], "{halves} halves");
            }
        }
    }
}
