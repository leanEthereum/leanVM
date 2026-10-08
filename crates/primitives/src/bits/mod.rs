// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Bit transposes.

#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use core::arch::x86_64::*;

/// Transpose the eight 8x8 bit matrices of a 64-byte block, gathered across rows.
///
/// ```text
///     output[b * 8 + t] bit x  =  input[x * 8 + b] bit t
/// ```
///
/// So byte column `b` of the eight input rows becomes output row `b`, bit-transposed.
///
/// - AVX-512 VBMI with GFNI: one byte permute and one affine map.
/// - AVX2 with GFNI: a byte gather in shuffles and unpacks, then one affine map.
/// - AVX2: the same gather, then three masked-swap rounds.
/// - aarch64: a table lookup, then three masked-swap rounds.
/// - Elsewhere: the same rounds on a gathered word per column.
#[inline]
pub fn bit_transpose_64bytes(input: &[u8; 64], output: &mut [u8; 64]) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
    // SAFETY: the features are enabled at compile time.
    unsafe {
        bit_transpose_64bytes_gfni(input, output);
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "gfni",
        not(target_feature = "avx512vbmi")
    ))]
    // SAFETY: the features are enabled at compile time.
    unsafe {
        bit_transpose_64bytes_gfni_avx2(input, output);
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "gfni")))]
    // SAFETY: the feature is enabled at compile time.
    unsafe {
        bit_transpose_64bytes_avx2(input, output);
    }
    #[cfg(target_arch = "aarch64")]
    // SAFETY: aarch64 always has NEON.
    unsafe {
        bit_transpose_64bytes_neon(input, output);
    }
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"),
        all(target_arch = "x86_64", target_feature = "avx2"),
        target_arch = "aarch64"
    )))]
    bit_transpose_64bytes_portable(input, output);
}

/// Transpose the 64x64 bit matrix whose word `r` is row `r`, in place.
///
/// ```text
///     after: m[c] bit r  =  before: m[r] bit c
/// ```
///
/// Six rounds of masked swaps (Hacker's Delight, section 7-3), halving the block each round.
/// Round `j` swaps the upper-right and lower-left `j x j` blocks of every `2j x 2j` block on the diagonal.
/// The rounds with `j >= 8` pair whole runs of words, which the compiler vectorizes.
#[inline]
pub fn transpose_64x64(m: &mut [u64; 64]) {
    #[inline(always)]
    fn round<const J: usize>(m: &mut [u64; 64], mask: u64) {
        for base in (0..64).step_by(2 * J) {
            for k in base..base + J {
                let t = ((m[k] >> J) ^ m[k + J]) & mask;
                m[k] ^= t << J;
                m[k + J] ^= t;
            }
        }
    }
    round::<32>(m, 0x0000_0000_FFFF_FFFF);
    round::<16>(m, 0x0000_FFFF_0000_FFFF);
    round::<8>(m, 0x00FF_00FF_00FF_00FF);
    round::<4>(m, 0x0F0F_0F0F_0F0F_0F0F);
    round::<2>(m, 0x3333_3333_3333_3333);
    round::<1>(m, 0x5555_5555_5555_5555);
}

/// Transpose the 8x8 bit matrix whose byte `r` is row `r` (Hacker's Delight, section 7-3).
///
/// Bit `r * 8 + c` moves to bit `c * 8 + r`.
#[inline(always)]
#[cfg_attr(
    all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"),
    allow(dead_code)
)]
const fn transpose_8x8_bits(mut x: u64) -> u64 {
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^ t ^ (t << 28)
}

/// Gather each byte column into a word, and transpose its bits.
///
/// The compiler vectorizes the gather, which beats transposing the bytes in registers first.
#[cfg_attr(
    any(
        all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"),
        all(target_arch = "x86_64", target_feature = "avx2"),
        target_arch = "aarch64"
    ),
    allow(dead_code)
)]
#[inline]
fn bit_transpose_64bytes_portable(input: &[u8; 64], output: &mut [u8; 64]) {
    for (b, row) in output.as_chunks_mut::<8>().0.iter_mut().enumerate() {
        let column = u64::from_le_bytes(std::array::from_fn(|x| input[8 * x + b]));
        *row = transpose_8x8_bits(column).to_le_bytes();
    }
}

/// `vpermb` gathers each byte column into a word, rows reversed.
///
/// `vgf2p8affineqb` then computes, per byte `j` of the constant and word `A`:
///
/// ```text
///     result byte j bit i  =  parity(A byte (7 - i)  &  constant byte j)
/// ```
///
/// With constant byte `j = 1 << j`, that is bit `j` of `A`'s byte `7 - i`: the reversal undoes it.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
#[target_feature(enable = "avx512f,avx512vbmi,gfni")]
unsafe fn bit_transpose_64bytes_gfni(input: &[u8; 64], output: &mut [u8; 64]) {
    // SAFETY: each load and store is one 64-byte array.
    unsafe {
        let rows = bit_transpose_zmm(_mm512_loadu_si512(input.as_ptr().cast()));
        _mm512_storeu_si512(output.as_mut_ptr().cast(), rows);
    }
}

/// The same transpose on a register: qword `x` is input row `x`, and byte `8b + t` of the result is output row `b`, byte `t`.
///
/// One byte permute and one affine map, so a caller that gathers its rows into a register never stores them first.
///
/// # Safety
///
/// The CPU must have the enabled target features.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
#[inline]
#[target_feature(enable = "avx512f,avx512vbmi,gfni")]
pub fn bit_transpose_zmm(rows: __m512i) -> __m512i {
    // Word `b`, byte `j`: input row `7 - j`, column `b`.
    const IDX: [u8; 64] = {
        let mut idx = [0u8; 64];
        let mut i = 0;
        while i < 64 {
            idx[i] = ((7 - i % 8) * 8 + i / 8) as u8;
            i += 1;
        }
        idx
    };
    // SAFETY: the index array is 64 bytes.
    let columns = _mm512_permutexvar_epi8(unsafe { _mm512_loadu_si512(IDX.as_ptr().cast()) }, rows);
    let unit = _mm512_set1_epi64(0x8040_2010_0804_0201_u64 as i64);
    _mm512_gf2p8affine_epi64_epi8::<0>(unit, columns)
}

/// Gather each byte column of the eight 8-byte rows into a word, in the row order `order` picks.
///
/// After two unpack rounds, lane `l` of the result's register `w` holds columns `4w + 2l` and `4w + 2l + 1`.
/// Their bytes sit at:
///
/// ```text
///     rows 0, 1, 4, 5    bytes 0..4 (first column), 4..8 (second)
///     rows 2, 3, 6, 7    bytes 8..12 (first column), 12..16 (second)
/// ```
///
/// So `order[8c + k]` is the byte that becomes byte `k` of the lane's column `c`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "avx2")]
fn gather_columns_avx2(input: &[u8; 64], order: &[u8; 16]) -> [__m256i; 2] {
    // SAFETY: the loads read the two halves of the 64-byte input and the 16-byte order.
    let (v0, v1, order) = unsafe {
        (
            _mm256_loadu_si256(input.as_ptr().cast()),
            _mm256_loadu_si256(input.as_ptr().add(32).cast()),
            _mm256_broadcastsi128_si256(_mm_loadu_si128(order.as_ptr().cast())),
        )
    };
    // Lane 0: rows 0 and 4, then rows 1 and 5, byte-interleaved; lane 1: rows 2 and 6, then 3 and 7.
    let (t0, t1) = (_mm256_unpacklo_epi8(v0, v1), _mm256_unpackhi_epi8(v0, v1));
    // Dword `c` of lane 0 is column `c` of rows 0, 1, 4, 5; of lane 1, of rows 2, 3, 6, 7.
    let (u0, u1) = (_mm256_unpacklo_epi8(t0, t1), _mm256_unpackhi_epi8(t0, t1));
    // Bring both halves of two columns into one lane, then order their bytes.
    [u0, u1].map(|u| _mm256_shuffle_epi8(_mm256_permute4x64_epi64::<0b11_01_10_00>(u), order))
}

/// [`gather_columns_avx2`] with the rows reversed, then the affine map of the AVX-512 arm.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
#[cfg_attr(target_feature = "avx512vbmi", allow(dead_code))]
#[target_feature(enable = "avx2,gfni")]
unsafe fn bit_transpose_64bytes_gfni_avx2(input: &[u8; 64], output: &mut [u8; 64]) {
    const REVERSED: [u8; 16] = [11, 10, 3, 2, 9, 8, 1, 0, 15, 14, 7, 6, 13, 12, 5, 4];
    let unit = _mm256_set1_epi64x(0x8040_2010_0804_0201_u64 as i64);
    for (i, columns) in gather_columns_avx2(input, &REVERSED).into_iter().enumerate() {
        let rows = _mm256_gf2p8affine_epi64_epi8::<0>(unit, columns);
        // SAFETY: the two stores fill the 64-byte output.
        unsafe { _mm256_storeu_si256(output.as_mut_ptr().add(32 * i).cast(), rows) };
    }
}

/// [`gather_columns_avx2`] in row order, then the three masked-swap rounds of [`transpose_8x8_bits`] on four words at a time.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(target_feature = "gfni", allow(dead_code))]
#[target_feature(enable = "avx2")]
unsafe fn bit_transpose_64bytes_avx2(input: &[u8; 64], output: &mut [u8; 64]) {
    const NATURAL: [u8; 16] = [0, 1, 8, 9, 2, 3, 10, 11, 4, 5, 12, 13, 6, 7, 14, 15];
    #[inline]
    #[target_feature(enable = "avx2")]
    fn swap<const D: i32>(x: __m256i, mask: u64) -> __m256i {
        let mask = _mm256_set1_epi64x(mask as i64);
        let t = _mm256_and_si256(_mm256_xor_si256(x, _mm256_srli_epi64::<D>(x)), mask);
        _mm256_xor_si256(x, _mm256_xor_si256(t, _mm256_slli_epi64::<D>(t)))
    }
    for (i, x) in gather_columns_avx2(input, &NATURAL).into_iter().enumerate() {
        let x = swap::<7>(x, 0x00AA_00AA_00AA_00AA);
        let x = swap::<14>(x, 0x0000_CCCC_0000_CCCC);
        let x = swap::<28>(x, 0x0000_0000_F0F0_F0F0);
        // SAFETY: the two stores fill the 64-byte output.
        unsafe { _mm256_storeu_si256(output.as_mut_ptr().add(32 * i).cast(), x) };
    }
}

/// `vqtbl4q_u8` gathers each byte column into a word, then three masked-swap rounds transpose its bits.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn bit_transpose_64bytes_neon(input: &[u8; 64], output: &mut [u8; 64]) {
    // SAFETY: NEON is part of the aarch64 baseline, and every load and store offset is below 64, the length of
    // both arrays.
    unsafe {
        let in_ptr = input.as_ptr();
        let v0 = vld1q_u8(in_ptr);
        let v1 = vld1q_u8(in_ptr.add(16));
        let v2 = vld1q_u8(in_ptr.add(32));
        let v3 = vld1q_u8(in_ptr.add(48));
        let table = uint8x16x4_t(v0, v1, v2, v3);

        // vqtbl4q indexes that bring bytes belonging to byte-chunk b ∈ 0..8
        // into contiguous 8-byte runs, packed two-chunks-per-Q-reg.
        const IDX0: [u8; 16] = [0, 8, 16, 24, 32, 40, 48, 56, 1, 9, 17, 25, 33, 41, 49, 57];
        const IDX1: [u8; 16] = [2, 10, 18, 26, 34, 42, 50, 58, 3, 11, 19, 27, 35, 43, 51, 59];
        const IDX2: [u8; 16] = [4, 12, 20, 28, 36, 44, 52, 60, 5, 13, 21, 29, 37, 45, 53, 61];
        const IDX3: [u8; 16] = [6, 14, 22, 30, 38, 46, 54, 62, 7, 15, 23, 31, 39, 47, 55, 63];

        let mut y0 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX0.as_ptr())));
        let mut y1 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX1.as_ptr())));
        let mut y2 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX2.as_ptr())));
        let mut y3 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX3.as_ptr())));

        let mask1 = vdupq_n_u64(0x00AA00AA00AA00AA);
        let mask2 = vdupq_n_u64(0x0000CCCC0000CCCC);
        let mask3 = vdupq_n_u64(0x00000000F0F0F0F0);

        // Round 1: distance 7.
        let t0 = vandq_u64(veorq_u64(y0, vshrq_n_u64::<7>(y0)), mask1);
        let t1 = vandq_u64(veorq_u64(y1, vshrq_n_u64::<7>(y1)), mask1);
        let t2 = vandq_u64(veorq_u64(y2, vshrq_n_u64::<7>(y2)), mask1);
        let t3 = vandq_u64(veorq_u64(y3, vshrq_n_u64::<7>(y3)), mask1);
        y0 = veorq_u64(y0, veorq_u64(t0, vshlq_n_u64::<7>(t0)));
        y1 = veorq_u64(y1, veorq_u64(t1, vshlq_n_u64::<7>(t1)));
        y2 = veorq_u64(y2, veorq_u64(t2, vshlq_n_u64::<7>(t2)));
        y3 = veorq_u64(y3, veorq_u64(t3, vshlq_n_u64::<7>(t3)));

        // Round 2: distance 14.
        let t0 = vandq_u64(veorq_u64(y0, vshrq_n_u64::<14>(y0)), mask2);
        let t1 = vandq_u64(veorq_u64(y1, vshrq_n_u64::<14>(y1)), mask2);
        let t2 = vandq_u64(veorq_u64(y2, vshrq_n_u64::<14>(y2)), mask2);
        let t3 = vandq_u64(veorq_u64(y3, vshrq_n_u64::<14>(y3)), mask2);
        y0 = veorq_u64(y0, veorq_u64(t0, vshlq_n_u64::<14>(t0)));
        y1 = veorq_u64(y1, veorq_u64(t1, vshlq_n_u64::<14>(t1)));
        y2 = veorq_u64(y2, veorq_u64(t2, vshlq_n_u64::<14>(t2)));
        y3 = veorq_u64(y3, veorq_u64(t3, vshlq_n_u64::<14>(t3)));

        // Round 3: distance 28.
        let t0 = vandq_u64(veorq_u64(y0, vshrq_n_u64::<28>(y0)), mask3);
        let t1 = vandq_u64(veorq_u64(y1, vshrq_n_u64::<28>(y1)), mask3);
        let t2 = vandq_u64(veorq_u64(y2, vshrq_n_u64::<28>(y2)), mask3);
        let t3 = vandq_u64(veorq_u64(y3, vshrq_n_u64::<28>(y3)), mask3);
        y0 = veorq_u64(y0, veorq_u64(t0, vshlq_n_u64::<28>(t0)));
        y1 = veorq_u64(y1, veorq_u64(t1, vshlq_n_u64::<28>(t1)));
        y2 = veorq_u64(y2, veorq_u64(t2, vshlq_n_u64::<28>(t2)));
        y3 = veorq_u64(y3, veorq_u64(t3, vshlq_n_u64::<28>(t3)));

        let out_ptr = output.as_mut_ptr();
        vst1q_u8(out_ptr, vreinterpretq_u8_u64(y0));
        vst1q_u8(out_ptr.add(16), vreinterpretq_u8_u64(y1));
        vst1q_u8(out_ptr.add(32), vreinterpretq_u8_u64(y2));
        vst1q_u8(out_ptr.add(48), vreinterpretq_u8_u64(y3));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    /// The definition, one bit at a time.
    fn reference(input: &[u8; 64]) -> [u8; 64] {
        let mut output = [0u8; 64];
        for x in 0..8 {
            for b in 0..8 {
                for t in 0..8 {
                    output[b * 8 + t] |= ((input[x * 8 + b] >> t) & 1) << x;
                }
            }
        }
        output
    }

    #[test]
    fn transpose_64x64_matches_definition() {
        let mut rng = Rng::new(0x6464);
        let edges: [[u64; 64]; 3] = [[0; 64], [u64::MAX; 64], std::array::from_fn(|r| 1 << r)];
        for m in edges
            .into_iter()
            .chain((0..64).map(|_| std::array::from_fn(|_| rng.next_u64())))
        {
            // The definition, one bit at a time.
            let mut want = [0u64; 64];
            for (r, &row) in m.iter().enumerate() {
                for (c, col) in want.iter_mut().enumerate() {
                    *col |= ((row >> c) & 1) << r;
                }
            }
            let mut got = m;
            transpose_64x64(&mut got);
            assert_eq!(got, want);
        }
    }

    #[test]
    fn transpose_8x8_bits_matches_definition() {
        let mut rng = Rng::new(0x88);
        for x in [0, u64::MAX, 1, 1 << 63]
            .into_iter()
            .chain((0..256).map(|_| rng.next_u64()))
        {
            let mut want = 0u64;
            for r in 0..8 {
                for c in 0..8 {
                    want |= ((x >> (r * 8 + c)) & 1) << (c * 8 + r);
                }
            }
            assert_eq!(transpose_8x8_bits(x), want, "input={x:016x}");
        }
    }

    #[test]
    fn every_arm_matches_reference() {
        // Invariant: every arm this target compiles matches the definition, not only the dispatched one.
        let mut rng = Rng::new(0xB17_BB17);
        let edges = [[0u8; 64], [0xFF; 64], std::array::from_fn(|i| 1 << (i % 8))];
        for input in edges
            .into_iter()
            .chain((0..256).map(|_| std::array::from_fn(|_| rng.next_u8())))
        {
            let want = reference(&input);
            let mut got = [0u8; 64];
            bit_transpose_64bytes(&input, &mut got);
            assert_eq!(got, want, "dispatched");
            bit_transpose_64bytes_portable(&input, &mut got);
            assert_eq!(got, want, "portable");
            #[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
            {
                // SAFETY: compiled only with the features enabled.
                unsafe { bit_transpose_64bytes_gfni(&input, &mut got) };
                assert_eq!(got, want, "gfni");
            }
            #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
            {
                // SAFETY: compiled only with the features enabled.
                unsafe { bit_transpose_64bytes_gfni_avx2(&input, &mut got) };
                assert_eq!(got, want, "gfni avx2");
            }
            #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
            {
                // SAFETY: compiled only with the feature enabled.
                unsafe { bit_transpose_64bytes_avx2(&input, &mut got) };
                assert_eq!(got, want, "avx2");
            }
            #[cfg(target_arch = "aarch64")]
            {
                // SAFETY: aarch64 always has NEON.
                unsafe { bit_transpose_64bytes_neon(&input, &mut got) };
                assert_eq!(got, want, "neon");
            }
        }
    }
}
