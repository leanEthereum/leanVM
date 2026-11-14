// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Bit transposes.

/// Transpose the eight 8x8 bit matrices of a 64-byte block, gathered across rows.
///
/// ```text
///     output[b * 8 + t] bit x  =  input[x * 8 + b] bit t
/// ```
///
/// So byte column `b` of the eight input rows becomes output row `b`, bit-transposed.
#[inline]
pub fn bit_transpose_64bytes(input: &[u8; 64], output: &mut [u8; 64]) {
    for (b, row) in output.as_chunks_mut::<8>().0.iter_mut().enumerate() {
        let column = u64::from_le_bytes(std::array::from_fn(|x| input[8 * x + b]));
        *row = transpose_8x8_bits(column).to_le_bytes();
    }
}

/// Transpose the 8x8 bit matrix whose byte `r` is row `r` (Hacker's Delight, section 7-3).
///
/// Bit `r * 8 + c` moves to bit `c * 8 + r`.
#[inline(always)]
fn transpose_8x8_bits(mut x: u64) -> u64 {
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^ t ^ (t << 28)
}

/// [`bit_transpose_64bytes`] in a register.
///
/// `vpermb` gathers each byte column into a word, rows reversed.
///
/// `vgf2p8affineqb` then computes, per byte `j` of the constant and word `A`:
///
/// ```text
///     result byte j bit i  =  parity(A byte (7 - i)  &  constant byte j)
/// ```
///
/// With constant byte `j = 1 << j`, that is bit `j` of `A`'s byte `7 - i`: the reversal undoes it.
///
/// The cfg gate guarantees `avx512f`, `avx512vbmi` and `gfni` at compile time.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi", target_feature = "gfni"))]
#[inline(always)]
pub fn bit_transpose_64bytes_m512(input: core::arch::x86_64::__m512i) -> core::arch::x86_64::__m512i {
    use core::arch::x86_64::*;

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
    // SAFETY: the features are enabled at compile time, and `IDX` is 64 bytes.
    unsafe {
        let columns = _mm512_permutexvar_epi8(_mm512_loadu_si512(IDX.as_ptr().cast()), input);
        let unit = _mm512_set1_epi64(0x8040_2010_0804_0201_u64 as i64);
        _mm512_gf2p8affine_epi64_epi8::<0>(unit, columns)
    }
}

/// 4-bit bit reversal: the unpack network of the 16x16 in-lane transposes reads source rows in this order.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
const REV4: [usize; 16] = [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15];

/// A 16x16 byte transpose inside each 128-bit lane of 16 registers of one width: `out[k]` byte `p` of a lane is
/// `in[p]` byte `k` of that lane. Four rounds of unpacks.
macro_rules! transpose_bytes16x16_per_lane {
    ($(#[$m:meta])* $name:ident, $v:ty, $zero:ident, $([$lo:ident, $hi:ident]),*) => {
        $(#[$m])*
        ///
        /// # Safety
        ///
        /// Requires the target features the function enables.
        #[inline]
        pub fn $name(r: &mut [$v; 16]) {
            use core::arch::x86_64::*;
            *r = core::array::from_fn(|i| r[REV4[i]]);
            $({
                let mut t = [$zero(); 16];
                for i in 0..8 {
                    t[2 * i] = $lo(r[i], r[i + 8]);
                    t[2 * i + 1] = $hi(r[i], r[i + 8]);
                }
                *r = t;
            })*
        }
    };
}

transpose_bytes16x16_per_lane!(
    /// The in-lane 16x16 byte transpose of 16 AVX2 registers.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[target_feature(enable = "avx2")]
    transpose_bytes16x16_per_lane256,
    core::arch::x86_64::__m256i,
    _mm256_setzero_si256,
    [_mm256_unpacklo_epi8, _mm256_unpackhi_epi8],
    [_mm256_unpacklo_epi16, _mm256_unpackhi_epi16],
    [_mm256_unpacklo_epi32, _mm256_unpackhi_epi32],
    [_mm256_unpacklo_epi64, _mm256_unpackhi_epi64]
);

transpose_bytes16x16_per_lane!(
    /// The in-lane 16x16 byte transpose of 16 AVX-512 registers.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512bw"))]
    #[target_feature(enable = "avx512f", enable = "avx512bw")]
    transpose_bytes16x16_per_lane512,
    core::arch::x86_64::__m512i,
    _mm512_setzero_si512,
    [_mm512_unpacklo_epi8, _mm512_unpackhi_epi8],
    [_mm512_unpacklo_epi16, _mm512_unpackhi_epi16],
    [_mm512_unpacklo_epi32, _mm512_unpackhi_epi32],
    [_mm512_unpacklo_epi64, _mm512_unpackhi_epi64]
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

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
    fn bit_transpose_64bytes_matches_reference() {
        let mut rng = Rng::new(0xB17_BB17);
        let edges = [[0u8; 64], [0xFF; 64], std::array::from_fn(|i| 1 << (i % 8))];
        for input in edges
            .into_iter()
            .chain((0..256).map(|_| std::array::from_fn(|_| rng.next_u8())))
        {
            let mut got = [0u8; 64];
            bit_transpose_64bytes(&input, &mut got);
            assert_eq!(got, reference(&input));
        }
    }
}
