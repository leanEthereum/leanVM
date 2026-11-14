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
