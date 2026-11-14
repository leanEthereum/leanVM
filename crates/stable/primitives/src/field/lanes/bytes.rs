//! The byte operations as plain scalar code: the reference the vector arms are tested against, and the form a
//! backend without a vector arm for one of them uses.
#![allow(dead_code, reason = "each backend uses the ones it has no vector arm for")]

use super::Linear16;

/// Every byte of `x` through `m`.
#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    target_feature = "vpclmulqdq",
    target_feature = "gfni"
)))]
#[inline(always)]
pub fn map_bytes(m: &super::ByteMap, x: [u64; 8]) -> [u64; 8] {
    x.map(|w| {
        u64::from_le_bytes(
            w.to_le_bytes()
                .map(|b| m.nibbles[0][b as usize & 15] ^ m.nibbles[1][b as usize >> 4]),
        )
    })
}

/// `m` of each 16-bit field of each lane: field `f` of lane `i` to lane `i` of output `f`.
#[inline(always)]
pub fn map_fields(m: &Linear16, x: [u64; 8]) -> [[u64; 8]; 4] {
    core::array::from_fn(|f| x.map(|w| u64::from(m.apply((w >> (16 * f)) as u16))))
}

/// Eight rows of eight words transposed.
#[inline(always)]
pub fn transpose_words(rows: &[[u64; 8]; 8]) -> [[u64; 8]; 8] {
    core::array::from_fn(|c| core::array::from_fn(|r| rows[r][c]))
}

/// The 8 by 64 bit matrix of `rows` transposed: bit `k` of byte `n` is bit `n` of `rows[k]`. Each word's bytes
/// are gathered by row, then each 8 by 8 block is transposed in place, both by swaps of masked shifts.
#[inline(always)]
pub fn transpose_bits(rows: [u64; 8]) -> [u64; 8] {
    // Byte `k` of word `c` is byte `c` of row `k`.
    let mut w = rows;
    for (j, mask) in [
        (4usize, 0x0000_0000_ffff_ffffu64),
        (2, 0x0000_ffff_0000_ffff),
        (1, 0x00ff_00ff_00ff_00ff),
    ] {
        for i in (0..8).filter(|i| i & j == 0) {
            let t = ((w[i] >> (8 * j)) ^ w[i + j]) & mask;
            w[i + j] ^= t;
            w[i] ^= t << (8 * j);
        }
    }
    // Bit `k` of byte `b` swaps with bit `b` of byte `k`.
    w.map(|mut x| {
        for (s, mask) in [
            (7, 0x00aa_00aa_00aa_00aau64),
            (14, 0x0000_cccc_0000_cccc),
            (28, 0x0000_0000_f0f0_f0f0),
        ] {
            let t = (x ^ (x >> s)) & mask;
            x ^= t ^ (t << s);
        }
        x
    })
}

/// Sixteen rows of 64 bytes transposed: byte `b` of output `n` is byte `n` of `rows[b]`.
#[inline(always)]
pub fn transpose_bytes(rows: &[[u64; 8]; 16]) -> [u128; 64] {
    let bytes = rows.map(|r| {
        let mut b = [0u8; 64];
        for (b, w) in b.as_chunks_mut::<8>().0.iter_mut().zip(r) {
            *b = w.to_le_bytes();
        }
        b
    });
    core::array::from_fn(|n| u128::from_le_bytes(core::array::from_fn(|b| bytes[b][n])))
}
