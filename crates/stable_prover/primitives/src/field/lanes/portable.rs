//! Every lane operation as plain scalar code: a field lane is the scalar operation, a byte operation its loop. This is
//! the definition the tests hold every vector arm to, the backend of a target without a vector carry-less multiplier,
//! and the body a vector backend reuses for an operation it has no arm for.

use super::Linear16;
use crate::field::{F64, F128, F128Unreduced};

/// The carry-less product by schoolbook: `b * x^i` for every set bit `i` of `a`.
pub const fn mul_wide(a: u64, b: u64) -> u128 {
    let mut acc = 0u128;
    let mut i = 0;
    while i < 64 {
        if (a >> i) & 1 != 0 {
            acc ^= (b as u128) << i;
        }
        i += 1;
    }
    acc
}

/// One `E` product.
#[inline(always)]
pub(crate) fn mul(a: F128, b: F128) -> F128 {
    a.mul_unreduced(b).reduce()
}

/// Eight `K` elements.
#[derive(Clone, Copy, Debug)]
pub struct F64x8([F64; 8]);

/// Eight `E` elements.
#[derive(Clone, Copy, Debug)]
pub struct F128x8([F128; 8]);

/// Eight unreduced `E` sums of products.
#[derive(Clone, Copy, Debug)]
pub struct Acc8([F128Unreduced; 8]);

/// Eight sums of 128-bit carry-less products.
#[derive(Clone, Copy, Debug)]
pub struct Wide8([u128; 8]);

impl F64x8 {
    pub const ZERO: Self = Self([F64::ZERO; 8]);

    #[inline(always)]
    pub fn splat(k: F64) -> Self {
        Self([k; 8])
    }

    #[inline(always)]
    pub fn from_array(k: &[F64; 8]) -> Self {
        Self(*k)
    }

    #[inline(always)]
    pub fn to_array(self) -> [F64; 8] {
        self.0
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] + rhs.0[i]))
    }

    #[inline(always)]
    pub(super) fn product(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] * rhs.0[i]))
    }
}

impl F128x8 {
    pub const ZERO: Self = Self([F128::ZERO; 8]);

    #[inline(always)]
    pub fn splat(e: F128) -> Self {
        Self([e; 8])
    }

    #[inline(always)]
    pub fn from_array(e: &[F128; 8]) -> Self {
        Self(*e)
    }

    #[inline(always)]
    pub fn to_array(self) -> [F128; 8] {
        self.0
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] + rhs.0[i]))
    }

    /// The eight products `self[i] * rhs[i]`, unreduced.
    #[inline(always)]
    pub fn mul_unreduced(self, rhs: Self) -> Acc8 {
        Acc8(core::array::from_fn(|i| self.0[i].mul_unreduced(rhs.0[i])))
    }

    /// The eight mixed products `self[i] * k[i]`, unreduced.
    #[inline(always)]
    pub fn mul_base_unreduced(self, k: F64x8) -> Acc8 {
        Acc8(core::array::from_fn(|i| self.0[i].mul_base_unreduced(k.0[i])))
    }
}

impl Acc8 {
    pub const ZERO: Self = Self([F128Unreduced::ZERO; 8]);

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] ^ rhs.0[i]))
    }

    /// Every lane reduced.
    #[inline(always)]
    pub fn reduce(self) -> F128x8 {
        F128x8(self.0.map(F128Unreduced::reduce))
    }

    /// The sum of the eight lanes, reduced once.
    #[inline(always)]
    pub fn sum(self) -> F128 {
        self.0.into_iter().fold(F128Unreduced::ZERO, |s, x| s ^ x).reduce()
    }
}

impl Wide8 {
    pub const ZERO: Self = Self([0; 8]);

    /// The eight carry-less products `a[i] * b[i]`.
    #[inline(always)]
    pub fn mul(a: [u64; 8], b: [u64; 8]) -> Self {
        Self(core::array::from_fn(|i| super::mul_wide(a[i], b[i])))
    }

    #[inline(always)]
    pub(super) fn xor(self, rhs: Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i] ^ rhs.0[i]))
    }

    #[inline(always)]
    pub(super) fn to_array(self) -> [u128; 8] {
        self.0
    }
}

/// The low 64 bits of the eight carry-less products `a[i] * b[i]`.
#[inline(always)]
pub fn clmul8_low(a: [u64; 8], b: [u64; 8]) -> [u64; 8] {
    core::array::from_fn(|i| super::mul_wide(a[i], b[i]) as u64)
}

/// A GF(2)-linear map of bytes, as the images of the sixteen values of the low nibble and of the high one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteMap {
    pub(super) nibbles: [[u8; 16]; 2],
}

impl ByteMap {
    /// The map sending bit `c` to `images[c]`.
    pub const fn new(images: [u8; 8]) -> Self {
        let mut nibbles = [[0u8; 16]; 2];
        let mut c = 0;
        while c < 8 {
            let mut v = 0;
            while v < 16 {
                if v >> (c % 4) & 1 == 1 {
                    nibbles[c / 4][v] ^= images[c];
                }
                v += 1;
            }
            c += 1;
        }
        Self { nibbles }
    }
}

/// Every byte of `x` through `m`.
#[inline(always)]
pub fn map_bytes(m: &ByteMap, x: [u64; 8]) -> [u64; 8] {
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

/// The 8 by 64 bit matrix of `rows` transposed: bit `k` of byte `n` is bit `n` of `rows[k]`. Each word's bytes are
/// gathered by row, then each 8 by 8 block is transposed in place, both by swaps of masked shifts.
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
