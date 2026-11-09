//! Field arithmetic: `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` and `E = K[y]/(y^2 + x y + 1)`, on plain integers.

use std::ops::{Add, AddAssign, Mul, MulAssign};

/// The low 64 bits of a 64x64 carry-less product, by integer multiplication: with both operands split into the four
/// classes of their bit positions mod 4, a coefficient below bit 60 sums at most 15 bits, so its carries stay below
/// the next bit of its class. One at bit 60 or above may sum 16, whose carry lands past bit 63. Masking each class
/// product to its own bits then leaves the parities.
const fn clmul_low(a: u64, b: u64) -> u64 {
    const M0: u64 = 0x1111_1111_1111_1111;
    const M1: u64 = M0 << 1;
    const M2: u64 = M0 << 2;
    const M3: u64 = M0 << 3;
    let (x0, x1, x2, x3) = (a & M0, a & M1, a & M2, a & M3);
    let (y0, y1, y2, y3) = (b & M0, b & M1, b & M2, b & M3);
    let z0 = x0.wrapping_mul(y0) ^ x1.wrapping_mul(y3) ^ x2.wrapping_mul(y2) ^ x3.wrapping_mul(y1);
    let z1 = x0.wrapping_mul(y1) ^ x1.wrapping_mul(y0) ^ x2.wrapping_mul(y3) ^ x3.wrapping_mul(y2);
    let z2 = x0.wrapping_mul(y2) ^ x1.wrapping_mul(y1) ^ x2.wrapping_mul(y0) ^ x3.wrapping_mul(y3);
    let z3 = x0.wrapping_mul(y3) ^ x1.wrapping_mul(y2) ^ x2.wrapping_mul(y1) ^ x3.wrapping_mul(y0);
    z0 & M0 | z1 & M1 | z2 & M2 | z3 & M3
}

/// 64x64 carry-less product: the high half is the low half of the bit-reversed operands' product, reversed back.
const fn clmul(a: u64, b: u64) -> u128 {
    let low = clmul_low(a, b);
    let high = clmul_low(a.reverse_bits(), b.reverse_bits()).reverse_bits() >> 1;
    (high as u128) << 64 | low as u128
}

/// The carry-less square: the bits of `a` spread to the even positions.
const fn spread(a: u64) -> u128 {
    let mut x = a as u128;
    x = (x | x << 32) & 0x0000_0000_FFFF_FFFF_0000_0000_FFFF_FFFF;
    x = (x | x << 16) & 0x0000_FFFF_0000_FFFF_0000_FFFF_0000_FFFF;
    x = (x | x << 8) & 0x00FF_00FF_00FF_00FF_00FF_00FF_00FF_00FF;
    x = (x | x << 4) & 0x0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F;
    x = (x | x << 2) & 0x3333_3333_3333_3333_3333_3333_3333_3333;
    (x | x << 1) & 0x5555_5555_5555_5555_5555_5555_5555_5555
}

/// Reduce a 128-bit carry-less product modulo `x^64 + x^4 + x^3 + x + 1`.
pub(crate) const fn reduce(p: u128) -> u64 {
    let (lo, hi) = (p as u64, (p >> 64) as u64);
    // The bits of `hi * 0x1B` shifted past x^63 wrap around once more, and that second fold is final.
    let spill = (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
    let v = hi ^ spill;
    lo ^ v ^ (v << 1) ^ (v << 3) ^ (v << 4)
}

const fn base_mul(left: u64, right: u64) -> u64 {
    reduce(clmul(left, right))
}

/// GF(2^64) = F2\[x\]/(x^64 + x^4 + x^3 + x + 1)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct K(pub u64);

impl K {
    /// Its transport image: one 64-bit little-endian word.
    pub fn to_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }

    pub fn square(self) -> Self {
        Self(reduce(spread(self.0)))
    }

    /// `self^(2^64 - 2)` by Itoh-Tsujii, each `t_k = self^(2^k - 1)`; zero maps to zero.
    pub fn inv(self) -> Self {
        let sq = |mut v: Self, n: u32| {
            for _ in 0..n {
                v = v.square();
            }
            v
        };
        let t1 = self;
        let t2 = sq(t1, 1) * t1;
        let t3 = sq(t2, 1) * t1;
        let t6 = sq(t3, 3) * t3;
        let t12 = sq(t6, 6) * t6;
        let t24 = sq(t12, 12) * t12;
        let t48 = sq(t24, 24) * t24;
        let t60 = sq(t48, 12) * t12;
        let t63 = sq(t60, 3) * t3;
        sq(t63, 1)
    }
}

impl Add for K {
    type Output = Self;
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

impl Mul for K {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self(base_mul(self.0, rhs.0))
    }
}

/// K\[y\]/(y^2 + x y + 1): the challenge field, a degree-2 extension of K.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct E {
    pub c0: u64,
    pub c1: u64,
}

pub const ZERO: E = E::new(0, 0);
pub const ONE: E = E::new(1, 0);
pub const GEN: E = E::new(2, 0);

/// `x * value` in K.
const fn times_x(value: u64) -> u64 {
    value << 1 ^ (0u64.wrapping_sub(value >> 63) & 0x1B)
}

impl E {
    pub const fn new(c0: u64, c1: u64) -> Self {
        Self { c0, c1 }
    }

    pub fn sum(values: impl IntoIterator<Item = E>) -> E {
        values.into_iter().fold(ZERO, |acc, value| acc + value)
    }

    /// Each limb ANDed with `mask`: itself under all ones, zero under zero.
    pub fn masked(self, mask: u64) -> Self {
        Self::new(self.c0 & mask, self.c1 & mask)
    }

    pub fn square(self) -> Self {
        let (s0, s1) = (spread(self.c0), spread(self.c1));
        // y^2 = x y + 1.
        Self::new(reduce(s0 ^ s1), reduce(s1 << 1))
    }

    /// `self^(2^64)`: K is fixed, and y maps to its conjugate y + x.
    fn frobenius(self) -> Self {
        Self::new(self.c0 ^ times_x(self.c1), self.c1)
    }

    pub fn pow(self, exponent: u64) -> Self {
        let (mut base, mut out, mut n) = (self, ONE, exponent);
        while n != 0 {
            if n & 1 == 1 {
                out *= base;
            }
            base = base.square();
            n >>= 1;
        }
        out
    }

    /// `self^(2^128 - 2)` through the norm to K: with `m` the conjugate, `self * m` lies in K. Zero maps to zero.
    pub fn inv(self) -> Self {
        let m = self.frobenius();
        let norm = self * m;
        m * E::from(K(norm.c0).inv())
    }
}

impl From<K> for E {
    fn from(value: K) -> Self {
        Self::new(value.0, 0)
    }
}

impl Add for E {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self::new(self.c0 ^ rhs.c0, self.c1 ^ rhs.c1)
    }
}

impl AddAssign for E {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Mul for E {
    type Output = Self;
    /// Karatsuba: three base products, then y^2 = x y + 1 folds `a1 b1 y^2` back, the x a one-bit shift.
    fn mul(self, rhs: Self) -> Self {
        let (a, b) = (self, rhs);
        let (p0, p1) = (clmul(a.c0, b.c0), clmul(a.c1, b.c1));
        let middle = clmul(a.c0 ^ a.c1, b.c0 ^ b.c1) ^ p0 ^ p1;
        Self::new(reduce(p0 ^ p1), reduce(middle ^ p1 << 1))
    }
}

impl Mul<K> for E {
    type Output = Self;
    fn mul(self, rhs: K) -> Self {
        Self::new(base_mul(self.c0, rhs.0), base_mul(self.c1, rhs.0))
    }
}

impl MulAssign for E {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

/// How many bits of the other operand one [`Scaled`] lookup consumes.
const WINDOW: usize = 6;
const WINDOWS_PER_LIMB: usize = 64usize.div_ceil(WINDOW);

/// Multiplication by one fixed `r`, which is F2-linear: `r * x^(WINDOW j) * y^t * n` tabulated for every window value
/// `n`, so a product is the sum of one entry per window of the other operand, with nothing left to reduce. It pays
/// where `r` multiplies many values.
///
/// One flat run of tables, indexed through bounds checks the compiler cannot discharge: they keep the lookups, and loops
/// of products, from being vectorized into AVX-512 gathers, which lose to the scalar loads.
pub struct Scaled(Vec<E>);

impl Scaled {
    pub fn new(r: E) -> Self {
        // r * x^k * y^t, k ascending: each step multiplies every limb by x.
        let mut tables = vec![ZERO; (2 * WINDOWS_PER_LIMB) << WINDOW];
        let mut monomial = r;
        for limb_tables in tables.as_chunks_mut::<{ WINDOWS_PER_LIMB << WINDOW }>().0 {
            let mut power = monomial;
            for table in limb_tables.as_chunks_mut::<{ 1 << WINDOW }>().0 {
                for bit in 0..WINDOW {
                    for low in 0..1 << bit {
                        table[1 << bit | low] = table[low] + power;
                    }
                    power = E::new(times_x(power.c0), times_x(power.c1));
                }
            }
            // times y, with y^2 = x y + 1.
            monomial = E::new(monomial.c1, monomial.c0 ^ times_x(monomial.c1));
        }
        Self(tables)
    }

    #[inline]
    pub fn mul(&self, a: E) -> E {
        let mut product = ZERO;
        let mut table = 0;
        for limb in [a.c0, a.c1] {
            for window in 0..WINDOWS_PER_LIMB {
                product += self.0[(table << WINDOW) | ((limb >> (WINDOW * window)) as usize % (1 << WINDOW))];
                table += 1;
            }
        }
        product
    }
}

/// `[1, base, base^2, ...]`, `count` terms.
pub fn powers(base: E, count: usize) -> Vec<E> {
    let mut out = Vec::with_capacity(count);
    let mut power = ONE;
    for _ in 0..count {
        out.push(power);
        power *= base;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Independent reference vectors: (a, b, a * b).
    const K_VECTORS: [(u64, u64, u64); 3] = [
        (0x01090913877ed8ed, 0x66ab35ac2768468f, 0x50c4519dc383744a),
        (0xa7715ae18f12a3b5, 0x05743059f43fa4f5, 0xeb64cd9cd9cda6df),
        (0xbd3efb4705e79ddd, 0x3aff618604de4ae0, 0xc3d7a95fa9cb59bb),
    ];

    /// Independent reference vectors: (a, b, a * b, a * a, a^-1).
    type ReferenceVector = ([u64; 2], [u64; 2], [u64; 2], [u64; 2], [u64; 2]);
    const E_VECTORS: [ReferenceVector; 4] = [
        (
            [0x8a1d921ca352a3c3, 0xa10d04b240699a83],
            [0x936d4747ab0e6d1c, 0xe46ab5adb68f9c7d],
            [0xfbbffa3000b331c0, 0xbf494d14ce4eadf8],
            [0x3eb21e43df9bbb1c, 0x7836265481e5ee7d],
            [0x4dbcb8833d2c881c, 0x01d5fd8ef4de46b1],
        ),
        (
            [0x4ced30628e0cd071, 0xc694494e11044370],
            [0x079184601cbc456d, 0xc2b90e2d4a7acb31],
            [0x1df92a5bbf394f60, 0x4f9871091371b5d2],
            [0x87f8c19a80de6b2b, 0xe1b7b5434dbf44ba],
            [0xe5886c008822ac39, 0x5014981d45105c3b],
        ),
        (
            [0x1f7678795f345ff4, 0xd584a285e92195e8],
            [0xa4fab233b7895f8e, 0xe8c4546870efc3e0],
            [0x39944740fab79b32, 0x677a979829fc8fea],
            [0x33bf067a3def0161, 0x7dd98b6fdaf72b54],
            [0x126bd1f8da56668e, 0xf1e4a54eaa0dc2d0],
        ),
        (
            [0xf8a7e4e12a61d563, 0x852495966643d5c8],
            [0x5b2495d1eb090346, 0x786d6f68d7273a2f],
            [0x6617b862c301fca8, 0x1edae1e051362791],
            [0xd03dc472c71a8299, 0xab7efb6717791597],
            [0x36a2e97ec7233d69, 0xb5f24753a7ede4d1],
        ),
    ];

    /// Operands that drive the reduction's spill: the top bits, all bits, and the modulus tail.
    const CORNERS: [u64; 5] = [1, u64::MAX, 1 << 63, 0xF000_0000_0000_0000, 0x1B];

    /// Schoolbook multiply, then bit-by-bit long division by the modulus.
    fn reference_mul(a: u64, b: u64) -> u64 {
        let mut p = (0..64)
            .filter(|i| (a >> i) & 1 != 0)
            .fold(0u128, |p, i| p ^ (b as u128) << i);
        for bit in (64..128).rev() {
            if (p >> bit) & 1 != 0 {
                p ^= ((1u128 << 64) | 0x1B) << (bit - 64);
            }
        }
        p as u64
    }

    #[test]
    fn base_field_matches_reference() {
        for (a, b, c) in K_VECTORS {
            assert_eq!(K(a) * K(b), K(c));
        }
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let random = std::iter::repeat_with(move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        });
        let operands = K_VECTORS
            .iter()
            .flat_map(|&(a, b, c)| [a, b, c])
            .chain(CORNERS)
            .chain(random.take(40));
        for a in operands.clone() {
            for b in operands.clone() {
                assert_eq!((K(a) * K(b)).0, reference_mul(a, b));
            }
            assert_eq!(K(a) * K(a).inv(), K(1));
        }
        assert_eq!(K(0).inv(), K(0));
    }

    #[test]
    fn extension_field_matches_reference() {
        let e = |limbs: [u64; 2]| E::new(limbs[0], limbs[1]);
        for (a, b, c, s, i) in E_VECTORS {
            assert_eq!(e(a) * e(b), e(c));
            assert_eq!(e(a).square(), e(s));
            assert_eq!(e(a).inv(), e(i));
            for value in [e(a), e(b), e(c), E::new(a[0], 0), E::new(0, b[1])] {
                assert_eq!(value * value.inv(), ONE);
                let sixty_four_squarings = (0..64).fold(value, |v, _| v.square());
                assert_eq!(value.frobenius(), sixty_four_squarings);
            }
            assert_eq!(e(a).pow(5), e(a).square().square() * e(a));
        }
        let y = E::new(0, 1);
        assert_eq!(y * y, E::new(1, 2));
        assert_eq!(y.frobenius(), y + GEN);
        for (a, b, ..) in E_VECTORS {
            let scaled = Scaled::new(e(a));
            for value in [e(b), y, ONE, ZERO, E::new(u64::MAX, u64::MAX)] {
                assert_eq!(scaled.mul(value), e(a) * value);
            }
        }
        assert_eq!(ZERO.inv(), ZERO);
    }
}
