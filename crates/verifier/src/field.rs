//! Field arithmetic: `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` and `E = K[y]/(y^3 + y + 1)`, on plain integers.

use crate::{VerifierError, require};
use std::ops::{Add, AddAssign, Mul, MulAssign};

/// The low 64 bits of a 64x64 carry-less product, by integer multiplication: with both operands split into the four
/// classes of their bit positions mod 4, a coefficient below bit 63 sums at most 15 bits, so its carries stay below
/// the next bit of its class, and the one that sums 16 carries past bit 63. That class's bits carry the parities.
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

/// K\[y\]/(y^3 + y + 1): the challenge field, a degree-3 extension of K.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct E {
    pub c0: u64,
    pub c1: u64,
    pub c2: u64,
}

pub const ZERO: E = E::new(0, 0, 0);
pub const ONE: E = E::new(1, 0, 0);
pub const GEN: E = E::new(2, 0, 0);

impl E {
    pub const fn new(c0: u64, c1: u64, c2: u64) -> Self {
        Self { c0, c1, c2 }
    }

    pub fn from_bytes(data: &[u8]) -> Result<Self, VerifierError> {
        require(data.len() == 24, VerifierError::FieldElementLength)?;
        let limb = |at: usize| u64::from_le_bytes(data[at..at + 8].try_into().unwrap());
        Ok(Self::new(limb(0), limb(8), limb(16)))
    }

    pub fn sum(values: impl IntoIterator<Item = E>) -> E {
        values.into_iter().fold(ZERO, |acc, value| acc + value)
    }

    /// Each limb ANDed with `mask`: itself under all ones, zero under zero.
    pub fn masked(self, mask: u64) -> Self {
        Self::new(self.c0 & mask, self.c1 & mask, self.c2 & mask)
    }

    pub fn is_zero(self) -> bool {
        self == ZERO
    }

    pub fn square(self) -> Self {
        let (s0, s1, s2) = (spread(self.c0), spread(self.c1), spread(self.c2));
        // y^4 = y^2 + y.
        Self::new(reduce(s0), reduce(s2), reduce(s1 ^ s2))
    }

    /// `self^(2^64)`: K is fixed, and y maps to y^2.
    fn frobenius(self) -> Self {
        Self::new(self.c0, self.c2, self.c1 ^ self.c2)
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

    /// `self^(2^192 - 2)` through the norm to K: with `m` the product of the two conjugates, `self * m` lies in K. Zero maps to zero.
    pub fn inv(self) -> Self {
        let m = self.frobenius() * self.frobenius().frobenius();
        let norm = self * m;
        m * E::from(K(norm.c0).inv())
    }
}

impl From<K> for E {
    fn from(value: K) -> Self {
        Self::new(value.0, 0, 0)
    }
}

impl Add for E {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self::new(self.c0 ^ rhs.c0, self.c1 ^ rhs.c1, self.c2 ^ rhs.c2)
    }
}

impl AddAssign for E {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Mul for E {
    type Output = Self;
    /// Karatsuba: six base products into the coefficients of y^0..y^4, then y^3 = y + 1 folds them back into three limbs.
    fn mul(self, rhs: Self) -> Self {
        let (a, b) = (self, rhs);
        let (p0, p1, p2) = (clmul(a.c0, b.c0), clmul(a.c1, b.c1), clmul(a.c2, b.c2));
        let e1 = clmul(a.c0 ^ a.c1, b.c0 ^ b.c1) ^ p0 ^ p1;
        let e2 = clmul(a.c0 ^ a.c2, b.c0 ^ b.c2) ^ p0 ^ p2 ^ p1;
        let e3 = clmul(a.c1 ^ a.c2, b.c1 ^ b.c2) ^ p1 ^ p2;
        Self::new(reduce(p0 ^ e3), reduce(e1 ^ e3 ^ p2), reduce(e2 ^ p2))
    }
}

impl Mul<K> for E {
    type Output = Self;
    fn mul(self, rhs: K) -> Self {
        Self::new(
            base_mul(self.c0, rhs.0),
            base_mul(self.c1, rhs.0),
            base_mul(self.c2, rhs.0),
        )
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
        let times_x = |value: u64| value << 1 ^ (0u64.wrapping_sub(value >> 63) & 0x1B);
        let mut tables = vec![ZERO; (3 * WINDOWS_PER_LIMB) << WINDOW];
        let mut monomial = r;
        for limb_tables in tables.as_chunks_mut::<{ WINDOWS_PER_LIMB << WINDOW }>().0 {
            let mut power = monomial;
            for table in limb_tables.as_chunks_mut::<{ 1 << WINDOW }>().0 {
                for bit in 0..WINDOW {
                    for low in 0..1 << bit {
                        table[1 << bit | low] = table[low] + power;
                    }
                    power = E::new(times_x(power.c0), times_x(power.c1), times_x(power.c2));
                }
            }
            // times y, with y^3 = y + 1.
            monomial = E::new(monomial.c2, monomial.c0 ^ monomial.c2, monomial.c1);
        }
        Self(tables)
    }

    #[inline]
    pub fn mul(&self, a: E) -> E {
        let mut product = ZERO;
        let mut table = 0;
        for limb in [a.c0, a.c1, a.c2] {
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

    /// Independent Python reference vectors: (a, b, a * b).
    const K_VECTORS: [(u64, u64, u64); 3] = [
        (0x01090913877ed8ed, 0x66ab35ac2768468f, 0x50c4519dc383744a),
        (0xa7715ae18f12a3b5, 0x05743059f43fa4f5, 0xeb64cd9cd9cda6df),
        (0xbd3efb4705e79ddd, 0x3aff618604de4ae0, 0xc3d7a95fa9cb59bb),
    ];

    /// Independent Python reference vectors: (a, b, a * b, a * a).
    type ReferenceVector = ([u64; 3], [u64; 3], [u64; 3], [u64; 3]);
    const E_VECTORS: [ReferenceVector; 4] = [
        (
            [0x950e87d7f5606615, 0x2c61275c9e6b6cf8, 0x1f00bca0042db923],
            [0x6dbca290a9eab706, 0x4c10a4fe30cffdda, 0xf26fff4cc4fd394d],
            [0x888a0fc35abaf5f6, 0x68a84cbc132b0649, 0x9fdeaf613003cabe],
            [0x8fba131ad5d46b8c, 0x1c170457f537a805, 0x3632cc098ca15135],
        ),
        (
            [0x6814a2bc786a6d2d, 0xa26b351e6c8042c5, 0x54760e7fbc051c6c],
            [0xd4c08880a5a4666d, 0x29610ae0eed8f1e7, 0xc34bd8e2fe5213e5],
            [0x2ad322ebf2f9043b, 0x8ac800aa67154c80, 0x6d0f76651d3c4d0c],
            [0xcf800ef2b83bb43a, 0xefe1c6cd064dd44c, 0x57dc5c7a60e2981b],
        ),
        (
            [0x6c50afb6e9fb123d, 0x6f28d015a2aa0b9d, 0x4e385994ebac94af],
            [0x194f9545adba52ce, 0xc675ce05588f882f, 0x57de8c051d4b7ef2],
            [0xea6b9f9d23d4a1ff, 0xd82aa6058c431457, 0x5fd4d8fda2f1e74a],
            [0x8f30fe43aa05b396, 0xe3593591eccd9efe, 0x7c5a1b128788c51f],
        ),
        (
            [0xd998efd82733e933, 0x6df216c33f8f3201, 0x11dc6f3fcb57d5d8],
            [0x8860a84722025e05, 0x33176469aa6ef630, 0x607507ebc5b864d7],
            [0xfa3a0d66cdfbc1b3, 0xbd47bd3343aad307, 0xdaf50186477f6a77],
            [0x69c8d8c24f416884, 0x4b597d648a162147, 0x95603a5d95c9512a],
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
        let e = |limbs: [u64; 3]| E::new(limbs[0], limbs[1], limbs[2]);
        for (a, b, c, s) in E_VECTORS {
            assert_eq!(e(a) * e(b), e(c));
            assert_eq!(e(a).square(), e(s));
            for value in [e(a), e(b), e(c), E::new(a[0], 0, 0), E::new(0, 0, b[2])] {
                assert_eq!(value * value.inv(), ONE);
                let sixty_four_squarings = (0..64).fold(value, |v, _| v.square());
                assert_eq!(value.frobenius(), sixty_four_squarings);
            }
            assert_eq!(e(a).pow(5), e(a).square().square() * e(a));
        }
        let y = E::new(0, 1, 0);
        assert_eq!(y * y * y, y + ONE);
        for (a, b, _, _) in E_VECTORS {
            let scaled = Scaled::new(e(a));
            for value in [e(b), y, ONE, ZERO, E::new(u64::MAX, u64::MAX, u64::MAX)] {
                assert_eq!(scaled.mul(value), e(a) * value);
            }
        }
        assert_eq!(ZERO.inv(), ZERO);
    }
}
