//! The base field `F_p` of BN254, in Montgomery form over four 64-bit limbs.
//!
//! Every function is `const`, so that the constants derived from the verification key (the
//! fixed points' lines, `e(alpha, beta)`'s Miller loop) are computed at compile time.

/// `p`, little-endian limbs: below `2^254`, its top limb below `2^63 - 1`, so a Montgomery
/// product needs no carry past the top limb (`mul`).
pub const MODULUS: [u64; 4] = [
    0x3c20_8c16_d87c_fd47,
    0x9781_6a91_6871_ca8d,
    0xb850_45b6_8181_585d,
    0x3064_4e72_e131_a029,
];

/// `-p^-1 mod 2^64`.
const INV: u64 = 0x87d2_0782_e486_6389;

/// `R mod p`, `R = 2^256`: one in Montgomery form.
const R: [u64; 4] = [
    0xd35d_438d_c58f_0d9d,
    0x0a78_eb28_f5c7_0b3d,
    0x666e_a36f_7879_462c,
    0x0e0a_77c1_9a07_df2f,
];

/// `R^2 mod p`: a canonical value times it is its Montgomery form.
const R2: Fp = Fp([
    0xf32c_fc5b_538a_fa89,
    0xb5e7_1911_d445_01fb,
    0x47ab_1eff_0a41_7ff6,
    0x06d8_9f71_cab8_351f,
]);

/// `p - 2`, the exponent of Fermat's inverse.
const P_MINUS_2: [u64; 4] = [MODULUS[0] - 2, MODULUS[1], MODULUS[2], MODULUS[3]];

/// An element `a` of `F_p` as `a R mod p`, always below `p`, so equal elements have equal limbs.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Fp([u64; 4]);

/// `a + b * c + carry`, as its low and high words.
#[inline(always)]
const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 * c as u128 + carry as u128;
    (t as u64, (t >> 64) as u64)
}

/// `a + b + carry`, as the sum and its carry.
#[inline(always)]
const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 + carry as u128;
    (t as u64, (t >> 64) as u64)
}

/// `a - b - borrow`, as the difference and its borrow (0 or 1).
#[inline(always)]
const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let (d, b1) = a.overflowing_sub(b);
    let (d, b2) = d.overflowing_sub(borrow);
    (d, (b1 | b2) as u64)
}

/// `a - b` over four limbs, and whether it borrowed.
#[inline(always)]
const fn sub4(a: &[u64; 4], b: &[u64; 4]) -> ([u64; 4], bool) {
    let (d0, c) = sbb(a[0], b[0], 0);
    let (d1, c) = sbb(a[1], b[1], c);
    let (d2, c) = sbb(a[2], b[2], c);
    let (d3, c) = sbb(a[3], b[3], c);
    ([d0, d1, d2, d3], c != 0)
}

/// `a` below `2p`, reduced below `p`.
#[inline(always)]
const fn reduce(a: [u64; 4]) -> [u64; 4] {
    match sub4(&a, &MODULUS) {
        (_, true) => a,
        (d, false) => d,
    }
}

impl Fp {
    pub const ZERO: Self = Self([0; 4]);
    pub const ONE: Self = Self(R);

    /// The element of canonical limbs `a`, or `None` if `a` is not below `p`.
    pub const fn from_canonical(a: [u64; 4]) -> Option<Self> {
        match sub4(&a, &MODULUS) {
            (_, true) => Some(Self(a).mul(&R2)),
            (_, false) => None,
        }
    }

    /// A constant's element, its canonical limbs below `p`.
    pub const fn constant(a: [u64; 4]) -> Self {
        match Self::from_canonical(a) {
            Some(x) => x,
            None => panic!("a constant below p"),
        }
    }

    pub const fn is_zero(&self) -> bool {
        self.0[0] | self.0[1] | self.0[2] | self.0[3] == 0
    }

    #[inline(always)]
    pub const fn add(&self, rhs: &Self) -> Self {
        // Both are below p < 2^254, so the sum fits four limbs.
        let (s0, c) = adc(self.0[0], rhs.0[0], 0);
        let (s1, c) = adc(self.0[1], rhs.0[1], c);
        let (s2, c) = adc(self.0[2], rhs.0[2], c);
        let (s3, _) = adc(self.0[3], rhs.0[3], c);
        Self(reduce([s0, s1, s2, s3]))
    }

    #[inline(always)]
    pub const fn double(&self) -> Self {
        self.add(self)
    }

    #[inline(always)]
    pub const fn sub(&self, rhs: &Self) -> Self {
        match sub4(&self.0, &rhs.0) {
            (d, false) => Self(d),
            (d, true) => {
                let (s0, c) = adc(d[0], MODULUS[0], 0);
                let (s1, c) = adc(d[1], MODULUS[1], c);
                let (s2, c) = adc(d[2], MODULUS[2], c);
                let (s3, _) = adc(d[3], MODULUS[3], c);
                Self([s0, s1, s2, s3])
            }
        }
    }

    #[inline(always)]
    pub const fn neg(&self) -> Self {
        if self.is_zero() {
            *self
        } else {
            Self(sub4(&MODULUS, &self.0).0)
        }
    }

    /// The Montgomery product `a b R^-1`: CIOS with no carry word, which `p`'s spare top bits allow.
    #[inline(always)]
    pub const fn mul(&self, rhs: &Self) -> Self {
        let (a, b) = (&self.0, &rhs.0);
        let mut t = [0u64; 4];
        let mut i = 0;
        while i < 4 {
            let (t0, mut c) = mac(t[0], a[0], b[i], 0);
            let m = t0.wrapping_mul(INV);
            // t0 + m p0 is zero mod 2^64 by the choice of m: its low word is known, and it
            // carries exactly when t0 is not zero.
            let mut d = ((m as u128 * MODULUS[0] as u128) >> 64) as u64 + (t0 != 0) as u64;
            let mut j = 1;
            while j < 4 {
                let (tj, cj) = mac(t[j], a[j], b[i], c);
                let (tm, dj) = mac(tj, m, MODULUS[j], d);
                t[j - 1] = tm;
                (c, d) = (cj, dj);
                j += 1;
            }
            t[3] = c + d;
            i += 1;
        }
        Self(reduce(t))
    }

    #[inline(always)]
    pub const fn square(&self) -> Self {
        self.mul(self)
    }

    /// `self^e`, `e` little-endian limbs.
    pub const fn pow(&self, e: &[u64; 4]) -> Self {
        let mut acc = Self::ONE;
        let mut i = 256;
        while i > 0 {
            i -= 1;
            acc = acc.square();
            if (e[i / 64] >> (i % 64)) & 1 == 1 {
                acc = acc.mul(self);
            }
        }
        acc
    }

    /// The inverse, by Fermat; zero has none.
    pub const fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            Some(self.pow(&P_MINUS_2))
        }
    }
}
