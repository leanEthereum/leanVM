//! The groups: G1 is `y^2 = x^3 + 3` over `F_p`, G2 the twist `y^2 = x^3 + 3 / xi` over `F_p2`.

use crate::Error;
use crate::fp::Fp;
use crate::fp2::Fp2;
use crate::fp12::X_NAF;

/// A point of G1 as the advice holds it: canonical coordinates, little-endian limbs.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G1Point {
    pub x: [u64; 4],
    pub y: [u64; 4],
}

/// A point of G2 as the advice holds it: each coordinate `c0 + c1 u` as `[c0, c1]`, canonical.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G2Point {
    pub x: [[u64; 4]; 2],
    pub y: [[u64; 4]; 2],
}

/// `b` of G1.
const B1: Fp = Fp::constant([3, 0, 0, 0]);

/// `b` of G2: `3 / xi`.
pub const B2: Fp2 = Fp2::constant(
    [
        0x3267_e6dc_24a1_38e5,
        0xb5b4_c5e5_59db_efa3,
        0x81be_1899_1be0_6ac3,
        0x2b14_9d40_ceb8_aaae,
    ],
    [
        0xe4a2_bd06_85c3_15d2,
        0xa74f_a084_e52d_1852,
        0xcd2c_afad_eed8_fdf4,
        0x0097_13b0_3af0_fed4,
    ],
);

/// `xi^((p - 1) / 3)` and `xi^((p - 1) / 2)`: the untwist-Frobenius-twist map `psi` multiplies
/// the conjugated coordinates by them.
const PSI_X: Fp2 = Fp2::constant(
    [
        0x99e3_9557_176f_553d,
        0xb78c_c310_c2c3_330c,
        0x4c0b_ec3c_f559_b143,
        0x2fb3_4798_4f79_11f7,
    ],
    [
        0x1665_d51c_640f_cba2,
        0x32ae_2a1d_0b7c_9dce,
        0x4ba4_cc8b_d75a_0794,
        0x16c9_e550_61eb_ae20,
    ],
);
const PSI_Y: Fp2 = Fp2::constant(
    [
        0xdc54_0146_71a0_135a,
        0xdbaa_e0ed_a9c9_5998,
        0xdc5e_c698_b6e2_f9b9,
        0x063c_f305_489a_f5dc,
    ],
    [
        0x82d3_7f63_2623_b0e3,
        0x2180_7dc9_8fa2_5bd2,
        0x0704_b5a7_ec79_6f2b,
        0x07c0_3cbc_ac41_049a,
    ],
);

/// An affine point of G1, never the point at infinity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G1Affine {
    pub x: Fp,
    pub y: Fp,
}

impl G1Affine {
    /// A placeholder, for arrays filled before they are read.
    pub const ZERO: Self = Self {
        x: Fp::ZERO,
        y: Fp::ZERO,
    };

    /// A constant's point, checked on the curve at compile time.
    pub const fn constant(point: &G1Point) -> Self {
        let p = Self {
            x: Fp::constant(point.x),
            y: Fp::constant(point.y),
        };
        assert!(p.is_on_curve(), "a constant on G1");
        p
    }

    const fn is_on_curve(&self) -> bool {
        let lhs = self.y.square();
        let rhs = self.x.square().mul(&self.x).add(&B1);
        lhs.sub(&rhs).is_zero()
    }

    /// The advice's point, refused unless its coordinates are below `p` and it is on the curve:
    /// so the point at infinity, which EIP-197 writes `(0, 0)`, is refused too. G1 has cofactor
    /// one, so it is in the group.
    pub fn from_point(point: &G1Point) -> Result<Self, Error> {
        let p = Self {
            x: Fp::from_canonical(point.x).ok_or(Error::NotInField)?,
            y: Fp::from_canonical(point.y).ok_or(Error::NotInField)?,
        };
        if p.is_on_curve() { Ok(p) } else { Err(Error::NotOnCurve) }
    }
}

/// An affine point of G2, never the point at infinity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G2Affine {
    pub x: Fp2,
    pub y: Fp2,
}

impl G2Affine {
    /// A constant's point, checked on the curve at compile time.
    pub const fn constant(point: &G2Point) -> Self {
        let p = Self {
            x: Fp2::constant(point.x[0], point.x[1]),
            y: Fp2::constant(point.y[0], point.y[1]),
        };
        assert!(p.is_on_curve(), "a constant on G2");
        p
    }

    const fn is_on_curve(&self) -> bool {
        let lhs = self.y.square();
        let rhs = self.x.square().mul(&self.x).add(&B2);
        lhs.sub(&rhs).is_zero()
    }

    /// The advice's point, refused unless its coordinates are below `p`, it is on the twist and
    /// in G2, the subgroup of order `r`.
    ///
    /// The subgroup test is El Housni, Guillevic and Piellard's for BN254 ("Co-factor clearing
    /// and subgroup membership testing on pairing-friendly curves", 2022): `Q` is in G2 exactly
    /// when `[x + 1] Q + psi([x] Q) + psi^2([x] Q) = psi^3([2 x] Q)`.
    pub fn from_point(point: &G2Point) -> Result<Self, Error> {
        let coordinate = |c: &[[u64; 4]; 2]| -> Result<Fp2, Error> {
            Ok(Fp2::new(
                Fp::from_canonical(c[0]).ok_or(Error::NotInField)?,
                Fp::from_canonical(c[1]).ok_or(Error::NotInField)?,
            ))
        };
        let q = Self {
            x: coordinate(&point.x)?,
            y: coordinate(&point.y)?,
        };
        if !q.is_on_curve() {
            return Err(Error::NotOnCurve);
        }
        let xq = G2Jacobian::mul_by_x(&q);
        let lhs = xq.add_affine(&q).add(&xq.psi()).add(&xq.psi().psi());
        let rhs = xq.double().psi().psi().psi();
        if lhs.equals(&rhs) {
            Ok(q)
        } else {
            Err(Error::NotInSubgroup)
        }
    }

    pub const fn neg(&self) -> Self {
        Self {
            x: self.x,
            y: self.y.neg(),
        }
    }

    /// `psi`, the endomorphism of the twist that acts on G2 as `p`, the Frobenius map.
    pub const fn psi(&self) -> Self {
        Self {
            x: self.x.conjugate().mul(&PSI_X),
            y: self.y.conjugate().mul(&PSI_Y),
        }
    }
}

/// A Jacobian point type over a field and its affine points: `(X / Z^2, Y / Z^3)`, the point at
/// infinity having `Z = 0`.
macro_rules! jacobian {
    ($name:ident, $field:ty, $affine:ty) => {
        #[derive(Clone, Copy, Debug)]
        pub struct $name {
            x: $field,
            y: $field,
            z: $field,
        }

        impl $name {
            pub const INFINITY: Self = Self {
                x: <$field>::ONE,
                y: <$field>::ONE,
                z: <$field>::ZERO,
            };

            pub const fn from_affine(p: &$affine) -> Self {
                Self {
                    x: p.x,
                    y: p.y,
                    z: <$field>::ONE,
                }
            }

            pub const fn is_infinity(&self) -> bool {
                self.z.is_zero()
            }

            /// `dbl-2009-l`: two products and five squares.
            pub const fn double(&self) -> Self {
                let a = self.x.square();
                let b = self.y.square();
                let c = b.square();
                let d = self.x.add(&b).square().sub(&a).sub(&c).double();
                let e = a.double().add(&a);
                let f = e.square();
                let x = f.sub(&d.double());
                let y = e.mul(&d.sub(&x)).sub(&c.double().double().double());
                let z = self.y.mul(&self.z).double();
                Self { x, y, z }
            }

            /// The sum with an affine point, `madd-2007-bl`: seven products and four squares.
            pub const fn add_affine(&self, p: &$affine) -> Self {
                if self.is_infinity() {
                    return Self::from_affine(p);
                }
                let z1z1 = self.z.square();
                let u2 = p.x.mul(&z1z1);
                let s2 = p.y.mul(&self.z).mul(&z1z1);
                let h = u2.sub(&self.x);
                let r = s2.sub(&self.y).double();
                if h.is_zero() {
                    // The same x: the same point, or its opposite.
                    return if r.is_zero() {
                        self.double()
                    } else {
                        Self::INFINITY
                    };
                }
                let hh = h.square();
                let i = hh.double().double();
                let j = h.mul(&i);
                let v = self.x.mul(&i);
                let x = r.square().sub(&j).sub(&v.double());
                let y = r.mul(&v.sub(&x)).sub(&self.y.mul(&j).double());
                let z = self.z.add(&h).square().sub(&z1z1).sub(&hh);
                Self { x, y, z }
            }
        }
    };
}

jacobian!(G1Jacobian, Fp, G1Affine);
jacobian!(G2Jacobian, Fp2, G2Affine);

impl G1Jacobian {
    /// The affine point, or `None` at infinity.
    pub const fn to_affine(self) -> Option<G1Affine> {
        match self.z.inverse() {
            Some(z_inv) => {
                let z_inv2 = z_inv.square();
                Some(G1Affine {
                    x: self.x.mul(&z_inv2),
                    y: self.y.mul(&z_inv2.mul(&z_inv)),
                })
            }
            None => None,
        }
    }

    /// `[k] p` for `k` in `1..=N`, affine: one inversion for all, by Montgomery's trick.
    pub const fn multiples<const N: usize>(p: &G1Affine) -> [G1Affine; N] {
        let mut points = [Self::INFINITY; N];
        points[0] = Self::from_affine(p);
        let mut k = 1;
        while k < N {
            points[k] = points[k - 1].add_affine(p);
            k += 1;
        }
        // prefix[k] is the product of the z's before k.
        let mut prefix = [Fp::ONE; N];
        let mut acc = Fp::ONE;
        k = 0;
        while k < N {
            prefix[k] = acc;
            acc = acc.mul(&points[k].z);
            k += 1;
        }
        let mut inverse = match acc.inverse() {
            Some(inverse) => inverse,
            None => panic!("no multiple is at infinity"),
        };
        let mut out = [G1Affine::ZERO; N];
        while k > 0 {
            k -= 1;
            let z_inv = inverse.mul(&prefix[k]);
            inverse = inverse.mul(&points[k].z);
            let z_inv2 = z_inv.square();
            out[k] = G1Affine {
                x: points[k].x.mul(&z_inv2),
                y: points[k].y.mul(&z_inv2.mul(&z_inv)),
            };
        }
        out
    }
}

impl G2Jacobian {
    /// Whether both are the same point.
    pub const fn equals(&self, other: &Self) -> bool {
        if self.is_infinity() || other.is_infinity() {
            return self.is_infinity() && other.is_infinity();
        }
        let (z1z1, z2z2) = (self.z.square(), other.z.square());
        self.x.mul(&z2z2).sub(&other.x.mul(&z1z1)).is_zero()
            && self
                .y
                .mul(&z2z2.mul(&other.z))
                .sub(&other.y.mul(&z1z1.mul(&self.z)))
                .is_zero()
    }

    /// The sum, `add-2007-bl`: eleven products and five squares.
    pub const fn add(&self, other: &Self) -> Self {
        if self.is_infinity() {
            return *other;
        }
        if other.is_infinity() {
            return *self;
        }
        let z1z1 = self.z.square();
        let z2z2 = other.z.square();
        let u1 = self.x.mul(&z2z2);
        let u2 = other.x.mul(&z1z1);
        let s1 = self.y.mul(&other.z).mul(&z2z2);
        let s2 = other.y.mul(&self.z).mul(&z1z1);
        let h = u2.sub(&u1);
        let r = s2.sub(&s1).double();
        if h.is_zero() {
            return if r.is_zero() { self.double() } else { Self::INFINITY };
        }
        let i = h.double().square();
        let j = h.mul(&i);
        let v = u1.mul(&i);
        let x = r.square().sub(&j).sub(&v.double());
        let y = r.mul(&v.sub(&x)).sub(&s1.mul(&j).double());
        let z = self.z.add(&other.z).square().sub(&z1z1).sub(&z2z2).mul(&h);
        Self { x, y, z }
    }

    /// `psi`, on Jacobian coordinates: the conjugate of `Z` keeps them consistent.
    const fn psi(&self) -> Self {
        Self {
            x: self.x.conjugate().mul(&PSI_X),
            y: self.y.conjugate().mul(&PSI_Y),
            z: self.z.conjugate(),
        }
    }

    /// `[x] q`, `x` the BN parameter, by its signed digits.
    fn mul_by_x(q: &G2Affine) -> Self {
        let neg = q.neg();
        let mut acc = Self::from_affine(q);
        for digit in X_NAF[..X_NAF.len() - 1].iter().rev() {
            acc = acc.double();
            match digit {
                1 => acc = acc.add_affine(q),
                -1 => acc = acc.add_affine(&neg),
                _ => {}
            }
        }
        acc
    }
}
