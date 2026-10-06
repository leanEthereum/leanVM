//! `F_p12 = F_p6[w] / (w^2 - v)`, where the pairing takes its values.

use crate::fp2::Fp2;
use crate::fp6::Fp6;

/// `c0 + c1 w`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Fp12 {
    pub c0: Fp6,
    pub c1: Fp6,
}

/// `xi^((p^k - 1) / 6)` for `k` in 1..=3: the Frobenius map's factor on `w`.
const FROBENIUS_C1: [Fp2; 3] = [
    Fp2::constant(
        [
            0xd60b_35da_dcc9_e470,
            0x5c52_1e08_292f_2176,
            0xe8b9_9fdd_76e6_8b60,
            0x1284_b71c_2865_a7df,
        ],
        [
            0xca5c_f05f_80f3_62ac,
            0x7479_9277_8eee_c7e5,
            0xa632_7cfe_1215_0b8e,
            0x2469_96f3_b4fa_e7e6,
        ],
    ),
    Fp2::constant(
        [
            0xe4bd_44e5_607c_fd49,
            0xc28f_069f_bb96_6e3d,
            0x5e6d_d9e7_e0ac_ccb0,
            0x3064_4e72_e131_a029,
        ],
        [0; 4],
    ),
    Fp2::constant(
        [
            0xe86f_7d39_1ed4_a67f,
            0x894c_b38d_be55_d24a,
            0xefe9_608c_d0ac_aa90,
            0x19dc_81cf_cc82_e4bb,
        ],
        [
            0x7694_aa2b_f4c0_c101,
            0x7f03_a5e3_97d4_39ec,
            0x06cb_eee3_3576_139d,
            0x00ab_f8b6_0be7_7d73,
        ],
    ),
];

/// `x = 4965661367192848881`, the BN parameter, in non-adjacent form, least significant digit first.
pub(crate) const X_NAF: [i8; 63] = [
    1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, -1,
    0, -1, 0, -1, 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 1,
];

impl Fp12 {
    pub const ONE: Self = Self::new(Fp6::ONE, Fp6::ZERO);

    pub const fn new(c0: Fp6, c1: Fp6) -> Self {
        Self { c0, c1 }
    }

    /// Karatsuba: three products in `F_p6`.
    pub const fn mul(&self, rhs: &Self) -> Self {
        let v0 = self.c0.mul(&rhs.c0);
        let v1 = self.c1.mul(&rhs.c1);
        let c1 = self.c0.add(&self.c1).mul(&rhs.c0.add(&rhs.c1)).sub(&v0).sub(&v1);
        Self::new(v0.add(&v1.mul_by_v()), c1)
    }

    /// The complex method: two products in `F_p6`.
    pub const fn square(&self) -> Self {
        let v2 = self.c0.mul(&self.c1);
        let v0 = self.c0.sub(&self.c1).mul(&self.c0.sub(&self.c1.mul_by_v())).add(&v2);
        Self::new(v0.add(&v2.mul_by_v()), v2.double())
    }

    /// `c0 - c1 w`, `x^(p^6)`: the inverse of an element of the cyclotomic subgroup.
    pub const fn conjugate(&self) -> Self {
        Self::new(self.c0, self.c1.neg())
    }

    /// `(c0 - c1 w) / (c0^2 - v c1^2)`; zero has none.
    pub const fn inverse(&self) -> Option<Self> {
        match self.c0.square().sub(&self.c1.square().mul_by_v()).inverse() {
            Some(t) => Some(Self::new(self.c0.mul(&t), self.c1.mul(&t).neg())),
            None => None,
        }
    }

    /// `x^(p^k)` for `k` in 1..=3.
    pub const fn frobenius(&self, k: usize) -> Self {
        let c1 = self.c1.frobenius(k).mul_by_fp2(&FROBENIUS_C1[k - 1]);
        Self::new(self.c0.frobenius(k), c1)
    }

    /// The product by a line's value `a0 + (a3 + a4 v) w`, sparse: three of the six coefficients.
    pub const fn mul_by_034(&self, a0: &Fp2, a3: &Fp2, a4: &Fp2) -> Self {
        let a = self.c0.mul_by_fp2(a0);
        let b = self.c1.mul_by_01(a3, a4);
        let e = self.c0.add(&self.c1).mul_by_01(&a0.add(a3), a4);
        Self::new(b.mul_by_v().add(&a), e.sub(&a.add(&b)))
    }

    /// The product by a normalized line's value `1 + (a3 + a4 v) w`.
    pub const fn mul_by_34(&self, a3: &Fp2, a4: &Fp2) -> Self {
        let b = self.c1.mul_by_01(a3, a4);
        let e = self.c0.add(&self.c1).mul_by_01(&a3.add(&Fp2::ONE), a4);
        Self::new(b.mul_by_v().add(&self.c0), e.sub(&self.c0.add(&b)))
    }

    /// Granger and Scott's square, for an element of the cyclotomic subgroup: six squares in `F_p2`.
    pub const fn cyclotomic_square(&self) -> Self {
        let (r0, r4, r3) = (&self.c0.c0, &self.c0.c1, &self.c0.c2);
        let (r2, r1, r5) = (&self.c1.c0, &self.c1.c1, &self.c1.c2);

        // (t0 + t1 y) = (r0 + r1 y)^2, y^2 = xi, and likewise the other two pairs.
        let (t0, t1) = square_pair(r0, r1);
        let (t2, t3) = square_pair(r2, r3);
        let (t4, t5) = square_pair(r4, r5);

        let z0 = triple_minus_double(&t0, r0);
        let z1 = triple_plus_double(&t1, r1);
        let z2 = triple_plus_double(&t5.mul_by_xi(), r2);
        let z3 = triple_minus_double(&t4, r3);
        let z4 = triple_minus_double(&t2, r4);
        let z5 = triple_plus_double(&t3, r5);
        Self::new(Fp6::new(z0, z4, z3), Fp6::new(z2, z1, z5))
    }

    /// `self^x`, for an element of the cyclotomic subgroup, where the inverse is the conjugate.
    pub const fn cyclotomic_exp_by_x(&self) -> Self {
        let inverse = self.conjugate();
        let mut acc = *self;
        let mut i = X_NAF.len() - 1;
        while i > 0 {
            i -= 1;
            acc = acc.cyclotomic_square();
            match X_NAF[i] {
                1 => acc = acc.mul(self),
                -1 => acc = acc.mul(&inverse),
                _ => {}
            }
        }
        acc
    }

    /// `self^((p^12 - 1) / r)`, Fuentes-Castaneda, Knapp and Rodriguez-Henriquez's chain for
    /// the hard part, as arkworks writes it; zero has none.
    pub const fn final_exponentiation(&self) -> Option<Self> {
        // The easy part, f^((p^6 - 1)(p^2 + 1)), lands in the cyclotomic subgroup.
        let inverse = match self.inverse() {
            Some(inverse) => inverse,
            None => return None,
        };
        let f = self.conjugate().mul(&inverse);
        let r = f.frobenius(2).mul(&f);

        // The hard part.
        let y0 = r.cyclotomic_exp_by_x().conjugate();
        let y1 = y0.cyclotomic_square();
        let y2 = y1.cyclotomic_square();
        let y3 = y2.mul(&y1);
        let y4 = y3.cyclotomic_exp_by_x().conjugate();
        let y5 = y4.cyclotomic_square();
        let y6 = y5.cyclotomic_exp_by_x().conjugate();
        let y3 = y3.conjugate();
        let y6 = y6.conjugate();
        let y7 = y6.mul(&y4);
        let y8 = y7.mul(&y3);
        let y9 = y8.mul(&y1);
        let y10 = y8.mul(&y4);
        let y11 = y10.mul(&r);
        let y13 = y9.frobenius(1).mul(&y11);
        let y14 = y8.frobenius(2).mul(&y13);
        let y15 = r.conjugate().mul(&y9).frobenius(3);
        Some(y15.mul(&y14))
    }
}

/// `(a + b y)^2` with `y^2 = xi`: `(a^2 + xi b^2, 2 a b)`, from one product and one square.
#[inline(always)]
const fn square_pair(a: &Fp2, b: &Fp2) -> (Fp2, Fp2) {
    let ab = a.mul(b);
    let s = a.add(b).mul(&b.mul_by_xi().add(a)).sub(&ab).sub(&ab.mul_by_xi());
    (s, ab.double())
}

/// `3 t - 2 r`.
#[inline(always)]
const fn triple_minus_double(t: &Fp2, r: &Fp2) -> Fp2 {
    t.sub(r).double().add(t)
}

/// `3 t + 2 r`.
#[inline(always)]
const fn triple_plus_double(t: &Fp2, r: &Fp2) -> Fp2 {
    t.add(r).double().add(t)
}
