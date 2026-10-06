//! `F_p6 = F_p2[v] / (v^3 - xi)`, `xi = 9 + u`.

use crate::fp2::Fp2;

/// `c0 + c1 v + c2 v^2`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Fp6 {
    pub c0: Fp2,
    pub c1: Fp2,
    pub c2: Fp2,
}

/// `xi^((p^k - 1) / 3)` for `k` in 1..=3: the Frobenius map's factor on `v`.
const FROBENIUS_C1: [Fp2; 3] = [
    Fp2::constant(
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
    ),
    Fp2::constant(
        [
            0xe4bd_44e5_607c_fd48,
            0xc28f_069f_bb96_6e3d,
            0x5e6d_d9e7_e0ac_ccb0,
            0x3064_4e72_e131_a029,
        ],
        [0; 4],
    ),
    Fp2::constant(
        [
            0x7b74_6ee8_7bdc_fb6d,
            0x805f_fd3d_5d69_42d3,
            0xbaff_1c77_959f_25ac,
            0x0856_e078_b755_ef0a,
        ],
        [
            0x380c_ab2b_aaa5_86de,
            0x0fdf_31bf_98ff_2631,
            0xa9f3_0e6d_ec26_094f,
            0x04f1_de41_b3d1_766f,
        ],
    ),
];

/// `xi^(2 (p^k - 1) / 3)` for `k` in 1..=3: the factor on `v^2`.
const FROBENIUS_C2: [Fp2; 3] = [
    Fp2::constant(
        [
            0x848a_1f55_921e_a762,
            0xd333_65f7_be94_ec72,
            0x80f3_c0b7_5a18_1e84,
            0x05b5_4f5e_64ee_a801,
        ],
        [
            0xc13b_4711_cd2b_8126,
            0x3685_d2ea_1bde_c763,
            0x9f3a_80b0_3b0b_1c92,
            0x2c14_5edb_e7fd_8aee,
        ],
    ),
    Fp2::constant(
        [
            0x5763_4731_77ff_fffe,
            0xd4f2_63f1_acdb_5c4f,
            0x59e2_6bce_a0d4_8bac,
            0x0000_0000_0000_0000,
        ],
        [0; 4],
    ),
    Fp2::constant(
        [
            0x0e1a_92bc_3ccb_f066,
            0xe633_0945_75b0_6bcb,
            0x19be_e0f7_b5b2_444e,
            0x0bc5_8c66_11c0_8dab,
        ],
        [
            0x5fe3_ed9d_730c_239f,
            0xa44a_9e08_737f_96e5,
            0xfeb0_f6ef_0cd2_1d04,
            0x23d5_e999_e191_0a12,
        ],
    ),
];

impl Fp6 {
    pub const ZERO: Self = Self::new(Fp2::ZERO, Fp2::ZERO, Fp2::ZERO);
    pub const ONE: Self = Self::new(Fp2::ONE, Fp2::ZERO, Fp2::ZERO);

    pub const fn new(c0: Fp2, c1: Fp2, c2: Fp2) -> Self {
        Self { c0, c1, c2 }
    }

    #[inline(always)]
    pub const fn add(&self, rhs: &Self) -> Self {
        Self::new(self.c0.add(&rhs.c0), self.c1.add(&rhs.c1), self.c2.add(&rhs.c2))
    }

    #[inline(always)]
    pub const fn sub(&self, rhs: &Self) -> Self {
        Self::new(self.c0.sub(&rhs.c0), self.c1.sub(&rhs.c1), self.c2.sub(&rhs.c2))
    }

    #[inline(always)]
    pub const fn double(&self) -> Self {
        Self::new(self.c0.double(), self.c1.double(), self.c2.double())
    }

    #[inline(always)]
    pub const fn neg(&self) -> Self {
        Self::new(self.c0.neg(), self.c1.neg(), self.c2.neg())
    }

    /// The product by `v`: `v^3 = xi` wraps the top coefficient.
    #[inline(always)]
    pub const fn mul_by_v(&self) -> Self {
        Self::new(self.c2.mul_by_xi(), self.c0, self.c1)
    }

    /// Karatsuba: six products in `F_p2`.
    pub const fn mul(&self, rhs: &Self) -> Self {
        let (a, b) = (self, rhs);
        let v0 = a.c0.mul(&b.c0);
        let v1 = a.c1.mul(&b.c1);
        let v2 = a.c2.mul(&b.c2);
        let t0 = a.c1.add(&a.c2).mul(&b.c1.add(&b.c2)).sub(&v1).sub(&v2);
        let t1 = a.c0.add(&a.c1).mul(&b.c0.add(&b.c1)).sub(&v0).sub(&v1);
        let t2 = a.c0.add(&a.c2).mul(&b.c0.add(&b.c2)).sub(&v0).sub(&v2);
        Self::new(t0.mul_by_xi().add(&v0), t1.add(&v2.mul_by_xi()), t2.add(&v1))
    }

    /// Chung and Hasan's SQR2: two squares and three products in `F_p2`.
    pub const fn square(&self) -> Self {
        let s0 = self.c0.square();
        let s1 = self.c0.mul(&self.c1).double();
        let s2 = self.c0.sub(&self.c1).add(&self.c2).square();
        let s3 = self.c1.mul(&self.c2).double();
        let s4 = self.c2.square();
        Self::new(
            s3.mul_by_xi().add(&s0),
            s4.mul_by_xi().add(&s1),
            s1.add(&s2).add(&s3).sub(&s0).sub(&s4),
        )
    }

    /// Each coefficient times `k`.
    #[inline(always)]
    pub const fn mul_by_fp2(&self, k: &Fp2) -> Self {
        Self::new(self.c0.mul(k), self.c1.mul(k), self.c2.mul(k))
    }

    /// The product by `b0 + b1 v`: five products in `F_p2`.
    pub const fn mul_by_01(&self, b0: &Fp2, b1: &Fp2) -> Self {
        let v0 = self.c0.mul(b0);
        let v1 = self.c1.mul(b1);
        let t0 = self.c1.add(&self.c2).mul(b1).sub(&v1).mul_by_xi().add(&v0);
        let t1 = b0.add(b1).mul(&self.c0.add(&self.c1)).sub(&v0).sub(&v1);
        let t2 = self.c0.add(&self.c2).mul(b0).sub(&v0).add(&v1);
        Self::new(t0, t1, t2)
    }

    /// `x^(p^k)` for `k` in 1..=3.
    pub const fn frobenius(&self, k: usize) -> Self {
        Self::new(
            self.c0.frobenius(k),
            self.c1.frobenius(k).mul(&FROBENIUS_C1[k - 1]),
            self.c2.frobenius(k).mul(&FROBENIUS_C2[k - 1]),
        )
    }

    pub const fn inverse(&self) -> Option<Self> {
        let (a0, a1, a2) = (&self.c0, &self.c1, &self.c2);
        let t0 = a0.square().sub(&a1.mul(a2).mul_by_xi());
        let t1 = a2.square().mul_by_xi().sub(&a0.mul(a1));
        let t2 = a1.square().sub(&a0.mul(a2));
        let norm = a2.mul(&t1).add(&a1.mul(&t2)).mul_by_xi().add(&a0.mul(&t0));
        match norm.inverse() {
            Some(n) => Some(Self::new(t0.mul(&n), t1.mul(&n), t2.mul(&n))),
            None => None,
        }
    }
}
