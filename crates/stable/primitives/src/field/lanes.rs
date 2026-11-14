//! Eight field elements at a time: the stable prover's one SIMD layer, and the only place in it that holds
//! architecture-specific code.
//!
//! - [`F128x8`]: eight `E` elements, lane `i` element `i`.
//! - [`F64x8`]: eight `K` elements.
//! - [`Acc8`]: eight unreduced `E` sums, what products land in before one reduction per lane ([`Acc8::reduce`]) or
//!   one for the whole sum ([`Acc8::sum`]).
//! - [`clmul8`]: eight carry-less 64x64 products.
//!
//! Every operation is lane by lane and agrees bit for bit with the scalar one ([`F128`], [`F64`]) on each lane, on
//! every target. A backend defines the types and their core methods; this module adds the operators, the slice
//! loads and stores, and the derived products.

use core::ops::{Add, AddAssign, Mul, MulAssign};

use super::{F64, F128};

cfg_select! {
    all(target_arch = "x86_64", target_feature = "avx2", target_feature = "vpclmulqdq") => {
        mod x86;
        pub use x86::{Acc8, F64x8, F128x8, clmul8};
    }
    _ => {
        mod portable;
        pub use portable::{Acc8, F64x8, F128x8, clmul8};
    }
}

impl F64x8 {
    /// The eight elements of `src`, which holds exactly eight.
    #[inline(always)]
    pub fn load(src: &[F64]) -> Self {
        Self::from_array(src.try_into().expect("a lane load reads eight elements"))
    }

    /// Write the eight elements over `dst`, which holds exactly eight.
    #[inline(always)]
    pub fn store(self, dst: &mut [F64]) {
        let dst: &mut [F64; 8] = dst.try_into().expect("a lane store writes eight elements");
        *dst = self.to_array();
    }
}

impl F128x8 {
    /// The eight elements of `src`, which holds exactly eight.
    #[inline(always)]
    pub fn load(src: &[F128]) -> Self {
        Self::from_array(src.try_into().expect("a lane load reads eight elements"))
    }

    /// Write the eight elements over `dst`, which holds exactly eight.
    #[inline(always)]
    pub fn store(self, dst: &mut [F128]) {
        let dst: &mut [F128; 8] = dst.try_into().expect("a lane store writes eight elements");
        *dst = self.to_array();
    }

    /// The product of every lane by one `K` scalar, which multiplies all sixteen `K` coefficients: an NTT
    /// butterfly's row of sixteen words read as eight `E` elements.
    #[inline(always)]
    pub fn mul_scalar_base(self, t: F64) -> Self {
        self.mul_base(F64x8::splat(t))
    }
}

macro_rules! additive {
    ($($t:ty),*) => {$(
        impl Add for $t {
            type Output = Self;
            #[inline(always)]
            fn add(self, rhs: Self) -> Self {
                self.xor(rhs)
            }
        }

        impl AddAssign for $t {
            #[inline(always)]
            fn add_assign(&mut self, rhs: Self) {
                *self = self.xor(rhs);
            }
        }
    )*};
}
additive!(F64x8, F128x8, Acc8);

macro_rules! multiplicative {
    ($($t:ty),*) => {$(
        impl Mul for $t {
            type Output = Self;
            #[inline(always)]
            fn mul(self, rhs: Self) -> Self {
                self.product(rhs)
            }
        }

        impl MulAssign for $t {
            #[inline(always)]
            fn mul_assign(&mut self, rhs: Self) {
                *self = self.product(rhs);
            }
        }
    )*};
}
multiplicative!(F64x8, F128x8);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::F128Unreduced;
    use crate::field::gf2_64::clmul_portable;
    use crate::test_rng::Rng;

    /// Random lanes with the reduction's corner cases mixed in.
    fn ext8(rng: &mut Rng) -> [F128; 8] {
        let mut e: [F128; 8] = core::array::from_fn(|_| rng.ext());
        e[2] = F128::new(u64::MAX, u64::MAX);
        e[5] = F128::ZERO;
        e[6] = F128::new(1 << 63, 1 << 63);
        e
    }

    fn base8(rng: &mut Rng) -> [F64; 8] {
        let mut k: [F64; 8] = core::array::from_fn(|_| F64(rng.next_u64()));
        k[1] = F64(u64::MAX);
        k[4] = F64(0xF000_0000_0000_0000);
        k
    }

    fn lanes<T>(f: impl FnMut(usize) -> T) -> [T; 8] {
        core::array::from_fn(f)
    }

    /// Every operation against the scalar field, lane by lane.
    #[test]
    fn lanes_match_scalar() {
        let mut rng = Rng::new(0x1A4E5);
        for _ in 0..500 {
            let (a, b, c) = (ext8(&mut rng), ext8(&mut rng), ext8(&mut rng));
            let (k, l) = (base8(&mut rng), base8(&mut rng));
            let (va, vb, vc) = (F128x8::from_array(&a), F128x8::from_array(&b), F128x8::from_array(&c));
            let (vk, vl) = (F64x8::from_array(&k), F64x8::from_array(&l));
            let (r, t) = (rng.ext(), F64(rng.next_u64()));

            // Moves.
            assert_eq!(va.to_array(), a);
            assert_eq!(vk.to_array(), k);
            assert_eq!(F128x8::splat(r).to_array(), [r; 8]);
            assert_eq!(F64x8::splat(t).to_array(), [t; 8]);
            assert_eq!(F128x8::ZERO.to_array(), [F128::ZERO; 8]);
            assert_eq!(F64x8::ZERO.to_array(), [F64::ZERO; 8]);
            assert_eq!(Acc8::ZERO.reduce().to_array(), [F128::ZERO; 8]);
            let (mut e, mut w) = ([F128::ZERO; 8], [F64::ZERO; 8]);
            F128x8::load(&a).store(&mut e);
            F64x8::load(&k).store(&mut w);
            assert_eq!((e, w), (a, k));

            // `K` lanes.
            assert_eq!((vk + vl).to_array(), lanes(|i| k[i] + l[i]));
            assert_eq!((vk * vl).to_array(), lanes(|i| k[i] * l[i]));
            assert_eq!((vk * F64x8::splat(t)).to_array(), lanes(|i| k[i] * t));

            // `E` lanes.
            assert_eq!((va + vb).to_array(), lanes(|i| a[i] + b[i]));
            assert_eq!((va * vb).to_array(), lanes(|i| a[i] * b[i]));
            assert_eq!((va * va).to_array(), lanes(|i| a[i].square()));
            assert_eq!(va.mul_base(vk).to_array(), lanes(|i| a[i].mul_base(k[i])));
            assert_eq!(va.mul_scalar_base(t).to_array(), lanes(|i| a[i].mul_base(t)));
            let mut x = va;
            x += vb;
            x *= vc;
            assert_eq!(x.to_array(), lanes(|i| (a[i] + b[i]) * c[i]));

            // Unreduced sums: full and mixed products, accumulated, then reduced per lane or summed.
            let mut acc = va.mul_unreduced(vb);
            acc += vc.mul_base_unreduced(vk);
            let acc = acc + vb.mul_unreduced(vc);
            let want = lanes(|i| a[i] * b[i] + c[i].mul_base(k[i]) + b[i] * c[i]);
            assert_eq!(acc.reduce().to_array(), want);
            assert_eq!(acc.sum(), want.iter().sum());
            let unreduced = (0..8).fold(F128Unreduced::ZERO, |s, i| {
                s ^ a[i].mul_unreduced(b[i]) ^ c[i].mul_base_unreduced(k[i]) ^ b[i].mul_unreduced(c[i])
            });
            assert_eq!(acc.sum(), unreduced.reduce());

            // Carry-less products.
            let (p, q) = (k.map(|k| k.0), l.map(|l| l.0));
            assert_eq!(clmul8(p, q), lanes(|i| clmul_portable(p[i], q[i])));
        }
    }

    #[test]
    #[should_panic(expected = "a lane load reads eight elements")]
    fn short_loads_panic() {
        F128x8::load(&[F128::ONE; 7]);
    }
}
