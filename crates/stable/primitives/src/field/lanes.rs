//! Eight field elements at a time: the stable prover's one SIMD layer, and the only place in it that holds
//! architecture-specific code.
//!
//! - [`F128x8`]: eight `E` elements, lane `i` element `i`.
//! - [`F64x8`]: eight `K` elements.
//! - [`Acc8`]: eight unreduced `E` sums, what products land in before one reduction per lane ([`Acc8::reduce`]) or
//!   one for the whole sum ([`Acc8::sum`]), or read as they are ([`Acc8::to_array`]).
//! - [`clmul8`]: eight carry-less 64x64 products, and [`clmul8_low`] their low halves, for products known to fit 64
//!   bits; [`Wide8`], sums of such products.
//! - 64 bytes at a time: [`map_bytes`], a GF(2)-linear map of bytes ([`ByteMap`]); [`map_fields`], one from 16 bits
//!   to 32 ([`Linear16`]) on the 16-bit fields of eight words; and the transposes [`transpose_words`],
//!   [`transpose_bits`] and [`transpose_bytes`].
//!
//! Every operation is lane by lane and agrees bit for bit with the scalar one ([`F128`], [`F64`]) on each lane, on
//! every target. A backend defines the types and their core methods; this module adds the operators, the slice
//! loads and stores, and the derived products.

use core::ops::{Add, AddAssign, Mul, MulAssign};

use super::{F64, F128};

mod bytes;

cfg_select! {
    all(target_arch = "x86_64", target_feature = "avx2", target_feature = "vpclmulqdq") => {
        mod x86;
        use x86 as backend;
    }
    all(target_arch = "aarch64", target_feature = "aes") => {
        mod neon;
        use neon as backend;
    }
    _ => {
        mod portable;
        use portable as backend;
    }
}
pub(crate) use backend::mul;
pub use backend::{
    Acc8, F64x8, F128x8, Wide8, clmul8, clmul8_low, map_bytes, map_fields, transpose_bits, transpose_bytes,
    transpose_words,
};

/// A GF(2)-linear map of bytes, held in the one form its backend applies: where x86 has GFNI, GF2P8AFFINEQB's
/// matrix, bit `c` of byte `7 - k` being bit `k` of the image of bit `c`; elsewhere the images of the sixteen values
/// of the low nibble and of the high one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteMap {
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "vpclmulqdq",
        target_feature = "gfni"
    ))]
    matrix: u64,
    #[cfg(not(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "vpclmulqdq",
        target_feature = "gfni"
    )))]
    nibbles: [[u8; 16]; 2],
}

impl ByteMap {
    /// The map sending bit `c` to `images[c]`.
    pub const fn new(images: [u8; 8]) -> Self {
        cfg_select! {
            all(target_arch = "x86_64", target_feature = "avx2", target_feature = "vpclmulqdq", target_feature = "gfni") => {
                let mut matrix = 0u64;
                let mut c = 0;
                while c < 8 {
                    let mut k = 0;
                    while k < 8 {
                        matrix |= ((images[c] >> k & 1) as u64) << (c + 8 * (7 - k));
                        k += 1;
                    }
                    c += 1;
                }
                Self { matrix }
            }
            _ => {
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
    }
}

/// A GF(2)-linear map from 16 bits to 32, held in the forms the backends apply it in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Linear16 {
    /// The images of the 256 values of the low byte and of the high one.
    bytes: [[u32; 256]; 2],
    /// Byte `o` of the images of the sixteen values of nibble `n`, at `[o][n]`.
    nibbles: [[[u8; 16]; 4]; 4],
}

impl Linear16 {
    /// The map sending bit `t` to `images[t]`.
    pub const fn new(images: [u32; 16]) -> Self {
        let mut bytes = [[0u32; 256]; 2];
        let mut nibbles = [[[0u8; 16]; 4]; 4];
        let mut t = 0;
        while t < 16 {
            let mut v = 0;
            while v < 256 {
                if v >> (t % 8) & 1 == 1 {
                    bytes[t / 8][v] ^= images[t];
                }
                if v < 16 && v >> (t % 4) & 1 == 1 {
                    let mut o = 0;
                    while o < 4 {
                        nibbles[o][t / 4][v] ^= (images[t] >> (8 * o)) as u8;
                        o += 1;
                    }
                }
                v += 1;
            }
            t += 1;
        }
        Self { bytes, nibbles }
    }

    /// The image of `x`.
    #[inline(always)]
    pub fn apply(&self, x: u16) -> u32 {
        self.bytes[0][x as usize & 0xff] ^ self.bytes[1][x as usize >> 8]
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
additive!(F64x8, F128x8, Acc8, Wide8);

impl Wide8 {
    /// The sum of the eight lanes.
    #[inline(always)]
    pub fn sum(self) -> u128 {
        self.to_array().into_iter().fold(0, |a, b| a ^ b)
    }
}

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
            let products = va.mul_unreduced(vb) + vc.mul_base_unreduced(vk);
            let want = lanes(|i| a[i].mul_unreduced(b[i]) ^ c[i].mul_base_unreduced(k[i]));
            assert_eq!(products.to_array(), want);

            // Carry-less products.
            let (p, q) = (k.map(|k| k.0), l.map(|l| l.0));
            assert_eq!(clmul8(p, q), lanes(|i| clmul_portable(p[i], q[i])));
            assert_eq!(clmul8_low(p, q), lanes(|i| clmul_portable(p[i], q[i]) as u64));
            let wide = Wide8::mul(p, q) + Wide8::mul(q, q);
            let want = lanes(|i| clmul_portable(p[i], q[i]) ^ clmul_portable(q[i], q[i]));
            assert_eq!((wide.to_array(), wide.sum()), (want, want.iter().fold(0, |a, b| a ^ b)));
        }
    }

    /// The byte operations against their definitions, bit by bit.
    #[test]
    fn byte_operations_match_their_definitions() {
        let mut rng = Rng::new(0xB17E5);
        let word = |rng: &mut Rng| -> [u64; 8] { core::array::from_fn(|_| rng.next_u64()) };
        let bytes = |x: &[u64; 8]| -> [u8; 64] { core::array::from_fn(|n| (x[n / 8] >> (8 * (n % 8))) as u8) };
        for _ in 0..200 {
            let images: [u8; 8] = core::array::from_fn(|_| rng.next_u64() as u8);
            let x = word(&mut rng);
            let image = |b: u8| (0..8).filter(|c| b >> c & 1 == 1).fold(0, |a, c| a ^ images[c]);
            assert_eq!(bytes(&map_bytes(&ByteMap::new(images), x)), bytes(&x).map(image));

            let images: [u32; 16] = core::array::from_fn(|_| rng.next_u64() as u32);
            let image = |v: u64| (0..16).filter(|t| v >> t & 1 == 1).fold(0, |a, t| a ^ images[t]);
            let m = Linear16::new(images);
            assert_eq!(
                map_fields(&m, x),
                core::array::from_fn(|f| x.map(|w| u64::from(image(w >> (16 * f) & 0xffff))))
            );

            let rows: [[u64; 8]; 8] = core::array::from_fn(|_| word(&mut rng));
            assert_eq!(
                transpose_words(&rows),
                core::array::from_fn(|c| core::array::from_fn(|r| rows[r][c]))
            );

            let t = bytes(&transpose_bits(x));
            for (n, k) in (0..64).flat_map(|n| (0..8).map(move |k| (n, k))) {
                assert_eq!(t[n] >> k & 1, (x[k] >> n & 1) as u8, "bit {k} of byte {n}");
            }

            let rows: [[u64; 8]; 16] = core::array::from_fn(|_| word(&mut rng));
            let t = transpose_bytes(&rows);
            for (n, b) in (0..64).flat_map(|n| (0..16).map(move |b| (n, b))) {
                assert_eq!((t[n] >> (8 * b)) as u8, bytes(&rows[b])[n], "byte {b} of {n}");
            }
        }
    }

    #[test]
    #[should_panic(expected = "a lane load reads eight elements")]
    fn short_loads_panic() {
        F128x8::load(&[F128::ONE; 7]);
    }
}
