//! Eight field elements at a time: the stable prover's one SIMD layer, and the only code in it that names an
//! architecture.
//!
//! Lanes of field elements, lane `i` holding element `i`:
//! - [`F64x8`]: eight `K` elements, with `+` and `*`.
//! - [`F128x8`]: eight `E` elements, with `+`, `*` and the mixed product by eight `K` elements ([`F128x8::mul_base`]).
//! - [`Acc8`]: eight unreduced `E` sums. [`F128x8::mul_unreduced`] and [`F128x8::mul_base_unreduced`] land products
//!   here, `+` adds them, and one reduction ends a sum of many: per lane ([`Acc8::reduce`]) or of all eight
//!   ([`Acc8::sum`]).
//! - [`Wide8`]: eight sums of 128-bit carry-less products of words, for polynomials no reduction may touch; and
//!   [`clmul8_low`], the low halves of eight such products, for products known to fit 64 bits.
//!
//! Byte operations, on 64 bytes held as eight words:
//! - [`map_bytes`]: every byte through one GF(2)-linear map ([`ByteMap`]).
//! - [`map_fields`]: every 16-bit field through one GF(2)-linear map to 32 bits ([`Linear16`]).
//! - [`transpose_words`], [`transpose_bits`], [`transpose_bytes`]: 8 by 8 words, 8 by 64 bits, 16 by 64 bytes.
//!
//! One element at a time: [`mul_wide`], the carry-less product every field product is built from, and the backend's
//! `E` product, which `F128 * F128` calls.
//!
//! Each operation has one portable body (`portable.rs`, plain scalar code), which defines it: it is the backend of a
//! target without a vector carry-less multiplier, and the tests hold every vector arm to it, bit for bit. The vector
//! backends are `x86.rs` (AVX2 or AVX-512, with VPCLMULQDQ, and GFNI for the byte maps and the bit transpose) and
//! `neon.rs` (aarch64 with PMULL); each reuses the portable body of an operation it has no arm for. This module adds
//! what follows from a backend's core: the operators, the slice loads and stores, and the reduced products.

use core::ops::{Add, AddAssign, Mul, MulAssign};

use super::{F64, F128};

#[allow(dead_code, reason = "a vector backend uses only the bodies it has no arm for")]
mod portable;

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
        use portable as backend;
    }
}
pub(crate) use backend::mul;
pub use backend::{
    Acc8, ByteMap, F64x8, F128x8, Wide8, clmul8_low, map_bytes, map_fields, transpose_bits, transpose_bytes,
    transpose_words,
};

/// The carry-less product of two 64-bit polynomials: PMULL on aarch64, PCLMULQDQ on x86-64, the portable schoolbook
/// elsewhere. Its own arms rather than the backend's, as x86-64 has PCLMULQDQ well before VPCLMULQDQ.
#[inline(always)]
pub fn mul_wide(a: u64, b: u64) -> u128 {
    cfg_select! {
        all(target_arch = "aarch64", target_feature = "aes") => {
            // SAFETY: the cfg enables aes, which carries PMULL.
            unsafe { core::arch::aarch64::vmull_p64(a, b) }
        }
        all(target_arch = "x86_64", target_feature = "pclmulqdq") => {
            use core::arch::x86_64::{__m128i, _mm_clmulepi64_si128, _mm_cvtsi64_si128};
            // SAFETY: the cfg enables pclmulqdq; both sides of the transmute are 128 plain bits.
            unsafe {
                let p = _mm_clmulepi64_si128::<0x00>(_mm_cvtsi64_si128(a as i64), _mm_cvtsi64_si128(b as i64));
                core::mem::transmute::<__m128i, u128>(p)
            }
        }
        _ => portable::mul_wide(a, b),
    }
}

/// A GF(2)-linear map from 16 bits to 32, held in the forms the backends apply it in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Linear16 {
    /// The images of the 256 values of the low byte and of the high one.
    bytes: [[u32; 256]; 2],
    /// Byte `o` of the images of the sixteen values of nibble `n`, at `[o][n]`, for x86's byte shuffles.
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

    /// The eight mixed products `self[i] * k[i]`.
    #[inline(always)]
    pub fn mul_base(self, k: F64x8) -> Self {
        self.mul_base_unreduced(k).reduce()
    }
}

impl Wide8 {
    /// The sum of the eight lanes.
    #[inline(always)]
    pub fn sum(self) -> u128 {
        self.to_array().into_iter().fold(0, |a, b| a ^ b)
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

impl Mul for F64x8 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        self.product(rhs)
    }
}

impl Mul for F128x8 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        self.mul_unreduced(rhs).reduce()
    }
}

impl MulAssign for F128x8 {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    /// Random elements with the reduction's corner cases mixed in.
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

    /// Every field operation against the portable body: the scalar operation, lane by lane.
    #[test]
    fn field_lanes_match_the_scalar_field() {
        let mut rng = Rng::new(0x1A4E5);
        for _ in 0..500 {
            let (a, b, c) = (ext8(&mut rng), ext8(&mut rng), ext8(&mut rng));
            let (k, l) = (base8(&mut rng), base8(&mut rng));
            let (va, vb, vc) = (F128x8::from_array(&a), F128x8::from_array(&b), F128x8::from_array(&c));
            let (vk, vl) = (F64x8::from_array(&k), F64x8::from_array(&l));
            let (r, t) = (rng.ext(), F64(rng.next_u64()));

            // One element.
            for i in 0..8 {
                assert_eq!(mul_wide(k[i].0, l[i].0), portable::mul_wide(k[i].0, l[i].0));
                assert_eq!(mul(a[i], b[i]), portable::mul(a[i], b[i]));
            }

            // Moves.
            assert_eq!(va.to_array(), a);
            assert_eq!(vk.to_array(), k);
            assert_eq!(F128x8::splat(r).to_array(), [r; 8]);
            assert_eq!(F64x8::splat(t).to_array(), [t; 8]);
            assert_eq!(F128x8::ZERO.to_array(), [F128::ZERO; 8]);
            assert_eq!(F64x8::ZERO.to_array(), [F64::ZERO; 8]);
            assert_eq!(Acc8::ZERO.reduce().to_array(), [F128::ZERO; 8]);
            assert_eq!(F64x8::load(&k).to_array(), k);
            let mut e = [F128::ZERO; 8];
            F128x8::load(&a).store(&mut e);
            assert_eq!(e, a);

            // `K` lanes.
            assert_eq!((vk + vl).to_array(), lanes(|i| k[i] + l[i]));
            assert_eq!((vk * vl).to_array(), lanes(|i| k[i] * l[i]));

            // `E` lanes.
            assert_eq!((va + vb).to_array(), lanes(|i| a[i] + b[i]));
            assert_eq!((va * vb).to_array(), lanes(|i| a[i] * b[i]));
            assert_eq!(va.mul_base(vk).to_array(), lanes(|i| a[i].mul_base(k[i])));
            let mut x = va;
            x += vb;
            x *= vc;
            assert_eq!(x.to_array(), lanes(|i| (a[i] + b[i]) * c[i]));

            // Unreduced sums of full and mixed products, reduced per lane or summed.
            let mut acc = va.mul_unreduced(vb);
            acc += vc.mul_base_unreduced(vk);
            let acc = acc + vb.mul_unreduced(vc);
            let want = lanes(|i| a[i] * b[i] + c[i].mul_base(k[i]) + b[i] * c[i]);
            assert_eq!(acc.reduce().to_array(), want);
            assert_eq!(acc.sum(), want.iter().sum());

            // Carry-less products of words.
            let (p, q) = (k.map(|k| k.0), l.map(|l| l.0));
            assert_eq!(clmul8_low(p, q), lanes(|i| portable::mul_wide(p[i], q[i]) as u64));
            let wide = Wide8::mul(p, q) + Wide8::mul(q, q);
            let want = lanes(|i| portable::mul_wide(p[i], q[i]) ^ portable::mul_wide(q[i], q[i]));
            assert_eq!((wide.to_array(), wide.sum()), (want, want.iter().fold(0, |a, b| a ^ b)));
        }
    }

    /// The byte operations of the backend and the portable bodies against their definitions, bit by bit.
    #[test]
    fn byte_operations_match_their_definitions() {
        let mut rng = Rng::new(0xB17E5);
        let word = |rng: &mut Rng| -> [u64; 8] { core::array::from_fn(|_| rng.next_u64()) };
        let bytes = |x: &[u64; 8]| -> [u8; 64] { core::array::from_fn(|n| (x[n / 8] >> (8 * (n % 8))) as u8) };
        for _ in 0..200 {
            let images: [u8; 8] = core::array::from_fn(|_| rng.next_u64() as u8);
            let x = word(&mut rng);
            let image = |b: u8| (0..8).filter(|c| b >> c & 1 == 1).fold(0, |a, c| a ^ images[c]);
            let want = bytes(&x).map(image);
            assert_eq!(bytes(&map_bytes(&ByteMap::new(images), x)), want);
            assert_eq!(bytes(&portable::map_bytes(&portable::ByteMap::new(images), x)), want);

            let images: [u32; 16] = core::array::from_fn(|_| rng.next_u64() as u32);
            let image = |v: u64| (0..16).filter(|t| v >> t & 1 == 1).fold(0, |a, t| a ^ images[t]);
            let m = Linear16::new(images);
            let want: [[u64; 8]; 4] = core::array::from_fn(|f| x.map(|w| u64::from(image(w >> (16 * f) & 0xffff))));
            assert_eq!(map_fields(&m, x), want);
            assert_eq!(portable::map_fields(&m, x), want);

            let rows: [[u64; 8]; 8] = core::array::from_fn(|_| word(&mut rng));
            let want: [[u64; 8]; 8] = core::array::from_fn(|c| core::array::from_fn(|r| rows[r][c]));
            assert_eq!(transpose_words(&rows), want);
            assert_eq!(portable::transpose_words(&rows), want);

            for t in [transpose_bits(x), portable::transpose_bits(x)].map(|t| bytes(&t)) {
                for (n, k) in (0..64).flat_map(|n| (0..8).map(move |k| (n, k))) {
                    assert_eq!(t[n] >> k & 1, (x[k] >> n & 1) as u8, "bit {k} of byte {n}");
                }
            }

            let rows: [[u64; 8]; 16] = core::array::from_fn(|_| word(&mut rng));
            for t in [transpose_bytes(&rows), portable::transpose_bytes(&rows)] {
                for (n, b) in (0..64).flat_map(|n| (0..16).map(move |b| (n, b))) {
                    assert_eq!((t[n] >> (8 * b)) as u8, bytes(&rows[b])[n], "byte {b} of {n}");
                }
            }
        }
    }
}
