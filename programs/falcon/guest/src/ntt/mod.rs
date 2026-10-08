//! The negacyclic NTT over `Z_q`, `q = 12289`, on signed 64-bit coefficients.
//!
//! `x^512 + 1` splits into 512 linear factors `x - psi^(2i+1)`, with `psi` a primitive 1024-th root of unity.
//!
//! A product by a twiddle is Plantard's (two multiplies), a product of two transforms Montgomery's (three).
//!
//! The registers are 64 bits wide, so no sum is ever reduced:
//!
//! ```text
//!   forward   |a| <= 12288 + 9 * 6145 < 2^17      each layer adds one reduced product
//!   product   |a * b| < 2^35 < 2^31 * q            in Montgomery's range, reduced below q/2 + 2
//!   inverse   |a| <= 2^9 * 6146 < 2^22            each layer doubles the sums
//! ```
//!
//! A transform is three passes of three layers: eight coefficients stay in registers for twelve butterflies.

use crate::{N, Q};

/// `q^-1 mod 2^32`, so that `t - (t * q^-1 mod 2^32) * q` is a multiple of `2^32`.
const Q_INV: i64 = {
    // Newton's iteration doubles the correct low bits: 1, 2, 4, ..., 32.
    let mut x: u32 = Q as u32;
    let mut i = 0;
    while i < 5 {
        x = x.wrapping_mul(2u32.wrapping_sub((Q as u32).wrapping_mul(x)));
        i += 1;
    }
    x as i32 as i64
};
const _: () = assert!((Q as i32).wrapping_mul(Q_INV as i32) == 1);

/// `q^-1 mod 2^64`, for Plantard's products.
const Q_INV_64: u64 = {
    // Newton's iteration doubles the correct low bits: 1, 2, 4, ..., 64.
    let mut x: u64 = Q as u64;
    let mut i = 0;
    while i < 6 {
        x = x.wrapping_mul(2u64.wrapping_sub((Q as u64).wrapping_mul(x)));
        i += 1;
    }
    x
};
const _: () = assert!((Q as u64).wrapping_mul(Q_INV_64) == 1);

/// Plantard's fudge exponent `alpha`: `2^alpha q < 2^31`, the most it may be.
const ALPHA: u32 = 17;
const _: () = assert!((Q << ALPHA) < 1 << 31 && (Q << (ALPHA + 1)) >= 1 << 31);

/// `R = 2^32 mod q`.
const R: i64 = (1 << 32) % Q;

/// `a * b mod q`.
const fn mul_mod(a: i64, b: i64) -> i64 {
    (a * b).rem_euclid(Q)
}

/// `a^e mod q`.
const fn pow_mod(a: i64, mut e: u64) -> i64 {
    let (mut base, mut acc) = (a.rem_euclid(Q), 1);
    while e > 0 {
        if e & 1 == 1 {
            acc = mul_mod(acc, base);
        }
        base = mul_mod(base, base);
        e >>= 1;
    }
    acc
}

/// The representative of `a mod q` in `[-q/2, q/2]`.
const fn centered(a: i64) -> i64 {
    let a = a.rem_euclid(Q);
    if a > Q / 2 { a - Q } else { a }
}

/// `psi`: a primitive 1024-th root of unity, `g^12` for the least generator `g` of `Z_q^*`.
const PSI: i64 = {
    // q - 1 = 2^12 * 3, so g generates Z_q^* iff neither g^((q-1)/2) nor g^((q-1)/3) is 1.
    let mut g = 2;
    while pow_mod(g, (Q as u64 - 1) / 2) == 1 || pow_mod(g, (Q as u64 - 1) / 3) == 1 {
        g += 1;
    }
    pow_mod(g, (Q as u64 - 1) / (2 * N as u64))
};
const _: () = assert!(pow_mod(PSI, N as u64) == Q - 1);

/// `zeta_k = psi^brv(k)`, centered, `brv` reversing 9 bits.
///
/// The layer of distance `len` takes `zeta_k` for `k` in `[N / 2len, N / len)`, one per block, in order.
const ZETAS: [i64; N] = {
    let mut zetas = [0; N];
    let mut k = 0;
    while k < N {
        let brv = (k as u32).reverse_bits() >> (u32::BITS - N.trailing_zeros());
        zetas[k] = centered(pow_mod(PSI, brv as u64));
        k += 1;
    }
    zetas
};

/// `zeta` as Plantard's multiplier: `b q^-1 mod 2^64` for `b = -zeta 2^64 mod q`.
///
/// Plantard's product by it is `-a b / 2^64 = a zeta mod q`.
const fn plantard(zeta: i64) -> i64 {
    let b = centered(-mul_mod(zeta, pow_mod(2, 64)));
    (b as u64).wrapping_mul(Q_INV_64) as i64
}

/// The forward twiddles, as Plantard's multipliers.
const FORWARD: [i64; N] = {
    let mut twiddles = [0; N];
    let mut k = 1;
    while k < N {
        twiddles[k] = plantard(ZETAS[k]);
        k += 1;
    }
    twiddles
};

/// The inverse twiddles, as Plantard's multipliers: each layer's forward twiddles, negated and in reverse order.
///
/// The inverse undoes the blocks of a layer from the last to the first, so it reads them in order here.
///
/// ```text
///   layer range [lo, 2lo):   INVERSE[lo + b] = -zeta_(2lo - 1 - b)
/// ```
const INVERSE: [i64; N] = {
    let mut twiddles = [0; N];
    let mut k = 1;
    while k < N {
        let lo = 1 << (usize::BITS - 1 - k.leading_zeros());
        twiddles[k] = plantard(-ZETAS[3 * lo - 1 - k]);
        k += 1;
    }
    twiddles
};

/// `R^2 / n mod q`, centered: what turns `multiply`'s `n a b / R` back into `a b`, through a Montgomery reduction.
const UNSCALE: i64 = centered(mul_mod(mul_mod(R, R), pow_mod(N as i64, Q as u64 - 2)));

/// `a * b`'s low 32 bits, sign-extended: rv64im's `mulw`.
#[inline(always)]
fn mulw(a: i64, b: i64) -> i64 {
    #[cfg(target_arch = "riscv64")]
    {
        let product;
        // SAFETY: `mulw` reads two registers and writes one, touching nothing else.
        unsafe {
            core::arch::asm!("mulw {}, {}, {}", lateout(reg) product, in(reg) a, in(reg) b, options(pure, nomem, nostack));
        }
        product
    }
    #[cfg(not(target_arch = "riscv64"))]
    {
        (a as i32).wrapping_mul(b as i32) as i64
    }
}

/// Montgomery's reduction: `t / R mod q`, of magnitude at most `|t| / 2^32 + q / 2`, for `|t| < 2^31 * q`.
#[inline(always)]
fn reduce(t: i64) -> i64 {
    // m = t / q mod 2^32, as a signed 32-bit value: t - m * q is a multiple of 2^32.
    let m = mulw(t, Q_INV);
    (t - m * Q) >> 32
}

/// Plantard's product by a twiddle: `a zeta mod q`, of magnitude at most `q / 2 + 1`, for `|a zeta| < 2^62`.
///
/// With `X = a b'` wrapping, `b' = b q^-1 mod 2^64`, and `Y = X >> 32`:
///
/// ```text
///   k = (a b - X q) / 2^64           an integer, = a b / 2^64 mod q, |k| < q / 2 + 1
///   (Y + 2^alpha) q / 2^32  =  -k + (2^alpha q - E) / 2^32,   E = ((X mod 2^32) q - a b) / 2^32
///   0 <= 2^alpha q - E < 2^32         for |a b| < 2^62
///   →  floor((Y + 2^alpha) q / 2^32)  =  -k  =  a zeta mod q
/// ```
#[inline(always)]
const fn mul_twiddle(a: i64, twiddle: i64) -> i64 {
    let y = a.wrapping_mul(twiddle) >> 32;
    ((y + (1 << ALPHA)) * Q) >> 32
}

/// A Cooley-Tukey butterfly: `(x, y) <- (x + zeta y, x - zeta y)`.
#[inline(always)]
const fn forward_butterfly(x: &mut [i64; 8], lo: usize, hi: usize, twiddle: i64) {
    let t = mul_twiddle(x[hi], twiddle);
    x[hi] = x[lo] - t;
    x[lo] += t;
}

/// A Gentleman-Sande butterfly: `(x, y) <- (x + y, zeta (x - y))`.
#[inline(always)]
const fn inverse_butterfly(x: &mut [i64; 8], lo: usize, hi: usize, twiddle: i64) {
    let t = x[lo];
    x[lo] = t + x[hi];
    x[hi] = mul_twiddle(t - x[hi], twiddle);
}

/// `a <- n (a * b) / R mod (x^512 + 1)`, coefficient by coefficient congruent mod q, `b` clobbered.
///
/// Two forward transforms, then the inverse, its first pass taking the pointwise products as it loads.
///
/// `sub_centered` takes the result to `c - a * b`.
pub fn multiply(a: &mut [i64; N], b: &mut [i64; N]) {
    forward(a);
    forward(b);
    inverse_pass::<1>(a, Some(b));
    inverse_pass::<8>(a, None);
    inverse_pass::<64>(a, None);
}

/// The forward NTT, in place: natural order in, bit-reversed order out.
fn forward(a: &mut [i64; N]) {
    forward_pass::<256>(a);
    forward_pass::<32>(a);
    forward_pass::<4>(a);
}

/// Three forward layers, of distances `LEN`, `LEN / 2` and `LEN / 4`, on blocks of `2 LEN`.
///
/// ```text
///   coefficients j + m LEN/4, m = 0..8
///   distance LEN     (0,4) (1,5) (2,6) (3,7)    one twiddle per block
///   distance LEN/2   (0,2) (1,3) (4,6) (5,7)    two
///   distance LEN/4   (0,1) (2,3) (4,5) (6,7)    four
/// ```
#[inline(always)]
fn forward_pass<const LEN: usize>(a: &mut [i64; N]) {
    let (step, blocks) = (LEN / 4, N / (2 * LEN));
    let first = &FORWARD[blocks..2 * blocks];
    let second = FORWARD[2 * blocks..4 * blocks].as_chunks::<2>().0;
    let third = FORWARD[4 * blocks..8 * blocks].as_chunks::<4>().0;
    for (((block, &z1), z2), z3) in a.chunks_exact_mut(2 * LEN).zip(first).zip(second).zip(third) {
        for j in 0..step {
            let mut x: [i64; 8] = core::array::from_fn(|m| block[j + m * step]);
            for m in 0..4 {
                forward_butterfly(&mut x, m, m + 4, z1);
            }
            for m in [0, 1, 4, 5] {
                forward_butterfly(&mut x, m, m + 2, z2[m / 4]);
            }
            for m in [0, 2, 4, 6] {
                forward_butterfly(&mut x, m, m + 1, z3[m / 2]);
            }
            for (m, &v) in x.iter().enumerate() {
                block[j + m * step] = v;
            }
        }
    }
}

/// Three inverse layers, of distances `LEN`, `2 LEN` and `4 LEN`, on blocks of `8 LEN`.
///
/// Given `factors`, each coefficient is first replaced by its Montgomery product with its factor: the pointwise product.
///
/// ```text
///   coefficients j + m LEN, m = 0..8
///   distance LEN     (0,1) (2,3) (4,5) (6,7)    four twiddles per block
///   distance 2 LEN   (0,2) (1,3) (4,6) (5,7)    two
///   distance 4 LEN   (0,4) (1,5) (2,6) (3,7)    one
/// ```
#[inline(always)]
fn inverse_pass<const LEN: usize>(a: &mut [i64; N], factors: Option<&[i64; N]>) {
    let blocks = N / (8 * LEN);
    let first = INVERSE[4 * blocks..8 * blocks].as_chunks::<4>().0;
    let second = INVERSE[2 * blocks..4 * blocks].as_chunks::<2>().0;
    let third = &INVERSE[blocks..2 * blocks];
    for (i, (((block, z1), z2), &z3)) in a
        .chunks_exact_mut(8 * LEN)
        .zip(first)
        .zip(second)
        .zip(third)
        .enumerate()
    {
        let factors = factors.map(|f| &f[8 * LEN * i..8 * LEN * (i + 1)]);
        for j in 0..LEN {
            let mut x: [i64; 8] = core::array::from_fn(|m| block[j + m * LEN]);
            if let Some(f) = factors {
                for (m, x) in x.iter_mut().enumerate() {
                    *x = reduce(*x * f[j + m * LEN]);
                }
            }
            for m in [0, 2, 4, 6] {
                inverse_butterfly(&mut x, m, m + 1, z1[m / 2]);
            }
            for m in [0, 1, 4, 5] {
                inverse_butterfly(&mut x, m, m + 2, z2[m / 4]);
            }
            for m in 0..4 {
                inverse_butterfly(&mut x, m, m + 4, z3);
            }
            for (m, &v) in x.iter().enumerate() {
                block[j + m * LEN] = v;
            }
        }
    }
}

/// `c - p mod q`, centered in `[-(q-1)/2, (q-1)/2]`, for `0 <= c < 5q` and `p` a coefficient of `multiply`'s output.
///
/// One Montgomery reduction takes both terms, `c R` undoing its `1 / R`, and `UNSCALE` the product's `n / R`:
///
/// ```text
///   (c R - UNSCALE p) / R  =  c - p / n * R / R  =  c - (s2 * h)_i      mod q
///   |c R - UNSCALE p| < 2^30 + 2^35  →  |result| < q/2 + 10
/// ```
#[inline(always)]
pub fn sub_centered(c: i64, p: i64) -> i64 {
    let x = reduce(c * R - UNSCALE * p);
    // A result in the ten values past q/2 on either side takes one more step, almost never.
    if (x + Q / 2) as u64 > (Q - 1) as u64 {
        wrap(x)
    } else {
        x
    }
}

/// `x` moved by `q` toward zero.
#[cold]
const fn wrap(x: i64) -> i64 {
    if x > 0 { x - Q } else { x + Q }
}
