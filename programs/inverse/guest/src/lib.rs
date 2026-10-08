//! Inverses in BN254's base field, the one a Groth16 verifier's pairing works in: by Fermat's exponentiation, or by a
//! hint the guest checks with one product.
//!
//! An element is four little-endian words in Montgomery form, `x R mod p` with `R = 2^256`.
#![no_std]

use leanvm_guest::hint;

/// A field element in Montgomery form, below `p`.
pub type Fp = [u64; 4];

/// The modulus `p`.
pub const P: Fp = [
    0x3c20_8c16_d87c_fd47,
    0x9781_6a91_6871_ca8d,
    0xb850_45b6_8181_585d,
    0x3064_4e72_e131_a029,
];

/// One: `R mod p`.
pub const ONE: Fp = [
    0xd35d_438d_c58f_0d9d,
    0x0a78_eb28_f5c7_0b3d,
    0x666e_a36f_7879_462c,
    0x0e0a_77c1_9a07_df2f,
];

/// `R^2 mod p`, which a product takes into Montgomery form.
const R2: Fp = [
    0xf32c_fc5b_538a_fa89,
    0xb5e7_1911_d445_01fb,
    0x47ab_1eff_0a41_7ff6,
    0x06d8_9f71_cab8_351f,
];

/// `-p^-1 mod 2^64`.
const INV: u64 = 0x87d2_0782_e486_6389;

/// `p - 2`, the exponent of an inverse by Fermat.
const P_MINUS_2: Fp = [P[0] - 2, P[1], P[2], P[3]];

/// What the guest is asked to do for each element: invert it by exponentiation, by a hint, or by a hint the prover
/// got wrong.
pub const BY_EXPONENT: u64 = 0;
pub const BY_HINT: u64 = 1;
pub const BY_WRONG_HINT: u64 = 2;

/// Whether `a` is below `p`.
pub fn is_canonical(a: &[u64; 4]) -> bool {
    a.iter()
        .rev()
        .zip(P.iter().rev())
        .find(|(x, p)| x != p)
        .is_some_and(|(x, p)| x < p)
}

/// `a b R^-1 mod p`, by coarsely integrated operand scanning.
#[inline]
pub fn mul(a: &Fp, b: &Fp) -> Fp {
    let mut t = [0u64; 6];
    for &bi in b {
        let mut carry = 0u64;
        for j in 0..4 {
            let s = t[j] as u128 + a[j] as u128 * bi as u128 + carry as u128;
            (t[j], carry) = (s as u64, (s >> 64) as u64);
        }
        let s = t[4] as u128 + carry as u128;
        (t[4], t[5]) = (s as u64, (s >> 64) as u64);

        // Add the multiple of p that clears the low word, and drop it.
        let m = t[0].wrapping_mul(INV);
        let mut carry = ((t[0] as u128 + m as u128 * P[0] as u128) >> 64) as u64;
        for j in 1..4 {
            let s = t[j] as u128 + m as u128 * P[j] as u128 + carry as u128;
            (t[j - 1], carry) = (s as u64, (s >> 64) as u64);
        }
        let s = t[4] as u128 + carry as u128;
        (t[3], t[4]) = (s as u64, t[5] + (s >> 64) as u64);
    }

    // Below 2p, so one subtraction at most.
    let mut r = [0u64; 4];
    let mut borrow = 0u64;
    for j in 0..4 {
        let (d, b1) = t[j].overflowing_sub(P[j]);
        let (d, b2) = d.overflowing_sub(borrow);
        (r[j], borrow) = (d, (b1 | b2) as u64);
    }
    if t[4] == 0 && borrow == 1 {
        [t[0], t[1], t[2], t[3]]
    } else {
        r
    }
}

/// The element `x`, which must be below `p`, in Montgomery form.
pub fn from_canonical(x: &[u64; 4]) -> Fp {
    assert!(is_canonical(x), "an element below p");
    mul(x, &R2)
}

/// The element `a` out of Montgomery form.
pub fn to_canonical(a: &Fp) -> [u64; 4] {
    mul(a, &[1, 0, 0, 0])
}

/// `x^-1`, zero for zero, as `x^(p-2)`: a square for each bit of the exponent, and a product for each set one.
pub fn inverse(x: &Fp) -> Fp {
    let mut acc = ONE;
    for word in P_MINUS_2.iter().rev() {
        for bit in (0..64).rev() {
            acc = mul(&acc, &acc);
            if word >> bit & 1 == 1 {
                acc = mul(&acc, x);
            }
        }
    }
    acc
}

/// `x^-1` for a nonzero `x`, from a hint: the prover chose it, so it must be an element and its product with `x` one.
pub fn inverse_by_hint(x: &Fp) -> Fp {
    checked(x, *hint(|| inverse(x)))
}

/// `inv` if it is `x`'s inverse; a panic, so no proof, otherwise.
pub fn checked(x: &Fp, inv: Fp) -> Fp {
    // Word by word: an array's `==` is a byte-wise `memcmp`.
    let product = mul(x, &inv);
    let one = (0..4).fold(0, |differs, i| differs | (product[i] ^ ONE[i])) == 0;
    assert!(is_canonical(&inv) && one, "the hint is the inverse");
    inv
}
