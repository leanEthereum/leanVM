//! The field `GF(2^8) = GF(2)[x] / (x^8 + x^4 + x^3 + x + 1)`.
//!
//! The executable functions are the portable paths of `crates/primitives/src/field/gf2_8.rs`, copied
//! with the same bodies; `tests/equivalence/gf2_8.rs` checks the two agree.
//!
//! Specification: an element is a polynomial over GF(2) of degree below 8, bit `i` its coefficient of
//! `x^i`. The product [`f8_mul`] is the carry-less product ([`clmul`], the one of `crate::clmul`) reduced
//! modulo `M = x^8 + x^4 + x^3 + x + 1`, where "reduced" is the definition of a remainder
//! ([`is_remainder8`]).
use crate::clmul::*;
use core::ops::{Add, AddAssign, Mul, MulAssign};
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// The modulus `M = x^8 + x^4 + x^3 + x + 1`.
pub open spec fn modulus8() -> u128 {
    0x11Bu128
}

/// `r` is the remainder of `p` modulo `M`: `p = q * M + r` for some polynomial `q`, and `deg r < 8`.
///
/// A `p` of degree below 16 has a quotient of degree below 8, so `q < 2^8` loses nothing.
pub open spec fn is_remainder8(p: u16, r: u8) -> bool {
    exists|q: u64| q < 256 && p as u128 == clmul(q, modulus8()) ^ (r as u128)
}

/// `p mod M`, the unique remainder (unique by [`lemma_remainder8_unique`]).
pub open spec fn f8_mod(p: u16) -> u8 {
    choose|r: u8| is_remainder8(p, r)
}

/// The product in `GF(2^8)`: `a * b mod M`. The carry-less product of two bytes has degree below 15
/// ([`lemma_clmul8_closed`]), so the cast to `u16` loses nothing.
pub open spec fn f8_mul(a: u8, b: u8) -> u8 {
    f8_mod(clmul(a as u64, b as u128) as u16)
}

/// `a^n` in `GF(2^8)`.
pub open spec fn f8_pow(a: u8, n: nat) -> u8
    decreases n,
{
    if n == 0 {
        1
    } else {
        f8_mul(f8_pow(a, (n - 1) as nat), a)
    }
}

// ---------------------------------------------------------------------------------------------
// The carry-less product of two bytes, in closed form
// ---------------------------------------------------------------------------------------------
/// `[a_i] * b * x^i` at 16 bits.
pub open spec fn term8(a: u8, b: u8, i: u16) -> u16 {
    if (a >> i) & 1 == 1 {
        (b as u16) << i
    } else {
        0
    }
}

/// The eight partial products of [`clmul`] for bytes, XORed: a bit-vector term.
pub open spec fn clmul8_closed(a: u8, b: u8) -> u16 {
    term8(a, b, 0) ^ term8(a, b, 1) ^ term8(a, b, 2) ^ term8(a, b, 3) ^ term8(a, b, 4) ^ term8(a, b, 5)
        ^ term8(a, b, 6) ^ term8(a, b, 7)
}

/// The partial products past bit 7 of a byte are zero.
proof fn lemma_clmul_upto_byte(a: u8, b: u128, n: nat)
    requires
        8 <= n <= 64,
    ensures
        clmul_upto(a as u64, b, n) == clmul_upto(a as u64, b, 8),
    decreases n,
{
    if n > 8 {
        let i = (n - 1) as nat;
        lemma_clmul_upto_byte(a, b, i);
        let s = i as u64;
        assert(s >= 8 ==> ((a as u64) >> s) & 1 != 1) by (bit_vector);
        let x = clmul_upto(a as u64, b, i);
        assert(x ^ 0 == x) by (bit_vector);
    }
}

/// [`clmul`] of two bytes is [`clmul8_closed`], of degree below 15.
pub proof fn lemma_clmul8_closed(a: u8, b: u8)
    ensures
        clmul(a as u64, b as u128) == clmul8_closed(a, b) as u128,
        clmul8_closed(a, b) >> 15u16 == 0,
{
    lemma_clmul_upto_byte(a, b as u128, 64);
    reveal_with_fuel(clmul_upto, 9);
    assert(clmul_upto(a as u64, b as u128, 8) == clmul8_closed(a, b) as u128) by {
        assert({
            let (a, w) = (a as u64, b as u128);
            let t = |i: u64|
                if (a >> i) & 1 == 1 {
                    w << (i as u128)
                } else {
                    0
                };
            0 ^ t(0) ^ t(1) ^ t(2) ^ t(3) ^ t(4) ^ t(5) ^ t(6) ^ t(7) == clmul8_closed(a as u8, b) as u128
        }) by (bit_vector);
    }
    assert(clmul8_closed(a, b) >> 15u16 == 0) by (bit_vector);
}

// ---------------------------------------------------------------------------------------------
// The reduction
// ---------------------------------------------------------------------------------------------
/// The closed form of the production `gf8_reduce`, as a spec function.
pub open spec fn reduce8_formula(p: u16) -> u8 {
    let h: u16 = p >> 8u16;
    let t: u16 = (p & 0xff) ^ h ^ (h << 1u16) ^ (h << 3u16) ^ (h << 4u16);
    let h2: u16 = t >> 8u16;
    ((t & 0xff) ^ h2 ^ (h2 << 1u16) ^ (h2 << 3u16) ^ (h2 << 4u16)) as u8
}

/// `q * M = q x^8 + q * (x^4 + x^3 + x + 1)`.
pub proof fn lemma_clmul_modulus8(q: u64)
    requires
        q < 256,
    ensures
        clmul(q, modulus8()) == ((q as u128) << 8u128) ^ crate::gf2_64::times_r64(q),
{
    assert(modulus8() == 0x1Bu128 ^ (1u128 << 8u128)) by (bit_vector);
    lemma_clmul_xor_right(q, 0x1Bu128, 1u128 << 8u128);
    crate::gf2_64::lemma_clmul_r64(q);
    lemma_clmul_monomial(q, 8);
    let (a, b) = (crate::gf2_64::times_r64(q), (q as u128) << 8u128);
    assert(a ^ b == b ^ a) by (bit_vector);
}

/// The production reduction returns a remainder of `p` modulo `M`, for every `p < 2^16`: its quotient
/// is `h ^ h2`, the two upper bytes it folds.
pub proof fn lemma_reduce8_formula_is_remainder(p: u16)
    ensures
        is_remainder8(p, reduce8_formula(p)),
{
    let h: u16 = p >> 8u16;
    let t: u16 = (p & 0xff) ^ h ^ (h << 1u16) ^ (h << 3u16) ^ (h << 4u16);
    let h2: u16 = t >> 8u16;
    let q = (h ^ h2) as u8 as u64;
    lemma_clmul_modulus8(q);
    assert({
        let h: u16 = p >> 8u16;
        let t: u16 = (p & 0xff) ^ h ^ (h << 1u16) ^ (h << 3u16) ^ (h << 4u16);
        let h2: u16 = t >> 8u16;
        let w = ((h ^ h2) as u8) as u128;
        p as u128 == ((w << 8u128) ^ (w ^ (w << 1u128) ^ (w << 3u128) ^ (w << 4u128))) ^ (reduce8_formula(
            p,
        ) as u128)
    }) by (bit_vector);
    assert(p as u128 == clmul(q, modulus8()) ^ (reduce8_formula(p) as u128));
}

/// The remainder modulo `M` is unique.
pub proof fn lemma_remainder8_unique(p: u16, r1: u8, r2: u8)
    requires
        is_remainder8(p, r1),
        is_remainder8(p, r2),
    ensures
        r1 == r2,
{
    let q1 = choose|q: u64| q < 256 && p as u128 == clmul(q, modulus8()) ^ (r1 as u128);
    let q2 = choose|q: u64| q < 256 && p as u128 == clmul(q, modulus8()) ^ (r2 as u128);
    lemma_clmul_modulus8(q1);
    lemma_clmul_modulus8(q2);
    assert({
        let (w1, w2) = (q1 as u128, q2 as u128);
        q1 < 256 && q2 < 256 && ((w1 << 8u128) ^ (w1 ^ (w1 << 1u128) ^ (w1 << 3u128) ^ (w1 << 4u128))) ^ (
        r1 as u128) == ((w2 << 8u128) ^ (w2 ^ (w2 << 1u128) ^ (w2 << 3u128) ^ (w2 << 4u128))) ^ (r2 as u128)
            ==> r1 == r2
    }) by (bit_vector);
}

/// `p mod M` is the production reduction's closed form.
pub proof fn lemma_f8_mod(p: u16)
    ensures
        f8_mod(p) == reduce8_formula(p),
        is_remainder8(p, f8_mod(p)),
{
    lemma_reduce8_formula_is_remainder(p);
    lemma_remainder8_unique(p, f8_mod(p), reduce8_formula(p));
}

/// The product in closed form: a bit-vector term over the two bytes.
pub open spec fn f8_mul_closed(a: u8, b: u8) -> u8 {
    reduce8_formula(clmul8_closed(a, b))
}

pub proof fn lemma_f8_mul_closed(a: u8, b: u8)
    ensures
        f8_mul(a, b) == f8_mul_closed(a, b),
{
    lemma_clmul8_closed(a, b);
    assert((clmul8_closed(a, b) as u128) as u16 == clmul8_closed(a, b)) by (bit_vector);
    lemma_f8_mod(clmul8_closed(a, b));
}

/// Reduction is GF(2)-linear.
pub proof fn lemma_f8_mod_xor(p1: u16, p2: u16)
    ensures
        f8_mod(p1 ^ p2) == f8_mod(p1) ^ f8_mod(p2),
{
    lemma_f8_mod(p1);
    lemma_f8_mod(p2);
    lemma_f8_mod(p1 ^ p2);
    assert(reduce8_formula(p1 ^ p2) == reduce8_formula(p1) ^ reduce8_formula(p2)) by (bit_vector);
}

/// A polynomial of degree below 8 is its own remainder.
pub proof fn lemma_f8_mod_small(p: u16)
    requires
        p >> 8u16 == 0,
    ensures
        f8_mod(p) == p as u8,
{
    lemma_f8_mod(p);
    assert(p >> 8u16 == 0 ==> reduce8_formula(p) == p as u8) by (bit_vector);
}

/// Multiplication by `x` in `GF(2^8)`: shift, and fold `x^8` back as `x^4 + x^3 + x + 1`.
pub open spec fn mulx8(a: u8) -> u8 {
    (a << 1u8) ^ (if a >> 7u8 == 1 {
        0x1Bu8
    } else {
        0u8
    })
}

/// `a * x^k` in `GF(2^8)`.
pub open spec fn mulx8_pow(a: u8, k: nat) -> u8
    decreases k,
{
    if k == 0 {
        a
    } else {
        mulx8(mulx8_pow(a, (k - 1) as nat))
    }
}

/// `(p x) mod M = (p mod M) x mod M`.
pub proof fn lemma_f8_mod_shl1(p: u16)
    requires
        p >> 15u16 == 0,
    ensures
        f8_mod(p << 1u16) == mulx8(f8_mod(p)),
{
    lemma_f8_mod(p);
    lemma_f8_mod(p << 1u16);
    assert(p >> 15u16 == 0 ==> reduce8_formula(p << 1u16) == mulx8(reduce8_formula(p))) by (bit_vector);
}

/// A multiple of `M` reduces to zero.
pub proof fn lemma_f8_mod_multiple(q: u8)
    ensures
        f8_mod(clmul(q as u64, modulus8()) as u16) == 0,
{
    lemma_clmul_modulus8(q as u64);
    lemma_f8_mod(clmul(q as u64, modulus8()) as u16);
    assert({
        let w = (q as u64) as u128;
        reduce8_formula((((w << 8u128) ^ (w ^ (w << 1u128) ^ (w << 3u128) ^ (w << 4u128)))) as u16) == 0
    }) by (bit_vector);
}

// ---------------------------------------------------------------------------------------------
// GF(2^8) is a commutative ring
// ---------------------------------------------------------------------------------------------
pub proof fn lemma_f8_mul_comm(a: u8, b: u8)
    ensures
        f8_mul(a, b) == f8_mul(b, a),
{
    lemma_f8_mul_closed(a, b);
    lemma_f8_mul_closed(b, a);
    assert(f8_mul_closed(a, b) == f8_mul_closed(b, a)) by (bit_vector);
}

pub proof fn lemma_f8_mul_one(a: u8)
    ensures
        f8_mul(a, 1) == a,
        f8_mul(1, a) == a,
{
    lemma_f8_mul_closed(a, 1);
    lemma_f8_mul_closed(1, a);
    assert(f8_mul_closed(a, 1) == a && f8_mul_closed(1, a) == a) by (bit_vector);
}

pub proof fn lemma_f8_mul_zero(a: u8)
    ensures
        f8_mul(a, 0) == 0,
        f8_mul(0, a) == 0,
{
    lemma_clmul_zero(a as u64);
    assert(0u16 >> 8u16 == 0) by (bit_vector);
    lemma_f8_mod_small(0);
    lemma_f8_mul_comm(a, 0);
}

pub proof fn lemma_f8_mul_xor_right(a: u8, b: u8, c: u8)
    ensures
        f8_mul(a, b ^ c) == f8_mul(a, b) ^ f8_mul(a, c),
{
    assert((b ^ c) as u128 == (b as u128) ^ (c as u128)) by (bit_vector);
    lemma_clmul_xor_right(a as u64, b as u128, c as u128);
    let (x, y) = (clmul(a as u64, b as u128), clmul(a as u64, c as u128));
    assert((x ^ y) as u16 == (x as u16) ^ (y as u16)) by (bit_vector);
    lemma_f8_mod_xor(x as u16, y as u16);
}

/// `a * (x b) = x (a * b)`.
pub proof fn lemma_f8_mul_mulx(a: u8, b: u8)
    ensures
        f8_mul(a, mulx8(b)) == mulx8(f8_mul(a, b)),
{
    let m: u128 = if b >> 7u8 == 1 {
        modulus8()
    } else {
        0
    };
    // b x = mulx(b) + [b_7] M, as polynomials.
    assert((b as u128) << 1u128 == (mulx8(b) as u128) ^ (if b >> 7u8 == 1 {
        0x11Bu128
    } else {
        0u128
    })) by (bit_vector);
    lemma_clmul_shl1(a as u64, b as u128);
    lemma_clmul_xor_right(a as u64, mulx8(b) as u128, m);
    lemma_clmul8_closed(a, b);
    let p = clmul(a as u64, b as u128);
    let c16 = clmul8_closed(a, b);
    assert(p == (c16 as u128) && c16 >> 15u16 == 0 ==> (p << 1u128) as u16 == (p as u16) << 1u16 && (p as u16)
        >> 15u16 == 0) by (bit_vector);
    lemma_f8_mod_shl1(p as u16);
    let (x, y) = (clmul(a as u64, mulx8(b) as u128), clmul(a as u64, m));
    assert((x ^ y) as u16 == (x as u16) ^ (y as u16)) by (bit_vector);
    lemma_f8_mod_xor(x as u16, y as u16);
    if b >> 7u8 == 1 {
        lemma_f8_mod_multiple(a);
    } else {
        lemma_clmul_zero(a as u64);
        assert(0u16 >> 8u16 == 0) by (bit_vector);
        lemma_f8_mod_small(0);
    }
    let r = f8_mod(x as u16);
    assert(r ^ 0 == r) by (bit_vector);
}

pub proof fn lemma_f8_mul_mulx_pow(a: u8, b: u8, k: nat)
    ensures
        f8_mul(a, mulx8_pow(b, k)) == mulx8_pow(f8_mul(a, b), k),
    decreases k,
{
    if k > 0 {
        lemma_f8_mul_mulx_pow(a, b, (k - 1) as nat);
        lemma_f8_mul_mulx(a, mulx8_pow(b, (k - 1) as nat));
    }
}

/// `x^k` is `1 << k` for `k < 8`.
pub proof fn lemma_mulx8_pow_one(k: nat)
    requires
        k < 8,
    ensures
        mulx8_pow(1, k) == 1u8 << (k as u8),
    decreases k,
{
    if k == 0 {
        assert(1u8 << 0u8 == 1) by (bit_vector);
    } else {
        lemma_mulx8_pow_one((k - 1) as nat);
        let s = (k - 1) as u8;
        assert(s < 7 ==> mulx8(1u8 << s) == 1u8 << (s + 1)) by (bit_vector);
    }
}

/// `t * x^k = mulx^k(t)`.
pub proof fn lemma_f8_mul_monomial(t: u8, k: nat)
    requires
        k < 8,
    ensures
        f8_mul(t, 1u8 << (k as u8)) == mulx8_pow(t, k),
{
    lemma_mulx8_pow_one(k);
    lemma_f8_mul_mulx_pow(t, 1, k);
    lemma_f8_mul_one(t);
}

/// The low `n` coefficients of `c`, for `n <= 8`.
pub open spec fn low8(c: u8, n: u16) -> u8 {
    ((c as u16) & sub(1u16 << n, 1)) as u8
}

/// Associativity, by linearity in `c` and the monomial case `(a b) x^k = a (b x^k)`.
pub proof fn lemma_f8_mul_assoc_upto(a: u8, b: u8, c: u8, n: u16)
    requires
        n <= 8,
    ensures
        f8_mul(f8_mul(a, b), low8(c, n)) == f8_mul(a, f8_mul(b, low8(c, n))),
    decreases n,
{
    if n == 0 {
        assert(((c as u16) & sub(1u16 << 0u16, 1)) as u8 == 0) by (bit_vector);
        lemma_f8_mul_zero(f8_mul(a, b));
        lemma_f8_mul_zero(b);
        lemma_f8_mul_zero(a);
    } else {
        let i = sub(n, 1);
        lemma_f8_mul_assoc_upto(a, b, c, i);
        let e: u8 = if (c >> (i as u8)) & 1 == 1 {
            1u8 << (i as u8)
        } else {
            0
        };
        let lo = low8(c, i);
        assert(i < 8 ==> ((c as u16) & sub(1u16 << add(i, 1), 1)) as u8 == ((c as u16) & sub(1u16 << i, 1)) as u8
            ^ (if (c >> (i as u8)) & 1 == 1 {
            1u8 << (i as u8)
        } else {
            0u8
        })) by (bit_vector);
        assert(low8(c, n) == lo ^ e);
        lemma_f8_mul_xor_right(f8_mul(a, b), lo, e);
        lemma_f8_mul_xor_right(b, lo, e);
        lemma_f8_mul_xor_right(a, f8_mul(b, lo), f8_mul(b, e));
        if (c >> (i as u8)) & 1 == 1 {
            lemma_f8_mul_monomial(f8_mul(a, b), i as nat);
            lemma_f8_mul_monomial(b, i as nat);
            lemma_f8_mul_mulx_pow(a, b, i as nat);
        } else {
            lemma_f8_mul_zero(f8_mul(a, b));
            lemma_f8_mul_zero(b);
            lemma_f8_mul_zero(a);
        }
    }
}

pub proof fn lemma_f8_mul_assoc(a: u8, b: u8, c: u8)
    ensures
        f8_mul(f8_mul(a, b), c) == f8_mul(a, f8_mul(b, c)),
{
    lemma_f8_mul_assoc_upto(a, b, c, 8);
    assert(((c as u16) & sub(1u16 << 8u16, 1)) as u8 == c) by (bit_vector);
}

// ---------------------------------------------------------------------------------------------
// Powers
// ---------------------------------------------------------------------------------------------
pub proof fn lemma_f8_pow_add(a: u8, m: nat, n: nat)
    ensures
        f8_mul(f8_pow(a, m), f8_pow(a, n)) == f8_pow(a, m + n),
    decreases n,
{
    if n == 0 {
        lemma_f8_mul_one(f8_pow(a, m));
    } else {
        lemma_f8_pow_add(a, m, (n - 1) as nat);
        lemma_f8_mul_assoc(f8_pow(a, m), f8_pow(a, (n - 1) as nat), a);
        assert((m + n - 1) as nat + 1 == m + n);
    }
}

/// `a^255` by an addition chain over the closed-form product (`3 = 2 + 1`, `15 = 3 * 4 + 3`,
/// `255 = 15 * 16 + 15`): ten products, few enough for the interpreter to evaluate at every `a`.
pub open spec fn f8_pow255_chain(a: u8) -> u8 {
    let a3 = f8_mul_closed(f8_mul_closed(a, a), a);
    let a6 = f8_mul_closed(a3, a3);
    let a15 = f8_mul_closed(f8_mul_closed(a6, a6), a3);
    let a30 = f8_mul_closed(a15, a15);
    let a60 = f8_mul_closed(a30, a30);
    let a120 = f8_mul_closed(a60, a60);
    let a240 = f8_mul_closed(a120, a120);
    f8_mul_closed(a240, a15)
}

/// `f8_pow(a, x) * f8_pow(a, y) = f8_pow(a, x + y)`, with the product in closed form.
proof fn lemma_pow_closed_add(a: u8, x: nat, y: nat)
    ensures
        f8_mul_closed(f8_pow(a, x), f8_pow(a, y)) == f8_pow(a, x + y),
{
    lemma_f8_pow_add(a, x, y);
    lemma_f8_mul_closed(f8_pow(a, x), f8_pow(a, y));
}

pub proof fn lemma_f8_pow255_chain(a: u8)
    ensures
        f8_pow255_chain(a) == f8_pow(a, 255),
{
    assert(f8_pow(a, 1) == a) by {
        assert(f8_pow(a, 0) == 1);
        lemma_f8_mul_one(a);
    }
    lemma_pow_closed_add(a, 1, 1);
    lemma_pow_closed_add(a, 2, 1);
    lemma_pow_closed_add(a, 3, 3);
    lemma_pow_closed_add(a, 6, 6);
    lemma_pow_closed_add(a, 12, 3);
    lemma_pow_closed_add(a, 15, 15);
    lemma_pow_closed_add(a, 30, 30);
    lemma_pow_closed_add(a, 60, 60);
    lemma_pow_closed_add(a, 120, 120);
    lemma_pow_closed_add(a, 240, 15);
}

/// `a^255 = 1` for every nonzero `a <= n`.
pub open spec fn fermat_upto(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        f8_pow255_chain(n as u8) == 1 && fermat_upto((n - 1) as nat)
    }
}

proof fn lemma_fermat_upto(n: nat, a: u8)
    requires
        fermat_upto(n),
        0 < a <= n,
    ensures
        f8_pow255_chain(a) == 1,
    decreases n,
{
    if a < n {
        lemma_fermat_upto((n - 1) as nat, a);
    }
}

/// `a^254` is the inverse of every nonzero `a`, by evaluating `a^255` at all 255 of them.
///
/// Needs no irreducibility argument: the check is exhaustive.
pub proof fn lemma_f8_inv_correct(a: u8)
    requires
        a != 0,
    ensures
        f8_mul(a, f8_pow(a, 254)) == 1,
{
    assert(fermat_upto(255)) by (compute_only);
    lemma_fermat_upto(255, a);
    lemma_f8_pow255_chain(a);
    lemma_f8_mul_comm(a, f8_pow(a, 254));
}

// ---------------------------------------------------------------------------------------------
// Executable code: the portable paths of `crates/primitives/src/field/gf2_8.rs`
// ---------------------------------------------------------------------------------------------
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct F8(pub u8);

impl F8 {
    pub const ZERO: Self = Self(0);

    pub const ONE: Self = Self(1);

    /// Multiplicative inverse via Fermat: x^254 = x^{-1} in F_{2^8}.
    /// Exponent bit pattern 0xFE = 0b11111110: 7 squarings + 6 multiplies.
    pub fn inv(self) -> (r: Self)
        ensures
            r.0 == f8_pow(self.0, 254),
            self.0 != 0 ==> f8_mul(self.0, r.0) == 1,
    {
        let ghost a = self.0;
        proof {
            lemma2_to64();
            assert(f8_pow(a, 1) == a) by {
                assert(f8_pow(a, 0) == 1);
                lemma_f8_mul_one(a);
            }
        }
        let mut result = Self::ONE;
        let mut sq = self;
        for i in 0..8
            invariant
                sq.0 == f8_pow(a, pow2(i as nat)),
                result.0 == f8_pow(a, if i == 0 { 0 } else { (pow2(i as nat) - 2) as nat }),
                pow2(0) == 1 && pow2(1) == 2 && pow2(8) == 256,
        {
            proof {
                lemma_pow2_unfold((i + 1) as nat);
                lemma_pow2_pos(i as nat);
                lemma_f8_pow_add(a, pow2(i as nat), pow2(i as nat));
                if i > 0 {
                    lemma_f8_pow_add(a, (pow2(i as nat) - 2) as nat, pow2(i as nat));
                    if i > 1 {
                        lemma_pow2_strictly_increases(1, i as nat);
                    }
                }
                let s = i as u8;
                assert(s < 8 ==> (((0xFEu8 >> s) & 1 != 0) == (s != 0))) by (bit_vector);
            }
            if (0xFEu8 >> i) & 1 != 0 {
                result *= sq;
            }
            sq *= sq;
        }
        proof {
            if a != 0 {
                lemma_f8_inv_correct(a);
            }
        }
        result
    }
}

// In GF(2⁸), addition is bitwise XOR by definition. The `^` is correct, not a
// typo for `+` (which is what these Clippy lints guard against).
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl for F8 {
    open spec fn obeys_add_spec() -> bool {
        true
    }

    open spec fn add_req(self, rhs: F8) -> bool {
        true
    }

    open spec fn add_spec(self, rhs: F8) -> F8 {
        F8(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for F8 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> (r: Self)
        ensures
            r.0 == self.0 ^ rhs.0,
    {
        Self(self.0 ^ rhs.0)
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddAssignSpecImpl for F8 {
    open spec fn obeys_add_assign_spec() -> bool {
        true
    }

    open spec fn add_assign_req(&self, rhs: F8) -> bool {
        true
    }

    open spec fn add_assign_spec(&self, rhs: F8) -> &F8 {
        &F8(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl AddAssign for F8 {
    #[inline]
    fn add_assign(&mut self, rhs: Self)
        ensures
            final(self).0 == old(self).0 ^ rhs.0,
    {
        self.0 ^= rhs.0;
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl for F8 {
    open spec fn obeys_mul_spec() -> bool {
        true
    }

    open spec fn mul_req(self, rhs: F8) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: F8) -> F8 {
        F8(f8_mul(self.0, rhs.0))
    }
}

impl Mul for F8 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> (r: Self)
        ensures
            r.0 == f8_mul(self.0, rhs.0),
    {
        proof {
            lemma_clmul8_closed(self.0, rhs.0);
        }
        Self(gf8_reduce(clmul8(self.0, rhs.0)))
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulAssignSpecImpl for F8 {
    open spec fn obeys_mul_assign_spec() -> bool {
        true
    }

    open spec fn mul_assign_req(&self, rhs: F8) -> bool {
        true
    }

    open spec fn mul_assign_spec(&self, rhs: F8) -> &F8 {
        &F8(f8_mul(self.0, rhs.0))
    }
}

impl MulAssign for F8 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self)
        ensures
            final(self).0 == f8_mul(old(self).0, rhs.0),
    {
        *self = *self * rhs;
    }
}

/// Carry-less product of two bytes; result fits in 15 bits.
///
/// The portable arm only: the NEON arm (`clmul8_neon`, PMULL) is out of scope.
#[inline]
fn clmul8(a: u8, b: u8) -> (r: u16)
    ensures
        r as u128 == clmul(a as u64, b as u128),
{
    clmul8_software(a, b)
}

/// Software fallback / test oracle. Used when `aes` is off, and as the
/// cross-check oracle inside the `software_matches_neon` unit test.
#[allow(dead_code)]
#[inline]
pub const fn clmul8_software(a: u8, b: u8) -> (r: u16)
    ensures
        r as u128 == clmul(a as u64, b as u128),
{
    let b16 = b as u16;
    let mut acc: u16 = 0;
    let mut i = 0;
    while i < 8
        invariant
            0 <= i <= 8,
            b16 == b as u16,
            acc as u128 == clmul_upto(a as u64, b as u128, i as nat),
        decreases 8 - i,
    {
        proof {
            let s = i as u16;
            assert(s < 8 ==> ((a >> s) & 1 != 0) == (((a as u64) >> (s as u64)) & 1 == 1)) by (bit_vector);
            assert(s < 8 ==> (acc ^ ((b as u16) << s)) as u128 == (acc as u128) ^ ((b as u128) << (s as u128)))
                by (bit_vector);
            assert((acc as u128) ^ 0 == acc as u128) by (bit_vector);
            assert(term(a as u64, b as u128, i as nat) == if ((a as u64) >> (s as u64)) & 1 == 1 {
                (b as u128) << (s as u128)
            } else {
                0
            });
        }
        if (a >> i) & 1 != 0 {
            acc ^= b16 << i;
        }
        i += 1;
    }
    proof {
        lemma_clmul_upto_byte(a, b as u128, 64);
    }
    acc
}

/// Reduce a polynomial of degree ≤ 14 modulo x^8 + x^4 + x^3 + x + 1.
/// Two-step fold: first turns 15-bit input into ≤12-bit, second into ≤8-bit.
///
/// Exposed `pub` so flock's URM shift_reduce inner kernel can reuse it.
///
/// Proven for every `p: u16`, degree 15 included: the result is the remainder of `p` modulo `M`.
#[inline]
pub const fn gf8_reduce(p: u16) -> (r: u8)
    ensures
        r == f8_mod(p),
        is_remainder8(p, r),
{
    proof {
        lemma_f8_mod(p);
    }
    let h: u16 = p >> 8;
    let t: u16 = (p & 0xff) ^ h ^ (h << 1) ^ (h << 3) ^ (h << 4);
    let h2: u16 = t >> 8;
    ((t & 0xff) ^ h2 ^ (h2 << 1) ^ (h2 << 3) ^ (h2 << 4)) as u8
}

} // verus!
