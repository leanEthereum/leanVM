//! The base field `K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`.
//!
//! The executable functions are the portable paths of `crates/primitives/src/field/gf2_64.rs`, copied
//! with the same bodies; `tests/equivalence.rs` checks the two agree.
//!
//! Specification: an element is a polynomial over GF(2) of degree below 64, bit `i` its coefficient of
//! `x^i`. The product [`k_mul`] is the carry-less product ([`clmul`]) reduced modulo
//! `M = x^64 + x^4 + x^3 + x + 1`, where "reduced" is the definition of a remainder ([`is_remainder`]).
use crate::clmul::*;
use core::ops::{Add, AddAssign, Mul, MulAssign};
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// The modulus `M = x^64 + x^4 + x^3 + x + 1`, as a 65-bit polynomial.
pub open spec fn modulus() -> u128 {
    0x1_0000_0000_0000_001Bu128
}

/// `r` is the remainder of `p` modulo `M`: `p = q * M + r` for some polynomial `q`, and `deg r < 64`.
///
/// A `p` of degree below 128 has a quotient of degree below 64, so `q: u64` loses nothing.
pub open spec fn is_remainder(p: u128, r: u64) -> bool {
    exists|q: u64| p == clmul(q, modulus()) ^ (r as u128)
}

/// `p mod M`, the unique remainder (unique by [`lemma_remainder_unique`]).
pub open spec fn k_mod(p: u128) -> u64 {
    choose|r: u64| is_remainder(p, r)
}

/// The product in `K`: `a * b mod M`.
pub open spec fn k_mul(a: u64, b: u64) -> u64 {
    k_mod(clmul(a, b as u128))
}

/// `a^n` in `K`.
pub open spec fn k_pow(a: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        1
    } else {
        k_mul(k_pow(a, (n - 1) as nat), a)
    }
}

/// `a` squared `n` times, `a^(2^n)` by [`lemma_k_sq_iter_pow`].
pub open spec fn k_sq_iter(a: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        a
    } else {
        let v = k_sq_iter(a, (n - 1) as nat);
        k_mul(v, v)
    }
}

// ---------------------------------------------------------------------------------------------
// The reduction
// ---------------------------------------------------------------------------------------------
/// The closed form of the production `reduce`, as a spec function.
pub open spec fn reduce_formula(p: u128) -> u64 {
    let (lo, hi) = (p as u64, (p >> 64u128) as u64);
    let spill = (hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64);
    let v = hi ^ spill;
    lo ^ v ^ (v << 1u64) ^ (v << 3u64) ^ (v << 4u64)
}

/// Multiplication by `x` in `K`: shift, and fold `x^64` back as `x^4 + x^3 + x + 1`.
pub open spec fn mulx(a: u64) -> u64 {
    (a << 1u64) ^ (if a >> 63u64 == 1 {
        0x1Bu64
    } else {
        0u64
    })
}

/// `a * x^k` in `K`.
pub open spec fn mulx_pow(a: u64, k: nat) -> u64
    decreases k,
{
    if k == 0 {
        a
    } else {
        mulx(mulx_pow(a, (k - 1) as nat))
    }
}

/// `q * (x^4 + x^3 + x + 1) = q ^ q<<1 ^ q<<3 ^ q<<4`, the product by the reduction constant `0x1B`.
pub open spec fn times_r64(q: u64) -> u128 {
    let w = q as u128;
    w ^ (w << 1u128) ^ (w << 3u128) ^ (w << 4u128)
}

pub proof fn lemma_clmul_r64(q: u64)
    ensures
        clmul(q, 0x1Bu128) == times_r64(q),
{
    assert(0x1Bu128 == (1u128 << 0u128) ^ (1u128 << 1u128) ^ (1u128 << 3u128) ^ (1u128 << 4u128))
        by (bit_vector);
    let (e0, e1, e3, e4) = (1u128 << 0u128, 1u128 << 1u128, 1u128 << 3u128, 1u128 << 4u128);
    lemma_clmul_xor_right(q, e0 ^ e1 ^ e3, e4);
    lemma_clmul_xor_right(q, e0 ^ e1, e3);
    lemma_clmul_xor_right(q, e0, e1);
    lemma_clmul_monomial(q, 0);
    lemma_clmul_monomial(q, 1);
    lemma_clmul_monomial(q, 3);
    lemma_clmul_monomial(q, 4);
    let w = q as u128;
    assert(w << 0u128 == w) by (bit_vector);
}

/// `q * M = q x^64 + q * 0x1B`.
pub proof fn lemma_clmul_modulus(q: u64)
    ensures
        clmul(q, modulus()) == ((q as u128) << 64u128) ^ times_r64(q),
{
    assert(modulus() == 0x1Bu128 ^ (1u128 << 64u128)) by (bit_vector);
    lemma_clmul_xor_right(q, 0x1Bu128, 1u128 << 64u128);
    lemma_clmul_r64(q);
    lemma_clmul_monomial(q, 64);
    let (a, b) = (times_r64(q), (q as u128) << 64u128);
    assert(a ^ b == b ^ a) by (bit_vector);
}

/// The production reduction returns a remainder of `p` modulo `M`, with quotient `hi ^ spill`.
pub proof fn lemma_reduce_formula_is_remainder(p: u128)
    ensures
        is_remainder(p, reduce_formula(p)),
{
    let hi = (p >> 64u128) as u64;
    let q = hi ^ ((hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64));
    lemma_clmul_modulus(q);
    assert({
        let hi = (p >> 64u128) as u64;
        let q = hi ^ ((hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64));
        let w = q as u128;
        p == ((w << 64u128) ^ (w ^ (w << 1u128) ^ (w << 3u128) ^ (w << 4u128))) ^ (reduce_formula(p) as u128)
    }) by (bit_vector);
}

/// The remainder modulo `M` is unique.
pub proof fn lemma_remainder_unique(p: u128, r1: u64, r2: u64)
    requires
        is_remainder(p, r1),
        is_remainder(p, r2),
    ensures
        r1 == r2,
{
    let q1 = choose|q: u64| p == clmul(q, modulus()) ^ (r1 as u128);
    let q2 = choose|q: u64| p == clmul(q, modulus()) ^ (r2 as u128);
    lemma_clmul_modulus(q1);
    lemma_clmul_modulus(q2);
    assert({
        let (w1, w2) = (q1 as u128, q2 as u128);
        ((w1 << 64u128) ^ (w1 ^ (w1 << 1u128) ^ (w1 << 3u128) ^ (w1 << 4u128))) ^ (r1 as u128) == ((w2
            << 64u128) ^ (w2 ^ (w2 << 1u128) ^ (w2 << 3u128) ^ (w2 << 4u128))) ^ (r2 as u128) ==> r1 == r2
    }) by (bit_vector);
}

/// `p mod M` is the production reduction's closed form.
pub proof fn lemma_k_mod(p: u128)
    ensures
        k_mod(p) == reduce_formula(p),
        is_remainder(p, k_mod(p)),
{
    lemma_reduce_formula_is_remainder(p);
    lemma_remainder_unique(p, k_mod(p), reduce_formula(p));
}

/// Reduction is GF(2)-linear.
pub proof fn lemma_k_mod_xor(p1: u128, p2: u128)
    ensures
        k_mod(p1 ^ p2) == k_mod(p1) ^ k_mod(p2),
{
    lemma_k_mod(p1);
    lemma_k_mod(p2);
    lemma_k_mod(p1 ^ p2);
    assert(reduce_formula(p1 ^ p2) == reduce_formula(p1) ^ reduce_formula(p2)) by (bit_vector);
}

/// A polynomial of degree below 64 is its own remainder.
pub proof fn lemma_k_mod_small(p: u128)
    requires
        p >> 64u128 == 0,
    ensures
        k_mod(p) == p as u64,
{
    lemma_k_mod(p);
    assert(p >> 64u128 == 0 ==> reduce_formula(p) == p as u64) by (bit_vector);
}

/// `(p x) mod M = (p mod M) x mod M`.
pub proof fn lemma_k_mod_shl1(p: u128)
    requires
        p >> 127u128 == 0,
    ensures
        k_mod(p << 1u128) == mulx(k_mod(p)),
{
    lemma_k_mod(p);
    lemma_k_mod(p << 1u128);
    assert(p >> 127u128 == 0 ==> reduce_formula(p << 1u128) == mulx(reduce_formula(p))) by (bit_vector);
}

/// A multiple of `M` reduces to zero.
pub proof fn lemma_k_mod_multiple(q: u64)
    ensures
        k_mod(clmul(q, modulus())) == 0,
{
    lemma_clmul_modulus(q);
    lemma_k_mod(clmul(q, modulus()));
    assert({
        let w = q as u128;
        reduce_formula((w << 64u128) ^ (w ^ (w << 1u128) ^ (w << 3u128) ^ (w << 4u128))) == 0
    }) by (bit_vector);
}

// ---------------------------------------------------------------------------------------------
// K is a commutative ring
// ---------------------------------------------------------------------------------------------
pub proof fn lemma_k_mul_comm(a: u64, b: u64)
    ensures
        k_mul(a, b) == k_mul(b, a),
{
    lemma_clmul_comm(a, b);
}

pub proof fn lemma_k_mul_xor_right(a: u64, b: u64, c: u64)
    ensures
        k_mul(a, b ^ c) == k_mul(a, b) ^ k_mul(a, c),
{
    assert((b ^ c) as u128 == (b as u128) ^ (c as u128)) by (bit_vector);
    lemma_clmul_xor_right(a, b as u128, c as u128);
    lemma_k_mod_xor(clmul(a, b as u128), clmul(a, c as u128));
}

pub proof fn lemma_k_mul_xor_left(a: u64, b: u64, c: u64)
    ensures
        k_mul(a ^ b, c) == k_mul(a, c) ^ k_mul(b, c),
{
    lemma_k_mul_comm(a ^ b, c);
    lemma_k_mul_comm(a, c);
    lemma_k_mul_comm(b, c);
    lemma_k_mul_xor_right(c, a, b);
}

pub proof fn lemma_k_mul_one(a: u64)
    ensures
        k_mul(a, 1) == a,
        k_mul(1, a) == a,
{
    assert(1u64 as u128 == 1u128 << 0u128) by (bit_vector);
    lemma_clmul_monomial(a, 0);
    assert((a as u128) << 0u128 == (a as u128) && (a as u128) >> 64u128 == 0) by (bit_vector);
    lemma_k_mod_small(a as u128);
    lemma_k_mul_comm(a, 1);
}

pub proof fn lemma_k_mul_zero(a: u64)
    ensures
        k_mul(a, 0) == 0,
        k_mul(0, a) == 0,
{
    lemma_clmul_zero(a);
    assert(0u128 >> 64u128 == 0) by (bit_vector);
    lemma_k_mod_small(0);
    lemma_k_mul_comm(a, 0);
}

/// `a * (x b) = x (a * b)`.
pub proof fn lemma_k_mul_mulx(a: u64, b: u64)
    ensures
        k_mul(a, mulx(b)) == mulx(k_mul(a, b)),
{
    let m: u128 = if b >> 63u64 == 1 {
        modulus()
    } else {
        0
    };
    // b x = mulx(b) + [b_63] M, as polynomials.
    assert((b as u128) << 1u128 == (mulx(b) as u128) ^ (if b >> 63u64 == 1 {
        0x1_0000_0000_0000_001Bu128
    } else {
        0u128
    })) by (bit_vector);
    lemma_clmul_shl1(a, b as u128);
    lemma_clmul_xor_right(a, mulx(b) as u128, m);
    lemma_clmul_bound(a, b);
    lemma_k_mod_shl1(clmul(a, b as u128));
    lemma_k_mod_xor(clmul(a, mulx(b) as u128), clmul(a, m));
    if b >> 63u64 == 1 {
        lemma_k_mod_multiple(a);
    } else {
        lemma_clmul_zero(a);
        assert(0u128 >> 64u128 == 0) by (bit_vector);
        lemma_k_mod_small(0);
    }
    let r = k_mod(clmul(a, mulx(b) as u128));
    assert(r ^ 0 == r) by (bit_vector);
}

pub proof fn lemma_k_mul_mulx_pow(a: u64, b: u64, k: nat)
    ensures
        k_mul(a, mulx_pow(b, k)) == mulx_pow(k_mul(a, b), k),
    decreases k,
{
    if k > 0 {
        lemma_k_mul_mulx_pow(a, b, (k - 1) as nat);
        lemma_k_mul_mulx(a, mulx_pow(b, (k - 1) as nat));
    }
}

/// `x^k` is `1 << k` for `k < 64`.
pub proof fn lemma_mulx_pow_one(k: nat)
    requires
        k < 64,
    ensures
        mulx_pow(1, k) == 1u64 << (k as u64),
    decreases k,
{
    if k == 0 {
        assert(1u64 << 0u64 == 1) by (bit_vector);
    } else {
        lemma_mulx_pow_one((k - 1) as nat);
        let s = (k - 1) as u64;
        assert(s < 63 ==> mulx(1u64 << s) == 1u64 << (s + 1)) by (bit_vector);
    }
}

/// `t * x^k = mulx^k(t)`.
pub proof fn lemma_k_mul_monomial(t: u64, k: nat)
    requires
        k < 64,
    ensures
        k_mul(t, 1u64 << (k as u64)) == mulx_pow(t, k),
{
    lemma_mulx_pow_one(k);
    lemma_k_mul_mulx_pow(t, 1, k);
    lemma_k_mul_one(t);
}

/// Associativity, by linearity in `c` and the monomial case `(a b) x^k = a (b x^k)`.
pub proof fn lemma_k_mul_assoc_upto(a: u64, b: u64, c: u64, n: nat)
    requires
        n <= 64,
    ensures
        k_mul(k_mul(a, b), low(c, n)) == k_mul(a, k_mul(b, low(c, n))),
    decreases n,
{
    if n == 0 {
        assert(low(c, 0) == 0) by {
            assert(c & ((1u64 << 0u64) - 1) as u64 == 0) by (bit_vector);
        }
        lemma_k_mul_zero(k_mul(a, b));
        lemma_k_mul_zero(b);
        lemma_k_mul_zero(a);
    } else {
        let i = (n - 1) as nat;
        lemma_k_mul_assoc_upto(a, b, c, i);
        lemma_low_step(c, i);
        let e: u64 = if bit(c, i) {
            1u64 << (i as u64)
        } else {
            0
        };
        let lo = low(c, i);
        lemma_k_mul_xor_right(k_mul(a, b), lo, e);
        lemma_k_mul_xor_right(b, lo, e);
        lemma_k_mul_xor_right(a, k_mul(b, lo), k_mul(b, e));
        if bit(c, i) {
            lemma_k_mul_monomial(k_mul(a, b), i);
            lemma_k_mul_monomial(b, i);
            lemma_k_mul_mulx_pow(a, b, i);
        } else {
            lemma_k_mul_zero(k_mul(a, b));
            lemma_k_mul_zero(b);
            lemma_k_mul_zero(a);
        }
    }
}

pub proof fn lemma_k_mul_assoc(a: u64, b: u64, c: u64)
    ensures
        k_mul(k_mul(a, b), c) == k_mul(a, k_mul(b, c)),
{
    lemma_k_mul_assoc_upto(a, b, c, 64);
}

// ---------------------------------------------------------------------------------------------
// Powers
// ---------------------------------------------------------------------------------------------
pub proof fn lemma_k_pow_add(a: u64, m: nat, n: nat)
    ensures
        k_mul(k_pow(a, m), k_pow(a, n)) == k_pow(a, m + n),
    decreases n,
{
    if n == 0 {
        lemma_k_mul_one(k_pow(a, m));
    } else {
        lemma_k_pow_add(a, m, (n - 1) as nat);
        lemma_k_mul_assoc(k_pow(a, m), k_pow(a, (n - 1) as nat), a);
        assert((m + n - 1) as nat + 1 == m + n);
    }
}

/// Squaring `n` times raises to the power `2^n`: `(a^m)^(2^n) = a^(m 2^n)`.
pub proof fn lemma_k_sq_iter_pow(a: u64, m: nat, n: nat)
    ensures
        k_sq_iter(k_pow(a, m), n) == k_pow(a, m * pow2(n)),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
        assert(m * pow2(0) == m) by (nonlinear_arith)
            requires
                pow2(0) == 1,
        ;
    } else {
        lemma_k_sq_iter_pow(a, m, (n - 1) as nat);
        let e = m * pow2((n - 1) as nat);
        lemma_k_pow_add(a, e, e);
        lemma_pow2_unfold(n);
        assert(e + e == m * pow2(n)) by (nonlinear_arith)
            requires
                e == m * pow2((n - 1) as nat),
                pow2(n) == 2 * pow2((n - 1) as nat),
        ;
    }
}

pub proof fn lemma_k_sq_iter_add(a: u64, m: nat, n: nat)
    ensures
        k_sq_iter(k_sq_iter(a, m), n) == k_sq_iter(a, m + n),
    decreases n,
{
    if n > 0 {
        lemma_k_sq_iter_add(a, m, (n - 1) as nat);
    }
}

// ---------------------------------------------------------------------------------------------
// Fermat: every element of K is fixed by the 64th power of squaring, a^(2^64) = a
// ---------------------------------------------------------------------------------------------
/// The carry-less square in closed form: bit `i` of `a` moves to bit `2i` (Morton spread with zeros).
pub open spec fn spread(a: u64) -> u128 {
    let x = a as u128;
    let x = (x | (x << 32u128)) & 0x0000_0000_FFFF_FFFF_0000_0000_FFFF_FFFFu128;
    let x = (x | (x << 16u128)) & 0x0000_FFFF_0000_FFFF_0000_FFFF_0000_FFFFu128;
    let x = (x | (x << 8u128)) & 0x00FF_00FF_00FF_00FF_00FF_00FF_00FF_00FFu128;
    let x = (x | (x << 4u128)) & 0x0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0Fu128;
    let x = (x | (x << 2u128)) & 0x3333_3333_3333_3333_3333_3333_3333_3333u128;
    (x | (x << 1u128)) & 0x5555_5555_5555_5555_5555_5555_5555_5555u128
}

/// The square of a polynomial over GF(2) is its bit spread: cross terms cancel in pairs.
pub proof fn lemma_clmul_square_upto(a: u64, n: nat)
    requires
        n <= 64,
    ensures
        clmul(low(a, n), low(a, n) as u128) == spread(low(a, n)),
    decreases n,
{
    if n == 0 {
        assert(low(a, 0) == 0) by {
            assert(a & ((1u64 << 0u64) - 1) as u64 == 0) by (bit_vector);
        }
        lemma_clmul_zero(0);
        assert(spread(0) == 0) by (bit_vector);
    } else {
        let i = (n - 1) as nat;
        lemma_clmul_square_upto(a, i);
        lemma_low_step(a, i);
        let l = low(a, i);
        let e: u64 = if bit(a, i) {
            1u64 << (i as u64)
        } else {
            0
        };
        let (lw, ew) = (l as u128, e as u128);
        assert((l ^ e) as u128 == (l as u128) ^ (e as u128)) by (bit_vector);
        lemma_clmul_xor_left(l, e, lw ^ ew);
        lemma_clmul_xor_right(l, lw, ew);
        lemma_clmul_xor_right(e, lw, ew);
        lemma_clmul_comm(l, e);
        assert(spread(l ^ e) == spread(l) ^ spread(e)) by (bit_vector);
        if bit(a, i) {
            let s = i as u64;
            assert(s < 64 ==> ((1u64 << s) as u128) == 1u128 << (s as u128)) by (bit_vector);
            lemma_clmul_monomial(e, i as u128);
            assert(s < 64 ==> ((1u64 << s) as u128) << (s as u128) == spread(1u64 << s)) by (bit_vector);
        } else {
            lemma_clmul_zero(0);
            lemma_clmul_zero(l);
            lemma_clmul_comm(l, 0);
            assert(spread(0) == 0) by (bit_vector);
        }
        let (x, y, z) = (clmul(l, lw), clmul(l, ew), clmul(e, ew));
        assert((x ^ y) ^ (y ^ z) == x ^ z) by (bit_vector);
    }
}

/// Squaring in `K` in closed form.
pub proof fn lemma_k_square(a: u64)
    ensures
        k_mul(a, a) == reduce_formula(spread(a)),
{
    lemma_clmul_square_upto(a, 64);
    lemma_k_mod(clmul(a, a as u128));
}

/// `(a + b)^2 = a^2 + b^2`.
pub proof fn lemma_k_square_xor(a: u64, b: u64)
    ensures
        k_mul(a ^ b, a ^ b) == k_mul(a, a) ^ k_mul(b, b),
{
    lemma_k_mul_xor_left(a, b, a ^ b);
    lemma_k_mul_xor_right(a, a, b);
    lemma_k_mul_xor_right(b, a, b);
    lemma_k_mul_comm(a, b);
    let (x, y, z) = (k_mul(a, a), k_mul(a, b), k_mul(b, b));
    assert((x ^ y) ^ (y ^ z) == x ^ z) by (bit_vector);
}

pub proof fn lemma_k_sq_iter_xor(a: u64, b: u64, n: nat)
    ensures
        k_sq_iter(a ^ b, n) == k_sq_iter(a, n) ^ k_sq_iter(b, n),
    decreases n,
{
    if n > 0 {
        lemma_k_sq_iter_xor(a, b, (n - 1) as nat);
        lemma_k_square_xor(k_sq_iter(a, (n - 1) as nat), k_sq_iter(b, (n - 1) as nat));
    }
}

/// `(a b)^2 = a^2 b^2`.
pub proof fn lemma_k_square_mul(a: u64, b: u64)
    ensures
        k_mul(k_mul(a, b), k_mul(a, b)) == k_mul(k_mul(a, a), k_mul(b, b)),
{
    let ab = k_mul(a, b);
    lemma_k_mul_assoc(a, b, ab);
    lemma_k_mul_assoc(b, a, b);
    lemma_k_mul_comm(a, b);
    lemma_k_mul_assoc(a, b, b);
    lemma_k_mul_assoc(a, a, k_mul(b, b));
    lemma_k_mul_comm(b, ab);
}

pub proof fn lemma_k_sq_iter_mul(a: u64, b: u64, n: nat)
    ensures
        k_sq_iter(k_mul(a, b), n) == k_mul(k_sq_iter(a, n), k_sq_iter(b, n)),
    decreases n,
{
    if n > 0 {
        lemma_k_sq_iter_mul(a, b, (n - 1) as nat);
        lemma_k_square_mul(k_sq_iter(a, (n - 1) as nat), k_sq_iter(b, (n - 1) as nat));
    }
}

pub proof fn lemma_k_sq_iter_one(n: nat)
    ensures
        k_sq_iter(1, n) == 1,
    decreases n,
{
    if n > 0 {
        lemma_k_sq_iter_one((n - 1) as nat);
        lemma_k_mul_one(1);
    }
}

pub proof fn lemma_k_sq_iter_zero(n: nat)
    ensures
        k_sq_iter(0, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_k_sq_iter_zero((n - 1) as nat);
        lemma_k_mul_zero(0);
    }
}

/// Squaring commutes with powers: `(a^i)^(2^n) = (a^(2^n))^i`.
pub proof fn lemma_k_sq_iter_k_pow(a: u64, i: nat, n: nat)
    ensures
        k_sq_iter(k_pow(a, i), n) == k_pow(k_sq_iter(a, n), i),
    decreases i,
{
    if i == 0 {
        lemma_k_sq_iter_one(n);
    } else {
        lemma_k_sq_iter_k_pow(a, (i - 1) as nat, n);
        lemma_k_sq_iter_mul(k_pow(a, (i - 1) as nat), a, n);
    }
}

/// The powers of the generator `x` below `x^64` are the monomials.
pub proof fn lemma_k_pow_x(i: nat)
    requires
        i < 64,
    ensures
        k_pow(2, i) == 1u64 << (i as u64),
    decreases i,
{
    if i == 0 {
        assert(1u64 << 0u64 == 1) by (bit_vector);
    } else {
        lemma_k_pow_x((i - 1) as nat);
        let t = k_pow(2, (i - 1) as nat);
        assert(2u64 == 1u64 << 1u64) by (bit_vector);
        lemma_k_mul_monomial(t, 1);
        assert(mulx_pow(t, 0) == t);
        let s = (i - 1) as u64;
        assert(s < 63 ==> mulx(1u64 << s) == 1u64 << (s + 1)) by (bit_vector);
    }
}

/// Squarings 0 to 8 of `x`.
proof fn lemma_k_frobenius_x_0()
    ensures
        k_sq_iter(0x2u64, 8) == 0x11011u64,
{
    assert(k_sq_iter(0x2u64, 0) == 0x2u64);
    lemma_k_square(0x2u64);
    assert(reduce_formula(spread(0x2u64)) == 0x4u64) by (bit_vector);
    assert(k_sq_iter(0x2u64, 1) == 0x4u64);
    lemma_k_square(0x4u64);
    assert(reduce_formula(spread(0x4u64)) == 0x10u64) by (bit_vector);
    assert(k_sq_iter(0x2u64, 2) == 0x10u64);
    lemma_k_square(0x10u64);
    assert(reduce_formula(spread(0x10u64)) == 0x100u64) by (bit_vector);
    assert(k_sq_iter(0x2u64, 3) == 0x100u64);
    lemma_k_square(0x100u64);
    assert(reduce_formula(spread(0x100u64)) == 0x10000u64) by (bit_vector);
    assert(k_sq_iter(0x2u64, 4) == 0x10000u64);
    lemma_k_square(0x10000u64);
    assert(reduce_formula(spread(0x10000u64)) == 0x100000000u64) by (bit_vector);
    assert(k_sq_iter(0x2u64, 5) == 0x100000000u64);
    lemma_k_square(0x100000000u64);
    assert(reduce_formula(spread(0x100000000u64)) == 0x1bu64) by (bit_vector);
    assert(k_sq_iter(0x2u64, 6) == 0x1bu64);
    lemma_k_square(0x1bu64);
    assert(reduce_formula(spread(0x1bu64)) == 0x145u64) by (bit_vector);
    assert(k_sq_iter(0x2u64, 7) == 0x145u64);
    lemma_k_square(0x145u64);
    assert(reduce_formula(spread(0x145u64)) == 0x11011u64) by (bit_vector);
    assert(k_sq_iter(0x2u64, 8) == 0x11011u64);
}

/// Squarings 8 to 16 of `x`.
proof fn lemma_k_frobenius_x_1()
    ensures
        k_sq_iter(0x11011u64, 8) == 0x15f0144001a114fu64,
{
    assert(k_sq_iter(0x11011u64, 0) == 0x11011u64);
    lemma_k_square(0x11011u64);
    assert(reduce_formula(spread(0x11011u64)) == 0x101000101u64) by (bit_vector);
    assert(k_sq_iter(0x11011u64, 1) == 0x101000101u64);
    lemma_k_square(0x101000101u64);
    assert(reduce_formula(spread(0x101000101u64)) == 0x100000001001au64) by (bit_vector);
    assert(k_sq_iter(0x11011u64, 2) == 0x100000001001au64);
    lemma_k_square(0x100000001001au64);
    assert(reduce_formula(spread(0x100000001001au64)) == 0x1a00000144u64) by (bit_vector);
    assert(k_sq_iter(0x11011u64, 3) == 0x1a00000144u64);
    lemma_k_square(0x1a00000144u64);
    assert(reduce_formula(spread(0x1a00000144u64)) == 0x10dbcu64) by (bit_vector);
    assert(k_sq_iter(0x11011u64, 4) == 0x10dbcu64);
    lemma_k_square(0x10dbcu64);
    assert(reduce_formula(spread(0x10dbcu64)) == 0x100514550u64) by (bit_vector);
    assert(k_sq_iter(0x11011u64, 5) == 0x100514550u64);
    lemma_k_square(0x100514550u64);
    assert(reduce_formula(spread(0x100514550u64)) == 0x11011011111bu64) by (bit_vector);
    assert(k_sq_iter(0x11011u64, 6) == 0x11011011111bu64);
    lemma_k_square(0x11011011111bu64);
    assert(reduce_formula(spread(0x11011011111bu64)) == 0x10001011a1a015eu64) by (bit_vector);
    assert(k_sq_iter(0x11011u64, 7) == 0x10001011a1a015eu64);
    lemma_k_square(0x10001011a1a015eu64);
    assert(reduce_formula(spread(0x10001011a1a015eu64)) == 0x15f0144001a114fu64) by (bit_vector);
    assert(k_sq_iter(0x11011u64, 8) == 0x15f0144001a114fu64);
}

/// Squarings 16 to 24 of `x`.
proof fn lemma_k_frobenius_x_2()
    ensures
        k_sq_iter(0x15f0144001a114fu64, 8) == 0xb6d535c542116f62u64,
{
    assert(k_sq_iter(0x15f0144001a114fu64, 0) == 0x15f0144001a114fu64);
    lemma_k_square(0x15f0144001a114fu64);
    assert(reduce_formula(spread(0x15f0144001a114fu64)) == 0x1aad43011ba1e5u64) by (bit_vector);
    assert(k_sq_iter(0x15f0144001a114fu64, 1) == 0x1aad43011ba1e5u64);
    lemma_k_square(0x1aad43011ba1e5u64);
    assert(reduce_formula(spread(0x1aad43011ba1e5u64)) == 0x11cefef6be466u64) by (bit_vector);
    assert(k_sq_iter(0x15f0144001a114fu64, 2) == 0x11cefef6be466u64);
    lemma_k_square(0x11cefef6be466u64);
    assert(reduce_formula(spread(0x11cefef6be466u64)) == 0x5455145e48670f13u64) by (bit_vector);
    assert(k_sq_iter(0x15f0144001a114fu64, 3) == 0x5455145e48670f13u64);
    lemma_k_square(0x5455145e48670f13u64);
    assert(reduce_formula(spread(0x5455145e48670f13u64)) == 0xbaf1bebe1ae4ad02u64) by (bit_vector);
    assert(k_sq_iter(0x15f0144001a114fu64, 4) == 0xbaf1bebe1ae4ad02u64);
    lemma_k_square(0xbaf1bebe1ae4ad02u64);
    assert(reduce_formula(spread(0xbaf1bebe1ae4ad02u64)) == 0xb0ef530df44bb042u64) by (bit_vector);
    assert(k_sq_iter(0x15f0144001a114fu64, 5) == 0xb0ef530df44bb042u64);
    lemma_k_square(0xb0ef530df44bb042u64);
    assert(reduce_formula(spread(0xb0ef530df44bb042u64)) == 0xe2170b43ee771735u64) by (bit_vector);
    assert(k_sq_iter(0x15f0144001a114fu64, 6) == 0xe2170b43ee771735u64);
    lemma_k_square(0xe2170b43ee771735u64);
    assert(reduce_formula(spread(0xe2170b43ee771735u64)) == 0x48380fd207a3b527u64) by (bit_vector);
    assert(k_sq_iter(0x15f0144001a114fu64, 7) == 0x48380fd207a3b527u64);
    lemma_k_square(0x48380fd207a3b527u64);
    assert(reduce_formula(spread(0x48380fd207a3b527u64)) == 0xb6d535c542116f62u64) by (bit_vector);
    assert(k_sq_iter(0x15f0144001a114fu64, 8) == 0xb6d535c542116f62u64);
}

/// Squarings 24 to 32 of `x`.
proof fn lemma_k_frobenius_x_3()
    ensures
        k_sq_iter(0xb6d535c542116f62u64, 8) == 0x5c62236777028505u64,
{
    assert(k_sq_iter(0xb6d535c542116f62u64, 0) == 0xb6d535c542116f62u64);
    lemma_k_square(0xb6d535c542116f62u64);
    assert(reduce_formula(spread(0xb6d535c542116f62u64)) == 0xa6df6baa62f965f5u64) by (bit_vector);
    assert(k_sq_iter(0xb6d535c542116f62u64, 1) == 0xa6df6baa62f965f5u64);
    lemma_k_square(0xa6df6baa62f965f5u64);
    assert(reduce_formula(spread(0xa6df6baa62f965f5u64)) == 0xb9df3947cea0ffe7u64) by (bit_vector);
    assert(k_sq_iter(0xb6d535c542116f62u64, 2) == 0xb9df3947cea0ffe7u64);
    lemma_k_square(0xb9df3947cea0ffe7u64);
    assert(reduce_formula(spread(0xb9df3947cea0ffe7u64)) == 0xe1882807248fe588u64) by (bit_vector);
    assert(k_sq_iter(0xb6d535c542116f62u64, 3) == 0xe1882807248fe588u64);
    lemma_k_square(0xe1882807248fe588u64);
    assert(reduce_formula(spread(0xe1882807248fe588u64)) == 0x180d86953ed141c6u64) by (bit_vector);
    assert(k_sq_iter(0xb6d535c542116f62u64, 4) == 0x180d86953ed141c6u64);
    lemma_k_square(0x180d86953ed141c6u64);
    assert(reduce_formula(spread(0x180d86953ed141c6u64)) == 0x1894566cd1db8abfu64) by (bit_vector);
    assert(k_sq_iter(0xb6d535c542116f62u64, 5) == 0x1894566cd1db8abfu64);
    lemma_k_square(0x1894566cd1db8abfu64);
    assert(reduce_formula(spread(0x1894566cd1db8abfu64)) == 0x4cc78bf4ea999e25u64) by (bit_vector);
    assert(k_sq_iter(0xb6d535c542116f62u64, 6) == 0x4cc78bf4ea999e25u64);
    lemma_k_square(0x4cc78bf4ea999e25u64);
    assert(reduce_formula(spread(0x4cc78bf4ea999e25u64)) == 0xe333308087e402bau64) by (bit_vector);
    assert(k_sq_iter(0xb6d535c542116f62u64, 7) == 0xe333308087e402bau64);
    lemma_k_square(0xe333308087e402bau64);
    assert(reduce_formula(spread(0xe333308087e402bau64)) == 0x5c62236777028505u64) by (bit_vector);
    assert(k_sq_iter(0xb6d535c542116f62u64, 8) == 0x5c62236777028505u64);
}

/// Squarings 32 to 40 of `x`.
proof fn lemma_k_frobenius_x_4()
    ensures
        k_sq_iter(0x5c62236777028505u64, 8) == 0x13846a66c22c75beu64,
{
    assert(k_sq_iter(0x5c62236777028505u64, 0) == 0x5c62236777028505u64);
    lemma_k_square(0x5c62236777028505u64);
    assert(reduce_formula(spread(0x5c62236777028505u64)) == 0xb964dc682c67ddcdu64) by (bit_vector);
    assert(k_sq_iter(0x5c62236777028505u64, 1) == 0xb964dc682c67ddcdu64);
    lemma_k_square(0xb964dc682c67ddcdu64);
    assert(reduce_formula(spread(0xb964dc682c67ddcdu64)) == 0xb58ac9a23d208acbu64) by (bit_vector);
    assert(k_sq_iter(0x5c62236777028505u64, 2) == 0xb58ac9a23d208acbu64);
    lemma_k_square(0xb58ac9a23d208acbu64);
    assert(reduce_formula(spread(0xb58ac9a23d208acbu64)) == 0xb3fcc2ab3699fc73u64) by (bit_vector);
    assert(k_sq_iter(0x5c62236777028505u64, 3) == 0xb3fcc2ab3699fc73u64);
    lemma_k_square(0xb3fcc2ab3699fc73u64);
    assert(reduce_formula(spread(0xb3fcc2ab3699fc73u64)) == 0xb2644136253abfe8u64) by (bit_vector);
    assert(k_sq_iter(0x5c62236777028505u64, 4) == 0xb2644136253abfe8u64);
    lemma_k_square(0xb2644136253abfe8u64);
    assert(reduce_formula(spread(0xb2644136253abfe8u64)) == 0xb37cd8f5f54e22c6u64) by (bit_vector);
    assert(k_sq_iter(0x5c62236777028505u64, 5) == 0xb37cd8f5f54e22c6u64);
    lemma_k_square(0xb37cd8f5f54e22c6u64);
    assert(reduce_formula(spread(0xb37cd8f5f54e22c6u64)) == 0xe267d02369c356e5u64) by (bit_vector);
    assert(k_sq_iter(0x5c62236777028505u64, 6) == 0xe267d02369c356e5u64);
    lemma_k_square(0xe267d02369c356e5u64);
    assert(reduce_formula(spread(0xe267d02369c356e5u64)) == 0x82c8dc57a143827u64) by (bit_vector);
    assert(k_sq_iter(0x5c62236777028505u64, 7) == 0x82c8dc57a143827u64);
    lemma_k_square(0x82c8dc57a143827u64);
    assert(reduce_formula(spread(0x82c8dc57a143827u64)) == 0x13846a66c22c75beu64) by (bit_vector);
    assert(k_sq_iter(0x5c62236777028505u64, 8) == 0x13846a66c22c75beu64);
}

/// Squarings 40 to 48 of `x`.
proof fn lemma_k_frobenius_x_5()
    ensures
        k_sq_iter(0x13846a66c22c75beu64, 8) == 0xfa5ac498d20dd97eu64,
{
    assert(k_sq_iter(0x13846a66c22c75beu64, 0) == 0x13846a66c22c75beu64);
    lemma_k_square(0x13846a66c22c75beu64);
    assert(reduce_formula(spread(0x13846a66c22c75beu64)) == 0x4b75c5e1cfbc9888u64) by (bit_vector);
    assert(k_sq_iter(0x13846a66c22c75beu64, 1) == 0x4b75c5e1cfbc9888u64);
    lemma_k_square(0x4b75c5e1cfbc9888u64);
    assert(reduce_formula(spread(0x4b75c5e1cfbc9888u64)) == 0xe6e383fc30ec5c40u64) by (bit_vector);
    assert(k_sq_iter(0x13846a66c22c75beu64, 2) == 0xe6e383fc30ec5c40u64);
    lemma_k_square(0xe6e383fc30ec5c40u64);
    assert(reduce_formula(spread(0xe6e383fc30ec5c40u64)) == 0x18db4821d1201031u64) by (bit_vector);
    assert(k_sq_iter(0x13846a66c22c75beu64, 3) == 0x18db4821d1201031u64);
    lemma_k_square(0x18db4821d1201031u64);
    assert(reduce_formula(spread(0x18db4821d1201031u64)) == 0x4cc669b6b7c0691au64) by (bit_vector);
    assert(k_sq_iter(0x13846a66c22c75beu64, 4) == 0x4cc669b6b7c0691au64);
    lemma_k_square(0x4cc669b6b7c0691au64);
    assert(reduce_formula(spread(0x4cc669b6b7c0691au64)) == 0xf26221ddce9cb783u64) by (bit_vector);
    assert(k_sq_iter(0x13846a66c22c75beu64, 5) == 0xf26221ddce9cb783u64);
    lemma_k_square(0xf26221ddce9cb783u64);
    assert(reduce_formula(spread(0xf26221ddce9cb783u64)) == 0x57399d3c29092c2fu64) by (bit_vector);
    assert(k_sq_iter(0x13846a66c22c75beu64, 6) == 0x57399d3c29092c2fu64);
    lemma_k_square(0x57399d3c29092c2fu64);
    assert(reduce_formula(spread(0x57399d3c29092c2fu64)) == 0xae86719cd83b743eu64) by (bit_vector);
    assert(k_sq_iter(0x13846a66c22c75beu64, 7) == 0xae86719cd83b743eu64);
    lemma_k_square(0xae86719cd83b743eu64);
    assert(reduce_formula(spread(0xae86719cd83b743eu64)) == 0xfa5ac498d20dd97eu64) by (bit_vector);
    assert(k_sq_iter(0x13846a66c22c75beu64, 8) == 0xfa5ac498d20dd97eu64);
}

/// Squarings 48 to 56 of `x`.
proof fn lemma_k_frobenius_x_6()
    ensures
        k_sq_iter(0xfa5ac498d20dd97eu64, 8) == 0x10a51a6f8e1e1acu64,
{
    assert(k_sq_iter(0xfa5ac498d20dd97eu64, 0) == 0xfa5ac498d20dd97eu64);
    lemma_k_square(0xfa5ac498d20dd97eu64);
    assert(reduce_formula(spread(0xfa5ac498d20dd97eu64)) == 0x50a9adfa20f7c8d5u64) by (bit_vector);
    assert(k_sq_iter(0xfa5ac498d20dd97eu64, 1) == 0x50a9adfa20f7c8d5u64);
    lemma_k_square(0x50a9adfa20f7c8d5u64);
    assert(reduce_formula(spread(0x50a9adfa20f7c8d5u64)) == 0xaf06ffc8fb2c50a6u64) by (bit_vector);
    assert(k_sq_iter(0xfa5ac498d20dd97eu64, 2) == 0xaf06ffc8fb2c50a6u64);
    lemma_k_square(0xaf06ffc8fb2c50a6u64);
    assert(reduce_formula(spread(0xaf06ffc8fb2c50a6u64)) == 0xfe42058b1100328eu64) by (bit_vector);
    assert(k_sq_iter(0xfa5ac498d20dd97eu64, 3) == 0xfe42058b1100328eu64);
    lemma_k_square(0xfe42058b1100328eu64);
    assert(reduce_formula(spread(0xfe42058b1100328eu64)) == 0x11cb06c04a986a2u64) by (bit_vector);
    assert(k_sq_iter(0xfa5ac498d20dd97eu64, 4) == 0x11cb06c04a986a2u64);
    lemma_k_square(0x11cb06c04a986a2u64);
    assert(reduce_formula(spread(0x11cb06c04a986a2u64)) == 0xb5837f7159f74u64) by (bit_vector);
    assert(k_sq_iter(0xfa5ac498d20dd97eu64, 5) == 0xb5837f7159f74u64);
    lemma_k_square(0xb5837f7159f74u64);
    assert(reduce_formula(spread(0xb5837f7159f74u64)) == 0x551507a7ec9563d7u64) by (bit_vector);
    assert(k_sq_iter(0xfa5ac498d20dd97eu64, 6) == 0x551507a7ec9563d7u64);
    lemma_k_square(0x551507a7ec9563d7u64);
    assert(reduce_formula(spread(0x551507a7ec9563d7u64)) == 0xfefb5bba15c4fcc9u64) by (bit_vector);
    assert(k_sq_iter(0xfa5ac498d20dd97eu64, 7) == 0xfefb5bba15c4fcc9u64);
    lemma_k_square(0xfefb5bba15c4fcc9u64);
    assert(reduce_formula(spread(0xfefb5bba15c4fcc9u64)) == 0x10a51a6f8e1e1acu64) by (bit_vector);
    assert(k_sq_iter(0xfa5ac498d20dd97eu64, 8) == 0x10a51a6f8e1e1acu64);
}

/// Squarings 56 to 64 of `x`.
proof fn lemma_k_frobenius_x_7()
    ensures
        k_sq_iter(0x10a51a6f8e1e1acu64, 8) == 0x2u64,
{
    assert(k_sq_iter(0x10a51a6f8e1e1acu64, 0) == 0x10a51a6f8e1e1acu64);
    lemma_k_square(0x10a51a6f8e1e1acu64);
    assert(reduce_formula(spread(0x10a51a6f8e1e1acu64)) == 0x555b52acff1ce98cu64) by (bit_vector);
    assert(k_sq_iter(0x10a51a6f8e1e1acu64, 1) == 0x555b52acff1ce98cu64);
    lemma_k_square(0x555b52acff1ce98cu64);
    assert(reduce_formula(spread(0x555b52acff1ce98cu64)) == 0xfffface6ff2beb3bu64) by (bit_vector);
    assert(k_sq_iter(0x10a51a6f8e1e1acu64, 2) == 0xfffface6ff2beb3bu64);
    lemma_k_square(0xfffface6ff2beb3bu64);
    assert(reduce_formula(spread(0xfffface6ff2beb3bu64)) == 0x55550444ff3218d8u64) by (bit_vector);
    assert(k_sq_iter(0x10a51a6f8e1e1acu64, 3) == 0x55550444ff3218d8u64);
    lemma_k_square(0x55550444ff3218d8u64);
    assert(reduce_formula(spread(0x55550444ff3218d8u64)) == 0xffffafaf00f1e0ebu64) by (bit_vector);
    assert(k_sq_iter(0x10a51a6f8e1e1acu64, 4) == 0xffffafaf00f1e0ebu64);
    lemma_k_square(0xffffafaf00f1e0ebu64);
    assert(reduce_formula(spread(0xffffafaf00f1e0ebu64)) == 0x5500ff01ff03u64) by (bit_vector);
    assert(k_sq_iter(0x10a51a6f8e1e1acu64, 5) == 0x5500ff01ff03u64);
    lemma_k_square(0x5500ff01ff03u64);
    assert(reduce_formula(spread(0x5500ff01ff03u64)) == 0x55550000fffe0005u64) by (bit_vector);
    assert(k_sq_iter(0x10a51a6f8e1e1acu64, 6) == 0x55550000fffe0005u64);
    lemma_k_square(0x55550000fffe0005u64);
    assert(reduce_formula(spread(0x55550000fffe0005u64)) == 0xffffffff0000000au64) by (bit_vector);
    assert(k_sq_iter(0x10a51a6f8e1e1acu64, 7) == 0xffffffff0000000au64);
    lemma_k_square(0xffffffff0000000au64);
    assert(reduce_formula(spread(0xffffffff0000000au64)) == 0x2u64) by (bit_vector);
    assert(k_sq_iter(0x10a51a6f8e1e1acu64, 8) == 0x2u64);
}

/// `x^(2^64) = x`, by 64 concrete squarings.
pub proof fn lemma_k_frobenius_x()
    ensures
        k_sq_iter(2, 64) == 2,
{
    lemma_k_frobenius_x_0();
    lemma_k_frobenius_x_1();
    lemma_k_frobenius_x_2();
    lemma_k_frobenius_x_3();
    lemma_k_frobenius_x_4();
    lemma_k_frobenius_x_5();
    lemma_k_frobenius_x_6();
    lemma_k_frobenius_x_7();
    lemma_k_sq_iter_add(2, 8, 8);
    assert(k_sq_iter(2, 16) == 0x15f0144001a114fu64);
    lemma_k_sq_iter_add(2, 16, 8);
    assert(k_sq_iter(2, 24) == 0xb6d535c542116f62u64);
    lemma_k_sq_iter_add(2, 24, 8);
    assert(k_sq_iter(2, 32) == 0x5c62236777028505u64);
    lemma_k_sq_iter_add(2, 32, 8);
    assert(k_sq_iter(2, 40) == 0x13846a66c22c75beu64);
    lemma_k_sq_iter_add(2, 40, 8);
    assert(k_sq_iter(2, 48) == 0xfa5ac498d20dd97eu64);
    lemma_k_sq_iter_add(2, 48, 8);
    assert(k_sq_iter(2, 56) == 0x10a51a6f8e1e1acu64);
    lemma_k_sq_iter_add(2, 56, 8);
    assert(k_sq_iter(2, 64) == 0x2u64);
}

/// Fermat in `K`: `a^(2^64) = a` for every `a`.
///
/// Squaring is GF(2)-linear and multiplicative, so it suffices that it fixes `x`, whose powers
/// `x^i = 1 << i` span `K`.
pub proof fn lemma_k_fermat(a: u64)
    ensures
        k_sq_iter(a, 64) == a,
{
    lemma_k_fermat_upto(a, 64);
}

pub proof fn lemma_k_fermat_upto(a: u64, n: nat)
    requires
        n <= 64,
    ensures
        k_sq_iter(low(a, n), 64) == low(a, n),
    decreases n,
{
    if n == 0 {
        assert(low(a, 0) == 0) by {
            assert(a & ((1u64 << 0u64) - 1) as u64 == 0) by (bit_vector);
        }
        lemma_k_sq_iter_zero(64);
    } else {
        let i = (n - 1) as nat;
        lemma_k_fermat_upto(a, i);
        lemma_low_step(a, i);
        let e: u64 = if bit(a, i) {
            1u64 << (i as u64)
        } else {
            0
        };
        lemma_k_sq_iter_xor(low(a, i), e, 64);
        if bit(a, i) {
            lemma_k_pow_x(i);
            lemma_k_sq_iter_k_pow(2, i, 64);
            lemma_k_frobenius_x();
        } else {
            lemma_k_sq_iter_zero(64);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// K is a field: the inverse is an inverse
// ---------------------------------------------------------------------------------------------
/// The only idempotents of `K` are 0 and 1 (Berlekamp: the Frobenius fixes only `GF(2)`, so `M` has a
/// single irreducible factor; with Fermat, `K` is a field).
pub proof fn lemma_k_idempotent(e: u64)
    requires
        k_mul(e, e) == e,
    ensures
        e == 0 || e == 1,
{
    lemma_k_square(e);
    assert(reduce_formula(spread(e)) == e ==> e == 0 || e == 1) by (bit_vector);
}

pub proof fn lemma_k_pow_zero(n: nat)
    requires
        n > 0,
    ensures
        k_pow(0, n) == 0,
{
    lemma_k_mul_zero(k_pow(0, (n - 1) as nat));
}

/// `a^(2^64 - 2)` is the inverse of every nonzero `a`, and zero's image is zero.
pub proof fn lemma_k_inverse(a: u64)
    ensures
        a != 0 ==> k_mul(a, k_pow(a, (pow2(64) - 2) as nat)) == 1,
        a == 0 ==> k_pow(a, (pow2(64) - 2) as nat) == 0,
{
    lemma2_to64();
    let q = pow2(64);
    let w = k_pow(a, (q - 2) as nat);
    let u = k_pow(a, (q - 1) as nat);
    if a == 0 {
        lemma_k_pow_zero((q - 2) as nat);
    } else {
        // u = a^(q-1) = a * w.
        assert(u == k_mul(w, a));
        lemma_k_mul_comm(w, a);
        // a^q = a by Fermat.
        lemma_k_sq_iter_pow(a, 1, 64);
        assert(k_pow(a, 1) == a) by {
            assert(k_pow(a, 0) == 1);
            lemma_k_mul_one(a);
        }
        lemma_k_fermat(a);
        assert(k_pow(a, q) == a);
        // u^2 = a^(2q - 2) = a^q a^(q-2) = u, so u is 0 or 1.
        lemma_k_pow_add(a, (q - 1) as nat, (q - 1) as nat);
        lemma_k_pow_add(a, q, (q - 2) as nat);
        assert((q - 1) as nat + (q - 1) as nat == q + (q - 2) as nat);
        lemma_k_idempotent(u);
        // u = 0 would give a = a^q = u a = 0.
        lemma_k_pow_add(a, (q - 1) as nat, 1);
        assert((q - 1) as nat + 1 == q);
        if u == 0 {
            lemma_k_mul_zero(a);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Executable code: the portable paths of `crates/primitives/src/field/gf2_64.rs`
// ---------------------------------------------------------------------------------------------
/// Reduction constant of the base field: `x^64 = x^4 + x^3 + x + 1 = 0x1B`.
pub const R64: u64 = 0x1B;

/// A GF(2^64) element; bit i = coefficient of x^i.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct F64(pub u64);

impl F64 {
    /// Degree over GF(2), the number of binary coefficients in one element.
    pub const DEGREE: usize = 64;

    pub const ZERO: Self = Self(0);

    pub const ONE: Self = Self(1);

    /// `x`, with `ord(x) = 2^64 - 1`.
    pub const G: Self = Self(2);

    #[inline]
    pub const fn is_zero(self) -> (r: bool)
        ensures
            r == (self.0 == 0),
    {
        self.0 == 0
    }

    /// Squaring, as a bit spread followed by one reduction.
    ///
    /// Cross terms vanish in characteristic 2, so the square moves bit `i` to bit `2i`.
    /// On aarch64 it is the product with itself instead: its PMULL folds stay in the vector register,
    /// where [`reduce`] would cross to integer registers and back.
    #[inline]
    pub fn square(self) -> (r: Self)
        ensures
            r.0 == k_mul(self.0, self.0),
    {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            self * self
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            Self(reduce(square_wide(self.0)))
        }
    }

    /// Multiplicative inverse `x^(2^64 - 2)`, mapping zero to zero.
    ///
    /// Itoh-Tsujii: with `t_k = x^(2^k - 1)`, the inverse is `t_63^2`.
    pub fn inv(self) -> (r: Self)
        ensures
            r.0 == k_pow(self.0, (pow2(64) - 2) as nat),
            self.0 != 0 ==> k_mul(self.0, r.0) == 1,
            self.0 == 0 ==> r.0 == 0,
    {
        proof {
            lemma_k_inverse(self.0);
        }
        // Square `v` a total of `n` times.
        let sq = |v: Self, n: u32| -> (r: Self)
            ensures
                r.0 == k_sq_iter(v.0, n as nat),
            {
                let ghost v0 = v;
                let mut v = v;
                for i in 0..n
                    invariant
                        v.0 == k_sq_iter(v0.0, i as nat),
                {
                    v = v.square();
                }
                v
            };
        let ghost a = self.0;
        proof {
            lemma2_to64();
            lemma2_to64_rest();
            assert(k_pow(a, 1) == a) by {
                assert(k_pow(a, 0) == 1);
                lemma_k_mul_one(a);
                lemma_k_mul_comm(1, a);
            }
        }
        // Each step reads t_k = x^(2^k - 1).
        let t1 = self;
        let t2 = sq(t1, 1) * t1;
        proof { step(a, 1, 1, 1) }
        let t3 = sq(t2, 1) * t1;
        proof { step(a, 2, 1, 1) }
        let t6 = sq(t3, 3) * t3;
        proof { step(a, 3, 3, 3) }
        let t12 = sq(t6, 6) * t6;
        proof { step(a, 6, 6, 6) }
        let t24 = sq(t12, 12) * t12;
        proof { step(a, 12, 12, 12) }
        let t48 = sq(t24, 24) * t24;
        proof { step(a, 24, 24, 24) }
        let t60 = sq(t48, 12) * t12;
        proof { step(a, 48, 12, 12) }
        let t63 = sq(t60, 3) * t3;
        proof { step(a, 60, 3, 3) }
        // (x^(2^63 - 1))^2 = x^(2^64 - 2).
        proof {
            lemma_k_sq_iter_pow(a, (pow2(63) - 1) as nat, 1);
        }
        sq(t63, 1)
    }
}

/// One Itoh-Tsujii step: `t_k^(2^n) * t_n = t_(k + n)` with `t_k = a^(2^k - 1)`.
proof fn step(a: u64, k: nat, n: nat, n2: nat)
    requires
        n == n2,
        k + n <= 64,
    ensures
        k_mul(k_sq_iter(k_pow(a, (pow2(k) - 1) as nat), n), k_pow(a, (pow2(n2) - 1) as nat)) == k_pow(
            a,
            (pow2(k + n) - 1) as nat,
        ),
{
    lemma_k_sq_iter_pow(a, (pow2(k) - 1) as nat, n);
    lemma_pow2_pos(k);
    lemma_pow2_pos(n);
    lemma_pow2_adds(k, n);
    let e1 = ((pow2(k) - 1) as nat) * pow2(n);
    let e2 = (pow2(n) - 1) as nat;
    lemma_k_pow_add(a, e1, e2);
    assert(e1 + e2 == (pow2(k + n) - 1) as nat) by (nonlinear_arith)
        requires
            e1 == ((pow2(k) - 1) as nat) * pow2(n),
            e2 == (pow2(n) - 1) as nat,
            pow2(k) * pow2(n) == pow2(k + n),
            pow2(k) > 0,
            pow2(n) > 0,
    ;
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl for F64 {
    open spec fn obeys_add_spec() -> bool {
        true
    }

    open spec fn add_req(self, rhs: F64) -> bool {
        true
    }

    open spec fn add_spec(self, rhs: F64) -> F64 {
        F64(self.0 ^ rhs.0)
    }
}

impl Add for F64 {
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
impl vstd::std_specs::ops::MulSpecImpl for F64 {
    open spec fn obeys_mul_spec() -> bool {
        true
    }

    open spec fn mul_req(self, rhs: F64) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: F64) -> F64 {
        F64(k_mul(self.0, rhs.0))
    }
}

impl Mul for F64 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> (r: Self)
        ensures
            r.0 == k_mul(self.0, rhs.0),
    {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_shift_tail(self, rhs) }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq is enabled at compile time.
            unsafe { Self(x86_64::mul(self.0, rhs.0)) }
        }
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "pclmulqdq")
        )))]
        {
            Self(reduce(mul_wide(self.0, rhs.0)))
        }
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddAssignSpecImpl for F64 {
    open spec fn obeys_add_assign_spec() -> bool {
        true
    }

    open spec fn add_assign_req(&self, rhs: F64) -> bool {
        true
    }

    open spec fn add_assign_spec(&self, rhs: F64) -> &F64 {
        &F64(self.0 ^ rhs.0)
    }
}

impl AddAssign for F64 {
    #[inline]
    fn add_assign(&mut self, rhs: Self)
        ensures
            final(self).0 == old(self).0 ^ rhs.0,
    {
        self.0 ^= rhs.0;
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulAssignSpecImpl for F64 {
    open spec fn obeys_mul_assign_spec() -> bool {
        true
    }

    open spec fn mul_assign_req(&self, rhs: F64) -> bool {
        true
    }

    open spec fn mul_assign_spec(&self, rhs: F64) -> &F64 {
        &F64(k_mul(self.0, rhs.0))
    }
}

impl MulAssign for F64 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self)
        ensures
            final(self).0 == k_mul(old(self).0, rhs.0),
    {
        *self = *self * rhs;
    }
}

/// The carry-less product of two 64-bit polynomials, as a 128-bit polynomial.
#[inline]
pub fn mul_wide(a: u64, b: u64) -> (r: u128)
    ensures
        r == clmul(a, b as u128),
{
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        proof {
            broadcast use crate::intrinsics::aarch64::axiom_u64x2_as_u128;
            let p = clmul(a, b as u128);
            assert(((p as u64) as u128) | ((((p >> 64u128) as u64) as u128) << 64u128) == p) by (bit_vector);
        }
        // SAFETY: aes is enabled at compile time; the reinterpret is between 128-bit values.
        unsafe { core::mem::transmute::<core::arch::aarch64::uint64x2_t, u128>(aarch64::pmull(a, b)) }
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    {
        // SAFETY: pclmulqdq is enabled at compile time.
        unsafe { x86_64::clmul(a, b) }
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq")
    )))]
    {
        software::clmul(a, b)
    }
}

/// The carry-less square of a 64-bit polynomial: bit `i` moves to bit `2i`.
#[inline]
pub fn square_wide(a: u64) -> (r: u128)
    ensures
        r == clmul(a, a as u128),
{
    #[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
    {
        // SAFETY: bmi2 is enabled at compile time.
        unsafe { x86_64::spread(a) }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "bmi2")))]
    {
        mul_wide(a, a)
    }
}

/// Reduce a 128-bit carry-less product modulo `x^64 + x^4 + x^3 + x + 1`.
#[inline]
pub const fn reduce(p: u128) -> (r: u64)
    ensures
        r == k_mod(p),
        is_remainder(p, r),
{
    proof {
        lemma_k_mod(p);
    }
    // Split the product into its low and high words.
    let (lo, hi) = (p as u64, (p >> 64) as u64);
    // The bits of `hi * 0x1B` shifted past x^63, which wrap around as `spill * 0x1B`.
    let spill = (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
    // Fold `hi` and `spill` together: both are multiplied by the same constant.
    let v = hi ^ spill;
    lo ^ v ^ (v << 1) ^ (v << 3) ^ (v << 4)
}

pub mod software {
    use super::*;

    /// Portable 64x64 carry-less product, used by fallback paths and as the reference.
    pub const fn clmul(a: u64, b: u64) -> (r: u128)
        ensures
            r == crate::clmul::clmul(a, b as u128),
    {
        let mut acc = 0u128;
        let mut i = 0;
        // Schoolbook: XOR in `b * x^i` for every set bit `i` of `a`.
        while i < 64
            invariant
                0 <= i <= 64,
                acc == clmul_upto(a, b as u128, i as nat),
            decreases 64 - i,
        {
            proof {
                let s = i as u64;
                let bb = b as u128;
                assert(((a >> s) & 1 != 0) == ((a >> s) & 1 == 1)) by (bit_vector);
                assert(acc ^ 0 == acc) by (bit_vector);
            }
            if (a >> i) & 1 != 0 {
                acc ^= (b as u128) << i;
            }
            i += 1;
        }
        acc
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod aarch64 {
    use super::{F64, R64};
    use crate::neon::xor3_u64;
    use core::arch::aarch64::*;
    use core::mem::transmute;
    #[cfg(verus_keep_ghost)]
    use super::{k_mul, k_mod, lemma_clmul_fold_reduction};
    #[cfg(verus_keep_ghost)]
    use crate::intrinsics::aarch64::*;
    #[cfg(verus_keep_ghost)]
    use crate::intrinsics::transmuted;
    use vstd::prelude::*;

    /// 64x64 carry-less product as a 128-bit NEON vector.
    ///
    /// # Safety
    /// Requires the `aes` target feature (compiles to PMULL); only call where
    /// `aes` is statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn pmull(a: u64, b: u64) -> (r: uint64x2_t)
        ensures
            u64x2(r)[0] == crate::clmul::clmul(a, b as u128) as u64,
            u64x2(r)[1] == (crate::clmul::clmul(a, b as u128) >> 64u128) as u64,
    {
        proof {
            broadcast use axiom_u128_as_u64x2;
        }
        // SAFETY: u128 and uint64x2_t are both 128-bit values.
        unsafe { transmute::<u128, uint64x2_t>(vmull_p64(a, b)) }
    }

    /// Carry-less product of the two *high* lanes: PMULL2 on the register
    /// pair, no lane extraction (the lane-crossing-free way to fold a
    /// product's high half).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn pmull_hi(a: uint64x2_t, b: uint64x2_t) -> (r: uint64x2_t)
        ensures
            u64x2(r)[0] == crate::clmul::clmul(u64x2(a)[1], u64x2(b)[1] as u128) as u64,
            u64x2(r)[1] == (crate::clmul::clmul(u64x2(a)[1], u64x2(b)[1] as u128) >> 64u128) as u64,
    {
        proof {
            broadcast use axiom_u128_as_u64x2, axiom_u64x2_as_p64x2;
        }
        // SAFETY: bit-level reinterprets between 128-bit vector types.
        unsafe {
            transmute::<u128, uint64x2_t>(vmull_high_p64(
                transmute::<uint64x2_t, poly64x2_t>(a),
                transmute::<uint64x2_t, poly64x2_t>(b),
            ))
        }
    }

    /// The two lanes of a register as one 128-bit polynomial, lane 0 the low word.
    pub open spec fn u64x2_u128(v: uint64x2_t) -> u128 {
        (u64x2(v)[0] as u128) | ((u64x2(v)[1] as u128) << 64u128)
    }

    proof fn lemma_u64x2_u128(v: uint64x2_t)
        ensures
            u64x2(v)[0] == u64x2_u128(v) as u64,
            u64x2(v)[1] == (u64x2_u128(v) >> 64u128) as u64,
    {
        let (a, b) = (u64x2(v)[0], u64x2(v)[1]);
        assert(a == (((a as u128) | ((b as u128) << 64u128)) as u64) && b == ((((a as u128) | ((b as u128) << 64u128))
            >> 64u128) as u64)) by (bit_vector);
    }

    /// The reduction of one product in a register: `p ^ t ^ u` with `t = hi(p) * 0x1B`, `u = hi(t) * 0x1B`,
    /// whose low lane is `k_mod` of the product, given `p`'s lanes are the product's words.
    proof fn lemma_fold_lanes(p: uint64x2_t, r: uint64x2_t, t: uint64x2_t, u: uint64x2_t, pp: u128)
        requires
            u64x2(p)[0] == pp as u64,
            u64x2(p)[1] == (pp >> 64u128) as u64,
            u64x2(r)[1] == R64,
            u64x2(t)[0] == crate::clmul::clmul(u64x2(p)[1], u64x2(r)[1] as u128) as u64,
            u64x2(t)[1] == (crate::clmul::clmul(u64x2(p)[1], u64x2(r)[1] as u128) >> 64u128) as u64,
            u64x2(u)[0] == crate::clmul::clmul(u64x2(t)[1], u64x2(r)[1] as u128) as u64,
        ensures
            u64x2(p)[0] ^ u64x2(t)[0] ^ u64x2(u)[0] == k_mod(pp),
    {
        lemma_clmul_fold_reduction(pp);
        let tt = crate::clmul::clmul((pp >> 64u128) as u64, 0x1Bu128);
        let uu = crate::clmul::clmul((tt >> 64u128) as u64, 0x1Bu128);
        assert((pp ^ tt ^ uu) as u64 == (pp as u64) ^ (tt as u64) ^ (uu as u64)) by (bit_vector);
    }

    /// Reduce two 128-bit carry-less products into one lane pair: `[reduce(p0), reduce(p1)]`.
    ///
    /// Seven instructions for the pair.
    ///
    /// Rewritten for Verus: the empty `asm!` block that hides the lanes from LLVM is in [`hide_lanes`], whose
    /// body is that block and whose specification is that it leaves both registers unchanged.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn reduce_pair_pmull4(p0: uint64x2_t, p1: uint64x2_t) -> (r: uint64x2_t)
        ensures
            u64x2(r)[0] == k_mod(u64x2_u128(p0)),
            u64x2(r)[1] == k_mod(u64x2_u128(p1)),
    {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let (t0, t1) = (pmull_hi(p0, r), pmull_hi(p1, r));
            let (u0, u1) = (pmull_hi(t0, r), pmull_hi(t1, r));
            let (e0, e1) = (xor3_u64(p0, t0, u0), xor3_u64(p1, t1, u1));
            // Why: only lane 0 of each sum survives the zip.
            // LLVM would gather the six low lanes with three inserts and XOR once: one instruction more.
            // An empty asm block hides the lanes from it, and emits nothing.
            let (e0, e1) = hide_lanes(e0, e1);
            proof {
                lemma_u64x2_u128(p0);
                lemma_u64x2_u128(p1);
                lemma_fold_lanes(p0, r, t0, u0, u64x2_u128(p0));
                lemma_fold_lanes(p1, r, t1, u1, u64x2_u128(p1));
            }
            vzip1q_u64(e0, e1)
        }
    }

    /// The empty `asm!` block of [`reduce_pair_pmull4`]: it emits nothing, so both registers keep their value.
    #[verifier::external_body]
    #[inline(always)]
    fn hide_lanes(mut e0: uint64x2_t, mut e1: uint64x2_t) -> (r: (uint64x2_t, uint64x2_t))
        ensures
            r == (e0, e1),
    {
        // SAFETY: an empty block, which reads and writes nothing.
        unsafe {
            core::arch::asm!(
                "/* {0:v} {1:v} */",
                inout(vreg) e0,
                inout(vreg) e1,
                options(pure, nomem, nostack, preserves_flags)
            );
        }
        (e0, e1)
    }

    /// The default `Mul` kernel on aarch64. 3-PMULL multiply: product, then two
    /// PMULL-by-0x1B folds, the second taking the first's <=4-bit overflow
    /// exactly (`ov*0x1B` fits in 8 bits).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_shift_tail(a: F64, b: F64) -> (r: F64)
        ensures
            r.0 == k_mul(a.0, b.0),
    {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let p = pmull(a.0, b.0);
            let t = pmull_hi(p, r);
            let u = pmull_hi(t, r);
            proof {
                lemma_fold_lanes(p, r, t, u, crate::clmul::clmul(a.0, b.0 as u128));
            }
            F64(vgetq_lane_u64::<0>(veorq_u64(veorq_u64(p, t), u)))
        }
    }
}

/// The x86-64 products.
#[cfg(target_arch = "x86_64")]
pub mod x86_64 {
    use super::R64;
    use core::arch::x86_64::*;
    #[cfg(verus_keep_ghost)]
    use super::{k_mul, lemma_clmul_fold_reduction, lemma_clmul_square_upto, lemma_k_mod};
    #[cfg(verus_keep_ghost)]
    use crate::clmul::low;
    use vstd::prelude::*;
    #[cfg(verus_keep_ghost)]
    use crate::intrinsics::x86::*;
    #[cfg(verus_keep_ghost)]
    use crate::intrinsics::transmuted;
    #[cfg(verus_keep_ghost)]
    use crate::clmul::lemma_u64_bits_eq;

    /// One field product: the carry-less product, then two carry-less folds of its high word by `0x1B`.
    ///
    /// # Safety
    ///
    /// Requires the `pclmulqdq` target feature.
    #[inline]
    #[target_feature(enable = "pclmulqdq")]
    pub unsafe fn mul(a: u64, b: u64) -> (r: u64)
        ensures
            r == k_mul(a, b),
    {
        proof {
            lemma_clmul_sel();
            lemma_i64_round_trip(a);
            lemma_i64_round_trip(b);
            lemma_i64_round_trip(R64);
        }
        let r = _mm_cvtsi64_si128(R64 as i64);
        let p = _mm_clmulepi64_si128::<0x00>(_mm_cvtsi64_si128(a as i64), _mm_cvtsi64_si128(b as i64));
        // hi * 0x1B, at most 68 bits.
        let t = _mm_clmulepi64_si128::<0x01>(p, r);
        // Its spill past x^63, times 0x1B: at most 8 bits.
        let u = _mm_clmulepi64_si128::<0x01>(t, r);
        proof {
            lemma_clmul_words_split(m128(p), a, b);
            lemma_clmul_words_split(m128(t), m128(p)[1], R64);
            lemma_clmul_words_split(m128(u), m128(t)[1], R64);
            let pp = crate::clmul::clmul(a, b as u128);
            lemma_clmul_fold_reduction(pp);
            let tt = crate::clmul::clmul((pp >> 64u128) as u64, 0x1Bu128);
            let uu = crate::clmul::clmul((tt >> 64u128) as u64, 0x1Bu128);
            assert((pp ^ tt ^ uu) as u64 == (pp as u64) ^ (tt as u64) ^ (uu as u64)) by (bit_vector);
        }
        _mm_cvtsi128_si64(_mm_xor_si128(_mm_xor_si128(p, t), u)) as u64
    }

    /// 64x64 carry-less product.
    ///
    /// # Safety
    ///
    /// Requires the `pclmulqdq` target feature.
    #[inline]
    #[target_feature(enable = "pclmulqdq")]
    pub unsafe fn clmul(a: u64, b: u64) -> (r: u128)
        ensures
            r == crate::clmul::clmul(a, b as u128),
    {
        proof {
            lemma_i64_round_trip(a);
            lemma_i64_round_trip(b);
        }
        // Move both operands into the low qword of a vector register.
        let (a, b) = (_mm_cvtsi64_si128(a as i64), _mm_cvtsi64_si128(b as i64));
        proof {
            let (x, y) = (m128(a)[0], m128(b)[0]);
            lemma_clmul_sel();
            let pp = crate::clmul::clmul(x, y as u128);
            assert(((pp as u64) as u128) | ((((pp >> 64u128) as u64) as u128) << 64u128) == pp) by (bit_vector);
            broadcast use axiom_m128_as_u128;
        }
        // SAFETY: both types are 128 bits wide with no invalid bit patterns.
        unsafe { core::mem::transmute::<__m128i, u128>(_mm_clmulepi64_si128::<0x00>(a, b)) }
    }

    /// Carry-less square by bit deposit: `pdep` spreads each 32-bit half onto the even bits of one word.
    ///
    /// # Safety
    ///
    /// Requires the `bmi2` target feature.
    #[inline]
    #[target_feature(enable = "bmi2")]
    pub unsafe fn spread(a: u64) -> (r: u128)
        ensures
            r == crate::clmul::clmul(a, a as u128),
    {
        // Bits 0, 2, 4, ...: where a square puts the input bits.
        const EVEN: u64 = 0x5555_5555_5555_5555;
        // Low half of `a` into the low word, high half into the high word.
        let lo = _pdep_u64(a, EVEN);
        let hi = _pdep_u64(a >> 32, EVEN);
        proof {
            lemma_pdep_even(a, lo);
            lemma_pdep_even(a >> 32, hi);
            lemma_spread_halves(a, lo, hi);
            assert(low(a, 64) == a);
            lemma_clmul_square_upto(a, 64);
        }
        lo as u128 | (hi as u128) << 64
    }

    // -----------------------------------------------------------------------------------------
    // Proof helpers
    // -----------------------------------------------------------------------------------------
    pub proof fn lemma_i64_round_trip(a: u64)
        ensures
            (a as i64) as u64 == a,
    {
        assert((a as i64) as u64 == a) by (bit_vector);
    }

    /// PCLMULQDQ's two result words are the low and high words of the carry-less product.
    pub proof fn lemma_clmul_words_split(w: [u64; 2], a: u64, b: u64)
        requires
            w[0] == clmul_words(a, b)[0],
            w[1] == clmul_words(a, b)[1],
        ensures
            w[0] == crate::clmul::clmul(a, b as u128) as u64,
            w[1] == (crate::clmul::clmul(a, b as u128) >> 64u128) as u64,
    {
    }

    /// The set bits of `0x5555...`: the even positions, and so `ones_below(EVEN, j) = ceil(j / 2)`.
    pub proof fn lemma_ones_below_even(j: nat)
        requires
            j <= 64,
        ensures
            ones_below(0x5555_5555_5555_5555u64, j) == (j + 1) / 2,
        decreases j,
    {
        if j > 0 {
            lemma_ones_below_even((j - 1) as nat);
            let s = (j - 1) as u64;
            assert(s < 64 ==> (((0x5555_5555_5555_5555u64 >> s) & 1 == 1) == (s % 2 == 0))) by (bit_vector);
        }
    }

    /// Bit `j` of `pdep(a, EVEN)` is bit `j / 2` of `a` for even `j`, zero for odd `j`.
    pub proof fn lemma_pdep_even(a: u64, d: u64)
        requires
            forall|j: nat| j < 64 ==> #[trigger] crate::clmul::bit(d, j) == pdep_bit(a, 0x5555_5555_5555_5555u64, j),
        ensures
            d == spread_word(a),
    {
        assert forall|j: nat| j < 64 implies #[trigger] crate::clmul::bit(d, j) == crate::clmul::bit(spread_word(a), j) by {
            lemma_ones_below_even(j);
            let s = j as u64;
            assert(s < 64 ==> (((0x5555_5555_5555_5555u64 >> s) & 1 == 1) == (s % 2 == 0))) by (bit_vector);
            assert(s < 64 ==> (((spread_word(a) >> s) & 1 == 1) == (s % 2 == 0 && (a >> ((s + 1) / 2)) & 1 == 1)))
                by (bit_vector);
            assert((s + 1) / 2 == ((j + 1) / 2) as u64);
        }
        lemma_u64_bits_eq(d, spread_word(a));
    }

    /// The low 32 bits of `a` spread onto the even bits of a word.
    pub open spec fn spread_word(a: u64) -> u64 {
        let x = a & 0xFFFF_FFFF;
        let x = (x | (x << 16u64)) & 0x0000_FFFF_0000_FFFFu64;
        let x = (x | (x << 8u64)) & 0x00FF_00FF_00FF_00FFu64;
        let x = (x | (x << 4u64)) & 0x0F0F_0F0F_0F0F_0F0Fu64;
        let x = (x | (x << 2u64)) & 0x3333_3333_3333_3333u64;
        (x | (x << 1u64)) & 0x5555_5555_5555_5555u64
    }

    /// The two spread halves make the spread of the whole word.
    pub proof fn lemma_spread_halves(a: u64, lo: u64, hi: u64)
        requires
            lo == spread_word(a),
            hi == spread_word(a >> 32u64),
        ensures
            lo as u128 | (hi as u128) << 64u128 == super::spread(a),
    {
        assert(spread_word(a) as u128 | (spread_word(a >> 32u64) as u128) << 64u128 == super::spread(a)) by (bit_vector);
    }
}

// ---------------------------------------------------------------------------------------------
// The scalar SIMD products: their reduction, given the semantics of the carry-less multiply
// ---------------------------------------------------------------------------------------------
/// The reduction of `x86_64::mul` (PCLMULQDQ) and `aarch64::mul_shift_tail` / `reduce_pair_pmull4` (PMULL):
///
/// ```text
///     t = hi(p) * 0x1B,  u = hi(t) * 0x1B,  result = lo(p ^ t ^ u)
/// ```
///
/// equals [`reduce`], so with the instruction computing [`clmul`] those kernels compute [`k_mul`].
pub proof fn lemma_clmul_fold_reduction(p: u128)
    ensures
        ({
            let t = clmul((p >> 64u128) as u64, 0x1Bu128);
            let u = clmul((t >> 64u128) as u64, 0x1Bu128);
            (p ^ t ^ u) as u64 == k_mod(p)
        }),
{
    let t = clmul((p >> 64u128) as u64, 0x1Bu128);
    lemma_clmul_r64((p >> 64u128) as u64);
    lemma_clmul_r64((t >> 64u128) as u64);
    lemma_k_mod(p);
    assert({
        let h = ((p >> 64u128) as u64) as u128;
        let t = h ^ (h << 1u128) ^ (h << 3u128) ^ (h << 4u128);
        let h2 = ((t >> 64u128) as u64) as u128;
        let u = h2 ^ (h2 << 1u128) ^ (h2 << 3u128) ^ (h2 << 4u128);
        (p ^ t ^ u) as u64 == reduce_formula(p)
    }) by (bit_vector);
}

} // verus!
