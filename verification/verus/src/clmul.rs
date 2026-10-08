//! Carry-less multiplication: the product of polynomials over GF(2).
//!
//! A polynomial over GF(2) of degree below `w` is a `w`-bit word, bit `i` its coefficient of `x^i`.
//! Addition is XOR, and the product is the schoolbook one: XOR in `b * x^i` for every set bit `i` of `a`.
//! That is the definition below ([`clmul`]), from which every lemma here is proven.
use vstd::prelude::*;

verus! {

/// Bit `i` of `a`: its coefficient of `x^i`.
pub open spec fn bit(a: u64, i: nat) -> bool {
    (a >> (i as u64)) & 1 == 1
}

/// The `i`-th partial product `[a_i] * b * x^i`.
pub open spec fn term(a: u64, b: u128, i: nat) -> u128 {
    if bit(a, i) {
        b << (i as u128)
    } else {
        0
    }
}

/// `sum_{i < n} [a_i] * b * x^i` over GF(2): XOR of shifted ANDs.
pub open spec fn clmul_upto(a: u64, b: u128, n: nat) -> u128
    decreases n,
{
    if n == 0 {
        0
    } else {
        clmul_upto(a, b, (n - 1) as nat) ^ term(a, b, (n - 1) as nat)
    }
}

/// The carry-less product `a * b` of a polynomial `a` of degree below 64 and a polynomial `b`, modulo `x^128`.
///
/// Every use below has `deg a + deg b < 128`, where the truncation is vacuous (see [`lemma_clmul_bound`]).
pub open spec fn clmul(a: u64, b: u128) -> u128 {
    clmul_upto(a, b, 64)
}

/// The low `n` coefficients of `a`.
pub open spec fn low(a: u64, n: nat) -> u64 {
    if n >= 64 {
        a
    } else {
        a & ((1u64 << (n as u64)) - 1) as u64
    }
}

/// The product is GF(2)-linear in its right factor.
pub proof fn lemma_clmul_upto_xor_right(a: u64, b1: u128, b2: u128, n: nat)
    ensures
        clmul_upto(a, b1 ^ b2, n) == clmul_upto(a, b1, n) ^ clmul_upto(a, b2, n),
    decreases n,
{
    if n > 0 {
        let i = (n - 1) as nat;
        lemma_clmul_upto_xor_right(a, b1, b2, i);
        let (x1, x2) = (clmul_upto(a, b1, i), clmul_upto(a, b2, i));
        let s = i as u128;
        if bit(a, i) {
            assert((x1 ^ x2) ^ ((b1 ^ b2) << s) == (x1 ^ (b1 << s)) ^ (x2 ^ (b2 << s))) by (bit_vector);
            assert(term(a, b1 ^ b2, i) == (b1 ^ b2) << s);
            assert(clmul_upto(a, b1 ^ b2, n) == clmul_upto(a, b1 ^ b2, i) ^ term(a, b1 ^ b2, i));
        } else {
            assert((x1 ^ x2) ^ 0 == (x1 ^ 0) ^ (x2 ^ 0)) by (bit_vector);
        }
    } else {
        assert(0u128 ^ 0u128 == 0u128) by (bit_vector);
    }
}

pub proof fn lemma_clmul_xor_right(a: u64, b1: u128, b2: u128)
    ensures
        clmul(a, b1 ^ b2) == clmul(a, b1) ^ clmul(a, b2),
{
    lemma_clmul_upto_xor_right(a, b1, b2, 64);
}

/// The product is GF(2)-linear in its left factor.
pub proof fn lemma_clmul_upto_xor_left(a1: u64, a2: u64, b: u128, n: nat)
    ensures
        clmul_upto(a1 ^ a2, b, n) == clmul_upto(a1, b, n) ^ clmul_upto(a2, b, n),
    decreases n,
{
    if n > 0 {
        let i = (n - 1) as nat;
        lemma_clmul_upto_xor_left(a1, a2, b, i);
        let (x1, x2) = (clmul_upto(a1, b, i), clmul_upto(a2, b, i));
        let (t1, t2, t) = (term(a1, b, i), term(a2, b, i), term(a1 ^ a2, b, i));
        let s = i as u64;
        assert(((a1 ^ a2) >> s) & 1 == 1 <==> (((a1 >> s) & 1 == 1) != ((a2 >> s) & 1 == 1))) by (bit_vector);
        assert(t == t1 ^ t2) by {
            let v = b << (i as u128);
            assert(v ^ 0 == v && 0 ^ v == v && v ^ v == 0 && 0u128 ^ 0u128 == 0) by (bit_vector);
        }
        assert((x1 ^ x2) ^ (t1 ^ t2) == (x1 ^ t1) ^ (x2 ^ t2)) by (bit_vector);
    } else {
        assert(0u128 ^ 0u128 == 0u128) by (bit_vector);
    }
}

pub proof fn lemma_clmul_xor_left(a1: u64, a2: u64, b: u128)
    ensures
        clmul(a1 ^ a2, b) == clmul(a1, b) ^ clmul(a2, b),
{
    lemma_clmul_upto_xor_left(a1, a2, b, 64);
}

/// Multiplying by `x` (a left shift) commutes with the product: `a * (b x) = (a * b) x`, modulo `x^128`.
pub proof fn lemma_clmul_upto_shl1(a: u64, b: u128, n: nat)
    requires
        n <= 64,
    ensures
        clmul_upto(a, b << 1u128, n) == clmul_upto(a, b, n) << 1u128,
    decreases n,
{
    if n > 0 {
        let i = (n - 1) as nat;
        lemma_clmul_upto_shl1(a, b, i);
        let x = clmul_upto(a, b, i);
        let s = i as u128;
        if bit(a, i) {
            assert(s < 64 ==> (x << 1u128) ^ ((b << 1u128) << s) == (x ^ (b << s)) << 1u128) by (bit_vector);
        } else {
            assert((x << 1u128) ^ 0 == (x ^ 0) << 1u128) by (bit_vector);
        }
    } else {
        assert(0u128 << 1u128 == 0u128) by (bit_vector);
    }
}

pub proof fn lemma_clmul_shl1(a: u64, b: u128)
    ensures
        clmul(a, b << 1u128) == clmul(a, b) << 1u128,
{
    lemma_clmul_upto_shl1(a, b, 64);
}

/// The product by a monomial is a shift: `a * x^j = a << j`, for `j <= 64`.
pub proof fn lemma_clmul_upto_monomial(a: u64, j: u128, n: nat)
    requires
        j <= 64,
        n <= 64,
    ensures
        clmul_upto(a, 1u128 << j, n) == (low(a, n) as u128) << j,
    decreases n,
{
    if n == 0 {
        assert((a & ((1u64 << 0u64) - 1) as u64) as u128 == 0) by (bit_vector);
        assert(0u128 << j == 0) by (bit_vector);
    } else {
        let i = (n - 1) as nat;
        lemma_clmul_upto_monomial(a, j, i);
        let s = i as u64;
        let lo = low(a, i);
        assert(lo == a & ((1u64 << s) - 1) as u64);
        if n < 64 {
            assert(low(a, n) == a & ((1u64 << (s + 1)) - 1) as u64);
            assert(s < 63 && j <= 64 ==> {
                let t = if (a >> s) & 1 == 1 { (1u128 << j) << (s as u128) } else { 0 };
                ((a & ((1u64 << s) - 1) as u64) as u128) << j ^ t == ((a & ((1u64 << (s + 1)) - 1) as u64) as u128) << j
            }) by (bit_vector);
        } else {
            assert(low(a, n) == a);
            assert(s == 63 && j <= 64 ==> {
                let t = if (a >> s) & 1 == 1 { (1u128 << j) << (s as u128) } else { 0 };
                ((a & ((1u64 << s) - 1) as u64) as u128) << j ^ t == (a as u128) << j
            }) by (bit_vector);
        }
    }
}

pub proof fn lemma_clmul_monomial(a: u64, j: u128)
    requires
        j <= 64,
    ensures
        clmul(a, 1u128 << j) == (a as u128) << j,
{
    lemma_clmul_upto_monomial(a, j, 64);
}

/// Splitting the left factor into its low `n` bits and its bit `n`.
pub proof fn lemma_low_step(a: u64, n: nat)
    requires
        n < 64,
    ensures
        low(a, n + 1) == low(a, n) ^ (if bit(a, n) { 1u64 << (n as u64) } else { 0 }),
{
    let s = n as u64;
    if n + 1 < 64 {
        assert(s < 63 ==> a & ((1u64 << (s + 1)) - 1) as u64 == (a & ((1u64 << s) - 1) as u64) ^ (if (a >> s)
            & 1 == 1 {
            1u64 << s
        } else {
            0
        })) by (bit_vector);
    } else {
        assert(s == 63 ==> a == (a & ((1u64 << s) - 1) as u64) ^ (if (a >> s) & 1 == 1 {
            1u64 << s
        } else {
            0
        })) by (bit_vector);
    }
}

/// The product is commutative: `a * b = b * a` for polynomials of degree below 64.
pub proof fn lemma_clmul_upto_comm(a: u64, b: u64, n: nat)
    requires
        n <= 64,
    ensures
        clmul(a, low(b, n) as u128) == clmul_upto(b, a as u128, n),
    decreases n,
{
    if n == 0 {
        assert(low(b, 0) == 0) by {
            assert(b & ((1u64 << 0u64) - 1) as u64 == 0) by (bit_vector);
        }
        lemma_clmul_upto_xor_right(a, 0, 0, 64);
        assert(0u128 ^ 0u128 == 0u128) by (bit_vector);
        let z = clmul(a, 0);
        assert(z ^ z == 0) by (bit_vector);
    } else {
        let i = (n - 1) as nat;
        lemma_clmul_upto_comm(a, b, i);
        lemma_low_step(b, i);
        let e: u64 = if bit(b, i) { 1u64 << (i as u64) } else { 0 };
        let lo = low(b, i);
        assert((lo ^ e) as u128 == (lo as u128) ^ (e as u128)) by (bit_vector);
        lemma_clmul_xor_right(a, lo as u128, e as u128);
        if bit(b, i) {
            assert(((1u64 << (i as u64)) as u128) == 1u128 << (i as u128)) by {
                let s = i as u64;
                assert(s < 64 ==> ((1u64 << s) as u128) == 1u128 << (s as u128)) by (bit_vector);
            }
            lemma_clmul_monomial(a, i as u128);
        } else {
            lemma_clmul_upto_xor_right(a, 0, 0, 64);
            let z = clmul(a, 0);
            assert(0u128 ^ 0u128 == 0u128) by (bit_vector);
            assert(z ^ z == 0) by (bit_vector);
        }
    }
}

pub proof fn lemma_clmul_comm(a: u64, b: u64)
    ensures
        clmul(a, b as u128) == clmul(b, a as u128),
{
    lemma_clmul_upto_comm(a, b, 64);
}

/// The product of two polynomials of degree below 64 has degree below 127.
pub proof fn lemma_clmul_upto_bound(a: u64, b: u128, n: nat)
    requires
        b >> 64u128 == 0,
        n <= 64,
    ensures
        clmul_upto(a, b, n) >> ((63 + n) as u128) == 0,
    decreases n,
{
    if n == 0 {
        assert(0u128 >> 63u128 == 0) by (bit_vector);
    } else {
        let i = (n - 1) as nat;
        lemma_clmul_upto_bound(a, b, i);
        let x = clmul_upto(a, b, i);
        let s = i as u128;
        assert(s < 64 && b >> 64u128 == 0 && x >> (63 + s) == 0 ==> (x ^ (b << s)) >> (64 + s) == 0 && (x ^ 0)
            >> (64 + s) == 0) by (bit_vector);
    }
}

pub proof fn lemma_clmul_bound(a: u64, b: u64)
    ensures
        clmul(a, b as u128) >> 127u128 == 0,
{
    assert((b as u128) >> 64u128 == 0) by (bit_vector);
    lemma_clmul_upto_bound(a, b as u128, 64);
}

/// The product by zero.
pub proof fn lemma_clmul_zero(a: u64)
    ensures
        clmul(a, 0) == 0,
{
    lemma_clmul_xor_right(a, 0, 0);
    let z = clmul(a, 0);
    assert(0u128 ^ 0u128 == 0u128) by (bit_vector);
    assert(z ^ z == 0) by (bit_vector);
}

} // verus!
