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

/// Two words with the same bits are equal.
pub proof fn lemma_u64_bits_eq(x: u64, y: u64)
    requires
        forall|j: nat| j < 64 ==> #[trigger] bit(x, j) == bit(y, j),
    ensures
        x == y,
{
    assert(bit(x, 0) == bit(y, 0));
    assert(bit(x, 1) == bit(y, 1));
    assert(bit(x, 2) == bit(y, 2));
    assert(bit(x, 3) == bit(y, 3));
    assert(bit(x, 4) == bit(y, 4));
    assert(bit(x, 5) == bit(y, 5));
    assert(bit(x, 6) == bit(y, 6));
    assert(bit(x, 7) == bit(y, 7));
    assert(bit(x, 8) == bit(y, 8));
    assert(bit(x, 9) == bit(y, 9));
    assert(bit(x, 10) == bit(y, 10));
    assert(bit(x, 11) == bit(y, 11));
    assert(bit(x, 12) == bit(y, 12));
    assert(bit(x, 13) == bit(y, 13));
    assert(bit(x, 14) == bit(y, 14));
    assert(bit(x, 15) == bit(y, 15));
    assert(bit(x, 16) == bit(y, 16));
    assert(bit(x, 17) == bit(y, 17));
    assert(bit(x, 18) == bit(y, 18));
    assert(bit(x, 19) == bit(y, 19));
    assert(bit(x, 20) == bit(y, 20));
    assert(bit(x, 21) == bit(y, 21));
    assert(bit(x, 22) == bit(y, 22));
    assert(bit(x, 23) == bit(y, 23));
    assert(bit(x, 24) == bit(y, 24));
    assert(bit(x, 25) == bit(y, 25));
    assert(bit(x, 26) == bit(y, 26));
    assert(bit(x, 27) == bit(y, 27));
    assert(bit(x, 28) == bit(y, 28));
    assert(bit(x, 29) == bit(y, 29));
    assert(bit(x, 30) == bit(y, 30));
    assert(bit(x, 31) == bit(y, 31));
    assert(bit(x, 32) == bit(y, 32));
    assert(bit(x, 33) == bit(y, 33));
    assert(bit(x, 34) == bit(y, 34));
    assert(bit(x, 35) == bit(y, 35));
    assert(bit(x, 36) == bit(y, 36));
    assert(bit(x, 37) == bit(y, 37));
    assert(bit(x, 38) == bit(y, 38));
    assert(bit(x, 39) == bit(y, 39));
    assert(bit(x, 40) == bit(y, 40));
    assert(bit(x, 41) == bit(y, 41));
    assert(bit(x, 42) == bit(y, 42));
    assert(bit(x, 43) == bit(y, 43));
    assert(bit(x, 44) == bit(y, 44));
    assert(bit(x, 45) == bit(y, 45));
    assert(bit(x, 46) == bit(y, 46));
    assert(bit(x, 47) == bit(y, 47));
    assert(bit(x, 48) == bit(y, 48));
    assert(bit(x, 49) == bit(y, 49));
    assert(bit(x, 50) == bit(y, 50));
    assert(bit(x, 51) == bit(y, 51));
    assert(bit(x, 52) == bit(y, 52));
    assert(bit(x, 53) == bit(y, 53));
    assert(bit(x, 54) == bit(y, 54));
    assert(bit(x, 55) == bit(y, 55));
    assert(bit(x, 56) == bit(y, 56));
    assert(bit(x, 57) == bit(y, 57));
    assert(bit(x, 58) == bit(y, 58));
    assert(bit(x, 59) == bit(y, 59));
    assert(bit(x, 60) == bit(y, 60));
    assert(bit(x, 61) == bit(y, 61));
    assert(bit(x, 62) == bit(y, 62));
    assert(bit(x, 63) == bit(y, 63));
    assert(x == y) by (bit_vector)
        requires
            ((x >> 0u64) & 1 == 1) == ((y >> 0u64) & 1 == 1),
            ((x >> 1u64) & 1 == 1) == ((y >> 1u64) & 1 == 1),
            ((x >> 2u64) & 1 == 1) == ((y >> 2u64) & 1 == 1),
            ((x >> 3u64) & 1 == 1) == ((y >> 3u64) & 1 == 1),
            ((x >> 4u64) & 1 == 1) == ((y >> 4u64) & 1 == 1),
            ((x >> 5u64) & 1 == 1) == ((y >> 5u64) & 1 == 1),
            ((x >> 6u64) & 1 == 1) == ((y >> 6u64) & 1 == 1),
            ((x >> 7u64) & 1 == 1) == ((y >> 7u64) & 1 == 1),
            ((x >> 8u64) & 1 == 1) == ((y >> 8u64) & 1 == 1),
            ((x >> 9u64) & 1 == 1) == ((y >> 9u64) & 1 == 1),
            ((x >> 10u64) & 1 == 1) == ((y >> 10u64) & 1 == 1),
            ((x >> 11u64) & 1 == 1) == ((y >> 11u64) & 1 == 1),
            ((x >> 12u64) & 1 == 1) == ((y >> 12u64) & 1 == 1),
            ((x >> 13u64) & 1 == 1) == ((y >> 13u64) & 1 == 1),
            ((x >> 14u64) & 1 == 1) == ((y >> 14u64) & 1 == 1),
            ((x >> 15u64) & 1 == 1) == ((y >> 15u64) & 1 == 1),
            ((x >> 16u64) & 1 == 1) == ((y >> 16u64) & 1 == 1),
            ((x >> 17u64) & 1 == 1) == ((y >> 17u64) & 1 == 1),
            ((x >> 18u64) & 1 == 1) == ((y >> 18u64) & 1 == 1),
            ((x >> 19u64) & 1 == 1) == ((y >> 19u64) & 1 == 1),
            ((x >> 20u64) & 1 == 1) == ((y >> 20u64) & 1 == 1),
            ((x >> 21u64) & 1 == 1) == ((y >> 21u64) & 1 == 1),
            ((x >> 22u64) & 1 == 1) == ((y >> 22u64) & 1 == 1),
            ((x >> 23u64) & 1 == 1) == ((y >> 23u64) & 1 == 1),
            ((x >> 24u64) & 1 == 1) == ((y >> 24u64) & 1 == 1),
            ((x >> 25u64) & 1 == 1) == ((y >> 25u64) & 1 == 1),
            ((x >> 26u64) & 1 == 1) == ((y >> 26u64) & 1 == 1),
            ((x >> 27u64) & 1 == 1) == ((y >> 27u64) & 1 == 1),
            ((x >> 28u64) & 1 == 1) == ((y >> 28u64) & 1 == 1),
            ((x >> 29u64) & 1 == 1) == ((y >> 29u64) & 1 == 1),
            ((x >> 30u64) & 1 == 1) == ((y >> 30u64) & 1 == 1),
            ((x >> 31u64) & 1 == 1) == ((y >> 31u64) & 1 == 1),
            ((x >> 32u64) & 1 == 1) == ((y >> 32u64) & 1 == 1),
            ((x >> 33u64) & 1 == 1) == ((y >> 33u64) & 1 == 1),
            ((x >> 34u64) & 1 == 1) == ((y >> 34u64) & 1 == 1),
            ((x >> 35u64) & 1 == 1) == ((y >> 35u64) & 1 == 1),
            ((x >> 36u64) & 1 == 1) == ((y >> 36u64) & 1 == 1),
            ((x >> 37u64) & 1 == 1) == ((y >> 37u64) & 1 == 1),
            ((x >> 38u64) & 1 == 1) == ((y >> 38u64) & 1 == 1),
            ((x >> 39u64) & 1 == 1) == ((y >> 39u64) & 1 == 1),
            ((x >> 40u64) & 1 == 1) == ((y >> 40u64) & 1 == 1),
            ((x >> 41u64) & 1 == 1) == ((y >> 41u64) & 1 == 1),
            ((x >> 42u64) & 1 == 1) == ((y >> 42u64) & 1 == 1),
            ((x >> 43u64) & 1 == 1) == ((y >> 43u64) & 1 == 1),
            ((x >> 44u64) & 1 == 1) == ((y >> 44u64) & 1 == 1),
            ((x >> 45u64) & 1 == 1) == ((y >> 45u64) & 1 == 1),
            ((x >> 46u64) & 1 == 1) == ((y >> 46u64) & 1 == 1),
            ((x >> 47u64) & 1 == 1) == ((y >> 47u64) & 1 == 1),
            ((x >> 48u64) & 1 == 1) == ((y >> 48u64) & 1 == 1),
            ((x >> 49u64) & 1 == 1) == ((y >> 49u64) & 1 == 1),
            ((x >> 50u64) & 1 == 1) == ((y >> 50u64) & 1 == 1),
            ((x >> 51u64) & 1 == 1) == ((y >> 51u64) & 1 == 1),
            ((x >> 52u64) & 1 == 1) == ((y >> 52u64) & 1 == 1),
            ((x >> 53u64) & 1 == 1) == ((y >> 53u64) & 1 == 1),
            ((x >> 54u64) & 1 == 1) == ((y >> 54u64) & 1 == 1),
            ((x >> 55u64) & 1 == 1) == ((y >> 55u64) & 1 == 1),
            ((x >> 56u64) & 1 == 1) == ((y >> 56u64) & 1 == 1),
            ((x >> 57u64) & 1 == 1) == ((y >> 57u64) & 1 == 1),
            ((x >> 58u64) & 1 == 1) == ((y >> 58u64) & 1 == 1),
            ((x >> 59u64) & 1 == 1) == ((y >> 59u64) & 1 == 1),
            ((x >> 60u64) & 1 == 1) == ((y >> 60u64) & 1 == 1),
            ((x >> 61u64) & 1 == 1) == ((y >> 61u64) & 1 == 1),
            ((x >> 62u64) & 1 == 1) == ((y >> 62u64) & 1 == 1),
            ((x >> 63u64) & 1 == 1) == ((y >> 63u64) & 1 == 1),
    ;
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
