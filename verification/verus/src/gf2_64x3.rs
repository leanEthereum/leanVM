//! The extension field `E = K[y] / (y^3 + y + 1)` over the base field `K = GF(2^64)`.
//!
//! The executable functions are the portable paths of `crates/primitives/src/field/gf2_64x3.rs` and
//! `gf2_64x3/software.rs`, copied with the same bodies where Verus accepts them; `tests/equivalence.rs`
//! checks the two agree.
//!
//! Specification: an element is `c0 + c1 y + c2 y^2` with `c_i` in `K`. The product [`e_mul`] is the
//! product of polynomials in `y` over `K` (coefficients by [`k_mul`]), folded by `y^3 = y + 1` and
//! `y^4 = y^2 + y`.
use crate::clmul::*;
use crate::gf2_64::*;
use vstd::arithmetic::power2::*;
use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul, MulAssign};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// The product in `E`.
///
/// ```text
///     (a0 + a1 y + a2 y^2)(b0 + b1 y + b2 y^2) = d0 + d1 y + d2 y^2 + d3 y^3 + d4 y^4,
///     d_k = sum_{i + j = k} a_i b_j,   and y^3 = y + 1, y^4 = y^2 + y.
/// ```
pub open spec fn e_mul(a: F192, b: F192) -> F192 {
    let d0 = k_mul(a.c0, b.c0);
    let d1 = k_mul(a.c0, b.c1) ^ k_mul(a.c1, b.c0);
    let d2 = k_mul(a.c0, b.c2) ^ k_mul(a.c1, b.c1) ^ k_mul(a.c2, b.c0);
    let d3 = k_mul(a.c1, b.c2) ^ k_mul(a.c2, b.c1);
    let d4 = k_mul(a.c2, b.c2);
    F192 { c0: d0 ^ d3, c1: d1 ^ d3 ^ d4, c2: d2 ^ d4 }
}

/// The sum in `E`, coefficient-wise in `K`.
pub open spec fn e_add(a: F192, b: F192) -> F192 {
    F192 { c0: a.c0 ^ b.c0, c1: a.c1 ^ b.c1, c2: a.c2 ^ b.c2 }
}

/// The embedding of `K` in `E`.
pub open spec fn e_from_k(k: u64) -> F192 {
    F192 { c0: k, c1: 0, c2: 0 }
}

/// A 128-bit coefficient from its `[low, high]` words.
pub open spec fn wide(w: [u64; 2]) -> u128 {
    ((w[1] as u128) << 64u128) | (w[0] as u128)
}

/// The element an unreduced value stands for: each 128-bit coefficient reduced modulo `M`.
pub open spec fn e_value(u: F192Unreduced) -> F192 {
    F192 { c0: k_mod(wide(u.coeffs[0])), c1: k_mod(wide(u.coeffs[1])), c2: k_mod(wide(u.coeffs[2])) }
}

/// Coefficient-wise XOR of unreduced values.
pub open spec fn u_xor(u: F192Unreduced, v: F192Unreduced) -> F192Unreduced {
    F192Unreduced {
        coeffs: [
            [u.coeffs[0][0] ^ v.coeffs[0][0], u.coeffs[0][1] ^ v.coeffs[0][1]],
            [u.coeffs[1][0] ^ v.coeffs[1][0], u.coeffs[1][1] ^ v.coeffs[1][1]],
            [u.coeffs[2][0] ^ v.coeffs[2][0], u.coeffs[2][1] ^ v.coeffs[2][1]],
        ],
    }
}

/// The unreduced value with the given 128-bit coefficients.
pub open spec fn u_from_wide(c0: u128, c1: u128, c2: u128) -> F192Unreduced {
    F192Unreduced {
        coeffs: [[c0 as u64, (c0 >> 64u128) as u64], [c1 as u64, (c1 >> 64u128) as u64], [
            c2 as u64,
            (c2 >> 64u128) as u64,
        ]],
    }
}

pub proof fn lemma_wide_split(c: u128)
    ensures
        wide([c as u64, (c >> 64u128) as u64]) == c,
{
    assert(((((c >> 64u128) as u64) as u128) << 64u128) | ((c as u64) as u128) == c) by (bit_vector);
}

pub proof fn lemma_u_from_wide(c0: u128, c1: u128, c2: u128)
    ensures
        e_value(u_from_wide(c0, c1, c2)) == (F192 { c0: k_mod(c0), c1: k_mod(c1), c2: k_mod(c2) }),
{
    lemma_wide_split(c0);
    lemma_wide_split(c1);
    lemma_wide_split(c2);
}

/// Lazy reduction: reducing a XOR of unreduced values is the sum of their reductions.
pub proof fn lemma_e_value_xor(u: F192Unreduced, v: F192Unreduced)
    ensures
        e_value(u_xor(u, v)) == e_add(e_value(u), e_value(v)),
{
    let w = u_xor(u, v);
    assert forall|k: int| 0 <= k < 3 implies #[trigger] wide(w.coeffs[k]) == wide(u.coeffs[k]) ^ wide(v.coeffs[k]) by {
        let (a0, a1, b0, b1) = (u.coeffs[k][0], u.coeffs[k][1], v.coeffs[k][0], v.coeffs[k][1]);
        assert((((a1 ^ b1) as u128) << 64u128) | ((a0 ^ b0) as u128) == (((a1 as u128) << 64u128) | (
        a0 as u128)) ^ (((b1 as u128) << 64u128) | (b0 as u128))) by (bit_vector);
    }
    lemma_k_mod_xor(wide(u.coeffs[0]), wide(v.coeffs[0]));
    lemma_k_mod_xor(wide(u.coeffs[1]), wide(v.coeffs[1]));
    lemma_k_mod_xor(wide(u.coeffs[2]), wide(v.coeffs[2]));
}

/// XOR of a sequence of unreduced values.
pub open spec fn u_sum(us: Seq<F192Unreduced>) -> F192Unreduced
    decreases us.len(),
{
    if us.len() == 0 {
        F192Unreduced::ZERO
    } else {
        u_xor(u_sum(us.drop_last()), us.last())
    }
}

/// Sum of a sequence of elements.
pub open spec fn e_sum(es: Seq<F192>) -> F192
    decreases es.len(),
{
    if es.len() == 0 {
        F192::ZERO
    } else {
        e_add(e_sum(es.drop_last()), es.last())
    }
}

/// The identity the accumulating kernels rely on: reducing an XOR-accumulated sum of unreduced
/// values once equals summing the reduced values.
pub proof fn lemma_lazy_reduction(us: Seq<F192Unreduced>)
    ensures
        e_value(u_sum(us)) == e_sum(us.map_values(|u: F192Unreduced| e_value(u))),
    decreases us.len(),
{
    let es = us.map_values(|u: F192Unreduced| e_value(u));
    if us.len() == 0 {
        lemma_u_zero();
    } else {
        lemma_lazy_reduction(us.drop_last());
        assert(us.drop_last().map_values(|u: F192Unreduced| e_value(u)) =~= es.drop_last());
        lemma_e_value_xor(u_sum(us.drop_last()), us.last());
    }
}

pub proof fn lemma_u_zero()
    ensures
        e_value(F192Unreduced::ZERO) == F192::ZERO,
{
    lemma_u_from_wide(0, 0, 0);
    assert(u_from_wide(0, 0, 0) == F192Unreduced::ZERO) by {
        assert((0u128 as u64) == 0 && ((0u128 >> 64u128) as u64) == 0) by (bit_vector);
    }
    assert(0u128 >> 64u128 == 0) by (bit_vector);
    lemma_k_mod_small(0);
}

// ---------------------------------------------------------------------------------------------
// The software product, unrolled: what the 3 x 3 loop accumulates
// ---------------------------------------------------------------------------------------------
/// The accumulator `e` after the first `n` steps of the schoolbook loop (row-major over `i, j < 3`).
pub open spec fn sched(a: Seq<u64>, b: Seq<u64>, n: nat) -> Seq<u128>
    decreases n,
{
    if n == 0 {
        seq![0u128, 0u128, 0u128, 0u128, 0u128]
    } else {
        let s = sched(a, b, (n - 1) as nat);
        let (i, j) = (((n - 1) / 3) as int, ((n - 1) % 3) as int);
        s.update(i + j, s[i + j] ^ clmul(a[i], b[j] as u128))
    }
}

/// `p_ij = a_i * b_j` as polynomials.
pub open spec fn cp(a: Seq<u64>, b: Seq<u64>, i: int, j: int) -> u128 {
    clmul(a[i], b[j] as u128)
}

pub proof fn lemma_sched_9(a: Seq<u64>, b: Seq<u64>)
    requires
        a.len() == 3,
        b.len() == 3,
    ensures
        sched(a, b, 9) == seq![
            0 ^ cp(a, b, 0, 0),
            0 ^ cp(a, b, 0, 1) ^ cp(a, b, 1, 0),
            0 ^ cp(a, b, 0, 2) ^ cp(a, b, 1, 1) ^ cp(a, b, 2, 0),
            0 ^ cp(a, b, 1, 2) ^ cp(a, b, 2, 1),
            0 ^ cp(a, b, 2, 2),
        ],
{
    reveal_with_fuel(sched, 10);
    assert(sched(a, b, 9) =~= seq![
            0 ^ cp(a, b, 0, 0),
            0 ^ cp(a, b, 0, 1) ^ cp(a, b, 1, 0),
            0 ^ cp(a, b, 0, 2) ^ cp(a, b, 1, 1) ^ cp(a, b, 2, 0),
            0 ^ cp(a, b, 1, 2) ^ cp(a, b, 2, 1),
            0 ^ cp(a, b, 2, 2),
        ]);
}

/// The y-folded coefficients reduce to the product in `E`.
pub proof fn lemma_mul_unreduced_value(a: F192, b: F192)
    ensures
        ({
            let (sa, sb) = (seq![a.c0, a.c1, a.c2], seq![b.c0, b.c1, b.c2]);
            let e = sched(sa, sb, 9);
            e_value(u_from_wide(e[0] ^ e[3], e[1] ^ e[3] ^ e[4], e[2] ^ e[4])) == e_mul(a, b)
        }),
{
    let (sa, sb) = (seq![a.c0, a.c1, a.c2], seq![b.c0, b.c1, b.c2]);
    lemma_sched_9(sa, sb);
    let e = sched(sa, sb, 9);
    lemma_u_from_wide(e[0] ^ e[3], e[1] ^ e[3] ^ e[4], e[2] ^ e[4]);
    assert forall|x: u128| #![auto] 0 ^ x == x by {
        assert(0 ^ x == x) by (bit_vector);
    }
    let p = |i: int, j: int| cp(sa, sb, i, j);
    // Reduction is linear, so it distributes over every XOR.
    lemma_k_mod_xor(e[0], e[3]);
    lemma_k_mod_xor(e[1] ^ e[3], e[4]);
    lemma_k_mod_xor(e[1], e[3]);
    lemma_k_mod_xor(e[2], e[4]);
    lemma_k_mod_xor(p(0, 1), p(1, 0));
    lemma_k_mod_xor(p(0, 2) ^ p(1, 1), p(2, 0));
    lemma_k_mod_xor(p(0, 2), p(1, 1));
    lemma_k_mod_xor(p(1, 2), p(2, 1));
}

// ---------------------------------------------------------------------------------------------
// E is a commutative ring, and its Frobenius
// ---------------------------------------------------------------------------------------------
/// `a^n` in `E`.
pub open spec fn e_pow(a: F192, n: nat) -> F192
    decreases n,
{
    if n == 0 {
        F192::ONE
    } else {
        e_mul(e_pow(a, (n - 1) as nat), a)
    }
}

/// `a` squared `n` times in `E`.
pub open spec fn e_sq_iter(a: F192, n: nat) -> F192
    decreases n,
{
    if n == 0 {
        a
    } else {
        let v = e_sq_iter(a, (n - 1) as nat);
        e_mul(v, v)
    }
}

/// The Frobenius shuffle `c0 + c2 y + (c1 + c2) y^2`.
pub open spec fn e_frobenius(a: F192) -> F192 {
    F192 { c0: a.c0, c1: a.c2, c2: a.c1 ^ a.c2 }
}

pub proof fn lemma_e_mul_one(a: F192)
    ensures
        e_mul(a, F192::ONE) == a,
        e_mul(F192::ONE, a) == a,
{
    lemma_k_mul_one(a.c0);
    lemma_k_mul_one(a.c1);
    lemma_k_mul_one(a.c2);
    lemma_k_mul_zero(a.c0);
    lemma_k_mul_zero(a.c1);
    lemma_k_mul_zero(a.c2);
    let (x0, x1, x2) = (a.c0, a.c1, a.c2);
    assert(x0 ^ (0u64 ^ 0u64) == x0 && (0u64 ^ x1) ^ (0u64 ^ 0u64) ^ 0u64 == x1 && (0u64 ^ 0u64 ^ x2) ^ 0u64
        == x2) by (bit_vector);
    assert(x0 ^ (0u64 ^ 0u64) == x0 && (0u64 ^ x1) ^ (0u64 ^ 0u64) ^ 0u64 == x1 && (0u64 ^ 0u64 ^ x2) ^ 0u64
        == x2) by (bit_vector);
    assert(x0 ^ (0u64 ^ 0u64) == x0 && (x1 ^ 0u64) ^ (0u64 ^ 0u64) ^ 0u64 == x1 && (x2 ^ 0u64 ^ 0u64) ^ 0u64
        == x2) by (bit_vector);
}

pub proof fn lemma_e_mul_comm(a: F192, b: F192)
    ensures
        e_mul(a, b) == e_mul(b, a),
{
    lemma_k_mul_comm(a.c0, b.c0);
    lemma_k_mul_comm(a.c0, b.c1);
    lemma_k_mul_comm(a.c0, b.c2);
    lemma_k_mul_comm(a.c1, b.c0);
    lemma_k_mul_comm(a.c1, b.c1);
    lemma_k_mul_comm(a.c1, b.c2);
    lemma_k_mul_comm(a.c2, b.c0);
    lemma_k_mul_comm(a.c2, b.c1);
    lemma_k_mul_comm(a.c2, b.c2);
    let (p00, p01, p02, p10, p11, p12, p20, p21, p22) = (
        k_mul(a.c0, b.c0),
        k_mul(a.c0, b.c1),
        k_mul(a.c0, b.c2),
        k_mul(a.c1, b.c0),
        k_mul(a.c1, b.c1),
        k_mul(a.c1, b.c2),
        k_mul(a.c2, b.c0),
        k_mul(a.c2, b.c1),
        k_mul(a.c2, b.c2),
    );
    assert(p00 ^ (p12 ^ p21) == p00 ^ (p21 ^ p12) && (p01 ^ p10) ^ (p12 ^ p21) ^ p22 == (p10 ^ p01) ^ (p21 ^ p12)
        ^ p22 && (p02 ^ p11 ^ p20) ^ p22 == (p20 ^ p11 ^ p02) ^ p22) by (bit_vector);
}

/// Associativity, by expanding both sides into the 27 triple products of coefficients.
pub proof fn lemma_e_mul_assoc(a: F192, b: F192, c: F192)
    ensures
        e_mul(e_mul(a, b), c) == e_mul(a, e_mul(b, c)),
{
    let t000 = k_mul(k_mul(a.c0, b.c0), c.c0);
    lemma_k_mul_assoc(a.c0, b.c0, c.c0);
    let t001 = k_mul(k_mul(a.c0, b.c0), c.c1);
    lemma_k_mul_assoc(a.c0, b.c0, c.c1);
    let t002 = k_mul(k_mul(a.c0, b.c0), c.c2);
    lemma_k_mul_assoc(a.c0, b.c0, c.c2);
    let t010 = k_mul(k_mul(a.c0, b.c1), c.c0);
    lemma_k_mul_assoc(a.c0, b.c1, c.c0);
    let t011 = k_mul(k_mul(a.c0, b.c1), c.c1);
    lemma_k_mul_assoc(a.c0, b.c1, c.c1);
    let t012 = k_mul(k_mul(a.c0, b.c1), c.c2);
    lemma_k_mul_assoc(a.c0, b.c1, c.c2);
    let t020 = k_mul(k_mul(a.c0, b.c2), c.c0);
    lemma_k_mul_assoc(a.c0, b.c2, c.c0);
    let t021 = k_mul(k_mul(a.c0, b.c2), c.c1);
    lemma_k_mul_assoc(a.c0, b.c2, c.c1);
    let t022 = k_mul(k_mul(a.c0, b.c2), c.c2);
    lemma_k_mul_assoc(a.c0, b.c2, c.c2);
    let t100 = k_mul(k_mul(a.c1, b.c0), c.c0);
    lemma_k_mul_assoc(a.c1, b.c0, c.c0);
    let t101 = k_mul(k_mul(a.c1, b.c0), c.c1);
    lemma_k_mul_assoc(a.c1, b.c0, c.c1);
    let t102 = k_mul(k_mul(a.c1, b.c0), c.c2);
    lemma_k_mul_assoc(a.c1, b.c0, c.c2);
    let t110 = k_mul(k_mul(a.c1, b.c1), c.c0);
    lemma_k_mul_assoc(a.c1, b.c1, c.c0);
    let t111 = k_mul(k_mul(a.c1, b.c1), c.c1);
    lemma_k_mul_assoc(a.c1, b.c1, c.c1);
    let t112 = k_mul(k_mul(a.c1, b.c1), c.c2);
    lemma_k_mul_assoc(a.c1, b.c1, c.c2);
    let t120 = k_mul(k_mul(a.c1, b.c2), c.c0);
    lemma_k_mul_assoc(a.c1, b.c2, c.c0);
    let t121 = k_mul(k_mul(a.c1, b.c2), c.c1);
    lemma_k_mul_assoc(a.c1, b.c2, c.c1);
    let t122 = k_mul(k_mul(a.c1, b.c2), c.c2);
    lemma_k_mul_assoc(a.c1, b.c2, c.c2);
    let t200 = k_mul(k_mul(a.c2, b.c0), c.c0);
    lemma_k_mul_assoc(a.c2, b.c0, c.c0);
    let t201 = k_mul(k_mul(a.c2, b.c0), c.c1);
    lemma_k_mul_assoc(a.c2, b.c0, c.c1);
    let t202 = k_mul(k_mul(a.c2, b.c0), c.c2);
    lemma_k_mul_assoc(a.c2, b.c0, c.c2);
    let t210 = k_mul(k_mul(a.c2, b.c1), c.c0);
    lemma_k_mul_assoc(a.c2, b.c1, c.c0);
    let t211 = k_mul(k_mul(a.c2, b.c1), c.c1);
    lemma_k_mul_assoc(a.c2, b.c1, c.c1);
    let t212 = k_mul(k_mul(a.c2, b.c1), c.c2);
    lemma_k_mul_assoc(a.c2, b.c1, c.c2);
    let t220 = k_mul(k_mul(a.c2, b.c2), c.c0);
    lemma_k_mul_assoc(a.c2, b.c2, c.c0);
    let t221 = k_mul(k_mul(a.c2, b.c2), c.c1);
    lemma_k_mul_assoc(a.c2, b.c2, c.c1);
    let t222 = k_mul(k_mul(a.c2, b.c2), c.c2);
    lemma_k_mul_assoc(a.c2, b.c2, c.c2);
    lemma_k_mul_xor_left(k_mul(a.c0, b.c0), (k_mul(a.c1, b.c2) ^ k_mul(a.c2, b.c1)), c.c0);
    lemma_k_mul_xor_left(k_mul(a.c1, b.c2), k_mul(a.c2, b.c1), c.c0);
    lemma_k_mul_xor_left(k_mul(a.c0, b.c0), (k_mul(a.c1, b.c2) ^ k_mul(a.c2, b.c1)), c.c1);
    lemma_k_mul_xor_left(k_mul(a.c1, b.c2), k_mul(a.c2, b.c1), c.c1);
    lemma_k_mul_xor_left(k_mul(a.c0, b.c0), (k_mul(a.c1, b.c2) ^ k_mul(a.c2, b.c1)), c.c2);
    lemma_k_mul_xor_left(k_mul(a.c1, b.c2), k_mul(a.c2, b.c1), c.c2);
    lemma_k_mul_xor_left(((k_mul(a.c0, b.c1) ^ k_mul(a.c1, b.c0)) ^ (k_mul(a.c1, b.c2) ^ k_mul(a.c2, b.c1))), k_mul(a.c2, b.c2), c.c0);
    lemma_k_mul_xor_left((k_mul(a.c0, b.c1) ^ k_mul(a.c1, b.c0)), (k_mul(a.c1, b.c2) ^ k_mul(a.c2, b.c1)), c.c0);
    lemma_k_mul_xor_left(k_mul(a.c0, b.c1), k_mul(a.c1, b.c0), c.c0);
    lemma_k_mul_xor_left(k_mul(a.c1, b.c2), k_mul(a.c2, b.c1), c.c0);
    lemma_k_mul_xor_left(((k_mul(a.c0, b.c1) ^ k_mul(a.c1, b.c0)) ^ (k_mul(a.c1, b.c2) ^ k_mul(a.c2, b.c1))), k_mul(a.c2, b.c2), c.c1);
    lemma_k_mul_xor_left((k_mul(a.c0, b.c1) ^ k_mul(a.c1, b.c0)), (k_mul(a.c1, b.c2) ^ k_mul(a.c2, b.c1)), c.c1);
    lemma_k_mul_xor_left(k_mul(a.c0, b.c1), k_mul(a.c1, b.c0), c.c1);
    lemma_k_mul_xor_left(k_mul(a.c1, b.c2), k_mul(a.c2, b.c1), c.c1);
    lemma_k_mul_xor_left(((k_mul(a.c0, b.c1) ^ k_mul(a.c1, b.c0)) ^ (k_mul(a.c1, b.c2) ^ k_mul(a.c2, b.c1))), k_mul(a.c2, b.c2), c.c2);
    lemma_k_mul_xor_left((k_mul(a.c0, b.c1) ^ k_mul(a.c1, b.c0)), (k_mul(a.c1, b.c2) ^ k_mul(a.c2, b.c1)), c.c2);
    lemma_k_mul_xor_left(k_mul(a.c0, b.c1), k_mul(a.c1, b.c0), c.c2);
    lemma_k_mul_xor_left(k_mul(a.c1, b.c2), k_mul(a.c2, b.c1), c.c2);
    lemma_k_mul_xor_left(((k_mul(a.c0, b.c2) ^ k_mul(a.c1, b.c1)) ^ k_mul(a.c2, b.c0)), k_mul(a.c2, b.c2), c.c0);
    lemma_k_mul_xor_left((k_mul(a.c0, b.c2) ^ k_mul(a.c1, b.c1)), k_mul(a.c2, b.c0), c.c0);
    lemma_k_mul_xor_left(k_mul(a.c0, b.c2), k_mul(a.c1, b.c1), c.c0);
    lemma_k_mul_xor_left(((k_mul(a.c0, b.c2) ^ k_mul(a.c1, b.c1)) ^ k_mul(a.c2, b.c0)), k_mul(a.c2, b.c2), c.c1);
    lemma_k_mul_xor_left((k_mul(a.c0, b.c2) ^ k_mul(a.c1, b.c1)), k_mul(a.c2, b.c0), c.c1);
    lemma_k_mul_xor_left(k_mul(a.c0, b.c2), k_mul(a.c1, b.c1), c.c1);
    lemma_k_mul_xor_left(((k_mul(a.c0, b.c2) ^ k_mul(a.c1, b.c1)) ^ k_mul(a.c2, b.c0)), k_mul(a.c2, b.c2), c.c2);
    lemma_k_mul_xor_left((k_mul(a.c0, b.c2) ^ k_mul(a.c1, b.c1)), k_mul(a.c2, b.c0), c.c2);
    lemma_k_mul_xor_left(k_mul(a.c0, b.c2), k_mul(a.c1, b.c1), c.c2);
    lemma_k_mul_xor_right(a.c0, k_mul(b.c0, c.c0), (k_mul(b.c1, c.c2) ^ k_mul(b.c2, c.c1)));
    lemma_k_mul_xor_right(a.c0, k_mul(b.c1, c.c2), k_mul(b.c2, c.c1));
    lemma_k_mul_xor_right(a.c0, ((k_mul(b.c0, c.c1) ^ k_mul(b.c1, c.c0)) ^ (k_mul(b.c1, c.c2) ^ k_mul(b.c2, c.c1))), k_mul(b.c2, c.c2));
    lemma_k_mul_xor_right(a.c0, (k_mul(b.c0, c.c1) ^ k_mul(b.c1, c.c0)), (k_mul(b.c1, c.c2) ^ k_mul(b.c2, c.c1)));
    lemma_k_mul_xor_right(a.c0, k_mul(b.c0, c.c1), k_mul(b.c1, c.c0));
    lemma_k_mul_xor_right(a.c0, k_mul(b.c1, c.c2), k_mul(b.c2, c.c1));
    lemma_k_mul_xor_right(a.c0, ((k_mul(b.c0, c.c2) ^ k_mul(b.c1, c.c1)) ^ k_mul(b.c2, c.c0)), k_mul(b.c2, c.c2));
    lemma_k_mul_xor_right(a.c0, (k_mul(b.c0, c.c2) ^ k_mul(b.c1, c.c1)), k_mul(b.c2, c.c0));
    lemma_k_mul_xor_right(a.c0, k_mul(b.c0, c.c2), k_mul(b.c1, c.c1));
    lemma_k_mul_xor_right(a.c1, k_mul(b.c0, c.c0), (k_mul(b.c1, c.c2) ^ k_mul(b.c2, c.c1)));
    lemma_k_mul_xor_right(a.c1, k_mul(b.c1, c.c2), k_mul(b.c2, c.c1));
    lemma_k_mul_xor_right(a.c1, ((k_mul(b.c0, c.c1) ^ k_mul(b.c1, c.c0)) ^ (k_mul(b.c1, c.c2) ^ k_mul(b.c2, c.c1))), k_mul(b.c2, c.c2));
    lemma_k_mul_xor_right(a.c1, (k_mul(b.c0, c.c1) ^ k_mul(b.c1, c.c0)), (k_mul(b.c1, c.c2) ^ k_mul(b.c2, c.c1)));
    lemma_k_mul_xor_right(a.c1, k_mul(b.c0, c.c1), k_mul(b.c1, c.c0));
    lemma_k_mul_xor_right(a.c1, k_mul(b.c1, c.c2), k_mul(b.c2, c.c1));
    lemma_k_mul_xor_right(a.c1, ((k_mul(b.c0, c.c2) ^ k_mul(b.c1, c.c1)) ^ k_mul(b.c2, c.c0)), k_mul(b.c2, c.c2));
    lemma_k_mul_xor_right(a.c1, (k_mul(b.c0, c.c2) ^ k_mul(b.c1, c.c1)), k_mul(b.c2, c.c0));
    lemma_k_mul_xor_right(a.c1, k_mul(b.c0, c.c2), k_mul(b.c1, c.c1));
    lemma_k_mul_xor_right(a.c2, k_mul(b.c0, c.c0), (k_mul(b.c1, c.c2) ^ k_mul(b.c2, c.c1)));
    lemma_k_mul_xor_right(a.c2, k_mul(b.c1, c.c2), k_mul(b.c2, c.c1));
    lemma_k_mul_xor_right(a.c2, ((k_mul(b.c0, c.c1) ^ k_mul(b.c1, c.c0)) ^ (k_mul(b.c1, c.c2) ^ k_mul(b.c2, c.c1))), k_mul(b.c2, c.c2));
    lemma_k_mul_xor_right(a.c2, (k_mul(b.c0, c.c1) ^ k_mul(b.c1, c.c0)), (k_mul(b.c1, c.c2) ^ k_mul(b.c2, c.c1)));
    lemma_k_mul_xor_right(a.c2, k_mul(b.c0, c.c1), k_mul(b.c1, c.c0));
    lemma_k_mul_xor_right(a.c2, k_mul(b.c1, c.c2), k_mul(b.c2, c.c1));
    lemma_k_mul_xor_right(a.c2, ((k_mul(b.c0, c.c2) ^ k_mul(b.c1, c.c1)) ^ k_mul(b.c2, c.c0)), k_mul(b.c2, c.c2));
    lemma_k_mul_xor_right(a.c2, (k_mul(b.c0, c.c2) ^ k_mul(b.c1, c.c1)), k_mul(b.c2, c.c0));
    lemma_k_mul_xor_right(a.c2, k_mul(b.c0, c.c2), k_mul(b.c1, c.c1));
    assert(((t000 ^ (t120 ^ t210)) ^ ((((t012 ^ t102) ^ (t122 ^ t212)) ^ t222) ^ (((t021 ^ t111) ^ t201) ^ t221))) == ((t000 ^ (t012 ^ t021)) ^ ((((t102 ^ t111) ^ t120) ^ t122) ^ (((t201 ^ t210) ^ (t212 ^ t221)) ^ t222))) && ((((t001 ^ (t121 ^ t211)) ^ (((t010 ^ t100) ^ (t120 ^ t210)) ^ t220)) ^ ((((t012 ^ t102) ^ (t122 ^ t212)) ^ t222) ^ (((t021 ^ t111) ^ t201) ^ t221))) ^ (((t022 ^ t112) ^ t202) ^ t222)) == ((((((t001 ^ t010) ^ (t012 ^ t021)) ^ t022) ^ (t100 ^ (t112 ^ t121))) ^ ((((t102 ^ t111) ^ t120) ^ t122) ^ (((t201 ^ t210) ^ (t212 ^ t221)) ^ t222))) ^ (((t202 ^ t211) ^ t220) ^ t222)) && ((((t002 ^ (t122 ^ t212)) ^ (((t011 ^ t101) ^ (t121 ^ t211)) ^ t221)) ^ (((t020 ^ t110) ^ t200) ^ t220)) ^ (((t022 ^ t112) ^ t202) ^ t222)) == ((((((t002 ^ t011) ^ t020) ^ t022) ^ (((t101 ^ t110) ^ (t112 ^ t121)) ^ t122)) ^ (t200 ^ (t212 ^ t221))) ^ (((t202 ^ t211) ^ t220) ^ t222))) by (bit_vector);
}

pub proof fn lemma_e_pow_add(a: F192, m: nat, n: nat)
    ensures
        e_mul(e_pow(a, m), e_pow(a, n)) == e_pow(a, m + n),
    decreases n,
{
    if n == 0 {
        lemma_e_mul_one(e_pow(a, m));
    } else {
        lemma_e_pow_add(a, m, (n - 1) as nat);
        lemma_e_mul_assoc(e_pow(a, m), e_pow(a, (n - 1) as nat), a);
        assert((m + n - 1) as nat + 1 == m + n);
    }
}

pub proof fn lemma_e_pow_mul(a: F192, m: nat, n: nat)
    ensures
        e_pow(e_pow(a, m), n) == e_pow(a, m * n),
    decreases n,
{
    if n == 0 {
        assert(m * 0 == 0) by (nonlinear_arith);
    } else {
        lemma_e_pow_mul(a, m, (n - 1) as nat);
        lemma_e_pow_add(a, m * (n - 1) as nat, m);
        assert(m * (n - 1) as nat + m == m * n) by (nonlinear_arith)
            requires
                n > 0,
        ;
    }
}

pub proof fn lemma_e_pow_one(a: F192)
    ensures
        e_pow(a, 1) == a,
{
    assert(e_pow(a, 0) == F192::ONE);
    lemma_e_mul_one(a);
}

pub proof fn lemma_e_sq_iter_pow(a: F192, n: nat)
    ensures
        e_sq_iter(a, n) == e_pow(a, pow2(n)),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
        lemma_e_pow_one(a);
    } else {
        lemma_e_sq_iter_pow(a, (n - 1) as nat);
        let e = pow2((n - 1) as nat);
        lemma_e_pow_add(a, e, e);
        lemma_pow2_unfold(n);
    }
}

/// The Galois action on the y-coefficients after `n` squarings: `(c1, c2) -> (c2, c1 + c2)` has order 3.
pub open spec fn rot(n: nat, x1: u64, x2: u64) -> (u64, u64) {
    if n % 3 == 0 {
        (x1, x2)
    } else if n % 3 == 1 {
        (x2, x1 ^ x2)
    } else {
        (x1 ^ x2, x1)
    }
}

/// `n` squarings in `E` square each coefficient `n` times and rotate the y-coefficients.
pub proof fn lemma_e_sq_iter_shape(a: F192, n: nat)
    ensures
        ({
            let r = rot(n, k_sq_iter(a.c1, n), k_sq_iter(a.c2, n));
            e_sq_iter(a, n) == (F192 { c0: k_sq_iter(a.c0, n), c1: r.0, c2: r.1 })
        }),
    decreases n,
{
    if n > 0 {
        let i = (n - 1) as nat;
        lemma_e_sq_iter_shape(a, i);
        let v = e_sq_iter(a, i);
        lemma_square_spec(v);
        let (x, y) = (k_sq_iter(a.c1, i), k_sq_iter(a.c2, i));
        lemma_k_square_xor(x, y);
        let (sx, sy) = (k_mul(x, x), k_mul(y, y));
        assert(sy ^ (sx ^ sy) == sx && (sx ^ sy) ^ sx == sy) by (bit_vector);
    }
}

/// The Frobenius shuffle is the 64th squaring, `a^(2^64)`, by Fermat in `K`.
pub proof fn lemma_e_frobenius(a: F192)
    ensures
        e_frobenius(a) == e_sq_iter(a, 64),
        e_frobenius(a) == e_pow(a, pow2(64)),
{
    lemma_e_sq_iter_shape(a, 64);
    lemma_k_fermat(a.c0);
    lemma_k_fermat(a.c1);
    lemma_k_fermat(a.c2);
    lemma_e_sq_iter_pow(a, 64);
}

/// The embedding of `K` is multiplicative.
pub proof fn lemma_e_from_k_mul(x: u64, y: u64)
    ensures
        e_mul(e_from_k(x), e_from_k(y)) == e_from_k(k_mul(x, y)),
{
    lemma_k_mul_zero(x);
    lemma_k_mul_zero(y);
    lemma_k_mul_zero(0);
    let p = k_mul(x, y);
    assert(p ^ (0u64 ^ 0u64) == p && (0u64 ^ 0u64) ^ (0u64 ^ 0u64) ^ 0u64 == 0u64 && (0u64 ^ 0u64 ^ 0u64)
        ^ 0u64 == 0u64) by (bit_vector);
}

pub proof fn lemma_e_from_k_pow(x: u64, n: nat)
    ensures
        e_from_k(k_pow(x, n)) == e_pow(e_from_k(x), n),
    decreases n,
{
    if n > 0 {
        lemma_e_from_k_pow(x, (n - 1) as nat);
        lemma_e_from_k_mul(k_pow(x, (n - 1) as nat), x);
    }
}

/// The norm `a φ(a) φ²(a) = a^(1 + q + q^2)`, `q = 2^64`, lies in `K`: it is fixed by the Frobenius.
pub proof fn lemma_norm(a: F192)
    ensures
        ({
            let m = e_mul(e_frobenius(a), e_frobenius(e_frobenius(a)));
            let q = pow2(64);
            &&& m == e_pow(a, q + q * q)
            &&& e_mul(a, m) == e_pow(a, 1 + q + q * q)
            &&& e_mul(a, m).c1 == 0
            &&& e_mul(a, m).c2 == 0
        }),
{
    let q = pow2(64);
    let fa = e_frobenius(a);
    lemma_e_frobenius(a);
    lemma_e_frobenius(fa);
    lemma_e_pow_mul(a, q, q);
    lemma_e_pow_add(a, q, q * q);
    let m = e_mul(fa, e_frobenius(fa));
    lemma_e_pow_one(a);
    lemma_e_pow_add(a, 1, q + q * q);
    assert(1 + (q + q * q) == 1 + q + q * q);
    let norm = e_mul(a, m);
    // φ(norm) = a^(q + q^2 + q^3), and a^(q^3) = φ³(a) = a.
    lemma_e_frobenius(norm);
    lemma_e_pow_mul(a, 1 + q + q * q, q);
    lemma_e_frobenius(e_frobenius(fa));
    lemma_e_pow_mul(a, q * q, q);
    assert(e_frobenius(e_frobenius(fa)) == a) by {
        let (x1, x2) = (a.c1, a.c2);
        assert(x2 ^ (x1 ^ x2) == x1 && (x1 ^ x2) ^ (x2 ^ (x1 ^ x2)) == x2) by (bit_vector);
    }
    lemma_e_pow_add(a, q + q * q, q * q * q);
    assert((1 + q + q * q) * q == (q + q * q) + q * q * q) by (nonlinear_arith);
    lemma_e_mul_comm(m, a);
    let (n1, n2) = (norm.c1, norm.c2);
    assert(n2 == n1 && (n1 ^ n2) == n2 ==> n1 == 0 && n2 == 0) by (bit_vector);
}

/// `m N^(q-2) = a^(q^3 - 2)`, the exponent bookkeeping of `F192::inv`.
pub proof fn lemma_inv_exponent(a: F192)
    ensures
        ({
            let m = e_mul(e_frobenius(a), e_frobenius(e_frobenius(a)));
            let norm = e_mul(a, m);
            e_mul(m, e_from_k(k_pow(norm.c0, (pow2(64) - 2) as nat))) == e_pow(a, (pow2(192) - 2) as nat)
        }),
{
    let q = pow2(64);
    lemma2_to64();
    lemma_pow2_adds(64, 64);
    lemma_pow2_adds(128, 64);
    lemma_norm(a);
    let m = e_mul(e_frobenius(a), e_frobenius(e_frobenius(a)));
    let norm = e_mul(a, m);
    assert(e_from_k(norm.c0) == norm);
    lemma_e_from_k_pow(norm.c0, (q - 2) as nat);
    lemma_e_pow_mul(a, 1 + q + q * q, (q - 2) as nat);
    lemma_e_pow_add(a, q + q * q, ((1 + q + q * q) * (q - 2)) as nat);
    assert(pow2(192) == q * q * q);
    assert((q + q * q) + (1 + q + q * q) * (q - 2) == q * q * q - 2) by (nonlinear_arith);
}

// ---------------------------------------------------------------------------------------------
// E is a field: the inverse is an inverse
// ---------------------------------------------------------------------------------------------
/// The only idempotents of `E` are 0 and 1.
pub proof fn lemma_e_idempotent(e: F192)
    requires
        e_mul(e, e) == e,
    ensures
        e == F192::ZERO || e == F192::ONE,
{
    lemma_square_spec(e);
    lemma_k_idempotent(e.c0);
    lemma_k_square(e.c1);
    lemma_k_square(e.c2);
    let (c1, c2) = (e.c1, e.c2);
    assert(reduce_formula(spread(c2)) == c1 && reduce_formula(spread(c1)) ^ reduce_formula(spread(c2)) == c2
        ==> c1 == 0 && c2 == 0) by (bit_vector);
}

pub proof fn lemma_e_pow_zero(n: nat)
    requires
        n > 0,
    ensures
        e_pow(F192::ZERO, n) == F192::ZERO,
{
    let p = e_pow(F192::ZERO, (n - 1) as nat);
    lemma_k_mul_zero(p.c0);
    lemma_k_mul_zero(p.c1);
    lemma_k_mul_zero(p.c2);
    assert(0u64 ^ (0u64 ^ 0u64) == 0u64 && (0u64 ^ 0u64) ^ (0u64 ^ 0u64) ^ 0u64 == 0u64 && (0u64 ^ 0u64 ^ 0u64)
        ^ 0u64 == 0u64) by (bit_vector);
}

/// `a^(2^192 - 2)` is the inverse of every nonzero `a` of `E`, and zero's image is zero.
pub proof fn lemma_e_inverse(a: F192)
    ensures
        a != F192::ZERO ==> e_mul(a, e_pow(a, (pow2(192) - 2) as nat)) == F192::ONE,
        a == F192::ZERO ==> e_pow(a, (pow2(192) - 2) as nat) == F192::ZERO,
{
    lemma2_to64();
    lemma_pow2_adds(64, 64);
    lemma_pow2_adds(128, 64);
    let q = pow2(64);
    let big = pow2(192);
    assert(big == q * q * q);
    let w = e_pow(a, (big - 2) as nat);
    let u = e_pow(a, (big - 1) as nat);
    if a == F192::ZERO {
        lemma_e_pow_zero((big - 2) as nat);
    } else {
        assert(u == e_mul(w, a));
        lemma_e_mul_comm(w, a);
        // a^(q^3) = φ³(a) = a.
        let fa = e_frobenius(a);
        lemma_e_frobenius(a);
        lemma_e_frobenius(fa);
        lemma_e_frobenius(e_frobenius(fa));
        lemma_e_pow_mul(a, q, q);
        lemma_e_pow_mul(a, q * q, q);
        assert(e_frobenius(e_frobenius(fa)) == a) by {
            let (x1, x2) = (a.c1, a.c2);
            assert(x2 ^ (x1 ^ x2) == x1 && (x1 ^ x2) ^ (x2 ^ (x1 ^ x2)) == x2) by (bit_vector);
        }
        assert(e_pow(a, big) == a);
        // u^2 = u, so u is 0 or 1; u = 0 would give a = 0.
        lemma_e_pow_add(a, (big - 1) as nat, (big - 1) as nat);
        lemma_e_pow_add(a, big, (big - 2) as nat);
        assert((big - 1) as nat + (big - 1) as nat == big + (big - 2) as nat);
        lemma_e_idempotent(u);
        lemma_e_pow_add(a, (big - 1) as nat, 1);
        lemma_e_pow_one(a);
        assert((big - 1) as nat + 1 == big);
        if u == F192::ZERO {
            lemma_k_mul_zero(a.c0);
            lemma_k_mul_zero(a.c1);
            lemma_k_mul_zero(a.c2);
            assert(0u64 ^ (0u64 ^ 0u64) == 0u64 && (0u64 ^ 0u64) ^ (0u64 ^ 0u64) ^ 0u64 == 0u64 && (0u64 ^ 0u64
                ^ 0u64) ^ 0u64 == 0u64) by (bit_vector);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Executable code: the portable paths
// ---------------------------------------------------------------------------------------------
/// An element `c0 + c1*y + c2*y^2`; bit `i` of each coefficient is its coefficient of `x^i`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct F192 {
    /// The coefficient of `y^0`.
    pub c0: u64,
    /// The coefficient of `y^1`.
    pub c1: u64,
    /// The coefficient of `y^2`.
    pub c2: u64,
}

impl F192 {
    pub const ZERO: Self = Self { c0: 0, c1: 0, c2: 0 };

    pub const ONE: Self = Self { c0: 1, c1: 0, c2: 0 };

    /// The element `y` (root of y^3 + y + 1 over the base field).
    pub const Y: Self = Self { c0: 0, c1: 1, c2: 0 };

    #[inline]
    pub const fn new(c0: u64, c1: u64, c2: u64) -> (r: Self)
        ensures
            r == (F192 { c0, c1, c2 }),
    {
        Self { c0, c1, c2 }
    }

    #[inline]
    pub const fn is_zero(self) -> (r: bool)
        ensures
            r == (self == F192::ZERO),
    {
        self.c0 == 0 && self.c1 == 0 && self.c2 == 0
    }

    /// Product without the base-field reduction, for XOR accumulation.
    #[inline]
    pub fn mul_unreduced(self, rhs: Self) -> (r: F192Unreduced)
        ensures
            e_value(r) == e_mul(self, rhs),
    {
        software::mul_unreduced(self, rhs)
    }

    /// Mixed product by a base-field scalar.
    ///
    /// The scalar has no `y` component, so the three coefficients multiply independently in `K`.
    #[inline]
    pub fn mul_base(self, k: F64) -> (r: Self)
        ensures
            r == e_mul(self, e_from_k(k.0)),
            r == (F192 { c0: k_mul(self.c0, k.0), c1: k_mul(self.c1, k.0), c2: k_mul(self.c2, k.0) }),
    {
        self.mul_base_unreduced(k).reduce()
    }

    /// Mixed product by a base-field scalar without the reduction, for XOR accumulation.
    #[inline]
    pub fn mul_base_unreduced(self, k: F64) -> (r: F192Unreduced)
        ensures
            e_value(r) == e_mul(self, e_from_k(k.0)),
            e_value(r) == (F192 {
                c0: k_mul(self.c0, k.0),
                c1: k_mul(self.c1, k.0),
                c2: k_mul(self.c2, k.0),
            }),
    {
        let (w0, w1, w2) = (mul_wide(self.c0, k.0), mul_wide(self.c1, k.0), mul_wide(self.c2, k.0));
        proof {
            lemma_u_from_wide(w0, w1, w2);
            lemma_mul_base_spec(self, k.0);
        }
        F192Unreduced::from_wide([w0, w1, w2])
    }

    /// Squaring, with 3 base-field squarings instead of 6 products.
    ///
    /// Cross terms vanish in characteristic 2:
    ///
    /// ```text
    ///     (c0 + c1*y + c2*y^2)^2 = c0^2 + c1^2*y^2 + c2^2*y^4
    ///                            = c0^2 + c2^2*y + (c1^2 + c2^2)*y^2     (y^4 = y^2 + y)
    /// ```
    #[inline]
    pub fn square(self) -> (r: Self)
        ensures
            r == e_mul(self, self),
    {
        // Square each coefficient as a 128-bit polynomial.
        let (s0, s1, s2) = (square_wide(self.c0), square_wide(self.c1), square_wide(self.c2));
        proof {
            lemma_u_from_wide(s0, s2, s1 ^ s2);
            lemma_k_mod_xor(s1, s2);
            lemma_square_spec(self);
        }
        // Fold y^4 back onto y^2 and y, then reduce each coefficient once.
        F192Unreduced::from_wide([s0, s2, s1 ^ s2]).reduce()
    }

    /// The Frobenius `self^(2^64)`, as the coefficient shuffle `c0 + c2·y + (c1 + c2)·y²`.
    #[inline]
    ///
    /// `r == e_pow(self, 2^64)` is [`lemma_e_frobenius`].
    pub const fn frobenius(self) -> (r: Self)
        ensures
            r == e_frobenius(self),
    {
        Self { c0: self.c0, c1: self.c2, c2: self.c1 ^ self.c2 }
    }

    /// Multiplicative inverse: `self^(2^192 − 2)`. `ZERO.inv() == ZERO`.
    ///
    /// Via the norm to the base field. With `φ` the Frobenius and
    /// `m = φ(self)·φ²(self)`, the product `self·m` is the norm `N(self) ∈ K`,
    /// so `self⁻¹ = m·N(self)⁻¹` needs two extension multiplies, one base-field
    /// inverse and one base-field scaling.
    ///
    /// Production checks `N(self) ∈ K` with a `debug_assert!`; here it is proven ([`lemma_norm`]).
    pub fn inv(self) -> (r: Self)
        ensures
            r == e_pow(self, (pow2(192) - 2) as nat),
            self != F192::ZERO ==> e_mul(self, r) == F192::ONE,
            self == F192::ZERO ==> r == F192::ZERO,
    {
        proof {
            lemma_e_inverse(self);
        }
        let m = self.frobenius() * self.frobenius().frobenius();
        let norm = self * m;
        proof {
            lemma_norm(self);
            assert(norm.c1 == 0 && norm.c2 == 0);
            lemma_inv_exponent(self);
        }
        m.mul_base(F64(norm.c0).inv())
    }
}

/// The mixed product is the product by an element of `K`.
pub proof fn lemma_mul_base_spec(a: F192, k: u64)
    ensures
        e_mul(a, e_from_k(k)) == (F192 { c0: k_mul(a.c0, k), c1: k_mul(a.c1, k), c2: k_mul(a.c2, k) }),
{
    lemma_k_mul_zero(a.c0);
    lemma_k_mul_zero(a.c1);
    lemma_k_mul_zero(a.c2);
    let (x0, x1, x2) = (k_mul(a.c0, k), k_mul(a.c1, k), k_mul(a.c2, k));
    assert(x0 ^ (0u64 ^ 0u64) == x0 && (0u64 ^ x1) ^ (0u64 ^ 0u64) ^ 0u64 == x1 && (0u64 ^ 0u64 ^ x2) ^ 0u64
        == x2) by (bit_vector);
}

/// Squaring in `E`: the cross terms cancel.
pub proof fn lemma_square_spec(a: F192)
    ensures
        e_mul(a, a) == (F192 {
            c0: k_mul(a.c0, a.c0),
            c1: k_mul(a.c2, a.c2),
            c2: k_mul(a.c1, a.c1) ^ k_mul(a.c2, a.c2),
        }),
{
    lemma_k_mul_comm(a.c0, a.c1);
    lemma_k_mul_comm(a.c0, a.c2);
    lemma_k_mul_comm(a.c1, a.c2);
    let (s0, s1, s2) = (k_mul(a.c0, a.c0), k_mul(a.c1, a.c1), k_mul(a.c2, a.c2));
    let (x01, x02, x12) = (k_mul(a.c0, a.c1), k_mul(a.c0, a.c2), k_mul(a.c1, a.c2));
    assert(s0 ^ (x12 ^ x12) == s0 && (x01 ^ x01) ^ (x12 ^ x12) ^ s2 == s2 && (x02 ^ s1 ^ x02) ^ s2 == s1 ^ s2)
        by (bit_vector);
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl for F192 {
    open spec fn obeys_add_spec() -> bool {
        true
    }

    open spec fn add_req(self, rhs: F192) -> bool {
        true
    }

    open spec fn add_spec(self, rhs: F192) -> F192 {
        e_add(self, rhs)
    }
}

impl Add for F192 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> (r: Self)
        ensures
            r == e_add(self, rhs),
    {
        Self { c0: self.c0 ^ rhs.c0, c1: self.c1 ^ rhs.c1, c2: self.c2 ^ rhs.c2 }
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl for F192 {
    open spec fn obeys_mul_spec() -> bool {
        true
    }

    open spec fn mul_req(self, rhs: F192) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: F192) -> F192 {
        e_mul(self, rhs)
    }
}

impl Mul for F192 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> (r: Self)
        ensures
            r == e_mul(self, rhs),
    {
        self.mul_unreduced(rhs).reduce()
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddAssignSpecImpl for F192 {
    open spec fn obeys_add_assign_spec() -> bool {
        true
    }

    open spec fn add_assign_req(&self, rhs: F192) -> bool {
        true
    }

    open spec fn add_assign_spec(&self, rhs: F192) -> &F192 {
        &e_add(*self, rhs)
    }
}

impl AddAssign for F192 {
    #[inline]
    fn add_assign(&mut self, rhs: Self)
        ensures
            *final(self) == e_add(*old(self), rhs),
    {
        self.c0 ^= rhs.c0;
        self.c1 ^= rhs.c1;
        self.c2 ^= rhs.c2;
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulAssignSpecImpl for F192 {
    open spec fn obeys_mul_assign_spec() -> bool {
        true
    }

    open spec fn mul_assign_req(&self, rhs: F192) -> bool {
        true
    }

    open spec fn mul_assign_spec(&self, rhs: F192) -> &F192 {
        &e_mul(*self, rhs)
    }
}

impl MulAssign for F192 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self)
        ensures
            *final(self) == e_mul(*old(self), rhs),
    {
        *self = *self * rhs;
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<F64> for F192 {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(k: F64) -> F192 {
        e_from_k(k.0)
    }
}

impl From<F64> for F192 {
    #[inline]
    fn from(k: F64) -> Self {
        Self { c0: k.0, c1: 0, c2: 0 }
    }
}

/// An F192 value whose coefficients are not yet reduced modulo the base polynomial.
///
/// Coefficient `k` is the 128-bit carry-less polynomial multiplying `y^k`, for `k < 3`.
/// Products land here already folded by `y^3 = y + 1`, so a sum of them is a plain XOR.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F192Unreduced {
    /// The 128-bit coefficients of `y^0`, `y^1`, `y^2`, each as its `[low, high]` words.
    pub coeffs: [[u64; 2]; 3],
}

impl F192Unreduced {
    pub const ZERO: Self = Self { coeffs: [[0, 0], [0, 0], [0, 0]] };

    /// Build from three 128-bit coefficients.
    #[inline]
    pub fn from_wide(coeffs: [u128; 3]) -> (r: Self)
        ensures
            r == u_from_wide(coeffs[0], coeffs[1], coeffs[2]),
    {
        Self {
            coeffs: [
                [coeffs[0] as u64, (coeffs[0] >> 64) as u64],
                [coeffs[1] as u64, (coeffs[1] >> 64) as u64],
                [coeffs[2] as u64, (coeffs[2] >> 64) as u64],
            ],
        }
    }

    /// Reduce each coefficient modulo the base polynomial.
    #[inline]
    pub fn reduce(self) -> (r: F192)
        ensures
            r == e_value(self),
    {
        // Production maps this over the three coefficients.
        let reduce_one = |w: [u64; 2]| -> (r: u64)
            ensures
                r == k_mod(wide(w)),
            { reduce(u128::from(w[1]) << 64 | u128::from(w[0])) };
        let (c0, c1, c2) = (reduce_one(self.coeffs[0]), reduce_one(self.coeffs[1]), reduce_one(self.coeffs[2]));
        F192 { c0, c1, c2 }
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<F192> for F192Unreduced {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(e: F192) -> F192Unreduced {
        F192Unreduced { coeffs: [[e.c0, 0], [e.c1, 0], [e.c2, 0]] }
    }
}

impl From<F192> for F192Unreduced {
    /// Embed a reduced element: each coefficient is its own 128-bit polynomial.
    #[inline]
    fn from(e: F192) -> Self {
        Self { coeffs: [[e.c0, 0], [e.c1, 0], [e.c2, 0]] }
    }
}

/// Embedding a reduced element and reducing it gives the element back.
pub proof fn lemma_from_f192(e: F192)
    ensures
        e_value(F192Unreduced { coeffs: [[e.c0, 0], [e.c1, 0], [e.c2, 0]] }) == e,
{
    assert(wide([e.c0, 0]) == e.c0 as u128 && (e.c0 as u128) >> 64u128 == 0) by {
        let c = e.c0;
        assert((((0u64 as u128) << 64u128) | (c as u128)) == c as u128 && (c as u128) >> 64u128 == 0) by (bit_vector);
    }
    assert(wide([e.c1, 0]) == e.c1 as u128 && (e.c1 as u128) >> 64u128 == 0) by {
        let c = e.c1;
        assert((((0u64 as u128) << 64u128) | (c as u128)) == c as u128 && (c as u128) >> 64u128 == 0) by (bit_vector);
    }
    assert(wide([e.c2, 0]) == e.c2 as u128 && (e.c2 as u128) >> 64u128 == 0) by {
        let c = e.c2;
        assert((((0u64 as u128) << 64u128) | (c as u128)) == c as u128 && (c as u128) >> 64u128 == 0) by (bit_vector);
    }
    lemma_k_mod_small(e.c0 as u128);
    lemma_k_mod_small(e.c1 as u128);
    lemma_k_mod_small(e.c2 as u128);
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::BitXorSpecImpl for F192Unreduced {
    open spec fn obeys_bitxor_spec() -> bool {
        true
    }

    open spec fn bitxor_req(self, rhs: F192Unreduced) -> bool {
        true
    }

    open spec fn bitxor_spec(self, rhs: F192Unreduced) -> F192Unreduced {
        u_xor(self, rhs)
    }
}

impl BitXor for F192Unreduced {
    type Output = Self;

    #[inline]
    /// Production takes `mut self`, which Verus does not accept; the copy rebinds it.
    fn bitxor(self, rhs: Self) -> (r: Self)
        ensures
            r == u_xor(self, rhs),
            e_value(r) == e_add(e_value(self), e_value(rhs)),
    {
        proof {
            lemma_e_value_xor(self, rhs);
        }
        let mut s = self;
        s ^= rhs;
        s
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::BitXorAssignSpecImpl for F192Unreduced {
    open spec fn obeys_bitxor_assign_spec() -> bool {
        true
    }

    open spec fn bitxor_assign_req(&self, rhs: F192Unreduced) -> bool {
        true
    }

    open spec fn bitxor_assign_spec(&self, rhs: F192Unreduced) -> &F192Unreduced {
        &u_xor(*self, rhs)
    }
}

impl BitXorAssign for F192Unreduced {
    /// Production: one XOR per word of the flattened coefficients.
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self)
        ensures
            *final(self) == u_xor(*old(self), rhs),
    {
        let mut k = 0;
        while k < 3
            invariant
                0 <= k <= 3,
                forall|i: int| 0 <= i < k ==> #[trigger] self.coeffs[i] == u_xor(*old(self), rhs).coeffs[i],
                forall|i: int| k <= i < 3 ==> #[trigger] self.coeffs[i] == old(self).coeffs[i],
            decreases 3 - k,
        {
            let mut row = self.coeffs[k];
            row[0] ^= rhs.coeffs[k][0];
            row[1] ^= rhs.coeffs[k][1];
            self.coeffs[k] = row;
            k += 1;
        }
        assert(self.coeffs =~= u_xor(*old(self), rhs).coeffs);
    }
}

// Batched products: the portable arms.
/// Two independent products.
#[inline(always)]
pub fn mul2(a: [F192; 2], b: [F192; 2]) -> (r: [F192; 2])
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] r[i] == e_mul(a[i], b[i]),
{
    [a[0] * b[0], a[1] * b[1]]
}

/// Four independent products.
#[inline(always)]
pub fn mul4(a: [F192; 4], b: [F192; 4]) -> (r: [F192; 4])
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] r[i] == e_mul(a[i], b[i]),
{
    let lo = mul2([a[0], a[1]], [b[0], b[1]]);
    let hi = mul2([a[2], a[3]], [b[2], b[3]]);
    [lo[0], lo[1], hi[0], hi[1]]
}

/// Four independent products without the reduction, for a caller XOR-accumulating many products.
///
/// Production builds the array with `std::array::from_fn`.
#[inline(always)]
pub fn mul_unreduced4(a: [F192; 4], b: [F192; 4]) -> (r: [F192Unreduced; 4])
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] e_value(r[i]) == e_mul(a[i], b[i]),
{
    [a[0].mul_unreduced(b[0]), a[1].mul_unreduced(b[1]), a[2].mul_unreduced(b[2]), a[3].mul_unreduced(b[3])]
}

/// Eight mixed products `t * k[i]` by one shared `E` scalar.
///
/// Production maps `t.mul_base` over `k`.
#[inline(always)]
pub fn mul_base8(t: F192, k: [F64; 8]) -> (r: [F192; 8])
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] r[i] == e_mul(t, e_from_k(k[i].0)),
{
    [
        t.mul_base(k[0]),
        t.mul_base(k[1]),
        t.mul_base(k[2]),
        t.mul_base(k[3]),
        t.mul_base(k[4]),
        t.mul_base(k[5]),
        t.mul_base(k[6]),
        t.mul_base(k[7]),
    ]
}

/// Eight `E` weights, laid out once for [`dot_base`].
///
/// ```text
///     lo  lane j = [w_2j.c0,   w_2j.c1  ]
///     hi  lane j = [w_2j+1.c0, w_2j+1.c1]
///     c2  lane j = [w_2j.c2,   w_2j+1.c2]
/// ```
#[derive(Clone, Copy, Debug, Default)]
#[repr(C, align(64))]
pub struct Weights8 {
    pub lo: [u64; 8],
    pub hi: [u64; 8],
    pub c2: [u64; 8],
}

/// Weight `i` as [`Weights8::get`] reads it.
pub open spec fn w8_get(w: Weights8, i: int) -> F192 {
    let j = i / 2;
    let pair = if i % 2 == 0 {
        w.lo
    } else {
        w.hi
    };
    F192 { c0: pair[2 * j], c1: pair[2 * j + 1], c2: w.c2[2 * j + i % 2] }
}

impl Weights8 {
    /// Pack eight weights.
    ///
    /// Production starts from `Self::default()` and copies two words at a time with `copy_from_slice`.
    pub fn new(w: &[F192; 8]) -> (out: Self)
        ensures
            forall|i: int| 0 <= i < 8 ==> #[trigger] w8_get(out, i) == w[i],
    {
        let mut out = Self { lo: [0, 0, 0, 0, 0, 0, 0, 0], hi: [0, 0, 0, 0, 0, 0, 0, 0], c2: [0, 0, 0, 0, 0, 0, 0, 0] };
        for j in 0..4usize
            invariant
                forall|i: int| 0 <= i < 2 * j ==> #[trigger] w8_get(out, i) == w[i],
        {
            let (e, o) = (w[2 * j], w[2 * j + 1]);
            let ghost before = out;
            out.lo[2 * j] = e.c0;
            out.lo[2 * j + 1] = e.c1;
            out.hi[2 * j] = o.c0;
            out.hi[2 * j + 1] = o.c1;
            out.c2[2 * j] = e.c2;
            out.c2[2 * j + 1] = o.c2;
            assert forall|i: int| 0 <= i < 2 * j + 2 implies #[trigger] w8_get(out, i) == w[i] by {
                if i >= 2 * j {
                    assert(i / 2 == j);
                } else {
                    assert(i / 2 < j);
                    assert(2 * (i / 2) + 1 < 2 * j && 2 * (i / 2) + i % 2 < 2 * j);
                    assert(w8_get(out, i) == w8_get(before, i));
                }
            }
        }
        out
    }

    /// Weight `i`, unpacked.
    #[inline]
    pub const fn get(&self, i: usize) -> (r: F192)
        requires
            i < 8,
        ensures
            r == w8_get(*self, i as int),
    {
        let j = i / 2;
        let pair = if i % 2 == 0 { &self.lo } else { &self.hi };
        F192::new(pair[2 * j], pair[2 * j + 1], self.c2[2 * j + i % 2])
    }
}

/// `sum_{m < n} w_m * k_m`, weight `m` being `w8_get(w[m / 8], m % 8)`.
pub open spec fn dot_spec(w: Seq<Weights8>, k: Seq<F64>, n: nat) -> F192
    decreases n,
{
    if n == 0 {
        F192::ZERO
    } else {
        let m = (n - 1) as int;
        e_add(dot_spec(w, k, (n - 1) as nat), e_mul(w8_get(w[m / 8], m % 8), e_from_k(k[m].0)))
    }
}

/// The mixed inner product `sum_i w_i * k_i`, unreduced.
///
/// Production checks `k.len() == 8 * w.len()` with `assert_eq!` and folds over `as_chunks::<8>`.
#[inline]
pub fn dot_base(w: &[Weights8], k: &[F64]) -> (r: F192Unreduced)
    requires
        k.len() == 8 * w.len(),
    ensures
        e_value(r) == dot_spec(w@, k@, k.len() as nat),
{
    let mut acc = F192Unreduced::ZERO;
    proof {
        lemma_u_zero();
    }
    for c in 0..w.len()
        invariant
            k.len() == 8 * w.len(),
            e_value(acc) == dot_spec(w@, k@, (8 * c) as nat),
    {
        for i in 0..8usize
            invariant
                k.len() == 8 * w.len(),
                c < w.len(),
                e_value(acc) == dot_spec(w@, k@, (8 * c + i) as nat),
        {
            proof {
                assert((8 * c + i) / 8 == c && (8 * c + i) % 8 == i as int) by (nonlinear_arith)
                    requires
                        i < 8,
                ;
            }
            acc = acc ^ w[c].get(i).mul_base_unreduced(k[8 * c + i]);
        }
    }
    acc
}

pub mod software {
    use super::*;
    use crate::gf2_64::software::clmul;

    /// Schoolbook: nine base products into the five coefficients of y^0..y^4, then the y-fold.
    pub fn mul_unreduced(a: F192, b: F192) -> (r: F192Unreduced)
        ensures
            e_value(r) == e_mul(a, b),
    {
        let ghost (ga, gb) = (a, b);
        let (a, b) = ([a.c0, a.c1, a.c2], [b.c0, b.c1, b.c2]);
        let mut e = [0u128, 0, 0, 0, 0];
        // a_i * b_j lands on y^(i + j).
        for i in 0..3usize
            invariant
                e@ == sched(a@, b@, (3 * i) as nat),
        {
            for j in 0..3usize
                invariant
                    0 <= i < 3,
                    e@ == sched(a@, b@, (3 * i + j) as nat),
            {
                proof {
                    assert(((3 * i + j) / 3) as int == i && ((3 * i + j) % 3) as int == j);
                }
                e[i + j] ^= clmul(a[i], b[j]);
                proof {
                    assert(e@ =~= sched(a@, b@, (3 * i + j + 1) as nat));
                }
            }
        }
        proof {
            assert(a@ =~= seq![ga.c0, ga.c1, ga.c2]);
            assert(b@ =~= seq![gb.c0, gb.c1, gb.c2]);
            lemma_mul_unreduced_value(ga, gb);
        }
        // y^3 = y + 1 and y^4 = y^2 + y.
        F192Unreduced::from_wide([e[0] ^ e[3], e[1] ^ e[3] ^ e[4], e[2] ^ e[4]])
    }

    pub fn mul(a: F192, b: F192) -> (r: F192)
        ensures
            r == e_mul(a, b),
    {
        mul_unreduced(a, b).reduce()
    }
}

// ---------------------------------------------------------------------------------------------
// The x86 Karatsuba product, given the semantics of the carry-less multiply
// ---------------------------------------------------------------------------------------------
/// `x86_64::mul_unreduced` (six PCLMULQDQs, Karatsuba, then `fold`) yields the same three 128-bit
/// coefficients as the schoolbook product above, with each PCLMULQDQ computing [`clmul`]:
///
/// ```text
///     p0 = a0 b0, p1 = a1 b1, p2 = a2 b2, p01 = (a0+a1)(b0+b1), p02 = (a0+a2)(b0+b2), p12 = (a1+a2)(b1+b2)
///     d0 = p0 ^ p12 ^ p1 ^ p2,   d1 = p0 ^ p12 ^ p01,   d2 = p0 ^ p1 ^ p02
/// ```
pub proof fn lemma_karatsuba_fold(a: F192, b: F192)
    ensures
        ({
            let c = |x: u64, y: u64| clmul(x, y as u128);
            let (p0, p1, p2) = (c(a.c0, b.c0), c(a.c1, b.c1), c(a.c2, b.c2));
            let p01 = c(a.c0 ^ a.c1, b.c0 ^ b.c1);
            let p02 = c(a.c0 ^ a.c2, b.c0 ^ b.c2);
            let p12 = c(a.c1 ^ a.c2, b.c1 ^ b.c2);
            let q = p0 ^ p12;
            let e = sched(seq![a.c0, a.c1, a.c2], seq![b.c0, b.c1, b.c2], 9);
            &&& q ^ p1 ^ p2 == e[0] ^ e[3]
            &&& q ^ p01 == e[1] ^ e[3] ^ e[4]
            &&& p0 ^ p1 ^ p02 == e[2] ^ e[4]
        }),
{
    let (sa, sb) = (seq![a.c0, a.c1, a.c2], seq![b.c0, b.c1, b.c2]);
    lemma_sched_9(sa, sb);
    // Expand each Karatsuba product bilinearly into the nine schoolbook products.
    assert forall|x1: u64, x2: u64, y1: u64, y2: u64|
        #[trigger] clmul(x1 ^ x2, (y1 ^ y2) as u128) == clmul(x1, y1 as u128) ^ clmul(x1, y2 as u128) ^ clmul(
            x2,
            y1 as u128,
        ) ^ clmul(x2, y2 as u128) by {
        assert((y1 ^ y2) as u128 == (y1 as u128) ^ (y2 as u128)) by (bit_vector);
        lemma_clmul_xor_left(x1, x2, (y1 ^ y2) as u128);
        lemma_clmul_xor_right(x1, y1 as u128, y2 as u128);
        lemma_clmul_xor_right(x2, y1 as u128, y2 as u128);
        let (a1, a2, b1, b2) = (clmul(x1, y1 as u128), clmul(x1, y2 as u128), clmul(x2, y1 as u128), clmul(
            x2,
            y2 as u128,
        ));
        assert((a1 ^ a2) ^ (b1 ^ b2) == a1 ^ a2 ^ b1 ^ b2) by (bit_vector);
    }
    let c = |x: u64, y: u64| clmul(x, y as u128);
    let (c00, c01, c02, c10, c11, c12, c20, c21, c22) = (
        c(a.c0, b.c0),
        c(a.c0, b.c1),
        c(a.c0, b.c2),
        c(a.c1, b.c0),
        c(a.c1, b.c1),
        c(a.c1, b.c2),
        c(a.c2, b.c0),
        c(a.c2, b.c1),
        c(a.c2, b.c2),
    );
    assert(c00 ^ (c11 ^ c12 ^ c21 ^ c22) ^ c11 ^ c22 == (0 ^ c00) ^ (0 ^ c12 ^ c21)) by (bit_vector);
    assert(c00 ^ (c11 ^ c12 ^ c21 ^ c22) ^ (c00 ^ c01 ^ c10 ^ c11) == (0 ^ c01 ^ c10) ^ (0 ^ c12 ^ c21) ^ (0
        ^ c22)) by (bit_vector);
    assert(c00 ^ c11 ^ (c00 ^ c02 ^ c20 ^ c22) == (0 ^ c02 ^ c11 ^ c20) ^ (0 ^ c22)) by (bit_vector);
}

} // verus!
