//! The additive NTT over `K = GF(2^64)` in the Lin-Chung-Han novel polynomial basis.
//!
//! The executable functions are the portable scalar parts of `crates/pcs/src/ntt/additive_ntt_f64.rs`,
//! copied with the same names and bodies where Verus accepts them; `tests/equivalence/ntt.rs` checks
//! the copies against production.
//!
//! Specification, following annex `d` of the leanVM document:
//!
//! - [`span`]: the subset sum `Σ_j bit_j(idx) · s[j]` of a sequence of field elements.
//! - [`subspace_poly`]: the unnormalized subspace polynomial `s_i`, by its recurrence
//!   `s_0(x) = x`, `s_i(x) = s_{i-1}(x) · (s_{i-1}(x) + s_{i-1}(b_{i-1}))`, evaluated in `K`.
//! - [`normalized_subspace_poly`]: `Ŵ_i(x) = s_i(x) · s_i(b_i)^(-1)`, with the inverse `y^(2^64 - 2)`.
//! - [`layer_map`]: one layer of butterflies on a buffer of interleaved lanes, by row index;
//!   [`forward_layers`] and [`inverse_layers`] compose them.
//! - [`novel_eval`]: the novel-basis polynomial `Σ_j a_j X_j(x)`, `X_j = Π_i Ŵ_i(x)^(bit_i(j))`, in its
//!   even-odd form; [`lemma_novel_eval_flat`] proves it equal to the flat sum [`novel_sum`].
//!
//! Main results: [`lemma_inverse_butterfly`], [`lemma_span_xor`], `twiddles_radix8`'s postcondition,
//! [`lemma_subspace_poly_additive`], [`lemma_twiddle_is_subspace_poly`], `generate_evals_from_subspace`'s
//! postcondition, `radix8_butterflies`' postcondition, [`lemma_inverse_after_forward`],
//! [`lemma_forward_evaluates`] and [`lemma_encode_evaluates`]. The last two hold for any basis whose table
//! rows start with one (`Ŵ_i(b_i) = 1`); [`lemma_standard_rows_start_with_one`] proves that for the standard
//! basis, so [`lemma_standard_forward_evaluates`] and [`lemma_standard_encode_evaluates`] state them for
//! `AdditiveNttF64::standard(dim)` without hypothesis.
//!
//! The parallel driver (`transform`, `gathered_pass`, `run_layers`, `fused_rows`, `replicate`,
//! `transpose_lane_major`) is not copied: it is out of scope. The SIMD butterflies `lane_butterflies` dispatches
//! to are in `crate::ntt_simd`.
// `global size_of usize` expands to a braced block.
#![allow(unused_braces)]

use crate::gf2_64::*;
use crate::ntt_simd::*;
use core::ops::{Add, AddAssign, Mul, MulAssign};
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

global size_of usize == 8;

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// Bit `j` of `idx`, zero past the word.
pub open spec fn idx_bit(idx: usize, j: nat) -> bool {
    j < 64 && (idx >> (j as usize)) & 1 == 1
}

/// `Σ_j bit_j(idx) · s[j]`: the XOR of the elements of `s` whose index is a set bit of `idx`.
pub open spec fn span(s: Seq<F64>, idx: usize) -> u64
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        span(s.drop_last(), idx) ^ (if idx_bit(idx, (s.len() - 1) as nat) {
            s.last().0
        } else {
            0
        })
    }
}

/// The unnormalized subspace polynomial `s_i` of the basis, evaluated at `x`:
/// `s_0(x) = x` and `s_i(x) = s_{i-1}(x) · (s_{i-1}(x) + s_{i-1}(b_{i-1}))`.
pub open spec fn subspace_poly(basis: Seq<F64>, i: nat, x: u64) -> u64
    decreases i,
{
    if i == 0 {
        x
    } else {
        let p = subspace_poly(basis, (i - 1) as nat, x);
        k_mul(p, p ^ subspace_poly(basis, (i - 1) as nat, basis[i - 1].0))
    }
}

/// The inverse in `K`, `y^(2^64 - 2)` (zero for zero), as `F64::inv` computes it.
pub open spec fn k_inv(y: u64) -> u64 {
    k_pow(y, (pow2(64) - 2) as nat)
}

/// The normalized subspace polynomial `Ŵ_i(x) = s_i(x) / s_i(b_i)`.
pub open spec fn normalized_subspace_poly(basis: Seq<F64>, i: nat, x: u64) -> u64 {
    k_mul(subspace_poly(basis, i, x), k_inv(subspace_poly(basis, i, basis[i as int].0)))
}

/// The standard basis `{1, x, x^2, ..., x^(dim-1)}` of the domain: `b_c = x^c`, bit `c` alone.
pub open spec fn standard_basis(dim: nat) -> Seq<F64> {
    Seq::new(dim, |c: int| F64(1u64 << (c as u64)))
}

/// The twiddle of one block at one layer, as read from the table `tab`: a subset sum of row
/// `L - layer - 1` past its first entry, `L` the number of rows.
pub open spec fn twiddle_spec(tab: Seq<Seq<F64>>, layer: nat, block: usize) -> u64 {
    span(tab[tab.len() - layer - 1].skip(1), block)
}

/// The forward butterfly's top output: `u + v t`.
pub open spec fn bf_top(u: u64, v: u64, t: u64) -> u64 {
    u ^ k_mul(v, t)
}

/// The forward butterfly's bottom output: `v + (u + v t)`.
pub open spec fn bf_bot(u: u64, v: u64, t: u64) -> u64 {
    v ^ bf_top(u, v, t)
}

/// The inverse butterfly's top output: `u + (v + u) t`.
pub open spec fn ibf_top(u: u64, v: u64, t: u64) -> u64 {
    u ^ k_mul(v ^ u, t)
}

/// The inverse butterfly's bottom output: `v + u`.
pub open spec fn ibf_bot(u: u64, v: u64, t: u64) -> u64 {
    v ^ u
}

// ---------------------------------------------------------------------------------------------
// Butterflies
// ---------------------------------------------------------------------------------------------
proof fn lemma_xor_facts(a: u64, b: u64, c: u64)
    ensures
        a ^ a == 0,
        a ^ 0 == a,
        0 ^ a == a,
        a ^ b == b ^ a,
        (a ^ b) ^ c == a ^ (b ^ c),
        (a ^ b) ^ b == a,
        (a ^ b) ^ a == b,
        a ^ (a ^ b) == b,
        b ^ (a ^ b) == a,
{
    assert(a ^ a == 0 && a ^ 0 == a && 0 ^ a == a && a ^ b == b ^ a && (a ^ b) ^ c == a ^ (b ^ c) && (a ^ b) ^ b == a
        && (a ^ b) ^ a == b && a ^ (a ^ b) == b && b ^ (a ^ b) == a) by (bit_vector);
}

/// The forward butterfly evaluates the line `u + v X` at `X = t` and `X = t + 1`.
pub proof fn lemma_butterfly_evaluates(u: u64, v: u64, t: u64)
    ensures
        bf_top(u, v, t) == u ^ k_mul(v, t),
        bf_bot(u, v, t) == u ^ k_mul(v, t ^ 1),
{
    lemma_k_mul_xor_right(v, t, 1);
    lemma_k_mul_one(v);
    let p = k_mul(v, t);
    assert(v ^ (u ^ p) == u ^ (p ^ v)) by (bit_vector);
}

/// The inverse butterfly of `inverse_transform` undoes the forward one, for every twiddle.
pub proof fn lemma_inverse_butterfly(u: u64, v: u64, t: u64)
    ensures
        ibf_top(bf_top(u, v, t), bf_bot(u, v, t), t) == u,
        ibf_bot(bf_top(u, v, t), bf_bot(u, v, t), t) == v,
        bf_top(ibf_top(u, v, t), ibf_bot(u, v, t), t) == u,
        bf_bot(ibf_top(u, v, t), ibf_bot(u, v, t), t) == v,
{
    let p = k_mul(v, t);
    let a = u ^ p;
    lemma_xor_facts(v, a, 0);
    lemma_xor_facts(u, p, 0);
    let q = k_mul(v ^ u, t);
    lemma_xor_facts(u, q, 0);
    lemma_xor_facts(v, u, 0);
    lemma_xor_facts(u ^ q, v ^ u, 0);
    assert((v ^ u) ^ (u ^ q) ^ (u ^ q) == v ^ u) by (bit_vector);
    assert((v ^ u) ^ (u ^ q) == v ^ q) by (bit_vector);
}

/// The transposed butterfly undoes the forward one with its rows swapped, input and output.
pub proof fn lemma_transposed_inverts_swapped(u: u64, v: u64, t: u64)
    ensures
        ({
            let (a, b) = (bf_top(u, v, t), bf_bot(u, v, t));
            let s = b ^ a;
            s == v && a ^ k_mul(s, t) == u
        }),
{
    let p = k_mul(v, t);
    lemma_xor_facts(u, p, 0);
    lemma_xor_facts(v, u ^ p, 0);
}

/// One lane's butterfly, forward or transposed.
#[inline(always)]
pub fn butterfly_one<const TRANSPOSED: bool>(u: &mut F64, v: &mut F64, t: F64)
    ensures
        TRANSPOSED ==> final(u).0 == old(u).0 ^ old(v).0 && final(v).0 == old(v).0 ^ k_mul(
            old(u).0 ^ old(v).0,
            t.0,
        ),
        !TRANSPOSED ==> final(u).0 == bf_top(old(u).0, old(v).0, t.0) && final(v).0 == bf_bot(
            old(u).0,
            old(v).0,
            t.0,
        ),
{
    if TRANSPOSED {
        let s = *u + *v;
        *u = s;
        *v += s * t;
    } else {
        *u += *v * t;
        *v += *u;
    }
}

// ---------------------------------------------------------------------------------------------
// Subset sums of the basis
// ---------------------------------------------------------------------------------------------
proof fn lemma_bit_xor(i: usize, j: usize, k: usize)
    requires
        k < 64,
    ensures
        ((i ^ j) >> k) & 1 == 1 <==> (((i >> k) & 1 == 1) != ((j >> k) & 1 == 1)),
{
    assert(((i ^ j) >> k) & 1 == 1 <==> (((i >> k) & 1 == 1) != ((j >> k) & 1 == 1))) by (bit_vector)
        requires
            k < 64,
    ;
}

proof fn lemma_xor_select(a: u64, b: u64, x: u64)
    ensures
        (a ^ b) ^ 0 == (a ^ 0) ^ (b ^ 0),
        (a ^ b) ^ x == (a ^ x) ^ (b ^ 0),
        (a ^ b) ^ x == (a ^ 0) ^ (b ^ x),
        (a ^ b) ^ 0 == (a ^ x) ^ (b ^ x),
{
    assert((a ^ b) ^ 0 == (a ^ 0) ^ (b ^ 0) && (a ^ b) ^ x == (a ^ x) ^ (b ^ 0) && (a ^ b) ^ x == (a ^ 0) ^ (b
        ^ x) && (a ^ b) ^ 0 == (a ^ x) ^ (b ^ x)) by (bit_vector);
}

/// The subset sum is F_2-linear in the index: `span(s, i ^ j) = span(s, i) + span(s, j)`.
pub proof fn lemma_span_xor(s: Seq<F64>, i: usize, j: usize)
    ensures
        span(s, i ^ j) == span(s, i) ^ span(s, j),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(0u64 ^ 0u64 == 0) by (bit_vector);
    } else {
        let d = s.drop_last();
        let k = (s.len() - 1) as nat;
        lemma_span_xor(d, i, j);
        if k < 64 {
            lemma_bit_xor(i, j, k as usize);
        }
        lemma_xor_select(span(d, i), span(d, j), s.last().0);
    }
}

/// The subset sum of the zero index is zero.
pub proof fn lemma_span_zero(s: Seq<F64>)
    ensures
        span(s, 0) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_span_zero(s.drop_last());
        let k = (s.len() - 1) as usize;
        assert((0usize >> k) & 1 == 0) by (bit_vector);
        assert(0u64 ^ 0u64 == 0) by (bit_vector);
    }
}

proof fn lemma_bit_double(b: usize, k: usize)
    requires
        b < 0x8000_0000_0000_0000usize,
        k < 63,
    ensures
        ((b * 2) as usize >> ((k + 1) as usize)) & 1 == (b >> k) & 1,
        ((b * 2 + 1) as usize >> ((k + 1) as usize)) & 1 == (b >> k) & 1,
        ((b * 2) as usize >> 0usize) & 1 == 0,
        ((b * 2 + 1) as usize >> 0usize) & 1 == 1,
{
    let b2 = (b * 2) as usize;
    let b21 = (b * 2 + 1) as usize;
    assert(b2 == b << 1usize && b21 == (b << 1usize) | 1) by (bit_vector)
        requires
            b < 0x8000_0000_0000_0000usize,
            b2 == b * 2,
            b21 == b * 2 + 1,
    ;
    assert(((b << 1usize) >> ((k + 1) as usize)) & 1 == (b >> k) & 1 && (((b << 1usize) | 1) >> ((k + 1) as usize))
        & 1 == (b >> k) & 1 && ((b << 1usize) >> 0usize) & 1 == 0 && (((b << 1usize) | 1) >> 0usize) & 1 == 1)
        by (bit_vector)
        requires
            k < 63,
    ;
}

/// Doubling the index shifts the subset sum by one element; the low bit selects the first element.
pub proof fn lemma_span_double(s: Seq<F64>, b: usize)
    requires
        1 <= s.len() <= 64,
        b < 0x8000_0000_0000_0000usize,
    ensures
        span(s, (b * 2) as usize) == span(s.skip(1), b),
        span(s, (b * 2 + 1) as usize) == s[0].0 ^ span(s.skip(1), b),
    decreases s.len(),
{
    let n = (s.len() - 1) as nat;
    let d = s.drop_last();
    if n == 0 {
        lemma_bit_double(b, 0);
        assert(span(d, (b * 2) as usize) == 0);
        assert(span(d, (b * 2 + 1) as usize) == 0);
        assert(span(s.skip(1), b) == 0);
        lemma_xor_facts(s[0].0, 0, 0);
        lemma_xor_facts(0, 0, 0);
        assert(span(s, (b * 2) as usize) == span(d, (b * 2) as usize) ^ 0);
    } else {
        lemma_span_double(d, b);
        lemma_bit_double(b, (n - 1) as usize);
        assert(s.skip(1).drop_last() =~= d.skip(1));
        assert(s.skip(1).last() == s.last());
        let sel = if idx_bit(b, (n - 1) as nat) {
            s.last().0
        } else {
            0
        };
        lemma_xor_facts(s[0].0, span(d.skip(1), b), sel);
        assert(span(s.skip(1), b) == span(d.skip(1), b) ^ sel);
        assert(span(s, (b * 2) as usize) == span(d, (b * 2) as usize) ^ sel);
    }
}

/// Index bits past `m` select nothing: a subset sum of an index below `2^m` reads only `s[..m]`.
pub proof fn lemma_span_low(s: Seq<F64>, b: usize, m: nat)
    requires
        m <= s.len(),
        b < pow2(m),
    ensures
        span(s, b) == span(s.take(m as int), b),
    decreases s.len(),
{
    if s.len() == m {
        assert(s.take(m as int) =~= s);
    } else {
        let k = (s.len() - 1) as nat;
        lemma_span_low(s.drop_last(), b, m);
        assert(s.drop_last().take(m as int) =~= s.take(m as int));
        if k < 64 {
            lemma_usize_shr_is_div(b, k as usize);
            if m < k {
                lemma_pow2_strictly_increases(m, k);
            }
            lemma_basic_div(b as int, pow2(k) as int);
            assert((0usize & 1) == 0) by (bit_vector);
        }
        lemma_xor_facts(span(s.drop_last(), b), 0, 0);
    }
}

/// `Σ_j bit_j(idx) · basis[j]`.
#[inline]
pub fn span_get(basis: &[F64], idx: usize) -> (r: F64)
    requires
        basis.len() <= 64,
    ensures
        r.0 == span(basis@, idx),
{
    let mut acc = F64::ZERO;
    for j in 0..basis.len()
        invariant
            basis.len() <= 64,
            acc.0 == span(basis@.take(j as int), idx),
    {
        let b = basis[j];
        assert(basis@.take(j + 1).drop_last() =~= basis@.take(j as int));
        proof {
            lemma_xor_facts(acc.0, 0, 0);
        }
        if (idx >> j) & 1 == 1 {
            acc += b;
        }
    }
    assert(basis@.take(basis.len() as int) =~= basis@);
    acc
}

// ---------------------------------------------------------------------------------------------
// Subspace polynomials
// ---------------------------------------------------------------------------------------------
/// `s_i` is F_2-linear: `s_i(x + y) = s_i(x) + s_i(y)`.
pub proof fn lemma_subspace_poly_additive(basis: Seq<F64>, i: nat, x: u64, y: u64)
    ensures
        subspace_poly(basis, i, x ^ y) == subspace_poly(basis, i, x) ^ subspace_poly(basis, i, y),
    decreases i,
{
    if i > 0 {
        let j = (i - 1) as nat;
        lemma_subspace_poly_additive(basis, j, x, y);
        let a = subspace_poly(basis, j, x);
        let b = subspace_poly(basis, j, y);
        let c = subspace_poly(basis, j, basis[j as int].0);
        // (a + b)(a + b + c) = a(a + c) + a b + b(b + c) + b a
        assert((a ^ b) ^ c == (a ^ c) ^ b && (a ^ b) ^ c == (b ^ c) ^ a) by (bit_vector);
        lemma_k_mul_xor_left(a, b, (a ^ b) ^ c);
        lemma_k_mul_xor_right(a, a ^ c, b);
        lemma_k_mul_xor_right(b, b ^ c, a);
        lemma_k_mul_comm(a, b);
        let (p, q, r) = (k_mul(a, a ^ c), k_mul(b, b ^ c), k_mul(a, b));
        assert((p ^ r) ^ (q ^ r) == p ^ q) by (bit_vector);
    }
}

/// `s_i(0) = 0`.
pub proof fn lemma_subspace_poly_zero(basis: Seq<F64>, i: nat)
    ensures
        subspace_poly(basis, i, 0) == 0,
{
    lemma_subspace_poly_additive(basis, i, 0, 0);
    let z = subspace_poly(basis, i, 0);
    assert(0u64 ^ 0u64 == 0u64 && z ^ z == 0) by (bit_vector);
}

/// `s_i` vanishes on the first `i` basis elements.
pub proof fn lemma_subspace_poly_vanishes(basis: Seq<F64>, i: nat, j: nat)
    requires
        j < i,
    ensures
        subspace_poly(basis, i, basis[j as int].0) == 0,
    decreases i,
{
    let x = basis[j as int].0;
    let p = subspace_poly(basis, (i - 1) as nat, x);
    let c = subspace_poly(basis, (i - 1) as nat, basis[i - 1].0);
    if j == i - 1 {
        lemma_xor_facts(p, 0, 0);
        lemma_k_mul_zero(p);
    } else {
        lemma_subspace_poly_vanishes(basis, (i - 1) as nat, j);
        lemma_k_mul_zero(p ^ c);
    }
}

/// So `s_i` vanishes on the whole span of the first `i` basis elements.
pub proof fn lemma_subspace_poly_vanishes_on_span(basis: Seq<F64>, i: nat, idx: usize)
    requires
        i <= basis.len(),
    ensures
        subspace_poly(basis, i, span(basis.take(i as int), idx)) == 0,
{
    lemma_subspace_poly_kills_prefix(basis, i, basis.take(i as int), idx);
}

proof fn lemma_subspace_poly_kills_prefix(basis: Seq<F64>, i: nat, s: Seq<F64>, idx: usize)
    requires
        s.len() <= i <= basis.len(),
        forall|j: int| 0 <= j < s.len() ==> s[j] == basis[j],
    ensures
        subspace_poly(basis, i, span(s, idx)) == 0,
    decreases s.len(),
{
    if s.len() == 0 {
        lemma_subspace_poly_zero(basis, i);
    } else {
        let d = s.drop_last();
        lemma_subspace_poly_kills_prefix(basis, i, d, idx);
        let sel = if idx_bit(idx, (s.len() - 1) as nat) {
            s.last().0
        } else {
            0
        };
        lemma_subspace_poly_additive(basis, i, span(d, idx), sel);
        if idx_bit(idx, (s.len() - 1) as nat) {
            lemma_subspace_poly_vanishes(basis, i, (s.len() - 1) as nat);
        } else {
            lemma_subspace_poly_zero(basis, i);
        }
        lemma_xor_facts(0, 0, 0);
    }
}

/// The normalized `Ŵ_i` is F_2-linear too.
pub proof fn lemma_normalized_additive(basis: Seq<F64>, i: nat, x: u64, y: u64)
    ensures
        normalized_subspace_poly(basis, i, x ^ y) == normalized_subspace_poly(basis, i, x)
            ^ normalized_subspace_poly(basis, i, y),
        normalized_subspace_poly(basis, i, 0) == 0,
{
    lemma_subspace_poly_additive(basis, i, x, y);
    let c = k_inv(subspace_poly(basis, i, basis[i as int].0));
    lemma_k_mul_xor_left(subspace_poly(basis, i, x), subspace_poly(basis, i, y), c);
    lemma_subspace_poly_zero(basis, i);
    lemma_k_mul_zero(c);
}

/// A subset sum of `Ŵ_i` values is `Ŵ_i` of the subset sum.
pub proof fn lemma_span_normalized(basis: Seq<F64>, i: nat, s: Seq<F64>, t: Seq<F64>, idx: usize)
    requires
        s.len() == t.len(),
        forall|j: int| 0 <= j < s.len() ==> s[j].0 == normalized_subspace_poly(basis, i, #[trigger] t[j].0),
    ensures
        span(s, idx) == normalized_subspace_poly(basis, i, span(t, idx)),
    decreases s.len(),
{
    lemma_normalized_additive(basis, i, 0, 0);
    if s.len() > 0 {
        lemma_span_normalized(basis, i, s.drop_last(), t.drop_last(), idx);
        let sel = if idx_bit(idx, (s.len() - 1) as nat) {
            t.last().0
        } else {
            0
        };
        lemma_normalized_additive(basis, i, span(t.drop_last(), idx), sel);
    }
}

// ---------------------------------------------------------------------------------------------
// The twiddle table
// ---------------------------------------------------------------------------------------------
/// Table of the normalized subspace polynomials at the basis.
///
/// - Row `i` holds `s_i(b_j)` for every basis element `b_j` with `j >= i`.
/// - Each row is scaled so that its first entry is one.
pub fn generate_evals_from_subspace(basis: &[F64]) -> (evals: Vec<Vec<F64>>)
    requires
        basis.len() >= 1,
    ensures
        evals.len() == basis.len(),
        forall|i: int| 0 <= i < evals.len() ==> (#[trigger] evals@[i])@.len() == basis.len() - i,
        forall|i: int, k: int|
            0 <= i < evals.len() && 0 <= k < evals@[i]@.len() ==> (#[trigger] evals@[i]@[k]).0
                == normalized_subspace_poly(basis@, i as nat, basis@[i + k].0),
{
    let l = basis.len();
    let mut evals: Vec<Vec<F64>> = Vec::with_capacity(l);
    evals.push(vstd::slice::slice_to_vec(basis));
    for i in 1..l
        invariant
            l == basis.len(),
            evals.len() == i,
            forall|i0: int| 0 <= i0 < i ==> (#[trigger] evals@[i0])@.len() == l - i0,
            forall|i0: int, k: int|
                0 <= i0 < i && 0 <= k < l - i0 ==> (#[trigger] evals@[i0]@[k]).0 == subspace_poly(
                    basis@,
                    i0 as nat,
                    basis@[i0 + k].0,
                ),
    {
        assert(evals@[i - 1]@.len() == l - (i - 1));
        let mut row: Vec<F64> = Vec::with_capacity(l - i);
        for k in 1..evals[i - 1].len()
            invariant
                l == basis.len(),
                1 <= i < l,
                evals.len() == i,
                evals@[i - 1]@.len() == l - (i - 1),
                forall|k0: int|
                    0 <= k0 < l - (i - 1) ==> (#[trigger] evals@[i - 1]@[k0]).0 == subspace_poly(
                        basis@,
                        (i - 1) as nat,
                        basis@[i - 1 + k0].0,
                    ),
                row.len() == k - 1,
                forall|k0: int|
                    0 <= k0 < k - 1 ==> (#[trigger] row@[k0]).0 == subspace_poly(basis@, i as nat, basis@[i + k0].0),
        {
            let val = evals[i - 1][k] * (evals[i - 1][k] + evals[i - 1][0]);
            row.push(val);
        }
        evals.push(row);
        assert(evals@[i as int] == row);
    }
    // Rewritten from `for row in evals.iter_mut() { .. for v in row.iter_mut() { .. } }`.
    for i in 0..l
        invariant
            l == basis.len(),
            evals.len() == l,
            forall|i0: int| 0 <= i0 < l ==> (#[trigger] evals@[i0])@.len() == l - i0,
            forall|i0: int, k: int|
                0 <= i0 < l && 0 <= k < l - i0 ==> (#[trigger] evals@[i0]@[k]).0 == if i0 < i {
                    normalized_subspace_poly(basis@, i0 as nat, basis@[i0 + k].0)
                } else {
                    subspace_poly(basis@, i0 as nat, basis@[i0 + k].0)
                },
    {
        let ghost pre = evals@;
        assert(evals@[i as int]@.len() == l - i);
        let inv = evals[i][0].inv();
        for k in 0..l - i
            invariant
                l == basis.len(),
                0 <= i < l,
                evals.len() == l,
                pre.len() == l,
                inv.0 == k_inv(subspace_poly(basis@, i as nat, basis@[i as int].0)),
                forall|i0: int| 0 <= i0 < l && i0 != i ==> #[trigger] evals@[i0] == pre[i0],
                evals@[i as int]@.len() == l - i,
                forall|k0: int|
                    0 <= k0 < l - i ==> (#[trigger] evals@[i as int]@[k0]).0 == if k0 < k {
                        normalized_subspace_poly(basis@, i as nat, basis@[i + k0].0)
                    } else {
                        subspace_poly(basis@, i as nat, basis@[i + k0].0)
                    },
        {
            evals[i][k] *= inv;
        }
        assert forall|i0: int| 0 <= i0 < l implies (#[trigger] evals@[i0])@.len() == l - i0 by {
            if i0 != i {
                assert(evals@[i0] == pre[i0]);
            }
        }
        assert forall|i0: int, k: int| 0 <= i0 < l && 0 <= k < l - i0 implies (#[trigger] evals@[i0]@[k]).0 == if i0
            < i + 1 {
            normalized_subspace_poly(basis@, i0 as nat, basis@[i0 + k].0)
        } else {
            subspace_poly(basis@, i0 as nat, basis@[i0 + k].0)
        } by {
            if i0 != i {
                assert(evals@[i0] == pre[i0]);
                assert(evals@[i0]@[k] == pre[i0]@[k]);
            }
        }
    }
    evals
}

/// Additive NTT over F_{2^64} with the standard polynomial-basis subspace
/// `{1, x, x², …}`: the F_2-subspace is `{0, 1, …, 2^ℓ−1}` under the natural
/// integer encoding, exactly as in the extension-field version (whose domain already
/// lived inside this very subfield).
#[derive(Clone, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct AdditiveNttF64 {
    evals: Vec<Vec<F64>>,
}

impl AdditiveNttF64 {
    /// The twiddle table, row by row.
    pub closed spec fn table(&self) -> Seq<Seq<F64>> {
        self.evals@.map_values(|r: Vec<F64>| r@)
    }

    /// The table of a basis of `ℓ` elements: row `i` holds `Ŵ_i(b_(i+k))` for `k < ℓ - i`.
    pub open spec fn is_table_of(tab: Seq<Seq<F64>>, basis: Seq<F64>) -> bool {
        &&& tab.len() == basis.len()
        &&& forall|i: int| 0 <= i < tab.len() ==> #[trigger] tab[i].len() == basis.len() - i
        &&& forall|i: int, k: int|
            0 <= i < tab.len() && 0 <= k < tab[i].len() ==> (#[trigger] tab[i][k]).0
                == normalized_subspace_poly(basis, i as nat, basis[i + k].0)
    }

    /// The twiddle table of a domain of dimension `1..=63`.
    pub open spec fn well_formed(&self) -> bool {
        &&& 1 <= self.table().len() <= 63
        &&& forall|i: int|
            0 <= i < self.table().len() ==> #[trigger] self.table()[i].len() == self.table().len() - i
    }

    fn new(basis: &[F64]) -> (r: Self)
        requires
            1 <= basis.len() <= 63,
        ensures
            r.well_formed(),
            Self::is_table_of(r.table(), basis@),
    {
        let r = Self { evals: generate_evals_from_subspace(basis) };
        assert forall|i: int| 0 <= i < r.table().len() implies #[trigger] r.table()[i].len() == r.table().len()
            - i by {
            assert(r.table()[i] == r.evals@[i]@);
            assert(r.evals@[i]@.len() == basis.len() - i);
        }
        assert forall|i: int, k: int| 0 <= i < r.table().len() && 0 <= k < r.table()[i].len() implies (
        #[trigger] r.table()[i][k]).0 == normalized_subspace_poly(basis@, i as nat, basis@[i + k].0) by {
            assert(r.table()[i] == r.evals@[i]@);
        }
        r
    }

    /// Standard NTT with basis `{1, x, …, x^(dim-1)}`. Requires `dim ≤ 63` so
    /// the evaluation domain (and the twiddles) stay inside F_{2^64} without
    /// wrap; far beyond any codeword size in use.
    ///
    /// Rewritten: the `assert!` is a precondition, which also excludes `dim = 0` (production panics
    /// there), and the basis is built by a loop instead of `map(..).collect()`.
    pub fn standard(dim: usize) -> (r: Self)
        requires
            1 <= dim <= 63,
        ensures
            r.well_formed(),
            r.table().len() == dim,
            Self::is_table_of(r.table(), standard_basis(dim as nat)),
    {
        let mut basis: Vec<F64> = Vec::with_capacity(dim);
        for i in 0..dim
            invariant
                dim <= 63,
                basis@ == standard_basis(i as nat),
        {
            basis.push(F64(1u64 << i));
            assert(basis@ =~= standard_basis((i + 1) as nat));
        }
        Self::new(&basis)
    }

    pub const fn log_domain_size(&self) -> (r: usize)
        ensures
            r == self.table().len(),
    {
        self.evals.len()
    }

    /// Twiddle of one block at one layer.
    ///
    /// - It is `s_i(sum_j bit_j(block) * b_(i+1+j))`, with `i = L - layer - 1` on a `2^L`-point domain.
    /// - The normalized `s_i` is F_2-linear, so this is a subset sum of row `i` of the table.
    pub fn twiddle(&self, layer: usize, block: usize) -> (r: F64)
        requires
            layer < self.table().len(),
            1 <= self.table()[self.table().len() - layer - 1].len() <= 65,
        ensures
            r.0 == twiddle_spec(self.table(), layer as nat, block),
    {
        let v = &self.evals[self.log_domain_size() - layer - 1];
        assert(v@ == self.table()[self.table().len() - layer - 1]);
        span_get(&v[1..], block)
    }

    /// The seven twiddles a radix-8 group needs, breadth-first: layer `layer`,
    /// then `layer + 1` (one per half), then `layer + 2` (one per quarter).
    ///
    /// `span_get` is F_2-linear in the block index, so the six deeper twiddles are
    /// the block's own contribution plus a fixed correction per sub-block index:
    /// one scan of the three basis rows replaces seven.
    pub fn twiddles_radix8(&self, layer: usize, block: usize) -> (r: [F64; 7])
        requires
            layer + 3 <= self.table().len(),
            block < pow2(layer as nat),
            layer + 1 <= self.table()[self.table().len() - layer - 1].len() <= 64,
            layer + 2 <= self.table()[self.table().len() - layer - 2].len() <= 64,
            layer + 3 <= self.table()[self.table().len() - layer - 3].len() <= 64,
        ensures
            r[0].0 == twiddle_spec(self.table(), layer as nat, block),
            r[1].0 == twiddle_spec(self.table(), (layer + 1) as nat, (2 * block) as usize),
            r[2].0 == twiddle_spec(self.table(), (layer + 1) as nat, (2 * block + 1) as usize),
            r[3].0 == twiddle_spec(self.table(), (layer + 2) as nat, (4 * block) as usize),
            r[4].0 == twiddle_spec(self.table(), (layer + 2) as nat, (4 * block + 1) as usize),
            r[5].0 == twiddle_spec(self.table(), (layer + 2) as nat, (4 * block + 2) as usize),
            r[6].0 == twiddle_spec(self.table(), (layer + 2) as nat, (4 * block + 3) as usize),
    {
        let l = self.log_domain_size();
        let (v0, v1, v2) = (&self.evals[l - layer - 1], &self.evals[l - layer - 2], &self.evals[l - layer - 3]);
        assert(v0@ == self.table()[l - layer - 1] && v1@ == self.table()[l - layer - 2] && v2@ == self.table()[l - layer
            - 3]);
        let ghost (s0, s1, s2) = (v0@.skip(1), v1@.skip(2), v2@.skip(3));
        let (mut t0, mut a, mut c) = (F64::ZERO, F64::ZERO, F64::ZERO);
        for j in 0..layer
            invariant
                layer <= 61,
                v0@.len() >= layer + 1,
                v1@.len() >= layer + 2,
                v2@.len() >= layer + 3,
                s0 == v0@.skip(1),
                s1 == v1@.skip(2),
                s2 == v2@.skip(3),
                t0.0 == span(s0.take(j as int), block),
                a.0 == span(s1.take(j as int), block),
                c.0 == span(s2.take(j as int), block),
        {
            assert(s0.take(j + 1).drop_last() =~= s0.take(j as int));
            assert(s1.take(j + 1).drop_last() =~= s1.take(j as int));
            assert(s2.take(j + 1).drop_last() =~= s2.take(j as int));
            proof {
                lemma_xor_facts(t0.0, 0, 0);
                lemma_xor_facts(a.0, 0, 0);
                lemma_xor_facts(c.0, 0, 0);
            }
            if (block >> j) & 1 == 1 {
                t0 += v0[1 + j];
                a += v1[2 + j];
                c += v2[3 + j];
            }
        }
        let (d, e0, e1) = (v1[1], v2[1], v2[2]);
        proof {
            self.lemma_twiddles_radix8(layer as nat, block, t0.0, a.0, c.0);
        }
        [t0, a, a + d, c, c + e0, c + e1, c + e0 + e1]
    }

    proof fn lemma_twiddles_radix8(&self, layer: nat, block: usize, t0: u64, a: u64, c: u64)
        requires
            layer + 3 <= self.table().len(),
            block < pow2(layer),
            layer + 1 <= self.table()[self.table().len() - layer - 1].len() <= 64,
            layer + 2 <= self.table()[self.table().len() - layer - 2].len() <= 64,
            layer + 3 <= self.table()[self.table().len() - layer - 3].len() <= 64,
            t0 == span(self.table()[self.table().len() - layer - 1].skip(1).take(layer as int), block),
            a == span(self.table()[self.table().len() - layer - 2].skip(2).take(layer as int), block),
            c == span(self.table()[self.table().len() - layer - 3].skip(3).take(layer as int), block),
        ensures
            ({
                let tab = self.table();
                let (v1, v2) = (tab[tab.len() - layer - 2], tab[tab.len() - layer - 3]);
                &&& t0 == twiddle_spec(tab, layer, block)
                &&& a == twiddle_spec(tab, layer + 1, (2 * block) as usize)
                &&& a ^ v1[1].0 == twiddle_spec(tab, layer + 1, (2 * block + 1) as usize)
                &&& c == twiddle_spec(tab, layer + 2, (4 * block) as usize)
                &&& c ^ v2[1].0 == twiddle_spec(tab, layer + 2, (4 * block + 1) as usize)
                &&& c ^ v2[2].0 == twiddle_spec(tab, layer + 2, (4 * block + 2) as usize)
                &&& (c ^ v2[1].0) ^ v2[2].0 == twiddle_spec(tab, layer + 2, (4 * block + 3) as usize)
            }),
    {
        let tab = self.table();
        let (v0, v1, v2) = (tab[tab.len() - layer - 1], tab[tab.len() - layer - 2], tab[tab.len() - layer - 3]);
        lemma2_to64();
        lemma2_to64_rest();
        if layer < 61 {
            lemma_pow2_strictly_increases(layer, 61);
        }
        assert(v1.skip(1).skip(1) =~= v1.skip(2));
        assert(v2.skip(1).skip(1) =~= v2.skip(2));
        assert(v2.skip(2).skip(1) =~= v2.skip(3));
        // Layer `layer`: the block alone.
        lemma_span_low(v0.skip(1), block, layer);
        // Layer `layer + 1`: sub-block `2b + h`.
        lemma_span_low(v1.skip(2), block, layer);
        lemma_span_double(v1.skip(1), block);
        lemma_xor_facts(a, v1[1].0, 0);
        // Layer `layer + 2`: sub-block `4b + 2h + q = 2(2b + h) + q`.
        lemma_span_low(v2.skip(3), block, layer);
        let b2 = (2 * block) as usize;
        let b21 = (2 * block + 1) as usize;
        lemma_span_double(v2.skip(2), block);
        lemma_span_double(v2.skip(1), b2);
        lemma_span_double(v2.skip(1), b21);
        assert((b2 * 2) as usize == (4 * block) as usize);
        assert((b2 * 2 + 1) as usize == (4 * block + 1) as usize);
        assert((b21 * 2) as usize == (4 * block + 2) as usize);
        assert((b21 * 2 + 1) as usize == (4 * block + 3) as usize);
        let (e0, e1) = (v2[1].0, v2[2].0);
        assert(e0 ^ (e1 ^ c) == (c ^ e0) ^ e1 && e1 ^ c == c ^ e1 && e0 ^ c == c ^ e0) by (bit_vector);
    }
}

/// The twiddle of a block is `Ŵ_i` of the block's point, `i = L - layer - 1`: the subset sum of the
/// basis elements `b_(i+1+j)` over the set bits `j` of the block index (the claim of `twiddle`'s
/// documentation).
pub proof fn lemma_twiddle_is_subspace_poly(tab: Seq<Seq<F64>>, basis: Seq<F64>, layer: nat, block: usize)
    requires
        AdditiveNttF64::is_table_of(tab, basis),
        layer < tab.len(),
    ensures
        ({
            let i = (tab.len() - layer - 1) as nat;
            twiddle_spec(tab, layer, block) == normalized_subspace_poly(basis, i, span(basis.skip((i + 1) as int), block))
        }),
{
    let i = (tab.len() - layer - 1) as nat;
    let s = tab[i as int].skip(1);
    let t = basis.skip((i + 1) as int);
    assert forall|j: int| 0 <= j < s.len() implies s[j].0 == normalized_subspace_poly(basis, i, #[trigger] t[j].0) by {
        assert(tab[i as int][j + 1] == s[j]);
    }
    lemma_span_normalized(basis, i, s, t, block);
}


// ---------------------------------------------------------------------------------------------
// Butterflies on every lane of a row pair (portable path)
// ---------------------------------------------------------------------------------------------
/// One lane's butterfly outputs `(new_u, new_v)`, forward or transposed.
pub open spec fn butterfly_spec(transposed: bool, u: u64, v: u64, t: u64) -> (u64, u64) {
    if transposed {
        (u ^ v, v ^ k_mul(u ^ v, t))
    } else {
        (bf_top(u, v, t), bf_bot(u, v, t))
    }
}

/// Butterfly all `num_ntts` lanes of one (top row, bottom row) pair with a
/// shared twiddle: new_u = u + v*t; new_v = v + new_u.
#[inline]
pub fn butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64)
    requires
        old(top).len() == old(bot).len(),
    ensures
        final(top).len() == old(top).len(),
        final(bot).len() == old(bot).len(),
        forall|i: int|
            0 <= i < old(top).len() ==> ((#[trigger] final(top)@[i]).0, final(bot)@[i].0) == butterfly_spec(
                false,
                old(top)@[i].0,
                old(bot)@[i].0,
                twiddle.0,
            ),
{
    lane_butterflies::<false>(top, bot, twiddle);
}

/// The transposed butterfly on every lane of a row pair: s = u + v; new_u = s; new_v = v + s*t.
///
/// It is the inverse of the forward butterfly with the rows swapped.
#[inline]
pub fn transposed_butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64)
    requires
        old(top).len() == old(bot).len(),
    ensures
        final(top).len() == old(top).len(),
        final(bot).len() == old(bot).len(),
        forall|i: int|
            0 <= i < old(top).len() ==> ((#[trigger] final(top)@[i]).0, final(bot)@[i].0) == butterfly_spec(
                true,
                old(top)@[i].0,
                old(bot)@[i].0,
                twiddle.0,
            ),
{
    lane_butterflies::<true>(top, bot, twiddle);
}

/// The butterflies of every lane of a row pair, forward or transposed.
///
/// On NEON this processes eight lanes per iteration. Four independent pair
/// reductions stay in the vector register file, exposing their PMULL chains
/// in parallel and amortizing the loop branch and constant setup. The pair
/// kernel handles a short even tail, and the scalar path handles an odd tail.
///
/// Rewritten for Verus: the SIMD kernels (`crate::ntt_simd`) take the rows and the offset instead of
/// `top.as_mut_ptr().add(..)` and `bot.as_mut_ptr().add(..)`; the NEON pair loop tests `top.len() - lane >= 2`
/// instead of `lane + 2 <= top.len()` (the same for `lane <= top.len()`, and Verus has no bound on a slice's
/// length that rules out the overflow of `lane + 2`); the `zip` of the rows' `iter_mut` from `done` is an index
/// loop; `debug_assert_eq!(top.len(), bot.len())` is the `requires`.
#[inline]
pub fn lane_butterflies<const TRANSPOSED: bool>(top: &mut [F64], bot: &mut [F64], twiddle: F64)
    requires
        old(top).len() == old(bot).len(),
    ensures
        final(top).len() == old(top).len(),
        final(bot).len() == old(bot).len(),
        forall|i: int|
            0 <= i < old(top).len() ==> ((#[trigger] final(top)@[i]).0, final(bot)@[i].0) == butterfly_spec(
                TRANSPOSED,
                old(top)@[i].0,
                old(bot)@[i].0,
                twiddle.0,
            ),
{
    let ghost (top0, bot0) = (top@, bot@);
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    let done = {
        let vectors = top.len() / 8;
        // SAFETY: the target features are enabled at compile time and each
        // iteration reads and writes exactly eight elements from both rows.
        unsafe {
            for i in 0..vectors
                invariant
                    vectors == top0.len() / 8,
                    bot0.len() == top0.len(),
                    top0.len() <= usize::MAX,
                    butterflied(TRANSPOSED, top0, bot0, top@, bot@, 0, 8 * i, twiddle.0),
            {
                let ghost (top1, bot1) = (top@, bot@);
                proof {
                    lemma_fundamental_div_mod(top0.len() as int, 8);
                    assert(8 * i + 8 <= top0.len());
                }
                butterfly_lanes_avx512::<TRANSPOSED>(top, bot, 8 * i, twiddle.0);
                proof {
                    lemma_butterflied_extend(TRANSPOSED, top0, bot0, top1, bot1, top@, bot@, 0, 8 * i, 8 * i + 8, twiddle.0);
                }
            }
        }
        8 * vectors
    };
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "vpclmulqdq",
        target_feature = "avx2",
        not(target_feature = "avx512f")
    ))]
    let done = {
        let vectors = top.len() / 4;
        // SAFETY: the target features are enabled at compile time and each
        // iteration reads and writes exactly four elements from both rows.
        unsafe {
            for i in 0..vectors
                invariant
                    vectors == top0.len() / 4,
                    bot0.len() == top0.len(),
                    top0.len() <= usize::MAX,
                    butterflied(TRANSPOSED, top0, bot0, top@, bot@, 0, 4 * i, twiddle.0),
            {
                let ghost (top1, bot1) = (top@, bot@);
                proof {
                    lemma_fundamental_div_mod(top0.len() as int, 4);
                    assert(4 * i + 4 <= top0.len());
                }
                butterfly_lanes_avx2::<TRANSPOSED>(top, bot, 4 * i, twiddle.0);
                proof {
                    lemma_butterflied_extend(TRANSPOSED, top0, bot0, top1, bot1, top@, bot@, 0, 4 * i, 4 * i + 4, twiddle.0);
                }
            }
        }
        4 * vectors
    };
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    let done = {
        let vectors = top.len() / 8;
        let mut lane = 8 * vectors;
        // SAFETY: aes target feature is enabled at compile time; the kernels
        // read and write lanes [8i, 8i+8), then pairs below the rows' length.
        unsafe {
            for i in 0..vectors
                invariant
                    vectors == top0.len() / 8,
                    lane == 8 * vectors,
                    bot0.len() == top0.len(),
                    top0.len() <= usize::MAX,
                    butterflied(TRANSPOSED, top0, bot0, top@, bot@, 0, 8 * i, twiddle.0),
            {
                let ghost (top1, bot1) = (top@, bot@);
                proof {
                    lemma_fundamental_div_mod(top0.len() as int, 8);
                    assert(8 * i + 8 <= top0.len());
                }
                butterfly_lanes_neon_8::<TRANSPOSED>(top, bot, 8 * i, twiddle.0);
                proof {
                    lemma_butterflied_extend(TRANSPOSED, top0, bot0, top1, bot1, top@, bot@, 0, 8 * i, 8 * i + 8, twiddle.0);
                }
            }
            proof {
                lemma_fundamental_div_mod(top0.len() as int, 8);
            }
            while top.len() - lane >= 2
                invariant
                    lane <= top0.len(),
                    bot0.len() == top0.len(),
                    top0.len() <= usize::MAX,
                    butterflied(TRANSPOSED, top0, bot0, top@, bot@, 0, lane as int, twiddle.0),
                decreases top0.len() - lane,
            {
                let ghost (top1, bot1) = (top@, bot@);
                butterfly_lane_pair_neon::<TRANSPOSED>(top, bot, lane, twiddle.0);
                proof {
                    lemma_butterflied_extend(TRANSPOSED, top0, bot0, top1, bot1, top@, bot@, 0, lane as int, lane + 2, twiddle.0);
                }
                lane += 2;
            }
        }
        lane
    };
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")
    )))]
    let done = 0;
    let n = top.len();
    for i in done..n
        invariant
            n == top0.len(),
            top.len() == top0.len(),
            bot.len() == top0.len(),
            bot0.len() == top0.len(),
            forall|j: int|
                0 <= j < i ==> ((#[trigger] top@[j]).0, bot@[j].0) == butterfly_spec(TRANSPOSED, top0[j].0, bot0[j].0, twiddle.0),
            forall|j: int| i <= j < top0.len() ==> #[trigger] top@[j] == top0[j] && bot@[j] == bot0[j],
    {
        let mut u = top[i];
        let mut v = bot[i];
        butterfly_one::<TRANSPOSED>(&mut u, &mut v, twiddle);
        top[i] = u;
        bot[i] = v;
    }
}

// ---------------------------------------------------------------------------------------------
// Layers
// ---------------------------------------------------------------------------------------------
/// Row of word `p` in a buffer of `m` interleaved lanes.
pub open spec fn row_of(p: int, m: nat) -> int {
    p / (m as int)
}

/// Block of word `p` at a layer whose blocks are `2h` rows.
pub open spec fn blk_of(p: int, m: nat, h: nat) -> int {
    row_of(p, m) / ((2 * h) as int)
}

/// Row of word `p` inside its block of `2h` rows.
pub open spec fn r_of(p: int, m: nat, h: nat) -> int {
    row_of(p, m) % ((2 * h) as int)
}

/// One layer of butterflies on a buffer of `m` interleaved lanes, word `p` being row `p / m`, lane `p % m`.
///
/// Rows pair `h` apart inside blocks of `2h` rows: each top row `r` with bottom row `r + h`, lane by lane.
/// Block `b` takes the twiddle `tw(b)`. The forward butterfly is `(u, v) -> (u + v t, v + u + v t)`,
/// the inverse one `(u, v) -> (u + (v + u) t, v + u)`.
pub open spec fn layer_map(data: Seq<F64>, m: nat, h: nat, tw: spec_fn(int) -> u64, inverse: bool) -> Seq<F64> {
    Seq::new(
        data.len(),
        |p: int|
            {
                let t = tw(blk_of(p, m, h));
                if r_of(p, m, h) < h {
                    let (u, v) = (data[p].0, data[p + h * m].0);
                    F64(
                        if inverse {
                            ibf_top(u, v, t)
                        } else {
                            bf_top(u, v, t)
                        },
                    )
                } else {
                    let (u, v) = (data[p - h * m].0, data[p].0);
                    F64(
                        if inverse {
                            ibf_bot(u, v, t)
                        } else {
                            bf_bot(u, v, t)
                        },
                    )
                }
            },
    )
}

/// The twiddles of one layer, block by block, read from the table.
pub open spec fn layer_twiddles(tab: Seq<Seq<F64>>, layer: nat) -> spec_fn(int) -> u64 {
    |b: int| twiddle_spec(tab, layer, b as usize)
}

/// Half a block at one layer of a `2^log_d`-row transform: layer 0 pairs rows half the domain apart.
pub open spec fn layer_half(log_d: nat, layer: nat) -> nat {
    pow2((log_d - layer - 1) as nat)
}

/// The forward layers `start..end` of a `2^log_d`-row transform on `m` lanes, applied in order.
pub open spec fn forward_layers(tab: Seq<Seq<F64>>, data: Seq<F64>, m: nat, log_d: nat, start: nat, end: nat) -> Seq<F64>
    decreases end,
{
    if end <= start {
        data
    } else {
        layer_map(
            forward_layers(tab, data, m, log_d, start, (end - 1) as nat),
            m,
            layer_half(log_d, (end - 1) as nat),
            layer_twiddles(tab, (end - 1) as nat),
            false,
        )
    }
}

/// The inverse layers `log_d - 1` down to `lo` of a `2^log_d`-row transform on `m` lanes, applied in order.
pub open spec fn inverse_layers(tab: Seq<Seq<F64>>, data: Seq<F64>, m: nat, log_d: nat, lo: nat) -> Seq<F64>
    decreases log_d - lo,
{
    if lo >= log_d {
        data
    } else {
        layer_map(
            inverse_layers(tab, data, m, log_d, lo + 1),
            m,
            layer_half(log_d, lo),
            layer_twiddles(tab, lo),
            true,
        )
    }
}

pub proof fn lemma_compose(blk: int, r: int, lane: int, m: nat, h: nat)
    requires
        0 <= blk,
        0 <= r < 2 * h,
        0 <= lane < m,
    ensures
        ({
            let q = (blk * (2 * h) + r) * m + lane;
            &&& q >= 0
            &&& row_of(q, m) == blk * (2 * h) + r
            &&& q % (m as int) == lane
            &&& blk_of(q, m, h) == blk
            &&& r_of(q, m, h) == r
        }),
{
    let row = blk * (2 * h) + r;
    lemma_mul_nonnegative(blk, (2 * h) as int);
    lemma_mul_nonnegative(row, m as int);
    lemma_fundamental_div_mod_converse(row * m + lane, m as int, row, lane);
    lemma_fundamental_div_mod_converse(row, (2 * h) as int, blk, r);
}

proof fn lemma_decompose(p: int, m: nat, h: nat)
    requires
        0 <= p,
        m > 0,
        h > 0,
    ensures
        0 <= p % (m as int) < m,
        0 <= row_of(p, m),
        0 <= blk_of(p, m, h),
        0 <= r_of(p, m, h) < 2 * h,
        p == (blk_of(p, m, h) * (2 * h) + r_of(p, m, h)) * m + p % (m as int),
{
    let row = row_of(p, m);
    lemma_fundamental_div_mod(p, m as int);
    lemma_mod_pos_bound(p, m as int);
    lemma_div_pos_is_pos(p, m as int);
    lemma_fundamental_div_mod(row, (2 * h) as int);
    lemma_mod_pos_bound(row, (2 * h) as int);
    lemma_div_pos_is_pos(row, (2 * h) as int);
    let (b, r, lane) = (blk_of(p, m, h), r_of(p, m, h), p % (m as int));
    assert(p == (b * (2 * h) + r) * m + lane) by (nonlinear_arith)
        requires
            p == m * row + lane,
            row == (2 * h) * b + r,
    ;
}

pub proof fn lemma_bound(blk: int, r: int, lane: int, m: nat, h: nat, nb: nat)
    requires
        0 <= blk < nb,
        0 <= r < 2 * h,
        0 <= lane < m,
    ensures
        (blk * (2 * h) + r) * m + lane < nb * (2 * h) * m,
{
    let row = blk * (2 * h) + r;
    assert(row + 1 <= nb * (2 * h)) by (nonlinear_arith)
        requires
            row == blk * (2 * h) + r,
            r < 2 * h,
            blk + 1 <= nb,
    ;
    assert(row * m + lane < nb * (2 * h) * m) by (nonlinear_arith)
        requires
            row + 1 <= nb * (2 * h),
            0 <= lane < m,
            0 <= row,
    ;
}

pub proof fn lemma_blk_bound(p: int, m: nat, h: nat, nb: nat)
    requires
        0 <= p < nb * (2 * h) * m,
        m > 0,
        h > 0,
    ensures
        blk_of(p, m, h) < nb,
{
    lemma_decompose(p, m, h);
    let (b, r, lane) = (blk_of(p, m, h), r_of(p, m, h), p % (m as int));
    if b >= nb {
        assert(p >= nb * (2 * h) * m) by (nonlinear_arith)
            requires
                p == (b * (2 * h) + r) * m + lane,
                b >= nb,
                r >= 0,
                lane >= 0,
                m > 0,
                h > 0,
        ;
    }
}

/// Word `p` has had its butterfly at the sweep position `(block, row, lane)`: butterflies run block by
/// block, then by row of the top half, then by lane.
pub open spec fn swept(p: int, m: nat, h: nat, block: int, row: int, lane: int) -> bool {
    let b = blk_of(p, m, h);
    let r = r_of(p, m, h);
    let rr = if r < h {
        r
    } else {
        r - h
    };
    b < block || (b == block && (rr < row || (rr == row && p % (m as int) < lane)))
}

/// Mid-sweep: the swept words hold the layer's output, the others its input.
pub open spec fn sweep_inv(
    data: Seq<F64>,
    prev: Seq<F64>,
    target: Seq<F64>,
    m: nat,
    h: nat,
    block: int,
    row: int,
    lane: int,
) -> bool {
    &&& data.len() == prev.len()
    &&& target.len() == prev.len()
    &&& forall|p: int|
        0 <= p < data.len() ==> #[trigger] data[p] == if swept(p, m, h, block, row, lane) {
            target[p]
        } else {
            prev[p]
        }
}

proof fn lemma_sweep_start(prev: Seq<F64>, target: Seq<F64>, m: nat, h: nat)
    requires
        m > 0,
        h > 0,
        target.len() == prev.len(),
    ensures
        sweep_inv(prev, prev, target, m, h, 0, 0, 0),
{
    assert forall|p: int| 0 <= p < prev.len() implies !swept(p, m, h, 0, 0, 0) by {
        lemma_decompose(p, m, h);
    }
}

proof fn lemma_sweep_lane_end(data: Seq<F64>, prev: Seq<F64>, target: Seq<F64>, m: nat, h: nat, block: int, row: int)
    requires
        m > 0,
        h > 0,
        sweep_inv(data, prev, target, m, h, block, row, m as int),
    ensures
        sweep_inv(data, prev, target, m, h, block, row + 1, 0),
{
    assert forall|p: int| 0 <= p < data.len() implies swept(p, m, h, block, row, m as int) == swept(
        p,
        m,
        h,
        block,
        row + 1,
        0,
    ) by {
        lemma_decompose(p, m, h);
    }
    assert forall|p: int| 0 <= p < data.len() implies #[trigger] data[p] == if swept(p, m, h, block, row + 1, 0) {
        target[p]
    } else {
        prev[p]
    } by {
        assert(swept(p, m, h, block, row, m as int) == swept(p, m, h, block, row + 1, 0));
    }
}

proof fn lemma_sweep_row_end(data: Seq<F64>, prev: Seq<F64>, target: Seq<F64>, m: nat, h: nat, block: int)
    requires
        m > 0,
        h > 0,
        sweep_inv(data, prev, target, m, h, block, h as int, 0),
    ensures
        sweep_inv(data, prev, target, m, h, block + 1, 0, 0),
{
    assert forall|p: int| 0 <= p < data.len() implies swept(p, m, h, block, h as int, 0) == swept(
        p,
        m,
        h,
        block + 1,
        0,
        0,
    ) by {
        lemma_decompose(p, m, h);
    }
    assert forall|p: int| 0 <= p < data.len() implies #[trigger] data[p] == if swept(p, m, h, block + 1, 0, 0) {
        target[p]
    } else {
        prev[p]
    } by {
        assert(swept(p, m, h, block, h as int, 0) == swept(p, m, h, block + 1, 0, 0));
    }
}

proof fn lemma_sweep_end(data: Seq<F64>, prev: Seq<F64>, target: Seq<F64>, m: nat, h: nat, nb: nat)
    requires
        m > 0,
        h > 0,
        prev.len() == nb * (2 * h) * m,
        sweep_inv(data, prev, target, m, h, nb as int, 0, 0),
    ensures
        data == target,
{
    assert forall|p: int| 0 <= p < data.len() implies data[p] == target[p] by {
        lemma_blk_bound(p, m, h, nb);
    }
    assert(data =~= target);
}

/// The exec offsets of one butterfly and their bounds.
proof fn lemma_sweep_index(nb: nat, h: nat, m: nat, block: int, row: int, lane: int)
    requires
        0 <= block < nb,
        0 <= row < h,
        0 <= lane < m,
    ensures
        block * ((2 * h) * m) + row * m + lane == (block * (2 * h) + row) * m + lane,
        (block * (2 * h) + row) * m + lane + h * m < nb * (2 * h) * m,
        (2 * h) * m <= nb * (2 * h) * m,
        block * ((2 * h) * m) <= nb * (2 * h) * m,
        row * m <= nb * (2 * h) * m,
        h * m <= nb * (2 * h) * m,
        h > 0 && m > 0 ==> h * m > 0,
{
    if h > 0 && m > 0 {
        assert(h * m > 0) by (nonlinear_arith)
            requires
                h > 0,
                m > 0,
        ;
    }
    lemma_bound(block, row + h, lane, m, h, nb);
    lemma_bound(block, 0, 0, m, h, nb);
    lemma_bound(0, row, 0, m, h, nb);
    lemma_bound(0, h as int, 0, m, h, nb);
    assert(block * ((2 * h) * m) + row * m + lane == (block * (2 * h) + row) * m + lane) by (nonlinear_arith);
    assert((block * (2 * h) + (row + h)) * m + lane == (block * (2 * h) + row) * m + lane + h * m) by (nonlinear_arith);
    assert((2 * h) * m <= nb * (2 * h) * m) by (nonlinear_arith)
        requires
            nb >= 1,
    ;
    assert(block * ((2 * h) * m) == (block * (2 * h) + 0) * m + 0) by (nonlinear_arith);
    assert(row * m == (0 * (2 * h) + row) * m + 0) by (nonlinear_arith);
    assert(h * m == (0 * (2 * h) + h) * m + 0) by (nonlinear_arith);
}

/// One butterfly of a sweep advances the sweep position by one lane.
proof fn lemma_sweep_step(
    data: Seq<F64>,
    new: Seq<F64>,
    prev: Seq<F64>,
    m: nat,
    h: nat,
    nb: nat,
    tw: spec_fn(int) -> u64,
    inverse: bool,
    block: int,
    row: int,
    lane: int,
)
    requires
        m > 0,
        h > 0,
        prev.len() == nb * (2 * h) * m,
        0 <= block < nb,
        0 <= row < h,
        0 <= lane < m,
        sweep_inv(data, prev, layer_map(prev, m, h, tw, inverse), m, h, block, row, lane),
        new.len() == data.len(),
        ({
            let q1 = (block * (2 * h) + row) * m + lane;
            let q2 = q1 + h * m;
            let (u, v, t) = (data[q1].0, data[q2].0, tw(block));
            &&& new[q1].0 == if inverse {
                ibf_top(u, v, t)
            } else {
                bf_top(u, v, t)
            }
            &&& new[q2].0 == if inverse {
                ibf_bot(u, v, t)
            } else {
                bf_bot(u, v, t)
            }
            &&& forall|p: int| 0 <= p < new.len() && p != q1 && p != q2 ==> #[trigger] new[p] == data[p]
        }),
    ensures
        sweep_inv(new, prev, layer_map(prev, m, h, tw, inverse), m, h, block, row, lane + 1),
{
    let target = layer_map(prev, m, h, tw, inverse);
    let q1 = (block * (2 * h) + row) * m + lane;
    let q2 = q1 + h * m;
    lemma_compose(block, row, lane, m, h);
    lemma_compose(block, row + h, lane, m, h);
    lemma_sweep_index(nb, h, m, block, row, lane);
    assert((block * (2 * h) + (row + h)) * m + lane == q2) by (nonlinear_arith)
        requires
            q1 == (block * (2 * h) + row) * m + lane,
            q2 == q1 + h * m,
    ;
    assert(!swept(q1, m, h, block, row, lane));
    assert(!swept(q2, m, h, block, row, lane));
    assert(data[q1] == prev[q1]);
    assert(data[q2] == prev[q2]);
    assert(new[q1] == target[q1]);
    assert(new[q2] == target[q2]);
    assert forall|p: int| 0 <= p < new.len() implies #[trigger] new[p] == if swept(p, m, h, block, row, lane + 1) {
        target[p]
    } else {
        prev[p]
    } by {
        if p != q1 && p != q2 {
            lemma_decompose(p, m, h);
            let (b, r) = (blk_of(p, m, h), r_of(p, m, h));
            if b == block && p % (m as int) == lane {
                if r == row {
                    assert(p == q1);
                } else if r == row + h {
                    assert(p == q2);
                }
            }
            assert(new[p] == data[p]);
        }
    }
}

/// The exec shape of one layer of a `2^log_d`-row transform: `2^layer` blocks of `2h` rows.
pub proof fn lemma_layer_shape(log_d: nat, layer: nat, m: nat)
    requires
        layer < log_d,
    ensures
        layer_half(log_d, layer) > 0,
        pow2(layer) > 0,
        pow2((log_d - layer) as nat) == 2 * layer_half(log_d, layer),
        pow2(layer) * (2 * layer_half(log_d, layer)) * m == m * pow2(log_d),
{
    let k = (log_d - layer) as nat;
    lemma_pow2_pos(layer);
    lemma_pow2_pos((k - 1) as nat);
    lemma_pow2_unfold(k);
    lemma_pow2_adds(layer, k);
    assert(pow2(layer) * pow2(k) * m == m * pow2(log_d)) by (nonlinear_arith)
        requires
            pow2(layer) * pow2(k) == pow2(log_d),
    ;
}

pub proof fn lemma_layer_map_len(data: Seq<F64>, m: nat, h: nat, tw: spec_fn(int) -> u64, inverse: bool)
    ensures
        layer_map(data, m, h, tw, inverse).len() == data.len(),
{
}

pub proof fn lemma_forward_layers_len(tab: Seq<Seq<F64>>, data: Seq<F64>, m: nat, log_d: nat, start: nat, end: nat)
    ensures
        forward_layers(tab, data, m, log_d, start, end).len() == data.len(),
    decreases end,
{
    if end > start {
        lemma_forward_layers_len(tab, data, m, log_d, start, (end - 1) as nat);
    }
}

pub proof fn lemma_inverse_layers_len(tab: Seq<Seq<F64>>, data: Seq<F64>, m: nat, log_d: nat, lo: nat)
    ensures
        inverse_layers(tab, data, m, log_d, lo).len() == data.len(),
    decreases log_d - lo,
{
    if lo < log_d {
        lemma_inverse_layers_len(tab, data, m, log_d, lo + 1);
    }
}

/// The inverse layer undoes the forward layer with the same twiddles, word by word.
pub proof fn lemma_layer_roundtrip(y: Seq<F64>, m: nat, h: nat, nb: nat, tw: spec_fn(int) -> u64)
    requires
        m > 0,
        h > 0,
        y.len() == nb * (2 * h) * m,
    ensures
        layer_map(layer_map(y, m, h, tw, false), m, h, tw, true) == y,
{
    let z = layer_map(y, m, h, tw, false);
    let w = layer_map(z, m, h, tw, true);
    assert forall|p: int| 0 <= p < y.len() implies w[p] == y[p] by {
        lemma_decompose(p, m, h);
        lemma_blk_bound(p, m, h, nb);
        let (b, r, lane) = (blk_of(p, m, h), r_of(p, m, h), p % (m as int));
        if r < h {
            let q = p + h * m;
            lemma_compose(b, r + h, lane, m, h);
            lemma_bound(b, r + h, lane, m, h, nb);
            assert((b * (2 * h) + (r + h)) * m + lane == q) by (nonlinear_arith)
                requires
                    p == (b * (2 * h) + r) * m + lane,
                    q == p + h * m,
            ;
            lemma_inverse_butterfly(y[p].0, y[q].0, tw(b));
        } else {
            let q = p - h * m;
            lemma_compose(b, r - h, lane, m, h);
            assert((b * (2 * h) + (r - h)) * m + lane == q) by (nonlinear_arith)
                requires
                    p == (b * (2 * h) + r) * m + lane,
                    q == p - h * m,
            ;
            lemma_inverse_butterfly(y[q].0, y[p].0, tw(b));
        }
    }
    assert(w =~= y);
}

proof fn lemma_inverse_after_forward_from(tab: Seq<Seq<F64>>, x: Seq<F64>, m: nat, log_d: nat, j: nat)
    requires
        m > 0,
        x.len() == m * pow2(log_d),
        j <= log_d,
    ensures
        inverse_layers(tab, forward_layers(tab, x, m, log_d, 0, log_d), m, log_d, j) == forward_layers(
            tab,
            x,
            m,
            log_d,
            0,
            j,
        ),
    decreases log_d - j,
{
    if j < log_d {
        lemma_inverse_after_forward_from(tab, x, m, log_d, j + 1);
        let y = forward_layers(tab, x, m, log_d, 0, j);
        lemma_forward_layers_len(tab, x, m, log_d, 0, j);
        lemma_layer_shape(log_d, j, m);
        lemma_layer_roundtrip(y, m, layer_half(log_d, j), pow2(j), layer_twiddles(tab, j));
    }
}

/// The inverse transform undoes the forward one: `inverse_layers ∘ forward_layers = id` on every buffer of
/// `m` lanes of `2^log_d` rows, for any twiddle table.
pub proof fn lemma_inverse_after_forward(tab: Seq<Seq<F64>>, x: Seq<F64>, m: nat, log_d: nat)
    requires
        m > 0,
        x.len() == m * pow2(log_d),
    ensures
        inverse_layers(tab, forward_layers(tab, x, m, log_d, 0, log_d), m, log_d, 0) == x,
{
    lemma_inverse_after_forward_from(tab, x, m, log_d, 0);
}

proof fn lemma_pow2_injective(a: nat, b: nat)
    requires
        pow2(a) == pow2(b),
    ensures
        a == b,
{
    if a < b {
        lemma_pow2_strictly_increases(a, b);
    } else if b < a {
        lemma_pow2_strictly_increases(b, a);
    }
}

/// `log2(n)` of a power of two.
///
/// Rewritten from `primitives::log2_strict_usize`: its `assert!` is a precondition, and `trailing_zeros`
/// a search for the exponent.
pub fn log2_strict_usize(n: usize) -> (r: usize)
    requires
        exists|k: nat| n == pow2(k),
    ensures
        r < 64,
        pow2(r as nat) == n,
{
    let ghost k = choose|k: nat| n == pow2(k);
    proof {
        lemma2_to64_rest();
        if k >= 64 {
            if k > 64 {
                lemma_pow2_strictly_increases(64, k);
            }
        }
    }
    let mut r: usize = 0;
    while (1usize << r) < n
        invariant
            r <= k < 64,
            n == pow2(k),
        decreases k - r,
    {
        proof {
            lemma_usize_pow2_no_overflow(r as nat);
            lemma_usize_shl_is_mul(1, r);
        }
        r += 1;
    }
    proof {
        lemma_usize_pow2_no_overflow(r as nat);
        lemma_usize_shl_is_mul(1, r);
        if r < k {
            lemma_pow2_strictly_increases(r as nat, k);
        }
    }
    r
}

/// Scalar reference: one butterfly at a time over `num_ntts` interleaved lanes.
///
/// The test helper of the same name in production, which its tests check against the parallel `transform`.
pub fn forward_scalar_from_layer(ntt: &AdditiveNttF64, data: &mut [F64], num_ntts: usize, start_layer: usize)
    requires
        ntt.well_formed(),
        num_ntts > 0,
        exists|k: nat| old(data).len() == num_ntts * pow2(k) && start_layer <= k <= ntt.table().len(),
    ensures
        forall|k: nat|
            old(data).len() == num_ntts * #[trigger] pow2(k) ==> final(data)@ == forward_layers(
                ntt.table(),
                old(data)@,
                num_ntts as nat,
                k,
                start_layer as nat,
                k,
            ),
{
    let ghost tab = ntt.table();
    let ghost orig = data@;
    let ghost m = num_ntts as nat;
    let ghost k0 = choose|k: nat| data.len() == num_ntts * pow2(k) && start_layer <= k <= ntt.table().len();
    let n_total = data.len();
    proof {
        lemma_div_by_multiple(pow2(k0) as int, num_ntts as int);
        assert(num_ntts * pow2(k0) == pow2(k0) * num_ntts) by (nonlinear_arith);
    }
    let log_d = log2_strict_usize(n_total / num_ntts);
    proof {
        lemma_pow2_injective(log_d as nat, k0);
    }
    for layer in start_layer..log_d
        invariant
            ntt.well_formed(),
            tab == ntt.table(),
            log_d <= tab.len(),
            start_layer <= log_d,
            num_ntts > 0,
            m == num_ntts,
            n_total == data.len(),
            n_total == num_ntts * pow2(log_d as nat),
            data@ == forward_layers(tab, orig, m, log_d as nat, start_layer as nat, layer as nat),
    {
        let ghost h = layer_half(log_d as nat, layer as nat);
        let ghost nb = pow2(layer as nat);
        proof {
            lemma_layer_shape(log_d as nat, layer as nat, m);
            lemma_usize_pow2_no_overflow(layer as nat);
            lemma_usize_pow2_no_overflow((log_d - layer) as nat);
            lemma_usize_shl_is_mul(1, layer);
            lemma_usize_shl_is_mul(1, (log_d - layer) as usize);
            lemma_usize_shr_is_div(pow2((log_d - layer) as nat) as usize, 1);
            lemma2_to64();
            lemma_bound(0, 0, 0, m, h, nb);
            lemma_sweep_index(nb, h, m, 0, 0, 0);
        }
        let num_blocks = 1usize << layer;
        let block_size = 1usize << (log_d - layer);
        let block_size_half = block_size >> 1;
        let block_elems = block_size * num_ntts;
        let ghost prev = data@;
        let ghost tw = layer_twiddles(tab, layer as nat);
        let ghost target = layer_map(prev, m, h, tw, false);
        proof {
            lemma_sweep_start(prev, target, m, h);
        }
        for block in 0..num_blocks
            invariant
                ntt.well_formed(),
                tab == ntt.table(),
                layer < log_d <= tab.len(),
                num_ntts > 0,
                m == num_ntts,
                h > 0,
                num_blocks == nb,
                block_size_half == h,
                block_elems == (2 * h) * m,
                n_total == data.len(),
                prev.len() == nb * (2 * h) * m,
                tw == layer_twiddles(tab, layer as nat),
                target == layer_map(prev, m, h, tw, false),
                sweep_inv(data@, prev, target, m, h, block as int, 0, 0),
        {
            let twiddle = ntt.twiddle(layer, block);
            proof {
                lemma_sweep_index(nb, h, m, block as int, 0, 0);
            }
            let block_start = block * block_elems;
            for row in 0..block_size_half
                invariant
                    num_ntts > 0,
                    m == num_ntts,
                    h > 0,
                    block < nb,
                    block_size_half == h,
                    block_elems == (2 * h) * m,
                    block_start == block * ((2 * h) * m),
                    n_total == data.len(),
                    prev.len() == nb * (2 * h) * m,
                    twiddle.0 == tw(block as int),
                    target == layer_map(prev, m, h, tw, false),
                    sweep_inv(data@, prev, target, m, h, block as int, row as int, 0),
            {
                proof {
                    lemma_sweep_index(nb, h, m, block as int, row as int, 0);
                }
                let off_top = block_start + row * num_ntts;
                let off_bot = off_top + block_size_half * num_ntts;
                for lane in 0..num_ntts
                    invariant
                        num_ntts > 0,
                        m == num_ntts,
                        h > 0,
                        block < nb,
                        row < h,
                        block_size_half == h,
                        off_top == block * ((2 * h) * m) + row * m,
                        off_bot == off_top + h * m,
                        n_total == data.len(),
                        prev.len() == nb * (2 * h) * m,
                        twiddle.0 == tw(block as int),
                        target == layer_map(prev, m, h, tw, false),
                        sweep_inv(data@, prev, target, m, h, block as int, row as int, lane as int),
                {
                    proof {
                        lemma_sweep_index(nb, h, m, block as int, row as int, lane as int);
                    }
                    let ghost d0 = data@;
                    let v = data[off_bot + lane];
                    let new_u = data[off_top + lane] + v * twiddle;
                    data[off_top + lane] = new_u;
                    data[off_bot + lane] = v + new_u;
                    proof {
                        lemma_sweep_step(d0, data@, prev, m, h, nb, tw, false, block as int, row as int, lane as int);
                    }
                }
                proof {
                    lemma_sweep_lane_end(data@, prev, target, m, h, block as int, row as int);
                }
            }
            proof {
                lemma_sweep_row_end(data@, prev, target, m, h, block as int);
            }
        }
        proof {
            lemma_sweep_end(data@, prev, target, m, h, nb);
        }
    }
    proof {
        assert forall|k: nat| orig.len() == num_ntts * pow2(k) implies k == log_d by {
            lemma_div_by_multiple(pow2(k) as int, num_ntts as int);
            assert(num_ntts * pow2(k) == pow2(k) * num_ntts) by (nonlinear_arith);
            lemma_pow2_injective(log_d as nat, k);
        }
    }
}

impl AdditiveNttF64 {
    /// Recover novel-basis coefficients from evaluations with a scalar inverse NTT.
    ///
    /// Rewritten: the `assert!` is a precondition, and `for layer in (0..log_d).rev()` a `while` loop.
    pub fn inverse_transform(&self, data: &mut [F64])
        requires
            self.well_formed(),
            exists|k: nat| old(data).len() == pow2(k) && k <= self.table().len(),
        ensures
            forall|k: nat|
                old(data).len() == #[trigger] pow2(k) ==> final(data)@ == inverse_layers(self.table(), old(data)@, 1, k, 0),
    {
        let ghost tab = self.table();
        let ghost orig = data@;
        let ghost k0 = choose|k: nat| data.len() == pow2(k) && k <= self.table().len();
        let log_d = log2_strict_usize(data.len());
        proof {
            lemma_pow2_injective(log_d as nat, k0);
        }
        let mut next = log_d;
        while next > 0
            invariant
                self.well_formed(),
                tab == self.table(),
                log_d <= tab.len(),
                next <= log_d,
                data.len() == pow2(log_d as nat),
                data@ == inverse_layers(tab, orig, 1, log_d as nat, next as nat),
            decreases next,
        {
            let layer = next - 1;
            let ghost h = layer_half(log_d as nat, layer as nat);
            let ghost nb = pow2(layer as nat);
            proof {
                lemma_layer_shape(log_d as nat, layer as nat, 1);
                lemma_usize_pow2_no_overflow(layer as nat);
                lemma_usize_pow2_no_overflow((log_d - layer - 1) as nat);
                lemma_usize_shl_is_mul(1, layer);
                lemma_usize_shl_is_mul(1, (log_d - layer - 1) as usize);
            }
            let num_blocks = 1usize << layer;
            let block_size_half = 1usize << (log_d - layer - 1);
            let ghost prev = data@;
            let ghost tw = layer_twiddles(tab, layer as nat);
            let ghost target = layer_map(prev, 1, h, tw, true);
            proof {
                lemma_sweep_start(prev, target, 1, h);
            }
            for block in 0..num_blocks
                invariant
                    self.well_formed(),
                    tab == self.table(),
                    layer < log_d <= tab.len(),
                    h > 0,
                    num_blocks == nb,
                    block_size_half == h,
                    block_size_half == 1usize << ((log_d - layer - 1) as usize),
                    pow2((log_d - layer) as nat) == 2 * h,
                    data.len() == prev.len(),
                    prev.len() == nb * (2 * h) * 1,
                    tw == layer_twiddles(tab, layer as nat),
                    target == layer_map(prev, 1, h, tw, true),
                    sweep_inv(data@, prev, target, 1, h, block as int, 0, 0),
            {
                let twiddle = self.twiddle(layer, block);
                proof {
                    lemma_sweep_index(nb, h, 1, block as int, 0, 0);
                    lemma_usize_shl_is_mul(block, (log_d - layer) as usize);
                }
                let block_start = block << (log_d - layer);
                for idx0 in block_start..(block_start + block_size_half)
                    invariant
                        h > 0,
                        block < nb,
                        layer < log_d <= 63,
                        block_size_half == h,
                        block_size_half == 1usize << ((log_d - layer - 1) as usize),
                        block_start == block * (2 * h),
                        block_start == block << ((log_d - layer) as usize),
                        data.len() == prev.len(),
                        prev.len() == nb * (2 * h) * 1,
                        twiddle.0 == tw(block as int),
                        target == layer_map(prev, 1, h, tw, true),
                        block_start <= idx0,
                        sweep_inv(data@, prev, target, 1, h, block as int, idx0 - block_start, 0),
                {
                    let ghost row = idx0 - block_start;
                    proof {
                        lemma_sweep_index(nb, h, 1, block as int, row, 0);
                        lemma_or_is_add(block, row as usize, (log_d - layer) as usize);
                    }
                    let idx1 = idx0 | block_size_half;
                    let ghost d0 = data@;
                    let u = data[idx0];
                    let new_v = data[idx1] + u;
                    data[idx1] = new_v;
                    data[idx0] = u + new_v * twiddle;
                    proof {
                        lemma_sweep_step(d0, data@, prev, 1, h, nb, tw, true, block as int, row, 0);
                        lemma_sweep_lane_end(data@, prev, target, 1, h, block as int, row);
                    }
                }
                proof {
                    lemma_sweep_row_end(data@, prev, target, 1, h, block as int);
                }
            }
            proof {
                lemma_sweep_end(data@, prev, target, 1, h, nb);
            }
            next = layer;
        }
        proof {
            assert forall|k: nat| orig.len() == pow2(k) implies k == log_d by {
                lemma_pow2_injective(log_d as nat, k);
            }
        }
    }
}

proof fn lemma_or_is_add(block: usize, j: usize, s: usize)
    requires
        1 <= s < 64,
        j < (1usize << ((s - 1) as usize)),
        (block << s) as int + j + (1usize << ((s - 1) as usize)) <= usize::MAX,
    ensures
        (((block << s) + j) as usize) | (1usize << ((s - 1) as usize)) == (block << s) + j + (1usize << ((s
            - 1) as usize)),
{
    let x = block << s;
    let hb = 1usize << ((s - 1) as usize);
    assert(((x + j) as usize) | hb == ((x + j) as usize) + hb) by (bit_vector)
        requires
            x == block << s,
            hb == 1usize << ((s - 1) as usize),
            1 <= s < 64,
            j < hb,
    ;
}


// ---------------------------------------------------------------------------------------------
// Fused layers on one row group
// ---------------------------------------------------------------------------------------------
/// The twelve butterflies of one radix-8 row group, with its seven twiddles breadth-first.
///
/// Single-lane rows: row `i` is the one word `rows[i]` (a `num_ntts`-lane slice in production), so each
/// `butterfly_lanes(ri, rj, t)` is the one-lane `butterfly_one::<false>(&mut ri, &mut rj, t)`.
///
/// It is three successive layers on the eight rows: rows 4 apart with `t[0]`, then rows 2 apart with
/// `t[1 + half]`, then adjacent rows with `t[3 + quarter]`. With `t = twiddles_radix8(layer, block)` these
/// are the twiddles of `block` at `layer`, of its halves `2 block + h` at `layer + 1`, and of its quarters
/// `4 block + q` at `layer + 2`.
pub fn radix8_butterflies(rows: &mut [F64; 8], t: &[F64; 7])
    ensures
        final(rows)@ == layer_map(
            layer_map(layer_map(old(rows)@, 1, 4, |b: int| t@[0].0, false), 1, 2, |b: int| t@[1 + b].0, false),
            1,
            1,
            |b: int| t@[3 + b].0,
            false,
        ),
{
    let ghost x = rows@;
    // Rewritten from `let [r0, r1, r2, r3, r4, r5, r6, r7] = rows;`: Verus has no slice patterns.
    let (mut r0, mut r1, mut r2, mut r3) = (rows[0], rows[1], rows[2], rows[3]);
    let (mut r4, mut r5, mut r6, mut r7) = (rows[4], rows[5], rows[6], rows[7]);
    // Layer L: rows 4 apart, one twiddle for the whole block.
    butterfly_one::<false>(&mut r0, &mut r4, t[0]);
    butterfly_one::<false>(&mut r1, &mut r5, t[0]);
    butterfly_one::<false>(&mut r2, &mut r6, t[0]);
    butterfly_one::<false>(&mut r3, &mut r7, t[0]);
    let ghost y1 = seq![r0, r1, r2, r3, r4, r5, r6, r7];
    // Layer L+1: rows 2 apart, one twiddle per half.
    butterfly_one::<false>(&mut r0, &mut r2, t[1]);
    butterfly_one::<false>(&mut r1, &mut r3, t[1]);
    butterfly_one::<false>(&mut r4, &mut r6, t[2]);
    butterfly_one::<false>(&mut r5, &mut r7, t[2]);
    let ghost y2 = seq![r0, r1, r2, r3, r4, r5, r6, r7];
    // Layer L+2: adjacent rows, one twiddle per quarter.
    butterfly_one::<false>(&mut r0, &mut r1, t[3]);
    butterfly_one::<false>(&mut r2, &mut r3, t[4]);
    butterfly_one::<false>(&mut r4, &mut r5, t[5]);
    butterfly_one::<false>(&mut r6, &mut r7, t[6]);
    *rows = [r0, r1, r2, r3, r4, r5, r6, r7];
    proof {
        let l1 = layer_map(x, 1, 4, |b: int| t@[0].0, false);
        let l2 = layer_map(l1, 1, 2, |b: int| t@[1 + b].0, false);
        let l3 = layer_map(l2, 1, 1, |b: int| t@[3 + b].0, false);
        lemma_small_rows(8, 4);
        lemma_small_rows(8, 2);
        lemma_small_rows(8, 1);
        assert(l1 =~= y1);
        assert(l2 =~= y2);
        assert(l3 =~= rows@);
    }
}

/// Layers L and L+1 on one group of four single-lane rows: the body of the closure that
/// `butterfly_interleaved_fused_2layer` runs on every row group of a layer-L block.
///
/// It is two successive layers on the four rows: rows 2 apart with `t_outer`, then adjacent rows with
/// `t_inner_a` (first half) and `t_inner_b` (second half).
pub fn radix4_butterflies(rows: &mut [F64; 4], t_outer: F64, t_inner_a: F64, t_inner_b: F64)
    ensures
        final(rows)@ == layer_map(
            layer_map(old(rows)@, 1, 2, |b: int| t_outer.0, false),
            1,
            1,
            |b: int|
                if b == 0 {
                    t_inner_a.0
                } else {
                    t_inner_b.0
                },
            false,
        ),
{
    let ghost x = rows@;
    // Rewritten from `let [row_a, row_b, row_c, row_d] = rows;`: Verus has no slice patterns.
    let (mut row_a, mut row_b, mut row_c, mut row_d) = (rows[0], rows[1], rows[2], rows[3]);
    // Layer L: rows 2 apart, one twiddle for the block.
    butterfly_one::<false>(&mut row_a, &mut row_c, t_outer);
    butterfly_one::<false>(&mut row_b, &mut row_d, t_outer);
    let ghost y1 = seq![row_a, row_b, row_c, row_d];
    // Layer L+1: adjacent rows, one twiddle per half.
    butterfly_one::<false>(&mut row_a, &mut row_b, t_inner_a);
    butterfly_one::<false>(&mut row_c, &mut row_d, t_inner_b);
    *rows = [row_a, row_b, row_c, row_d];
    proof {
        let l1 = layer_map(x, 1, 2, |b: int| t_outer.0, false);
        let l2 = layer_map(
            l1,
            1,
            1,
            |b: int|
                if b == 0 {
                    t_inner_a.0
                } else {
                    t_inner_b.0
                },
            false,
        );
        lemma_small_rows(4, 2);
        lemma_small_rows(4, 1);
        assert(l1 =~= y1);
        assert(l2 =~= rows@);
    }
}

/// Block and in-block row of every row of a single-lane group of `n <= 8` rows.
proof fn lemma_small_rows(n: int, h: nat)
    requires
        0 < n <= 8,
        h == 1 || h == 2 || h == 4,
    ensures
        forall|p: int|
            0 <= p < n ==> #[trigger] blk_of(p, 1, h) == p / (2 * h as int) && r_of(p, 1, h) == p % (2 * h as int),
{
    assert forall|p: int| 0 <= p < n implies #[trigger] blk_of(p, 1, h) == p / (2 * h as int) && r_of(p, 1, h) == p
        % (2 * h as int) by {
        assert(row_of(p, 1) == p);
    }
}


// ---------------------------------------------------------------------------------------------
// The forward transform evaluates the novel-basis polynomial
// ---------------------------------------------------------------------------------------------
/// The novel-basis polynomial with coefficients `a` (`2^d` of them), split at level `i` and residue `l`,
/// evaluated at `x`:
///
/// `novel_eval(i, l, x) = Σ_{j < 2^(d-i)} a[l + 2^i j] · Π_{c < d-i} Ŵ_(i+c)(x)^(bit_c(j))`,
///
/// written by its even-odd split on the lowest bit of `j` (annex `d`, Lemma "Even-odd refinement"):
/// `novel_eval(i, l, x) = novel_eval(i+1, l, x) + Ŵ_i(x) · novel_eval(i+1, l + 2^i, x)`.
/// The polynomial itself is `P(x) = novel_eval(0, 0, x) = Σ_j a_j X_j(x)` with `X_j = Π_i Ŵ_i^(bit_i(j))`;
/// [`lemma_novel_eval_flat`] proves this equality with the flat sum [`novel_sum`].
pub open spec fn novel_eval(basis: Seq<F64>, a: Seq<F64>, d: nat, i: nat, l: int, x: u64) -> u64
    decreases d - i,
{
    if i >= d {
        a[l].0
    } else {
        novel_eval(basis, a, d, i + 1, l, x) ^ k_mul(
            normalized_subspace_poly(basis, i, x),
            novel_eval(basis, a, d, i + 1, l + pow2(i), x),
        )
    }
}

/// `novel_eval` at level `i` reads `x` only through `Ŵ_j(x)` for `j >= i`.
proof fn lemma_novel_eval_congruent(basis: Seq<F64>, a: Seq<F64>, d: nat, i: nat, l: int, x: u64, y: u64)
    requires
        forall|j: nat| i <= j < d ==> normalized_subspace_poly(basis, j, x) == normalized_subspace_poly(basis, j, y),
    ensures
        novel_eval(basis, a, d, i, l, x) == novel_eval(basis, a, d, i, l, y),
    decreases d - i,
{
    if i < d {
        lemma_novel_eval_congruent(basis, a, d, i + 1, l, x, y);
        lemma_novel_eval_congruent(basis, a, d, i + 1, l + pow2(i), x, y);
    }
}

proof fn lemma_bit_shr(v: usize, n: usize, c: usize)
    requires
        n + c < 64,
    ensures
        ((v >> n) >> c) & 1 == (v >> ((n + c) as usize)) & 1,
        (v >> n) >> 1usize == v >> ((n + 1) as usize),
{
    assert(((v >> n) >> c) & 1 == (v >> ((n + c) as usize)) & 1 && (v >> n) >> 1usize == v >> ((n + 1) as usize))
        by (bit_vector)
        requires
            n + c < 64,
    ;
}

/// A subset sum over a concatenation: the second part reads the index shifted past the first.
proof fn lemma_span_concat(s1: Seq<F64>, s2: Seq<F64>, v: usize)
    requires
        s1.len() + s2.len() <= 64,
    ensures
        span(s1 + s2, v) == span(s1, v) ^ span(s2, v >> (s1.len() as usize)),
    decreases s2.len(),
{
    let n1 = s1.len() as usize;
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
        lemma_xor_facts(span(s1, v), 0, 0);
    } else {
        let s = s1 + s2;
        lemma_span_concat(s1, s2.drop_last(), v);
        assert(s.drop_last() =~= s1 + s2.drop_last());
        assert(s.last() == s2.last());
        let c = (s2.len() - 1) as usize;
        lemma_bit_shr(v, n1, c);
        let sel = if idx_bit(v, (s.len() - 1) as nat) {
            s.last().0
        } else {
            0
        };
        lemma_xor_facts(span(s1, v), span(s2.drop_last(), v >> n1), sel);
    }
}

/// The point of index `v` splits at basis element `i`: the low part, `b_i` if bit `i` is set, and the part
/// above, which reads `v >> (i + 1)`.
proof fn lemma_span_split(basis: Seq<F64>, i: nat, v: usize)
    requires
        i < basis.len() <= 63,
    ensures
        span(basis, v) == span(basis.take(i as int), v) ^ ((if idx_bit(v, i) {
            basis[i as int].0
        } else {
            0
        }) ^ span(basis.skip((i + 1) as int), v >> ((i + 1) as usize))),
{
    let (lo, hi) = (basis.take(i as int), basis.skip(i as int));
    assert(lo + hi =~= basis);
    lemma_span_concat(lo, hi, v);
    let w = v >> (i as usize);
    let one = seq![basis[i as int]];
    assert(one + basis.skip((i + 1) as int) =~= hi);
    lemma_span_concat(one, basis.skip((i + 1) as int), w);
    lemma_bit_shr(v, i as usize, 0);
    assert(one.drop_last().len() == 0);
    assert(span(one.drop_last(), w) == 0);
    assert(one.last() == basis[i as int]);
    assert(w >> 0usize == w) by (bit_vector);
    let sel = if idx_bit(v, i) {
        basis[i as int].0
    } else {
        0
    };
    assert(span(one, w) == 0 ^ sel);
    lemma_xor_facts(sel, 0, 0);
}

/// `Ŵ_j` of a point, `j > i`, reads only the bits above `i`.
proof fn lemma_point_above(basis: Seq<F64>, i: nat, j: nat, v: usize)
    requires
        i < j < basis.len() <= 63,
    ensures
        normalized_subspace_poly(basis, j, span(basis, v)) == normalized_subspace_poly(
            basis,
            j,
            span(basis.skip((i + 1) as int), v >> ((i + 1) as usize)),
        ),
{
    lemma_span_split(basis, i, v);
    let lo = span(basis.take(i as int), v);
    let sel = if idx_bit(v, i) {
        basis[i as int].0
    } else {
        0
    };
    let hi = span(basis.skip((i + 1) as int), v >> ((i + 1) as usize));
    lemma_normalized_additive(basis, j, lo, sel ^ hi);
    lemma_normalized_additive(basis, j, sel, hi);
    let c = k_inv(subspace_poly(basis, j, basis[j as int].0));
    lemma_subspace_poly_kills_prefix(basis, j, basis.take(i as int), v);
    lemma_k_mul_zero(c);
    if idx_bit(v, i) {
        lemma_subspace_poly_vanishes(basis, j, i);
    }
    lemma_xor_facts(normalized_subspace_poly(basis, j, hi), 0, 0);
}

/// `Ŵ_i` of a point is bit `i` of its index plus `Ŵ_i` of the part above, if `Ŵ_i(b_i) = 1`.
proof fn lemma_point_at(basis: Seq<F64>, i: nat, v: usize)
    requires
        i < basis.len() <= 63,
        normalized_subspace_poly(basis, i, basis[i as int].0) == 1,
    ensures
        normalized_subspace_poly(basis, i, span(basis, v)) == (if idx_bit(v, i) {
            1u64
        } else {
            0u64
        }) ^ normalized_subspace_poly(basis, i, span(basis.skip((i + 1) as int), v >> ((i + 1) as usize))),
{
    lemma_span_split(basis, i, v);
    let lo = span(basis.take(i as int), v);
    let sel = if idx_bit(v, i) {
        basis[i as int].0
    } else {
        0
    };
    let hi = span(basis.skip((i + 1) as int), v >> ((i + 1) as usize));
    lemma_normalized_additive(basis, i, lo, sel ^ hi);
    lemma_normalized_additive(basis, i, sel, hi);
    let c = k_inv(subspace_poly(basis, i, basis[i as int].0));
    lemma_subspace_poly_kills_prefix(basis, i, basis.take(i as int), v);
    lemma_k_mul_zero(c);
    lemma_xor_facts(normalized_subspace_poly(basis, i, sel ^ hi), 0, 0);
}

/// Bit `i` of `v` against `v mod 2^(i+1)`.
proof fn lemma_bit_mod(v: usize, i: nat)
    requires
        i < 63,
    ensures
        v as int % pow2(i + 1) as int == (if idx_bit(v, i) {
            pow2(i) as int
        } else {
            0
        }) + v as int % pow2(i) as int,
        (v as int % pow2(i) as int) < pow2(i),
        (v >> ((i + 1) as usize)) == v as int / pow2(i + 1) as int,
{
    lemma_pow2_pos(i);
    lemma_pow2_unfold(i + 1);
    lemma_usize_shr_is_div(v, i as usize);
    lemma_usize_shr_is_div(v, (i + 1) as usize);
    lemma_mod_breakdown(v as int, pow2(i) as int, 2);
    lemma_mod_pos_bound(v as int, pow2(i) as int);
    let w = v >> (i as usize);
    assert(w & 1 == 1 <==> w % 2 == 1) by (bit_vector);
    assert(pow2(i + 1) == pow2(i) * 2) by (nonlinear_arith)
        requires
            pow2(i + 1) == 2 * pow2(i),
    ;
    let q = v as int / pow2(i) as int;
    assert(w as int == q);
    lemma_mod_pos_bound(q, 2);
    let y = pow2(i) as int;
    if idx_bit(v, i) {
        assert(q % 2 == 1);
        assert(y * (q % 2) == y);
    } else {
        assert(q % 2 == 0);
        assert(y * (q % 2) == 0);
    }
}

/// After `k` forward layers (code layers `0..k`) of a full single-lane transform, word `v` holds the
/// level-`L - k` part of the polynomial at its point: the annex's invariant, with `i = L - k`.
proof fn lemma_forward_invariant(tab: Seq<Seq<F64>>, basis: Seq<F64>, a: Seq<F64>, k: nat)
    requires
        AdditiveNttF64::is_table_of(tab, basis),
        1 <= basis.len() <= 63,
        a.len() == pow2(basis.len()),
        forall|i: nat| i < basis.len() ==> normalized_subspace_poly(basis, i, #[trigger] basis[i as int].0) == 1,
        k <= basis.len(),
    ensures
        ({
            let ll = basis.len();
            let y = forward_layers(tab, a, 1, ll, 0, k);
            &&& y.len() == a.len()
            &&& forall|v: int|
                0 <= v < a.len() ==> (#[trigger] y[v]).0 == novel_eval(
                    basis,
                    a,
                    ll,
                    (ll - k) as nat,
                    v % pow2((ll - k) as nat) as int,
                    span(basis, v as usize),
                )
        }),
    decreases k,
{
    let ll = basis.len();
    lemma_forward_layers_len(tab, a, 1, ll, 0, k);
    if k == 0 {
        assert forall|v: int| 0 <= v < a.len() implies (#[trigger] a[v]).0 == novel_eval(
            basis,
            a,
            ll,
            ll,
            v % pow2(ll) as int,
            span(basis, v as usize),
        ) by {
            lemma_small_mod(v as nat, pow2(ll));
        }
    } else {
        let layer = (k - 1) as nat;
        let i = (ll - k) as nat;
        lemma_forward_invariant(tab, basis, a, layer);
        let y = forward_layers(tab, a, 1, ll, 0, layer);
        let h = layer_half(ll, layer);
        let tw = layer_twiddles(tab, layer);
        let nb = pow2(layer);
        lemma_layer_shape(ll, layer, 1);
        assert(h == pow2(i));
        lemma_pow2_unfold(i + 1);
        lemma2_to64();
        lemma2_to64_rest();
        lemma_pow2_strictly_increases(ll, 64);
        assert forall|v: int| 0 <= v < a.len() implies (#[trigger] forward_layers(tab, a, 1, ll, 0, k)[v]).0
            == novel_eval(basis, a, ll, i, v % pow2(i) as int, span(basis, v as usize)) by {
            lemma_forward_step_word(tab, basis, a, y, ll, layer, i, h, nb, v);
        }
    }
}

/// One word of the inductive step of [`lemma_forward_invariant`].
proof fn lemma_forward_step_word(
    tab: Seq<Seq<F64>>,
    basis: Seq<F64>,
    a: Seq<F64>,
    y: Seq<F64>,
    ll: nat,
    layer: nat,
    i: nat,
    h: nat,
    nb: nat,
    v: int,
)
    requires
        AdditiveNttF64::is_table_of(tab, basis),
        ll == basis.len(),
        1 <= ll <= 63,
        layer < ll,
        i == ll - layer - 1,
        h == pow2(i),
        h == layer_half(ll, layer),
        nb == pow2(layer),
        pow2(i + 1) == 2 * h,
        a.len() == pow2(ll),
        a.len() < pow2(64),
        pow2(64) == 0x1_0000_0000_0000_0000,
        nb * (2 * h) * 1 == 1 * pow2(ll),
        forall|i0: nat| i0 < ll ==> normalized_subspace_poly(basis, i0, #[trigger] basis[i0 as int].0) == 1,
        y == forward_layers(tab, a, 1, ll, 0, layer),
        y.len() == a.len(),
        forall|w: int|
            0 <= w < a.len() ==> (#[trigger] y[w]).0 == novel_eval(
                basis,
                a,
                ll,
                i + 1,
                w % pow2(i + 1) as int,
                span(basis, w as usize),
            ),
        0 <= v < a.len(),
    ensures
        forward_layers(tab, a, 1, ll, 0, layer + 1)[v].0 == novel_eval(
            basis,
            a,
            ll,
            i,
            v % pow2(i) as int,
            span(basis, v as usize),
        ),
{
    let tw = layer_twiddles(tab, layer);
    let z = forward_layers(tab, a, 1, ll, 0, layer + 1);
    assert(z == layer_map(y, 1, h, tw, false));
    lemma_decompose(v, 1, h);
    lemma_blk_bound(v, 1, h, nb);
    let (b, r) = (blk_of(v, 1, h), r_of(v, 1, h));
    assert(row_of(v, 1) == v);
    // The twiddle of the block is `Ŵ_i` of the block's point.
    lemma_twiddle_is_subspace_poly(tab, basis, layer, b as usize);
    let t = tw(b);
    let ell = v % pow2(i) as int;
    // The pair of `v`: the top word `p` and the bottom word `q = p + h`, of the same block.
    let (p, q) = if r < h {
        (v, v + h)
    } else {
        (v - h, v)
    };
    let rp = if r < h {
        r
    } else {
        r - h
    };
    lemma_compose(b, rp, 0, 1, h);
    lemma_compose(b, rp + h, 0, 1, h);
    lemma_bound(b, rp + h, 0, 1, h, nb);
    assert((b * (2 * h) + rp) * 1 + 0 == p) by (nonlinear_arith)
        requires
            v == (b * (2 * h) + r) * 1 + 0,
            p == (if r < h { v } else { v - h }),
            rp == (if r < h { r } else { r - h }),
    ;
    assert((b * (2 * h) + (rp + h)) * 1 + 0 == q) by (nonlinear_arith)
        requires
            p == (b * (2 * h) + rp) * 1 + 0,
            q == p + h,
    ;
    // Bit `i` of the two indices, and their residues.
    lemma_bit_mod(p as usize, i);
    lemma_bit_mod(q as usize, i);
    lemma_bit_mod(v as usize, i);
    lemma_fundamental_div_mod_converse(p, (2 * h) as int, b, rp);
    lemma_fundamental_div_mod_converse(q, (2 * h) as int, b, rp + h);
    assert(!idx_bit(p as usize, i));
    assert(idx_bit(q as usize, i));
    assert(p % pow2(i) as int == ell && q % pow2(i) as int == ell);
    assert(p % pow2(i + 1) as int == ell && q % pow2(i + 1) as int == ell + pow2(i));
    // Both points agree on every `Ŵ_j`, `j > i`, and differ by one on `Ŵ_i`.
    let hi = span(basis.skip((i + 1) as int), b as usize);
    assert((p as usize) >> ((i + 1) as usize) == b as usize && (q as usize) >> ((i + 1) as usize) == b as usize);
    let (xp, xq, xv) = (span(basis, p as usize), span(basis, q as usize), span(basis, v as usize));
    lemma_point_at(basis, i, p as usize);
    lemma_point_at(basis, i, q as usize);
    assert forall|j: nat| i + 1 <= j < ll implies normalized_subspace_poly(basis, j, xp) == normalized_subspace_poly(
        basis,
        j,
        xv,
    ) && normalized_subspace_poly(basis, j, xq) == normalized_subspace_poly(basis, j, xv) by {
        lemma_point_above(basis, i, j, p as usize);
        lemma_point_above(basis, i, j, q as usize);
        lemma_point_above(basis, i, j, v as usize);
    }
    lemma_novel_eval_congruent(basis, a, ll, i + 1, ell, xp, xv);
    lemma_novel_eval_congruent(basis, a, ll, i + 1, ell + pow2(i), xq, xv);
    let lo_part = novel_eval(basis, a, ll, i + 1, ell, xv);
    let hi_part = novel_eval(basis, a, ll, i + 1, ell + pow2(i), xv);
    assert(y[p].0 == lo_part && y[q].0 == hi_part);
    assert(normalized_subspace_poly(basis, i, xp) == t) by {
        lemma_xor_facts(t, 0, 0);
    }
    lemma_k_mul_comm(hi_part, t);
    lemma_k_mul_comm(hi_part, t ^ 1);
    lemma_butterfly_evaluates(lo_part, hi_part, t);
    if r < h {
        assert(z[v].0 == bf_top(y[p].0, y[q].0, t));
    } else {
        assert(normalized_subspace_poly(basis, i, xv) == 1 ^ t);
        assert(1u64 ^ t == t ^ 1u64) by (bit_vector);
        assert(z[v].0 == bf_bot(y[p].0, y[q].0, t));
    }
}

/// The forward transform evaluates the novel-basis polynomial on the subspace domain.
///
/// On one lane of `2^L` words, `L` the table's dimension, word `v` of the output is
/// `P(x_v) = Σ_j a_j X_j(x_v)` (see [`novel_eval`]), where `a` is the input read as novel-basis
/// coefficients and `x_v = Σ_c bit_c(v) b_c` the point of index `v`, bit 0 first (no bit reversal).
///
/// Hypothesis: every normalizer works, `Ŵ_i(b_i) = 1`, i.e. every row of the table starts with one
/// (`tab[i][0] = 1`); it holds when every `s_i(b_i)` is nonzero. [`lemma_standard_rows_start_with_one`]
/// discharges it for the standard basis.
pub proof fn lemma_forward_evaluates(tab: Seq<Seq<F64>>, basis: Seq<F64>, a: Seq<F64>)
    requires
        AdditiveNttF64::is_table_of(tab, basis),
        1 <= basis.len() <= 63,
        a.len() == pow2(basis.len()),
        forall|i: nat| i < basis.len() ==> normalized_subspace_poly(basis, i, #[trigger] basis[i as int].0) == 1,
    ensures
        forall|v: int|
            0 <= v < a.len() ==> (#[trigger] forward_layers(tab, a, 1, basis.len(), 0, basis.len())[v]).0
                == novel_eval(basis, a, basis.len(), 0, 0, span(basis, v as usize)),
{
    lemma_forward_invariant(tab, basis, a, basis.len());
    lemma2_to64();
}


// ---------------------------------------------------------------------------------------------
// Reed-Solomon encoding at a rate
// ---------------------------------------------------------------------------------------------
/// The message followed by zeros, `n` words.
pub open spec fn zero_pad(msg: Seq<F64>, n: nat) -> Seq<F64> {
    Seq::new(
        n,
        |v: int|
            if v < msg.len() {
                msg[v]
            } else {
                F64(0)
            },
    )
}

/// `n` words of copies of the message, back to back.
pub open spec fn replicate(msg: Seq<F64>, n: nat) -> Seq<F64> {
    Seq::new(n, |v: int| msg[v % msg.len() as int])
}

/// Layers `0..e` are layers `0..r` followed by layers `r..e`.
pub proof fn lemma_forward_layers_split(tab: Seq<Seq<F64>>, x: Seq<F64>, m: nat, log_d: nat, r: nat, e: nat)
    requires
        r <= e,
    ensures
        forward_layers(tab, forward_layers(tab, x, m, log_d, 0, r), m, log_d, r, e) == forward_layers(
            tab,
            x,
            m,
            log_d,
            0,
            e,
        ),
    decreases e,
{
    if e > r {
        lemma_forward_layers_split(tab, x, m, log_d, r, (e - 1) as nat);
    }
}

/// The first `k <= r` layers on a zero-padded message of `2^(L-r)` words leave word `v` equal to the
/// padded word `v mod 2^(L-k)`: a butterfly whose bottom input is zero copies its top input to both outputs.
proof fn lemma_zero_pad_replicates(tab: Seq<Seq<F64>>, msg: Seq<F64>, ll: nat, r: nat, k: nat)
    requires
        r <= ll,
        k <= r,
        msg.len() == pow2((ll - r) as nat),
    ensures
        ({
            let x = zero_pad(msg, pow2(ll));
            let y = forward_layers(tab, x, 1, ll, 0, k);
            &&& y.len() == x.len()
            &&& forall|v: int| 0 <= v < y.len() ==> #[trigger] y[v] == x[v % pow2((ll - k) as nat) as int]
        }),
    decreases k,
{
    let x = zero_pad(msg, pow2(ll));
    lemma_forward_layers_len(tab, x, 1, ll, 0, k);
    if k == 0 {
        assert forall|v: int| 0 <= v < x.len() implies #[trigger] x[v] == x[v % pow2(ll) as int] by {
            lemma_small_mod(v as nat, pow2(ll));
        }
    } else {
        let layer = (k - 1) as nat;
        lemma_zero_pad_replicates(tab, msg, ll, r, layer);
        let y = forward_layers(tab, x, 1, ll, 0, layer);
        let h = layer_half(ll, layer);
        let nb = pow2(layer);
        let tw = layer_twiddles(tab, layer);
        lemma_layer_shape(ll, layer, 1);
        assert(h == pow2((ll - k) as nat));
        if (ll - k) as nat > (ll - r) as nat {
            lemma_pow2_strictly_increases((ll - r) as nat, (ll - k) as nat);
        }
        let z = forward_layers(tab, x, 1, ll, 0, k);
        assert(z == layer_map(y, 1, h, tw, false));
        assert forall|v: int| 0 <= v < z.len() implies #[trigger] z[v] == x[v % h as int] by {
            lemma_decompose(v, 1, h);
            lemma_blk_bound(v, 1, h, nb);
            let (b, rr) = (blk_of(v, 1, h), r_of(v, 1, h));
            assert(row_of(v, 1) == v);
            let t = tw(b);
            if rr < h {
                let q = v + h;
                lemma_compose(b, rr + h, 0, 1, h);
                lemma_bound(b, rr + h, 0, 1, h, nb);
                assert((b * (2 * h) + (rr + h)) * 1 + 0 == q) by (nonlinear_arith)
                    requires
                        v == (b * (2 * h) + rr) * 1 + 0,
                        q == v + h,
                ;
                lemma_fundamental_div_mod_converse(q, (2 * h) as int, b, rr + h);
                lemma_fundamental_div_mod_converse(v, (2 * h) as int, b, rr);
                assert(y[q] == F64(0));
                lemma_k_mul_zero(t);
                lemma_xor_facts(y[v].0, 0, 0);
                assert(v == (2 * b) * h + rr) by (nonlinear_arith)
                    requires
                        v == (b * (2 * h) + rr) * 1 + 0,
                ;
                lemma_fundamental_div_mod_converse(v, h as int, 2 * b, rr);
            } else {
                let p = v - h;
                lemma_compose(b, rr - h, 0, 1, h);
                assert((b * (2 * h) + (rr - h)) * 1 + 0 == p) by (nonlinear_arith)
                    requires
                        v == (b * (2 * h) + rr) * 1 + 0,
                        p == v - h,
                ;
                lemma_fundamental_div_mod_converse(p, (2 * h) as int, b, rr - h);
                lemma_fundamental_div_mod_converse(v, (2 * h) as int, b, rr);
                assert(y[v] == F64(0));
                lemma_k_mul_zero(t);
                lemma_xor_facts(y[p].0, 0, 0);
                assert(v == (2 * b + 1) * h + (rr - h)) by (nonlinear_arith)
                    requires
                        v == (b * (2 * h) + rr) * 1 + 0,
                ;
                lemma_fundamental_div_mod_converse(v, h as int, 2 * b + 1, rr - h);
            }
        }
    }
}

/// The encoder at rate `2^-r`: the layers `r..L` on `2^r` copies of a message of `2^(L-r)` words give the
/// evaluations, on the whole `2^L`-point domain, of the novel-basis polynomial whose coefficients are the
/// message (degree below `2^(L-r)`). So the codeword is the Reed-Solomon encoding of the message.
///
/// Same hypothesis as [`lemma_forward_evaluates`]: every row of the table starts with one.
pub proof fn lemma_encode_evaluates(tab: Seq<Seq<F64>>, basis: Seq<F64>, msg: Seq<F64>, r: nat)
    requires
        AdditiveNttF64::is_table_of(tab, basis),
        1 <= basis.len() <= 63,
        r <= basis.len(),
        msg.len() == pow2((basis.len() - r) as nat),
        forall|i: nat| i < basis.len() ==> normalized_subspace_poly(basis, i, #[trigger] basis[i as int].0) == 1,
    ensures
        ({
            let ll = basis.len();
            let codeword = forward_layers(tab, replicate(msg, pow2(ll)), 1, ll, r, ll);
            &&& codeword.len() == pow2(ll)
            &&& forall|v: int|
                0 <= v < pow2(ll) ==> (#[trigger] codeword[v]).0 == novel_eval(
                    basis,
                    zero_pad(msg, pow2(ll)),
                    ll,
                    0,
                    0,
                    span(basis, v as usize),
                )
        }),
{
    let ll = basis.len();
    let x = zero_pad(msg, pow2(ll));
    let rep = replicate(msg, pow2(ll));
    lemma_zero_pad_replicates(tab, msg, ll, r, r);
    lemma_pow2_pos((ll - r) as nat);
    if r > 0 {
        lemma_pow2_strictly_increases((ll - r) as nat, ll);
    }
    assert forall|v: int| 0 <= v < pow2(ll) implies x[v % pow2((ll - r) as nat) as int] == rep[v] by {
        lemma_mod_pos_bound(v, pow2((ll - r) as nat) as int);
    }
    assert(forward_layers(tab, x, 1, ll, 0, r) =~= rep);
    lemma_forward_layers_split(tab, x, 1, ll, r, ll);
    lemma_forward_layers_len(tab, rep, 1, ll, r, ll);
    lemma_forward_evaluates(tab, basis, x);
}


// ---------------------------------------------------------------------------------------------
// The standard basis: every row of the table starts with one
// ---------------------------------------------------------------------------------------------
/// `K` has no zero divisors.
pub proof fn lemma_k_no_zero_divisors(a: u64, b: u64)
    requires
        k_mul(a, b) == 0,
        a != 0,
    ensures
        b == 0,
{
    let ai = k_pow(a, (pow2(64) - 2) as nat);
    lemma_k_inverse(a);
    lemma_k_mul_comm(a, ai);
    lemma_k_mul_assoc(ai, a, b);
    lemma_k_mul_one(b);
    lemma_k_mul_zero(ai);
}

proof fn lemma_below_pow(x: u64, k: u64)
    requires
        k < 63,
    ensures
        x < (1u64 << k) ==> x < (1u64 << ((k + 1) as u64)),
        (x ^ (1u64 << k)) < (1u64 << k) ==> x < (1u64 << ((k + 1) as u64)),
        !((1u64 << ((k + 1) as u64)) < (1u64 << ((k + 1) as u64))),
{
    assert((x < (1u64 << k) ==> x < (1u64 << ((k + 1) as u64))) && ((x ^ (1u64 << k)) < (1u64 << k) ==> x < (1u64
        << ((k + 1) as u64)))) by (bit_vector)
        requires
            k < 63,
    ;
}

/// The roots of `s_i` for the standard basis lie below `2^i`: `s_i(x) = 0` only on `{0, .., 2^i - 1}`.
pub proof fn lemma_standard_roots(dim: nat, i: nat, x: u64)
    requires
        i <= dim <= 63,
        subspace_poly(standard_basis(dim), i, x) == 0,
    ensures
        x < (1u64 << (i as u64)),
    decreases i,
{
    let basis = standard_basis(dim);
    if i == 0 {
        assert(x == 0);
        assert(0u64 < (1u64 << 0u64)) by (bit_vector);
    } else {
        let j = (i - 1) as nat;
        let b = basis[j as int].0;
        assert(b == 1u64 << (j as u64));
        let p = subspace_poly(basis, j, x);
        let c = subspace_poly(basis, j, b);
        lemma_below_pow(x, j as u64);
        if p == 0 {
            lemma_standard_roots(dim, j, x);
        } else {
            lemma_k_no_zero_divisors(p, p ^ c);
            lemma_subspace_poly_additive(basis, j, x, b);
            lemma_standard_roots(dim, j, x ^ b);
        }
    }
}

/// For the standard basis every normalizer works: `Ŵ_i(b_i) = 1`, so every row of the table starts with one.
pub proof fn lemma_standard_rows_start_with_one(dim: nat)
    requires
        dim <= 63,
    ensures
        forall|i: nat|
            i < dim ==> normalized_subspace_poly(standard_basis(dim), i, #[trigger] standard_basis(dim)[i as int].0)
                == 1,
{
    assert forall|i: nat| i < dim implies normalized_subspace_poly(
        standard_basis(dim),
        i,
        #[trigger] standard_basis(dim)[i as int].0,
    ) == 1 by {
        let basis = standard_basis(dim);
        let y = subspace_poly(basis, i, basis[i as int].0);
        assert(basis[i as int].0 == 1u64 << (i as u64));
        if y == 0 {
            lemma_standard_roots(dim, i, basis[i as int].0);
            let k = i as u64;
            assert(!((1u64 << k) < (1u64 << k))) by (bit_vector);
        }
        lemma_k_inverse(y);
    }
}

/// The point of index `v` in the standard basis is `v` itself: the domain is `{0, .., 2^dim - 1}` under the
/// natural integer encoding.
pub proof fn lemma_standard_point(n: nat, v: usize)
    requires
        n <= 63,
        v < pow2(n),
    ensures
        span(standard_basis(n), v) == v as u64,
{
    lemma_standard_span(n, v);
    let k = n as u64;
    lemma_u64_pow2_no_overflow(n);
    assert(1 * pow2(n) == pow2(n));
    lemma_u64_shl_is_mul(1, k);
    let w = v as u64;
    assert(w < (1u64 << k) ==> w & sub(1u64 << k, 1) == w) by (bit_vector);
}

proof fn lemma_standard_span(n: nat, v: usize)
    requires
        n <= 63,
    ensures
        span(standard_basis(n), v) == (v as u64) & sub(1u64 << (n as u64), 1),
    decreases n,
{
    let w = v as u64;
    if n == 0 {
        assert(w & sub(1u64 << 0u64, 1) == 0) by (bit_vector);
    } else {
        let k = (n - 1) as u64;
        lemma_standard_span((n - 1) as nat, v);
        assert(standard_basis(n).drop_last() =~= standard_basis((n - 1) as nat));
        assert(standard_basis(n).last().0 == 1u64 << k);
        let kk = k as usize;
        assert(((v >> kk) & 1 == 1) == ((w >> k) & 1 == 1)) by (bit_vector)
            requires
                w == v as u64,
                kk == k as usize,
                k < 63,
        ;
        assert(((w >> k) & 1 == 1 ==> (w & sub(1u64 << k, 1)) ^ (1u64 << k) == w & sub(1u64 << ((k + 1) as u64), 1))
            && (!((w >> k) & 1 == 1) ==> (w & sub(1u64 << k, 1)) ^ 0 == w & sub(1u64 << ((k + 1) as u64), 1)))
            by (bit_vector)
            requires
                k < 63,
        ;
    }
}

/// The forward transform of `AdditiveNttF64::standard(dim)` evaluates the novel-basis polynomial on the
/// domain `{0, .., 2^dim - 1}`: output word `v` is `P(v) = Σ_{j < 2^dim} a_j X_j(v)` ([`novel_sum`]), with
/// no hypothesis.
pub proof fn lemma_standard_forward_evaluates(tab: Seq<Seq<F64>>, dim: nat, a: Seq<F64>)
    requires
        AdditiveNttF64::is_table_of(tab, standard_basis(dim)),
        1 <= dim <= 63,
        a.len() == pow2(dim),
    ensures
        forall|v: int|
            0 <= v < a.len() ==> (#[trigger] forward_layers(tab, a, 1, dim, 0, dim)[v]).0 == novel_sum(
                standard_basis(dim),
                a,
                dim,
                v as u64,
            ),
{
    lemma_standard_rows_start_with_one(dim);
    lemma_forward_evaluates(tab, standard_basis(dim), a);
    assert forall|v: int| 0 <= v < a.len() implies novel_eval(standard_basis(dim), a, dim, 0, 0, v as u64) == #[trigger] novel_sum(
        standard_basis(dim),
        a,
        dim,
        v as u64,
    ) by {
        lemma_novel_eval_flat(standard_basis(dim), a, dim, v as u64);
    }
    assert forall|v: int| 0 <= v < a.len() implies #[trigger] span(standard_basis(dim), v as usize) == v as u64 by {
        lemma2_to64();
        lemma2_to64_rest();
        lemma_pow2_strictly_increases(dim, 64);
        lemma_standard_point(dim, v as usize);
    }
}

/// The encoder of `AdditiveNttF64::standard(dim)` at rate `2^-r` is the Reed-Solomon encoding of the
/// message: word `v` of the codeword is `P(v)`, `P` the novel-basis polynomial whose coefficients are the
/// message (degree below `2^(dim - r)`), with no hypothesis.
pub proof fn lemma_standard_encode_evaluates(tab: Seq<Seq<F64>>, dim: nat, msg: Seq<F64>, r: nat)
    requires
        AdditiveNttF64::is_table_of(tab, standard_basis(dim)),
        1 <= dim <= 63,
        r <= dim,
        msg.len() == pow2((dim - r) as nat),
    ensures
        ({
            let codeword = forward_layers(tab, replicate(msg, pow2(dim)), 1, dim, r, dim);
            &&& codeword.len() == pow2(dim)
            &&& forall|v: int|
                0 <= v < pow2(dim) ==> (#[trigger] codeword[v]).0 == novel_sum(
                    standard_basis(dim),
                    zero_pad(msg, pow2(dim)),
                    dim,
                    v as u64,
                )
        }),
{
    lemma_standard_rows_start_with_one(dim);
    lemma_encode_evaluates(tab, standard_basis(dim), msg, r);
    let x = zero_pad(msg, pow2(dim));
    assert forall|v: int| 0 <= v < pow2(dim) implies novel_eval(standard_basis(dim), x, dim, 0, 0, v as u64) == #[trigger] novel_sum(
        standard_basis(dim),
        x,
        dim,
        v as u64,
    ) by {
        lemma_novel_eval_flat(standard_basis(dim), x, dim, v as u64);
    }
    assert forall|v: int| 0 <= v < pow2(dim) implies #[trigger] span(standard_basis(dim), v as usize) == v as u64 by {
        lemma2_to64();
        lemma2_to64_rest();
        lemma_pow2_strictly_increases(dim, 64);
        lemma_standard_point(dim, v as usize);
    }
}


// ---------------------------------------------------------------------------------------------
// The novel-basis polynomial as a flat sum
// ---------------------------------------------------------------------------------------------
/// `XOR_{j < n} f(j)`.
pub open spec fn xor_sum(f: spec_fn(int) -> u64, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        0
    } else {
        xor_sum(f, (n - 1) as nat) ^ f(n - 1)
    }
}

/// `Π_{c < n} Ŵ_(i+c)(x)^(bit_c(j))`, bit `c` of `j` being `(j / 2^c) mod 2`.
pub open spec fn novel_basis_from(basis: Seq<F64>, i: nat, n: nat, j: nat, x: u64) -> u64
    decreases n,
{
    if n == 0 {
        1
    } else {
        k_mul(
            if j % 2 == 1 {
                normalized_subspace_poly(basis, i, x)
            } else {
                1
            },
            novel_basis_from(basis, i + 1, (n - 1) as nat, j / 2, x),
        )
    }
}

/// The novel basis polynomial `X_j(x) = Π_{i < d} Ŵ_i(x)^(bit_i(j))`.
pub open spec fn novel_basis(basis: Seq<F64>, d: nat, j: nat, x: u64) -> u64 {
    novel_basis_from(basis, 0, d, j, x)
}

/// `Σ_{j < 2^(d-i)} a[l + 2^i j] · Π_{c < d-i} Ŵ_(i+c)(x)^(bit_c(j))`.
pub open spec fn novel_sum_from(basis: Seq<F64>, a: Seq<F64>, d: nat, i: nat, l: int, x: u64) -> u64 {
    xor_sum(
        |j: int| k_mul(a[l + pow2(i) * j].0, novel_basis_from(basis, i, (d - i) as nat, j as nat, x)),
        pow2((d - i) as nat),
    )
}

/// The novel-basis polynomial with coefficients `a`, as the flat sum `Σ_{j < 2^d} a_j X_j(x)`.
pub open spec fn novel_sum(basis: Seq<F64>, a: Seq<F64>, d: nat, x: u64) -> u64 {
    xor_sum(|j: int| k_mul(a[j].0, novel_basis(basis, d, j as nat, x)), pow2(d))
}

proof fn lemma_xor_sum_ext(f: spec_fn(int) -> u64, g: spec_fn(int) -> u64, n: nat)
    requires
        forall|j: int| 0 <= j < n ==> #[trigger] f(j) == g(j),
    ensures
        xor_sum(f, n) == xor_sum(g, n),
    decreases n,
{
    if n > 0 {
        lemma_xor_sum_ext(f, g, (n - 1) as nat);
    }
}

/// A sum over `2n` terms is the sum of its even terms plus the sum of its odd terms.
proof fn lemma_xor_sum_split(f: spec_fn(int) -> u64, n: nat)
    ensures
        xor_sum(f, 2 * n) == xor_sum(|j: int| f(2 * j), n) ^ xor_sum(|j: int| f(2 * j + 1), n),
    decreases n,
{
    let fe = |j: int| f(2 * j);
    let fo = |j: int| f(2 * j + 1);
    if n == 0 {
        lemma_xor_facts(0, 0, 0);
    } else {
        lemma_xor_sum_split(f, (n - 1) as nat);
        let (a, b) = (xor_sum(fe, (n - 1) as nat), xor_sum(fo, (n - 1) as nat));
        let (e, o) = (f(2 * n - 2), f(2 * n - 1));
        assert(xor_sum(f, (2 * n - 1) as nat) == xor_sum(f, (2 * (n - 1)) as nat) ^ e);
        assert(xor_sum(f, 2 * n) == xor_sum(f, (2 * (n - 1)) as nat) ^ e ^ o);
        assert((a ^ b) ^ e ^ o == (a ^ e) ^ (b ^ o)) by (bit_vector);
    }
}

/// Multiplication distributes over a sum.
proof fn lemma_xor_sum_scale(c: u64, f: spec_fn(int) -> u64, n: nat)
    ensures
        k_mul(c, xor_sum(f, n)) == xor_sum(|j: int| k_mul(c, f(j)), n),
    decreases n,
{
    if n == 0 {
        lemma_k_mul_zero(c);
    } else {
        lemma_xor_sum_scale(c, f, (n - 1) as nat);
        lemma_k_mul_xor_right(c, xor_sum(f, (n - 1) as nat), f(n - 1));
    }
}

/// `a (w p) = w (a p)`.
proof fn lemma_k_mul_swap(a: u64, w: u64, p: u64)
    ensures
        k_mul(a, k_mul(w, p)) == k_mul(w, k_mul(a, p)),
{
    lemma_k_mul_assoc(a, w, p);
    lemma_k_mul_comm(a, w);
    lemma_k_mul_assoc(w, a, p);
}

proof fn lemma_novel_eval_flat_from(basis: Seq<F64>, a: Seq<F64>, d: nat, i: nat, l: int, x: u64)
    requires
        i <= d,
    ensures
        novel_eval(basis, a, d, i, l, x) == novel_sum_from(basis, a, d, i, l, x),
    decreases d - i,
{
    let n = (d - i) as nat;
    let f = |j: int| k_mul(a[l + pow2(i) * j].0, novel_basis_from(basis, i, n, j as nat, x));
    if i == d {
        lemma2_to64();
        assert(pow2(i) * 0 == 0);
        lemma_k_mul_one(a[l].0);
        lemma_xor_facts(a[l].0, 0, 0);
        assert(xor_sum(f, 0) == 0);
        assert(xor_sum(f, 1) == 0 ^ f(0));
    } else {
        let m = (n - 1) as nat;
        let half = pow2(m);
        let w = normalized_subspace_poly(basis, i, x);
        let li = l + pow2(i);
        lemma_novel_eval_flat_from(basis, a, d, i + 1, l, x);
        lemma_novel_eval_flat_from(basis, a, d, i + 1, li, x);
        let g0 = |j: int| k_mul(a[l + pow2(i + 1) * j].0, novel_basis_from(basis, i + 1, m, j as nat, x));
        let g1 = |j: int| k_mul(a[li + pow2(i + 1) * j].0, novel_basis_from(basis, i + 1, m, j as nat, x));
        assert((d - (i + 1)) as nat == m);
        lemma_pow2_unfold(n);
        lemma_pow2_unfold(i + 1);
        lemma_xor_sum_split(f, half);
        let fe = |j: int| f(2 * j);
        let fo = |j: int| f(2 * j + 1);
        assert forall|j: int| 0 <= j < half implies #[trigger] fe(j) == g0(j) by {
            assert(pow2(i) * (2 * j) == pow2(i + 1) * j) by (nonlinear_arith)
                requires
                    pow2(i + 1) == 2 * pow2(i),
            ;
            assert((2 * j) % 2 == 0 && (2 * j) / 2 == j);
            assert(((2 * j) as nat) / 2 == j as nat);
            lemma_k_mul_one(novel_basis_from(basis, i + 1, m, j as nat, x));
        }
        assert forall|j: int| 0 <= j < half implies #[trigger] fo(j) == k_mul(w, g1(j)) by {
            assert(pow2(i) * (2 * j + 1) == pow2(i) + pow2(i + 1) * j) by (nonlinear_arith)
                requires
                    pow2(i + 1) == 2 * pow2(i),
            ;
            assert((2 * j + 1) % 2 == 1 && (2 * j + 1) / 2 == j);
            assert(((2 * j + 1) as nat) / 2 == j as nat);
            lemma_k_mul_swap(
                a[li + pow2(i + 1) * j].0,
                w,
                novel_basis_from(basis, i + 1, m, j as nat, x),
            );
        }
        lemma_xor_sum_ext(fe, g0, half);
        lemma_xor_sum_ext(fo, |j: int| k_mul(w, g1(j)), half);
        lemma_xor_sum_scale(w, g1, half);
        assert(2 * half == pow2(n));
    }
}

/// The even-odd form is the flat sum: `novel_eval(0, 0, x) = Σ_{j < 2^d} a_j X_j(x)`.
pub proof fn lemma_novel_eval_flat(basis: Seq<F64>, a: Seq<F64>, d: nat, x: u64)
    ensures
        novel_eval(basis, a, d, 0, 0, x) == novel_sum(basis, a, d, x),
{
    lemma_novel_eval_flat_from(basis, a, d, 0, 0, x);
    lemma2_to64();
    let f = |j: int| k_mul(a[0 + pow2(0) * j].0, novel_basis_from(basis, 0, (d - 0) as nat, j as nat, x));
    let g = |j: int| k_mul(a[j].0, novel_basis(basis, d, j as nat, x));
    assert forall|j: int| 0 <= j < pow2(d) implies #[trigger] f(j) == g(j) by {
        assert(0 + pow2(0) * j == j);
    }
    lemma_xor_sum_ext(f, g, pow2(d));
}

} // verus!
