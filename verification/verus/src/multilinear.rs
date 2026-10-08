//! The equality polynomial and its tables over the Boolean cube.
//!
//! The executable functions are the portable paths of `crates/primitives/src/multilinear.rs`, copied with the same
//! bodies where Verus accepts them; `tests/equivalence/multilinear.rs` checks the two agree. Where Verus rejects the
//! production form (iterator chains and `fold`, `as_chunks_mut`, `split_at_mut`, `MaybeUninit` and `set_len`,
//! `[x; N]`, the parallel pass), the copy spells out the same arithmetic in `while`/`for` loops over indices; each
//! such spot says what it replaces.
//!
//! Specification: over `E` ([`e_mul`], [`e_add`]; `1 - a = 1 + a` in characteristic 2),
//!
//! ```text
//!     eq(r, x) = prod_i (r_i x_i + (1 + r_i)(1 + x_i))        ([`eq_poly`], [`eq_factor`])
//! ```
//!
//! and a table over `n` variables holds at index `x` the value at the cube point whose coordinate `i` is bit `i`
//! of `x` (LSB first, [`cube_point`], [`eq_at`]).
use crate::gf2_64::*;
use crate::gf2_64x3::*;
use crate::phi8_tower::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// One coordinate's factor of `eq`: `r x + (1 + r)(1 + x)`.
pub open spec fn eq_factor(r: F192, x: F192) -> F192 {
    e_add(e_mul(r, x), e_mul(e_add(F192::ONE, r), e_add(F192::ONE, x)))
}

/// `eq(r, x) = prod_i eq_factor(r_i, x_i)`, the product taken from the first coordinate up.
pub open spec fn eq_poly(r: Seq<F192>, x: Seq<F192>) -> F192
    decreases r.len(),
{
    if r.len() == 0 {
        F192::ONE
    } else {
        e_mul(eq_poly(r.drop_last(), x.drop_last()), eq_factor(r.last(), x.last()))
    }
}

/// Bit `i` of an index.
pub open spec fn bit(x: usize, i: int) -> bool {
    (x >> (i as usize)) & 1 == 1
}

/// A bit as an element of `E`.
pub open spec fn e_bool(b: bool) -> F192 {
    if b {
        F192::ONE
    } else {
        F192::ZERO
    }
}

/// The point of the cube `{0, 1}^n` at index `x`: coordinate `i` is bit `i` of `x`.
pub open spec fn cube_point(n: nat, x: usize) -> Seq<F192> {
    Seq::new(n, |i: int| e_bool(bit(x, i)))
}

/// `eq(r, x)` at the cube point of index `x`.
pub open spec fn eq_at(r: Seq<F192>, x: usize) -> F192 {
    eq_poly(r, cube_point(r.len(), x))
}

/// `t` is `seed * eq(r, .)`: `2^n` entries, entry `x` being `seed * eq(r, x)`.
pub open spec fn is_eq_table(t: Seq<F192>, r: Seq<F192>, seed: F192) -> bool {
    &&& r.len() < 64
    &&& t.len() == (1usize << r.len())
    &&& forall|x: int| 0 <= x < t.len() ==> #[trigger] t[x] == e_mul(seed, eq_at(r, x as usize))
}

// ---------------------------------------------------------------------------------------------
// Algebra of E used below
// ---------------------------------------------------------------------------------------------
proof fn lemma_xor_ring(a: u64, b: u64, c: u64)
    ensures
        a ^ b == b ^ a,
        (a ^ b) ^ c == a ^ (b ^ c),
        a ^ 0 == a,
        0 ^ a == a,
        a ^ a == 0,
        a ^ (b ^ (c ^ a)) == b ^ c,
{
    assert(a ^ b == b ^ a && (a ^ b) ^ c == a ^ (b ^ c) && a ^ 0 == a && 0 ^ a == a && a ^ a == 0 && a ^ (b ^ (c
        ^ a)) == b ^ c) by (bit_vector);
}

/// `E` under `+`: commutative, associative, zero, every element its own negative.
pub proof fn lemma_e_add(a: F192, b: F192, c: F192)
    ensures
        e_add(a, b) == e_add(b, a),
        e_add(e_add(a, b), c) == e_add(a, e_add(b, c)),
        e_add(a, F192::ZERO) == a,
        e_add(F192::ZERO, a) == a,
        e_add(a, a) == F192::ZERO,
        e_add(a, e_add(b, e_add(c, a))) == e_add(b, c),
{
    lemma_xor_ring(a.c0, b.c0, c.c0);
    lemma_xor_ring(a.c1, b.c1, c.c1);
    lemma_xor_ring(a.c2, b.c2, c.c2);
}

pub proof fn lemma_e_mul_zero(a: F192)
    ensures
        e_mul(a, F192::ZERO) == F192::ZERO,
        e_mul(F192::ZERO, a) == F192::ZERO,
{
    lemma_k_mul_zero(a.c0);
    lemma_k_mul_zero(a.c1);
    lemma_k_mul_zero(a.c2);
    assert(0u64 ^ (0u64 ^ 0u64) == 0u64 && (0u64 ^ 0u64) ^ (0u64 ^ 0u64) ^ 0u64 == 0u64 && (0u64 ^ 0u64 ^ 0u64)
        ^ 0u64 == 0u64) by (bit_vector);
}

proof fn lemma_xor_distrib(
    b00: u64, b01: u64, b02: u64, b10: u64, b11: u64, b12: u64, b20: u64, b21: u64, b22: u64,
    c00: u64, c01: u64, c02: u64, c10: u64, c11: u64, c12: u64, c20: u64, c21: u64, c22: u64,
)
    ensures
        (b00 ^ c00) ^ ((b12 ^ c12) ^ (b21 ^ c21)) == (b00 ^ (b12 ^ b21)) ^ (c00 ^ (c12 ^ c21)),
        ((b01 ^ c01) ^ (b10 ^ c10)) ^ ((b12 ^ c12) ^ (b21 ^ c21)) ^ (b22 ^ c22) == ((b01 ^ b10) ^ (b12 ^ b21) ^ b22)
            ^ ((c01 ^ c10) ^ (c12 ^ c21) ^ c22),
        ((b02 ^ c02) ^ (b11 ^ c11) ^ (b20 ^ c20)) ^ (b22 ^ c22) == ((b02 ^ b11 ^ b20) ^ b22) ^ ((c02 ^ c11 ^ c20)
            ^ c22),
{
    assert((b00 ^ c00) ^ ((b12 ^ c12) ^ (b21 ^ c21)) == (b00 ^ (b12 ^ b21)) ^ (c00 ^ (c12 ^ c21))) by (bit_vector);
    assert(((b01 ^ c01) ^ (b10 ^ c10)) ^ ((b12 ^ c12) ^ (b21 ^ c21)) ^ (b22 ^ c22) == ((b01 ^ b10) ^ (b12 ^ b21)
        ^ b22) ^ ((c01 ^ c10) ^ (c12 ^ c21) ^ c22)) by (bit_vector);
    assert(((b02 ^ c02) ^ (b11 ^ c11) ^ (b20 ^ c20)) ^ (b22 ^ c22) == ((b02 ^ b11 ^ b20) ^ b22) ^ ((c02 ^ c11
        ^ c20) ^ c22)) by (bit_vector);
}

/// The product distributes over the sum.
pub proof fn lemma_e_mul_distrib(a: F192, b: F192, c: F192)
    ensures
        e_mul(a, e_add(b, c)) == e_add(e_mul(a, b), e_mul(a, c)),
        e_mul(e_add(b, c), a) == e_add(e_mul(b, a), e_mul(c, a)),
{
    let s = e_add(b, c);
    lemma_k_mul_xor_right(a.c0, b.c0, c.c0);
    lemma_k_mul_xor_right(a.c0, b.c1, c.c1);
    lemma_k_mul_xor_right(a.c0, b.c2, c.c2);
    lemma_k_mul_xor_right(a.c1, b.c0, c.c0);
    lemma_k_mul_xor_right(a.c1, b.c1, c.c1);
    lemma_k_mul_xor_right(a.c1, b.c2, c.c2);
    lemma_k_mul_xor_right(a.c2, b.c0, c.c0);
    lemma_k_mul_xor_right(a.c2, b.c1, c.c1);
    lemma_k_mul_xor_right(a.c2, b.c2, c.c2);
    lemma_xor_distrib(
        k_mul(a.c0, b.c0), k_mul(a.c0, b.c1), k_mul(a.c0, b.c2),
        k_mul(a.c1, b.c0), k_mul(a.c1, b.c1), k_mul(a.c1, b.c2),
        k_mul(a.c2, b.c0), k_mul(a.c2, b.c1), k_mul(a.c2, b.c2),
        k_mul(a.c0, c.c0), k_mul(a.c0, c.c1), k_mul(a.c0, c.c2),
        k_mul(a.c1, c.c0), k_mul(a.c1, c.c1), k_mul(a.c1, c.c2),
        k_mul(a.c2, c.c0), k_mul(a.c2, c.c1), k_mul(a.c2, c.c2),
    );
    assert(e_mul(a, s) == e_add(e_mul(a, b), e_mul(a, c)));
    lemma_e_mul_comm(a, s);
    lemma_e_mul_comm(a, b);
    lemma_e_mul_comm(a, c);
}

/// `v + v r = v (1 + r)`: the doubling's low child.
proof fn lemma_times_one_plus(v: F192, r: F192)
    ensures
        e_add(v, e_mul(v, r)) == e_mul(v, e_add(F192::ONE, r)),
{
    lemma_e_mul_distrib(v, F192::ONE, r);
    lemma_e_mul_one(v);
}

// ---------------------------------------------------------------------------------------------
// The equality polynomial
// ---------------------------------------------------------------------------------------------
/// At a cube coordinate the factor selects: `eq_factor(r, 1) = r`, `eq_factor(r, 0) = 1 + r`.
pub proof fn lemma_eq_factor_bits(r: F192)
    ensures
        eq_factor(r, F192::ONE) == r,
        eq_factor(r, F192::ZERO) == e_add(F192::ONE, r),
{
    let s = e_add(F192::ONE, r);
    assert(1u64 ^ 1u64 == 0u64 && 1u64 ^ 0u64 == 1u64 && 0u64 ^ 0u64 == 0u64) by (bit_vector);
    assert(e_add(F192::ONE, F192::ONE) == F192::ZERO);
    assert(e_add(F192::ONE, F192::ZERO) == F192::ONE);
    lemma_e_mul_one(r);
    lemma_e_mul_one(s);
    lemma_e_mul_zero(r);
    lemma_e_mul_zero(s);
    lemma_e_add(r, r, r);
    lemma_e_add(s, s, s);
}

/// In characteristic 2 the factor is `1 + r + x` for every `x`, the form `eq_eval` computes.
pub proof fn lemma_eq_factor_sum(r: F192, x: F192)
    ensures
        eq_factor(r, x) == e_add(e_add(F192::ONE, r), x),
{
    let (s, t, u) = (e_add(F192::ONE, r), e_add(F192::ONE, x), e_mul(r, x));
    // (1 + r)(1 + x) = (1 + r) + (x + r x).
    lemma_e_mul_distrib(s, F192::ONE, x);
    lemma_e_mul_one(s);
    lemma_e_mul_distrib(x, F192::ONE, r);
    lemma_e_mul_one(x);
    lemma_e_mul_comm(s, x);
    lemma_e_mul_comm(x, r);
    assert(e_mul(s, t) == e_add(s, e_add(x, u)));
    lemma_e_add(u, s, x);
    lemma_e_add(s, x, u);
    lemma_e_add(x, u, s);
    assert(e_add(u, e_add(s, e_add(x, u))) == e_add(s, x));
}

/// A table entry extended by one top variable: the low half picks `1 + r_i`, the high half `r_i`.
pub proof fn lemma_eq_at_high(r: Seq<F192>, j: usize)
    requires
        1 <= r.len() <= 63,
        j < (1usize << ((r.len() - 1) as usize)),
    ensures
        eq_at(r, j) == e_mul(eq_at(r.drop_last(), j), e_add(F192::ONE, r.last())),
        eq_at(r, (j + (1usize << ((r.len() - 1) as usize))) as usize) == e_mul(eq_at(r.drop_last(), j), r.last()),
{
    let i = (r.len() - 1) as usize;
    let j2 = (j + (1usize << i)) as usize;
    lemma_bit_add_high(j, i);
    let (p, p2) = (cube_point(r.len(), j), cube_point(r.len(), j2));
    assert(p.drop_last() =~= cube_point(i as nat, j));
    assert forall|k: int| 0 <= k < i implies #[trigger] bit(j2, k) == bit(j, k) by {
        lemma_bit_add_low(j, i, k as usize);
    }
    assert(p2.drop_last() =~= cube_point(i as nat, j));
    assert(p.last() == F192::ZERO);
    assert(p2.last() == F192::ONE);
    lemma_eq_factor_bits(r.last());
}

proof fn lemma_bit_add_high(j: usize, i: usize)
    requires
        i < 63,
        j < (1usize << i),
    ensures
        (j >> i) & 1 == 0,
        ((j + (1usize << i)) as usize >> i) & 1 == 1,
{
    assert((j >> i) & 1 == 0 && ((j + (1usize << i)) as usize >> i) & 1 == 1) by (bit_vector)
        requires
            i < 63,
            j < (1usize << i),
    ;
}

proof fn lemma_bit_add_low(j: usize, i: usize, k: usize)
    requires
        i < 63,
        j < (1usize << i),
        k < i,
    ensures
        ((j + (1usize << i)) as usize >> k) & 1 == (j >> k) & 1,
{
    assert(((j + (1usize << i)) as usize >> k) & 1 == (j >> k) & 1) by (bit_vector)
        requires
            i < 63,
            j < (1usize << i),
            k < i,
    ;
}

/// `2^(i+1) = 2 * 2^i` as shifts.
proof fn lemma_shl_double(i: usize)
    requires
        i < 63,
    ensures
        (1usize << i) * 2 == (1usize << ((i + 1) as usize)),
        (1usize << i) >= 1,
        (1usize << i) <= (1usize << 62usize),
{
    assert((1usize << i) * 2 == (1usize << ((i + 1) as usize)) && (1usize << i) >= 1 && (1usize << i) <= (1usize
        << 62usize)) by (bit_vector)
        requires
            i < 63,
    ;
}

/// The bits of `(h << L) | l`, `l < 2^L`: those of `l` below `L`, those of `h` above.
proof fn lemma_bit_concat(h: usize, l: usize, low: usize, k: usize)
    requires
        low < 64,
        l < (1usize << low),
        k < 64,
    ensures
        k < low ==> (((h << low) | l) >> k) & 1 == (l >> k) & 1,
        k >= low ==> (((h << low) | l) >> k) & 1 == (h >> ((k - low) as usize)) & 1,
{
    assert(k < low ==> (((h << low) | l) >> k) & 1 == (l >> k) & 1) by (bit_vector)
        requires
            low < 64,
            l < (1usize << low),
            k < 64,
    ;
    assert(k >= low ==> (((h << low) | l) >> k) & 1 == (h >> ((k - low) as usize)) & 1) by (bit_vector)
        requires
            low < 64,
            l < (1usize << low),
            k < 64,
    ;
}

/// `eq` of a concatenation is the product of the parts' `eq`.
pub proof fn lemma_eq_poly_concat(r1: Seq<F192>, x1: Seq<F192>, r2: Seq<F192>, x2: Seq<F192>)
    requires
        r1.len() == x1.len(),
        r2.len() == x2.len(),
    ensures
        eq_poly(r1 + r2, x1 + x2) == e_mul(eq_poly(r1, x1), eq_poly(r2, x2)),
    decreases r2.len(),
{
    if r2.len() == 0 {
        assert(r1 + r2 =~= r1);
        assert(x1 + x2 =~= x1);
        lemma_e_mul_one(eq_poly(r1, x1));
    } else {
        assert((r1 + r2).drop_last() =~= r1 + r2.drop_last());
        assert((x1 + x2).drop_last() =~= x1 + x2.drop_last());
        lemma_eq_poly_concat(r1, x1, r2.drop_last(), x2.drop_last());
        lemma_e_mul_assoc(
            eq_poly(r1, x1),
            eq_poly(r2.drop_last(), x2.drop_last()),
            eq_factor(r2.last(), x2.last()),
        );
    }
}

/// The tensor structure of the table: `eq(r, (h << L) | l) = eq(r[..L], l) * eq(r[L..], h)` for `l < 2^L`.
pub proof fn lemma_eq_at_tensor(r: Seq<F192>, low: usize, h: usize, l: usize)
    requires
        low <= r.len() < 64,
        l < (1usize << low),
    ensures
        eq_at(r, (h << low) | l) == e_mul(eq_at(r.subrange(0, low as int), l), eq_at(r.subrange(low as int, r.len() as int), h)),
{
    let n = r.len();
    let x = (h << low) | l;
    let (rl, rh) = (r.subrange(0, low as int), r.subrange(low as int, n as int));
    assert forall|k: int| 0 <= k < n implies #[trigger] bit(x, k) == (if k < low {
        bit(l, k)
    } else {
        bit(h, k - low)
    }) by {
        lemma_bit_concat(h, l, low, k as usize);
    }
    assert(cube_point(n, x) =~= cube_point(low as nat, l) + cube_point((n - low) as nat, h));
    assert(r =~= rl + rh);
    lemma_eq_poly_concat(rl, cube_point(low as nat, l), rh, cube_point((n - low) as nat, h));
}

/// `h * 2^L + l = (h << L) | l` for `l < 2^L` and `h < 2^(n - L)`, and it is below `2^n`.
proof fn lemma_index_split(h: usize, l: usize, low: usize, n: usize)
    requires
        low <= n < 64,
        l < (1usize << low),
        h < (1usize << ((n - low) as usize)),
    ensures
        h * (1usize << low) + l == (h << low) | l,
        h * (1usize << low) + l < (1usize << n),
{
    lemma_usize_pow2_no_overflow(low as nat);
    lemma_usize_pow2_no_overflow((n - low) as nat);
    lemma_usize_pow2_no_overflow(n as nat);
    lemma_usize_shl_is_mul(1, low);
    lemma_usize_shl_is_mul(1, (n - low) as usize);
    lemma_usize_shl_is_mul(1, n);
    lemma_pow2_adds((n - low) as nat, low as nat);
    lemma_pow2_pos(low as nat);
    assert(h * pow2(low as nat) + l < pow2(n as nat)) by (nonlinear_arith)
        requires
            h + 1 <= pow2((n - low) as nat),
            l < pow2(low as nat),
            pow2((n - low) as nat) * pow2(low as nat) == pow2(n as nat),
    ;
    lemma_usize_pow2_no_overflow(n as nat);
    lemma_usize_shl_is_mul(h, low);
    let hs = h << low;
    assert(hs + l == hs | l) by (bit_vector)
        requires
            hs == h << low,
            l < (1usize << low),
            low < 64,
    ;
}

/// An index splits as `((x >> L) << L) | (x & (2^L - 1))`, its high part below `2^(n - L)`.
proof fn lemma_index_parts(x: usize, low: usize, n: usize)
    requires
        low <= n < 64,
        x < (1usize << n),
    ensures
        x == ((x >> low) << low) | (x & sub(1usize << low, 1)),
        (x & sub(1usize << low, 1)) < (1usize << low),
        (x >> low) < (1usize << ((n - low) as usize)),
        (1usize << low) >= 1,
{
    assert(x == ((x >> low) << low) | (x & sub(1usize << low, 1)) && (x & sub(1usize << low, 1)) < (1usize << low)
        && (x >> low) < (1usize << ((n - low) as usize)) && (1usize << low) >= 1) by (bit_vector)
        requires
            low <= n < 64,
            x < (1usize << n),
    ;
}

// ---------------------------------------------------------------------------------------------
// Executable code: the portable paths
// ---------------------------------------------------------------------------------------------
/// Multilinear interpolation in one variable over `E`: `lo + t·(lo+hi)`, the
/// char-2 form of `(1−t)·lo + t·hi`.
#[inline]
pub fn interp(lo: F192, hi: F192, t: F192) -> (r: F192)
    ensures
        r == e_add(e_mul(e_add(F192::ONE, t), lo), e_mul(t, hi)),
{
    proof {
        lemma_e_mul_distrib(t, lo, hi);
        lemma_e_mul_distrib(lo, F192::ONE, t);
        lemma_e_mul_one(lo);
        lemma_e_mul_comm(lo, e_add(F192::ONE, t));
        lemma_e_mul_comm(lo, t);
        lemma_e_add(lo, e_mul(t, lo), e_mul(t, hi));
    }
    lo + t * (lo + hi)
}

/// Mixed interpolation: two `K` endpoints against an `E` parameter, one
/// `mul_base` (`lo + t·(lo+hi)` with `lo, hi ∈ K`).
#[inline]
pub fn interp_k(lo: F64, hi: F64, t: F192) -> (r: F192)
    ensures
        r == e_add(e_mul(e_add(F192::ONE, t), e_from_k(lo.0)), e_mul(t, e_from_k(hi.0))),
{
    proof {
        let (l, h) = (e_from_k(lo.0), e_from_k(hi.0));
        assert(e_from_k(lo.0 ^ hi.0) == e_add(l, h)) by {
            assert(0u64 ^ 0u64 == 0u64) by (bit_vector);
        }
        lemma_e_mul_distrib(t, l, h);
        lemma_e_mul_distrib(l, F192::ONE, t);
        lemma_e_mul_one(l);
        lemma_e_mul_comm(l, e_add(F192::ONE, t));
        lemma_e_mul_comm(l, t);
        lemma_e_add(l, e_mul(t, l), e_mul(t, h));
    }
    F192::from(lo) + t.mul_base(lo + hi)
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)`. For Boolean `r`, this is the indicator
/// of `x = r`; for arbitrary `r`, it is the multilinear interpolation weight.
///
/// Production folds over `r.iter().zip(x)` after a `debug_assert_eq!` of the lengths, here a `requires`.
pub fn eq_eval(r: &[F192], x: &[F192]) -> (e: F192)
    requires
        r.len() == x.len(),
    ensures
        e == eq_poly(r@, x@),
{
    let mut acc = F192::ONE;
    for i in 0..r.len()
        invariant
            r.len() == x.len(),
            acc == eq_poly(r@.subrange(0, i as int), x@.subrange(0, i as int)),
    {
        proof {
            lemma_eq_factor_sum(r@[i as int], x@[i as int]);
            assert(r@.subrange(0, i + 1).drop_last() =~= r@.subrange(0, i as int));
            assert(x@.subrange(0, i + 1).drop_last() =~= x@.subrange(0, i as int));
        }
        acc = acc * (F192::ONE + r[i] + x[i]);
    }
    proof {
        assert(r@.subrange(0, r.len() as int) =~= r@);
        assert(x@.subrange(0, x.len() as int) =~= x@);
    }
    acc
}

/// The `eq(r, ·)` table over `n = r.len()` variables. See [`fill_eq_table_uninit`].
pub fn eq_table(r: &[F192]) -> (t: Vec<F192>)
    requires
        r.len() < 64,
    ensures
        is_eq_table(t@, r@, F192::ONE),
    decreases r.len(), 2nat,
{
    eq_table_seeded(r, F192::ONE)
}

/// The table of `seed * eq(r, .)` over `n = r.len()` variables, in LSB-first order.
///
/// Production fills the spare capacity of `Vec::with_capacity(len)` and then sets the length; the copy fills a
/// vector of zeros. The length `1 << r.len()` needs `r.len() < 64`, a `requires`.
pub fn eq_table_seeded(r: &[F192], seed: F192) -> (t: Vec<F192>)
    requires
        r.len() < 64,
    ensures
        is_eq_table(t@, r@, seed),
    decreases r.len(), 1nat,
{
    // One entry per point of the cube: 2^n.
    let len = 1usize << r.len();

    let mut eq = vec![F192::ZERO; len];
    fill_eq_table_uninit(r, seed, eq.as_mut_slice());
    eq
}

/// Fill `out` with `seed * eq(r, .)`, in LSB-first order. Every entry is written before it is read.
///
/// A small table doubles a level at a time on the calling thread.
///
/// A large one is a tensor product, written in one parallel pass:
///
/// ```text
///     out[h * 2^L + l] = high[h] * low[l],    low = eq(r[..L]),  high = seed * eq(r[L..])
/// ```
///
/// Production writes `MaybeUninit` slots; the copy writes initialized ones. Its `assert_eq!` on the length is a
/// `requires`. The parallel pass (`parallel::chunks_mut` over chunks of whole rows, each row zipped with its
/// weight `high[h]` and cut `as_chunks_mut::<4>`) becomes a loop over the rows in order: each entry is written
/// once, from `high[h]` and `low` alone, so the order of the rows does not change the table.
pub fn fill_eq_table_uninit(r: &[F192], seed: F192, out: &mut [F192])
    requires
        r.len() < 64,
        old(out).len() == (1usize << r.len()),
    ensures
        is_eq_table(final(out)@, r@, seed),
    decreases r.len(), 0nat,
{
    if out.len() < EQ_PAR_LEN {
        return fill_eq_doubling(r, seed, out);
    }
    proof {
        let nn = r.len();
        assert(EQ_PAR_LEN == 65536) by (compute_only);
        assert((1usize << nn) >= 65536usize ==> nn >= 16) by (bit_vector)
            requires
                nn < 64,
        ;
    }
    let r_low = &r[..EQ_LOW_VARS];
    let r_high = &r[EQ_LOW_VARS..];
    let low = eq_table(r_low);
    let high = eq_table_seeded(r_high, seed);
    let ghost n = r.len();
    let ghost hl = (n - EQ_LOW_VARS) as usize;
    proof {
        assert(r_low@ == r@.subrange(0, EQ_LOW_VARS as int));
        assert(r_high@ == r@.subrange(EQ_LOW_VARS as int, n as int));
        assert(low.len() == 1024) by {
            assert((1usize << 10usize) == 1024) by (bit_vector);
        }
    }
    let mut h = 0;
    while h < high.len()
        invariant
            n == r.len(),
            n < 64,
            hl == n - EQ_LOW_VARS,
            out.len() == (1usize << n),
            low.len() == 1024,
            low.len() == (1usize << EQ_LOW_VARS),
            high.len() == (1usize << hl),
            is_eq_table(low@, r_low@, F192::ONE),
            is_eq_table(high@, r_high@, seed),
            r_low@ == r@.subrange(0, EQ_LOW_VARS as int),
            r_high@ == r@.subrange(EQ_LOW_VARS as int, n as int),
            h <= high.len(),
            forall|x: int| 0 <= x < h * 1024 ==> #[trigger] out@[x] == e_mul(seed, eq_at(r@, x as usize)),
        decreases high.len() - h,
    {
        let w = high[h];
        let mut c = 0;
        while c < low.len() / 4
            invariant
                n == r.len(),
                n < 64,
                hl == n - EQ_LOW_VARS,
                out.len() == (1usize << n),
                low.len() == 1024,
                low.len() == (1usize << EQ_LOW_VARS),
                high.len() == (1usize << hl),
                is_eq_table(low@, r_low@, F192::ONE),
                is_eq_table(high@, r_high@, seed),
                r_low@ == r@.subrange(0, EQ_LOW_VARS as int),
                r_high@ == r@.subrange(EQ_LOW_VARS as int, n as int),
                h < high.len(),
                w == high@[h as int],
                c <= 256,
                forall|x: int| 0 <= x < h * 1024 + 4 * c ==> #[trigger] out@[x] == e_mul(seed, eq_at(r@, x as usize)),
            decreases 256 - c,
        {
            let src = [low[4 * c], low[4 * c + 1], low[4 * c + 2], low[4 * c + 3]];
            let p = mul4([w, w, w, w], src);
            for k in 0..4
                invariant
                    n == r.len(),
                    n < 64,
                    hl == n - EQ_LOW_VARS,
                    out.len() == (1usize << n),
                    low.len() == 1024,
                    low.len() == (1usize << EQ_LOW_VARS),
                    high.len() == (1usize << hl),
                    is_eq_table(low@, r_low@, F192::ONE),
                    is_eq_table(high@, r_high@, seed),
                    r_low@ == r@.subrange(0, EQ_LOW_VARS as int),
                    r_high@ == r@.subrange(EQ_LOW_VARS as int, n as int),
                    h < high.len(),
                    w == high@[h as int],
                    c < 256,
                    forall|kk: int| 0 <= kk < 4 ==> #[trigger] p[kk] == e_mul(w, low@[4 * c + kk]),
                    forall|x: int| 0 <= x < h * 1024 + 4 * c + k ==> #[trigger] out@[x] == e_mul(seed, eq_at(r@, x as usize)),
            {
                let l = 4 * c + k;
                proof {
                    lemma_index_split(h, l, EQ_LOW_VARS, n as usize);
                    lemma_tensor_entry(r@, seed, h, l);
                    lemma_e_mul_one(eq_at(r_low@, l));
                }
                out[h * low.len() + l] = p[k];
            }
            c += 1;
        }
        h += 1;
    }
    proof {
        lemma_shl_sum(hl, EQ_LOW_VARS);
    }
}

/// `2^a * 2^b = 2^(a + b)` as shifts.
proof fn lemma_shl_sum(a: usize, b: usize)
    requires
        a + b < 64,
    ensures
        (1usize << a) * (1usize << b) == (1usize << ((a + b) as usize)),
{
    lemma_usize_pow2_no_overflow((a + b) as nat);
    lemma_usize_pow2_no_overflow(a as nat);
    lemma_usize_pow2_no_overflow(b as nat);
    lemma_usize_shl_is_mul(1, a);
    lemma_usize_shl_is_mul(1, b);
    lemma_usize_shl_is_mul(1, (a + b) as usize);
    lemma_pow2_adds(a as nat, b as nat);
}

/// One entry of the tensor pass: `seed eq(r_high, h) * eq(r_low, l) = seed eq(r, h 2^L + l)`.
proof fn lemma_tensor_entry(r: Seq<F192>, seed: F192, h: usize, l: usize)
    requires
        EQ_LOW_VARS <= r.len() < 64,
        l < 1024,
        h < (1usize << ((r.len() - EQ_LOW_VARS) as usize)),
    ensures
        h * 1024 + l < (1usize << r.len()),
        e_mul(e_mul(seed, eq_at(r.subrange(EQ_LOW_VARS as int, r.len() as int), h)), eq_at(r.subrange(0, EQ_LOW_VARS as int), l))
            == e_mul(seed, eq_at(r, (h * 1024 + l) as usize)),
{
    assert((1usize << 10usize) == 1024) by (bit_vector);
    lemma_index_split(h, l, EQ_LOW_VARS, r.len() as usize);
    lemma_eq_at_tensor(r, EQ_LOW_VARS, h, l);
    let (a, b) = (eq_at(r.subrange(0, EQ_LOW_VARS as int), l), eq_at(r.subrange(EQ_LOW_VARS as int, r.len() as int), h));
    lemma_e_mul_assoc(seed, b, a);
    lemma_e_mul_comm(b, a);
}

/// Tables below this size are built on the calling thread.
pub const EQ_PAR_LEN: usize = 1 << 16;

/// The variables of the L1-resident factor of a large `eq` table.
pub const EQ_LOW_VARS: usize = 10;

/// One doubling step on entry `j` of level `i`: the high child `v r_i` and the low child `v + v r_i`.
proof fn lemma_doubling_entry(r: Seq<F192>, seed: F192, j: usize)
    requires
        1 <= r.len() <= 63,
        j < (1usize << ((r.len() - 1) as usize)),
    ensures
        ({
            let v = e_mul(seed, eq_at(r.drop_last(), j));
            &&& e_mul(r.last(), v) == e_mul(seed, eq_at(r, (j + (1usize << ((r.len() - 1) as usize))) as usize))
            &&& e_mul(v, r.last()) == e_mul(seed, eq_at(r, (j + (1usize << ((r.len() - 1) as usize))) as usize))
            &&& e_add(v, e_mul(r.last(), v)) == e_mul(seed, eq_at(r, j))
            &&& e_add(v, e_mul(v, r.last())) == e_mul(seed, eq_at(r, j))
        }),
{
    let e = eq_at(r.drop_last(), j);
    let v = e_mul(seed, e);
    let rk = r.last();
    lemma_eq_at_high(r, j);
    lemma_e_mul_comm(rk, v);
    lemma_e_mul_assoc(seed, e, rk);
    lemma_times_one_plus(v, rk);
    lemma_e_mul_assoc(seed, e, e_add(F192::ONE, rk));
}

/// The level-by-level `eq` build: each level writes the high half from the low half, then rewrites the low half.
///
/// In characteristic 2 the low child is the high child plus the parent, so each pair costs one product.
///
/// Production enumerates `r.iter()`, splits `out[..2 * half]` with `split_at_mut` (and casts the initialized low
/// half from `MaybeUninit`), and walks both halves `as_chunks_mut::<4>` then their tails; the copy indexes
/// `lo[j] = out[j]`, `hi[j] = out[half + j]`, and `l[k] += p[k]` is `out[..] = out[..] + p[k]`.
fn fill_eq_doubling(r: &[F192], seed: F192, out: &mut [F192])
    requires
        r.len() < 64,
        old(out).len() == (1usize << r.len()),
    ensures
        is_eq_table(final(out)@, r@, seed),
{
    let ghost n = r.len();
    proof {
        assert((1usize << n) >= 1) by (bit_vector)
            requires
                n < 64,
        ;
    }
    out[0] = seed;
    proof {
        assert((1usize << 0usize) == 1) by (bit_vector);
        assert(eq_at(r@.subrange(0, 0), 0) == F192::ONE);
        lemma_e_mul_one(seed);
    }
    for i in 0..r.len()
        invariant
            n == r.len(),
            n < 64,
            out.len() == (1usize << n),
            forall|j: int| 0 <= j < (1usize << i) ==> #[trigger] out@[j] == e_mul(seed, eq_at(r@.subrange(0, i as int), j as usize)),
    {
        let rk = r[i];
        let half = 1usize << i;
        let ghost lvl = r@.subrange(0, i as int);
        let ghost nxt = r@.subrange(0, i + 1);
        let ghost before = out@;
        proof {
            lemma_shl_double(i);
            assert((1usize << ((i + 1) as usize)) <= (1usize << n)) by (bit_vector)
                requires
                    i < n,
                    n < 64,
            ;
            assert(nxt.drop_last() =~= lvl);
            assert(nxt.last() == rk);
        }
        let n4 = half / 4;
        let mut c = 0;
        while c < n4
            invariant
                n == r.len(),
                n < 64,
                i < n,
                out.len() == (1usize << n),
                half == (1usize << i),
                2 * half <= out.len(),
                before.len() == out.len(),
                n4 == half / 4,
                c <= n4,
                rk == r@[i as int],
                lvl == r@.subrange(0, i as int),
                nxt == r@.subrange(0, i + 1),
                nxt.drop_last() == lvl,
                nxt.last() == rk,
                forall|j: int| 0 <= j < half ==> #[trigger] before[j] == e_mul(seed, eq_at(lvl, j as usize)),
                forall|j: int| 0 <= j < 4 * c ==> #[trigger] out@[j] == e_mul(seed, eq_at(nxt, j as usize)),
                forall|j: int| 0 <= j < 4 * c ==> #[trigger] out@[half + j] == e_mul(seed, eq_at(nxt, (half + j) as usize)),
                forall|j: int| 4 * c <= j < half ==> #[trigger] out@[j] == before[j],
            decreases n4 - c,
        {
            let l = [out[4 * c], out[4 * c + 1], out[4 * c + 2], out[4 * c + 3]];
            let p = mul4([rk, rk, rk, rk], l);
            for k in 0..4
                invariant
                    n == r.len(),
                    n < 64,
                    i < n,
                    out.len() == (1usize << n),
                    half == (1usize << i),
                    2 * half <= out.len(),
                    before.len() == out.len(),
                    n4 == half / 4,
                    c < n4,
                    rk == r@[i as int],
                    lvl == r@.subrange(0, i as int),
                    nxt == r@.subrange(0, i + 1),
                    nxt.drop_last() == lvl,
                    nxt.last() == rk,
                    forall|kk: int| 0 <= kk < 4 ==> #[trigger] l[kk] == before[4 * c + kk],
                    forall|kk: int| 0 <= kk < 4 ==> #[trigger] p[kk] == e_mul(rk, l[kk]),
                    forall|j: int| 0 <= j < half ==> #[trigger] before[j] == e_mul(seed, eq_at(lvl, j as usize)),
                    forall|j: int| 0 <= j < 4 * c + k ==> #[trigger] out@[j] == e_mul(seed, eq_at(nxt, j as usize)),
                    forall|j: int| 0 <= j < 4 * c + k ==> #[trigger] out@[half + j] == e_mul(seed, eq_at(nxt, (half + j) as usize)),
                    forall|j: int| 4 * c + k <= j < half ==> #[trigger] out@[j] == before[j],
            {
                let j = 4 * c + k;
                proof {
                    lemma_doubling_entry(nxt, seed, j);
                }
                out[half + j] = p[k];
                out[j] = out[j] + p[k];
            }
            c += 1;
        }
        let mut j = 4 * n4;
        while j < half
            invariant
                n == r.len(),
                n < 64,
                i < n,
                out.len() == (1usize << n),
                half == (1usize << i),
                2 * half <= out.len(),
                before.len() == out.len(),
                4 * n4 <= j <= half,
                rk == r@[i as int],
                lvl == r@.subrange(0, i as int),
                nxt == r@.subrange(0, i + 1),
                nxt.drop_last() == lvl,
                nxt.last() == rk,
                forall|jj: int| 0 <= jj < half ==> #[trigger] before[jj] == e_mul(seed, eq_at(lvl, jj as usize)),
                forall|jj: int| 0 <= jj < j ==> #[trigger] out@[jj] == e_mul(seed, eq_at(nxt, jj as usize)),
                forall|jj: int| 0 <= jj < j ==> #[trigger] out@[half + jj] == e_mul(seed, eq_at(nxt, (half + jj) as usize)),
                forall|jj: int| j <= jj < half ==> #[trigger] out@[jj] == before[jj],
            decreases half - j,
        {
            proof {
                lemma_doubling_entry(nxt, seed, j);
            }
            let p = out[j] * rk;
            out[half + j] = p;
            out[j] = out[j] + p;
            j += 1;
        }
        proof {
            assert forall|jj: int| 0 <= jj < (1usize << ((i + 1) as usize)) implies #[trigger] out@[jj] == e_mul(
                seed,
                eq_at(nxt, jj as usize),
            ) by {
                if jj >= half {
                    assert(out@[half + (jj - half)] == e_mul(seed, eq_at(nxt, (half + (jj - half)) as usize)));
                }
            }
        }
    }
    proof {
        assert(r@.subrange(0, n as int) =~= r@);
    }
}

// ---------------------------------------------------------------------------------------------
// Marginalizing a variable out of a table
// ---------------------------------------------------------------------------------------------
/// The one-variable table: `eq([r0], 0) = 1 + r0`, `eq([r0], 1) = r0`.
proof fn lemma_eq_at_one(s: Seq<F192>)
    requires
        s.len() == 1,
    ensures
        eq_at(s, 0) == e_add(F192::ONE, s[0]),
        eq_at(s, 1) == s[0],
{
    assert(((0usize >> 0usize) & 1) == 0 && ((1usize >> 0usize) & 1) == 1) by (bit_vector);
    assert(s.drop_last().len() == 0);
    assert(eq_poly(s.drop_last(), cube_point(1, 0).drop_last()) == F192::ONE);
    assert(eq_poly(s.drop_last(), cube_point(1, 1).drop_last()) == F192::ONE);
    assert(cube_point(1, 0).last() == F192::ZERO);
    assert(cube_point(1, 1).last() == F192::ONE);
    lemma_eq_factor_bits(s[0]);
    lemma_e_mul_one(e_add(F192::ONE, s[0]));
    lemma_e_mul_one(s[0]);
}

/// `2i = (i << 1) | 0` and `2i + 1 = (i << 1) | 1`.
proof fn lemma_double_index(i: usize)
    requires
        i < 0x4000_0000_0000_0000usize,
    ensures
        2 * i == (i << 1usize) | 0usize,
        2 * i + 1 == (i << 1usize) | 1usize,
        (1usize << 1usize) == 2,
{
    assert(2 * i == (i << 1usize) | 0usize && 2 * i + 1 == (i << 1usize) | 1usize && (1usize << 1usize) == 2)
        by (bit_vector)
        requires
            i < 0x4000_0000_0000_0000usize,
    ;
}

/// The two entries of a table sharing all but the lowest variable: `eq(r, 2i) = (1 + r0) eq(r[1..], i)` and
/// `eq(r, 2i + 1) = r0 eq(r[1..], i)`.
pub proof fn lemma_eq_at_low(r: Seq<F192>, i: usize)
    requires
        1 <= r.len() < 64,
        i < (1usize << ((r.len() - 1) as usize)),
    ensures
        eq_at(r, (2 * i) as usize) == e_mul(e_add(F192::ONE, r[0]), eq_at(r.subrange(1, r.len() as int), i)),
        eq_at(r, (2 * i + 1) as usize) == e_mul(r[0], eq_at(r.subrange(1, r.len() as int), i)),
{
    let m = (r.len() - 1) as usize;
    assert((1usize << m) <= 0x4000_0000_0000_0000usize) by (bit_vector)
        requires
            m < 63,
    ;
    lemma_double_index(i);
    lemma_eq_at_tensor(r, 1, i, 0);
    lemma_eq_at_tensor(r, 1, i, 1);
    lemma_eq_at_one(r.subrange(0, 1));
}

/// Summing the two entries of each low pair of `seed * eq(r, .)` gives `seed * eq(r[1..], .)`: `eq(r_0, 0) +
/// eq(r_0, 1) = 1`.
pub proof fn lemma_shrink_low_eq(t: Seq<F192>, r: Seq<F192>, seed: F192)
    requires
        is_eq_table(t, r, seed),
        r.len() >= 1,
    ensures
        is_eq_table(Seq::new(t.len() / 2, |i: int| e_add(t[2 * i], t[2 * i + 1])), r.subrange(1, r.len() as int), seed),
{
    let n = r.len();
    let rest = r.subrange(1, n as int);
    lemma_shl_double((n - 1) as usize);
    assert forall|i: int| 0 <= i < t.len() / 2 implies #[trigger] e_add(t[2 * i], t[2 * i + 1]) == e_mul(
        seed,
        eq_at(rest, i as usize),
    ) by {
        lemma_eq_at_low(r, i as usize);
        let e = eq_at(rest, i as usize);
        let (c0, c1) = (e_add(F192::ONE, r[0]), r[0]);
        lemma_e_mul_distrib(seed, e_mul(c0, e), e_mul(c1, e));
        lemma_e_mul_distrib(e, c0, c1);
        lemma_e_add(F192::ONE, r[0], r[0]);
        lemma_e_add(r[0], r[0], r[0]);
        lemma_e_mul_one(e);
        assert(e_add(c0, c1) == F192::ONE);
        assert(e_add(e_mul(c0, e), e_mul(c1, e)) == e);
    }
}

/// Summing each entry of the low half of `seed * eq(r, .)` with its partner in the high half gives
/// `seed * eq(r[..n-1], .)`.
pub proof fn lemma_shrink_high_eq(t: Seq<F192>, r: Seq<F192>, seed: F192)
    requires
        is_eq_table(t, r, seed),
        r.len() >= 1,
    ensures
        is_eq_table(Seq::new(t.len() / 2, |i: int| e_add(t[i], t[i + t.len() / 2])), r.drop_last(), seed),
{
    let n = r.len();
    let half = 1usize << ((n - 1) as usize);
    lemma_shl_double((n - 1) as usize);
    assert forall|i: int| 0 <= i < t.len() / 2 implies #[trigger] e_add(t[i], t[i + t.len() / 2]) == e_mul(
        seed,
        eq_at(r.drop_last(), i as usize),
    ) by {
        lemma_eq_at_high(r, i as usize);
        let e = eq_at(r.drop_last(), i as usize);
        let (c0, c1) = (e_add(F192::ONE, r.last()), r.last());
        lemma_e_mul_distrib(seed, e_mul(e, c0), e_mul(e, c1));
        lemma_e_mul_distrib(e, c0, c1);
        lemma_e_add(F192::ONE, c1, c1);
        lemma_e_add(c1, c1, c1);
        lemma_e_mul_one(e);
        assert(e_add(c0, c1) == F192::ONE);
    }
}

/// Marginalize the lowest variable out of an `eq` table (in place). `eq(r_0, 0) +
/// eq(r_0, 1) = 1`, so summing adjacent entries drops `r_0` with no multiplies,
/// versus `2^{n-1}` to rebuild the table.
///
/// The pairwise sums of any table; on `seed * eq(r, .)` they are `seed * eq(r[1..], .)` ([`lemma_shrink_low_eq`]).
/// Production reborrows the vector as a slice to index it; the copy indexes the vector.
pub fn shrink_eq_low(table: &mut Vec<F192>)
    ensures
        final(table)@ == Seq::new(old(table)@.len() / 2, |i: int| e_add(old(table)@[2 * i], old(table)@[2 * i + 1])),
        forall|r: Seq<F192>, seed: F192|
            #[trigger] is_eq_table(old(table)@, r, seed) && r.len() >= 1 ==> is_eq_table(
                final(table)@,
                r.subrange(1, r.len() as int),
                seed,
            ),
{
    let ghost before = table@;
    let half = table.len() / 2;
    {
        for i in 0..half
            invariant
                half == before.len() / 2,
                table.len() == before.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] table@[j] == e_add(before[2 * j], before[2 * j + 1]),
                forall|j: int| i <= j < before.len() ==> #[trigger] table@[j] == before[j],
        {
            let (a, b) = (table[2 * i], table[2 * i + 1]);
            table[i] = a + b;
        }
    }
    table.truncate(half);
    proof {
        assert(table@ =~= Seq::new(before.len() / 2, |i: int| e_add(before[2 * i], before[2 * i + 1])));
        assert forall|r: Seq<F192>, seed: F192| #[trigger] is_eq_table(before, r, seed) && r.len() >= 1 implies is_eq_table(
            table@,
            r.subrange(1, r.len() as int),
            seed,
        ) by {
            lemma_shrink_low_eq(before, r, seed);
        }
    }
}

/// Marginalize the highest variable out of an `eq` table (in place), the
/// [`shrink_eq_low`] counterpart for a top-down sumcheck.
///
/// Each low entry plus its high partner; on `seed * eq(r, .)` that is `seed * eq(r[..n-1], .)`
/// ([`lemma_shrink_high_eq`]). Production splits the slice with `split_at_mut` and zips the halves; the copy
/// indexes `lo[i] = table[i]`, `hi[i] = table[half + i]`.
pub fn shrink_eq_high(table: &mut Vec<F192>)
    ensures
        final(table)@ == Seq::new(old(table)@.len() / 2, |i: int| e_add(old(table)@[i], old(table)@[i + old(table)@.len() / 2])),
        forall|r: Seq<F192>, seed: F192|
            #[trigger] is_eq_table(old(table)@, r, seed) && r.len() >= 1 ==> is_eq_table(
                final(table)@,
                r.drop_last(),
                seed,
            ),
{
    let ghost before = table@;
    let half = table.len() / 2;
    {
        for i in 0..half
            invariant
                half == before.len() / 2,
                table.len() == before.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] table@[j] == e_add(before[j], before[j + half]),
                forall|j: int| i <= j < before.len() ==> #[trigger] table@[j] == before[j],
        {
            let h = table[half + i];
            table[i] = table[i] + h;
        }
    }
    table.truncate(half);
    proof {
        assert(table@ =~= Seq::new(before.len() / 2, |i: int| e_add(before[i], before[i + before.len() / 2])));
        assert forall|r: Seq<F192>, seed: F192| #[trigger] is_eq_table(before, r, seed) && r.len() >= 1 implies is_eq_table(
            table@,
            r.drop_last(),
            seed,
        ) by {
            lemma_shrink_high_eq(before, r, seed);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The split table
// ---------------------------------------------------------------------------------------------
/// The table `eq(r, .)` as two smaller tables, `eq(r, x) = low[x mod 2^L] * high[x >> L]`.
///
/// - The low table is `eq` over the first `L` variables of `r`, the high table over the rest.
/// - Together they hold `2^L + 2^(n - L)` entries instead of `2^n`.
/// - Products are exact, so every entry equals the full table's.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug)]
pub struct SplitEq {
    /// The table over the low `L` variables.
    pub low: Vec<F192>,
    /// The table over the remaining variables.
    pub high: Vec<F192>,
    /// `L`.
    low_log: usize,
}

impl SplitEq {
    /// The split of `eq(r, .)` after `L = low_log` variables.
    pub closed spec fn splits(self, r: Seq<F192>) -> bool {
        &&& self.low_log <= r.len() < 64
        &&& is_eq_table(self.low@, r.subrange(0, self.low_log as int), F192::ONE)
        &&& is_eq_table(self.high@, r.subrange(self.low_log as int, r.len() as int), F192::ONE)
    }

    /// `L`.
    pub closed spec fn spec_low_log(self) -> usize {
        self.low_log
    }

    /// The split with at most `max_low` low variables.
    ///
    /// Production's `r.len().min(max_low)` is an `if`.
    pub fn with_low_vars(r: &[F192], max_low: usize) -> (s: Self)
        requires
            r.len() < 64,
        ensures
            s.splits(r@),
            s.spec_low_log() == (if r.len() < max_low { r.len() } else { max_low }),
    {
        Self::at_split(r, if r.len() < max_low { r.len() } else { max_low })
    }

    /// The split with at most `max_high` high variables.
    ///
    /// Production's `r.len().min(max_high)` is an `if`.
    pub fn with_high_vars(r: &[F192], max_high: usize) -> (s: Self)
        requires
            r.len() < 64,
        ensures
            s.splits(r@),
            s.spec_low_log() == r.len() - (if r.len() < max_high { r.len() } else { max_high }),
    {
        Self::at_split(r, r.len() - if r.len() < max_high { r.len() } else { max_high })
    }

    fn at_split(r: &[F192], low_log: usize) -> (s: Self)
        requires
            low_log <= r.len() < 64,
        ensures
            s.splits(r@),
            s.spec_low_log() == low_log,
    {
        Self { low: eq_table(&r[..low_log]), high: eq_table(&r[low_log..]), low_log }
    }

    /// The number of low variables `L`.
    pub const fn low_log(&self) -> (l: usize)
        ensures
            l == self.spec_low_log(),
    {
        self.low_log
    }

    /// `eq(r, x)`.
    ///
    /// The split of `eq(r, .)` for some `r` with `x` on its cube, a `requires`; the result is that entry.
    #[inline]
    pub fn at(&self, x: usize) -> (e: F192)
        requires
            exists|r: Seq<F192>| #[trigger] self.splits(r) && x < (1usize << r.len()),
        ensures
            forall|r: Seq<F192>| #[trigger] self.splits(r) && x < (1usize << r.len()) ==> e == eq_at(r, x),
    {
        let ghost r0 = choose|r: Seq<F192>| #[trigger] self.splits(r) && x < (1usize << r.len());
        proof {
            lemma_index_parts(x, self.low_log, r0.len() as usize);
            lemma_split_at(*self, r0, x);
        }
        self.low[x & (self.low.len() - 1)] * self.high[x >> self.low_log]
    }
}

/// The entry `at` reads, for any `r` the split is of.
proof fn lemma_split_at(s: SplitEq, r0: Seq<F192>, x: usize)
    requires
        s.splits(r0),
        x < (1usize << r0.len()),
    ensures
        s.low.len() >= 1,
        (x & sub(s.low@.len() as usize, 1)) < s.low.len(),
        (x >> s.spec_low_log()) < s.high.len(),
        forall|r: Seq<F192>| #[trigger] s.splits(r) && x < (1usize << r.len()) ==> e_mul(
            s.low@[(x & sub(s.low@.len() as usize, 1)) as int],
            s.high@[(x >> s.spec_low_log()) as int],
        ) == eq_at(r, x),
{
    let low = s.spec_low_log();
    lemma_index_parts(x, low, r0.len() as usize);
    assert forall|r: Seq<F192>| #[trigger] s.splits(r) && x < (1usize << r.len()) implies e_mul(
        s.low@[(x & sub(s.low@.len() as usize, 1)) as int],
        s.high@[(x >> low) as int],
    ) == eq_at(r, x) by {
        lemma_index_parts(x, low, r.len() as usize);
        let (l, h) = (x & sub(1usize << low, 1), x >> low);
        lemma_eq_at_tensor(r, low, h, l);
        lemma_e_mul_one(eq_at(r.subrange(0, low as int), l));
        lemma_e_mul_one(eq_at(r.subrange(low as int, r.len() as int), h));
    }
}

// ---------------------------------------------------------------------------------------------
// Sums over the cube, and the multilinear extension
// ---------------------------------------------------------------------------------------------
/// `sum_{i < n} g(i)`, from the first term up.
pub open spec fn e_sum_fn(g: spec_fn(int) -> F192, n: nat) -> F192
    decreases n,
{
    if n == 0 {
        F192::ZERO
    } else {
        e_add(e_sum_fn(g, (n - 1) as nat), g(n - 1))
    }
}

/// The multilinear extension of the table `f` at `p`: `sum_x eq(p, x) f[x]` over the cube.
pub open spec fn mle(f: Seq<F192>, p: Seq<F192>) -> F192 {
    e_sum_fn(|x: int| e_mul(eq_at(p, x as usize), f[x]), f.len())
}

/// A table of `K` words lifted into `E`.
pub open spec fn lift(t: Seq<F64>) -> Seq<F192> {
    t.map_values(|w: F64| e_from_k(w.0))
}

/// `(1 + t) lo + t hi`, the line through `(0, lo)` and `(1, hi)` at `t`.
pub open spec fn interp_spec(lo: F192, hi: F192, t: F192) -> F192 {
    e_add(e_mul(e_add(F192::ONE, t), lo), e_mul(t, hi))
}

/// The table with its lowest variable bound to `t`.
pub open spec fn fold_low(f: Seq<F192>, t: F192) -> Seq<F192> {
    Seq::new(f.len() / 2, |i: int| interp_spec(f[2 * i], f[2 * i + 1], t))
}

pub proof fn lemma_sum_ext(g1: spec_fn(int) -> F192, g2: spec_fn(int) -> F192, n: nat)
    requires
        forall|i: int| 0 <= i < n ==> #[trigger] g1(i) == g2(i),
    ensures
        e_sum_fn(g1, n) == e_sum_fn(g2, n),
    decreases n,
{
    if n > 0 {
        lemma_sum_ext(g1, g2, (n - 1) as nat);
    }
}

/// A sum of pairs: `sum_{x < 2m} g(x) = sum_{i < m} (g(2i) + g(2i + 1))`.
pub proof fn lemma_sum_pairs(g: spec_fn(int) -> F192, m: nat)
    ensures
        e_sum_fn(g, 2 * m) == e_sum_fn(|i: int| e_add(g(2 * i), g(2 * i + 1)), m),
    decreases m,
{
    if m > 0 {
        lemma_sum_pairs(g, (m - 1) as nat);
        let s = e_sum_fn(g, (2 * m - 2) as nat);
        assert(e_sum_fn(g, (2 * m - 1) as nat) == e_add(s, g(2 * m - 2)));
        lemma_e_add(s, g(2 * m - 2), g(2 * m - 1));
    }
}

/// The terms of `g` from `m` on.
pub open spec fn shifted(g: spec_fn(int) -> F192, m: int) -> spec_fn(int) -> F192 {
    |l: int| g(m + l)
}

/// The sums of `g` over consecutive blocks of `b` terms.
pub open spec fn block_sums(g: spec_fn(int) -> F192, b: nat) -> spec_fn(int) -> F192 {
    |h: int| e_sum_fn(shifted(g, h * b), b)
}

/// A sum split after `m` terms.
pub proof fn lemma_sum_split(g: spec_fn(int) -> F192, m: nat, k: nat)
    ensures
        e_sum_fn(g, m + k) == e_add(e_sum_fn(g, m), e_sum_fn(shifted(g, m as int), k)),
    decreases k,
{
    if k == 0 {
        lemma_e_add(e_sum_fn(g, m), F192::ZERO, F192::ZERO);
    } else {
        lemma_sum_split(g, m, (k - 1) as nat);
        assert(shifted(g, m as int)(k - 1) == g(m + k - 1));
        lemma_e_add(e_sum_fn(g, m), e_sum_fn(shifted(g, m as int), (k - 1) as nat), g(m + k - 1));
    }
}

/// A sum over `a` blocks of `b`: `sum_{x < ab} g(x) = sum_{h < a} sum_{l < b} g(hb + l)`.
pub proof fn lemma_sum_blocks(g: spec_fn(int) -> F192, a: nat, b: nat)
    ensures
        e_sum_fn(g, a * b) == e_sum_fn(block_sums(g, b), a),
    decreases a,
{
    if a > 0 {
        lemma_sum_blocks(g, (a - 1) as nat, b);
        let m = ((a - 1) * b) as nat;
        assert(a * b == m + b) by (nonlinear_arith)
            requires
                m == (a - 1) * b,
                a > 0,
        ;
        assert((a - 1) * b >= 0) by (nonlinear_arith)
            requires
                a > 0,
        ;
        assert(m as int == (a - 1) * b);
        lemma_sum_split(g, m, b);
        let bs = block_sums(g, b);
        assert(bs(a - 1) == e_sum_fn(shifted(g, m as int), b));
        assert(e_sum_fn(bs, a) == e_add(e_sum_fn(bs, (a - 1) as nat), bs(a - 1)));
        assert(e_sum_fn(g, ((a - 1) as nat) * b) == e_sum_fn(bs, (a - 1) as nat));
        assert(e_sum_fn(g, m) == e_sum_fn(bs, (a - 1) as nat));
    } else {
        assert(a * b == 0) by (nonlinear_arith)
            requires
                a == 0,
        ;
    }
}

/// A factor out of a sum: `c * sum_i g(i) = sum_i c g(i)`.
pub proof fn lemma_sum_scale(c: F192, g: spec_fn(int) -> F192, n: nat)
    ensures
        e_mul(c, e_sum_fn(g, n)) == e_sum_fn(|i: int| e_mul(c, g(i)), n),
    decreases n,
{
    if n == 0 {
        lemma_e_mul_zero(c);
    } else {
        lemma_sum_scale(c, g, (n - 1) as nat);
        lemma_e_mul_distrib(c, e_sum_fn(g, (n - 1) as nat), g(n - 1));
    }
}

/// Binding the lowest variable: `mle(f, p) = mle(fold_low(f, p_0), p[1..])`.
pub proof fn lemma_mle_fold_low(f: Seq<F192>, p: Seq<F192>)
    requires
        1 <= p.len() < 64,
        f.len() == (1usize << p.len()),
    ensures
        mle(f, p) == mle(fold_low(f, p[0]), p.subrange(1, p.len() as int)),
{
    let n = p.len();
    let rest = p.subrange(1, n as int);
    let g = fold_low(f, p[0]);
    let m = f.len() / 2;
    lemma_shl_double((n - 1) as usize);
    let big = |x: int| e_mul(eq_at(p, x as usize), f[x]);
    let small = |i: int| e_mul(eq_at(rest, i as usize), g[i]);
    lemma_sum_pairs(big, m as nat);
    assert forall|i: int| 0 <= i < m implies #[trigger] e_add(big(2 * i), big(2 * i + 1)) == small(i) by {
        lemma_eq_at_low(p, i as usize);
        let e = eq_at(rest, i as usize);
        let (c0, c1, a, b) = (e_add(F192::ONE, p[0]), p[0], f[2 * i], f[2 * i + 1]);
        lemma_e_mul_comm(c0, e);
        lemma_e_mul_comm(c1, e);
        lemma_e_mul_assoc(e, c0, a);
        lemma_e_mul_assoc(e, c1, b);
        lemma_e_mul_distrib(e, e_mul(c0, a), e_mul(c1, b));
    }
    lemma_sum_ext(|i: int| e_add(big(2 * i), big(2 * i + 1)), small, m as nat);
    assert(2 * m == f.len());
}

/// One term of the blocked sum: `eq(p, h 2^L + l) f[h 2^L + l] = eq(p_high, h) (eq(p_low, l) f[h 2^L + l])`.
proof fn lemma_mle_block_term(f: Seq<F192>, p: Seq<F192>, low: usize, h: int, l: int)
    requires
        low <= p.len() < 64,
        0 <= l < (1usize << low),
        0 <= h < (1usize << ((p.len() - low) as usize)),
    ensures
        h * (1usize << low) + l < (1usize << p.len()),
        e_mul(eq_at(p, (h * (1usize << low) + l) as usize), f[h * (1usize << low) + l]) == e_mul(
            eq_at(p.subrange(low as int, p.len() as int), h as usize),
            e_mul(eq_at(p.subrange(0, low as int), l as usize), f[h * (1usize << low) + l]),
        ),
{
    lemma_index_split(h as usize, l as usize, low, p.len() as usize);
    lemma_eq_at_tensor(p, low, h as usize, l as usize);
    let (el, eh) = (eq_at(p.subrange(0, low as int), l as usize), eq_at(p.subrange(low as int, p.len() as int), h as usize));
    lemma_e_mul_comm(el, eh);
    lemma_e_mul_assoc(eh, el, f[h * (1usize << low) + l]);
}

/// One block of the blocked sum is its row's value scaled by `eq(p_high, h)`.
proof fn lemma_mle_block_row(f: Seq<F192>, p: Seq<F192>, low: usize, h: int)
    requires
        low <= p.len() < 64,
        f.len() == (1usize << p.len()),
        0 <= h < (1usize << ((p.len() - low) as usize)),
    ensures
        block_sums(|x: int| e_mul(eq_at(p, x as usize), f[x]), (1usize << low) as nat)(h) == e_mul(
            eq_at(p.subrange(low as int, p.len() as int), h as usize),
            mle(f.subrange(h * (1usize << low), (h + 1) * (1usize << low)), p.subrange(0, low as int)),
        ),
{
    let n = p.len();
    let b = (1usize << low) as nat;
    let big = |x: int| e_mul(eq_at(p, x as usize), f[x]);
    assert((1usize << low) >= 1) by (bit_vector)
        requires
            low < 64,
    ;
    lemma_index_split(h as usize, 0, low, n as usize);
    lemma_index_split(h as usize, (b - 1) as usize, low, n as usize);
    assert((h + 1) * b == h * b + b) by (nonlinear_arith);
    let blk = f.subrange(h * b, (h + 1) * b);
    let pl = p.subrange(0, low as int);
    let eh = eq_at(p.subrange(low as int, n as int), h as usize);
    let inner = |l: int| e_mul(eq_at(pl, l as usize), blk[l]);
    lemma_sum_scale(eh, inner, b);
    assert forall|l: int| 0 <= l < b implies #[trigger] shifted(big, h * b)(l) == e_mul(eh, inner(l)) by {
        lemma_mle_block_term(f, p, low, h, l);
    }
    lemma_sum_ext(shifted(big, h * b), |l: int| e_mul(eh, inner(l)), b);
}

/// Binding the low `L` variables at once: `mle(f, p) = mle(rows, p[L..])` with `rows[h] = mle(block h of f,
/// p[..L])`, the blocks being the `2^(n - L)` runs of `2^L` entries.
pub proof fn lemma_mle_blocks(f: Seq<F192>, p: Seq<F192>, low: usize, rows: Seq<F192>)
    requires
        low <= p.len() < 64,
        f.len() == (1usize << p.len()),
        rows.len() == (1usize << ((p.len() - low) as usize)),
        forall|h: int| 0 <= h < rows.len() ==> #[trigger] rows[h] == mle(
            f.subrange(h * (1usize << low), (h + 1) * (1usize << low)),
            p.subrange(0, low as int),
        ),
    ensures
        mle(f, p) == mle(rows, p.subrange(low as int, p.len() as int)),
{
    let n = p.len();
    let ph = p.subrange(low as int, n as int);
    let b = (1usize << low) as nat;
    let a = rows.len();
    lemma_shl_sum(((n - low) as usize), low);
    assert(a * b == f.len());
    let big = |x: int| e_mul(eq_at(p, x as usize), f[x]);
    lemma_sum_blocks(big, a, b);
    assert forall|h: int| 0 <= h < a implies #[trigger] block_sums(big, b)(h) == e_mul(eq_at(ph, h as usize), rows[h]) by {
        lemma_mle_block_row(f, p, low, h);
    }
    lemma_sum_ext(block_sums(big, b), |h: int| e_mul(eq_at(ph, h as usize), rows[h]), a);
}

/// A one-entry table over no variables is its entry.
proof fn lemma_mle_one(f: Seq<F192>, p: Seq<F192>)
    requires
        f.len() == 1,
        p.len() == 0,
    ensures
        mle(f, p) == f[0],
{
    assert(eq_at(p, 0) == F192::ONE);
    lemma_e_mul_one(f[0]);
    lemma_e_add(f[0], F192::ZERO, F192::ZERO);
    let g = |x: int| e_mul(eq_at(p, x as usize), f[x]);
    assert(e_sum_fn(g, 0) == F192::ZERO);
    assert(e_sum_fn(g, 1) == e_add(F192::ZERO, g(0)));
}

/// The mixed fold: bind the lowest variable of a `K`-table to an
/// `E`-challenge, producing the `E`-table the remaining rounds fold. One
/// `mul_base` per output entry.
///
/// Production maps `0..table.len() / 2` and collects, after a `debug_assert_eq!` on the parity (a `requires`).
fn fold_low_k(table: &[F64], chi: F192) -> (g: Vec<F192>)
    requires
        table.len() % 2 == 0,
    ensures
        g@ == fold_low(lift(table@), chi),
{
    let mut out: Vec<F192> = Vec::new();
    for i in 0..table.len() / 2
        invariant
            table.len() % 2 == 0,
            out@ == fold_low(lift(table@), chi).subrange(0, i as int),
    {
        out.push(interp_k(table[2 * i], table[2 * i + 1], chi));
        proof {
            assert(out@ =~= fold_low(lift(table@), chi).subrange(0, i + 1));
        }
    }
    proof {
        assert(out@ =~= fold_low(lift(table@), chi));
    }
    out
}

/// Bind the remaining variables of a half-folded `E`-table, LSB-first.
///
/// `for &p in point` is a loop over the indices, and the `mut cur` argument is rebound. The table has one entry
/// per point of the cube, a `requires`.
fn fold_ladder(cur: Vec<F192>, point: &[F192]) -> (e: F192)
    requires
        point.len() < 64,
        cur.len() == (1usize << point.len()),
    ensures
        e == mle(cur@, point@),
{
    let mut cur = cur;
    let ghost n = point.len();
    let ghost orig = cur@;
    let mut len = cur.len();
    proof {
        assert(cur@.subrange(0, len as int) =~= orig);
        assert(point@.subrange(0, n as int) =~= point@);
    }
    for k in 0..point.len()
        invariant
            n == point.len(),
            n < 64,
            cur.len() == orig.len(),
            orig.len() == (1usize << n),
            len == (1usize << ((n - k) as usize)),
            len <= cur.len(),
            mle(cur@.subrange(0, len as int), point@.subrange(k as int, n as int)) == mle(orig, point@),
    {
        let p = point[k];
        let ghost before = cur@.subrange(0, len as int);
        let ghost all = cur@;
        proof {
            lemma_shl_double((n - k - 1) as usize);
            lemma_mle_fold_low(before, point@.subrange(k as int, n as int));
            assert(point@.subrange(k as int, n as int).subrange(1, (n - k) as int) =~= point@.subrange(k + 1, n as int));
        }
        len /= 2;
        for i in 0..len
            invariant
                cur.len() == all.len(),
                all.len() == orig.len(),
                2 * len <= all.len(),
                before == all.subrange(0, 2 * len),
                forall|j: int| 0 <= j < i ==> #[trigger] cur@[j] == interp_spec(before[2 * j], before[2 * j + 1], p),
                forall|j: int| i <= j < all.len() ==> #[trigger] cur@[j] == all[j],
        {
            cur[i] = interp(cur[2 * i], cur[2 * i + 1], p);
        }
        proof {
            assert(cur@.subrange(0, len as int) =~= fold_low(before, p));
        }
    }
    proof {
        assert((1usize << 0usize) == 1) by (bit_vector);
        lemma_mle_one(cur@.subrange(0, 1), point@.subrange(n as int, n as int));
    }
    cur[0]
}

/// The variables of the L1-resident low `eq` table of an MLE evaluation.
pub const MLE_LOW_VARS: usize = 10;

/// `eq(r, .)` packed eight weights at a time for [`dot_base`]. Needs `r.len() >= 3`.
///
/// Production maps `Weights8::new` over `as_chunks::<8>` of the table and collects; the copy loops over the
/// chunks.
fn packed_eq(r: &[F192]) -> (w: Vec<Weights8>)
    requires
        3 <= r.len() < 64,
    ensures
        8 * w.len() == (1usize << r.len()),
        forall|x: int| 0 <= x < (1usize << r.len()) ==> #[trigger] w8_get(w@[x / 8], x % 8) == eq_at(r@, x as usize),
{
    let t = eq_table(r);
    let ghost n = r.len();
    proof {
        assert((1usize << n) % 8 == 0) by (bit_vector)
            requires
                3 <= n < 64,
        ;
    }
    let mut out: Vec<Weights8> = Vec::new();
    for c in 0..t.len() / 8
        invariant
            n == r.len(),
            3 <= n < 64,
            is_eq_table(t@, r@, F192::ONE),
            t.len() % 8 == 0,
            out.len() == c,
            forall|x: int| 0 <= x < 8 * c ==> #[trigger] w8_get(out@[x / 8], x % 8) == t@[x],
    {
        let chunk = [t[8 * c], t[8 * c + 1], t[8 * c + 2], t[8 * c + 3], t[8 * c + 4], t[8 * c + 5], t[8 * c + 6], t[8 * c + 7]];
        out.push(Weights8::new(&chunk));
        proof {
            assert forall|x: int| 0 <= x < 8 * (c + 1) implies #[trigger] w8_get(out@[x / 8], x % 8) == t@[x] by {
                if x >= 8 * c {
                    assert(x / 8 == c && x % 8 == x - 8 * c) by (nonlinear_arith)
                        requires
                            8 * c <= x < 8 * c + 8,
                    ;
                } else {
                    assert(x / 8 < c) by (nonlinear_arith)
                        requires
                            0 <= x < 8 * c,
                    ;
                }
            }
        }
    }
    proof {
        assert forall|x: int| 0 <= x < (1usize << n) implies #[trigger] w8_get(out@[x / 8], x % 8) == eq_at(r@, x as usize) by {
            lemma_e_mul_one(eq_at(r@, x as usize));
        }
    }
    out
}

/// The packed dot product is the `eq`-weighted sum of the lifted row.
proof fn lemma_dot_is_mle(w: Seq<Weights8>, row: Seq<F64>, pl: Seq<F192>, k: nat)
    requires
        pl.len() < 64,
        k <= row.len(),
        row.len() == (1usize << pl.len()),
        8 * w.len() == row.len(),
        forall|x: int| 0 <= x < row.len() ==> #[trigger] w8_get(w[x / 8], x % 8) == eq_at(pl, x as usize),
    ensures
        dot_spec(w, row, k) == e_sum_fn(|x: int| e_mul(eq_at(pl, x as usize), lift(row)[x]), k),
    decreases k,
{
    if k > 0 {
        lemma_dot_is_mle(w, row, pl, (k - 1) as nat);
    }
}

/// Evaluate the MLE of a `K`-valued truth table at an `E`-point (length `log2(len)`).
///
/// The `eq` weights factor into a low and a high table:
///
/// ```text
///     f(point) = sum_h eq(point_high, h) * sum_l eq(point_low, l) * f[h * 2^L + l]
/// ```
///
/// Each row's inner sum is one [`dot_base`] against the packed low table, reduced once.
/// The table is read once and never lifted into `E`.
///
/// Production's `debug_assert_eq!` on the length is a `requires`; `match point.split_first()` tests the length;
/// `point.len().min(MLE_LOW_VARS)` is an `if`; `chunks_exact(..).map(..).collect()` is a loop pushing each row's
/// reduced dot product.
pub fn mle_eval(table: &[F64], point: &[F192]) -> (e: F192)
    requires
        point.len() < 64,
        table.len() == (1usize << point.len()),
    ensures
        e == mle(lift(table@), point@),
{
    let ghost n = point.len();
    let ghost f = lift(table@);
    if point.len() < 3 {
        if point.len() == 0 {
            proof {
                assert((1usize << 0usize) == 1) by (bit_vector);
                lemma_mle_one(f, point@);
            }
            return F192::from(table[0]);
        }
        let p0 = point[0];
        let rest = &point[1..];
        proof {
            lemma_shl_double((n - 1) as usize);
            lemma_mle_fold_low(f, point@);
            assert(fold_low(f, p0).len() == table.len() / 2);
        }
        return fold_ladder(fold_low_k(table, p0), rest);
    }
    let low_vars = if point.len() < MLE_LOW_VARS { point.len() } else { MLE_LOW_VARS };
    let low = packed_eq(&point[..low_vars]);
    let width = 1usize << low_vars;
    let ghost pl = point@.subrange(0, low_vars as int);
    let ghost hl = (n - low_vars) as usize;
    proof {
        lemma_shl_sum(hl, low_vars);
        assert((1usize << low_vars) >= 1) by (bit_vector)
            requires
                low_vars < 64,
        ;
        lemma_div_by_multiple((1usize << hl) as int, width as int);
    }
    let mut rows: Vec<F192> = Vec::new();
    let mut h = 0;
    while h < table.len() / width
        invariant
            n == point.len(),
            3 <= n < 64,
            low_vars <= n,
            hl == n - low_vars,
            width == (1usize << low_vars),
            width >= 1,
            table.len() == (1usize << n),
            (1usize << hl) * width == table.len(),
            table.len() / width == (1usize << hl),
            pl == point@.subrange(0, low_vars as int),
            f == lift(table@),
            8 * low.len() == width,
            forall|x: int| 0 <= x < width ==> #[trigger] w8_get(low@[x / 8], x % 8) == eq_at(pl, x as usize),
            h <= table.len() / width,
            rows.len() == h,
            forall|j: int| 0 <= j < h ==> #[trigger] rows@[j] == mle(f.subrange(j * width, (j + 1) * width), pl),
        decreases table.len() / width - h,
    {
        proof {
            assert(h * width <= (h + 1) * width <= table.len() && (h + 1) * width - h * width == width) by (nonlinear_arith)
                requires
                    h < (1usize << hl),
                    (1usize << hl) * width == table.len(),
            ;
        }
        let row = &table[h * width..(h + 1) * width];
        assert(row@ == table@.subrange(h * width, (h + 1) * width));
        let d = dot_base(&low, row).reduce();
        proof {
            lemma_dot_is_mle(low@, row@, pl, width as nat);
            assert(lift(row@) =~= f.subrange(h * width, (h + 1) * width));
        }
        rows.push(d);
        h += 1;
    }
    proof {
        lemma_mle_blocks(f, point@, low_vars, rows@);
    }
    fold_ladder(rows, &point[low_vars..])
}

// ---------------------------------------------------------------------------------------------
// The skip domain's shared barycentric weight
// ---------------------------------------------------------------------------------------------
/// `prod_{k=1}^{n-1} φ₈(k)` in `K`.
pub open spec fn phi8_prod(n: nat) -> u64
    decreases n,
{
    if n <= 1 {
        1
    } else {
        k_mul(phi8_prod((n - 1) as nat), phi8((n - 1) as u8))
    }
}

/// The weight of a window of `2^log` nodes: `(prod_{k=1}^{2^log - 1} φ₈(k))^(2^64 - 2)`, its inverse in `K`
/// ([`lemma_denominator_inverts`]).
pub open spec fn denominator_spec(log: nat) -> F192 {
    e_from_k(k_pow(phi8_prod(pow2(log)), (pow2(64) - 2) as nat))
}

/// The product in `K` the table is built with.
///
/// A `const fn` inside the `DENOMINATORS` initializer in production; Verus wants it at module level.
const fn mul(a: u64, b: u64) -> (r: u64)
    ensures
        r == k_mul(a, b),
{
    reduce(crate::gf2_64::software::clmul(a, b))
}

/// The barycentric weight every node of an aligned `size`-node window of the φ₈ table shares,
/// `1 / ∏_{k≠0} φ₈(k)`. φ₈ is F2-linear on its index, so `nodes[a] + nodes[b] = φ₈(a ^ b)` (the window's
/// offset cancels) and `b ↦ a ^ b` only permutes the window, leaving every node the same product.
/// Computed once for every window size.
///
/// Production's `debug_assert!` that `size` is a power of two at most 256 is a `requires`; `usize::trailing_zeros`
/// (which vstd does not specify) is `u64::trailing_zeros` of the same value.
pub fn window_denominator(size: usize) -> (d: F192)
    requires
        exists|log: nat| log <= 8 && size == #[trigger] pow2(log),
    ensures
        forall|log: nat| log <= 8 && size == #[trigger] pow2(log) ==> d == denominator_spec(log),
{
    let ghost log = choose|log: nat| log <= 8 && size == #[trigger] pow2(log);
    let tz = (size as u64).trailing_zeros();
    proof {
        lemma_pow2_injective_upto8(log);
        lemma_pow2_tz(size as u64, log);
    }
    DENOMINATORS[tz as usize]
}

/// The trailing zeros of `2^log` are `log`.
proof fn lemma_pow2_tz(x: u64, log: nat)
    requires
        log <= 8,
        x == pow2(log),
    ensures
        x.trailing_zeros() == log,
{
    lemma_pow2_shl(log);
    let t = x.trailing_zeros();
    broadcast use vstd::std_specs::bits::axiom_u64_trailing_zeros;
    let l = log as u64;
    assert(x == (1u64 << l));
    lemma_pow2_pos(log);
    assert(x != 0);
    assert(t < 64);
    assert((x >> (t as u64)) & 1u64 == 1u64);
    assert(forall|j: u64| 0 <= j < t ==> #[trigger] (x >> j) & 1u64 == 0u64);
    if (t as u64) < l {
        assert((x >> (t as u64)) & 1u64 == 0u64) by (bit_vector)
            requires
                x == (1u64 << l),
                (t as u64) < l,
                l <= 8,
        ;
    } else if (t as u64) > l {
        assert((x >> l) & 1u64 == 1u64) by (bit_vector)
            requires
                x == (1u64 << l),
                l <= 8,
        ;
    }
}

proof fn lemma_pow2_shl(log: nat)
    requires
        log <= 8,
    ensures
        pow2(log) == (1u64 << (log as u64)),
        pow2(log) == (1usize << (log as usize)),
        pow2(log) <= 256,
{
    lemma2_to64();
    let l = log as u64;
    assert(l <= 8 ==> (1u64 << l) == (if l == 0 { 1u64 } else if l == 1 { 2 } else if l == 2 { 4 } else if l == 3 { 8 } else if l == 4 { 16 } else if l == 5 { 32 } else if l == 6 { 64 } else if l == 7 { 128 } else { 256 })) by (bit_vector);
    let u = log as usize;
    assert(u <= 8 ==> (1usize << u) == (if u == 0 { 1usize } else if u == 1 { 2 } else if u == 2 { 4 } else if u == 3 { 8 } else if u == 4 { 16 } else if u == 5 { 32 } else if u == 6 { 64 } else if u == 7 { 128 } else { 256 })) by (bit_vector);
}

proof fn lemma_pow2_injective_upto8(log: nat)
    requires
        log <= 8,
    ensures
        forall|m: nat| m <= 8 && #[trigger] pow2(m) == pow2(log) ==> m == log,
{
    lemma2_to64();
}

/// [`window_denominator`] for every window size, at compile time. The nodes lie in `F64`, so the
/// product and its inverse (Fermat, `a^(2^64 - 2)`) stay there.
///
/// Verus's `exec const` form, to state what the table holds; the body is production's.
pub exec const DENOMINATORS: [F192; 9]
    ensures
        forall|log: int| 0 <= log < 9 ==> #[trigger] DENOMINATORS[log] == denominator_spec(log as nat),
{
    let mut out = [F192::ZERO; 9];
    let mut log = 0;
    while log < out.len()
        invariant
            log <= 9,
            forall|m: int| 0 <= m < log ==> #[trigger] out[m] == denominator_spec(m as nat),
        decreases 9 - log,
    {
        proof {
            lemma_pow2_shl(log as nat);
            lemma_pow2_pos(log as nat);
        }
        let mut product = 1;
        let mut k = 1;
        while k < 1 << log
            invariant
                log < 9,
                (1usize << log) == pow2(log as nat),
                (1usize << log) <= 256,
                1 <= k <= (1usize << log),
                product == phi8_prod(k as nat),
            decreases (1usize << log) - k,
        {
            product = mul(product, PHI_8_TABLE_192[k].c0);
            k += 1;
        }
        let ghost p = product;
        proof {
            lemma2_to64();
            assert(p == k_pow(p, 1)) by {
                lemma_k_mul_one(p);
                reveal_with_fuel(k_pow, 2);
            }
        }
        let (mut inverse, mut bit) = (1, 1);
        while bit < 64
            invariant
                1 <= bit <= 64,
                product == k_pow(p, pow2((bit - 1) as nat)),
                inverse == k_pow(p, (pow2(bit as nat) - 2) as nat),
                pow2(bit as nat) >= 2,
            decreases 64 - bit,
        {
            proof {
                lemma_pow2_unfold(bit as nat);
                lemma_pow2_unfold((bit + 1) as nat);
                lemma_k_pow_add(p, pow2((bit - 1) as nat), pow2((bit - 1) as nat));
                lemma_k_pow_add(p, (pow2(bit as nat) - 2) as nat, pow2(bit as nat));
            }
            product = mul(product, product);
            inverse = mul(inverse, product);
            bit += 1;
        }
        out[log] = F192::new(inverse, 0, 0);
        log += 1;
    }
    out
}

/// The weight inverts the product of the nonzero nodes of its window: `D * prod_{k=1}^{2^log - 1} φ₈(k) = 1`.
pub proof fn lemma_denominator_inverts(log: nat)
    requires
        log <= 8,
    ensures
        phi8_prod(pow2(log)) != 0,
        e_mul(denominator_spec(log), e_from_k(phi8_prod(pow2(log)))) == F192::ONE,
{
    lemma_pow2_shl(log);
    lemma_phi8_prod_nonzero(pow2(log));
    let p = phi8_prod(pow2(log));
    let w = k_pow(p, (pow2(64) - 2) as nat);
    lemma_k_inverse(p);
    lemma_k_mul_comm(p, w);
    lemma_e_from_k_mul(w, p);
}

/// A product of nonzero nodes is nonzero.
pub proof fn lemma_phi8_prod_nonzero(n: nat)
    requires
        n <= 256,
    ensures
        phi8_prod(n) != 0,
    decreases n,
{
    if n > 1 {
        lemma_phi8_prod_nonzero((n - 1) as nat);
        lemma_phi8_nonzero((n - 1) as u8);
        if phi8_prod(n) == 0 {
            crate::ntt::lemma_k_no_zero_divisors(phi8_prod((n - 1) as nat), phi8((n - 1) as u8));
        }
    }
}

} // verus!
