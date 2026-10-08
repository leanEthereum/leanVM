//! The additive NTT over `GF(2^8)` of flock's zerocheck, and the table that collapses the round-1 extension
//! through it.
//!
//! The executable functions are the portable paths of `crates/flock/src/zerocheck/ntt.rs` and
//! `crates/flock/src/zerocheck/ntt/inv_table.rs`, copied with the same names and bodies where Verus accepts
//! them; `tests/equivalence/flock_ntt.rs` checks the copies against production.
//!
//! Specification, over the field of `crate::gf2_8` (`f8_mul`), with the standard basis `b_i = x^i`
//! ([`basis8`], the byte with bit `i` alone):
//!
//! - [`subspace_poly8`]: the subspace polynomial `s_i`, `s_0(x) = x`, `s_i(x) = s_{i-1}(x) (s_{i-1}(x) +
//!   s_{i-1}(b_{i-1}))`, and [`normalized_poly8`], `Ŵ_i(x) = s_i(b_i)^(-1) s_i(x)`.
//! - [`novel8`]: the novel-basis polynomial `Σ_{j < 2^m} a_j X_j(x)`, `X_j = Π_{i < m} Ŵ_i(x)^(bit_i(j))`, by its
//!   split on the top bit of `j`; [`lemma_novel8_flat`] proves it equal to the flat sum [`novel8_sum`].
//! - [`fft_spec`] and [`ifft_spec`]: the recursions of `fft_rec` and `ifft_rec`, butterfly by butterfly.
//! - [`twiddles_of`]: the claim of `compute_twiddles`' documentation, entry `2^d - 1 + j` is the twiddle of
//!   block `j` at depth `d`, `Ŵ_(k-1-d)` of the block's first point.
//!
//! Main results: `compute_twiddles`' postcondition; [`lemma_fft_evaluates`] (the forward transform of an
//! NTT built with offset `β` maps the coefficients to the evaluations at `β + v`, `v < 2^k`);
//! [`lemma_ifft_after_fft`] and [`lemma_fft_after_ifft`] (the two transforms undo each other, so
//! [`lemma_ifft_interpolates`]); [`lemma_lde_shift`] (the columns of `M = forward_Λ ∘ inverse_S` satisfy
//! `M[i][j] = M[i ⊕ j][0]`); `InvNttTableByteSingleGf8::new`'s postcondition (row `w` of the table is the XOR of
//! the columns `t < 8` of `M` over the set bits `t` of `w`); and [`lemma_table_applies_lde`] (`apply_scalar`
//! multiplies `M` by the row's bits).
//!
//! The SIMD arms of `apply` are not copied.
use crate::gf2_8::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// The basis element `b_i = x^i`: the byte with bit `i` alone (`i < 8`).
pub open spec fn basis8(i: nat) -> u8 {
    1u8 << (i as u8)
}

/// The subspace polynomial `s_i` of the standard basis, evaluated at `x`:
/// `s_0(x) = x` and `s_i(x) = s_{i-1}(x) · (s_{i-1}(x) + s_{i-1}(b_{i-1}))`.
pub open spec fn subspace_poly8(i: nat, x: u8) -> u8
    decreases i,
{
    if i == 0 {
        x
    } else {
        let p = subspace_poly8((i - 1) as nat, x);
        f8_mul(p, p ^ subspace_poly8((i - 1) as nat, basis8((i - 1) as nat)))
    }
}

/// The inverse in `GF(2^8)`, `y^254` (zero for zero), as `F8::inv` computes it.
pub open spec fn f8_inv(y: u8) -> u8 {
    f8_pow(y, 254)
}

/// The normalized subspace polynomial `Ŵ_i(x) = s_i(b_i)^(-1) · s_i(x)`.
pub open spec fn normalized_poly8(i: nat, x: u8) -> u8 {
    f8_mul(f8_inv(subspace_poly8(i, basis8(i))), subspace_poly8(i, x))
}

/// The novel-basis polynomial with the `2^m` coefficients `a`, evaluated at `x`:
/// `Σ_{j < 2^m} a_j X_j(x)` with `X_j = Π_{i < m} Ŵ_i(x)^(bit_i(j))`, split on the top bit of `j`: the
/// polynomial of the low half of the coefficients, plus `Ŵ_(m-1)(x)` times the polynomial of the high half.
pub open spec fn novel8(m: nat, a: Seq<F8>, x: u8) -> u8
    decreases m,
{
    if m == 0 {
        a[0].0
    } else {
        let h = pow2((m - 1) as nat) as int;
        novel8((m - 1) as nat, a.subrange(0, h), x) ^ f8_mul(
            normalized_poly8((m - 1) as nat, x),
            novel8((m - 1) as nat, a.subrange(h, 2 * h), x),
        )
    }
}

/// `a + t b`, word by word.
pub open spec fn lincomb(a: Seq<F8>, t: u8, b: Seq<F8>) -> Seq<F8> {
    Seq::new(a.len(), |j: int| F8(a[j].0 ^ f8_mul(t, b[j].0)))
}

/// `fft_butterfly` on the halves of `v`: `(u, w) -> (u + λ w, w + (u + λ w))`.
pub open spec fn fft_butterfly_spec(v: Seq<F8>, lambda: u8) -> Seq<F8> {
    let h = v.len() / 2;
    Seq::new(
        v.len(),
        |p: int|
            if p < h {
                F8(v[p].0 ^ f8_mul(lambda, v[p + h].0))
            } else if p < 2 * h {
                F8(v[p].0 ^ (v[p - h].0 ^ f8_mul(lambda, v[p].0)))
            } else {
                v[p]
            },
    )
}

/// `ifft_butterfly` on the halves of `v`: `(u, w) -> (u + λ (w + u), w + u)`.
pub open spec fn ifft_butterfly_spec(v: Seq<F8>, lambda: u8) -> Seq<F8> {
    let h = v.len() / 2;
    Seq::new(
        v.len(),
        |p: int|
            if p < h {
                F8(v[p].0 ^ f8_mul(lambda, v[p + h].0 ^ v[p].0))
            } else if p < 2 * h {
                F8(v[p].0 ^ v[p - h].0)
            } else {
                v[p]
            },
    )
}

/// The recursion of `fft_rec(v, tw, idx)`: the butterfly with twiddle `tw[idx - 1]`, then the low half at
/// `2 idx` and the high half at `2 idx + 1`.
pub open spec fn fft_spec(v: Seq<F8>, tw: Seq<F8>, idx: int) -> Seq<F8>
    decreases v.len(),
{
    if v.len() <= 1 {
        v
    } else {
        let w = fft_butterfly_spec(v, tw[idx - 1].0);
        let h = v.len() / 2;
        fft_spec(w.subrange(0, h as int), tw, 2 * idx) + fft_spec(w.subrange(h as int, v.len() as int), tw, 2 * idx + 1)
    }
}

/// The recursion of `ifft_rec(v, tw, idx)`: the low half at `2 idx` and the high half at `2 idx + 1`, then
/// the inverse butterfly with twiddle `tw[idx - 1]`.
pub open spec fn ifft_spec(v: Seq<F8>, tw: Seq<F8>, idx: int) -> Seq<F8>
    decreases v.len(),
{
    if v.len() <= 1 {
        v
    } else {
        let h = v.len() / 2;
        ifft_butterfly_spec(
            ifft_spec(v.subrange(0, h as int), tw, 2 * idx) + ifft_spec(v.subrange(h as int, v.len() as int), tw, 2 * idx + 1),
            tw[idx - 1].0,
        )
    }
}

/// The first point of block `blk` of `2^m` points: `blk 2^m`, as a byte.
pub open spec fn block_offset(blk: nat, m: nat) -> u8 {
    (blk * pow2(m)) as u8
}

/// The twiddle table of a `2^k`-point NTT with offset `β`: entry `2^d - 1 + j`, for depth `d < k` and block
/// `j < 2^d`, is `Ŵ_(k-1-d)(β + j 2^(k-d))`, `Ŵ` of the first point of the block.
pub open spec fn twiddles_of(tw: Seq<F8>, k: nat, beta: u8) -> bool {
    &&& tw.len() + 1 == pow2(k)
    &&& forall|d: nat, j: nat|
        d < k && j < pow2(d) ==> (#[trigger] tw[pow2(d) - 1 + j]).0 == normalized_poly8(
            (k - 1 - d) as nat,
            beta ^ block_offset(j, (k - d) as nat),
        )
}

/// The twiddles of the subtree of `fft_rec` at `idx`, `2^m` points from `y` on: `tw[idx - 1] = Ŵ_(m-1)(y)`,
/// and the same for the low half from `y` and the high half from `y + b_(m-1)`.
pub open spec fn node_ok(tw: Seq<F8>, idx: int, m: nat, y: u8) -> bool
    decreases m,
{
    m == 0 || (tw[idx - 1].0 == normalized_poly8((m - 1) as nat, y) && node_ok(tw, 2 * idx, (m - 1) as nat, y)
        && node_ok(tw, 2 * idx + 1, (m - 1) as nat, y ^ basis8((m - 1) as nat)))
}

// ---------------------------------------------------------------------------------------------
// Field facts
// ---------------------------------------------------------------------------------------------
proof fn lemma_xor8(a: u8, b: u8, c: u8)
    ensures
        a ^ a == 0,
        a ^ 0 == a,
        0 ^ a == a,
        a ^ b == b ^ a,
        (a ^ b) ^ c == a ^ (b ^ c),
        (a ^ b) ^ b == a,
        a ^ (a ^ b) == b,
{
    assert(a ^ a == 0 && a ^ 0 == a && 0 ^ a == a && a ^ b == b ^ a && (a ^ b) ^ c == a ^ (b ^ c) && (a ^ b) ^ b == a
        && a ^ (a ^ b) == b) by (bit_vector);
}

/// `GF(2^8)` has no zero divisors.
pub proof fn lemma_f8_no_zero_divisors(a: u8, b: u8)
    requires
        f8_mul(a, b) == 0,
        a != 0,
    ensures
        b == 0,
{
    let ai = f8_inv(a);
    lemma_f8_inv_correct(a);
    lemma_f8_mul_comm(a, ai);
    lemma_f8_mul_assoc(ai, a, b);
    lemma_f8_mul_one(b);
    lemma_f8_mul_zero(ai);
}

/// `1^(-1) = 1`.
proof fn lemma_f8_inv_one()
    ensures
        f8_inv(1) == 1,
{
    lemma_f8_inv_correct(1);
    lemma_f8_mul_one(f8_inv(1));
}

proof fn lemma_f8_mul_xor_left(a: u8, b: u8, c: u8)
    ensures
        f8_mul(a ^ b, c) == f8_mul(a, c) ^ f8_mul(b, c),
{
    lemma_f8_mul_comm(a ^ b, c);
    lemma_f8_mul_comm(a, c);
    lemma_f8_mul_comm(b, c);
    lemma_f8_mul_xor_right(c, a, b);
}

/// `a (b c) = b (a c)`.
proof fn lemma_f8_mul_swap(a: u8, b: u8, c: u8)
    ensures
        f8_mul(a, f8_mul(b, c)) == f8_mul(b, f8_mul(a, c)),
{
    lemma_f8_mul_assoc(a, b, c);
    lemma_f8_mul_assoc(b, a, c);
    lemma_f8_mul_comm(a, b);
}

// ---------------------------------------------------------------------------------------------
// Bits of a byte
// ---------------------------------------------------------------------------------------------
/// `1 << s = 2^s` for a byte.
pub proof fn lemma_shl8(s: nat)
    requires
        s < 8,
    ensures
        basis8(s) as nat == pow2(s),
        pow2(s) <= 128,
{
    lemma2_to64();
    if s < 7 {
        lemma_pow2_strictly_increases(s, 7);
    }
    lemma_u8_shl_is_mul(1, s as u8);
}

/// Bit `s` against the comparisons with `2^s` and `2^(s+1)`.
proof fn lemma_bit8(x: u8, s: u8)
    requires
        s < 8,
    ensures
        (x >> s) == 1u8 ==> (x ^ (1u8 << s)) == sub(x, 1u8 << s) && (x ^ (1u8 << s)) < (1u8 << s),
        s < 7 ==> (x < (1u8 << s) ==> x < (1u8 << add(s, 1))),
        s < 7 ==> ((x ^ (1u8 << s)) < (1u8 << s) ==> x < (1u8 << add(s, 1))),
        s < 7 ==> (x < (1u8 << add(s, 1)) && !(x < (1u8 << s)) ==> (x ^ (1u8 << s)) < (1u8 << s)),
        s == 7 ==> (!(x < (1u8 << s)) ==> (x ^ (1u8 << s)) < (1u8 << s)),
        (x >> s) & 1u8 == 0u8 ==> (x ^ (1u8 << s)) == add(x, 1u8 << s),
{
    assert((x >> s) == 1u8 ==> (x ^ (1u8 << s)) == sub(x, 1u8 << s) && (x ^ (1u8 << s)) < (1u8 << s)) by (bit_vector)
        requires
            s < 8,
    ;
    assert(s < 7 ==> (x < (1u8 << s) ==> x < (1u8 << add(s, 1)))) by (bit_vector)
        requires
            s < 8,
    ;
    assert(s < 7 ==> ((x ^ (1u8 << s)) < (1u8 << s) ==> x < (1u8 << add(s, 1)))) by (bit_vector)
        requires
            s < 8,
    ;
    assert(s < 7 ==> (x < (1u8 << add(s, 1)) && !(x < (1u8 << s)) ==> (x ^ (1u8 << s)) < (1u8 << s))) by (bit_vector)
        requires
            s < 8,
    ;
    assert(s == 7 ==> (!(x < (1u8 << s)) ==> (x ^ (1u8 << s)) < (1u8 << s))) by (bit_vector);
    assert((x >> s) & 1u8 == 0u8 ==> (x ^ (1u8 << s)) == add(x, 1u8 << s)) by (bit_vector)
        requires
            s < 8,
    ;
}

/// An index `u` of the high half of `2^(s+1)` points: `u - 2^s = u ⊕ 2^s`, below `2^s`.
proof fn lemma_high_half(u: int, s: nat)
    requires
        s < 8,
        pow2(s) <= u < 2 * pow2(s),
    ensures
        (u - pow2(s)) as u8 == (u as u8) ^ basis8(s),
        ((u as u8) ^ basis8(s)) < basis8(s),
{
    lemma_shl8(s);
    let x = u as u8;
    assert(x as int == u);
    lemma_u8_shr_is_div(x, s as u8);
    lemma_fundamental_div_mod_converse(u, pow2(s) as int, 1, u - pow2(s));
    lemma_bit8(x, s as u8);
}

// ---------------------------------------------------------------------------------------------
// Subspace polynomials
// ---------------------------------------------------------------------------------------------
/// `s_i` is F_2-linear: `s_i(x + y) = s_i(x) + s_i(y)`.
pub proof fn lemma_subspace_poly8_additive(i: nat, x: u8, y: u8)
    ensures
        subspace_poly8(i, x ^ y) == subspace_poly8(i, x) ^ subspace_poly8(i, y),
    decreases i,
{
    if i > 0 {
        let j = (i - 1) as nat;
        lemma_subspace_poly8_additive(j, x, y);
        let a = subspace_poly8(j, x);
        let b = subspace_poly8(j, y);
        let c = subspace_poly8(j, basis8(j));
        // (a + b)(a + b + c) = a(a + c) + a b + b(b + c) + b a
        assert((a ^ b) ^ c == (a ^ c) ^ b && (a ^ b) ^ c == (b ^ c) ^ a) by (bit_vector);
        lemma_f8_mul_xor_left(a, b, (a ^ b) ^ c);
        lemma_f8_mul_xor_right(a, a ^ c, b);
        lemma_f8_mul_xor_right(b, b ^ c, a);
        lemma_f8_mul_comm(a, b);
        let (p, q, r) = (f8_mul(a, a ^ c), f8_mul(b, b ^ c), f8_mul(a, b));
        assert((p ^ r) ^ (q ^ r) == p ^ q) by (bit_vector);
    }
}

/// The normalized `Ŵ_i` is F_2-linear too.
pub proof fn lemma_normalized_poly8_additive(i: nat, x: u8, y: u8)
    ensures
        normalized_poly8(i, x ^ y) == normalized_poly8(i, x) ^ normalized_poly8(i, y),
{
    lemma_subspace_poly8_additive(i, x, y);
    lemma_f8_mul_xor_right(f8_inv(subspace_poly8(i, basis8(i))), subspace_poly8(i, x), subspace_poly8(i, y));
}

/// `s_i` vanishes on `{0, .., 2^i - 1}`, the span of `b_0 .. b_(i-1)`.
pub proof fn lemma_subspace_poly8_vanishes(i: nat, x: u8)
    requires
        i < 8,
        x < basis8(i),
    ensures
        subspace_poly8(i, x) == 0,
    decreases i,
{
    if i == 0 {
        assert(x < (1u8 << 0u8) ==> x == 0) by (bit_vector);
    } else {
        let j = (i - 1) as nat;
        let b = basis8(j);
        let p = subspace_poly8(j, x);
        let c = subspace_poly8(j, b);
        lemma_bit8(x, j as u8);
        assert(add(j as u8, 1) == i as u8);
        if x < b {
            lemma_subspace_poly8_vanishes(j, x);
            lemma_f8_mul_zero(p ^ c);
        } else {
            lemma_subspace_poly8_vanishes(j, x ^ b);
            lemma_subspace_poly8_additive(j, x ^ b, b);
            lemma_xor8(x, b, 0);
            lemma_xor8(c, 0, 0);
            lemma_f8_mul_zero(p);
        }
    }
}

/// The roots of `s_i` lie below `2^i`: `s_i(x) = 0` only on `{0, .., 2^i - 1}`.
pub proof fn lemma_subspace_poly8_roots(i: nat, x: u8)
    requires
        i < 8,
        subspace_poly8(i, x) == 0,
    ensures
        x < basis8(i),
    decreases i,
{
    if i == 0 {
        assert(0u8 < (1u8 << 0u8)) by (bit_vector);
    } else {
        let j = (i - 1) as nat;
        let b = basis8(j);
        let p = subspace_poly8(j, x);
        let c = subspace_poly8(j, b);
        lemma_bit8(x, j as u8);
        assert(add(j as u8, 1) == i as u8);
        if p == 0 {
            lemma_subspace_poly8_roots(j, x);
        } else {
            lemma_f8_no_zero_divisors(p, p ^ c);
            lemma_subspace_poly8_additive(j, x, b);
            lemma_subspace_poly8_roots(j, x ^ b);
        }
    }
}

/// Every normalizer works: `Ŵ_i(b_i) = 1` for `i < 8`.
pub proof fn lemma_normalized_poly8_at_basis(i: nat)
    requires
        i < 8,
    ensures
        normalized_poly8(i, basis8(i)) == 1,
{
    let y = subspace_poly8(i, basis8(i));
    if y == 0 {
        lemma_subspace_poly8_roots(i, basis8(i));
    }
    lemma_f8_inv_correct(y);
    lemma_f8_mul_comm(y, f8_inv(y));
}

/// `Ŵ_i` vanishes on `{0, .., 2^i - 1}`.
pub proof fn lemma_normalized_poly8_vanishes(i: nat, x: u8)
    requires
        i < 8,
        x < basis8(i),
    ensures
        normalized_poly8(i, x) == 0,
{
    lemma_subspace_poly8_vanishes(i, x);
    lemma_f8_mul_zero(f8_inv(subspace_poly8(i, basis8(i))));
}

/// `Ŵ_0(x) = x`.
proof fn lemma_normalized_poly8_zero(x: u8)
    ensures
        normalized_poly8(0, x) == x,
{
    assert(basis8(0) == 1) by {
        assert((1u8 << 0u8) == 1u8) by (bit_vector);
    }
    lemma_f8_inv_one();
    lemma_f8_mul_one(x);
}

// ---------------------------------------------------------------------------------------------
// The novel-basis polynomial is linear in its coefficients
// ---------------------------------------------------------------------------------------------
proof fn lemma_lincomb_halves(a: Seq<F8>, t: u8, b: Seq<F8>, h: int)
    requires
        a.len() == b.len() == 2 * h,
        h >= 0,
    ensures
        lincomb(a, t, b).subrange(0, h) == lincomb(a.subrange(0, h), t, b.subrange(0, h)),
        lincomb(a, t, b).subrange(h, 2 * h) == lincomb(a.subrange(h, 2 * h), t, b.subrange(h, 2 * h)),
{
    assert(lincomb(a, t, b).subrange(0, h) =~= lincomb(a.subrange(0, h), t, b.subrange(0, h)));
    assert(lincomb(a, t, b).subrange(h, 2 * h) =~= lincomb(a.subrange(h, 2 * h), t, b.subrange(h, 2 * h)));
}

/// `P_(a + t b) = P_a + t P_b`.
pub proof fn lemma_novel8_lincomb(m: nat, a: Seq<F8>, t: u8, b: Seq<F8>, x: u8)
    requires
        a.len() == pow2(m),
        b.len() == pow2(m),
    ensures
        novel8(m, lincomb(a, t, b), x) == novel8(m, a, x) ^ f8_mul(t, novel8(m, b, x)),
    decreases m,
{
    if m > 0 {
        let j = (m - 1) as nat;
        let h = pow2(j) as int;
        lemma_pow2_unfold(m);
        lemma_lincomb_halves(a, t, b, h);
        let (al, ah, bl, bh) = (a.subrange(0, h), a.subrange(h, 2 * h), b.subrange(0, h), b.subrange(h, 2 * h));
        lemma_novel8_lincomb(j, al, t, bl, x);
        lemma_novel8_lincomb(j, ah, t, bh, x);
        let w = normalized_poly8(j, x);
        let (pal, pah, pbl, pbh) = (novel8(j, al, x), novel8(j, ah, x), novel8(j, bl, x), novel8(j, bh, x));
        // (pal + t pbl) + w (pah + t pbh) = (pal + w pah) + t (pbl + w pbh)
        lemma_f8_mul_xor_right(w, pah, f8_mul(t, pbh));
        lemma_f8_mul_swap(w, t, pbh);
        lemma_f8_mul_xor_right(t, pbl, f8_mul(w, pbh));
        let (p1, p2, p3) = (f8_mul(t, pbl), f8_mul(w, pah), f8_mul(t, f8_mul(w, pbh)));
        assert((pal ^ p1) ^ (p2 ^ p3) == (pal ^ p2) ^ (p1 ^ p3)) by (bit_vector);
    } else {
        lemma2_to64();
    }
}

// ---------------------------------------------------------------------------------------------
// The novel-basis polynomial as a flat sum
// ---------------------------------------------------------------------------------------------
/// The novel basis polynomial `X_j(x) = Π_{i < m} Ŵ_i(x)^(bit_i(j))`, bit `i` of `j` being `(j / 2^i) mod 2`.
pub open spec fn novel_basis8(m: nat, j: int, x: u8) -> u8
    decreases m,
{
    if m == 0 {
        1
    } else {
        let rest = novel_basis8((m - 1) as nat, j, x);
        if (j / pow2((m - 1) as nat) as int) % 2 == 1 {
            f8_mul(rest, normalized_poly8((m - 1) as nat, x))
        } else {
            rest
        }
    }
}

/// The novel-basis polynomial with coefficients `a`, as the flat sum `Σ_{j < 2^m} a_j X_j(x)`.
pub open spec fn novel8_sum(m: nat, a: Seq<F8>, x: u8) -> u8 {
    xor_sum8(|j: int| f8_mul(a[j].0, novel_basis8(m, j, x)), pow2(m))
}

/// `X_j` reads only the low `n` bits of `j`.
proof fn lemma_novel_basis8_periodic(n: nat, j: int, q: int, x: u8)
    requires
        j >= 0,
        q >= 0,
    ensures
        novel_basis8(n, j + q * pow2(n), x) == novel_basis8(n, j, x),
    decreases n,
{
    if n > 0 {
        let p = pow2((n - 1) as nat) as int;
        lemma_pow2_unfold(n);
        lemma_pow2_pos((n - 1) as nat);
        assert(j + q * pow2(n) == j + (2 * q) * p) by (nonlinear_arith)
            requires
                pow2(n) == 2 * p,
        ;
        lemma_novel_basis8_periodic((n - 1) as nat, j, 2 * q, x);
        lemma_mod_multiples_vanish(q, j / p, 2);
        assert((j + (2 * q) * p) / p == 2 * q + j / p) by {
            lemma_fundamental_div_mod(j, p);
            lemma_mod_pos_bound(j, p);
            assert(j + (2 * q) * p == p * (2 * q + j / p) + j % p) by (nonlinear_arith)
                requires
                    j == p * (j / p) + j % p,
            ;
            lemma_fundamental_div_mod_converse(j + (2 * q) * p, p, 2 * q + j / p, j % p);
        }
    }
}

/// Multiplication distributes over a sum.
proof fn lemma_xor_sum8_scale(c: u8, f: spec_fn(int) -> u8, n: nat)
    ensures
        f8_mul(c, xor_sum8(f, n)) == xor_sum8(|j: int| f8_mul(c, f(j)), n),
    decreases n,
{
    if n == 0 {
        lemma_f8_mul_zero(c);
    } else {
        lemma_xor_sum8_scale(c, f, (n - 1) as nat);
        lemma_f8_mul_xor_right(c, xor_sum8(f, (n - 1) as nat), f(n - 1));
    }
}

/// The top-bit split is the flat sum: `novel8(m, a, x) = Σ_{j < 2^m} a_j X_j(x)`.
pub proof fn lemma_novel8_flat(m: nat, a: Seq<F8>, x: u8)
    requires
        a.len() == pow2(m),
    ensures
        novel8(m, a, x) == novel8_sum(m, a, x),
    decreases m,
{
    if m == 0 {
        lemma2_to64();
        lemma_f8_mul_one(a[0].0);
        let y = a[0].0;
        assert(0u8 ^ y == y) by (bit_vector);
        let f = |j: int| f8_mul(a[j].0, novel_basis8(0, j, x));
        assert(novel_basis8(0, 0, x) == 1);
        assert(xor_sum8(f, 1) == xor_sum8(f, 0) ^ f(0));
        assert(novel8_sum(0, a, x) == xor_sum8(f, 1));
    } else {
        let n = (m - 1) as nat;
        let h = pow2(n) as int;
        lemma_pow2_unfold(m);
        lemma_pow2_pos(n);
        let (al, ah) = (a.subrange(0, h), a.subrange(h, 2 * h));
        lemma_novel8_flat(n, al, x);
        lemma_novel8_flat(n, ah, x);
        let w = normalized_poly8(n, x);
        let f = |j: int| f8_mul(a[j].0, novel_basis8(m, j, x));
        lemma_xor_sum8_split(f, h as nat, h as nat);
        // The low half: bit `m - 1` of `j < 2^(m-1)` is zero.
        let fl = |j: int| f8_mul(al[j].0, novel_basis8(n, j, x));
        assert forall|j: int| 0 <= j < h implies #[trigger] f(j) == fl(j) by {
            assert(j / h == 0) by {
                lemma_fundamental_div_mod_converse(j, h, 0, j);
            }
        }
        lemma_xor_sum8_ext(f, fl, h as nat);
        // The high half: bit `m - 1` of `2^(m-1) + t` is one, and the lower bits are those of `t`.
        let fh = |t: int| f8_mul(ah[t].0, novel_basis8(n, t, x));
        let g = |t: int| f(h + t);
        assert forall|t: int| 0 <= t < h implies #[trigger] g(t) == f8_mul(w, fh(t)) by {
            lemma_novel_basis8_periodic(n, t, 1, x);
            assert((h + t) / h == 1) by {
                lemma_fundamental_div_mod_converse(h + t, h, 1, t);
            }
            assert(t + 1 * pow2(n) == h + t);
            let (c, b) = (ah[t].0, novel_basis8(n, t, x));
            assert(a[h + t].0 == c);
            // c (b w) = w (c b)
            lemma_f8_mul_comm(b, w);
            lemma_f8_mul_swap(c, w, b);
        }
        lemma_xor_sum8_ext(g, |t: int| f8_mul(w, fh(t)), h as nat);
        lemma_xor_sum8_scale(w, fh, h as nat);
        lemma_xor_sum8_ext(|t: int| f((h as nat) + t), g, h as nat);
        assert(novel8_sum(n, al, x) == xor_sum8(fl, h as nat));
        assert(novel8_sum(n, ah, x) == xor_sum8(fh, h as nat));
        assert(novel8_sum(m, a, x) == xor_sum8(f, (h as nat) + (h as nat)));
    }
}

// ---------------------------------------------------------------------------------------------
// The forward transform evaluates, the inverse undoes it
// ---------------------------------------------------------------------------------------------
proof fn lemma_fft_spec_len(v: Seq<F8>, tw: Seq<F8>, idx: int)
    ensures
        fft_spec(v, tw, idx).len() == v.len(),
    decreases v.len(),
{
    if v.len() > 1 {
        let w = fft_butterfly_spec(v, tw[idx - 1].0);
        let h = v.len() / 2;
        lemma_fft_spec_len(w.subrange(0, h as int), tw, 2 * idx);
        lemma_fft_spec_len(w.subrange(h as int, v.len() as int), tw, 2 * idx + 1);
    }
}

proof fn lemma_ifft_spec_len(v: Seq<F8>, tw: Seq<F8>, idx: int)
    ensures
        ifft_spec(v, tw, idx).len() == v.len(),
    decreases v.len(),
{
    if v.len() > 1 {
        let h = v.len() / 2;
        lemma_ifft_spec_len(v.subrange(0, h as int), tw, 2 * idx);
        lemma_ifft_spec_len(v.subrange(h as int, v.len() as int), tw, 2 * idx + 1);
    }
}

/// The forward transform evaluates the novel-basis polynomial: on `2^m` coefficients, with the twiddles of
/// a subtree from `y` ([`node_ok`]), output word `u` is `P(y + u)`.
pub proof fn lemma_fft_evaluates_from(v: Seq<F8>, tw: Seq<F8>, idx: int, m: nat, y: u8)
    requires
        m <= 8,
        v.len() == pow2(m),
        node_ok(tw, idx, m, y),
    ensures
        fft_spec(v, tw, idx).len() == v.len(),
        forall|u: int| 0 <= u < v.len() ==> (#[trigger] fft_spec(v, tw, idx)[u]).0 == novel8(m, v, y ^ (u as u8)),
    decreases m,
{
    lemma_fft_spec_len(v, tw, idx);
    if m == 0 {
        lemma2_to64();
        assert forall|u: int| 0 <= u < v.len() implies (#[trigger] fft_spec(v, tw, idx)[u]).0 == novel8(m, v, y ^ (u as u8)) by {
            assert(u == 0);
            assert(y ^ 0u8 == y) by (bit_vector);
        }
    } else {
        let j = (m - 1) as nat;
        let h = pow2(j) as int;
        let n = v.len() as int;
        lemma_pow2_unfold(m);
        lemma_pow2_pos(j);
        lemma_shl8(j);
        let lambda = tw[idx - 1].0;
        let w = fft_butterfly_spec(v, lambda);
        let (lo, hi) = (w.subrange(0, h), w.subrange(h, n));
        let (vl, vh) = (v.subrange(0, h), v.subrange(h, n));
        let b = basis8(j);
        lemma_fft_evaluates_from(lo, tw, 2 * idx, j, y);
        lemma_fft_evaluates_from(hi, tw, 2 * idx + 1, j, y ^ b);
        // The two halves after the butterfly, as combinations of the coefficient halves.
        assert(lo =~= lincomb(vl, lambda, vh));
        assert forall|i: int| 0 <= i < h implies #[trigger] hi[i] == lincomb(vl, lambda ^ 1, vh)[i] by {
            let (p, q) = (v[i].0, v[i + h].0);
            lemma_f8_mul_xor_left(lambda, 1, q);
            lemma_f8_mul_one(q);
            let r = f8_mul(lambda, q);
            assert(q ^ (p ^ r) == p ^ (r ^ q)) by (bit_vector);
        }
        assert(hi =~= lincomb(vl, lambda ^ 1, vh));
        lemma_novel8_lincomb(j, vl, lambda, vh, y);
        assert forall|u: int| 0 <= u < n implies (#[trigger] fft_spec(v, tw, idx)[u]).0 == novel8(m, v, y ^ (u as u8)) by {
            let x = y ^ (u as u8);
            lemma_normalized_poly8_additive(j, y, u as u8);
            lemma_novel8_lincomb(j, vl, lambda, vh, x);
            lemma_novel8_lincomb(j, vl, lambda ^ 1, vh, x);
            if u < h {
                assert((u as u8) < b);
                lemma_normalized_poly8_vanishes(j, u as u8);
                lemma_xor8(lambda, 0, 0);
                assert(fft_spec(v, tw, idx)[u] == fft_spec(lo, tw, 2 * idx)[u]);
            } else {
                lemma_high_half(u, j);
                let u8l = (u - h) as u8;
                lemma_normalized_poly8_additive(j, b, u8l);
                lemma_normalized_poly8_at_basis(j);
                lemma_normalized_poly8_vanishes(j, u8l);
                lemma_xor8(1, 0, 0);
                let ux = u as u8;
                assert((y ^ b) ^ (ux ^ b) == y ^ ux) by (bit_vector);
                assert(b ^ (ux ^ b) == ux) by (bit_vector);
                assert(fft_spec(v, tw, idx)[u] == fft_spec(hi, tw, 2 * idx + 1)[u - h]);
            }
        }
    }
}

/// The inverse butterfly undoes the forward one.
proof fn lemma_butterfly8_inverse(u: u8, w: u8, t: u8)
    ensures
        ({
            let (u1, w1) = (u ^ f8_mul(t, w), w ^ (u ^ f8_mul(t, w)));
            u1 ^ f8_mul(t, w1 ^ u1) == u && w1 ^ u1 == w
        }),
        ({
            let (u1, w1) = (u ^ f8_mul(t, w ^ u), w ^ u);
            u1 ^ f8_mul(t, w1) == u && w1 ^ (u1 ^ f8_mul(t, w1)) == w
        }),
{
    let r = f8_mul(t, w);
    assert((w ^ (u ^ r)) ^ (u ^ r) == w) by (bit_vector);
    assert((u ^ r) ^ r == u) by (bit_vector);
    let s = f8_mul(t, w ^ u);
    assert((u ^ s) ^ s == u) by (bit_vector);
    assert((w ^ u) ^ ((u ^ s) ^ s) == w) by (bit_vector);
}

/// The inverse transform undoes the forward one, for every twiddle table and every buffer.
pub proof fn lemma_ifft_after_fft(v: Seq<F8>, tw: Seq<F8>, idx: int)
    ensures
        ifft_spec(fft_spec(v, tw, idx), tw, idx) == v,
    decreases v.len(),
{
    if v.len() > 1 {
        let n = v.len() as int;
        let h = n / 2;
        let lambda = tw[idx - 1].0;
        let w = fft_butterfly_spec(v, lambda);
        let (lo, hi) = (w.subrange(0, h), w.subrange(h, n));
        lemma_ifft_after_fft(lo, tw, 2 * idx);
        lemma_ifft_after_fft(hi, tw, 2 * idx + 1);
        lemma_fft_spec_len(lo, tw, 2 * idx);
        lemma_fft_spec_len(hi, tw, 2 * idx + 1);
        let f = fft_spec(v, tw, idx);
        assert(f.subrange(0, h) =~= fft_spec(lo, tw, 2 * idx));
        assert(f.subrange(h, n) =~= fft_spec(hi, tw, 2 * idx + 1));
        assert(fft_spec(lo, tw, 2 * idx) + fft_spec(hi, tw, 2 * idx + 1) == f);
        let g = ifft_spec(fft_spec(lo, tw, 2 * idx), tw, 2 * idx) + ifft_spec(fft_spec(hi, tw, 2 * idx + 1), tw, 2 * idx + 1);
        assert(g =~= w);
        assert forall|p: int| 0 <= p < n implies #[trigger] ifft_butterfly_spec(w, lambda)[p] == v[p] by {
            if p < h {
                lemma_butterfly8_inverse(v[p].0, v[p + h].0, lambda);
            } else if p < 2 * h {
                lemma_butterfly8_inverse(v[p - h].0, v[p].0, lambda);
            }
        }
        assert(ifft_butterfly_spec(w, lambda) =~= v);
    }
}

/// The forward transform undoes the inverse one, for every twiddle table and every buffer.
#[verifier::rlimit(30)]
pub proof fn lemma_fft_after_ifft(v: Seq<F8>, tw: Seq<F8>, idx: int)
    ensures
        fft_spec(ifft_spec(v, tw, idx), tw, idx) == v,
    decreases v.len(),
{
    if v.len() > 1 {
        let n = v.len() as int;
        let h = n / 2;
        let lambda = tw[idx - 1].0;
        let (vl, vh) = (v.subrange(0, h), v.subrange(h, n));
        lemma_fft_after_ifft(vl, tw, 2 * idx);
        lemma_fft_after_ifft(vh, tw, 2 * idx + 1);
        lemma_ifft_spec_len(vl, tw, 2 * idx);
        lemma_ifft_spec_len(vh, tw, 2 * idx + 1);
        let g = ifft_spec(vl, tw, 2 * idx) + ifft_spec(vh, tw, 2 * idx + 1);
        let iv = ifft_spec(v, tw, idx);
        assert(iv == ifft_butterfly_spec(g, lambda));
        let w = fft_butterfly_spec(iv, lambda);
        assert forall|p: int| 0 <= p < n implies #[trigger] w[p] == g[p] by {
            if p < h {
                lemma_butterfly8_inverse(g[p].0, g[p + h].0, lambda);
            } else if p < 2 * h {
                lemma_butterfly8_inverse(g[p - h].0, g[p].0, lambda);
            }
        }
        assert(w =~= g);
        assert(w.subrange(0, h) =~= ifft_spec(vl, tw, 2 * idx));
        assert(w.subrange(h, n) =~= ifft_spec(vh, tw, 2 * idx + 1));
        assert(fft_spec(iv, tw, idx) =~= v);
    }
}

/// `2^k <= 256` for `k <= 8`.
proof fn lemma_pow2_le_256(k: nat)
    requires
        k <= 8,
    ensures
        pow2(k) <= 256,
        pow2(k) >= 1,
{
    lemma2_to64();
    if k < 8 {
        lemma_pow2_strictly_increases(k, 8);
    }
}

/// The first point of the high half of a block: `blk 2^m + 2^(m-1) = (blk 2^m) ⊕ b_(m-1)`.
proof fn lemma_block_offset_halves(blk: nat, m: nat)
    requires
        1 <= m <= 8,
        blk * pow2(m) + pow2(m) <= 256,
    ensures
        block_offset(2 * blk, (m - 1) as nat) == block_offset(blk, m),
        block_offset(2 * blk + 1, (m - 1) as nat) == block_offset(blk, m) ^ basis8((m - 1) as nat),
{
    let j = (m - 1) as nat;
    let h = pow2(j);
    lemma_pow2_unfold(m);
    lemma_pow2_pos(j);
    lemma_shl8(j);
    let x = blk * pow2(m);
    assert(2 * blk * h == x) by (nonlinear_arith)
        requires
            x == blk * pow2(m),
            pow2(m) == 2 * h,
    ;
    assert((2 * blk + 1) * h == x + h) by (nonlinear_arith)
        requires
            x == blk * pow2(m),
            pow2(m) == 2 * h,
    ;
    assert(x + h < 256) by (nonlinear_arith)
        requires
            x + 2 * h <= 256,
            h >= 1,
    ;
    let xb = x as u8;
    lemma_u8_shr_is_div(xb, j as u8);
    lemma_div_multiples_vanish((2 * blk) as int, h as int);
    assert(x as int == h * (2 * blk)) by (nonlinear_arith)
        requires
            2 * blk * h == x,
    ;
    assert(xb >> (j as u8) == 2 * blk);
    let q = (2 * blk) as u8;
    assert(q == ((2 * blk) % 256) as u8);
    assert(((2 * blk) as u8) & 1u8 == 0u8) by {
        lemma_mod_multiples_basic(blk as int, 2);
        assert((2 * blk) % 2 == 0);
        let qq = (2 * blk) as u8;
        assert(qq % 2 == 0) by {
            lemma_mod_mod((2 * blk) as int, 2, 128);
        }
        assert(qq % 2 == 0 ==> qq & 1u8 == 0u8) by (bit_vector);
    }
    lemma_bit8(xb, j as u8);
}

/// The twiddle table of offset `β` holds the twiddles of every subtree: at depth `d`, block `blk` covers the
/// `2^(k-d)` points from `β + blk 2^(k-d)` on.
proof fn lemma_twiddles_node_ok(tw: Seq<F8>, k: nat, beta: u8, d: nat, blk: nat)
    requires
        twiddles_of(tw, k, beta),
        k <= 8,
        d <= k,
        blk < pow2(d),
    ensures
        node_ok(tw, (pow2(d) + blk) as int, (k - d) as nat, beta ^ block_offset(blk, (k - d) as nat)),
    decreases k - d,
{
    if d < k {
        let m = (k - d) as nat;
        let j = (m - 1) as nat;
        let idx = (pow2(d) + blk) as int;
        let y = beta ^ block_offset(blk, m);
        assert(tw[pow2(d) - 1 + blk] == tw[idx - 1]);
        lemma_pow2_unfold(d + 1);
        lemma_twiddles_node_ok(tw, k, beta, d + 1, 2 * blk);
        lemma_twiddles_node_ok(tw, k, beta, d + 1, 2 * blk + 1);
        assert(2 * idx == pow2(d + 1) + 2 * blk);
        assert(2 * idx + 1 == pow2(d + 1) + (2 * blk + 1));
        assert((k - (d + 1)) as nat == j);
        // The block lies inside the domain of `2^k <= 256` points.
        lemma_pow2_adds(d, m);
        lemma_pow2_le_256(k);
        assert(blk * pow2(m) + pow2(m) <= 256) by (nonlinear_arith)
            requires
                blk + 1 <= pow2(d),
                pow2(d) * pow2(m) == pow2(k),
                pow2(k) <= 256,
        ;
        lemma_block_offset_halves(blk, m);
        let b = basis8(j);
        let o = block_offset(blk, m);
        assert((beta ^ o) ^ b == beta ^ (o ^ b)) by (bit_vector);
    }
}

/// The forward transform of a `2^k`-point NTT with offset `β` (`fft_rec` from the root) evaluates the
/// novel-basis polynomial on the domain `β + {0, .., 2^k - 1}`: output word `u` is `P(β + u)`, the point of
/// index `u` being `β ⊕ u` (no bit reversal).
pub proof fn lemma_fft_evaluates(tw: Seq<F8>, k: nat, beta: u8, v: Seq<F8>)
    requires
        twiddles_of(tw, k, beta),
        k <= 8,
        v.len() == pow2(k),
    ensures
        fft_spec(v, tw, 1).len() == v.len(),
        forall|u: int| 0 <= u < v.len() ==> (#[trigger] fft_spec(v, tw, 1)[u]).0 == novel8(k, v, beta ^ (u as u8)),
{
    lemma2_to64();
    lemma_twiddles_node_ok(tw, k, beta, 0, 0);
    assert(block_offset(0, k) == 0);
    assert(beta ^ 0u8 == beta) by (bit_vector);
    lemma_fft_evaluates_from(v, tw, 1, k, beta);
}

/// The inverse transform interpolates: if `e` holds the evaluations of `P` on the domain `β + {0, .., 2^k - 1}`
/// (word `u` is `P(β + u)`), then `ifft_rec` from the root returns the novel-basis coefficients of `P`.
pub proof fn lemma_ifft_interpolates(tw: Seq<F8>, k: nat, beta: u8, a: Seq<F8>, e: Seq<F8>)
    requires
        twiddles_of(tw, k, beta),
        k <= 8,
        a.len() == pow2(k),
        e.len() == pow2(k),
        forall|u: int| 0 <= u < e.len() ==> (#[trigger] e[u]).0 == novel8(k, a, beta ^ (u as u8)),
    ensures
        ifft_spec(e, tw, 1) == a,
{
    lemma_fft_evaluates(tw, k, beta, a);
    assert(fft_spec(a, tw, 1) =~= e);
    lemma_ifft_after_fft(a, tw, 1);
}

// ---------------------------------------------------------------------------------------------
// Translating a polynomial stays in the novel basis
// ---------------------------------------------------------------------------------------------
/// The novel-basis coefficients of `x -> P_a(x + c)`: on the top-bit split `P_a = A + Ŵ_(m-1) B`,
/// `P_a(x + c) = A(x + c) + Ŵ_(m-1)(c) B(x + c) + Ŵ_(m-1)(x) B(x + c)`, with `A` and `B` translated recursively.
pub open spec fn translate(m: nat, a: Seq<F8>, c: u8) -> Seq<F8>
    decreases m,
{
    if m == 0 {
        a
    } else {
        let h = pow2((m - 1) as nat) as int;
        let qa = translate((m - 1) as nat, a.subrange(0, h), c);
        let qb = translate((m - 1) as nat, a.subrange(h, 2 * h), c);
        lincomb(qa, normalized_poly8((m - 1) as nat, c), qb) + qb
    }
}

/// `P_(translate(a, c))(x) = P_a(x + c)` for every `x`.
pub proof fn lemma_translate(m: nat, a: Seq<F8>, c: u8, x: u8)
    requires
        a.len() == pow2(m),
    ensures
        translate(m, a, c).len() == pow2(m),
        novel8(m, translate(m, a, c), x) == novel8(m, a, x ^ c),
    decreases m,
{
    if m > 0 {
        let j = (m - 1) as nat;
        let h = pow2(j) as int;
        lemma_pow2_unfold(m);
        let (al, ah) = (a.subrange(0, h), a.subrange(h, 2 * h));
        let qa = translate(j, al, c);
        let qb = translate(j, ah, c);
        lemma_translate(j, al, c, x);
        lemma_translate(j, ah, c, x);
        let wc = normalized_poly8(j, c);
        let wx = normalized_poly8(j, x);
        let t = translate(m, a, c);
        assert(t.subrange(0, h) =~= lincomb(qa, wc, qb));
        assert(t.subrange(h, 2 * h) =~= qb);
        lemma_novel8_lincomb(j, qa, wc, qb, x);
        lemma_normalized_poly8_additive(j, x, c);
        let nb = novel8(j, ah, x ^ c);
        lemma_f8_mul_xor_left(wx, wc, nb);
        let (na, p, q) = (novel8(j, al, x ^ c), f8_mul(wc, nb), f8_mul(wx, nb));
        assert((na ^ p) ^ q == na ^ (q ^ p)) by (bit_vector);
    } else {
        lemma2_to64();
        assert(x ^ c == x ^ c);
    }
}

// ---------------------------------------------------------------------------------------------
// The columns of `forward_Λ ∘ inverse_S` are XOR shifts of one another
// ---------------------------------------------------------------------------------------------
/// The unit vector `e_t` of length `n`.
pub open spec fn unit(n: nat, t: int) -> Seq<F8> {
    Seq::new(n, |i: int| if i == t { F8(1) } else { F8(0) })
}

/// Column `t` of `M = forward_Λ ∘ inverse_S`: the forward transform with twiddles `tw_l` of the inverse
/// transform with twiddles `tw_s` of `e_t`, on `n` words.
pub open spec fn lde_column(tw_s: Seq<F8>, tw_l: Seq<F8>, n: nat, t: int) -> Seq<F8> {
    fft_spec(ifft_spec(unit(n, t), tw_s, 1), tw_l, 1)
}

/// Below `2^k`, indices stay below `2^k` under XOR.
proof fn lemma_xor_below(i: int, j: int, k: nat)
    requires
        k <= 8,
        0 <= i < pow2(k),
        0 <= j < pow2(k),
    ensures
        (((i as u8) ^ (j as u8)) as int) < pow2(k),
{
    if k < 8 {
        lemma_shl8(k);
        let (x, y, s) = (i as u8, j as u8, k as u8);
        assert(x < (1u8 << s) && y < (1u8 << s) ==> (x ^ y) < (1u8 << s)) by (bit_vector)
            requires
                s < 8,
        ;
    } else {
        lemma2_to64();
    }
}

/// The `S`-to-`Λ` extension matrix commutes with XOR shifts: `M[i][j] = M[i ⊕ j][0]`, for any two `2^k`-point
/// NTTs (offsets `β_s` and `β_l`). The column of `e_j` is the column of `e_0` read at `i ⊕ j`.
///
/// The interpolant of `e_j` on `S` is the interpolant of `e_0` translated by `j` ([`lemma_translate`]: the
/// translate has the right evaluations on `S`, and the inverse transform is injective), so its value at
/// `β_l + i` is the value of the interpolant of `e_0` at `β_l + (i ⊕ j)`.
pub proof fn lemma_lde_shift(tw_s: Seq<F8>, tw_l: Seq<F8>, k: nat, beta_s: u8, beta_l: u8, i: int, j: int)
    requires
        twiddles_of(tw_s, k, beta_s),
        twiddles_of(tw_l, k, beta_l),
        k <= 8,
        0 <= i < pow2(k),
        0 <= j < pow2(k),
    ensures
        lde_column(tw_s, tw_l, pow2(k), j).len() == pow2(k),
        lde_column(tw_s, tw_l, pow2(k), j)[i] == lde_column(tw_s, tw_l, pow2(k), 0)[((i as u8) ^ (j as u8)) as int],
{
    let n = pow2(k);
    let (e0, ej) = (unit(n, 0), unit(n, j));
    let (p0, pj) = (ifft_spec(e0, tw_s, 1), ifft_spec(ej, tw_s, 1));
    lemma_ifft_spec_len(e0, tw_s, 1);
    lemma_ifft_spec_len(ej, tw_s, 1);
    lemma_fft_after_ifft(e0, tw_s, 1);
    lemma_fft_evaluates(tw_s, k, beta_s, p0);
    lemma_fft_evaluates(tw_l, k, beta_l, p0);
    lemma_fft_evaluates(tw_l, k, beta_l, pj);
    let j8 = j as u8;
    let q = translate(k, p0, j8);
    lemma_translate(k, p0, j8, 0);
    // `q` interpolates `e_j` on `S`.
    lemma_fft_evaluates(tw_s, k, beta_s, q);
    assert forall|u: int| 0 <= u < n implies #[trigger] fft_spec(q, tw_s, 1)[u] == ej[u] by {
        let u8v = u as u8;
        lemma_translate(k, p0, j8, beta_s ^ u8v);
        assert((beta_s ^ u8v) ^ j8 == beta_s ^ (u8v ^ j8)) by (bit_vector);
        lemma_xor_below(u, j, k);
        let w = (u8v ^ j8) as int;
        assert(w as u8 == u8v ^ j8);
        assert(fft_spec(p0, tw_s, 1)[w] == e0[w]);
        lemma_pow2_le_256(k);
        assert((u8v ^ j8 == 0u8) == (u8v == j8)) by (bit_vector);
        assert((u as u8 == j as u8) == (u == j));
    }
    assert(fft_spec(q, tw_s, 1) =~= ej);
    lemma_ifft_after_fft(q, tw_s, 1);
    assert(q == pj);
    // So `M[i][j] = P_q(β_l + i) = P_(p0)(β_l + (i ⊕ j)) = M[i ⊕ j][0]`.
    let i8 = i as u8;
    lemma_translate(k, p0, j8, beta_l ^ i8);
    assert((beta_l ^ i8) ^ j8 == beta_l ^ (i8 ^ j8)) by (bit_vector);
    lemma_xor_below(i, j, k);
    let w = (i8 ^ j8) as int;
    assert(w as u8 == i8 ^ j8);
    assert(lde_column(tw_s, tw_l, n, j)[i].0 == lde_column(tw_s, tw_l, n, 0)[w].0);
}

// ---------------------------------------------------------------------------------------------
// Executable code: the portable paths of `crates/flock/src/zerocheck/ntt.rs`
// ---------------------------------------------------------------------------------------------
/// Twiddle recurrence used to build the next subspace layer's evaluation points:
/// `next_s(s, root) = s² + root · s = s · (s + root)`.
#[inline]
pub fn next_s(s: F8, s_at_root: F8) -> (r: F8)
    ensures
        r.0 == f8_mul(s.0, s.0 ^ s_at_root.0),
{
    s * (s + s_at_root)
}

#[inline]
pub fn fft_butterfly(v: &mut [F8], lambda: F8)
    ensures
        final(v)@ == fft_butterfly_spec(old(v)@, lambda.0),
{
    let ghost v0 = v@;
    let n = v.len();
    let half = n >> 1;
    proof {
        assert(n >> 1 == n / 2) by (bit_vector);
    }
    for i in 0..half
        invariant
            v.len() == n,
            v0.len() == n,
            half == n / 2,
            forall|p: int|
                0 <= p < n ==> #[trigger] v@[p] == if (0 <= p < i) || (half <= p < half + i) {
                    fft_butterfly_spec(v0, lambda.0)[p]
                } else {
                    v0[p]
                },
    {
        let w = v[half + i];
        v[i] += lambda * w;
        v[half + i] = w + v[i];
    }
    assert(v@ =~= fft_butterfly_spec(v0, lambda.0));
}

/// Whether `n` is a power of two.
pub open spec fn is_pow2_len(n: nat) -> bool {
    exists|m: nat| n == pow2(m)
}

/// A power of two other than one halves to a power of two.
proof fn lemma_pow2_half(n: nat)
    requires
        is_pow2_len(n),
        n != 1,
    ensures
        n >= 2,
        n % 2 == 0,
        is_pow2_len(n / 2),
{
    let m = choose|m: nat| n == pow2(m);
    lemma2_to64();
    assert(m > 0);
    lemma_pow2_unfold(m);
    lemma_pow2_pos((m - 1) as nat);
    assert(n / 2 == pow2((m - 1) as nat));
}

/// Rewritten: the requirement that `v` be a power-of-two length (production's only caller passes `2^k`
/// words) and that every twiddle read lie in the table are preconditions.
pub fn fft_rec(v: &mut [F8], tw: &[F8], idx: usize)
    requires
        is_pow2_len(old(v).len() as nat),
        idx >= 1,
        (idx + 1) * old(v).len() <= 2 * (tw.len() + 1),
        tw.len() < 256,
    ensures
        final(v)@ == fft_spec(old(v)@, tw@, idx as int),
    decreases old(v).len(),
{
    let ghost v0 = v@;
    let n = v.len();
    if n == 1 {
        return;
    }
    proof {
        lemma_pow2_half(n as nat);
        assert(idx + 1 <= tw.len() + 1) by (nonlinear_arith)
            requires
                (idx + 1) * n <= 2 * (tw.len() + 1),
                n >= 2,
        ;
    }
    fft_butterfly(v, tw[idx - 1]);
    let half = n >> 1;
    proof {
        assert(n >> 1 == n / 2) by (bit_vector);
        assert((2 * idx + 1) * half <= (idx + 1) * n && (2 * idx + 1 + 1) * half <= (idx + 1) * n) by (nonlinear_arith)
            requires
                n == 2 * half,
        ;
    }
    let ghost w = v@;
    let (lo, hi) = v.split_at_mut(half);
    fft_rec(lo, tw, 2 * idx);
    fft_rec(hi, tw, 2 * idx + 1);
    proof {
        assert(w.subrange(half as int, n as int).len() == half);
    }
}

#[inline]
pub fn ifft_butterfly(v: &mut [F8], lambda: F8)
    ensures
        final(v)@ == ifft_butterfly_spec(old(v)@, lambda.0),
{
    let ghost v0 = v@;
    let n = v.len();
    let half = n >> 1;
    proof {
        assert(n >> 1 == n / 2) by (bit_vector);
    }
    for i in 0..half
        invariant
            v.len() == n,
            v0.len() == n,
            half == n / 2,
            forall|p: int|
                0 <= p < n ==> #[trigger] v@[p] == if (0 <= p < i) || (half <= p < half + i) {
                    ifft_butterfly_spec(v0, lambda.0)[p]
                } else {
                    v0[p]
                },
    {
        v[half + i] += v[i];
        v[i] += lambda * v[half + i];
    }
    assert(v@ =~= ifft_butterfly_spec(v0, lambda.0));
}

/// Rewritten: the same preconditions as [`fft_rec`].
pub fn ifft_rec(v: &mut [F8], tw: &[F8], idx: usize)
    requires
        is_pow2_len(old(v).len() as nat),
        idx >= 1,
        (idx + 1) * old(v).len() <= 2 * (tw.len() + 1),
        tw.len() < 256,
    ensures
        final(v)@ == ifft_spec(old(v)@, tw@, idx as int),
    decreases old(v).len(),
{
    let ghost v0 = v@;
    let n = v.len();
    if n == 1 {
        return;
    }
    proof {
        lemma_pow2_half(n as nat);
        assert(idx + 1 <= tw.len() + 1) by (nonlinear_arith)
            requires
                (idx + 1) * n <= 2 * (tw.len() + 1),
                n >= 2,
        ;
    }
    let half = n >> 1;
    proof {
        assert(n >> 1 == n / 2) by (bit_vector);
        assert((2 * idx + 1) * half <= (idx + 1) * n && (2 * idx + 1 + 1) * half <= (idx + 1) * n) by (nonlinear_arith)
            requires
                n == 2 * half,
        ;
    }
    let (lo, hi) = v.split_at_mut(half);
    ifft_rec(lo, tw, 2 * idx);
    ifft_rec(hi, tw, 2 * idx + 1);
    ifft_butterfly(v, tw[idx - 1]);
}

/// The levels of the twiddle table occupy disjoint ranges: entry `2^d - 1 + j`, `j < 2^d`, names its level.
proof fn lemma_levels_disjoint(d: nat, j: nat, d2: nat, j2: nat)
    requires
        j < pow2(d),
        j2 < pow2(d2),
        pow2(d) + j == pow2(d2) + j2,
    ensures
        d == d2,
        j == j2,
{
    if d < d2 {
        lemma_pow2_strictly_increases(d, d2);
        lemma_pow2_unfold(d + 1);
        if d + 1 < d2 {
            lemma_pow2_strictly_increases(d + 1, d2);
        }
    } else if d2 < d {
        lemma_pow2_strictly_increases(d2, d);
        lemma_pow2_unfold(d2 + 1);
        if d2 + 1 < d {
            lemma_pow2_strictly_increases(d2 + 1, d);
        }
    }
}

/// Level `d < k` of the table lies inside its `2^k - 1` entries.
proof fn lemma_level_in_table(d: nat, j: nat, k: nat)
    requires
        d < k,
        j < pow2(d),
    ensures
        pow2(d) - 1 + j < pow2(k) - 1,
        pow2(d) >= 1,
{
    lemma_pow2_pos(d);
    lemma_pow2_unfold(d + 1);
    if d + 1 < k {
        lemma_pow2_strictly_increases(d + 1, k);
    }
}

/// Build the size-(2^k − 1) twiddle table for the additive NTT.
///
/// Layout: level-L twiddles live at offset (2^L − 1).
/// Level 0 has 2^{k-1} twiddles, level 1 has 2^{k-2}, …, level k−1 has 1.
///
/// Rewritten: `k <= 8` is a precondition (the domain lies in `GF(2^8)`); the `collect` of the first layer
/// and the `copy_from_slice` of it are index loops, and the unnamed loop variable is named.
pub fn compute_twiddles(k: usize, beta: F8) -> (twiddles: Vec<F8>)
    requires
        k <= 8,
    ensures
        twiddles_of(twiddles@, k as nat, beta.0),
{
    if k == 0 {
        proof {
            lemma2_to64();
        }
        return Vec::new();
    }
    let ghost b = beta.0;
    proof {
        lemma_pow2_le_256(k as nat);
        lemma_pow2_le_256((k - 1) as nat);
        lemma_usize_shl_is_mul(1, k);
        lemma_usize_shl_is_mul(1, (k - 1) as usize);
        lemma_pow2_unfold(k as nat);
        lemma2_to64();
    }
    let n = 1usize << k;
    let mut twiddles = vec![F8::ZERO; n - 1];

    // Layer 0: 2^{k-1} points beta + {0, 2, 4, ..., 2(write_at-1)}.
    let mut write_at = 1usize << (k - 1);
    let mut layer: Vec<F8> = Vec::new();
    for i in 0..write_at
        invariant
            b == beta.0,
            write_at == pow2((k - 1) as nat),
            write_at <= 128,
            pow2(1) == 2,
            layer.len() == i,
            forall|p: int| 0 <= p < i ==> (#[trigger] layer@[p]).0 == subspace_poly8(0, b ^ block_offset(p as nat, 1)),
    {
        proof {
            assert(block_offset(i as nat, 1) == (2 * i) as u8);
        }
        layer.push(beta + F8((2 * i) as u8));
    }
    let mut s_at_root = F8::ONE;

    // Write layer 0 directly (s_at_root = 1 ⇒ no scaling needed).
    for j in 0..write_at
        invariant
            1 <= k <= 8,
            write_at == pow2((k - 1) as nat),
            layer.len() == write_at,
            twiddles.len() + 1 == pow2(k as nat),
            forall|p: int| 0 <= p < write_at ==> (#[trigger] layer@[p]).0 == subspace_poly8(0, b ^ block_offset(p as nat, 1)),
            forall|j0: nat|
                j0 < j ==> (#[trigger] twiddles@[pow2((k - 1) as nat) - 1 + j0]).0 == normalized_poly8(
                    0,
                    b ^ block_offset(j0, 1),
                ),
    {
        proof {
            lemma_level_in_table((k - 1) as nat, j as nat, k as nat);
            lemma_normalized_poly8_zero(b ^ block_offset(j as nat, 1));
        }
        twiddles[write_at - 1 + j] = layer[j];
    }
    proof {
        assert(basis8(0) == 1) by {
            assert((1u8 << 0u8) == 1u8) by (bit_vector);
        }
        assert forall|d: nat, j: nat| (k - 1) as nat <= d < k && j < pow2(d) implies (#[trigger] twiddles@[pow2(d) - 1
            + j]).0 == normalized_poly8((k - 1 - d) as nat, b ^ block_offset(j, (k - d) as nat)) by {
            assert(d == k - 1);
        }
    }

    for step in 1..k
        invariant
            1 <= k <= 8,
            twiddles.len() + 1 == pow2(k as nat),
            write_at == pow2((k - step) as nat),
            layer.len() == pow2((k - 1) as nat),
            forall|p: int|
                0 <= p < write_at ==> (#[trigger] layer@[p]).0 == subspace_poly8(
                    (step - 1) as nat,
                    b ^ block_offset(p as nat, step as nat),
                ),
            s_at_root.0 == subspace_poly8((step - 1) as nat, basis8((step - 1) as nat)),
            forall|d: nat, j: nat|
                (k - step) as nat <= d < k && j < pow2(d) ==> (#[trigger] twiddles@[pow2(d) - 1 + j]).0 == normalized_poly8(
                    (k - 1 - d) as nat,
                    b ^ block_offset(j, (k - d) as nat),
                ),
    {
        let ghost dn = (k - 1 - step) as nat;
        proof {
            lemma_pow2_unfold((k - step) as nat);
            lemma_pow2_pos(dn);
            lemma_usize_shr_is_div(write_at, 1);
            lemma2_to64();
            if dn + 1 < k - 1 {
                lemma_pow2_strictly_increases(dn + 1, (k - 1) as nat);
            }
        }
        write_at >>= 1;
        assert(write_at == pow2(dn));
        // The root: `s_(step-1)(β + b_step) + s_(step-1)(β) = s_(step-1)(b_step)`.
        let ghost (l0, l1) = (layer@[0].0, layer@[1].0);
        proof {
            lemma_shl8(step as nat);
            let o1 = block_offset(1, step as nat);
            assert(o1 == basis8(step as nat));
            assert(block_offset(0, step as nat) == 0);
            lemma_subspace_poly8_additive((step - 1) as nat, b ^ o1, b);
            assert(b ^ 0u8 == b && (b ^ o1) ^ b == o1) by (bit_vector);
        }
        let next_s_root = next_s(layer[1] + layer[0], s_at_root);
        assert(next_s_root.0 == subspace_poly8(step as nat, basis8(step as nat)));
        let ghost prev = layer@;
        for i in 0..write_at
            invariant
                1 <= step < k <= 8,
                write_at == pow2(dn),
                dn == k - 1 - step,
                2 * write_at <= pow2((k - 1) as nat),
                prev.len() == pow2((k - 1) as nat),
                layer.len() == pow2((k - 1) as nat),
                s_at_root.0 == subspace_poly8((step - 1) as nat, basis8((step - 1) as nat)),
                forall|p: int|
                    0 <= p < 2 * write_at ==> (#[trigger] prev[p]).0 == subspace_poly8(
                        (step - 1) as nat,
                        b ^ block_offset(p as nat, step as nat),
                    ),
                forall|p: int| i <= p < layer.len() ==> #[trigger] layer@[p] == prev[p],
                forall|p: int|
                    0 <= p < i ==> (#[trigger] layer@[p]).0 == subspace_poly8(
                        step as nat,
                        b ^ block_offset(p as nat, (step + 1) as nat),
                    ),
        {
            proof {
                lemma_pow2_unfold((step + 1) as nat);
                assert(2 * i * pow2(step as nat) == i * pow2((step + 1) as nat)) by (nonlinear_arith)
                    requires
                        pow2((step + 1) as nat) == 2 * pow2(step as nat),
                ;
                assert(block_offset((2 * i) as nat, step as nat) == block_offset(i as nat, (step + 1) as nat));
            }
            layer[i] = next_s(layer[2 * i], s_at_root);
        }
        s_at_root = next_s_root;

        let s_inv = s_at_root.inv();
        let ghost done = twiddles@;
        for j in 0..write_at
            invariant
                1 <= step < k <= 8,
                write_at == pow2(dn),
                dn == k - 1 - step,
                layer.len() == pow2((k - 1) as nat),
                write_at <= layer.len(),
                done.len() + 1 == pow2(k as nat),
                twiddles.len() + 1 == pow2(k as nat),
                s_inv.0 == f8_inv(subspace_poly8(step as nat, basis8(step as nat))),
                forall|p: int|
                    0 <= p < write_at ==> (#[trigger] layer@[p]).0 == subspace_poly8(
                        step as nat,
                        b ^ block_offset(p as nat, (step + 1) as nat),
                    ),
                forall|q: int| 0 <= q < twiddles.len() && !(write_at - 1 <= q < write_at - 1 + j) ==> #[trigger] twiddles@[q] == done[q],
                forall|j0: nat|
                    j0 < j ==> (#[trigger] twiddles@[pow2(dn) - 1 + j0]).0 == normalized_poly8(
                        step as nat,
                        b ^ block_offset(j0, (step + 1) as nat),
                    ),
        {
            proof {
                lemma_level_in_table(dn, j as nat, k as nat);
            }
            twiddles[write_at - 1 + j] = s_inv * layer[j];
        }
        proof {
            assert forall|d: nat, j: nat| (k - (step + 1)) as nat <= d < k && j < pow2(d) implies (#[trigger] twiddles@[pow2(
                d,
            ) - 1 + j]).0 == normalized_poly8((k - 1 - d) as nat, b ^ block_offset(j, (k - d) as nat)) by {
                lemma_level_in_table(d, j, k as nat);
                if d != dn {
                    let q = pow2(d) - 1 + j;
                    if pow2(dn) - 1 <= q < pow2(dn) - 1 + pow2(dn) {
                        lemma_levels_disjoint(d, j, dn, (q - (pow2(dn) - 1)) as nat);
                    }
                    assert(twiddles@[q] == done[q]);
                }
            }
        }
    }
    twiddles
}

/// Additive NTT over GF(2^8) with domain of size 2^k.
///
/// Evaluation domain `W = β + span{1, 2, …, 2^{k-1}}` (additive coset of an
/// F_2 subspace of F_{2^8}). Maximum useful `k` is 7 (|W| = 128); k = 8 would
/// exhaust all 256 elements of F_{2^8}.
///
/// Internal LCH basis: the forward transform maps coefficients in the
/// Lin-Chung-Han basis to evaluations at the 2^k points of the domain.
/// `inverse` is the exact reverse.
#[derive(Clone, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct AdditiveNttGf8 {
    k: usize,
    twiddles: Vec<F8>,
}

impl AdditiveNttGf8 {
    /// The domain has `2^k_spec()` points.
    pub closed spec fn k_spec(&self) -> nat {
        self.k as nat
    }

    /// The twiddle table.
    pub closed spec fn tw(&self) -> Seq<F8> {
        self.twiddles@
    }

    /// At most `2^8` points, and a table of `2^k - 1` twiddles.
    pub open spec fn well_formed(&self) -> bool {
        self.k_spec() <= 8 && self.tw().len() + 1 == pow2(self.k_spec())
    }

    /// Build an NTT for a 2^k-point domain with offset β.
    ///
    /// Rewritten: `k <= 8` is a precondition, as for [`compute_twiddles`].
    pub fn new(k: usize, beta: F8) -> (r: Self)
        requires
            k <= 8,
        ensures
            r.k_spec() == k,
            r.well_formed(),
            twiddles_of(r.tw(), k as nat, beta.0),
    {
        Self { k, twiddles: compute_twiddles(k, beta) }
    }

    pub const fn k(&self) -> (r: usize)
        ensures
            r == self.k_spec(),
    {
        self.k
    }

    /// Rewritten: `k <= 8` (well-formedness) is a precondition, for the shift.
    pub const fn domain_size(&self) -> (r: usize)
        requires
            self.well_formed(),
        ensures
            r == pow2(self.k_spec()),
    {
        proof {
            lemma_pow2_le_256(self.k as nat);
            lemma_usize_shl_is_mul(1, self.k);
        }
        1usize << self.k
    }

    /// The forward transform: `fft_rec` from the root. With the table of `new(k, β)`, word `u` of the output
    /// is the novel-basis polynomial of the input at `β + u` ([`lemma_fft_evaluates`]).
    ///
    /// Rewritten: the `assert_eq!` on the length is a precondition.
    pub fn forward(&self, v: &mut [F8])
        requires
            self.well_formed(),
            old(v).len() == pow2(self.k_spec()),
        ensures
            final(v)@ == fft_spec(old(v)@, self.tw(), 1),
    {
        if v.len() <= 1 {
            return;
        }
        proof {
            lemma_pow2_le_256(self.k as nat);
        }
        fft_rec(v, &self.twiddles, 1);
    }

    /// The inverse transform: `ifft_rec` from the root, which undoes `forward` ([`lemma_ifft_after_fft`],
    /// [`lemma_fft_after_ifft`]) and so interpolates ([`lemma_ifft_interpolates`]).
    ///
    /// Rewritten: the `assert_eq!` on the length is a precondition.
    pub fn inverse(&self, v: &mut [F8])
        requires
            self.well_formed(),
            old(v).len() == pow2(self.k_spec()),
        ensures
            final(v)@ == ifft_spec(old(v)@, self.tw(), 1),
    {
        if v.len() <= 1 {
            return;
        }
        proof {
            lemma_pow2_le_256(self.k as nat);
        }
        ifft_rec(v, &self.twiddles, 1);
    }
}

// ---------------------------------------------------------------------------------------------
// The single-table collapse of `M = forward_Λ ∘ inverse_S` (`ntt/inv_table.rs`)
// ---------------------------------------------------------------------------------------------
/// `XOR_{j < n} f(j)`.
pub open spec fn xor_sum8(f: spec_fn(int) -> u8, n: nat) -> u8
    decreases n,
{
    if n == 0 {
        0
    } else {
        xor_sum8(f, (n - 1) as nat) ^ f(n - 1)
    }
}

/// Bit `t < 8` of the byte `w`.
pub open spec fn byte_bit(w: usize, t: int) -> bool {
    0 <= t < 8 && (w >> (t as usize)) & 1 == 1
}

/// Word `i` of row `w` of the table: `Σ_{t < 8, bit_t(w) = 1} M[i][t]`, the XOR of the columns `t < 8` of `M`
/// over the set bits of `w`.
pub open spec fn table_row(tw_s: Seq<F8>, tw_l: Seq<F8>, n: nat, w: usize, i: int) -> u8 {
    xor_sum8(|t: int| if byte_bit(w, t) { lde_column(tw_s, tw_l, n, t)[i].0 } else { 0 }, 8)
}

/// Word `i` of `M x`, `x` the bits of `bytes` (bit `t` of byte `b` is `x_(8b+t)`): `Σ_{j < 8 len} x_j M[i][j]`.
pub open spec fn lde_apply(tw_s: Seq<F8>, tw_l: Seq<F8>, n: nat, bytes: Seq<u8>, i: int) -> u8 {
    xor_sum8(
        |j: int| if byte_bit(bytes[j / 8] as usize, j % 8) { lde_column(tw_s, tw_l, n, j)[i].0 } else { 0 },
        8 * bytes.len(),
    )
}

/// What `apply_scalar` computes at word `i`: `Σ_b T[bytes[b]][i ⊕ 8b]`, `T` the table of `ell`-word rows.
pub open spec fn apply_formula(data: Seq<F8>, ell: nat, bytes: Seq<u8>, i: int) -> u8 {
    apply_partial(data, ell, bytes, i, bytes.len())
}

/// The first `nb` terms of [`apply_formula`].
pub open spec fn apply_partial(data: Seq<F8>, ell: nat, bytes: Seq<u8>, i: int, nb: nat) -> u8 {
    xor_sum8(|b: int| data[(bytes[b] as int) * ell + (((i as usize) ^ ((8 * b) as usize)) as int)].0, nb)
}

proof fn lemma_xor_sum8_ext(f: spec_fn(int) -> u8, g: spec_fn(int) -> u8, n: nat)
    requires
        forall|j: int| 0 <= j < n ==> #[trigger] f(j) == g(j),
    ensures
        xor_sum8(f, n) == xor_sum8(g, n),
    decreases n,
{
    if n > 0 {
        lemma_xor_sum8_ext(f, g, (n - 1) as nat);
    }
}

/// Changing one term of a sum by `c` changes the sum by `c`.
proof fn lemma_xor_sum8_one_term(f: spec_fn(int) -> u8, g: spec_fn(int) -> u8, n: nat, t: int, c: u8)
    requires
        0 <= t < n,
        forall|j: int| 0 <= j < n && j != t ==> #[trigger] f(j) == g(j),
        f(t) == g(t) ^ c,
    ensures
        xor_sum8(f, n) == xor_sum8(g, n) ^ c,
    decreases n,
{
    let (a, b) = (xor_sum8(f, (n - 1) as nat), xor_sum8(g, (n - 1) as nat));
    if t == n - 1 {
        lemma_xor_sum8_ext(f, g, (n - 1) as nat);
        let x = g(t);
        assert(a ^ (x ^ c) == (a ^ x) ^ c) by (bit_vector);
    } else {
        lemma_xor_sum8_one_term(f, g, (n - 1) as nat, t, c);
        let x = f(n - 1);
        assert((b ^ c) ^ x == (b ^ x) ^ c) by (bit_vector);
    }
}

/// A sum of zeros is zero.
proof fn lemma_xor_sum8_zero(f: spec_fn(int) -> u8, n: nat)
    requires
        forall|j: int| 0 <= j < n ==> #[trigger] f(j) == 0,
    ensures
        xor_sum8(f, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_xor_sum8_zero(f, (n - 1) as nat);
        assert(0u8 ^ 0u8 == 0u8) by (bit_vector);
    }
}

/// `Σ_{j < a + c} f(j) = Σ_{j < a} f(j) + Σ_{t < c} f(a + t)`.
proof fn lemma_xor_sum8_split(f: spec_fn(int) -> u8, a: nat, c: nat)
    ensures
        xor_sum8(f, a + c) == xor_sum8(f, a) ^ xor_sum8(|t: int| f(a + t), c),
    decreases c,
{
    let g = |t: int| f(a + t);
    if c == 0 {
        let x = xor_sum8(f, a);
        assert(x ^ 0u8 == x) by (bit_vector);
    } else {
        lemma_xor_sum8_split(f, a, (c - 1) as nat);
        assert(xor_sum8(f, a + c) == xor_sum8(f, (a + c - 1) as nat) ^ f(a + c - 1));
        assert(g(c - 1) == f(a + c - 1));
        let (x, y, z) = (xor_sum8(f, a), xor_sum8(g, (c - 1) as nat), f(a + c - 1));
        assert((x ^ y) ^ z == x ^ (y ^ z)) by (bit_vector);
    }
}

/// A sum over `8 n` terms, regrouped by bytes: `Σ_{j < 8n} f(j) = Σ_{b < n} Σ_{t < 8} f(8b + t)`.
proof fn lemma_xor_sum8_bytes(f: spec_fn(int) -> u8, n: nat)
    ensures
        xor_sum8(f, 8 * n) == xor_sum8(|b: int| xor_sum8(|t: int| f(8 * b + t), 8), n),
    decreases n,
{
    if n > 0 {
        let m = (n - 1) as nat;
        lemma_xor_sum8_bytes(f, m);
        lemma_xor_sum8_split(f, 8 * m, 8);
        assert(8 * m + 8 == 8 * n);
        lemma_xor_sum8_ext(|t: int| f(8 * m + t), |t: int| f(8 * (n - 1) + t), 8);
    }
}

/// Flipping a set bit `t` of `w` removes column `t` from row `w`.
proof fn lemma_table_row_flip(tw_s: Seq<F8>, tw_l: Seq<F8>, n: nat, w: usize, t: usize, i: int)
    requires
        t < 8,
        (w >> t) & 1 == 1,
    ensures
        table_row(tw_s, tw_l, n, w, i) == table_row(tw_s, tw_l, n, w ^ (1usize << t), i) ^ lde_column(
            tw_s,
            tw_l,
            n,
            t as int,
        )[i].0,
{
    let w2 = w ^ (1usize << t);
    let f = |t0: int| if byte_bit(w, t0) { lde_column(tw_s, tw_l, n, t0)[i].0 } else { 0 };
    let g = |t0: int| if byte_bit(w2, t0) { lde_column(tw_s, tw_l, n, t0)[i].0 } else { 0 };
    assert forall|j: int| 0 <= j < 8 && j != t implies #[trigger] f(j) == g(j) by {
        let ju = j as usize;
        assert(((w ^ (1usize << t)) >> ju) & 1 == (w >> ju) & 1) by (bit_vector)
            requires
                ju < 8,
                t < 8,
                ju != t,
        ;
    }
    assert(((w ^ (1usize << t)) >> t) & 1 == 0) by (bit_vector)
        requires
            t < 8,
            (w >> t) & 1 == 1,
    ;
    let c = lde_column(tw_s, tw_l, n, t as int)[i].0;
    assert(0u8 ^ c == c) by (bit_vector);
    lemma_xor_sum8_one_term(f, g, 8, t as int, c);
}

/// Row `0` is zero, and row `2^t` is column `t`.
proof fn lemma_table_row_units(tw_s: Seq<F8>, tw_l: Seq<F8>, n: nat, t: usize, i: int)
    requires
        t < 8,
    ensures
        table_row(tw_s, tw_l, n, 0, i) == 0,
        table_row(tw_s, tw_l, n, 1usize << t, i) == lde_column(tw_s, tw_l, n, t as int)[i].0,
{
    let f = |t0: int| if byte_bit(0, t0) { lde_column(tw_s, tw_l, n, t0)[i].0 } else { 0 };
    assert forall|j: int| 0 <= j < 8 implies #[trigger] f(j) == 0 by {
        let ju = j as usize;
        assert((0usize >> ju) & 1 == 0) by (bit_vector);
    }
    lemma_xor_sum8_zero(f, 8);
    let w = 1usize << t;
    assert((w >> t) & 1 == 1 && w ^ (1usize << t) == 0) by (bit_vector)
        requires
            t < 8,
            w == 1usize << t,
    ;
    lemma_table_row_flip(tw_s, tw_l, n, w, t, i);
    let c = lde_column(tw_s, tw_l, n, t as int)[i].0;
    assert(0u8 ^ c == c) by (bit_vector);
}

/// XOR of indices below `2^8`, as bytes or as words.
proof fn lemma_xor_index(i: int, j: int)
    requires
        0 <= i < 256,
        0 <= j < 256,
    ensures
        (((i as u8) ^ (j as u8)) as int) == (((i as usize) ^ (j as usize)) as int),
{
    let (x, y) = (i as usize, j as usize);
    assert(x < 256 && y < 256 ==> ((x as u8) ^ (y as u8)) as usize == x ^ y) by (bit_vector);
    assert(x as u8 == i as u8 && y as u8 == j as u8);
}

/// `apply_scalar`'s sum is `M` applied to the row's bits: with the table of two `2^k`-point NTTs (offsets `β_s`
/// and `β_l`), `Σ_b T[bytes[b]][i ⊕ 8b] = Σ_j x_j M[i][j]`. Each byte's row read at `i ⊕ 8b` is the sum of the
/// columns `8b + t` by [`lemma_lde_shift`].
pub proof fn lemma_apply_formula(
    tw_s: Seq<F8>,
    tw_l: Seq<F8>,
    k: nat,
    beta_s: u8,
    beta_l: u8,
    data: Seq<F8>,
    bytes: Seq<u8>,
    i: int,
)
    requires
        twiddles_of(tw_s, k, beta_s),
        twiddles_of(tw_l, k, beta_l),
        3 <= k <= 7,
        data.len() == 256 * pow2(k),
        forall|w: int, i0: int|
            0 <= w < 256 && 0 <= i0 < pow2(k) ==> (#[trigger] data[w * pow2(k) + i0]).0 == table_row(
                tw_s,
                tw_l,
                pow2(k),
                w as usize,
                i0,
            ),
        8 * bytes.len() == pow2(k),
        0 <= i < pow2(k),
    ensures
        apply_formula(data, pow2(k), bytes, i) == lde_apply(tw_s, tw_l, pow2(k), bytes, i),
{
    let n = pow2(k);
    let nc = bytes.len();
    lemma_pow2_le_256(k);
    lemma_usize_shl_is_mul(1, k as usize);
    let ku = k as usize;
    assert(n == (1usize << ku));
    let f = |j: int| if byte_bit(bytes[j / 8] as usize, j % 8) { lde_column(tw_s, tw_l, n, j)[i].0 } else { 0 };
    lemma_xor_sum8_bytes(f, nc);
    let lhs = |b: int| data[(bytes[b] as int) * n + (((i as usize) ^ ((8 * b) as usize)) as int)].0;
    let rhs = |b: int| xor_sum8(|t: int| f(8 * b + t), 8);
    assert forall|b: int| 0 <= b < nc implies #[trigger] lhs(b) == rhs(b) by {
        let w = bytes[b] as usize;
        let (iu, sh) = (i as usize, (8 * b) as usize);
        assert(8 * b < n);
        assert(iu < (1usize << ku) && sh < (1usize << ku) ==> (iu ^ sh) < (1usize << ku)) by (bit_vector)
            requires
                ku < 64,
        ;
        let ip = (iu ^ sh) as int;
        assert(lhs(b) == table_row(tw_s, tw_l, n, w, ip));
        let g = |t: int| if byte_bit(w, t) { lde_column(tw_s, tw_l, n, t)[ip].0 } else { 0 };
        assert forall|t: int| 0 <= t < 8 implies #[trigger] g(t) == f(8 * b + t) by {
            let j = 8 * b + t;
            assert(j / 8 == b && j % 8 == t);
            lemma_lde_shift(tw_s, tw_l, k, beta_s, beta_l, ip, t);
            lemma_lde_shift(tw_s, tw_l, k, beta_s, beta_l, i, j);
            lemma_xor_index(ip, t);
            lemma_xor_index(i, j);
            let (tu, bu, ju) = (t as usize, b as usize, j as usize);
            assert(pow2(3) == 8) by {
                lemma2_to64();
            }
            lemma_usize_shl_is_mul(bu, 3);
            assert(sh == bu << 3usize);
            assert(ju == add(bu << 3usize, tu));
            assert(((iu ^ sh) ^ tu) == (iu ^ ju)) by (bit_vector)
                requires
                    sh == bu << 3usize,
                    ju == add(bu << 3usize, tu),
                    tu < 8,
                    bu < 256,
            ;
        }
        lemma_xor_sum8_ext(g, |t: int| f(8 * b + t), 8);
    }
    lemma_xor_sum8_ext(lhs, rhs, nc);
}

/// Row `w` of `data` (rows of `n` words) is row `w` of the table.
pub open spec fn row_ok(data: Seq<F8>, tw_s: Seq<F8>, tw_l: Seq<F8>, n: nat, w: int) -> bool {
    forall|i: int| 0 <= i < n ==> (#[trigger] data[w * n + i]).0 == table_row(tw_s, tw_l, n, w as usize, i)
}

/// Rows of `n` words do not overlap.
proof fn lemma_row_disjoint(w0: int, i: int, r: int, n: nat)
    requires
        0 <= w0,
        0 <= r,
        0 <= i < n,
        w0 != r,
    ensures
        !(r * n <= w0 * n + i < r * n + n),
{
    if w0 < r {
        assert(w0 * n + i < r * n) by (nonlinear_arith)
            requires
                w0 + 1 <= r,
                i < n,
        ;
    } else {
        assert(w0 * n + i >= r * n + n) by (nonlinear_arith)
            requires
                w0 >= r + 1,
                i >= 0,
        ;
    }
}

/// Writing row `r` keeps every other row.
proof fn lemma_row_kept(before: Seq<F8>, after: Seq<F8>, tw_s: Seq<F8>, tw_l: Seq<F8>, n: nat, r: int, w0: int)
    requires
        0 <= r < 256,
        0 <= w0 < 256,
        w0 != r,
        before.len() == 256 * n,
        after.len() == 256 * n,
        row_ok(before, tw_s, tw_l, n, w0),
        forall|q: int| 0 <= q < after.len() && !(r * n <= q < r * n + n) ==> #[trigger] after[q] == before[q],
    ensures
        row_ok(after, tw_s, tw_l, n, w0),
{
    assert forall|i: int| 0 <= i < n implies (#[trigger] after[w0 * n + i]).0 == table_row(tw_s, tw_l, n, w0 as usize, i) by {
        lemma_row_disjoint(w0, i, r, n);
        assert(w0 * n + i < 256 * n) by (nonlinear_arith)
            requires
                w0 < 256,
                i < n,
        ;
        assert(0 <= w0 * n + i) by (nonlinear_arith)
            requires
                w0 >= 0,
                i >= 0,
        ;
        assert(before[w0 * n + i].0 == table_row(tw_s, tw_l, n, w0 as usize, i));
    }
}

/// A byte with one bit set is a power of two.
proof fn lemma_byte_pow2(w0: usize)
    requires
        1 <= w0 < 256,
        w0 & sub(w0, 1) == 0,
    ensures
        exists|t0: usize| t0 < 8 && w0 == 1usize << t0,
{
    broadcast use vstd::std_specs::bits::axiom_u64_trailing_zeros;
    let wl = w0 as u64;
    let z = vstd::std_specs::bits::u64_trailing_zeros(wl) as u64;
    assert(z < 64 && (wl >> z) & 1u64 == 1u64 && wl << sub(64, z) == 0);
    assert(z < 8 && w0 == 1usize << (z as usize)) by (bit_vector)
        requires
            wl == w0 as u64,
            z < 64,
            (wl >> z) & 1u64 == 1u64,
            wl << sub(64, z) == 0,
            w0 & sub(w0, 1) == 0,
            w0 < 256,
    ;
    assert((z as usize) < 8 && w0 == 1usize << (z as usize));
}

/// The lowest set bit of a nonzero byte, as `w.trailing_zeros()` finds it: below 8, set, and clearing it
/// lowers `w`.
proof fn lemma_low_bit(w: usize)
    requires
        1 <= w < 256,
    ensures
        ({
            let z = vstd::std_specs::bits::u64_trailing_zeros(w as u64) as usize;
            &&& z < 8
            &&& (w >> z) & 1 == 1
            &&& (w ^ (1usize << z)) < w
            &&& 1 <= (1usize << z) < 256
            &&& (1usize << z) & sub(1usize << z, 1) == 0
        }),
{
    broadcast use vstd::std_specs::bits::axiom_u64_trailing_zeros;
    let wl = w as u64;
    let z = vstd::std_specs::bits::u64_trailing_zeros(wl) as u64;
    assert(z < 64 && (wl >> z) & 1u64 == 1u64);
    assert(z < 8) by (bit_vector)
        requires
            (wl >> z) & 1u64 == 1u64,
            wl < 256,
            z < 64,
    ;
    let zu = z as usize;
    assert((w >> zu) & 1 == 1 && (w ^ (1usize << zu)) < w && 1 <= (1usize << zu) < 256 && (1usize << zu) & sub(1usize
        << zu, 1) == 0) by (bit_vector)
        requires
            wl == w as u64,
            zu == z as usize,
            z < 8,
            (wl >> z) & 1u64 == 1u64,
            w < 256,
    ;
}

/// The table that collapses the round-1 extension through the NTT, one row of `ell` words per byte value.
#[derive(Clone, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct InvNttTableByteSingleGf8 {
    pub k: usize,
    pub ell: usize,
    pub n_chunks: usize,
    /// `data[w * ell .. (w+1) * ell]` = T_0[w], the XOR-sum of columns of `M`
    /// indexed by the set bits of `w`.
    data: Vec<F8>,
}

impl InvNttTableByteSingleGf8 {
    /// The table, row after row.
    pub closed spec fn data_spec(&self) -> Seq<F8> {
        self.data@
    }

    /// The number of words per row.
    pub closed spec fn ell_spec(&self) -> nat {
        self.ell as nat
    }

    /// The domain has `2^k_spec()` points.
    pub closed spec fn k_spec(&self) -> nat {
        self.k as nat
    }

    /// The shape `new` builds: `ell = 2^k` words per row, `n_chunks = ell / 8` bytes per input row, 256 rows.
    pub closed spec fn well_formed(&self) -> bool {
        &&& 3 <= self.k <= 7
        &&& self.ell == pow2(self.k as nat)
        &&& self.n_chunks == self.ell / 8
        &&& self.data_spec().len() == 256 * self.ell
    }

    /// Built from the NTTs with twiddles `tw_s` (input domain) and `tw_l` (output domain): row `w` is
    /// [`table_row`].
    pub closed spec fn is_table_of(&self, tw_s: Seq<F8>, tw_l: Seq<F8>) -> bool {
        &&& self.well_formed()
        &&& forall|w: int, i: int|
            0 <= w < 256 && 0 <= i < self.ell ==> (#[trigger] self.data_spec()[w * self.ell + i]).0 == table_row(
                tw_s,
                tw_l,
                self.ell as nat,
                w as usize,
                i,
            )
    }

    /// Build the table given the two NTT instances: `ntt_S` over the input
    /// domain, `ntt_L` over the output (extension) domain. Both must have the
    /// same `k`.
    ///
    /// Rewritten: the three `assert!`s are preconditions; `tmp.iter_mut().for_each(..)`, the
    /// `cols.iter().enumerate()` loop and the `copy_from_slice` are index loops; `w.trailing_zeros()` is
    /// taken on `w as u64` (equal for every `w`; vstd specifies `trailing_zeros` for `u64`, not `usize`).
    pub fn new(ntt_s: &AdditiveNttGf8, ntt_l: &AdditiveNttGf8) -> (r: Self)
        requires
            ntt_s.well_formed(),
            ntt_l.well_formed(),
            ntt_s.k_spec() == ntt_l.k_spec(),
            3 <= ntt_s.k_spec() <= 7,
        ensures
            r.k_spec() == ntt_s.k_spec(),
            r.ell_spec() == pow2(ntt_s.k_spec()),
            r.is_table_of(ntt_s.tw(), ntt_l.tw()),
    {
        let ghost (tw_s, tw_l) = (ntt_s.tw(), ntt_l.tw());
        let k = ntt_s.k();
        proof {
            lemma_pow2_le_256(k as nat);
            lemma_usize_shl_is_mul(1, k);
            lemma2_to64();
            if k > 3 {
                lemma_pow2_strictly_increases(3, k as nat);
            }
        }
        let ell = 1usize << k;
        let n_chunks = ell / 8;
        let ghost n = ell as nat;

        let mut data = vec![F8::ZERO; 256 * ell];
        assert(forall|q: int| 0 <= q < data.len() ==> #[trigger] data@[q] == F8(0));

        // Compute the 8 unit-column images cols[t] = fwd_NTT_Λ ∘ inv_NTT_S (e_t)
        // for t ∈ 0..8. The remaining columns of M are XOR-shifted versions.
        let mut tmp = vec![F8::ZERO; ell];
        let mut cols: Vec<Vec<F8>> = Vec::with_capacity(8);
        for t in 0..8
            invariant
                ntt_s.well_formed(),
                ntt_l.well_formed(),
                tw_s == ntt_s.tw(),
                tw_l == ntt_l.tw(),
                ell == n,
                n == pow2(ntt_s.k_spec()),
                n == pow2(ntt_l.k_spec()),
                8 <= n <= 128,
                data.len() == 256 * n,
                forall|q: int| 0 <= q < data.len() ==> #[trigger] data@[q] == F8(0),
                tmp.len() == n,
                cols.len() == t,
                forall|t0: int| 0 <= t0 < t ==> (#[trigger] cols@[t0])@ == lde_column(tw_s, tw_l, n, t0),
        {
            for x in 0..ell
                invariant
                    tmp.len() == ell,
                    forall|p: int| 0 <= p < x ==> #[trigger] tmp@[p] == F8(0),
            {
                tmp[x] = F8::ZERO;
            }
            tmp[t] = F8::ONE;
            assert(tmp@ =~= unit(n, t as int));
            ntt_s.inverse(&mut tmp);
            proof {
                lemma_ifft_spec_len(unit(n, t as int), tw_s, 1);
            }
            ntt_l.forward(&mut tmp);
            proof {
                lemma_fft_spec_len(ifft_spec(unit(n, t as int), tw_s, 1), tw_l, 1);
            }
            let ghost before = cols@;
            cols.push(tmp.clone());
            proof {
                assert(cols@[t as int]@ =~= lde_column(tw_s, tw_l, n, t as int));
                assert forall|t0: int| 0 <= t0 < t + 1 implies (#[trigger] cols@[t0])@ == lde_column(tw_s, tw_l, n, t0) by {
                    if t0 < t {
                        assert(cols@[t0] == before[t0]);
                    }
                }
            }
        }
        proof {
            assert forall|t0: int| 0 <= t0 < 8 implies (#[trigger] cols@[t0])@.len() == n by {
                lemma_fft_spec_len(ifft_spec(unit(n, t0), tw_s, 1), tw_l, 1);
                lemma_ifft_spec_len(unit(n, t0), tw_s, 1);
            }
        }

        // T_0[0] already zero. T_0[2^t] = cols[t]. Then for non-power-of-two w,
        // T_0[w] = T_0[w ^ lo_bit] ⊕ T_0[lo_bit]; this builds all 256 entries
        // with one XOR per entry.
        proof {
            assert forall|i: int| 0 <= i < n implies (#[trigger] data@[0 * n + i]).0 == table_row(tw_s, tw_l, n, 0usize, i) by {
                lemma_table_row_units(tw_s, tw_l, n, 0, i);
            }
            assert(row_ok(data@, tw_s, tw_l, n, 0));
        }
        for t in 0..8
            invariant
                ell == n,
                8 <= n <= 128,
                data.len() == 256 * n,
                cols.len() == 8,
                forall|t0: int| 0 <= t0 < 8 ==> (#[trigger] cols@[t0])@ == lde_column(tw_s, tw_l, n, t0),
                forall|t0: int| 0 <= t0 < 8 ==> (#[trigger] cols@[t0])@.len() == n,
                row_ok(data@, tw_s, tw_l, n, 0),
                forall|t0: usize| t0 < t ==> #[trigger] row_ok(data@, tw_s, tw_l, n, (1usize << t0) as int),
        {
            proof {
                lemma2_to64();
                if t < 7 {
                    lemma_pow2_strictly_increases(t as nat, 7);
                }
                lemma_usize_shl_is_mul(1, t);
                assert((1usize << t) * ell <= 128 * 128) by (nonlinear_arith)
                    requires
                        (1usize << t) <= 128,
                        ell <= 128,
                ;
            }
            let ghost row = (1usize << t) as int;
            let ghost before = data@;
            let entry_start = (1usize << t) * ell;
            for i in 0..ell
                invariant
                    ell == n,
                    8 <= n <= 128,
                    t < 8,
                    1 <= row < 256,
                    entry_start == row * n,
                    data.len() == 256 * n,
                    before.len() == 256 * n,
                    cols.len() == 8,
                    cols@[t as int]@.len() == n,
                    forall|i0: int| 0 <= i0 < i ==> #[trigger] data@[entry_start + i0] == cols@[t as int]@[i0],
                    forall|q: int| 0 <= q < data.len() && !(entry_start <= q < entry_start + i) ==> #[trigger] data@[q] == before[q],
            {
                proof {
                    assert(entry_start + i < 256 * n) by (nonlinear_arith)
                        requires
                            entry_start == row * n,
                            row < 256,
                            i < n,
                    ;
                }
                data[entry_start + i] = cols[t][i];
            }
            proof {
                assert forall|i: int| 0 <= i < n implies (#[trigger] data@[row * n + i]).0 == table_row(tw_s, tw_l, n, row as usize, i) by {
                    lemma_table_row_units(tw_s, tw_l, n, t, i);
                }
                lemma_row_kept(before, data@, tw_s, tw_l, n, row, 0);
                assert forall|t0: usize| t0 < t + 1 implies #[trigger] row_ok(data@, tw_s, tw_l, n, (1usize << t0) as int) by {
                    if t0 < t {
                        let r0 = (1usize << t0) as int;
                        assert(t0 < 8 && t0 != t ==> (1usize << t0) != (1usize << t)) by (bit_vector);
                        if t0 < 7 {
                            lemma_pow2_strictly_increases(t0 as nat, 7);
                        }
                        lemma_usize_shl_is_mul(1, t0);
                        lemma_row_kept(before, data@, tw_s, tw_l, n, row, r0);
                    }
                }
            }
        }
        proof {
            assert forall|w0: usize| w0 < 256 && (w0 < 3 || (w0 >= 1 && w0 & sub(w0, 1) == 0)) implies #[trigger] row_ok(
                data@,
                tw_s,
                tw_l,
                n,
                w0 as int,
            ) by {
                if w0 != 0 {
                    assert(w0 < 3 ==> w0 & sub(w0, 1) == 0) by (bit_vector);
                    lemma_byte_pow2(w0);
                    let t0 = choose|t0: usize| t0 < 8 && w0 == 1usize << t0;
                    assert(row_ok(data@, tw_s, tw_l, n, (1usize << t0) as int));
                }
            }
        }
        for w in 3usize..256
            invariant
                ell == n,
                8 <= n <= 128,
                data.len() == 256 * n,
                forall|w0: usize|
                    w0 < 256 && (w0 < w || (w0 >= 1 && w0 & sub(w0, 1) == 0)) ==> #[trigger] row_ok(
                        data@,
                        tw_s,
                        tw_l,
                        n,
                        w0 as int,
                    ),
        {
            // Rewritten: `if (w & (w - 1)) == 0 { continue; }` (Verus's `for` has no `continue`) guards the rest.
            if (w & (w - 1)) != 0 {
                let ghost tz = vstd::std_specs::bits::u64_trailing_zeros(w as u64);
                proof {
                    lemma_low_bit(w);
                }
                let lo_bit = 1usize << (w as u64).trailing_zeros();
                let parent = w ^ lo_bit;
                proof {
                    let zu = tz as usize;
                    assert(lo_bit == 1usize << zu);
                    assert(row_ok(data@, tw_s, tw_l, n, parent as int));
                    assert(row_ok(data@, tw_s, tw_l, n, lo_bit as int));
                    assert(parent * ell <= 256 * 128 && lo_bit * ell <= 256 * 128 && w * ell <= 256 * 128) by (nonlinear_arith)
                        requires
                            parent < 256,
                            lo_bit < 256,
                            w < 256,
                            ell <= 128,
                    ;
                }
                // Borrow-checker friendly: read parent + bit_v slices, then write entry.
                let (parent_off, bit_off, entry_off) = (parent * ell, lo_bit * ell, w * ell);
                let ghost before = data@;
                for i in 0..ell
                    invariant
                        ell == n,
                        8 <= n <= 128,
                        3 <= w < 256,
                        parent < 256,
                        lo_bit < 256,
                        parent != w,
                        lo_bit != w,
                        parent_off == parent * n,
                        bit_off == lo_bit * n,
                        entry_off == w * n,
                        data.len() == 256 * n,
                        before.len() == 256 * n,
                        forall|i0: int|
                            0 <= i0 < i ==> (#[trigger] data@[entry_off + i0]).0 == before[parent_off + i0].0 ^ before[bit_off
                                + i0].0,
                        forall|q: int| 0 <= q < data.len() && !(entry_off <= q < entry_off + i) ==> #[trigger] data@[q] == before[q],
                {
                    proof {
                        assert(entry_off + i < 256 * n && parent_off + i < 256 * n && bit_off + i < 256 * n) by (nonlinear_arith)
                            requires
                                entry_off == w * n,
                                parent_off == parent * n,
                                bit_off == lo_bit * n,
                                w < 256,
                                parent < 256,
                                lo_bit < 256,
                                i < n,
                        ;
                        lemma_row_disjoint(parent as int, i as int, w as int, n);
                        lemma_row_disjoint(lo_bit as int, i as int, w as int, n);
                    }
                    let v = data[parent_off + i] + data[bit_off + i];
                    data[entry_off + i] = v;
                }
                proof {
                    let zu = tz as usize;
                    assert forall|i: int| 0 <= i < n implies (#[trigger] data@[(w as int) * n + i]).0 == table_row(
                        tw_s,
                        tw_l,
                        n,
                        w,
                        i,
                    ) by {
                        assert(before[(parent as int) * n + i].0 == table_row(tw_s, tw_l, n, parent, i));
                        assert(before[(lo_bit as int) * n + i].0 == table_row(tw_s, tw_l, n, lo_bit, i));
                        lemma_table_row_flip(tw_s, tw_l, n, w, zu, i);
                        lemma_table_row_units(tw_s, tw_l, n, zu, i);
                    }
                    assert forall|w0: usize|
                        w0 < 256 && (w0 < w + 1 || (w0 >= 1 && w0 & sub(w0, 1) == 0)) implies #[trigger] row_ok(
                        data@,
                        tw_s,
                        tw_l,
                        n,
                        w0 as int,
                    ) by {
                        if w0 != w {
                            assert(row_ok(before, tw_s, tw_l, n, w0 as int));
                            lemma_row_kept(before, data@, tw_s, tw_l, n, w as int, w0 as int);
                        }
                    }
                }
            }
        }
        proof {
            assert forall|w0: int, i: int| 0 <= w0 < 256 && 0 <= i < ell implies (#[trigger] data@[w0 * ell + i]).0
                == table_row(tw_s, tw_l, ell as nat, w0 as usize, i) by {
                assert(row_ok(data@, tw_s, tw_l, n, (w0 as usize) as int));
            }
        }
        Self { k, ell, n_chunks, data }
    }

    /// The number of input bytes per row.
    pub closed spec fn n_chunks_spec(&self) -> nat {
        self.n_chunks as nat
    }

    /// Scalar reference. Kept public so tests can use it as the cross-check
    /// oracle for the NEON variant.
    ///
    /// Rewritten: the two `assert_eq!`s are preconditions; `out.iter_mut().for_each(..)` and the
    /// `bytes.iter().enumerate()` loop are index loops.
    pub fn apply_scalar(&self, bytes: &[u8], out: &mut [F8])
        requires
            self.well_formed(),
            bytes.len() == self.n_chunks_spec(),
            old(out).len() == self.ell_spec(),
        ensures
            final(out).len() == self.ell_spec(),
            forall|i: int|
                0 <= i < self.ell_spec() ==> (#[trigger] final(out)@[i]).0 == apply_formula(
                    self.data_spec(),
                    self.ell_spec(),
                    bytes@,
                    i,
                ),
    {
        let ghost (data, ell) = (self.data_spec(), self.ell_spec());
        let ghost ku = self.k;
        proof {
            lemma_pow2_le_256(self.k as nat);
            lemma_usize_shl_is_mul(1, ku);
            lemma2_to64();
            if self.k > 3 {
                lemma_pow2_strictly_increases(3, self.k as nat);
            }
        }
        let n = out.len();
        for x in 0..n
            invariant
                out.len() == n,
                forall|p: int| 0 <= p < x ==> #[trigger] out@[p] == F8(0),
        {
            out[x] = F8::ZERO;
        }
        assert forall|i: int| 0 <= i < ell implies (#[trigger] out@[i]).0 == apply_partial(data, ell, bytes@, i, 0) by {
        }
        for b in 0..bytes.len()
            invariant
                self.well_formed(),
                data == self.data_spec(),
                ell == self.ell_spec(),
                ku == self.k,
                ell == (1usize << ku),
                8 <= ell <= 128,
                bytes.len() == ell / 8,
                out.len() == ell,
                forall|i: int| 0 <= i < ell ==> (#[trigger] out@[i]).0 == apply_partial(data, ell, bytes@, i, b as nat),
        {
            let byte_b = bytes[b];
            proof {
                assert((byte_b as usize) * self.ell + self.ell <= 256 * self.ell) by (nonlinear_arith)
                    requires
                        byte_b < 256,
                ;
            }
            let row_off = byte_b as usize * self.ell;
            let row = &self.data[row_off..row_off + self.ell];
            let shift = 8 * b;
            let ghost before = out@;
            for i in 0..self.ell
                invariant
                    ell == self.ell,
                    ku < 64,
                    ell == (1usize << ku),
                    8 <= ell <= 128,
                    shift == 8 * b,
                    shift < ell,
                    row@ == data.subrange(row_off as int, row_off + ell),
                    row_off == (byte_b as int) * ell,
                    row_off + ell <= data.len(),
                    byte_b == bytes@[b as int],
                    b < bytes.len(),
                    out.len() == ell,
                    before.len() == ell,
                    forall|i0: int| 0 <= i0 < ell ==> (#[trigger] before[i0]).0 == apply_partial(data, ell, bytes@, i0, b as nat),
                    forall|i0: int| i <= i0 < ell ==> #[trigger] out@[i0] == before[i0],
                    forall|i0: int|
                        0 <= i0 < i ==> (#[trigger] out@[i0]).0 == apply_partial(data, ell, bytes@, i0, (b + 1) as nat),
            {
                proof {
                    assert(i < (1usize << ku) && shift < (1usize << ku) ==> (i ^ shift) < (1usize << ku)) by (bit_vector)
                        requires
                            ku < 64,
                    ;
                    assert((i ^ shift) < ell);
                    assert(row.len() == ell);
                    assert(row@[(i ^ shift) as int] == data[row_off + ((i ^ shift) as int)]);
                    assert(apply_partial(data, ell, bytes@, i as int, (b + 1) as nat) == apply_partial(
                        data,
                        ell,
                        bytes@,
                        i as int,
                        b as nat,
                    ) ^ data[row_off + ((i ^ shift) as int)].0);
                }
                out[i] += row[i ^ shift];
            }
        }
    }
}

/// `apply_scalar` applies `M`: for the table of two `2^k`-point NTTs (twiddles `tw_s` of offset `β_s`, `tw_l` of
/// offset `β_l`), its output word `i` on an input row of `ell / 8` bytes is `Σ_j x_j M[i][j]`, `x` the row's
/// bits ([`lde_apply`]).
pub proof fn lemma_table_applies_lde(
    table: InvNttTableByteSingleGf8,
    tw_s: Seq<F8>,
    tw_l: Seq<F8>,
    beta_s: u8,
    beta_l: u8,
    bytes: Seq<u8>,
    i: int,
)
    requires
        table.is_table_of(tw_s, tw_l),
        twiddles_of(tw_s, table.k_spec(), beta_s),
        twiddles_of(tw_l, table.k_spec(), beta_l),
        bytes.len() == table.n_chunks_spec(),
        0 <= i < table.ell_spec(),
    ensures
        apply_formula(table.data_spec(), table.ell_spec(), bytes, i) == lde_apply(tw_s, tw_l, table.ell_spec(), bytes, i),
{
    let k = table.k_spec();
    lemma_pow2_le_256(k);
    lemma2_to64();
    if k > 3 {
        lemma_pow2_strictly_increases(3, k);
    }
    lemma_apply_formula(tw_s, tw_l, k, beta_s, beta_l, table.data_spec(), bytes, i);
}

} // verus!
