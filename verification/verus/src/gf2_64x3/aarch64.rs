//! The aarch64 kernels of `E`, `crates/primitives/src/field/gf2_64x3/aarch64.rs`, copied with the same bodies
//! except where noted at the function.
//!
//! A register holding a 128-bit coefficient is read through [`v128`], its two lanes as one polynomial. Given
//! the intrinsic specifications of `crate::intrinsics` (PMULL computes [`clmul`], ...), each kernel is proven to
//! compute the portable specification: [`mul`] is [`e_mul`], [`mul_unreduced`] stands for it ([`e_value`]),
//! the reductions are `k_mod` of each coefficient, and [`F192x1`] / [`F192x1Unreduced`] carry an element and
//! an unreduced value through sums and products.
#[cfg(verus_keep_ghost)]
use super::{
    e_add, e_from_k, e_mul, e_value, lemma_mul_base_spec, lemma_mul_unreduced_value, lemma_square_spec,
    lemma_u_from_wide, sched, u_from_wide, u_xor, wide,
};
use super::{F192Unreduced, F192};
#[cfg(verus_keep_ghost)]
use crate::clmul::clmul;
#[cfg(verus_keep_ghost)]
use crate::gf2_64::{k_mod, k_mul, lemma_clmul_fold_reduction, lemma_k_mod_xor};
use crate::gf2_64::{F64, R64};
#[cfg(verus_keep_ghost)]
use crate::intrinsics::aarch64::*;
#[cfg(verus_keep_ghost)]
use crate::intrinsics::aarch64_gfneon::*;
use crate::neon::xor3_u64;
use core::arch::aarch64::*;
use core::mem::transmute;
use core::mem::MaybeUninit;
use core::ops::{Add, BitXor, BitXorAssign, Mul};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::maybe_uninit::MaybeUninitAdditionalSpecFns;

verus! {

// ---------------------------------------------------------------------------------------------
// Registers as 128-bit polynomials
// ---------------------------------------------------------------------------------------------
/// The two lanes of a register as one 128-bit polynomial, lane 0 the low word.
pub open spec fn v128(v: uint64x2_t) -> u128 {
    wide(u64x2(v))
}

/// The unreduced value whose three coefficients are the registers `d`.
pub open spec fn x1_unreduced(d: [uint64x2_t; 3]) -> F192Unreduced {
    F192Unreduced { coeffs: [u64x2(d[0]), u64x2(d[1]), u64x2(d[2])] }
}

/// The three y-folded schoolbook coefficients of `a * b`, as the portable `software::mul_unreduced` builds them.
pub open spec fn folded(a: F192, b: F192) -> (u128, u128, u128) {
    let e = sched(seq![a.c0, a.c1, a.c2], seq![b.c0, b.c1, b.c2], 9);
    (e[0] ^ e[3], e[1] ^ e[3] ^ e[4], e[2] ^ e[4])
}

/// The words of a 128-bit polynomial, and the polynomial of two words.
proof fn lemma_wide_words(x: u128, w: [u64; 2])
    ensures
        wide(w) as u64 == w[0],
        (wide(w) >> 64u128) as u64 == w[1],
        wide([x as u64, (x >> 64u128) as u64]) == x,
{
    let (w0, w1) = (w[0], w[1]);
    assert((((w1 as u128) << 64u128) | (w0 as u128)) as u64 == w0 && ((((w1 as u128) << 64u128) | (w0 as u128))
        >> 64u128) as u64 == w1) by (bit_vector);
    assert((((((x >> 64u128) as u64) as u128) << 64u128) | ((x as u64) as u128)) == x) by (bit_vector);
}

/// A lane-wise XOR is the XOR of the polynomials.
proof fn lemma_wide_xor(a: [u64; 2], b: [u64; 2], r: [u64; 2])
    requires
        r[0] == a[0] ^ b[0],
        r[1] == a[1] ^ b[1],
    ensures
        wide(r) == wide(a) ^ wide(b),
{
    let (a0, a1, b0, b1) = (a[0], a[1], b[0], b[1]);
    assert((((a1 ^ b1) as u128) << 64u128) | ((a0 ^ b0) as u128) == ((((a1 as u128) << 64u128) | (a0 as u128)) ^ (
    ((b1 as u128) << 64u128) | (b0 as u128)))) by (bit_vector);
}

/// The y-folded coefficients reduce to the product.
proof fn lemma_folded_value(a: F192, b: F192)
    ensures
        ({
            let (d0, d1, d2) = folded(a, b);
            F192 { c0: k_mod(d0), c1: k_mod(d1), c2: k_mod(d2) } == e_mul(a, b)
        }),
{
    let (d0, d1, d2) = folded(a, b);
    lemma_mul_unreduced_value(a, b);
    lemma_u_from_wide(d0, d1, d2);
}

/// The nine products, folded as [`products`] does, are [`folded`].
proof fn lemma_products_fold(a: F192, b: F192)
    ensures
        ({
            let c = |x: u64, y: u64| clmul(x, y as u128);
            let y3 = c(a.c1, b.c2) ^ c(a.c2, b.c1);
            let (d0, d1, d2) = folded(a, b);
            &&& c(a.c0, b.c0) ^ y3 == d0
            &&& c(a.c0, b.c1) ^ c(a.c1, b.c0) ^ (y3 ^ c(a.c2, b.c2)) == d1
            &&& c(a.c0, b.c2) ^ c(a.c1, b.c1) ^ (c(a.c2, b.c0) ^ c(a.c2, b.c2)) == d2
        }),
{
    let (sa, sb) = (seq![a.c0, a.c1, a.c2], seq![b.c0, b.c1, b.c2]);
    super::lemma_sched_9(sa, sb);
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
    assert(c00 ^ (c12 ^ c21) == (0 ^ c00) ^ (0 ^ c12 ^ c21)) by (bit_vector);
    assert(c01 ^ c10 ^ ((c12 ^ c21) ^ c22) == (0 ^ c01 ^ c10) ^ (0 ^ c12 ^ c21) ^ (0 ^ c22)) by (bit_vector);
    assert(c02 ^ c11 ^ (c20 ^ c22) == (0 ^ c02 ^ c11 ^ c20) ^ (0 ^ c22)) by (bit_vector);
}

// ---------------------------------------------------------------------------------------------
// The kernels
// ---------------------------------------------------------------------------------------------
/// Carry-less product of the low qwords.
#[inline(always)]
fn lo(a: uint64x2_t, b: uint64x2_t) -> (r: uint64x2_t)
    ensures
        v128(r) == clmul(u64x2(a)[0], u64x2(b)[0] as u128),
{
    proof {
        broadcast use axiom_u128_as_u64x2;
        lemma_wide_words(clmul(u64x2(a)[0], u64x2(b)[0] as u128), u64x2(a));
    }
    // SAFETY: the module's cfg enables aes, and both sides of the reinterpret are 128 bits.
    unsafe { transmute::<u128, uint64x2_t>(vmull_p64(vgetq_lane_u64::<0>(a), vgetq_lane_u64::<0>(b))) }
}

/// Carry-less product of the high qwords.
#[inline(always)]
fn hi(a: uint64x2_t, b: uint64x2_t) -> (r: uint64x2_t)
    ensures
        v128(r) == clmul(u64x2(a)[1], u64x2(b)[1] as u128),
{
    proof {
        broadcast use axiom_u128_as_u64x2;
        lemma_wide_words(clmul(u64x2(a)[1], u64x2(b)[1] as u128), u64x2(a));
    }
    // SAFETY: the module's cfg enables aes, and both sides of the reinterpret are 128 bits.
    unsafe { transmute::<u128, uint64x2_t>(vmull_high_p64(vreinterpretq_p64_u64(a), vreinterpretq_p64_u64(b))) }
}

/// Two-way XOR.
#[inline(always)]
fn xor(a: uint64x2_t, b: uint64x2_t) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == u64x2(a)[0] ^ u64x2(b)[0],
        u64x2(r)[1] == u64x2(a)[1] ^ u64x2(b)[1],
        v128(r) == v128(a) ^ v128(b),
{
    // SAFETY: NEON is part of the aarch64 baseline.
    let r = unsafe { veorq_u64(a, b) };
    proof {
        lemma_wide_xor(u64x2(a), u64x2(b), u64x2(r));
    }
    r
}

/// Three-way XOR.
///
/// Rewritten for Verus: the result is bound to a name, for the proof.
#[inline(always)]
fn xor3(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> (r: uint64x2_t)
    ensures
        v128(r) == v128(a) ^ v128(b) ^ v128(c),
{
    // SAFETY: the helper issues `EOR3` only where the cfg enables it.
    let r = unsafe { xor3_u64(a, b, c) };
    proof {
        let (a0, a1, b0, b1) = (u64x2(a)[0], u64x2(a)[1], u64x2(b)[0], u64x2(b)[1]);
        let ab = [a0 ^ b0, a1 ^ b1];
        lemma_wide_xor(u64x2(a), u64x2(b), ab);
        lemma_wide_xor(ab, u64x2(c), u64x2(r));
    }
    r
}

/// An element as its two registers.
#[inline(always)]
fn split(e: F192) -> (r: (uint64x2_t, uint64x2_t))
    ensures
        u64x2(r.0)[0] == e.c0,
        u64x2(r.0)[1] == e.c1,
        u64x2(r.1)[0] == e.c2,
        u64x2(r.1)[1] == e.c2,
{
    // SAFETY: NEON is part of the aarch64 baseline.
    unsafe { (vcombine_u64(vcreate_u64(e.c0), vcreate_u64(e.c1)), vdupq_n_u64(e.c2)) }
}

/// The element whose coefficients are the low qwords of `c0`, `c1`, `c2`.
#[inline(always)]
fn join(c0: uint64x2_t, c1: uint64x2_t, c2: uint64x2_t) -> (r: F192)
    ensures
        r == (F192 { c0: u64x2(c0)[0], c1: u64x2(c1)[0], c2: u64x2(c2)[0] }),
{
    // SAFETY: NEON is part of the aarch64 baseline.
    unsafe {
        // One zip puts c0 and c1 side by side, so a store of the element is two stores.
        let c01 = vzip1q_u64(c0, c1);
        F192::new(
            vgetq_lane_u64::<0>(c01),
            vgetq_lane_u64::<1>(c01),
            vgetq_lane_u64::<0>(c2),
        )
    }
}

/// Reduce one 128-bit coefficient into its low qword.
///
/// Write the coefficient as `lo + hi * x^64`, with `x^64 = 0x1B`:
///
/// ```text
///     hi * 0x1B     = [a, s]      s has at most 4 bits
///     s  * 0x1B     = [b, 0]      at most 8 bits, so the fold ends here
///     result        = lo ^ a ^ b
/// ```
///
/// Two high-lane products and one three-way XOR.
#[inline(always)]
fn reduce_lane(d: uint64x2_t, r: uint64x2_t) -> (res: uint64x2_t)
    requires
        u64x2(r)[1] == R64,
    ensures
        u64x2(res)[0] == k_mod(v128(d)),
{
    let t = hi(d, r);
    proof {
        lemma_wide_words(0, u64x2(d));
        lemma_wide_words(0, u64x2(t));
        lemma_clmul_fold_reduction(v128(d));
    }
    let res = xor3(d, t, hi(t, r));
    proof {
        lemma_wide_words(0, u64x2(res));
    }
    res
}

/// Reduce the three coefficients of an unreduced element.
///
/// Rewritten for Verus: production destructures the array in the parameter (`[d0, d1, d2]: [uint64x2_t; 3]`);
/// the copy indexes it.
#[inline(always)]
fn reduce3(d: [uint64x2_t; 3]) -> (r: F192)
    ensures
        r == (F192 { c0: k_mod(v128(d[0])), c1: k_mod(v128(d[1])), c2: k_mod(v128(d[2])) }),
        r == e_value(x1_unreduced(d)),
{
    let (d0, d1, d2) = (d[0], d[1], d[2]);
    // SAFETY: NEON is part of the aarch64 baseline.
    let r = unsafe { vdupq_n_u64(R64) };
    join(reduce_lane(d0, r), reduce_lane(d1, r), reduce_lane(d2, r))
}

/// The y-folded schoolbook product: nine base products, each read straight from the operand registers.
///
/// Karatsuba saves three products but needs shuffles to build its operand sums.
/// Here a product costs an XOR, so the nine products are cheaper.
///
/// The one shuffle swaps the halves of the first operand.
/// A loop with a shared first factor hoists it.
///
/// ```text
///     y^0:  a0 b0 + a1 b2 + a2 b1                         (y^3 = y + 1)
///     y^1:  a0 b1 + a1 b0 + a1 b2 + a2 b1 + a2 b2         (y^4 = y^2 + y)
///     y^2:  a0 b2 + a1 b1 + a2 b0 + a2 b2
/// ```
#[inline(always)]
fn schoolbook(a: F192, b: F192) -> (r: [uint64x2_t; 3])
    ensures
        v128(r[0]) == folded(a, b).0,
        v128(r[1]) == folded(a, b).1,
        v128(r[2]) == folded(a, b).2,
{
    let ((a01, a22), (b01, b22)) = (split(a), split(b));
    products(a01, a22, b01, b22)
}

/// The element a pair of registers holds: `c0, c1` in the first, `c2` in the low lane of the second.
pub open spec fn regs_value(c01: uint64x2_t, c22: uint64x2_t) -> F192 {
    F192 { c0: u64x2(c01)[0], c1: u64x2(c01)[1], c2: u64x2(c22)[0] }
}

/// [`schoolbook`] of two elements already in their registers.
#[inline(always)]
fn products(a01: uint64x2_t, a22: uint64x2_t, b01: uint64x2_t, b22: uint64x2_t) -> (r: [uint64x2_t; 3])
    requires
        u64x2(a22)[1] == u64x2(a22)[0],
        u64x2(b22)[1] == u64x2(b22)[0],
    ensures
        v128(r[0]) == folded(regs_value(a01, a22), regs_value(b01, b22)).0,
        v128(r[1]) == folded(regs_value(a01, a22), regs_value(b01, b22)).1,
        v128(r[2]) == folded(regs_value(a01, a22), regs_value(b01, b22)).2,
{
    // SAFETY: NEON is part of the aarch64 baseline.
    let a10 = unsafe { vextq_u64::<1>(a01, a01) };
    // a_i b_j for every pair, named by (i, j).
    let (m00, m11) = (lo(a01, b01), hi(a01, b01));
    let (m10, m01) = (lo(a10, b01), hi(a10, b01));
    let (m02, m12) = (lo(a01, b22), hi(a01, b22));
    let (m20, m21) = (lo(a22, b01), hi(a22, b01));
    let m22 = lo(a22, b22);
    proof {
        assert(u64x2(a10)[0] == u64x2(a01)[1] && u64x2(a10)[1] == u64x2(a01)[0]);
        lemma_products_fold(regs_value(a01, a22), regs_value(b01, b22));
    }
    // Both y^3 terms land on y^0 and y^1.
    let y3 = xor(m12, m21);
    [
        xor(m00, y3),
        xor3(m01, m10, xor(y3, m22)),
        xor3(m02, m11, xor(m20, m22)),
    ]
}

/// The product, reduced.
#[inline(always)]
pub fn mul(a: F192, b: F192) -> (r: F192)
    ensures
        r == e_mul(a, b),
{
    proof {
        lemma_folded_value(a, b);
    }
    reduce3(schoolbook(a, b))
}

/// Three 128-bit coefficients as an unreduced element.
///
/// Rewritten for Verus: production maps the transmute over the array (`d.map(..)`), which Verus does not
/// support; the copy applies it to each coefficient.
#[inline(always)]
fn unreduced(d: [uint64x2_t; 3]) -> (r: F192Unreduced)
    ensures
        r == x1_unreduced(d),
{
    F192Unreduced {
        coeffs: [
            // SAFETY: `uint64x2_t` and `[u64; 2]` are both 16 plain bytes, valid for every bit pattern.
            unsafe { transmute::<uint64x2_t, [u64; 2]>(d[0]) },
            unsafe { transmute::<uint64x2_t, [u64; 2]>(d[1]) },
            unsafe { transmute::<uint64x2_t, [u64; 2]>(d[2]) },
        ],
    }
}

/// The product without the base-field reduction.
#[inline(always)]
pub fn mul_unreduced(a: F192, b: F192) -> (r: F192Unreduced)
    ensures
        e_value(r) == e_mul(a, b),
{
    proof {
        lemma_folded_value(a, b);
    }
    unreduced(schoolbook(a, b))
}

/// The mixed product by a base-field scalar, without the reduction: three base products.
#[inline(always)]
fn mul_base_lanes(a: F192, k: F64) -> (r: [uint64x2_t; 3])
    ensures
        v128(r[0]) == clmul(a.c0, k.0 as u128),
        v128(r[1]) == clmul(a.c1, k.0 as u128),
        v128(r[2]) == clmul(a.c2, k.0 as u128),
{
    let (a01, a22) = split(a);
    // SAFETY: NEON is part of the aarch64 baseline.
    let kk = unsafe { vdupq_n_u64(k.0) };
    [lo(a01, kk), hi(a01, kk), lo(a22, kk)]
}

/// The mixed product by a base-field scalar, reduced.
#[inline(always)]
pub fn mul_base(a: F192, k: F64) -> (r: F192)
    ensures
        r == e_mul(a, e_from_k(k.0)),
{
    proof {
        lemma_mul_base_spec(a, k.0);
    }
    reduce3(mul_base_lanes(a, k))
}

/// The mixed product by a base-field scalar, without the reduction.
#[inline(always)]
pub fn mul_base_unreduced(a: F192, k: F64) -> (r: F192Unreduced)
    ensures
        e_value(r) == e_mul(a, e_from_k(k.0)),
{
    proof {
        lemma_mul_base_spec(a, k.0);
    }
    unreduced(mul_base_lanes(a, k))
}

/// The square: three base squares, then the y-fold `y^4 = y^2 + y`.
#[inline(always)]
pub fn square(a: F192) -> (r: F192)
    ensures
        r == e_mul(a, a),
{
    let (a01, a22) = split(a);
    let (s0, s1, s2) = (lo(a01, a01), hi(a01, a01), lo(a22, a22));
    proof {
        lemma_square_spec(a);
        lemma_k_mod_xor(v128(s1), v128(s2));
    }
    reduce3([s0, s2, xor(s1, s2)])
}

/// Reduce an unreduced element.
///
/// Rewritten for Verus: production maps the transmute over the array (`u.coeffs.map(..)`); the copy applies
/// it to each coefficient.
#[inline(always)]
pub fn reduce(u: F192Unreduced) -> (r: F192)
    ensures
        r == e_value(u),
{
    proof {
        broadcast use axiom_words_as_u64x2;
    }
    // SAFETY: a `[u64; 2]` and a 128-bit register hold the same bits.
    reduce3(
        [
            unsafe { transmute::<[u64; 2], uint64x2_t>(u.coeffs[0]) },
            unsafe { transmute::<[u64; 2], uint64x2_t>(u.coeffs[1]) },
            unsafe { transmute::<[u64; 2], uint64x2_t>(u.coeffs[2]) },
        ],
    )
}

// ---------------------------------------------------------------------------------------------
// Memory helpers (trusted, tested in `tests/equivalence/intrinsics_aarch64_gfneon.rs`)
// ---------------------------------------------------------------------------------------------
/// The loads of [`F192x1::load`], production's expression: `c0, c1` into one register, `c2` into both lanes of
/// the other.
#[verifier::external_body]
#[inline(always)]
pub fn load_f192(e: &F192) -> (r: (uint64x2_t, uint64x2_t))
    ensures
        u64x2(r.0)[0] == e.c0,
        u64x2(r.0)[1] == e.c1,
        u64x2(r.1)[0] == e.c2,
        u64x2(r.1)[1] == e.c2,
{
    let words = (e as *const F192).cast::<u64>();
    // SAFETY: `e` is three words, `c0` and `c1` adjacent under `repr(C)`.
    unsafe { (vld1q_u64(words), vld1q_dup_u64(words.add(2))) }
}

/// The stores of [`F192x1::store`], production's statements: `c0, c1` from the first register, `c2` from the
/// low lane of the second. All three words are written, so `out` is initialized afterwards.
#[verifier::external_body]
#[inline(always)]
pub fn store_f192(out: &mut MaybeUninit<F192>, c01: uint64x2_t, c22: uint64x2_t)
    ensures
        final(out).as_option() == Some(regs_value(c01, c22)),
{
    let words = out.as_mut_ptr().cast::<u64>();
    // SAFETY: `out` is three words, `c0` and `c1` adjacent under `repr(C)`.
    unsafe {
        vst1q_u64(words, c01);
        vst1q_lane_u64::<0>(words.add(2), c22);
    }
}

// ---------------------------------------------------------------------------------------------
// Register-resident elements
// ---------------------------------------------------------------------------------------------
/// One element in its two registers, for a kernel whose values stay there from load to store.
///
/// An [`F192`] is three integer words: every sum of two runs on the integer side, and every
/// product moves its operands over and its result back, which costs more than the product.
/// These sums and products stay in vector registers. Keep them as named values or tuples: an
/// array of them is a memory object.
///
/// Its type invariant (a Verus addition, no runtime cost): both lanes of `c22` hold `c2`, which the high-lane
/// products of [`products`] read.
#[derive(Clone, Copy)]
pub struct F192x1 {
    c01: uint64x2_t,
    c22: uint64x2_t,
}

/// An unreduced product of [`F192x1`] values, or a sum of them: its three 128-bit coefficients
/// in registers.
#[derive(Clone, Copy)]
pub struct F192x1Unreduced([uint64x2_t; 3]);

impl F192x1 {
    /// The element the registers hold.
    pub closed spec fn value(self) -> F192 {
        regs_value(self.c01, self.c22)
    }

    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        u64x2(self.c22)[1] == u64x2(self.c22)[0]
    }

    #[inline(always)]
    pub fn new(e: F192) -> (r: Self)
        ensures
            r.value() == e,
    {
        let (c01, c22) = split(e);
        Self { c01, c22 }
    }

    /// The element at `e`, loaded into its registers.
    ///
    /// Rewritten for Verus: the two loads through the cast pointer are in [`load_f192`], whose body is
    /// production's expression.
    #[inline(always)]
    pub fn load(e: &F192) -> (r: Self)
        ensures
            r.value() == *e,
    {
        let (c01, c22) = load_f192(e);
        Self { c01, c22 }
    }

    /// Write the element to `out`, which need not be initialized.
    ///
    /// Rewritten for Verus: the two stores through the cast pointer are in [`store_f192`], whose body is
    /// production's statements.
    #[inline(always)]
    pub fn store(self, out: &mut MaybeUninit<F192>)
        ensures
            final(out).as_option() == Some(self.value()),
    {
        store_f192(out, self.c01, self.c22)
    }

    /// The product without the reduction.
    #[inline(always)]
    pub fn mul_unreduced(self, rhs: Self) -> (r: F192x1Unreduced)
        ensures
            e_value(r.value()) == e_mul(self.value(), rhs.value()),
    {
        proof {
            use_type_invariant(&self);
            use_type_invariant(&rhs);
            lemma_folded_value(self.value(), rhs.value());
        }
        F192x1Unreduced(products(self.c01, self.c22, rhs.c01, rhs.c22))
    }

    /// The mixed product by a base-field scalar, without the reduction.
    #[inline(always)]
    pub fn mul_base_unreduced(self, k: F64) -> (r: F192x1Unreduced)
        ensures
            e_value(r.value()) == e_mul(self.value(), e_from_k(k.0)),
    {
        proof {
            lemma_mul_base_spec(self.value(), k.0);
        }
        // SAFETY: NEON is part of the aarch64 baseline.
        let kk = unsafe { vdupq_n_u64(k.0) };
        F192x1Unreduced([lo(self.c01, kk), hi(self.c01, kk), lo(self.c22, kk)])
    }
}

// The operator traits' specifications: the results are stated by each impl's `ensures`, through the closed
// `value` views, so the generic `*_spec` functions are left unused.
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl for F192x1 {
    open spec fn obeys_add_spec() -> bool {
        false
    }

    open spec fn add_req(self, rhs: F192x1) -> bool {
        true
    }

    open spec fn add_spec(self, rhs: F192x1) -> F192x1 {
        arbitrary()
    }
}

impl Add for F192x1 {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: Self) -> (r: Self)
        ensures
            r.value() == e_add(self.value(), rhs.value()),
    {
        proof {
            use_type_invariant(&self);
            use_type_invariant(&rhs);
        }
        Self { c01: xor(self.c01, rhs.c01), c22: xor(self.c22, rhs.c22) }
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl for F192x1 {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: F192x1) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: F192x1) -> F192x1 {
        arbitrary()
    }
}

impl Mul for F192x1 {
    type Output = Self;

    #[inline(always)]
    fn mul(self, rhs: Self) -> (r: Self)
        ensures
            r.value() == e_mul(self.value(), rhs.value()),
    {
        self.mul_unreduced(rhs).reduce()
    }
}

impl F192x1Unreduced {
    /// The unreduced value the registers hold.
    pub closed spec fn value(self) -> F192Unreduced {
        x1_unreduced(self.0)
    }

    /// Rewritten for Verus: production fills the array with a repeat expression (`[vdupq_n_u64(0); 3]`); the
    /// copy lists the three registers.
    #[inline(always)]
    pub fn zero() -> (r: Self)
        ensures
            r.value() == F192Unreduced::ZERO,
    {
        // SAFETY: NEON is part of the aarch64 baseline.
        let z = unsafe { vdupq_n_u64(0) };
        proof {
            assert(u64x2(z) =~= [0u64, 0u64]);
        }
        let r = Self([z, z, z]);
        proof {
            assert(r.value().coeffs =~= F192Unreduced::ZERO.coeffs);
        }
        r
    }

    /// Reduce each coefficient, into the element's two registers.
    ///
    /// Rewritten for Verus: production destructures the array (`let [d0, d1, d2] = self.0`); the copy indexes it.
    #[inline(always)]
    pub fn reduce(self) -> (r: F192x1)
        ensures
            r.value() == e_value(self.value()),
    {
        let (d0, d1, d2) = (self.0[0], self.0[1], self.0[2]);
        // SAFETY: NEON is part of the aarch64 baseline.
        unsafe {
            let r = vdupq_n_u64(R64);
            let (c0, c1, c2) = (reduce_lane(d0, r), reduce_lane(d1, r), reduce_lane(d2, r));
            F192x1 {
                c01: vzip1q_u64(c0, c1),
                c22: vdupq_laneq_u64::<0>(c2),
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::BitXorSpecImpl for F192x1Unreduced {
    open spec fn obeys_bitxor_spec() -> bool {
        false
    }

    open spec fn bitxor_req(self, rhs: F192x1Unreduced) -> bool {
        true
    }

    open spec fn bitxor_spec(self, rhs: F192x1Unreduced) -> F192x1Unreduced {
        arbitrary()
    }
}

impl BitXor for F192x1Unreduced {
    type Output = Self;

    /// Rewritten for Verus: production destructures both arrays (`let ([a0, a1, a2], [b0, b1, b2]) = ..`); the
    /// copy indexes them.
    #[inline(always)]
    fn bitxor(self, rhs: Self) -> (r: Self)
        ensures
            r.value() == u_xor(self.value(), rhs.value()),
    {
        let (a0, a1, a2, b0, b1, b2) = (self.0[0], self.0[1], self.0[2], rhs.0[0], rhs.0[1], rhs.0[2]);
        let r = Self([xor(a0, b0), xor(a1, b1), xor(a2, b2)]);
        proof {
            let u = u_xor(self.value(), rhs.value());
            assert(u64x2(r.0[0]) =~= u.coeffs[0]);
            assert(u64x2(r.0[1]) =~= u.coeffs[1]);
            assert(u64x2(r.0[2]) =~= u.coeffs[2]);
            assert(r.value().coeffs =~= u.coeffs);
        }
        r
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::BitXorAssignSpecImpl for F192x1Unreduced {
    open spec fn obeys_bitxor_assign_spec() -> bool {
        false
    }

    open spec fn bitxor_assign_req(&self, rhs: F192x1Unreduced) -> bool {
        true
    }

    open spec fn bitxor_assign_spec(&self, rhs: F192x1Unreduced) -> &F192x1Unreduced {
        arbitrary()
    }
}

impl BitXorAssign for F192x1Unreduced {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self)
        ensures
            final(self).value() == u_xor(old(self).value(), rhs.value()),
    {
        *self = *self ^ rhs;
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<F192x1Unreduced> for F192Unreduced {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(u: F192x1Unreduced) -> F192Unreduced {
        u.value()
    }
}

impl From<F192x1Unreduced> for F192Unreduced {
    #[inline(always)]
    fn from(u: F192x1Unreduced) -> (r: F192Unreduced)
        ensures
            r == u.value(),
    {
        unreduced(u.0)
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<F192x1> for F192 {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(e: F192x1) -> F192 {
        e.value()
    }
}

impl From<F192x1> for F192 {
    #[inline(always)]
    fn from(e: F192x1) -> (r: F192)
        ensures
            r == e.value(),
    {
        // SAFETY: NEON is part of the aarch64 baseline.
        unsafe {
            Self::new(
                vgetq_lane_u64::<0>(e.c01),
                vgetq_lane_u64::<1>(e.c01),
                vgetq_lane_u64::<0>(e.c22),
            )
        }
    }
}

} // verus!
