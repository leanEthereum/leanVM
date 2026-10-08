//! Specifications of the AArch64 intrinsics (NEON, PMULL, SHA3's EOR3).
//!
//! A register is viewed as the array of its lanes, lane 0 first ([`u64x2`], [`p64x2`]). Each intrinsic's
//! result is given lane by lane; where the semantics is more than a lane-wise XOR or a move, an executable
//! twin `model_<intrinsic>` computes the same lanes for the differential tests.
#[cfg(verus_keep_ghost)]
use super::transmuted;
#[cfg(verus_keep_ghost)]
use crate::clmul::clmul;
use core::arch::aarch64::*;
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUint64x2(uint64x2_t);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPoly64x2(poly64x2_t);

// ---------------------------------------------------------------------------------------------
// Views and layout
// ---------------------------------------------------------------------------------------------
/// The two lanes of a `uint64x2_t`, lane 0 first.
pub open spec fn u64x2(v: uint64x2_t) -> [u64; 2] {
    transmuted::<uint64x2_t, [u64; 2]>(v)
}

/// The two lanes of a `poly64x2_t`, lane 0 first.
pub open spec fn p64x2(v: poly64x2_t) -> [u64; 2] {
    transmuted::<poly64x2_t, [u64; 2]>(v)
}

/// Layout: a `u128` read as a `uint64x2_t` is its low word in lane 0 and its high word in lane 1.
pub broadcast axiom fn axiom_u128_as_u64x2(x: u128)
    ensures
        #[trigger] u64x2(transmuted::<u128, uint64x2_t>(x)) == [x as u64, (x >> 64u128) as u64],
;

/// Layout: a `uint64x2_t` read as a `u128` is its two lanes, little-endian.
pub broadcast axiom fn axiom_u64x2_as_u128(v: uint64x2_t)
    ensures
        #[trigger] transmuted::<uint64x2_t, u128>(v) == (u64x2(v)[0] as u128) | ((u64x2(v)[1] as u128) << 64u128),
;

/// Layout: a `uint64x2_t` read as a `poly64x2_t` has the same lanes.
pub broadcast axiom fn axiom_u64x2_as_p64x2(v: uint64x2_t)
    ensures
        #[trigger] p64x2(transmuted::<uint64x2_t, poly64x2_t>(v)) == u64x2(v),
;

// ---------------------------------------------------------------------------------------------
// The specifications
// ---------------------------------------------------------------------------------------------
/// PMULL: the carry-less product of two 64-bit polynomials.
pub assume_specification[ vmull_p64 ](a: u64, b: u64) -> (r: u128)
    ensures
        r == clmul(a, b as u128),
;

/// PMULL2: the carry-less product of the high lanes.
pub assume_specification[ vmull_high_p64 ](a: poly64x2_t, b: poly64x2_t) -> (r: u128)
    ensures
        r == clmul(p64x2(a)[1], p64x2(b)[1] as u128),
;

pub assume_specification[ vdupq_n_u64 ](value: u64) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == value,
        u64x2(r)[1] == value,
;

pub assume_specification[ veorq_u64 ](a: uint64x2_t, b: uint64x2_t) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == u64x2(a)[0] ^ u64x2(b)[0],
        u64x2(r)[1] == u64x2(a)[1] ^ u64x2(b)[1],
;

/// EOR3: the three-way XOR.
pub assume_specification[ veor3q_u64 ](a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == u64x2(a)[0] ^ u64x2(b)[0] ^ u64x2(c)[0],
        u64x2(r)[1] == u64x2(a)[1] ^ u64x2(b)[1] ^ u64x2(c)[1],
;

/// ZIP1: the low lanes of `a` and `b`.
pub assume_specification[ vzip1q_u64 ](a: uint64x2_t, b: uint64x2_t) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == u64x2(a)[0],
        u64x2(r)[1] == u64x2(b)[0],
;

pub assume_specification<const IMM5: i32>[ vgetq_lane_u64::<IMM5> ](v: uint64x2_t) -> (r: u64)
    ensures
        0 <= IMM5 < 2 ==> r == u64x2(v)[IMM5 as int],
;

} // verus!
