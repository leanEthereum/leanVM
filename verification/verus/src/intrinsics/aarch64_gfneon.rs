//! Specifications of the AArch64 intrinsics the `E = GF(2^192)` NEON kernels (`gf2_64x3/aarch64.rs`) and the
//! `GF(2^8)` NEON helpers (`gf2_8.rs`) call, beyond the ones in [`super::aarch64`].
//!
//! Same conventions: a register is the array of its lanes, lane 0 first ([`u8x16`], [`u8x8`], [`p8x8`],
//! [`u16x8`], [`p16x8`], [`u64x1`]); each result is given lane by lane, through an open spec function where it
//! is more than a move or a XOR, with an executable twin `model_<name>` that `tests/equivalence/
//! intrinsics_aarch64_gfneon.rs` runs against the hardware.
#[cfg(verus_keep_ghost)]
use super::aarch64::{p64x2, u64x2};
#[cfg(verus_keep_ghost)]
use super::aarch64_bits::u8x16;
#[cfg(verus_keep_ghost)]
use super::transmuted;
#[cfg(verus_keep_ghost)]
use crate::clmul::clmul;
use core::arch::aarch64::*;
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUint8x8(uint8x8_t);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPoly8x8(poly8x8_t);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUint16x8(uint16x8_t);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPoly16x8(poly16x8_t);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUint64x1(uint64x1_t);

// ---------------------------------------------------------------------------------------------
// Views and layout
// ---------------------------------------------------------------------------------------------
/// The 8 bytes of a `uint8x8_t`, lane 0 first.
pub open spec fn u8x8(v: uint8x8_t) -> [u8; 8] {
    transmuted::<uint8x8_t, [u8; 8]>(v)
}

/// The 8 lanes of a `poly8x8_t`, lane 0 first.
pub open spec fn p8x8(v: poly8x8_t) -> [u8; 8] {
    transmuted::<poly8x8_t, [u8; 8]>(v)
}

/// The 8 lanes of a `uint16x8_t`, lane 0 first.
pub open spec fn u16x8(v: uint16x8_t) -> [u16; 8] {
    transmuted::<uint16x8_t, [u16; 8]>(v)
}

/// The 8 lanes of a `poly16x8_t`, lane 0 first.
pub open spec fn p16x8(v: poly16x8_t) -> [u16; 8] {
    transmuted::<poly16x8_t, [u16; 8]>(v)
}

/// The one lane of a `uint64x1_t`.
pub open spec fn u64x1(v: uint64x1_t) -> [u64; 1] {
    transmuted::<uint64x1_t, [u64; 1]>(v)
}

/// Layout: a `uint8x8_t` read as a `poly8x8_t` has the same lanes.
pub broadcast axiom fn axiom_u8x8_as_p8x8(v: uint8x8_t)
    ensures
        #[trigger] p8x8(transmuted::<uint8x8_t, poly8x8_t>(v)) == u8x8(v),
;

/// Layout: a `u64` read as a `poly8x8_t` is its bytes, little-endian.
pub broadcast axiom fn axiom_u64_as_p8x8(x: u64, i: int)
    requires
        0 <= i < 8,
    ensures
        #[trigger] p8x8(transmuted::<u64, poly8x8_t>(x))[i] == (x >> ((8 * i) as u64)) as u8,
;

/// Layout: `[u64; 2]` read as a `uint64x2_t` has those lanes.
pub broadcast axiom fn axiom_words_as_u64x2(w: [u64; 2])
    ensures
        #[trigger] u64x2(transmuted::<[u64; 2], uint64x2_t>(w)) == w,
;

// ---------------------------------------------------------------------------------------------
// Lane semantics, shared by the specifications and their executable twins
// ---------------------------------------------------------------------------------------------
/// Lane `i` of PMULL on bytes: the carry-less product of lane `i` of each operand, 15 bits in a 16-bit lane.
pub open spec fn vmull_p8_lane(a: u8, b: u8) -> u16 {
    clmul(a as u64, b as u128) as u16
}

/// Byte `k` of `UZP1` (`odd == 0`) or `UZP2` (`odd == 1`) on bytes: the even (odd) bytes of `a`, then those of
/// `b`.
pub open spec fn uzp_u8_lane(a: Seq<u8>, b: Seq<u8>, odd: int, k: int) -> u8 {
    if k < 8 {
        a[2 * k + odd]
    } else {
        b[2 * (k - 8) + odd]
    }
}

/// Lane `i` of `EXT` on 64-bit lanes: lane `i + n` of the concatenation `a`, `b`.
pub open spec fn ext_u64_lane(a: [u64; 2], b: [u64; 2], n: int, i: int) -> u64 {
    if i + n < 2 {
        a[i + n]
    } else {
        b[i + n - 2]
    }
}

/// Byte `k` of 16-bit lanes read as bytes: the low byte of lane `k / 2` at even `k`, its high byte at odd `k`.
pub open spec fn u16_byte(w: Seq<u16>, k: int) -> u8 {
    (w[k / 2] >> ((8 * (k % 2)) as u16)) as u8
}

// ---------------------------------------------------------------------------------------------
// The specifications
// ---------------------------------------------------------------------------------------------
pub assume_specification[ vreinterpretq_p64_u64 ](a: uint64x2_t) -> (r: poly64x2_t)
    ensures
        p64x2(r) == u64x2(a),
;

pub assume_specification[ vcreate_u64 ](a: u64) -> (r: uint64x1_t)
    ensures
        u64x1(r)[0] == a,
;

pub assume_specification[ vcombine_u64 ](a: uint64x1_t, b: uint64x1_t) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == u64x1(a)[0],
        u64x2(r)[1] == u64x1(b)[0],
;

/// EXT: the two lanes from lane `N` on of the concatenation `a`, `b`.
pub assume_specification<const N: i32>[ vextq_u64::<N> ](a: uint64x2_t, b: uint64x2_t) -> (r: uint64x2_t)
    ensures
        0 <= N < 2 ==> forall|i: int| 0 <= i < 2 ==> #[trigger] u64x2(r)[i] == ext_u64_lane(u64x2(a), u64x2(b), N as int, i),
;

/// DUP (element): lane `N` in both lanes.
pub assume_specification<const N: i32>[ vdupq_laneq_u64::<N> ](a: uint64x2_t) -> (r: uint64x2_t)
    ensures
        0 <= N < 2 ==> u64x2(r)[0] == u64x2(a)[N as int] && u64x2(r)[1] == u64x2(a)[N as int],
;

pub assume_specification[ vdup_n_p8 ](value: u8) -> (r: poly8x8_t)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] p8x8(r)[i] == value,
;

/// PMULL on bytes: eight carry-less products of byte lanes, each in a 16-bit lane.
pub assume_specification[ vmull_p8 ](a: poly8x8_t, b: poly8x8_t) -> (r: poly16x8_t)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] p16x8(r)[i] == vmull_p8_lane(p8x8(a)[i], p8x8(b)[i]),
;

pub assume_specification[ vreinterpretq_u16_p16 ](a: poly16x8_t) -> (r: uint16x8_t)
    ensures
        u16x8(r) == p16x8(a),
;

/// The 16-bit lanes as bytes, little-endian within each lane.
pub assume_specification[ vreinterpretq_u8_u16 ](a: uint16x8_t) -> (r: uint8x16_t)
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] u8x16(r)[k] == u16_byte(u16x8(a)@, k),
;

pub assume_specification<const IMM5: i32>[ vgetq_lane_u16::<IMM5> ](v: uint16x8_t) -> (r: u16)
    ensures
        0 <= IMM5 < 8 ==> r == u16x8(v)[IMM5 as int],
;

/// SHL (immediate) on 16-bit lanes.
pub assume_specification<const N: i32>[ vshlq_n_u16::<N> ](a: uint16x8_t) -> (r: uint16x8_t)
    ensures
        0 <= N < 16 ==> forall|i: int| 0 <= i < 8 ==> #[trigger] u16x8(r)[i] == u16x8(a)[i] << (N as u16),
;

pub assume_specification[ vget_low_u8 ](a: uint8x16_t) -> (r: uint8x8_t)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] u8x8(r)[i] == u8x16(a)[i],
;

pub assume_specification[ vget_high_u8 ](a: uint8x16_t) -> (r: uint8x8_t)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] u8x8(r)[i] == u8x16(a)[i + 8],
;

/// UZP1: the even bytes of `a`, then those of `b`.
pub assume_specification[ vuzp1q_u8 ](a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] u8x16(r)[k] == uzp_u8_lane(u8x16(a)@, u8x16(b)@, 0, k),
;

/// UZP2: the odd bytes of `a`, then those of `b`.
pub assume_specification[ vuzp2q_u8 ](a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] u8x16(r)[k] == uzp_u8_lane(u8x16(a)@, u8x16(b)@, 1, k),
;

pub assume_specification[ veorq_u8 ](a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] u8x16(r)[k] == u8x16(a)[k] ^ u8x16(b)[k],
;

// ---------------------------------------------------------------------------------------------
// Executable twins
// ---------------------------------------------------------------------------------------------
/// [`vmull_p8_lane`].
pub fn model_vmull_p8_lane(a: u8, b: u8) -> (r: u16)
    ensures
        r == vmull_p8_lane(a, b),
{
    crate::gf2_8::clmul8_software(a, b)
}

/// [`uzp_u8_lane`].
pub fn model_uzp_u8_lane(a: &[u8], b: &[u8], odd: usize, k: usize) -> (r: u8)
    requires
        a.len() == 16,
        b.len() == 16,
        odd < 2,
        k < 16,
    ensures
        r == uzp_u8_lane(a@, b@, odd as int, k as int),
{
    if k < 8 {
        a[2 * k + odd]
    } else {
        b[2 * (k - 8) + odd]
    }
}

/// [`ext_u64_lane`].
pub fn model_ext_u64_lane(a: [u64; 2], b: [u64; 2], n: usize, i: usize) -> (r: u64)
    requires
        n < 2,
        i < 2,
    ensures
        r == ext_u64_lane(a, b, n as int, i as int),
{
    if i + n < 2 {
        a[i + n]
    } else {
        b[i + n - 2]
    }
}

/// [`u16_byte`].
pub fn model_u16_byte(w: &[u16], k: usize) -> (r: u8)
    requires
        k < 2 * w.len(),
    ensures
        r == u16_byte(w@, k as int),
{
    (w[k / 2] >> ((8 * (k % 2)) as u16)) as u8
}

} // verus!
