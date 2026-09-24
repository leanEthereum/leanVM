//! The aarch64 backend: NEON batches.

use super::OUT_LEN;
use super::batch::Lanes32;
use core::arch::aarch64::*;

/// NEON: four lanes.
///
/// At this width the G dependency chain, not the four SIMD pipes, bounds the backend.
///
/// So it interleaves groups, and picks each rotation for latency.
#[derive(Clone, Copy)]
pub(super) struct Neon(uint32x4_t);

impl Lanes32 for Neon {
    const WIDTH: usize = 4;
    // Independent groups cover the G dependency chain.
    const GROUPS: usize = 4;

    #[inline(always)]
    unsafe fn load(p: *const u32) -> Self {
        Self(unsafe { vld1q_u32(p) })
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u32) {
        unsafe { vst1q_u32(p, self.0) }
    }
    #[inline(always)]
    fn splat(x: u32) -> Self {
        Self(unsafe { vdupq_n_u32(x) })
    }
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Self(unsafe { vaddq_u32(self.0, o.0) })
    }
    #[inline(always)]
    fn xor(self, o: Self) -> Self {
        Self(unsafe { veorq_u32(self.0, o.0) })
    }
    #[inline(always)]
    fn rotr<const N: u32>(self) -> Self {
        Self(rot4::<N>(self.0))
    }

    /// Four 4x4 transposes, one per quarter of the block.
    ///
    /// Quarter `q` holds words `4q..4q + 4`, so it transposes on its own.
    #[inline(always)]
    unsafe fn transpose(src: *const u8, stride: usize, block: &mut [Self; 16]) {
        unsafe {
            // The byte form of the load: the input has no 4-byte alignment.
            let r: [uint32x4_t; 16] =
                std::array::from_fn(|i| vreinterpretq_u32_u8(vld1q_u8(src.add((i / 4) * stride + 16 * (i % 4)))));
            for q in 0..4 {
                let [a, b, c, d] = [r[q], r[4 + q], r[8 + q], r[12 + q]];
                for (j, o) in transpose4(a, b, c, d).into_iter().enumerate() {
                    block[4 * q + j] = Self(o);
                }
            }
        }
    }

    /// The same network over the eight chaining words.
    ///
    /// Words 0..4 give each digest's first 16 bytes, words 4..8 its last 16.
    #[inline(always)]
    unsafe fn store_digests(h: &[Self; 8], out: *mut u8) {
        unsafe {
            for half in 0..2 {
                let [a, b, c, d] = [h[4 * half], h[4 * half + 1], h[4 * half + 2], h[4 * half + 3]];
                for (lane, o) in transpose4(a.0, b.0, c.0, d.0).into_iter().enumerate() {
                    // Unaligned: the output is bytes.
                    vst1q_u8(out.add(lane * OUT_LEN + 16 * half), vreinterpretq_u8_u32(o));
                }
            }
        }
    }
}

/// Rotate right by `N`, choosing the lowest-latency form.
///
/// Every rotation sits on the G dependency chain.
#[inline(always)]
fn rot4<const N: u32>(v: uint32x4_t) -> uint32x4_t {
    unsafe {
        match N {
            16 => vreinterpretq_u32_u16(vrev32q_u16(vreinterpretq_u16_u32(v))),
            8 => {
                /// Rotate each 32-bit element right by one byte.
                ///
                /// Byte `4l + j` of the result is byte `4l + (j + 1) % 4` of the input.
                static ROT8: [u8; 16] = [1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12];
                vreinterpretq_u32_u8(vqtbl1q_u8(vreinterpretq_u8_u32(v), vld1q_u8(ROT8.as_ptr())))
            }
            12 => rot_sri::<12, 20>(v),
            7 => rot_sri::<7, 25>(v),
            _ => unreachable!("BLAKE2s rotates by 16, 12, 8 or 7"),
        }
    }
}

/// Rotate right with `shl` then `sri`.
///
/// Assembly, because the compiler otherwise picks an accumulating form with a longer chain.
#[inline(always)]
fn rot_sri<const N: u32, const SHL: i32>(v: uint32x4_t) -> uint32x4_t {
    unsafe {
        let mut out = vshlq_n_u32::<SHL>(v);
        std::arch::asm!(
            "sri {out:v}.4s, {v:v}.4s, #{n}",
            out = inout(vreg) out,
            v = in(vreg) v,
            n = const N,
            options(pure, nomem, nostack)
        );
        out
    }
}

/// Transpose four vectors of four words: `out[j][i] = in[i][j]`.
#[inline(always)]
fn transpose4(a: uint32x4_t, b: uint32x4_t, c: uint32x4_t, d: uint32x4_t) -> [uint32x4_t; 4] {
    unsafe {
        let (ab0, ab1) = (vtrn1q_u32(a, b), vtrn2q_u32(a, b));
        let (cd0, cd1) = (vtrn1q_u32(c, d), vtrn2q_u32(c, d));
        let pair = |x, y| {
            (
                vreinterpretq_u32_u64(vtrn1q_u64(vreinterpretq_u64_u32(x), vreinterpretq_u64_u32(y))),
                vreinterpretq_u32_u64(vtrn2q_u64(vreinterpretq_u64_u32(x), vreinterpretq_u64_u32(y))),
            )
        };
        let ((o0, o2), (o1, o3)) = (pair(ab0, cd0), pair(ab1, cd1));
        [o0, o1, o2, o3]
    }
}
