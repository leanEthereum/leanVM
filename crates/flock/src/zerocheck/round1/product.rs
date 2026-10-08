// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! One medium position's `A B` bytes: its eight K-rows extended to `Lambda`, multiplied, and summed by powers of `x`.
//!
//! ```text
//!     out[l] = sum_K x^K * LDE(a_K)[l] * LDE(b_K)[l]        in GF(2^8), l in Lambda
//! ```
//!
//! - aarch64: the table lookups, products and shifts fused in NEON registers.
//! - AVX-512 with GFNI: one register per row, the products by `gf2p8mulb`.
//! - AVX2: two registers per row, the products by GFNI or by shifts and adds.
//! - Elsewhere: the scalar route, which is also every kernel's reference.

#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use core::arch::x86_64::*;

use primitives::field::F8;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "gfni")))]
use primitives::field::gf2_8::avx2::gf8_mul_vec32;
use primitives::field::gf2_8::gf8_reduce;
#[cfg(target_arch = "aarch64")]
use primitives::field::gf2_8::neon::{gf8_mul_vec16, gf8_reduce_vec16};

use super::{ELL, MEDIUM_BYTES, N_CHUNKS};
use crate::zerocheck::ntt::InvNttTableByteSingleGf8;

/// The `A B` bytes of one medium position, `a` and `b` its eight K-rows of eight bytes each.
#[inline]
pub(super) fn product_bytes(
    a: &[u8; MEDIUM_BYTES],
    b: &[u8; MEDIUM_BYTES],
    table: &InvNttTableByteSingleGf8,
) -> [u8; ELL] {
    let mut out = [0; ELL];
    shift_reduce_inner_ab(a, b, table, &mut out);
    out
}

// For one medium position and its eight K-rows K in 0..8:
//   1. Look up the extended A, B rows at bytes `8K .. 8K + 8`.
//   2. y_K[lane] = ntt_a[lane] · ntt_b[lane]  (in F_8).
//   3. acc[lane] ^= (y_K[lane] as u16) << K   (no reduction yet).
// At the end, reduce each acc[lane] back to a u8 in F_8.
//
// Output `out[lane]` is the F_8 representative of Σ_K x^K · y_K[lane] mod p.

// Fused NEON inner kernel: inv_NTT apply + F_8 mul + shift_reduce, all in
// NEON registers (no Vec<F8> round-trip).
//
// `xor_apply_byte_into_8_regs::<BH, ODD>` handles one byte position (b ≥ 1).
// `BH` (= b >> 1) selects which chunk-index XOR to apply; `ODD` (= b & 1)
// switches on the within-chunk half-swap. Both const-generic so the compiler
// dead-code-eliminates the if-branch and folds the chunk-index XORs.
//
// `fused_apply_one_k::<K>` runs one full K-row: the initial b=0 plain load,
// 7 calls to the byte helper for b=1..7 (with the specific protocol BH/ODD
// pattern), one 16-lane F_8 mul per output chunk, and finally widen-shift-XOR
// into the per-(K, lane) 16-bit accumulators.

/// # Safety
/// `table_base` points to a `256 * 64`-byte table, and `BH < 4`.
#[cfg(target_arch = "aarch64")]
// `0 ^ BH` is the i = 0 case of the `i ^ BH` row-select pattern below; spelling
// it out keeps the four loads visibly parallel.
#[allow(clippy::identity_op)]
#[inline(always)]
#[expect(
    clippy::too_many_arguments,
    reason = "Separate NEON accumulators preserve the register layout of the fused kernel."
)]
unsafe fn xor_apply_byte_into_8_regs<const BH: usize>(
    table_base: *const u8,
    a_byte: u8,
    b_byte: u8,
    da0: &mut core::arch::aarch64::uint8x16_t,
    da1: &mut core::arch::aarch64::uint8x16_t,
    da2: &mut core::arch::aarch64::uint8x16_t,
    da3: &mut core::arch::aarch64::uint8x16_t,
    db0: &mut core::arch::aarch64::uint8x16_t,
    db1: &mut core::arch::aarch64::uint8x16_t,
    db2: &mut core::arch::aarch64::uint8x16_t,
    db3: &mut core::arch::aarch64::uint8x16_t,
) {
    // SAFETY: NEON is part of the aarch64 baseline; `table_base` is the caller's `256 * 64`-byte table, so row
    // `byte * 64` plus a chunk offset `(i ^ BH) * 16 < 64` (`BH < 4`) stays inside it.
    unsafe {
        let ra = table_base.add(a_byte as usize * 64);
        let rb = table_base.add(b_byte as usize * 64);
        let va0 = vld1q_u8(ra.add((0 ^ BH) * 16));
        let va1 = vld1q_u8(ra.add((1 ^ BH) * 16));
        let va2 = vld1q_u8(ra.add((2 ^ BH) * 16));
        let va3 = vld1q_u8(ra.add((3 ^ BH) * 16));
        let vb0 = vld1q_u8(rb.add((0 ^ BH) * 16));
        let vb1 = vld1q_u8(rb.add((1 ^ BH) * 16));
        let vb2 = vld1q_u8(rb.add((2 ^ BH) * 16));
        let vb3 = vld1q_u8(rb.add((3 ^ BH) * 16));
        *da0 = veorq_u8(*da0, va0);
        *da1 = veorq_u8(*da1, va1);
        *da2 = veorq_u8(*da2, va2);
        *da3 = veorq_u8(*da3, va3);
        *db0 = veorq_u8(*db0, vb0);
        *db1 = veorq_u8(*db1, vb1);
        *db2 = veorq_u8(*db2, vb2);
        *db3 = veorq_u8(*db3, vb3);
    }
}

/// Process one K-row: 8 byte positions of `a` and `b` via the inv_NTT table,
/// F_8 multiply, widen-shift by K, XOR into the four `(acc_lo, acc_hi)` pairs.
///
/// # Safety
/// `table_base` points to a `256 * 64`-byte table, and `a_row` and `b_row` to `N_CHUNKS` readable bytes each.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
#[expect(
    clippy::too_many_arguments,
    reason = "Separate NEON accumulators preserve the register layout of the fused kernel."
)]
unsafe fn fused_apply_one_k<const K: i32>(
    table_base: *const u8,
    a_row: *const u8,
    b_row: *const u8,
    acc0_lo: &mut core::arch::aarch64::uint16x8_t,
    acc0_hi: &mut core::arch::aarch64::uint16x8_t,
    acc1_lo: &mut core::arch::aarch64::uint16x8_t,
    acc1_hi: &mut core::arch::aarch64::uint16x8_t,
    acc2_lo: &mut core::arch::aarch64::uint16x8_t,
    acc2_hi: &mut core::arch::aarch64::uint16x8_t,
    acc3_lo: &mut core::arch::aarch64::uint16x8_t,
    acc3_hi: &mut core::arch::aarch64::uint16x8_t,
) {
    // SAFETY: NEON is part of the aarch64 baseline; the caller guarantees `N_CHUNKS` readable bytes at `a_row` and
    // `b_row` and a `256 * 64`-byte table, and every load is a table row plus an offset below 64.
    unsafe {
        // `π_b(i') = i' ⊕ 8b` is a chunk-index XOR by `b >> 1`, which is a free
        // load offset, and for odd `b` a swap of each chunk's two 8-byte halves.
        // That swap is an involution and distributes over XOR, and it commutes
        // with the chunk reindexing, so the eight positions need one swap of the
        // accumulators between the odd group and the even group rather than one
        // per register per odd position: `E ⊕ S(O)` with the odds accumulated
        // plainly first. Four times fewer `ext`, and `ext` was the largest
        // single share of this body's vector work.
        let ra1 = table_base.add(*a_row.add(1) as usize * 64);
        let rb1 = table_base.add(*b_row.add(1) as usize * 64);
        let mut da0 = vld1q_u8(ra1);
        let mut da1 = vld1q_u8(ra1.add(16));
        let mut da2 = vld1q_u8(ra1.add(32));
        let mut da3 = vld1q_u8(ra1.add(48));
        let mut db0 = vld1q_u8(rb1);
        let mut db1 = vld1q_u8(rb1.add(16));
        let mut db2 = vld1q_u8(rb1.add(32));
        let mut db3 = vld1q_u8(rb1.add(48));

        // The rest of the odd positions, b = 3, 5, 7.
        macro_rules! apply {
            ($bh:literal, $b:literal) => {
                xor_apply_byte_into_8_regs::<$bh>(
                    table_base,
                    *a_row.add($b),
                    *b_row.add($b),
                    &mut da0,
                    &mut da1,
                    &mut da2,
                    &mut da3,
                    &mut db0,
                    &mut db1,
                    &mut db2,
                    &mut db3,
                )
            };
        }
        apply!(1, 3);
        apply!(2, 5);
        apply!(3, 7);

        // One swap for the whole odd group.
        da0 = vextq_u8::<8>(da0, da0);
        da1 = vextq_u8::<8>(da1, da1);
        da2 = vextq_u8::<8>(da2, da2);
        da3 = vextq_u8::<8>(da3, da3);
        db0 = vextq_u8::<8>(db0, db0);
        db1 = vextq_u8::<8>(db1, db1);
        db2 = vextq_u8::<8>(db2, db2);
        db3 = vextq_u8::<8>(db3, db3);

        // The even positions, b = 0, 2, 4, 6, which need no swap.
        apply!(0, 0);
        apply!(1, 2);
        apply!(2, 4);
        apply!(3, 6);

        // F_8 multiply lane-wise (4 × 16 lanes = 64 total).
        let y0 = gf8_mul_vec16(da0, db0);
        let y1 = gf8_mul_vec16(da1, db1);
        let y2 = gf8_mul_vec16(da2, db2);
        let y3 = gf8_mul_vec16(da3, db3);

        // Widen-shift by K, XOR into the 16-bit accumulators.
        *acc0_lo = veorq_u16(*acc0_lo, vshll_n_u8::<K>(vget_low_u8(y0)));
        *acc0_hi = veorq_u16(*acc0_hi, vshll_n_u8::<K>(vget_high_u8(y0)));
        *acc1_lo = veorq_u16(*acc1_lo, vshll_n_u8::<K>(vget_low_u8(y1)));
        *acc1_hi = veorq_u16(*acc1_hi, vshll_n_u8::<K>(vget_high_u8(y1)));
        *acc2_lo = veorq_u16(*acc2_lo, vshll_n_u8::<K>(vget_low_u8(y2)));
        *acc2_hi = veorq_u16(*acc2_hi, vshll_n_u8::<K>(vget_high_u8(y2)));
        *acc3_lo = veorq_u16(*acc3_lo, vshll_n_u8::<K>(vget_low_u8(y3)));
        *acc3_hi = veorq_u16(*acc3_hi, vshll_n_u8::<K>(vget_high_u8(y3)));
    }
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn shift_reduce_inner_ab_fused_neon(
    a_packed: &[u8; MEDIUM_BYTES],
    b_packed: &[u8; MEDIUM_BYTES],
    inv_table: &InvNttTableByteSingleGf8,
    out: &mut [u8; 64],
) {
    let byte_base_b = 0;
    let table_base = inv_table.data_ptr();

    // SAFETY: NEON is part of the aarch64 baseline. The table is `256 * 64` bytes, its `k` being `K_SKIP` (asserted
    // at the entry point). The row windows `byte_base_b + K * N_CHUNKS .. + N_CHUNKS` for `K < 8` lie in both packed
    // tables, whose lengths the entry point asserts against the windows it walks. `out` is 64 bytes.
    unsafe {
        let mut acc0_lo = vdupq_n_u16(0);
        let mut acc0_hi = vdupq_n_u16(0);
        let mut acc1_lo = vdupq_n_u16(0);
        let mut acc1_hi = vdupq_n_u16(0);
        let mut acc2_lo = vdupq_n_u16(0);
        let mut acc2_hi = vdupq_n_u16(0);
        let mut acc3_lo = vdupq_n_u16(0);
        let mut acc3_hi = vdupq_n_u16(0);

        // 8 K-iterations: each consumes N_CHUNKS = 8 packed witness bytes
        // for `a` and `b`. K is a const generic so `vshll_n_u8::<K>` specializes.
        macro_rules! do_k {
            ($k:literal) => {{
                let off = byte_base_b + $k * N_CHUNKS;
                fused_apply_one_k::<$k>(
                    table_base,
                    a_packed.as_ptr().add(off),
                    b_packed.as_ptr().add(off),
                    &mut acc0_lo,
                    &mut acc0_hi,
                    &mut acc1_lo,
                    &mut acc1_hi,
                    &mut acc2_lo,
                    &mut acc2_hi,
                    &mut acc3_lo,
                    &mut acc3_hi,
                );
            }};
        }
        do_k!(0);
        do_k!(1);
        do_k!(2);
        do_k!(3);
        do_k!(4);
        do_k!(5);
        do_k!(6);
        do_k!(7);

        // Reduce 16-bit accs → 16-byte F_8 results (4 × 16 lanes).
        let r0 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc0_lo), vreinterpretq_u8_u16(acc0_hi));
        let r1 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc1_lo), vreinterpretq_u8_u16(acc1_hi));
        let r2 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc2_lo), vreinterpretq_u8_u16(acc2_hi));
        let r3 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc3_lo), vreinterpretq_u8_u16(acc3_hi));

        let p = out.as_mut_ptr();
        vst1q_u8(p, r0);
        vst1q_u8(p.add(16), r1);
        vst1q_u8(p.add(32), r2);
        vst1q_u8(p.add(48), r3);
    }
}

/// Dispatch helper: picks the widest SIMD kernel this target has, otherwise scalar.
#[inline]
fn shift_reduce_inner_ab(
    a_packed: &[u8; MEDIUM_BYTES],
    b_packed: &[u8; MEDIUM_BYTES],
    inv_table: &InvNttTableByteSingleGf8,
    out: &mut [u8; 64],
) {
    #[cfg(target_arch = "aarch64")]
    {
        shift_reduce_inner_ab_fused_neon(a_packed, b_packed, inv_table, out);
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))]
    {
        // SAFETY: gfni and avx512bw are statically enabled at compile time.
        unsafe { shift_reduce_inner_ab_gfni_512(a_packed, b_packed, inv_table, out) };
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        not(all(target_feature = "gfni", target_feature = "avx512bw"))
    ))]
    {
        // SAFETY: avx2, and gfni where the kernel uses it, are statically enabled at compile time.
        unsafe { shift_reduce_inner_ab_avx2(a_packed, b_packed, inv_table, out) };
    }
    #[cfg(not(any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "avx2"))))]
    {
        shift_reduce_inner_ab_scalar(a_packed, b_packed, inv_table, out);
    }
}

/// The GFNI kernel one register wide: `ELL` is 64, so the whole column is one
/// ZMM and the combine issues a quarter of the instructions the 128-bit arm
/// does. Byte unpacking and `packus` both work within 128-bit lanes and are
/// exact inverses there, so the widened accumulators may sit in a different
/// order than the narrow arm's and still narrow back to the same bytes.
///
/// # Safety
/// Requires the `gfni` and `avx512bw` target features.
#[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))]
#[target_feature(enable = "gfni", enable = "avx512f", enable = "avx512bw")]
unsafe fn shift_reduce_inner_ab_gfni_512(
    a_packed: &[u8; MEDIUM_BYTES],
    b_packed: &[u8; MEDIUM_BYTES],
    inv_table: &InvNttTableByteSingleGf8,
    out: &mut [u8; 64],
) {
    let byte_base_b = 0;
    let chunk = |k: usize| byte_base_b + k * N_CHUNKS..byte_base_b + (k + 1) * N_CHUNKS;

    // SAFETY: the target features are carried by the function; the store covers exactly `out`.
    unsafe {
        let (mut acc_lo, mut acc_hi) = (_mm512_setzero_si512(), _mm512_setzero_si512());
        let zero = _mm512_setzero_si512();

        for k in 0..8 {
            let y = _mm512_gf2p8mul_epi8(
                inv_table.apply_zmm(a_packed[chunk(k)].try_into().expect("one chunk")),
                inv_table.apply_zmm(b_packed[chunk(k)].try_into().expect("one chunk")),
            );
            let shift = _mm_cvtsi32_si128(k as i32);
            acc_lo = _mm512_xor_si512(acc_lo, _mm512_sll_epi16(_mm512_unpacklo_epi8(y, zero), shift));
            acc_hi = _mm512_xor_si512(acc_hi, _mm512_sll_epi16(_mm512_unpackhi_epi8(y, zero), shift));
        }

        // Vectorized gf8_reduce over u16 lanes: two-step fold of the high byte
        // h with h ^ (h<<1) ^ (h<<3) ^ (h<<4)  (x^8 = x^4+x^3+x+1).
        let mask_ff = _mm512_set1_epi16(0xff);
        let fold = |p: __m512i| -> __m512i {
            let h = _mm512_srli_epi16::<8>(p);
            _mm512_xor_si512(
                _mm512_and_si512(p, mask_ff),
                _mm512_xor_si512(
                    _mm512_xor_si512(h, _mm512_slli_epi16::<1>(h)),
                    _mm512_xor_si512(_mm512_slli_epi16::<3>(h), _mm512_slli_epi16::<4>(h)),
                ),
            )
        };
        // Two folds bring 15-bit accumulators down to 8 bits; the second fold's
        // high byte is at most 0x0f, so lanes stay below 256 for `packus`.
        let reduce = |p: __m512i| _mm512_and_si512(fold(fold(p)), mask_ff);
        _mm512_storeu_si512(
            out.as_mut_ptr().cast(),
            _mm512_packus_epi16(reduce(acc_lo), reduce(acc_hi)),
        );
    }
}

/// The 512-bit kernel two registers wide. With GFNI the products are
/// `gf2p8mulb`; without it, the shift-and-add of `gf2_8::avx2::gf8_mul_vec32`.
///
/// # Safety
/// Requires the `avx2` target feature, and `gfni` where the target has it.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(all(target_feature = "gfni", target_feature = "avx512bw"), allow(dead_code))]
#[target_feature(enable = "avx2")]
unsafe fn shift_reduce_inner_ab_avx2(
    a_packed: &[u8; MEDIUM_BYTES],
    b_packed: &[u8; MEDIUM_BYTES],
    inv_table: &InvNttTableByteSingleGf8,
    out: &mut [u8; 64],
) {
    let byte_base_b = 0;
    // `inv_table.apply` overwrites every lane, so these need no re-zeroing per K.
    let mut a_col = [F8::ZERO; ELL];
    let mut b_col = [F8::ZERO; ELL];

    // SAFETY: the target features are carried by the function or enabled at
    // compile time; the loads and stores stay within a_col/b_col/out, each
    // exactly `ELL` bytes.
    unsafe {
        let mut acc = [[_mm256_setzero_si256(); 2]; 2];
        let zero = _mm256_setzero_si256();

        for k in 0..8 {
            let chunk_off = byte_base_b + k * N_CHUNKS;
            inv_table.apply(&a_packed[chunk_off..chunk_off + N_CHUNKS], &mut a_col);
            inv_table.apply(&b_packed[chunk_off..chunk_off + N_CHUNKS], &mut b_col);
            let shift = _mm_cvtsi32_si128(k as i32);
            for (h, [lo, hi]) in acc.iter_mut().enumerate() {
                let a = _mm256_loadu_si256(a_col.as_ptr().add(32 * h).cast());
                let b = _mm256_loadu_si256(b_col.as_ptr().add(32 * h).cast());
                #[cfg(target_feature = "gfni")]
                let y = _mm256_gf2p8mul_epi8(a, b);
                #[cfg(not(target_feature = "gfni"))]
                let y = gf8_mul_vec32(a, b);
                *lo = _mm256_xor_si256(*lo, _mm256_sll_epi16(_mm256_unpacklo_epi8(y, zero), shift));
                *hi = _mm256_xor_si256(*hi, _mm256_sll_epi16(_mm256_unpackhi_epi8(y, zero), shift));
            }
        }

        // Vectorized gf8_reduce over u16 lanes: two-step fold of the high byte
        // h with h ^ (h<<1) ^ (h<<3) ^ (h<<4)  (x^8 = x^4+x^3+x+1).
        let mask_ff = _mm256_set1_epi16(0xff);
        let fold = |p: __m256i| -> __m256i {
            let h = _mm256_srli_epi16::<8>(p);
            _mm256_xor_si256(
                _mm256_and_si256(p, mask_ff),
                _mm256_xor_si256(
                    _mm256_xor_si256(h, _mm256_slli_epi16::<1>(h)),
                    _mm256_xor_si256(_mm256_slli_epi16::<3>(h), _mm256_slli_epi16::<4>(h)),
                ),
            )
        };
        // Two folds bring 15-bit accumulators down to 8 bits; the second fold's
        // high byte is at most 0x0f, so lanes stay below 256 for `packus`.
        let reduce = |p: __m256i| _mm256_and_si256(fold(fold(p)), mask_ff);
        for (h, [lo, hi]) in acc.into_iter().enumerate() {
            _mm256_storeu_si256(
                out.as_mut_ptr().add(32 * h).cast(),
                _mm256_packus_epi16(reduce(lo), reduce(hi)),
            );
        }
    }
}

/// The scalar route: the fallback without NEON or AVX2, and every kernel's reference.
#[cfg_attr(
    any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "avx2")),
    allow(dead_code)
)]
pub(super) fn shift_reduce_inner_ab_scalar(
    a_packed: &[u8; MEDIUM_BYTES],
    b_packed: &[u8; MEDIUM_BYTES],
    inv_table: &InvNttTableByteSingleGf8,
    out: &mut [u8; 64],
) {
    // `inv_table.apply` overwrites every lane, so these need no re-zeroing per K.
    let mut a_col = [F8::ZERO; ELL];
    let mut b_col = [F8::ZERO; ELL];
    let mut acc: [u16; 64] = [0u16; 64];
    let byte_base_b = 0;
    for k in 0..8 {
        let chunk_off = byte_base_b + k * N_CHUNKS;
        inv_table.apply(&a_packed[chunk_off..chunk_off + N_CHUNKS], &mut a_col);
        inv_table.apply(&b_packed[chunk_off..chunk_off + N_CHUNKS], &mut b_col);
        for lane in 0..ELL {
            let y = (a_col[lane] * b_col[lane]).0 as u16;
            acc[lane] ^= y << k;
        }
    }
    for lane in 0..ELL {
        out[lane] = gf8_reduce(acc[lane]);
    }
}
