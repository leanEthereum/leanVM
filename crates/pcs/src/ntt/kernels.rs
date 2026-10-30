//! The butterfly sweeps of [`AdditiveNttF64`](super::AdditiveNttF64): portable, AVX2, AVX-512 and NEON.

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
use core::arch::x86_64::__m512i;
use primitives::field::F64;

/// Visit every row group of a fused multi-layer block.
///
/// ```text
///     the block is N slabs of equal height
///
///     slab 0:     row 0   row 1   ...   row r   ...
///     slab 1:     row 0   row 1   ...   row r   ...
///     ...
///     slab N-1:   row 0   row 1   ...   row r   ...
///
///     group r  =  row r of every slab
/// ```
///
/// - Each slab hands out its rows in turn, so the groups are disjoint without any pointer arithmetic.
/// - A source, when given, is a separate buffer of the block's length, cut the same way.
/// - With no source, a group is read in place.
#[inline(always)]
fn fused_rows<const N: usize>(
    block: &mut [F64],
    src: Option<&[F64]>,
    stride_rows: usize,
    num_ntts: usize,
    do_one: impl Fn(Option<[&[F64]; N]>, &mut [&mut [F64]; N]),
) {
    // Words from one slab to the next.
    let stride = stride_rows * num_ntts;
    let len = block.len();
    debug_assert_eq!(len, N * stride);
    let mut slabs = block.chunks_exact_mut(stride);
    let mut block_rows: [_; N] = std::array::from_fn(|_| slabs.next().unwrap().chunks_exact_mut(num_ntts));
    let mut src_rows = src.map(|src| {
        debug_assert_eq!(src.len(), len);
        let mut slabs = src.chunks_exact(stride);
        std::array::from_fn::<_, N, _>(|_| slabs.next().unwrap().chunks_exact(num_ntts))
    });
    for _ in 0..stride_rows {
        let mut rows: [&mut [F64]; N] = block_rows.each_mut().map(|slab| slab.next().unwrap());
        let srcs = src_rows
            .as_mut()
            .map(|slabs| slabs.each_mut().map(|slab| slab.next().unwrap()));
        do_one(srcs, &mut rows);
    }
}

/// The twelve butterflies of one radix-8 row group, as `butterfly(top row, bottom row, twiddle)` calls in order.
///
/// - Layer L: rows 4 apart, one twiddle for the whole block.
/// - Layer L+1: rows 2 apart, one twiddle per half.
/// - Layer L+2: adjacent rows, one twiddle per quarter.
///
/// The twiddles are breadth-first, as in [`butterfly_interleaved_fused_3layer`].
#[inline(always)]
fn radix8_schedule(mut butterfly: impl FnMut(usize, usize, usize)) {
    butterfly(0, 4, 0);
    butterfly(1, 5, 0);
    butterfly(2, 6, 0);
    butterfly(3, 7, 0);
    butterfly(0, 2, 1);
    butterfly(1, 3, 1);
    butterfly(4, 6, 2);
    butterfly(5, 7, 2);
    butterfly(0, 1, 3);
    butterfly(2, 3, 4);
    butterfly(4, 5, 5);
    butterfly(6, 7, 6);
}

/// The four butterflies of one radix-4 row group, as `butterfly(top row, bottom row, twiddle)` calls in order.
///
/// - Layer L: rows 2 apart, one twiddle for the block.
/// - Layer L+1: adjacent rows, one twiddle per half.
#[inline(always)]
fn radix4_schedule(mut butterfly: impl FnMut(usize, usize, usize)) {
    butterfly(0, 2, 0);
    butterfly(1, 3, 0);
    butterfly(0, 1, 1);
    butterfly(2, 3, 2);
}

/// Layers L, L+1 and L+2 fused into one sweep over a layer-L block.
///
/// ```text
///     a group is 8 rows, e = (block rows) / 8 apart:  r, r + e, ..., r + 7e
///
///     layer L     pairs rows 4e apart
///     layer L+1   pairs rows 2e apart
///     layer L+2   pairs rows  e apart
/// ```
///
/// - The eight rows stay in L1 across all twelve butterflies.
/// - The seven twiddles are breadth-first: one for layer L, two for L+1, four for L+2.
pub(super) fn butterfly_interleaved_fused_3layer(
    block: &mut [F64],
    src: Option<&[F64]>,
    t: &[F64; 7],
    eighth: usize,
    num_ntts: usize,
) {
    // On AVX-512 the whole sweep is one target-feature function, so each group's butterflies run on registers
    // inside the sweep's loop: a call per group would pass the vectors through memory.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        #[inline]
        #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
        fn sweep(block: &mut [F64], src: Option<&[F64]>, t: &[F64; 7], eighth: usize, num_ntts: usize) {
            fused_sweep_avx512::<8, 7>(
                block,
                src,
                eighth,
                num_ntts,
                t,
                #[inline(always)]
                |v, t| {
                    radix8_schedule(
                        #[inline(always)]
                        |top, bot, k| butterfly_regs(v, top, bot, t[k]),
                    );
                },
            );
        }
        // SAFETY: this code is compiled only where VPCLMULQDQ and AVX-512F are enabled, and `primitives`
        // refuses to build there without the AVX-512BW the sweep adds.
        unsafe { sweep(block, src, t, eighth, num_ntts) }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    fused_rows::<8>(block, src, eighth, num_ntts, |src, rows| {
        radix8_butterflies(src, rows, t)
    });
}

/// The sweep of [`fused_rows`] with `kernel` on registers: [`fused_lanes_avx512`] for each row group.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
fn fused_sweep_avx512<const N: usize, const T: usize>(
    block: &mut [F64],
    src: Option<&[F64]>,
    stride_rows: usize,
    num_ntts: usize,
    twiddles: &[F64; T],
    kernel: impl Fn(&mut RowVectors<N>, &[Twiddle; T]),
) {
    fused_rows::<N>(block, src, stride_rows, num_ntts, |src, rows| {
        fused_lanes_avx512(
            src,
            rows,
            twiddles,
            #[inline(always)]
            |v, t| kernel(v, t),
        )
    });
}

/// The twelve butterflies of one radix-8 row group, with its seven twiddles breadth-first.
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
#[inline(always)]
fn radix8_butterflies(src: Option<[&[F64]; 8]>, rows: &mut [&mut [F64]; 8], t: &[F64; 7]) {
    copy_rows(src, rows);
    radix8_schedule(|top, bot, k| butterfly_rows(rows, top, bot, t[k]));
}

/// [`butterfly_lanes`] on rows `top` and `bot` of a row group.
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
#[inline(always)]
fn butterfly_rows<const N: usize>(rows: &mut [&mut [F64]; N], top: usize, bot: usize, twiddle: F64) {
    let [top, bot] = rows.get_disjoint_mut([top, bot]).unwrap();
    butterfly_lanes(top, bot, twiddle);
}

/// Copy the rows that are read from a source into the rows that are written, where the two differ.
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
#[inline(always)]
fn copy_rows<const N: usize>(src: Option<[&[F64]; N]>, rows: &mut [&mut [F64]; N]) {
    for (from, row) in src.iter().flatten().zip(rows.iter_mut()) {
        row.copy_from_slice(from);
    }
}

/// Layers L and L+1 fused into one sweep over a layer-L block, four rows at a time.
///
/// The three twiddles are breadth-first: one for layer L, two for L+1.
pub(super) fn butterfly_interleaved_fused_2layer(
    block: &mut [F64],
    src: Option<&[F64]>,
    t: &[F64; 3],
    quarter: usize,
    num_ntts: usize,
) {
    // On AVX-512 the sweep is one target-feature function, like the radix-8 one.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        #[inline]
        #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
        fn sweep(block: &mut [F64], src: Option<&[F64]>, t: &[F64; 3], quarter: usize, num_ntts: usize) {
            fused_sweep_avx512::<4, 3>(
                block,
                src,
                quarter,
                num_ntts,
                t,
                #[inline(always)]
                |v, t| {
                    radix4_schedule(
                        #[inline(always)]
                        |top, bot, k| butterfly_regs(v, top, bot, t[k]),
                    );
                },
            );
        }
        // SAFETY: as in `butterfly_interleaved_fused_3layer`.
        unsafe { sweep(block, src, t, quarter, num_ntts) }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    fused_rows::<4>(block, src, quarter, num_ntts, |src, rows| {
        radix4_butterflies(src, rows, t)
    });
}

/// The four butterflies of one radix-4 row group.
#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
#[inline(always)]
fn radix4_butterflies(src: Option<[&[F64]; 4]>, rows: &mut [&mut [F64]; 4], t: &[F64; 3]) {
    copy_rows(src, rows);
    radix4_schedule(|top, bot, k| butterfly_rows(rows, top, bot, t[k]));
}

#[inline]
pub(super) fn butterfly_interleaved_block(block: &mut [F64], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    for r in 0..block_size_half {
        let off = r * num_ntts;
        butterfly_lanes(&mut top[off..off + num_ntts], &mut bot[off..off + num_ntts], twiddle);
    }
}

/// Butterfly all `num_ntts` lanes of one (top row, bottom row) pair with a
/// shared twiddle: new_u = u + v*t; new_v = v + new_u.
///
/// On NEON this processes eight lanes per iteration, and the scalar path handles the rest.
#[inline]
fn butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    debug_assert_eq!(top.len(), bot.len());
    // The lanes the vector kernels cover; the scalar loop at the end takes the rest.
    let done: usize;
    // Every layer's block 0 has twiddle zero: the butterfly is then `v' = v + u`, no product.
    if twiddle == F64::ZERO {
        for (v, &u) in bot.iter_mut().zip(top.iter()) {
            *v += u;
        }
        return;
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        // SAFETY: this code is compiled only where VPCLMULQDQ and AVX-512F are enabled, and `primitives`
        // refuses to build there without the AVX-512BW the kernel adds.
        unsafe { butterfly_lanes_avx512(top, bot, twiddle.0) };
        done = top.len();
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "pclmulqdq",
        target_feature = "avx2",
        not(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))
    ))]
    {
        // SAFETY: this code is compiled only where PCLMULQDQ and AVX2 are enabled, and every such
        // machine runs the kernel's features.
        unsafe { butterfly_lanes_avx2(top, bot, twiddle.0) };
        done = top.len();
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        // SAFETY: the aes target feature is enabled at compile time, and NEON is in the aarch64 baseline.
        done = unsafe { butterfly_lanes_neon(top, bot, twiddle.0) };
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq", target_feature = "avx2")
    )))]
    {
        done = 0;
    }
    for lane in done..top.len() {
        let v = bot[lane];
        let new_u = top[lane] + v * twiddle;
        top[lane] = new_u;
        bot[lane] = v + new_u;
    }
}

/// The transpose of [`butterfly_lanes`]: `s = u + v; u' = s; v' = s * t + v` over a pair of rows.
pub(crate) fn transpose_butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    debug_assert_eq!(top.len(), bot.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    // SAFETY: as in `butterfly_lanes`.
    unsafe {
        transpose_butterfly_lanes_avx512(top, bot, twiddle.0)
    }
    // One pass beats routing through the forward vector kernel, whose two extra XOR passes cost more here.
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    for (u, v) in top.iter_mut().zip(bot.iter_mut()) {
        let s = *u + *v;
        *u = s;
        *v += s * twiddle;
    }
}

/// [`butterfly_lanes_avx512`] at half the width, for a machine with AVX2 but not both
/// VPCLMULQDQ and AVX-512.
///
/// A tail of fewer than four lanes goes through a zero-padded vector, where the butterfly of zeros is zero.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "pclmulqdq",
    target_feature = "avx2",
    not(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))
))]
#[inline]
#[target_feature(enable = "pclmulqdq", enable = "avx2")]
#[cfg_attr(target_feature = "vpclmulqdq", target_feature(enable = "vpclmulqdq"))]
fn butterfly_lanes_avx2(top: &mut [F64], bot: &mut [F64], twiddle: u64) {
    use core::arch::x86_64::*;
    use primitives::{load_at, store_at};

    let vectors = top.len() / 4;
    for i in 0..vectors {
        let (new_u, new_v) = butterfly_ymm(load_at(top, 4 * i), load_at(bot, 4 * i), twiddle);
        store_at(top, 4 * i, new_u);
        store_at(bot, 4 * i, new_v);
    }
    let tail = top.len() - 4 * vectors;
    if tail != 0 {
        let (mut u, mut v) = ([F64::ZERO; 4], [F64::ZERO; 4]);
        u[..tail].copy_from_slice(&top[4 * vectors..]);
        v[..tail].copy_from_slice(&bot[4 * vectors..]);
        let (new_u, new_v) = butterfly_ymm(load_at::<_, __m256i>(&u, 0), load_at::<_, __m256i>(&v, 0), twiddle);
        store_at(&mut u, 0, new_u);
        store_at(&mut v, 0, new_v);
        top[4 * vectors..].copy_from_slice(&u[..tail]);
        bot[4 * vectors..].copy_from_slice(&v[..tail]);
    }
}

/// Four butterflies `u' = u + v * t`, `v' = v + u'` in registers: the products one per 128-bit
/// lane, even lanes then odd lanes as in `mul_xor_avx512`, then one shift-and-XOR reduction.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "pclmulqdq",
    target_feature = "avx2",
    not(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))
))]
#[inline]
#[target_feature(enable = "pclmulqdq", enable = "avx2")]
#[cfg_attr(target_feature = "vpclmulqdq", target_feature(enable = "vpclmulqdq"))]
fn butterfly_ymm(
    u: core::arch::x86_64::__m256i,
    v: core::arch::x86_64::__m256i,
    twiddle: u64,
) -> (core::arch::x86_64::__m256i, core::arch::x86_64::__m256i) {
    use core::arch::x86_64::*;
    use primitives::field::gf2_64x3::x86_64::reduce_halves256;

    #[cfg(target_feature = "vpclmulqdq")]
    let (even, odd) = {
        let tw = _mm256_set1_epi64x(twiddle as i64);
        (
            _mm256_clmulepi64_epi128::<0x00>(v, tw),
            _mm256_clmulepi64_epi128::<0x11>(v, tw),
        )
    };
    // Four 128-bit multiplies; immediate bit 0 picks the qword of `v`.
    #[cfg(not(target_feature = "vpclmulqdq"))]
    let (even, odd) = {
        let tw = _mm_cvtsi64_si128(twiddle as i64);
        let (v01, v23) = (_mm256_castsi256_si128(v), _mm256_extracti128_si256::<1>(v));
        (
            _mm256_set_m128i(
                _mm_clmulepi64_si128::<0x00>(v23, tw),
                _mm_clmulepi64_si128::<0x00>(v01, tw),
            ),
            _mm256_set_m128i(
                _mm_clmulepi64_si128::<0x01>(v23, tw),
                _mm_clmulepi64_si128::<0x01>(v01, tw),
            ),
        )
    };
    let new_u = _mm256_xor_si256(u, reduce_halves256(even, odd));
    (new_u, _mm256_xor_si256(v, new_u))
}

/// The butterflies of one row pair that the NEON kernel covers: whole groups of eight lanes.
/// Returns how many lanes it did.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "neon,aes")]
fn butterfly_lanes_neon(top: &mut [F64], bot: &mut [F64], twiddle: u64) -> usize {
    let lanes = top.len() / 8 * 8;
    for (top, bot) in top
        .as_chunks_mut::<8>()
        .0
        .iter_mut()
        .zip(bot.as_chunks_mut::<8>().0.iter_mut())
    {
        butterfly_lanes_neon_8(top, bot, twiddle);
    }
    lanes
}

/// Eight F64 butterflies as four independent NEON lane-pair reductions.
/// Loading all four bottom vectors before reducing them gives the out-of-order
/// core four independent PMULL chains to schedule, while one call amortizes
/// loop control and the duplicated twiddle/reduction constants over 8 lanes.
///
/// `top` and `bot` are eight words each.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "neon,aes")]
fn butterfly_lanes_neon_8(top: &mut [F64], bot: &mut [F64], twiddle: u64) {
    use core::arch::aarch64::*;
    use primitives::field::gf2_64::aarch64::{pmull, pmull_hi, reduce_pair_pmull4};
    use primitives::{load_at, store_at};

    let v: [uint64x2_t; 4] = std::array::from_fn(|i| load_at(bot, 2 * i));
    let tw = vdupq_n_u64(twiddle);
    for i in 0..4 {
        // SAFETY: the function carries the aes target feature the helpers need.
        let prod = unsafe { reduce_pair_pmull4(pmull(vgetq_lane_u64::<0>(v[i]), twiddle), pmull_hi(v[i], tw)) };
        let new_u = veorq_u64(load_at(top, 2 * i), prod);
        store_at(top, 2 * i, new_u);
        store_at(bot, 2 * i, veorq_u64(v[i], new_u));
    }
}

/// `u ^ v * tw` in each of the eight 64-bit lanes of an AVX-512 register, for the two kernels below.
///
/// The even and odd lanes' products land one per 128-bit lane, and `reduce_halves512` reduces them with shifts,
/// three-way XORs and one in-lane lookup rather than two more carry-less multiplies, the scarce unit on Zen 5.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
fn mul_xor_avx512(
    u: core::arch::x86_64::__m512i,
    v: core::arch::x86_64::__m512i,
    tw: core::arch::x86_64::__m512i,
) -> core::arch::x86_64::__m512i {
    use core::arch::x86_64::*;
    use primitives::field::gf2_64x3::x86_64::reduce_halves512;

    let even = _mm512_clmulepi64_epi128::<0x00>(v, tw);
    let odd = _mm512_clmulepi64_epi128::<0x11>(v, tw);
    _mm512_xor_si512(u, reduce_halves512(even, odd))
}

/// The butterflies of a pair of equal-length rows with a shared twiddle, eight lanes per AVX-512 register.
///
/// The last register is masked to the row's end.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
fn butterfly_lanes_avx512(top: &mut [F64], bot: &mut [F64], twiddle: u64) {
    use core::arch::x86_64::*;
    use primitives::simd::xor;

    let tw = _mm512_set1_epi64(twiddle as i64);
    // Butterfly top: u' = u + v * t. Bottom: v' = v + u'.
    pair_lanes_avx512(
        top,
        bot,
        #[inline(always)]
        |u, v| {
            let new_u = mul_xor_avx512(u, v, tw);
            (new_u, xor(v, new_u))
        },
    );
}

/// Map `op(u, v)` over a pair of equal-length rows, eight lanes per AVX-512 register, and store its two results.
///
/// The last register is masked to the rows' end.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
fn pair_lanes_avx512(top: &mut [F64], bot: &mut [F64], op: impl Fn(__m512i, __m512i) -> (__m512i, __m512i)) {
    use primitives::simd::{load_prefix, store_prefix};

    let step = |top: &mut [F64], bot: &mut [F64], i: usize, n: usize| {
        let (new_top, new_bot) = op(load_prefix(top, i, n), load_prefix(bot, i, n));
        store_prefix(top, i, n, new_top);
        store_prefix(bot, i, n, new_bot);
    };
    let vectors = top.len() / 8;
    for i in 0..vectors {
        step(top, bot, i, 8);
    }
    let tail = top.len() - 8 * vectors;
    if tail > 0 {
        step(top, bot, vectors, tail);
    }
}

/// Eight-lane vectors of every row that a register kernel keeps in flight.
///
/// One vector's butterflies form a dependent chain, so a second vector covers its latency.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
const LANE_VECTORS: usize = 2;

/// A broadcast twiddle, and whether it is zero: the butterfly is then `v' = v + u`, with no product.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
type Twiddle = (core::arch::x86_64::__m512i, bool);

/// The vectors of `N` rows held in registers: `v[row][k]` is vector `k` of the row.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
type RowVectors<const N: usize> = [[core::arch::x86_64::__m512i; LANE_VECTORS]; N];

/// Butterfly rows `top` and `bot` of every vector in flight.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
fn butterfly_regs<const N: usize>(v: &mut RowVectors<N>, top: usize, bot: usize, (tw, zero): Twiddle) {
    for k in 0..LANE_VECTORS {
        let (u, w) = (v[top][k], v[bot][k]);
        let new_u = if zero { u } else { mul_xor_avx512(u, w, tw) };
        v[top][k] = new_u;
        v[bot][k] = primitives::simd::xor(w, new_u);
    }
}

/// Runs `kernel` on `N` equal-length rows held in registers, [`LANE_VECTORS`] eight-lane vectors of every row at a time.
///
/// - The vectors load from `src`, or from `rows` when there is none, and store to `rows`.
/// - A vector is loaded and stored once, however many butterflies `kernel` applies to it.
/// - The kernel orders its butterflies breadth-first, so the vectors in flight hide each other's latency.
/// - The last chunk may be short: its vectors past the row's end load as zeros and are not stored.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
fn fused_lanes_avx512<const N: usize, const T: usize>(
    src: Option<[&[F64]; N]>,
    rows: &mut [&mut [F64]; N],
    twiddles: &[F64; T],
    kernel: impl Fn(&mut RowVectors<N>, &[Twiddle; T]),
) {
    use core::arch::x86_64::*;
    use primitives::simd::{load, load_prefix, store, store_prefix};

    const CHUNK: usize = 8 * LANE_VECTORS;
    let len = rows[0].len();
    debug_assert!(rows.iter().all(|row| row.len() == len));
    debug_assert!(src.iter().flatten().all(|row| row.len() == len));
    let tw = twiddles.map(|t| (_mm512_set1_epi64(t.0 as i64), t == F64::ZERO));
    let mut lane = 0;
    while lane + CHUNK <= len {
        // The chunk of every row, as arrays: the loads and stores below need no bounds check of their own.
        let chunks: [&mut [F64; CHUNK]; N] = rows
            .each_mut()
            .map(|row| (&mut row[lane..lane + CHUNK]).try_into().unwrap());
        let mut v: RowVectors<N> = match &src {
            Some(src) => std::array::from_fn(|i| {
                let from: &[F64; CHUNK] = src[i][lane..lane + CHUNK].try_into().unwrap();
                std::array::from_fn(|k| load(from, k))
            }),
            None => std::array::from_fn(|i| std::array::from_fn(|k| load(&*chunks[i], k))),
        };
        kernel(&mut v, &tw);
        for i in 0..N {
            for k in 0..LANE_VECTORS {
                store(chunks[i], k, v[i][k]);
            }
        }
        lane += CHUNK;
    }
    if lane < len {
        let reg = lane / 8;
        // The lanes of vector `k` of the short chunk: all eight, the row's last few, or none.
        let n = |k: usize| len.saturating_sub(lane + 8 * k).min(8);
        let mut v: RowVectors<N> = std::array::from_fn(|i| {
            std::array::from_fn(|k| match &src {
                Some(src) => load_prefix(src[i], reg + k, n(k)),
                None => load_prefix(&*rows[i], reg + k, n(k)),
            })
        });
        kernel(&mut v, &tw);
        for i in 0..N {
            for k in 0..LANE_VECTORS {
                store_prefix(rows[i], reg + k, n(k), v[i][k]);
            }
        }
    }
}

/// [`butterfly_lanes_avx512`] transposed: `s = u + v; u' = s; v' = s * t + v`.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx512bw")]
fn transpose_butterfly_lanes_avx512(top: &mut [F64], bot: &mut [F64], twiddle: u64) {
    use core::arch::x86_64::*;
    use primitives::simd::xor;

    let tw = _mm512_set1_epi64(twiddle as i64);
    pair_lanes_avx512(
        top,
        bot,
        #[inline(always)]
        |u, v| {
            let s = xor(u, v);
            (s, mul_xor_avx512(v, s, tw))
        },
    );
}
