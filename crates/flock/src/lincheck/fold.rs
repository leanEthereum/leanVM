//! The partial fold of the packed witness at the outer half of the claim point, one kernel per target.

use primitives::PrimeCharacteristicRing;

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use core::arch::x86_64::*;
#[cfg(target_arch = "aarch64")]
use primitives::F64;
use primitives::F192;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use primitives::bit_fold::avx2;
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use primitives::bit_fold::gfni::{OUT_BYTES, store_f192, weight_matrices};
#[cfg(target_arch = "aarch64")]
use std::arch::aarch64::*;

/// Padding-aware variant of `partial_fold_packed_z_fast`. Skips rows
/// `i_inner ∈ [useful_bits, k)`, since those rows hold zero in every block of an
/// honestly padded witness, so the fold over the outer dim is zero. Output
/// is byte-identical to the dense path on such witnesses.
pub(super) fn partial_fold_packed_z_fast_padded(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> Vec<F192> {
    let n_log = m - k_log;
    let k = 1usize << k_log;
    let n_outer = 1usize << n_log;
    assert_eq!(z_packed.len(), (1usize << m) / 8);
    assert_eq!(eq_outer.len(), n_outer);
    assert!(n_log >= 3, "need n_outer ≥ 8 for byte stripes");
    assert!(useful_bits <= k);
    let n_stripes = n_outer / 8;

    let stripes_per_chunk = (n_stripes / 256).max(1);
    let bytes_per_chunk = stripes_per_chunk * k;

    // Keep one length-k accumulator per worker rather than per chunk.
    let n_chunks = z_packed.len().div_ceil(bytes_per_chunk);
    parallel::fold_reduce(
        n_chunks,
        || vec![F192::ZERO; k],
        |acc, chunk_idx| {
            let lo = chunk_idx * bytes_per_chunk;
            let chunk_bytes = &z_packed[lo..(lo + bytes_per_chunk).min(z_packed.len())];
            let stripe_start = chunk_idx * stripes_per_chunk;
            let mut table = vec![F192::ZERO; 256];
            for (rel_stripe, stripe) in chunk_bytes.chunks(k).enumerate() {
                let byte_idx = stripe_start + rel_stripe;
                build_sum_table(&eq_outer[8 * byte_idx..8 * byte_idx + 8], &mut table);
                for (i_inner, &z_byte) in stripe[..useful_bits].iter().enumerate() {
                    acc[i_inner] += table[z_byte as usize];
                }
            }
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(b.iter()) {
                *x += *y;
            }
            a
        },
    )
}

/// Stripes swept per accumulator touch in the NEON tiled partial fold.
/// Larger values re-stream the accumulator less often but grow the tables that must stay in L1.
pub(super) const NEON_TILE_T: usize = 8;

/// Single-matrix NEON inner kernel: sweep TILE_T=8 stripes of a stripe-tile
/// for one BLOCK_K=8 block of i_inner positions, keeping all 8 accumulators
/// in NEON Q-registers.
///
/// # Safety
/// - `tile_bytes_ptr` must point to at least `TILE_T * k` bytes.
/// - `tables_ptr` must point to at least `TILE_T * 256` F192 entries.
/// - `out_ptr` must point to at least 8 F192 entries of mutable storage.
#[cfg(target_arch = "aarch64")]
#[inline(never)]
#[allow(unsafe_op_in_unsafe_fn)]
unsafe fn process_block_neon_single(
    tile_bytes_ptr: *const u8,
    k: usize,
    bs: usize,
    tables_ptr: *const F192,
    out_ptr: *mut F192,
) {
    const TILE_T: usize = NEON_TILE_T;

    let mut acc01 = [vdupq_n_u64(0); 8];
    let mut acc2 = [0u64; 8];
    for i in 0..8 {
        let out = &*out_ptr.add(i);
        acc01[i] = vld1q_u64([out.coefficients()[0].to_bits(), out.coefficients()[1].to_bits()].as_ptr());
        acc2[i] = out.coefficients()[2].to_bits();
    }

    // The 8 z index bytes of a stripe are consecutive, so fetch them with one
    // unaligned 8-byte scalar load and shift them out of the register rather
    // than with eight LDRBs: the gather already issues a table load per index,
    // and a second load per index would nearly double this kernel's load-port
    // pressure for data that is already in a register.
    //
    // Stripes are swept in pairs so each vector accumulator folds both table
    // lookups with one EOR3, halving the accumulator updates and the serial
    // dependency chain through each of the 8 live accumulators. The `c2`
    // limbs are scalar, so they just take two XORs.
    let mut t = 0;
    while t + 1 < TILE_T {
        let ta0 = tables_ptr.add(t * 256);
        let ta1 = tables_ptr.add((t + 1) * 256);
        let w0 = (tile_bytes_ptr.add(t * k + bs) as *const u64).read_unaligned();
        let w1 = (tile_bytes_ptr.add((t + 1) * k + bs) as *const u64).read_unaligned();
        for i in 0..8 {
            let e0 = &*ta0.add(((w0 >> (8 * i)) & 0xff) as usize);
            let e1 = &*ta1.add(((w1 >> (8 * i)) & 0xff) as usize);
            acc01[i] = veorq_u64(
                acc01[i],
                veorq_u64(
                    vld1q_u64([e0.coefficients()[0].to_bits(), e0.coefficients()[1].to_bits()].as_ptr()),
                    vld1q_u64([e1.coefficients()[0].to_bits(), e1.coefficients()[1].to_bits()].as_ptr()),
                ),
            );
            acc2[i] ^= e0.coefficients()[2].to_bits() ^ e1.coefficients()[2].to_bits();
        }
        t += 2;
    }
    if t < TILE_T {
        let ta = tables_ptr.add(t * 256);
        let w = (tile_bytes_ptr.add(t * k + bs) as *const u64).read_unaligned();
        for i in 0..8 {
            let entry = &*ta.add(((w >> (8 * i)) & 0xff) as usize);
            acc01[i] = veorq_u64(
                acc01[i],
                vld1q_u64([entry.coefficients()[0].to_bits(), entry.coefficients()[1].to_bits()].as_ptr()),
            );
            acc2[i] ^= entry.coefficients()[2].to_bits();
        }
    }

    for i in 0..8 {
        let out = &mut *out_ptr.add(i);
        let mut limbs = [0u64; 2];
        vst1q_u64(limbs.as_mut_ptr(), acc01[i]);
        *out = F192::new([F64::new(limbs[0]), F64::new(limbs[1]), F64::new(acc2[i])]);
    }
}

/// Shared shape validation for the two tiled NEON folds. Returns
/// `(k, n_tiles, useful)`, where `useful` is `useful_bits` rounded up to a
/// `BLOCK_K` multiple: padded rows fold to zero, and a boundary block's padding
/// bytes are 0 ⇒ `table[0] = 0` ⇒ they contribute nothing.
#[cfg(target_arch = "aarch64")]
fn neon_fold_params(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> (usize, usize, usize) {
    const TILE_T: usize = NEON_TILE_T;
    const BLOCK_K: usize = 8;

    let n_log = m - k_log;
    let k = 1usize << k_log;
    let n_outer = 1usize << n_log;
    assert_eq!(z_packed.len(), (1usize << m) / 8);
    assert_eq!(eq_outer.len(), n_outer);
    assert!(
        n_log >= 3 + TILE_T.trailing_zeros() as usize,
        "need n_outer ≥ 8·TILE_T stripes"
    );
    assert!(k_log >= 3, "need k ≥ 8");
    assert!(useful_bits <= k);
    let n_stripes = n_outer / 8;
    assert_eq!(n_stripes % TILE_T, 0);
    assert_eq!(k % BLOCK_K, 0);
    let useful = (useful_bits.div_ceil(BLOCK_K) * BLOCK_K).min(k);
    (k, n_stripes / TILE_T, useful)
}

/// **i_inner-partitioned** NEON partial fold: parallelizes over the
/// **output** (`i_inner`) instead of over z stripes.
///
/// Workers own disjoint output slices, keeping one shared length-`k` accumulator and avoiding a final reduction. Each worker rebuilds the per-tile sum tables for its slice.
#[cfg(target_arch = "aarch64")]
pub(super) fn partial_fold_packed_z_iblock_padded(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> Vec<F192> {
    const TILE_T: usize = NEON_TILE_T;
    const BLOCK_K: usize = 8;

    let (k, n_tiles, useful) = neon_fold_params(z_packed, m, k_log, useful_bits, eq_outer);

    // Rows [useful, k) stay zero from the vec init.
    let mut out = vec![F192::ZERO; k];
    if useful == 0 {
        return out;
    }

    // Partition the useful i_inner range across workers. Each chunk independently
    // rebuilds the per-tile sum tables, so chunk count drives redundant table
    // work that does NOT scale with cores and dominates the residual at the
    // protocol's m. One chunk per worker minimizes that
    // redundancy; the pool's claim counter then rebalances a straggler (an
    // efficiency core, say) without needing extra chunks to steal from. Each
    // chunk is a BLOCK_K multiple.
    let p = parallel::num_threads();
    let i_chunk = (useful / p).max(BLOCK_K).next_multiple_of(BLOCK_K);

    parallel::chunks_mut(&mut out[..useful], i_chunk, |ci, out_slice| {
        let i_base = ci * i_chunk;
        let n_block = out_slice.len() / BLOCK_K;
        // Per-tile tables stay L1-resident.
        let mut tables = vec![F192::ZERO; TILE_T * 256];
        for tile in 0..n_tiles {
            let stripe_base = tile * TILE_T;
            for t in 0..TILE_T {
                let eq_off = 8 * (stripe_base + t);
                build_sum_table(&eq_outer[eq_off..eq_off + 8], &mut tables[t * 256..(t + 1) * 256]);
            }
            let tables_ptr = tables.as_ptr();
            // Base of this (tile, i_base): process_block reads
            // z_base[t·k + bs] = z[(stripe_base+t)·k + i_base + bs].
            // SAFETY: `z_packed` is `n_stripes * k` bytes, `stripe_base < n_stripes` and `i_base < k`.
            let z_base = unsafe { z_packed.as_ptr().add(stripe_base * k + i_base) };
            for b in 0..n_block {
                let i = b * BLOCK_K;
                // SAFETY: the tile's `TILE_T` stripes end by `n_stripes`, a multiple of `TILE_T`, and
                // `i_base + i + BLOCK_K <= useful <= k` keeps every 8-byte row read inside its stripe; `tables` is
                // `TILE_T * 256` entries; `i + BLOCK_K <= out_slice.len()`, both being multiples of `BLOCK_K`.
                unsafe {
                    process_block_neon_single(z_base, k, i, tables_ptr, out_slice.as_mut_ptr().add(i));
                }
            }
        }
    });
    out
}

/// Outer(tile)-partitioned sibling of [`partial_fold_packed_z_iblock_padded`]
/// with the same result, parallelized to remove the redundant per-worker sum-table
/// rebuilds that cap iblock's multicore scaling. **This is the default fold**
/// (`partial_fold_packed_z_best`).
///
/// iblock partitions the length-k **output** across workers, so every worker
/// rebuilds **all** `n_stripes` tile tables: table work is done `p`× and does not
/// shrink with cores, taking a large share of the multi-threaded wall. Here we
/// partition the **tiles** (outer/stripe dim): each worker owns a contiguous tile
/// band, builds each of its tile tables exactly **once**, folds them into a
/// private length-k partial, and the `p` partials are XOR-reduced at the end. The
/// partial is the full length-k output, while the register-tiled inner kernel keeps its accumulators in NEON registers. This trades reduction traffic for eliminating redundant table construction.
///
/// # Safety / preconditions: identical to the iblock kernel.
#[cfg(target_arch = "aarch64")]
pub(super) fn partial_fold_packed_z_oblock_padded(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> Vec<F192> {
    const TILE_T: usize = NEON_TILE_T;
    const BLOCK_K: usize = 8;

    let (k, n_tiles, useful) = neon_fold_params(z_packed, m, k_log, useful_bits, eq_outer);

    // Columns [useful, k) stay zero from the partial init.
    if useful == 0 {
        return vec![F192::ZERO; k];
    }

    // One private length-k partial per worker; workers own contiguous tile bands,
    // so each tile's sum-tables are built exactly once (not once per worker).
    let p = parallel::num_threads();
    let tiles_per_worker = n_tiles.div_ceil(p);
    let n_workers = n_tiles.div_ceil(tiles_per_worker); // ≤ p, every band non-empty

    let mut partials = vec![F192::ZERO; n_workers * k];
    parallel::chunks_mut(&mut partials, k, |w, partial| {
        let tile_lo = w * tiles_per_worker;
        let tile_hi = ((w + 1) * tiles_per_worker).min(n_tiles);
        // Build each tile's L1-resident tables once.
        let mut tables = vec![F192::ZERO; TILE_T * 256];
        for tile in tile_lo..tile_hi {
            let stripe_base = tile * TILE_T;
            for t in 0..TILE_T {
                let eq_off = 8 * (stripe_base + t);
                build_sum_table(&eq_outer[eq_off..eq_off + 8], &mut tables[t * 256..(t + 1) * 256]);
            }
            let tables_ptr = tables.as_ptr();
            // SAFETY: `z_packed` is `n_stripes * k` bytes and `stripe_base < n_stripes`.
            let z_base = unsafe { z_packed.as_ptr().add(stripe_base * k) };
            let mut bs = 0usize;
            while bs < useful {
                // SAFETY: the tile's `TILE_T` stripes end by `n_stripes`, a multiple of `TILE_T`;
                // `bs + BLOCK_K <= useful <= k` keeps every row read inside its stripe and the 8 outputs inside
                // the length-`k` partial; `tables` is `TILE_T * 256` entries.
                unsafe {
                    process_block_neon_single(z_base, k, bs, tables_ptr, partial.as_mut_ptr().add(bs));
                }
                bs += BLOCK_K;
            }
        }
    });

    // XOR-reduce the per-worker partials: parallel over columns, sequential over
    // workers so each partial is streamed once.
    let (first, rest) = partials.split_at(k);
    let mut out = first.to_vec();
    let col_chunk = parallel::recommended_chunk_size(k);
    for chunk in rest.chunks(k) {
        parallel::chunks_mut_zip(&mut out, chunk, col_chunk, |_, o, s| {
            for (o_i, s_i) in o.iter_mut().zip(s) {
                *o_i += *s_i;
            }
        });
    }
    out
}

/// Stripes whose maps one byte-sliced sweep holds at once.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
const SWEEP_TILE: usize = 8;

/// The partial fold with GFNI, outer-partitioned like the tiled fold.
///
/// Byte `i_inner` of a stripe carries eight outer bits, so the fold is GF(2)-linear per stripe:
///
/// ```text
///     out[i_inner] += sum_{r : bit r of z[stripe][i_inner]} eq_outer[8 stripe + r]
/// ```
///
/// One register is 64 consecutive `i_inner` of a stripe, already byte-sliced.
/// So a stripe costs 24 affine products per 64 outputs, into accumulators kept byte-sliced until the end.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
fn partial_fold_packed_z_gfni(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> Vec<F192> {
    let (k, n_stripes) = (1usize << k_log, 1usize << (m - k_log - 3));
    assert_eq!(z_packed.len(), n_stripes * k);
    assert_eq!(eq_outer.len(), 8 * n_stripes);
    assert!(
        k >= 64 && n_stripes.is_multiple_of(SWEEP_TILE),
        "whole registers and whole tiles"
    );
    // Rows past `useful_bits` are honest zeros; a group straddling the boundary folds them in harmlessly.
    let groups = useful_bits.div_ceil(64);

    // One byte-sliced accumulator per worker, one tile of stripes per task.
    let acc = parallel::map_reduce_with_state(
        n_stripes / SWEEP_TILE,
        || (),
        // SAFETY: an all-zero bit pattern is a valid register value.
        || vec![unsafe { core::mem::zeroed::<[__m512i; OUT_BYTES]>() }; groups],
        // SAFETY: the module is compiled only with these target features enabled.
        |(), acc, tile| unsafe {
            fold_tile(
                z_packed,
                k,
                &eq_outer[8 * SWEEP_TILE * tile..][..8 * SWEEP_TILE],
                tile,
                acc,
            );
        },
        |mut x, y| {
            for (x, y) in x.iter_mut().flatten().zip(y.iter().flatten()) {
                // SAFETY: as above.
                *x = unsafe { xor(*x, *y) };
            }
            x
        },
    );

    #[target_feature(enable = "avx512f")]
    fn xor(x: __m512i, y: __m512i) -> __m512i {
        _mm512_xor_si512(x, y)
    }

    #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
    fn fold_tile(z_packed: &[u8], k: usize, eq: &[F192], tile: usize, acc: &mut [[__m512i; OUT_BYTES]]) {
        let eq: &[[F192; 8]] = eq.as_chunks().0;
        let matrices: [[u64; OUT_BYTES]; SWEEP_TILE] = std::array::from_fn(|t| weight_matrices(&eq[t]));
        let first = tile * SWEEP_TILE;
        for (g, acc) in acc.iter_mut().enumerate() {
            let mut r = *acc;
            for (t, m) in matrices.iter().enumerate() {
                let row = &z_packed[(first + t) * k + 64 * g..][..64];
                // SAFETY: the row is 64 bytes.
                let x = unsafe { _mm512_loadu_si512(row.as_ptr().cast()) };
                for (r, &m) in r.iter_mut().zip(m) {
                    *r = _mm512_xor_si512(*r, _mm512_gf2p8affine_epi64_epi8::<0>(x, _mm512_set1_epi64(m as i64)));
                }
            }
            *acc = r;
        }
    }

    // Rows past the last group stay zero.
    let mut out = vec![F192::ZERO; k];
    for (acc, out) in acc.iter().zip(out.as_chunks_mut::<64>().0) {
        // SAFETY: as above.
        unsafe { store_f192(acc, out) };
    }
    out
}

/// The partial fold on AVX2: the AVX-512 fold's shape, one register being 32 consecutive `i_inner` of a stripe.
///
/// A group of 64 `i_inner` is two halves of 24 byte-sliced accumulators, each half swept eight output bytes at a time.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(
    all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"),
    allow(dead_code)
)]
pub(super) fn partial_fold_packed_z_avx2<P: avx2::Product>(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> Vec<F192> {
    let (k, n_stripes) = (1usize << k_log, 1usize << (m - k_log - 3));
    assert_eq!(z_packed.len(), n_stripes * k);
    assert_eq!(eq_outer.len(), 8 * n_stripes);
    assert!(
        k >= 64 && n_stripes.is_multiple_of(SWEEP_TILE),
        "whole registers and whole tiles"
    );
    // Rows past `useful_bits` are honest zeros; a group straddling the boundary folds them in harmlessly.
    let groups = useful_bits.div_ceil(64);

    // One byte-sliced accumulator per worker, one tile of stripes per task.
    let acc = parallel::map_reduce_with_state(
        n_stripes / SWEEP_TILE,
        || (),
        // SAFETY: an all-zero bit pattern is a valid register value.
        || vec![unsafe { core::mem::zeroed::<[[__m256i; avx2::OUT_BYTES]; 2]>() }; groups],
        // SAFETY: the function is compiled only with AVX2 enabled.
        |(), acc, tile| unsafe {
            fold_tile::<P>(
                z_packed,
                k,
                &eq_outer[8 * SWEEP_TILE * tile..][..8 * SWEEP_TILE],
                tile,
                acc,
            );
        },
        |mut x, y| {
            for (x, y) in x.iter_mut().flatten().flatten().zip(y.iter().flatten().flatten()) {
                // SAFETY: as above.
                *x = unsafe { _mm256_xor_si256(*x, *y) };
            }
            x
        },
    );

    #[target_feature(enable = "avx2")]
    fn fold_tile<P: avx2::Product>(
        z_packed: &[u8],
        k: usize,
        eq: &[F192],
        tile: usize,
        acc: &mut [[[__m256i; avx2::OUT_BYTES]; 2]],
    ) {
        let eq: &[[F192; 8]] = eq.as_chunks().0;
        let maps: [[P::Map; avx2::OUT_BYTES]; SWEEP_TILE] = std::array::from_fn(|t| P::maps(&eq[t]));
        let first = tile * SWEEP_TILE;
        for (g, acc) in acc.iter_mut().enumerate() {
            for (h, acc) in acc.iter_mut().enumerate() {
                // Eight output bytes at a time keep their accumulators in registers.
                for (o, acc) in acc.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                    let mut r = *acc;
                    for (t, m) in maps.iter().enumerate() {
                        let row = &z_packed[(first + t) * k + 64 * g + avx2::HALF * h..][..avx2::HALF];
                        // SAFETY: the row is 32 bytes.
                        let x = unsafe { _mm256_loadu_si256(row.as_ptr().cast()) };
                        avx2::accumulate8::<P>(&mut r, P::input(x), &m[8 * o..]);
                    }
                    *acc = r;
                }
            }
        }
    }

    // Rows past the last group stay zero.
    let mut out = vec![F192::ZERO; k];
    for (acc, out) in acc.iter().zip(out.as_chunks_mut::<64>().0) {
        for (acc, out) in acc.iter().zip(out.as_chunks_mut::<{ avx2::HALF }>().0) {
            // SAFETY: as above.
            unsafe { avx2::store_f192(acc, out) };
        }
    }
    out
}

/// Dispatch helper: pick the fastest single-matrix partial fold available
/// for the given (m, k_log). Threads `useful_bits` through so the kernel
/// can skip blocks past the useful region of each block (byte-identical to
/// the dense path on honestly-padded witnesses).
pub(super) fn partial_fold_packed_z_best(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> Vec<F192> {
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))]
    if k_log >= 6 && n_log_ok_for_tile(m, k_log, SWEEP_TILE) {
        return partial_fold_packed_z_gfni(z_packed, m, k_log, useful_bits, eq_outer);
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        not(all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"))
    ))]
    if k_log >= 6 && n_log_ok_for_tile(m, k_log, SWEEP_TILE) {
        return partial_fold_packed_z_avx2::<avx2::Best>(z_packed, m, k_log, useful_bits, eq_outer);
    }
    if n_log_ok_for_tile(m, k_log, NEON_TILE_T) {
        #[cfg(target_arch = "aarch64")]
        {
            // `oblock` avoids per-worker table construction but adds private partials and a reduction, so use it only above the tuned crossover.
            let n_log = m - k_log;
            if n_log >= OBLOCK_MIN_N_LOG {
                return partial_fold_packed_z_oblock_padded(z_packed, m, k_log, useful_bits, eq_outer);
            }
            partial_fold_packed_z_iblock_padded(z_packed, m, k_log, useful_bits, eq_outer)
        }
        #[cfg(not(target_arch = "aarch64"))]
        {
            partial_fold_packed_z_fast_padded(z_packed, m, k_log, useful_bits, eq_outer)
        }
    } else {
        partial_fold_packed_z_fast_padded(z_packed, m, k_log, useful_bits, eq_outer)
    }
}

/// Outer-dimension threshold (`n_log = m − k_log`) at/above which the
/// outer(tile)-partitioned fold beats the i_inner-partitioned one. See
/// [`partial_fold_packed_z_best`] for the crossover calibration.
#[cfg(target_arch = "aarch64")]
const OBLOCK_MIN_N_LOG: usize = 16;

/// Quick test for "can we use the tiled fast path?". Tile uses `TILE_T`
/// stripes; we need `n_stripes` divisible by TILE_T and enough outer dim.
pub(super) const fn n_log_ok_for_tile(m: usize, k_log: usize, tile_t: usize) -> bool {
    let n_log = m - k_log;
    if n_log < 3 + (tile_t.trailing_zeros() as usize) {
        return false;
    }
    let n_stripes = 1usize << (n_log - 3);
    n_stripes.is_multiple_of(tile_t)
}

/// Build a 256-entry sum table over 8 F192 values:
///   `table[b] = Σ_{r: bit r of b is set}  eq8[r]`
///
/// Doubling construction (255 XORs): for each new bit position `i ∈ 0..8`,
/// extend the table by XORing `eq8[i]` into each existing entry. This
/// avoids the naive 8·256 = 2048 operations.
#[inline]
fn build_sum_table(eq8: &[F192], table: &mut [F192]) {
    debug_assert_eq!(eq8.len(), 8);
    debug_assert_eq!(table.len(), 256);
    table[0] = F192::ZERO;
    for (i, &e) in eq8.iter().enumerate() {
        let len = 1usize << i;
        for j in 0..len {
            table[len + j] = table[j] + e;
        }
    }
}
