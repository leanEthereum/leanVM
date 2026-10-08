//! The partial fold of the witness at the outer half of the claim point.
//!
//! ```text
//!     out[i] = sum_o eq_outer[o] * z_o[i]        o an instance, i a bit of it
//! ```
//!
//! The eight bits of instances `8s .. 8s + 8` at position `i` form one byte, the stripe byte `(s, i)`.
//! The fold is GF(2)-linear in each stripe byte, with the eight eq weights of its instances:
//!
//! ```text
//!     out[i] = sum_s  sum_{r : bit r of stripe byte (s, i)}  eq_outer[8s + r]
//! ```
//!
//! So every kernel maps stripe bytes through a 256-entry sum table or a GFNI matrix per output byte.
//!
//! The witness is stored instance-major, so stripe bytes are transposed from it on the fly, 64 positions at a time.
//! No second copy of the witness exists.

use primitives::bits::bit_transpose_64bytes;
use primitives::field::F192;

/// The instance-major witness, read as stripes of eight instances.
#[derive(Clone, Copy, Debug)]
pub(super) struct Stripes<'a> {
    /// The witness, `words` packed words per instance.
    z: &'a [u64],
    /// Packed words per instance.
    words: usize,
}

impl<'a> Stripes<'a> {
    /// The stripes of `z`, whose instances are `2^k_log` bits each.
    ///
    /// # Panics
    ///
    /// - When an instance is not whole words.
    /// - When the instances do not tile whole stripes.
    pub(super) fn new(z: &'a [u64], k_log: usize) -> Self {
        assert!(k_log >= 6, "an instance is whole words");
        let words = 1 << (k_log - 6);
        assert!(
            z.len().is_multiple_of(8 * words),
            "the instances tile whole stripes of eight"
        );
        Self { z, words }
    }

    /// Stripes, one per eight instances.
    const fn len(&self) -> usize {
        self.z.len() / (8 * self.words)
    }

    /// Positions per instance.
    const fn positions(&self) -> usize {
        64 * self.words
    }

    /// The eight instances' words `g`, word `r` being instance `8s + r`'s.
    #[inline(always)]
    fn rows(&self, s: usize, g: usize) -> [u64; 8] {
        let first = 8 * s * self.words + g;
        std::array::from_fn(|r| self.z[first + r * self.words])
    }

    /// Stripe `s`'s bytes at positions `64g .. 64g + 64`.
    ///
    /// ```text
    ///     byte i, bit r  =  bit 64g + i of instance 8s + r
    /// ```
    #[inline(always)]
    fn bytes(&self, s: usize, g: usize) -> [u8; 64] {
        let rows = self.rows(s, g).map(u64::to_le_bytes);
        let mut out = [0u8; 64];
        bit_transpose_64bytes(rows.as_flattened().try_into().expect("eight words"), &mut out);
        out
    }
}

/// The eq-weighted sum over instances of every position of the witness.
///
/// - `z` is instance-major, `2^k_log` bits per instance.
/// - `eq_outer` holds one weight per instance.
/// - Positions from `useful_bits` on are zero in every instance, so they fold to zero unread.
///
/// # Panics
///
/// When there is not one weight per instance.
pub(super) fn partial_fold(z: &[u64], k_log: usize, useful_bits: usize, eq_outer: &[F192]) -> Vec<F192> {
    let stripes = Stripes::new(z, k_log);
    assert_eq!(eq_outer.len(), 8 * stripes.len(), "one weight per instance");
    assert!(useful_bits <= stripes.positions());
    // Groups of 64 positions holding a useful bit; a group straddling the boundary folds its zeros harmlessly.
    let groups = useful_bits.div_ceil(64);
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))]
    if stripes.len().is_multiple_of(gfni::TILE) {
        return gfni::partial_fold(stripes, groups, eq_outer);
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        not(all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"))
    ))]
    if stripes.len().is_multiple_of(avx2::TILE) {
        return avx2::partial_fold::<primitives::bit_fold::avx2::Best>(stripes, groups, eq_outer);
    }
    #[cfg(target_arch = "aarch64")]
    if stripes.len().is_multiple_of(neon::TILE) {
        return neon::partial_fold(stripes, groups, eq_outer);
    }
    partial_fold_tables(stripes, groups, eq_outer)
}

/// The fold by 256-entry sum tables, one table per stripe: the portable kernel, and every target's for few stripes.
fn partial_fold_tables(stripes: Stripes<'_>, groups: usize, eq_outer: &[F192]) -> Vec<F192> {
    let k = stripes.positions();
    // Enough stripes per task to amortize its table, and enough tasks for every worker.
    let per_task = (stripes.len() / 256).max(1);
    parallel::fold_reduce(
        stripes.len().div_ceil(per_task),
        || vec![F192::ZERO; k],
        |acc, task| {
            let mut table = [F192::ZERO; 256];
            for s in task * per_task..((task + 1) * per_task).min(stripes.len()) {
                sum_table(
                    eq_outer[8 * s..8 * s + 8].try_into().expect("eight weights"),
                    &mut table,
                );
                for (g, acc) in acc.as_chunks_mut::<64>().0[..groups].iter_mut().enumerate() {
                    for (acc, byte) in acc.iter_mut().zip(stripes.bytes(s, g)) {
                        *acc += table[usize::from(byte)];
                    }
                }
            }
        },
        |mut x, y| {
            for (x, y) in x.iter_mut().zip(&y) {
                *x += *y;
            }
            x
        },
    )
}

/// The 256 subset sums of eight weights: `table[b] = sum_{r : bit r of b} eq8[r]`.
///
/// Each weight doubles the table built so far, one addition per entry.
#[inline]
fn sum_table(eq8: &[F192; 8], table: &mut [F192; 256]) {
    table[0] = F192::ZERO;
    for (i, &e) in eq8.iter().enumerate() {
        // Entries with bit `i` set are the entries below `2^i`, plus `e`.
        let (lo, hi) = table.split_at_mut(1 << i);
        for (h, &l) in hi[..lo.len()].iter_mut().zip(lo.iter()) {
            *h = l + e;
        }
    }
}

/// AVX-512 with GFNI: one register is 64 positions of a stripe, already byte-sliced.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
mod gfni {
    use core::arch::x86_64::*;

    use primitives::bit_fold::gfni::{OUT_BYTES, store_f192, weight_matrices};
    use primitives::bits::bit_transpose_zmm;
    use primitives::field::F192;

    use super::Stripes;

    /// Stripes whose matrices one sweep holds at once.
    pub(super) const TILE: usize = 8;

    /// One worker's byte-sliced sums: group `g`, register `o` is byte `o` of positions `64g .. 64g + 64`.
    type Accumulator = Vec<[__m512i; OUT_BYTES]>;

    /// The fold, a tile of stripes per task, every worker summing into its own byte-sliced accumulators.
    ///
    /// A stripe costs 24 affine products per 64 positions.
    pub(super) fn partial_fold(stripes: Stripes<'_>, groups: usize, eq_outer: &[F192]) -> Vec<F192> {
        let acc = parallel::map_reduce_with_state(
            stripes.len() / TILE,
            || (),
            // SAFETY: an all-zero bit pattern is a valid register value.
            || -> Accumulator { vec![unsafe { core::mem::zeroed() }; groups] },
            // SAFETY: the module is compiled only with these target features enabled.
            |(), acc, tile| unsafe { fold_tile(stripes, &eq_outer[8 * TILE * tile..][..8 * TILE], tile, acc) },
            // SAFETY: as above.
            |x, y| unsafe { merge(x, &y) },
        );
        let mut out = vec![F192::ZERO; stripes.positions()];
        for (acc, out) in acc.iter().zip(out.as_chunks_mut::<64>().0) {
            // SAFETY: as above.
            unsafe { store_f192(acc, out) };
        }
        out
    }

    #[target_feature(enable = "avx512f")]
    fn merge(mut x: Accumulator, y: &Accumulator) -> Accumulator {
        for (x, y) in x.iter_mut().flatten().zip(y.iter().flatten()) {
            *x = _mm512_xor_si512(*x, *y);
        }
        x
    }

    /// Stripe `s`'s bytes at positions `64g ..`, transposed in a register from the eight instances' words.
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512vbmi", enable = "gfni")]
    fn stripe(stripes: Stripes<'_>, s: usize, g: usize) -> __m512i {
        let [r0, r1, r2, r3, r4, r5, r6, r7] = stripes.rows(s, g).map(|w| w as i64);
        bit_transpose_zmm(_mm512_set_epi64(r7, r6, r5, r4, r3, r2, r1, r0))
    }

    /// Add one tile of stripes, its eight eq weights per stripe in `eq`.
    #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
    fn fold_tile(stripes: Stripes<'_>, eq: &[F192], tile: usize, acc: &mut Accumulator) {
        let eq: &[[F192; 8]] = eq.as_chunks().0;
        let matrices: [[u64; OUT_BYTES]; TILE] = std::array::from_fn(|t| weight_matrices(&eq[t]));
        for (g, acc) in acc.iter_mut().enumerate() {
            // The group's 24 sums stay in registers across the tile.
            let mut r = *acc;
            for (t, m) in matrices.iter().enumerate() {
                let x = stripe(stripes, TILE * tile + t, g);
                for (r, &m) in r.iter_mut().zip(m) {
                    *r = _mm512_xor_si512(*r, _mm512_gf2p8affine_epi64_epi8::<0>(x, _mm512_set1_epi64(m as i64)));
                }
            }
            *acc = r;
        }
    }
}

/// AVX2: the AVX-512 fold's shape, one register being 32 positions of a stripe.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(
    all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"),
    allow(dead_code)
)]
pub(super) mod avx2 {
    use core::arch::x86_64::*;

    use primitives::bit_fold::avx2::{self, HALF, OUT_BYTES, Product};
    use primitives::field::F192;

    use super::Stripes;

    /// Stripes whose maps one sweep holds at once.
    pub(crate) const TILE: usize = 8;

    /// One worker's byte-sliced sums: group `g`, half `h`, register `o` is byte `o` of 32 positions.
    type Accumulator = Vec<[[__m256i; OUT_BYTES]; 2]>;

    /// The fold with the product `P`, a tile of stripes per task.
    pub(crate) fn partial_fold<P: Product>(stripes: Stripes<'_>, groups: usize, eq_outer: &[F192]) -> Vec<F192> {
        let acc = parallel::map_reduce_with_state(
            stripes.len() / TILE,
            || (),
            // SAFETY: an all-zero bit pattern is a valid register value.
            || -> Accumulator { vec![unsafe { core::mem::zeroed() }; groups] },
            // SAFETY: the function is compiled only with AVX2 enabled.
            |(), acc, tile| unsafe { fold_tile::<P>(stripes, &eq_outer[8 * TILE * tile..][..8 * TILE], tile, acc) },
            |mut x, y| {
                for (x, y) in x.iter_mut().flatten().flatten().zip(y.iter().flatten().flatten()) {
                    // SAFETY: as above.
                    *x = unsafe { _mm256_xor_si256(*x, *y) };
                }
                x
            },
        );
        let mut out = vec![F192::ZERO; stripes.positions()];
        for (acc, out) in acc.iter().zip(out.as_chunks_mut::<64>().0) {
            for (acc, out) in acc.iter().zip(out.as_chunks_mut::<HALF>().0) {
                // SAFETY: as above.
                unsafe { avx2::store_f192(acc, out) };
            }
        }
        out
    }

    /// Add one tile of stripes, its eight eq weights per stripe in `eq`.
    #[target_feature(enable = "avx2")]
    fn fold_tile<P: Product>(stripes: Stripes<'_>, eq: &[F192], tile: usize, acc: &mut Accumulator) {
        let eq: &[[F192; 8]] = eq.as_chunks().0;
        let maps: [[P::Map; OUT_BYTES]; TILE] = std::array::from_fn(|t| P::maps(&eq[t]));
        for (g, acc) in acc.iter_mut().enumerate() {
            // The tile's stripe bytes of this group, transposed once and swept for every output byte.
            let bytes: [[u8; 64]; TILE] = std::array::from_fn(|t| stripes.bytes(TILE * tile + t, g));
            for (h, acc) in acc.iter_mut().enumerate() {
                // Eight output bytes at a time keep their accumulators in registers.
                for (o, acc) in acc.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                    let mut r = *acc;
                    for (bytes, m) in bytes.iter().zip(&maps) {
                        // SAFETY: half a stripe chunk is 32 bytes.
                        let x = unsafe { _mm256_loadu_si256(bytes[HALF * h..].as_ptr().cast()) };
                        avx2::accumulate8::<P>(&mut r, P::input(x), &m[8 * o..]);
                    }
                    *acc = r;
                }
            }
        }
    }
}

/// NEON: 256-entry sum tables, eight positions' accumulators held in registers across a tile of stripes.
#[cfg(target_arch = "aarch64")]
mod neon {
    use core::arch::aarch64::*;

    use primitives::field::F192;
    use primitives::field::neon::xor3_u64;

    use super::{Stripes, sum_table};

    /// Stripes swept per accumulator load.
    ///
    /// More re-stream the accumulators less often, but their tables must stay in L1.
    pub(super) const TILE: usize = 8;

    /// Positions whose accumulators one sweep keeps in registers.
    const BLOCK: usize = 8;

    /// The fold, a band of tiles per worker, each tile's tables built once.
    ///
    /// Workers sum into private partials, then the partials are added.
    pub(super) fn partial_fold(stripes: Stripes<'_>, groups: usize, eq_outer: &[F192]) -> Vec<F192> {
        let k = stripes.positions();
        let n_tiles = stripes.len() / TILE;
        let tiles_per_worker = n_tiles.div_ceil(parallel::num_threads());
        let n_workers = n_tiles.div_ceil(tiles_per_worker);

        let mut partials = vec![F192::ZERO; n_workers * k];
        parallel::chunks_mut(&mut partials, k, |w, partial| {
            let mut tables = [[F192::ZERO; 256]; TILE];
            for tile in w * tiles_per_worker..((w + 1) * tiles_per_worker).min(n_tiles) {
                for (t, table) in tables.iter_mut().enumerate() {
                    let s = TILE * tile + t;
                    sum_table(eq_outer[8 * s..8 * s + 8].try_into().expect("eight weights"), table);
                }
                for (g, out) in partial.as_chunks_mut::<64>().0[..groups].iter_mut().enumerate() {
                    let bytes: [[u8; 64]; TILE] = std::array::from_fn(|t| stripes.bytes(TILE * tile + t, g));
                    for (b, out) in out.as_chunks_mut::<BLOCK>().0.iter_mut().enumerate() {
                        // SAFETY: NEON is always present on aarch64.
                        unsafe { sweep(&bytes, BLOCK * b, &tables, out) };
                    }
                }
            }
        });

        // Add the partials, parallel over positions and sequential over workers.
        let (first, rest) = partials.split_at(k);
        let mut out = first.to_vec();
        let chunk = parallel::recommended_chunk_size(k);
        for partial in rest.chunks(k) {
            parallel::chunks_mut_zip(&mut out, partial, chunk, |_, o, p| {
                for (o, p) in o.iter_mut().zip(p) {
                    *o += *p;
                }
            });
        }
        out
    }

    /// Add a tile's table lookups at positions `at .. at + 8` of each stripe chunk to `out`.
    ///
    /// Stripes are swept in pairs, so each accumulator folds two lookups with one three-way XOR.
    #[inline]
    #[target_feature(enable = "neon")]
    fn sweep(bytes: &[[u8; 64]; TILE], at: usize, tables: &[[F192; 256]; TILE], out: &mut [F192; BLOCK]) {
        // The low two coefficients ride one vector register, the third a scalar.
        // SAFETY: the first two coefficients of an element are adjacent words.
        let low = |e: &F192| unsafe { vld1q_u64(&e.c0) };
        let mut acc01: [uint64x2_t; BLOCK] = out.each_ref().map(low);
        let mut acc2: [u64; BLOCK] = out.each_ref().map(|e| e.c2);
        for (pair, tables) in bytes.as_chunks::<2>().0.iter().zip(tables.as_chunks::<2>().0) {
            for i in 0..BLOCK {
                let e0 = &tables[0][usize::from(pair[0][at + i])];
                let e1 = &tables[1][usize::from(pair[1][at + i])];
                // SAFETY: the three-way XOR's target features are those the crate is built with.
                acc01[i] = unsafe { xor3_u64(acc01[i], low(e0), low(e1)) };
                acc2[i] ^= e0.c2 ^ e1.c2;
            }
        }
        for ((out, acc01), acc2) in out.iter_mut().zip(acc01).zip(acc2) {
            // SAFETY: as above.
            unsafe { vst1q_u64(&mut out.c0, acc01) };
            out.c2 = acc2;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::eq_table;
    use primitives::test_util::Rng;

    /// The definition, bit by bit: `out[i] = sum_o eq_outer[o] * z_o[i]`.
    fn reference(z: &[u64], k_log: usize, eq_outer: &[F192]) -> Vec<F192> {
        // Every set bit adds its instance's weight to its position.
        let k = 1usize << k_log;
        let mut out = vec![F192::ZERO; k];
        for (o, &eq) in eq_outer.iter().enumerate() {
            for (i, out) in out.iter_mut().enumerate() {
                let bit = o * k + i;
                if z[bit / 64] >> (bit % 64) & 1 == 1 {
                    *out += eq;
                }
            }
        }
        out
    }

    /// A random witness of `2^n_log` instances, zero from `useful` on in each.
    fn witness(rng: &mut Rng, k_log: usize, n_log: usize, useful: usize) -> Vec<u64> {
        let words = 1usize << (k_log - 6);
        let mut z: Vec<u64> = (0..words << n_log).map(|_| rng.next_u64()).collect();
        for instance in z.chunks_exact_mut(words) {
            for (w, word) in instance.iter_mut().enumerate() {
                // Keep the bits below `useful` of this word.
                let keep = useful.saturating_sub(64 * w).min(64);
                *word &= u64::MAX.checked_shr(64 - keep as u32).unwrap_or(0);
            }
        }
        z
    }

    #[test]
    fn every_kernel_is_the_definition() {
        // Invariant: each kernel computes the eq-weighted sum over instances, dense and padded.
        //
        // Fixture state, (k_log, n_log, useful):
        //
        //     n_log 3, 5        one or four stripes: the table kernel on every target
        //     n_log 6..         whole tiles: the SIMD kernels
        //     useful < 2^k_log  a group straddling the boundary, and groups never read
        let cases = [
            (6, 3, 64),
            (7, 5, 100),
            (6, 6, 64),
            (8, 7, 256),
            (10, 8, 597),
            (14, 6, 16_000),
            (12, 9, 2_336),
        ];
        let mut rng = Rng::new(0xF01D);
        for (k_log, n_log, useful) in cases {
            let z = witness(&mut rng, k_log, n_log, useful);
            let eq = eq_table(&rng.ext_vec(n_log));
            let want = reference(&z, k_log, &eq);
            let stripes = Stripes::new(&z, k_log);
            let groups = useful.div_ceil(64);

            // The dispatched kernel, then each kernel this target compiles.
            assert_eq!(
                partial_fold(&z, k_log, useful, &eq),
                want,
                "dispatch, {k_log} {n_log} {useful}"
            );
            assert_eq!(
                partial_fold_tables(stripes, groups, &eq),
                want,
                "tables, {k_log} {n_log} {useful}"
            );
            if n_log < 6 {
                continue;
            }
            #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
            {
                use primitives::bit_fold::avx2::Shuffle;
                assert_eq!(
                    avx2::partial_fold::<Shuffle>(stripes, groups, &eq),
                    want,
                    "avx2 shuffle"
                );
                #[cfg(target_feature = "gfni")]
                {
                    use primitives::bit_fold::avx2::Gfni;
                    assert_eq!(avx2::partial_fold::<Gfni>(stripes, groups, &eq), want, "avx2 gfni");
                }
            }
            #[cfg(all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"))]
            assert_eq!(gfni::partial_fold(stripes, groups, &eq), want, "avx-512 gfni");
            #[cfg(target_arch = "aarch64")]
            assert_eq!(neon::partial_fold(stripes, groups, &eq), want, "neon");
        }
    }

    #[test]
    fn stripe_bytes_are_eight_instances_bits() {
        // Invariant: stripe byte (s, i), bit r is bit i of instance 8s + r.
        let mut rng = Rng::new(0x57_819E);
        let (k_log, n_log) = (7, 4);
        let z = witness(&mut rng, k_log, n_log, 1 << k_log);
        let stripes = Stripes::new(&z, k_log);
        for s in 0..stripes.len() {
            for g in 0..2 {
                for (i, byte) in stripes.bytes(s, g).into_iter().enumerate() {
                    for r in 0..8 {
                        let bit = ((8 * s + r) << k_log) + 64 * g + i;
                        assert_eq!(
                            byte >> r & 1,
                            (z[bit / 64] >> (bit % 64) & 1) as u8,
                            "s={s} g={g} i={i} r={r}"
                        );
                    }
                }
            }
        }
    }
}
