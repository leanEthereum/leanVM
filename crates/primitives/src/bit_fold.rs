//! Weighted sums of packed bit rows, the fold that turns witness bits into F192 values.
//!
//! A row is `8 * CHUNKS` bits and every bit carries a fixed F192 weight:
//!
//! ```text
//!     fold(row) = sum_{s : bit s of row is set} w_s
//! ```
//!
//! The map is GF(2)-linear in the row's bits, so it splits into one 8-bit piece per byte.
//!
//! - Portable: a 256-entry subset-sum table per byte, one lookup per byte.
//! - GFNI: an 8x8 bit matrix per (input byte, output byte), applied to 64 rows by one instruction.

use crate::field::F192;

/// Rows folded per call.
pub const BLOCK: usize = 64;

/// The weights of every bit of a row, prepared for folding.
#[derive(Clone, Debug)]
pub struct BitFold {
    /// Bytes per row.
    n_chunks: usize,
    /// The target's fold kernel data.
    imp: Imp,
}

impl BitFold {
    /// Prepare `weights`, one per bit of a row.
    ///
    /// # Panics
    ///
    /// Panics unless a row is 8, 16, 32, 64 or 128 bytes.
    pub fn new(weights: &[F192]) -> Self {
        let n_chunks = weights.len() / 8;
        assert!(
            weights.len() == 8 * n_chunks && n_chunks.is_power_of_two() && (8..=128).contains(&n_chunks),
            "a row is 8 to 128 bytes, a power of two"
        );
        Self {
            n_chunks,
            imp: Imp::new(weights),
        }
    }

    /// Fold up to 64 rows split in two runs of bytes: `self` weighs the `A` bytes of `head_rows`, `tail` the `B` of `tail_rows`.
    ///
    /// The sums are added before the output transpose, so a row of 24 bytes costs 24 input bytes, not 32.
    #[inline]
    pub fn fold_block_pair<const A: usize, const B: usize>(
        &self,
        tail: &Self,
        head_rows: &[[u8; A]],
        tail_rows: &[[u8; B]],
        out: &mut [F192; BLOCK],
    ) {
        debug_assert!(A == self.n_chunks && B == tail.n_chunks);
        assert!(head_rows.len() <= BLOCK && head_rows.len() == tail_rows.len());
        self.imp.fold_block_pair(&tail.imp, head_rows, tail_rows, out);
    }

    /// Fold 64 rows given as byte columns: `cols[j][p]` is byte `j` of row `p`.
    ///
    /// This is the form [`crate::bits::bit_transpose_64bytes`] leaves a block of words in, and the GFNI fold's own
    /// intermediate, so it skips the fold's input transpose.
    #[inline]
    pub fn fold_columns<const CHUNKS: usize>(&self, cols: &[[u8; BLOCK]; CHUNKS], out: &mut [F192; BLOCK]) {
        debug_assert_eq!(CHUNKS, self.n_chunks);
        self.imp.fold_columns(cols, out);
    }
}

#[cfg(any(
    test,
    not(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))
))]
/// One 256-entry subset-sum table per byte of a row: entry `[j][v]` sums the weights of the set bits of `v` at byte `j`.
fn lookup_tables(weights: &[F192]) -> Vec<[F192; 256]> {
    weights
        .as_chunks::<8>()
        .0
        .iter()
        .map(|w| {
            let mut sums = [F192::ZERO; 256];
            // Each entry adds its lowest set bit's weight to an entry already built.
            for v in 1..256usize {
                let low = v.isolate_lowest_one();
                sums[v] = sums[v ^ low] + w[low.trailing_zeros() as usize];
            }
            sums
        })
        .collect()
}

#[cfg(any(
    test,
    not(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))
))]
/// The fold of one row through the byte tables: one lookup and one XOR per byte.
#[inline(always)]
fn fold_row_lookup<const CHUNKS: usize>(tables: &[[F192; 256]], row: &[u8; CHUNKS]) -> F192 {
    let tables: &[[F192; 256]; CHUNKS] = tables.try_into().expect("one table per byte");
    row.iter()
        .zip(tables)
        .fold(F192::ZERO, |acc, (&v, sums)| acc + sums[usize::from(v)])
}

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
)))]
use portable::Imp;

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use gfni::Imp;

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
)))]
mod portable {
    use super::{BLOCK, F192, fold_row_lookup, lookup_tables};

    /// The byte tables.
    #[derive(Clone, Debug)]
    pub(super) struct Imp {
        /// One subset-sum table per byte of a row.
        tables: Vec<[F192; 256]>,
    }

    impl Imp {
        pub(super) fn new(weights: &[F192]) -> Self {
            Self {
                tables: lookup_tables(weights),
            }
        }

        #[inline]
        pub(super) fn fold_block_pair<const A: usize, const B: usize>(
            &self,
            tail: &Self,
            head_rows: &[[u8; A]],
            tail_rows: &[[u8; B]],
            out: &mut [F192; BLOCK],
        ) {
            for ((o, head), tail_row) in out.iter_mut().zip(head_rows).zip(tail_rows) {
                *o = fold_row_lookup(&self.tables, head) + fold_row_lookup(&tail.tables, tail_row);
            }
        }

        #[inline]
        pub(super) fn fold_columns<const CHUNKS: usize>(&self, cols: &[[u8; BLOCK]; CHUNKS], out: &mut [F192; BLOCK]) {
            for (p, o) in out.iter_mut().enumerate() {
                *o = cols
                    .iter()
                    .zip(&self.tables)
                    .fold(F192::ZERO, |acc, (col, sums)| acc + sums[usize::from(col[p])]);
            }
        }
    }
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
mod gfni {
    //! The GFNI fold of 64 rows at a time.
    //!
    //! ```text
    //!     1. transpose   64 rows x CHUNKS bytes  ->  CHUNKS registers, register j = byte j of the 64 rows
    //!     2. multiply    out byte o += A[j][o] * (register j), one affine instruction for all 64 rows
    //!     3. transpose   24 registers of output bytes  ->  64 F192 values
    //! ```
    //!
    //! Both transposes are butterflies of two-register byte permutes.
    //!
    //! A stage swaps one bit of the byte offset inside a register with one bit of the register index.

    use core::arch::x86_64::*;
    use std::mem::MaybeUninit;
    use std::sync::LazyLock;

    use super::{BLOCK, F192};
    use crate::simd::{self, from_words, xor};

    /// Bytes of an F192.
    pub const OUT_BYTES: usize = 24;

    /// One butterfly stage: registers `z` and `z | zbit` exchange bytes through two permutes.
    ///
    /// The register bit `zbit` is a call argument, so a caller's constant loop unrolls into registers.
    #[derive(Clone, Copy, Debug)]
    struct Stage {
        /// Byte sources of the low register of each pair; bit 6 picks the high one.
        lo: [u8; 64],
        /// Byte sources of the high register of each pair.
        hi: [u8; 64],
    }

    impl Stage {
        /// Swap byte-offset bit `fbit` with the register bit, then permute each output by `sigma`.
        ///
        /// Output offset `f` takes the byte the plain swap leaves at offset `sigma(f)`.
        fn swap(fbit: usize, sigma: impl Fn(usize) -> usize) -> Self {
            // The plain swap: a byte keeps its offset except bit `fbit`, which trades places with the register bit.
            let lo = |f: usize| if f & fbit == 0 { f } else { 64 | (f ^ fbit) };
            let hi = |f: usize| if f & fbit == 0 { f | fbit } else { 64 | f };
            Self {
                lo: std::array::from_fn(|f| lo(sigma(f)) as u8),
                hi: std::array::from_fn(|f| hi(sigma(f)) as u8),
            }
        }

        #[inline]
        #[target_feature(enable = "avx512f,avx512bw,avx512vbmi,gfni")]
        fn apply<const N: usize>(&self, zbit: usize, regs: &mut [__m512i; N]) {
            let (lo, hi) = (simd::load(&self.lo, 0), simd::load(&self.hi, 0));
            for z in (0..N).filter(|z| z & zbit == 0) {
                let (u, w) = (regs[z], regs[z | zbit]);
                regs[z] = _mm512_permutex2var_epi8(u, lo, w);
                regs[z | zbit] = _mm512_permutex2var_epi8(u, hi, w);
            }
        }
    }

    /// The input byte that register `r` holds after the input stages, for rows of `2^c` bytes: its bits are the
    /// register's bits from `c - 6` on, then those below.
    const fn byte_of_reg(c: usize, r: usize) -> usize {
        let skew = c.saturating_sub(6);
        (r >> skew) | ((r & ((1 << skew) - 1)) << (c - skew))
    }

    /// The value in qword `l` of output register `r`.
    const fn lane_value(r: usize, l: usize) -> usize {
        l | (r << 3)
    }

    /// Stages taking eight registers of one output coefficient, register = byte `o` and offset = value `p`, to qwords.
    ///
    /// Stage `s` swaps register bit `s` with the value bit that [`lane_value`] gives register bit `s`.
    /// The last stage then orders each register's offsets as qword = lane, byte = `o`.
    ///
    /// So register `r`, qword `l` is the coefficient of value `lane_value(r, l)`.
    static OUTPUT_STAGES: LazyLock<[Stage; 3]> = LazyLock::new(|| {
        [0, 1, 2].map(|s| {
            Stage::swap(lane_value(1 << s, 0), |f| {
                if s == 2 { lane_value(f & 7, f >> 3) } else { f }
            })
        })
    });

    /// The coefficient registers of 24 registers of output bytes, register `o` holding byte `o` of 64 values.
    ///
    /// Per coefficient, register `r` and qword `l` hold the coefficient of value `lane_value(r, l)`.
    #[inline(always)]
    fn coefficients(acc: &[__m512i; OUT_BYTES]) -> [[__m512i; 8]; 3] {
        let mut c: [[__m512i; 8]; 3] = std::array::from_fn(|i| std::array::from_fn(|o| acc[8 * i + o]));
        for (s, stage) in OUTPUT_STAGES.iter().enumerate() {
            // SAFETY: the module is compiled only with these target features enabled.
            c.iter_mut().for_each(|c| unsafe { stage.apply(1 << s, c) });
        }
        c
    }

    /// Store 24 registers of output bytes, register `o` holding byte `o` of 64 values, as those 64 values.
    ///
    /// # Safety
    ///
    /// The CPU must have the target features this function enables.
    #[inline]
    #[target_feature(enable = "avx512f,avx512bw,avx512vbmi,gfni")]
    pub fn store_f192(acc: &[__m512i; OUT_BYTES], out: &mut [F192; BLOCK]) {
        let [c0, c1, c2] = coefficients(acc);

        // Interleave the three coefficients of values 8k..8k+8 into 24 consecutive qwords.
        //
        //     zmm 0   c0 c1 c2 | c0 c1 c2 | c0 c1        values 0, 1, 2
        //     zmm 1   c2 | c0 c1 c2 | c0 c1 c2 | c0      values 2, 3, 4, 5
        //     zmm 2   c1 c2 | c0 c1 c2 | c0 c1 c2        values 5, 6, 7
        //
        // Indices 0..8 pick c0, 8..16 pick c1; the masked permute then drops c2 into its slots.
        let idx01 = [
            _mm512_setr_epi64(0, 8, 0, 1, 9, 0, 2, 10),
            _mm512_setr_epi64(0, 3, 11, 0, 4, 12, 0, 5),
            _mm512_setr_epi64(13, 0, 6, 14, 0, 7, 15, 0),
        ];
        let idx2 = [
            _mm512_setr_epi64(0, 0, 0, 0, 0, 1, 0, 0),
            _mm512_setr_epi64(2, 0, 0, 3, 0, 0, 4, 0),
            _mm512_setr_epi64(0, 5, 0, 0, 6, 0, 0, 7),
        ];
        let mask2: [__mmask8; 3] = [0b0010_0100, 0b0100_1001, 0b1001_0010];
        for (k, group) in out.as_chunks_mut::<8>().0.iter_mut().enumerate() {
            for i in 0..3 {
                let v = _mm512_permutex2var_epi64(c0[k], idx01[i], c1[k]);
                let v = _mm512_mask_permutexvar_epi64(v, mask2[i], idx2[i], c2[k]);
                simd::store(group, i, v);
            }
        }
    }

    /// Byte sources gathering byte `o` of eight weights into qword `o`, in reverse weight order.
    ///
    /// Output register `g`, qword `l`, byte `7 - s` takes byte `8g + l` of weight `s`, input byte `24 s + 8g + l`.
    ///
    /// Returns the two-register sources, the third-register sources, and the mask of bytes from the third.
    const fn gather_index(g: usize) -> ([u8; 64], [u8; 64], u64) {
        let (mut lo, mut hi, mut mask) = ([0u8; 64], [0u8; 64], 0u64);
        let mut p = 0;
        while p < 64 {
            let (l, s) = (p / 8, 7 - p % 8);
            let src = 24 * s + 8 * g + l;
            if src < 128 {
                lo[p] = src as u8;
            } else {
                hi[p] = (src - 128) as u8;
                mask |= 1 << p;
            }
            p += 1;
        }
        (lo, hi, mask)
    }

    /// The gathers of the three output registers.
    const GATHER: [([u8; 64], [u8; 64], u64); 3] = [gather_index(0), gather_index(1), gather_index(2)];

    /// The GFNI matrices of eight weights, one per output byte.
    ///
    /// Matrix `o` maps an input byte `x` to byte `o` of `sum_{s : bit s of x} w_s`.
    ///
    /// The affine instruction computes result bit `k` as the parity of `x` against matrix byte `7 - k`.
    /// So matrix byte `7 - k` has bit `s` set when bit `k` of byte `o` of `w_s` is set.
    ///
    /// ```text
    ///     1. gather     qword o  =  byte o of w_7, ..., w_0        (a byte transpose)
    ///     2. transpose  each qword as an 8x8 bit matrix           (an affine against the reversed identity)
    /// ```
    ///
    /// # Safety
    ///
    /// The CPU must have the target features this function enables.
    #[inline]
    #[target_feature(enable = "avx512f,avx512bw,avx512vbmi,gfni")]
    pub fn weight_matrices(w: &[F192; 8]) -> [u64; OUT_BYTES] {
        let v: [__m512i; 3] = std::array::from_fn(|i| simd::load(w, i));
        // Byte t of each qword is the unit vector 1 << (7 - t).
        let reversed_identity = _mm512_set1_epi64(0x0102_0408_1020_4080);
        let mut out = [0u64; OUT_BYTES];
        for (g, (lo, hi, mask)) in GATHER.iter().enumerate() {
            let q = _mm512_permutex2var_epi8(v[0], simd::load(lo, 0), v[1]);
            let q = _mm512_mask_permutexvar_epi8(q, *mask, simd::load(hi, 0), v[2]);
            simd::store(&mut out, g, _mm512_gf2p8affine_epi64_epi8::<0>(reversed_identity, q));
        }
        out
    }

    /// The stages `first..first + log2(TILE)` of the input transpose of `CHUNKS`-byte rows, one tile of `TILE` registers
    /// at a time: register `r` is read through `load` and written back to `regs`.
    ///
    /// A stage swaps offset bit `s` with register bit `s + skew`, so a group of stages exchanges within the tiles
    /// of registers that differ only in that group's register bits.
    #[inline(always)]
    fn stages<const CHUNKS: usize, const TILE: usize>(
        input: &[Stage],
        first: usize,
        load: impl Fn(usize) -> __m512i,
        dst: *mut __m512i,
    ) {
        let skew = CHUNKS.trailing_zeros().saturating_sub(6) as usize;
        let (low, bits) = (first + skew, TILE.trailing_zeros() as usize);
        for t in 0..CHUNKS / TILE {
            // The tile's register `k` is register `base | k << low`.
            let base = ((t >> low) << (low + bits)) | (t & ((1 << low) - 1));
            let mut tile: [__m512i; TILE] = std::array::from_fn(|k| load(base | k << low));
            for i in 0..bits {
                // SAFETY: the module is compiled only with these target features enabled.
                unsafe { input[first + i].apply(1 << i, &mut tile) };
            }
            for (k, r) in tile.into_iter().enumerate() {
                // SAFETY: every register index is below CHUNKS, and `dst` holds CHUNKS registers.
                unsafe { dst.add(base | k << low).write(r) };
            }
        }
    }

    /// Phase 2, from one register per input byte: every output byte accumulates one affine product per input register.
    ///
    /// With `PREFETCH`, `next` is the block that follows, and its cache lines load two per input register pair.
    /// The pass is affine-bound, so the next block's fetch hides behind it, where a burst before the pass stalled.
    #[inline]
    #[target_feature(enable = "avx512f,avx512bw,avx512vbmi,gfni")]
    fn accumulate_into<const N: usize, const PREFETCH: bool>(
        acc: &mut [__m512i; OUT_BYTES],
        regs: &[__m512i; N],
        matrices: &[[u64; OUT_BYTES]; N],
        next: *const u8,
    ) {
        for (i, (pair, m)) in regs
            .as_chunks::<2>()
            .0
            .iter()
            .zip(matrices.as_chunks::<2>().0)
            .enumerate()
        {
            if PREFETCH {
                // A prefetch past the end of the data is harmless.
                _mm_prefetch::<_MM_HINT_T0>(next.wrapping_add(128 * i).cast());
                _mm_prefetch::<_MM_HINT_T0>(next.wrapping_add(128 * i + 64).cast());
            }
            for o in 0..OUT_BYTES {
                let g0 = _mm512_gf2p8affine_epi64_epi8::<0>(pair[0], _mm512_set1_epi64(m[0][o] as i64));
                let g1 = _mm512_gf2p8affine_epi64_epi8::<0>(pair[1], _mm512_set1_epi64(m[1][o] as i64));
                acc[o] = _mm512_ternarylogic_epi64::<0x96>(acc[o], g0, g1);
            }
        }
    }

    /// Stages taking row-major rows of `2^c` bytes, 64 of them, to one register per input byte.
    fn input_stages(c: usize) -> Vec<Stage> {
        // Input address of a byte: bits 0..c are its byte j in the row, bits c..c+6 its row p.
        //
        //     in a register        offset = address bits 0..6     register = address bits 6..c+6
        //     after the stages     offset = p                     register = j, rotated when c > 6
        //
        // Stage s swaps offset bit s with register bit s + (c - 6 when c > 6).
        let n_stages = c.min(6);
        // Without a rotation, a short row leaves offset = (p high bits, then p low bits).
        let plain = |p: usize| {
            if c >= 6 {
                p
            } else {
                (p >> (6 - c)) | ((p & ((1 << (6 - c)) - 1)) << c)
            }
        };
        (0..n_stages)
            .map(|s| {
                let last = s + 1 == n_stages;
                Stage::swap(1 << s, |f| if last { plain(f) } else { f })
            })
            .collect()
    }

    /// The GFNI matrices and the input transpose.
    #[derive(Clone, Debug)]
    pub(super) struct Imp {
        /// `matrices[24 r + o]` maps register `r` of the input transpose to output byte `o`.
        matrices: Vec<u64>,
        /// Stages taking row-major bytes to one register per input byte.
        input: Vec<Stage>,
    }

    impl Imp {
        pub(super) fn new(weights: &[F192]) -> Self {
            let n_chunks = weights.len() / 8;
            let c = n_chunks.trailing_zeros() as usize;

            let bytes: &[[F192; 8]] = weights.as_chunks().0;
            // SAFETY: the module is compiled only with these target features enabled.
            let matrices = (0..n_chunks)
                .flat_map(|r| unsafe { weight_matrices(&bytes[byte_of_reg(c, r)]) })
                .collect();
            Self {
                matrices,
                input: input_stages(c),
            }
        }

        #[inline]
        pub(super) fn fold_block_pair<const A: usize, const B: usize>(
            &self,
            tail: &Self,
            head_rows: &[[u8; A]],
            tail_rows: &[[u8; B]],
            out: &mut [F192; BLOCK],
        ) {
            let (mut acc, tail_acc) = (self.accumulate_rows(head_rows), tail.accumulate_rows(tail_rows));
            acc.iter_mut().zip(&tail_acc).for_each(|(a, t)| *a = xor(*a, *t));
            // SAFETY: the module is compiled only with these target features enabled.
            unsafe { store_f192(&acc, out) };
        }

        /// Phases 1 and 2 of up to 64 rows: 24 registers of output bytes.
        #[inline(always)]
        fn accumulate_rows<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]]) -> [__m512i; OUT_BYTES] {
            // The block that follows, for the prefetch.
            let next = rows.as_ptr().wrapping_add(BLOCK).cast();
            // A short block folds from a zero-padded copy.
            if rows.len() < BLOCK {
                let mut padded = [[0u8; CHUNKS]; BLOCK];
                padded[..rows.len()].copy_from_slice(rows);
                return self.fold_full::<CHUNKS>(&padded, next);
            }
            self.fold_full::<CHUNKS>(rows.try_into().expect("a full block"), next)
        }

        #[inline(always)]
        fn fold_full<const CHUNKS: usize>(
            &self,
            rows: &[[u8; CHUNKS]; BLOCK],
            next: *const u8,
        ) -> [__m512i; OUT_BYTES] {
            // Every register is written below only when at least one stage runs.
            const { assert!(CHUNKS.is_power_of_two() && CHUNKS >= 8, "a row is 8 to 128 bytes") };
            // Phase 1: CHUNKS registers of 64 bytes, row-major, then one register per input byte.
            let mut regs = MaybeUninit::<[__m512i; CHUNKS]>::uninit();
            let dst = regs.as_mut_ptr().cast::<__m512i>();
            let c = CHUNKS.trailing_zeros() as usize;
            // Stages run in groups of up to three, each group on tiles of registers that stay in registers.
            // The first group reads the rows, the next ones the registers the previous group wrote.
            let mut from = rows.as_ptr().cast::<__m512i>();
            for first in (0..c.min(6)).step_by(3) {
                // SAFETY: `from` holds CHUNKS registers, the rows or what the previous group wrote.
                let load = |r: usize| unsafe { from.add(r).read_unaligned() };
                match c.min(6) - first {
                    1 => stages::<CHUNKS, 2>(&self.input, first, load, dst),
                    2 => stages::<CHUNKS, 4>(&self.input, first, load, dst),
                    _ => stages::<CHUNKS, 8>(&self.input, first, load, dst),
                }
                from = dst;
            }
            // SAFETY: the first group wrote every register.
            self.accumulate::<CHUNKS, true>(unsafe { regs.assume_init_ref() }, next)
        }

        #[inline]
        pub(super) fn fold_columns<const CHUNKS: usize>(&self, cols: &[[u8; BLOCK]; CHUNKS], out: &mut [F192; BLOCK]) {
            // SAFETY: the module is compiled only with these target features enabled.
            unsafe { store_f192(&self.fold_columns_full::<CHUNKS>(cols), out) }
        }

        #[inline]
        #[target_feature(enable = "avx512f,avx512bw,avx512vbmi,gfni")]
        fn fold_columns_full<const CHUNKS: usize>(&self, cols: &[[u8; BLOCK]; CHUNKS]) -> [__m512i; OUT_BYTES] {
            let c = CHUNKS.trailing_zeros() as usize;
            let regs: [__m512i; CHUNKS] = std::array::from_fn(|r| simd::load(&cols[byte_of_reg(c, r)], 0));
            self.accumulate::<CHUNKS, false>(&regs, std::ptr::null())
        }

        /// Phase 2 of the block, from one register per input byte: 24 registers of output bytes.
        ///
        /// With `PREFETCH`, `next` is the block that follows (see [`accumulate_into`]).
        #[inline(always)]
        fn accumulate<const CHUNKS: usize, const PREFETCH: bool>(
            &self,
            regs: &[__m512i; CHUNKS],
            next: *const u8,
        ) -> [__m512i; OUT_BYTES] {
            let mut acc = [from_words([0; 8]); OUT_BYTES];
            let matrices = self.matrices.as_chunks::<OUT_BYTES>().0;
            // SAFETY: the module is compiled only with these target features enabled.
            unsafe {
                accumulate_into::<CHUNKS, PREFETCH>(
                    &mut acc,
                    regs,
                    matrices.try_into().expect("a matrix per register"),
                    next,
                );
            }
            acc
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    /// Every row width against the byte-table fold, the rows given as byte columns.
    #[test]
    fn fold_columns_matches_lookup() {
        fn check<const CHUNKS: usize>(rng: &mut Rng) {
            let weights: Vec<F192> = (0..8 * CHUNKS).map(|_| rng.ext()).collect();
            let (fold, tables) = (BitFold::new(&weights), lookup_tables(&weights));
            let rows: Vec<[u8; CHUNKS]> = (0..BLOCK)
                .map(|_| std::array::from_fn(|_| rng.next_u64() as u8))
                .collect();
            let cols: [[u8; BLOCK]; CHUNKS] = std::array::from_fn(|j| std::array::from_fn(|p| rows[p][j]));
            let mut out = [F192::ZERO; BLOCK];
            fold.fold_columns(&cols, &mut out);
            for (p, row) in rows.iter().enumerate() {
                assert_eq!(out[p], fold_row_lookup(&tables, row), "CHUNKS={CHUNKS}, row {p}");
            }
        }
        let mut rng = Rng::new(0xB17_F01D);
        check::<8>(&mut rng);
        check::<16>(&mut rng);
        check::<32>(&mut rng);
        check::<64>(&mut rng);
        check::<128>(&mut rng);
    }

    /// Two runs of bytes against the byte-table folds of each, full and short blocks.
    #[test]
    fn fold_block_pair_matches_lookup() {
        let mut rng = Rng::new(0x0009_A12B);
        let weights: Vec<F192> = (0..192).map(|_| rng.ext()).collect();
        let (head, tail) = (BitFold::new(&weights[..128]), BitFold::new(&weights[128..]));
        let (head_tables, tail_tables) = (lookup_tables(&weights[..128]), lookup_tables(&weights[128..]));
        for len in [BLOCK, 5] {
            let head_rows: Vec<[u8; 16]> = (0..len)
                .map(|_| std::array::from_fn(|_| rng.next_u64() as u8))
                .collect();
            let tail_rows: Vec<[u8; 8]> = (0..len)
                .map(|_| std::array::from_fn(|_| rng.next_u64() as u8))
                .collect();
            let mut out = [F192::ZERO; BLOCK];
            head.fold_block_pair(&tail, &head_rows, &tail_rows, &mut out);
            for p in 0..len {
                let want = fold_row_lookup(&head_tables, &head_rows[p]) + fold_row_lookup(&tail_tables, &tail_rows[p]);
                assert_eq!(out[p], want, "len={len}, row {p}");
            }
        }
    }

    /// The byte tables against the definition: the sum of the weights of the set bits.
    #[test]
    fn lookup_matches_definition() {
        let mut rng = Rng::new(0x5E7_B175);
        let weights: Vec<F192> = (0..64).map(|_| rng.ext()).collect();
        let tables = lookup_tables(&weights);
        for _ in 0..64 {
            let row: [u8; 8] = std::array::from_fn(|_| rng.next_u64() as u8);
            // Bit s of the row is bit s % 8 of byte s / 8.
            let direct = (0..64)
                .filter(|s| (row[s / 8] >> (s % 8)) & 1 == 1)
                .fold(F192::ZERO, |acc, s| acc + weights[s]);
            assert_eq!(fold_row_lookup(&tables, &row), direct, "row={row:02x?}");
        }
    }
}
