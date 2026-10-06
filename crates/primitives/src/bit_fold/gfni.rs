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
use std::sync::LazyLock;

use super::{BLOCK, F192};

/// Bytes of an F192.
pub const OUT_BYTES: usize = 24;

/// One butterfly stage: registers `z` and `z | zbit` exchange bytes through two permutes.
///
/// The caller passes `zbit` as a constant of its unrolled loop, so the registers never leave the register file.
#[derive(Clone, Copy, Debug)]
struct Stage {
    /// Byte sources of the low register of each pair; bit 6 picks the high one.
    lo: [u8; 64],
    /// Byte sources of the high register of each pair.
    hi: [u8; 64],
}

impl Stage {
    /// Swap byte-offset bit `fbit` with the register bit the stage is applied on, then permute each output by `sigma`.
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

    /// Exchange bytes between registers `z` and `z | zbit`, for every `z` with that bit clear.
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512vbmi")]
    fn apply<const N: usize>(&self, zbit: usize, regs: &mut [__m512i; N]) {
        // SAFETY: both index arrays are 64 bytes.
        let (lo, hi) = unsafe {
            (
                _mm512_loadu_si512(self.lo.as_ptr().cast()),
                _mm512_loadu_si512(self.hi.as_ptr().cast()),
            )
        };
        for k in 0..N / 2 {
            // Pair `k` with a zero inserted at bit `zbit`.
            let z = (k & (zbit - 1)) | ((k & !(zbit - 1)) << 1);
            let (u, w) = (regs[z], regs[z | zbit]);
            regs[z] = _mm512_permutex2var_epi8(u, lo, w);
            regs[z | zbit] = _mm512_permutex2var_epi8(u, hi, w);
        }
    }

    /// The stage undoing this one.
    fn inverse(&self) -> Self {
        let (mut lo, mut hi) = ([0u8; 64], [0u8; 64]);
        let mut place = |src: u8, pos: usize| {
            if src < 64 {
                lo[usize::from(src)] = pos as u8;
            } else {
                hi[usize::from(src) - 64] = pos as u8;
            }
        };
        for f in 0..64 {
            place(self.lo[f], f);
            place(self.hi[f], 64 | f);
        }
        Self { lo, hi }
    }
}

/// Stages taking eight registers of one output coefficient, register = byte `o` and offset = value `p`, to qwords.
///
/// Stage `s` pairs on register bit `s`.
///
/// ```text
///     after the stages     offset = (o, then p bits 0..3)     register = p bits 3..6
/// ```
///
/// So register `k`, qword `l` is the coefficient of value `8k + l`.
static OUTPUT_STAGES: LazyLock<[Stage; 3]> = LazyLock::new(|| {
    let to_qwords = |f: usize| (f >> 3) | ((f & 7) << 3);
    [0, 1, 2].map(|s| Stage::swap(8 << s, |f| if s == 2 { to_qwords(f) } else { f }))
});

/// [`OUTPUT_STAGES`] undone: eight registers of one coefficient's qwords back to one register per byte.
static INPUT_STAGES: LazyLock<[Stage; 3]> = LazyLock::new(|| {
    let [a, b, c] = &*OUTPUT_STAGES;
    [c.inverse(), b.inverse(), a.inverse()]
});

/// Stages taking eight registers of one output coefficient, register = byte `o` and offset = value `p`, to quad planes.
///
/// Stage `s` pairs on register bit `s`.
///
/// ```text
///     after the stages     offset = (o, then p bits 2..5)     register = p bits 0, 1, 5
/// ```
///
/// So register `u + 2v + 4g`, qword `l` is the coefficient of value `4 (8g + l) + u + 2v`: of quad `8g + l`, one register per `(u, v)`.
static QUAD_STAGES: LazyLock<[Stage; 3]> = LazyLock::new(|| {
    // The plain swaps leave offset = (o0, o1, p2, p3, p4, o2).
    let to_qwords = |f: usize| (f & 3) | ((f >> 3) << 2) | (((f >> 2) & 1) << 5);
    [Stage::swap(1, |f| f), Stage::swap(2, |f| f), Stage::swap(32, to_qwords)]
});

/// Store 24 registers of output bytes, register `o` holding byte `o` of 64 values, as those 64 values.
///
/// # Safety
///
/// The CPU must have the enabled target features.
#[inline]
#[target_feature(enable = "avx512f", enable = "avx512vbmi")]
pub fn store_f192(acc: &[__m512i; OUT_BYTES], out: &mut [F192; BLOCK]) {
    // Per coefficient, eight registers of output bytes become eight registers of qwords.
    let [mut c0, mut c1, mut c2] = [[_mm512_setzero_si512(); 8]; 3];
    for o in 0..8 {
        (c0[o], c1[o], c2[o]) = (acc[o], acc[8 + o], acc[16 + o]);
    }
    let stages = &*OUTPUT_STAGES;
    for (s, stage) in stages.iter().enumerate() {
        stage.apply(1 << s, &mut c0);
        stage.apply(1 << s, &mut c1);
        stage.apply(1 << s, &mut c2);
    }

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
    let dst = out.as_mut_ptr().cast::<u8>();
    for k in 0..8 {
        for i in 0..3 {
            let v = _mm512_permutex2var_epi64(c0[k], idx01[i], c1[k]);
            let v = _mm512_mask_permutexvar_epi64(v, mask2[i], idx2[i], c2[k]);
            // SAFETY: the three stores of value group k cover out[8k..8k+8], 192 bytes.
            unsafe { _mm512_storeu_si512(dst.add(192 * k + 64 * i).cast(), v) };
        }
    }
}

/// Qword sources splitting 24 consecutive qwords of eight values into coefficient `i` of each value.
///
/// Returns the two-register sources, the third-register sources, and the mask of lanes from the third.
const fn split_index(i: usize) -> ([i64; 8], [i64; 8], u8) {
    let (mut lo, mut hi, mut mask) = ([0i64; 8], [0i64; 8], 0u8);
    let mut l = 0;
    while l < 8 {
        let q = 3 * l + i;
        if q < 16 {
            lo[l] = q as i64;
        } else {
            hi[l] = (q - 16) as i64;
            mask |= 1 << l;
        }
        l += 1;
    }
    (lo, hi, mask)
}

const SPLIT: [([i64; 8], [i64; 8], u8); 3] = [split_index(0), split_index(1), split_index(2)];

/// Load 64 values as 24 registers of bytes, register `o` holding byte `o` of every value: [`store_f192`] undone.
#[inline]
#[target_feature(enable = "avx512f", enable = "avx512vbmi")]
fn load_f192(xs: &[F192; BLOCK]) -> [__m512i; OUT_BYTES] {
    let src = xs.as_ptr().cast::<u8>();
    // Coefficient `i` of values 8k..8k+8, one qword each.
    let split = |i: usize, k: usize| {
        let (lo, hi, mask) = &SPLIT[i];
        // SAFETY: values 8k..8k+8 are 192 bytes, three registers, and the index arrays are 64 bytes.
        unsafe {
            let v: [__m512i; 3] = std::array::from_fn(|r| _mm512_loadu_si512(src.add(192 * k + 64 * r).cast()));
            let q = _mm512_permutex2var_epi64(v[0], _mm512_loadu_si512(lo.as_ptr().cast()), v[1]);
            _mm512_mask_permutexvar_epi64(q, *mask, _mm512_loadu_si512(hi.as_ptr().cast()), v[2])
        }
    };
    let mut c: [[__m512i; 8]; 3] = std::array::from_fn(|i| std::array::from_fn(|k| split(i, k)));
    // The inverses run in reverse order, so stage `s` pairs on register bit `2 - s`.
    let stages = &*INPUT_STAGES;
    for (s, stage) in stages.iter().enumerate() {
        for coefficient in &mut c {
            stage.apply(4 >> s, coefficient);
        }
    }
    std::array::from_fn(|r| c[r / 8][r % 8])
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
/// The CPU must have the enabled target features.
#[inline]
#[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
pub fn weight_matrices(w: &[F192; 8]) -> [u64; OUT_BYTES] {
    let src = w.as_ptr().cast::<u8>();
    // SAFETY: eight weights are 192 bytes, exactly three registers.
    let v: [__m512i; 3] = std::array::from_fn(|i| unsafe { _mm512_loadu_si512(src.add(64 * i).cast()) });
    // Byte t of each qword is the unit vector 1 << (7 - t).
    let reversed_identity = _mm512_set1_epi64(0x0102_0408_1020_4080);
    let mut out = [0u64; OUT_BYTES];
    let dst = out.as_mut_ptr().cast::<u8>();
    for (g, (lo, hi, mask)) in GATHER.iter().enumerate() {
        // SAFETY: the index arrays are 64 bytes, and store g fills out[8g..8g+8].
        unsafe {
            let q = _mm512_permutex2var_epi8(v[0], _mm512_loadu_si512(lo.as_ptr().cast()), v[1]);
            let q = _mm512_mask_permutexvar_epi8(q, *mask, _mm512_loadu_si512(hi.as_ptr().cast()), v[2]);
            let a = _mm512_gf2p8affine_epi64_epi8::<0>(reversed_identity, q);
            _mm512_storeu_si512(dst.add(64 * g).cast(), a);
        }
    }
    out
}

/// A block of values, one register per byte.
pub(super) type Sliced = [__m512i; OUT_BYTES];

/// The GFNI matrices and the input transpose.
#[derive(Clone, Debug)]
pub(super) struct Imp {
    /// `matrices[24 r + o]` maps register `r` of the input transpose to output byte `o`.
    matrices: Vec<u64>,
    /// Stages taking row-major bytes to one register per input byte; stage `s` pairs on register bit `s + skew`.
    input: Vec<Stage>,
}

impl Imp {
    pub(super) fn new(weights: &[F192]) -> Self {
        let n_chunks = weights.len() / 8;
        let c = n_chunks.trailing_zeros() as usize;

        // Input address of a byte: bits 0..c are its byte j in the row, bits c..c+6 its row p.
        //
        //     in a register        offset = address bits 0..6     register = address bits 6..c+6
        //     after the stages     offset = p                     register = j, rotated when c > 6
        //
        // Stage s swaps offset bit s with register bit s + (c - 6 when c > 6).
        let n_stages = c.min(6);
        let skew = c.saturating_sub(6);
        // Without a rotation, a short row leaves offset = (p high bits, then p low bits).
        let plain = |p: usize| {
            if c >= 6 {
                p
            } else {
                (p >> (6 - c)) | ((p & ((1 << (6 - c)) - 1)) << c)
            }
        };
        let input = (0..n_stages)
            .map(|s| {
                let last = s + 1 == n_stages;
                Stage::swap(1 << s, |f| if last { plain(f) } else { f })
            })
            .collect();

        // Register `r` then holds input byte `j(r)`: its bits are register bits skew.. then 0..skew.
        let byte_of_reg = |r: usize| (r >> skew) | ((r & ((1 << skew) - 1)) << (c - skew));
        let bytes: &[[F192; 8]] = weights.as_chunks().0;
        // SAFETY: the module is compiled only with these target features enabled.
        let matrices = (0..n_chunks)
            .flat_map(|r| unsafe { weight_matrices(&bytes[byte_of_reg(r)]) })
            .collect();
        Self { matrices, input }
    }

    pub(super) fn new_f192(weights: &[F192]) -> Self {
        let bytes: &[[F192; 8]] = weights.as_chunks().0;
        // SAFETY: the module is compiled only with these target features enabled.
        let matrices = bytes.iter().flat_map(|b| unsafe { weight_matrices(b) }).collect();
        Self {
            matrices,
            input: Vec::new(),
        }
    }

    pub(super) fn slice(xs: &[F192; BLOCK]) -> Sliced {
        // SAFETY: the module is compiled only with these target features enabled.
        unsafe { load_f192(xs) }
    }

    #[inline]
    pub(super) fn apply_add_f192(&self, xs: &[F192; BLOCK], out: &mut [F192]) {
        self.apply_sliced_add(&Self::slice(xs), out);
    }

    #[inline]
    pub(super) fn apply_sliced_add(&self, regs: &Sliced, out: &mut [F192]) {
        let mut image = [F192::ZERO; BLOCK];
        // SAFETY: the module is compiled only with these target features enabled.
        unsafe { self.map_regs(regs, &mut image) };
        for (o, &y) in out.iter_mut().zip(&image) {
            *o += y;
        }
    }

    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
    fn map_regs(&self, regs: &Sliced, out: &mut [F192; BLOCK]) {
        let mut acc = [_mm512_setzero_si512(); OUT_BYTES];
        let matrices: &[[u64; OUT_BYTES]] = self.matrices.as_chunks().0;
        for (pair, m) in regs.as_chunks::<2>().0.iter().zip(matrices.as_chunks::<2>().0) {
            for o in 0..OUT_BYTES {
                let g0 = _mm512_gf2p8affine_epi64_epi8::<0>(pair[0], _mm512_set1_epi64(m[0][o] as i64));
                let g1 = _mm512_gf2p8affine_epi64_epi8::<0>(pair[1], _mm512_set1_epi64(m[1][o] as i64));
                acc[o] = _mm512_ternarylogic_epi64::<0x96>(acc[o], g0, g1);
            }
        }
        store_f192(&acc, out);
    }

    #[inline]
    pub(super) fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK]) {
        // A short block folds from a zero-padded copy.
        if rows.len() < BLOCK {
            let mut padded = [[0u8; CHUNKS]; BLOCK];
            padded[..rows.len()].copy_from_slice(rows);
            // SAFETY: the module is compiled only with these target features enabled.
            return unsafe { self.fold_full::<CHUNKS>(&padded, out) };
        }
        let rows: &[[u8; CHUNKS]; BLOCK] = rows.try_into().expect("a full block");
        // SAFETY: the module is compiled only with these target features enabled.
        unsafe { self.fold_full::<CHUNKS>(rows, out) };
    }

    /// Fold a full block into quad planes, see [`QUAD_STAGES`].
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
    pub(super) fn fold_quads<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK]) -> [[__m512i; 8]; 3] {
        let acc = self.fold_bytes::<CHUNKS>(rows);
        let mut planes = [[_mm512_setzero_si512(); 8]; 3];
        for (i, plane) in planes.iter_mut().enumerate() {
            plane.copy_from_slice(&acc[8 * i..8 * i + 8]);
        }
        let stages = &*QUAD_STAGES;
        for (s, stage) in stages.iter().enumerate() {
            for plane in &mut planes {
                stage.apply(1 << s, plane);
            }
        }
        planes
    }

    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
    fn fold_full<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK], out: &mut [F192; BLOCK]) {
        store_f192(&self.fold_bytes::<CHUNKS>(rows), out);
    }

    /// Fold a full block into 24 registers, register `o` holding byte `o` of the 64 values.
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
    fn fold_bytes<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK]) -> [__m512i; OUT_BYTES] {
        // Phase 1: CHUNKS registers of 64 bytes, row-major, then one register per input byte.
        let base = rows.as_ptr().cast::<u8>();
        let mut regs = [_mm512_setzero_si512(); CHUNKS];
        for (i, r) in regs.iter_mut().enumerate() {
            // SAFETY: the block is 64 * CHUNKS bytes, exactly CHUNKS registers.
            *r = unsafe { _mm512_loadu_si512(base.add(64 * i).cast()) };
        }
        // Up to three stages per pass over the registers, eight at a time, so a wide row is not
        // reloaded and stored for every stage when its registers outnumber the register file.
        let n_stages = CHUNKS.trailing_zeros().min(6) as usize;
        for first in (0..n_stages).step_by(3) {
            match n_stages - first {
                1 => self.input_stages::<2, CHUNKS>(first, &mut regs),
                2 => self.input_stages::<4, CHUNKS>(first, &mut regs),
                _ => self.input_stages::<8, CHUNKS>(first, &mut regs),
            }
        }

        // Phase 2: every output byte accumulates one affine product per input register.
        let mut acc = [_mm512_setzero_si512(); OUT_BYTES];
        let matrices: &[[u64; OUT_BYTES]] = self.matrices.as_chunks().0;
        for (pair, m) in regs.as_chunks::<2>().0.iter().zip(matrices.as_chunks::<2>().0) {
            for o in 0..OUT_BYTES {
                let g0 = _mm512_gf2p8affine_epi64_epi8::<0>(pair[0], _mm512_set1_epi64(m[0][o] as i64));
                let g1 = _mm512_gf2p8affine_epi64_epi8::<0>(pair[1], _mm512_set1_epi64(m[1][o] as i64));
                acc[o] = _mm512_ternarylogic_epi64::<0x96>(acc[o], g0, g1);
            }
        }
        acc
    }

    /// Input stages `first..first + log2(G)`, on each group of `G` registers they pair.
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512vbmi")]
    fn input_stages<const G: usize, const CHUNKS: usize>(&self, first: usize, regs: &mut [__m512i; CHUNKS]) {
        // Stage `s` pairs on register bit `s + skew`.
        let low = first + (CHUNKS.trailing_zeros() as usize).saturating_sub(6);
        let group_bits = (G - 1) << low;
        for base in (0..CHUNKS).filter(|r| r & group_bits == 0) {
            let mut group = [_mm512_setzero_si512(); G];
            for (k, g) in group.iter_mut().enumerate() {
                *g = regs[base | (k << low)];
            }
            for j in 0..G.trailing_zeros() as usize {
                self.input[first + j].apply(1 << j, &mut group);
            }
            for (k, g) in group.iter().enumerate() {
                regs[base | (k << low)] = *g;
            }
        }
    }
}
