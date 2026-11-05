//! The product polynomial's bit sums by GFNI outer products (x86-64 with AVX2 and GFNI): the
//! same values as [`crate::prover`]'s digit buckets, `sum over positions j of weights[j] (x)
//! product(q, j)` for every pack `q` of a block and every coefficient of its product.
//!
//! Eight consecutive `z` of one lane are a *lane byte*. For a lane byte's positions `j_0 .. j_7`
//! and one byte `b` of their weights, GF2P8AFFINEQB with the matrix `M_b` maps a *column byte*
//! (bit `k` = one coefficient of `product(q, j_k)`) to byte `b` of the sum of the weights of the
//! positions whose coefficient is set: the lane byte's share of that coefficient's sum. One
//! instruction does this for 32 (pack, coefficient) column bytes at once.
//!
//! Per block, two phases:
//! 1. per *row byte* with a nonzero weight (the same byte of the five lanes of a row, which `chi`
//!    mixes): the five lane bytes' embeddings, the products of each active lane byte, and their
//!    bit transposes into column bytes, staged register by register in a per-thread buffer;
//! 2. per staged register, every active lane byte's 24 matrices applied into accumulators held in
//!    registers (eight at a time on AVX2, all 24 with AVX-512), then one byte transpose back to
//!    field elements.
//!
//! The 8x8 byte transpose without VPERMB ([`transpose_bytes8x8`]) leaves the positions in a fixed
//! order ([`TRANSPOSED_ORDER`]), which the matrices absorb ([`COLUMN_BIT_POSITION`]).
//!
//! The two-phase outer-product scheme follows hashmancer-keccak's GFNI kernels; the code here is
//! written for this crate's layout (16-instance packs, 192-bit weights).

use core::arch::x86_64::*;

use primitives::field::F192;

use crate::keccak::BITS;
use crate::kernels::{PACKS, embed, products};
use crate::prover::PAYLOAD_BITS;
use crate::witness::words;

/// Staged registers per active lane byte: 32 column bytes each, six coefficient bytes per pack.
const STAGED: usize = PAYLOAD_BITS / 32;
/// Bytes of a weight.
const WEIGHT_BYTES: usize = 24;

type V = __m256i;

/// The GF2P8AFFINEQB source that turns the instruction into an 8x8 bit transpose of its matrix.
const BIT_TRANSPOSE: i64 = 0x8040_2010_0804_0201_u64 as i64;

/// The qword order [`transpose_bytes8x8`] leaves: output qword `d` byte `n` is byte `d` of input
/// `TRANSPOSED_ORDER[n]`.
const TRANSPOSED_ORDER: [usize; 8] = [0, 1, 4, 5, 2, 3, 6, 7];
/// The position that bit `i` of a column byte stands for, after the byte and bit transposes.
const COLUMN_BIT_POSITION: [usize; 8] = {
    let mut p = [0; 8];
    let mut i = 0;
    while i < 8 {
        p[i] = TRANSPOSED_ORDER[7 - i];
        i += 1;
    }
    p
};

/// In-lane byte interleave of the lane's two qwords (16-bit element `d` = byte `d` of both).
const INTERLEAVE: [u8; 32] = {
    let mut t = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        let j = i % 16;
        t[i] = if j % 2 == 0 { (j / 2) as u8 } else { (8 + j / 2) as u8 };
        i += 1;
    }
    t
};

/// 8x8 byte transpose of the qwords `a_0 .. a_7` (`p` = `a_0 .. a_3`, `q` = `a_4 .. a_7`): output
/// qword `d` (`d < 4` in the first register) byte `n` = byte `d` of `a_{TRANSPOSED_ORDER[n]}`. Two
/// in-lane byte shuffles, two 16-bit unpacks and two dword permutes.
///
/// # Safety
/// AVX2 (the module's build).
#[inline(always)]
unsafe fn transpose_bytes8x8(p: V, q: V) -> [V; 2] {
    unsafe {
        let il = _mm256_loadu_si256(INTERLEAVE.as_ptr().cast());
        let (p, q) = (_mm256_shuffle_epi8(p, il), _mm256_shuffle_epi8(q, il));
        // Dword d of lane 0: bytes d of (a0, a1, a4, a5); of lane 1: of (a2, a3, a6, a7).
        let (e, f) = (_mm256_unpacklo_epi16(p, q), _mm256_unpackhi_epi16(p, q));
        let idx = _mm256_setr_epi32(0, 4, 1, 5, 2, 6, 3, 7);
        [_mm256_permutevar8x32_epi32(e, idx), _mm256_permutevar8x32_epi32(f, idx)]
    }
}

/// 4x4 transpose of qwords: `out[i]` qword `k` = `r[k]` qword `i`.
///
/// # Safety
/// AVX2.
#[inline(always)]
unsafe fn transpose_qwords4x4(r: [V; 4]) -> [V; 4] {
    unsafe {
        let t0 = _mm256_unpacklo_epi64(r[0], r[1]);
        let t1 = _mm256_unpackhi_epi64(r[0], r[1]);
        let t2 = _mm256_unpacklo_epi64(r[2], r[3]);
        let t3 = _mm256_unpackhi_epi64(r[2], r[3]);
        [
            _mm256_permute2x128_si256(t0, t2, 0x20),
            _mm256_permute2x128_si256(t1, t3, 0x20),
            _mm256_permute2x128_si256(t0, t2, 0x31),
            _mm256_permute2x128_si256(t1, t3, 0x31),
        ]
    }
}

/// Where staged register `r` of active lane byte `a` lies in the buffer (`n_active` active lane
/// bytes). With AVX-512 the register pairs `2 R`, `2 R + 1` are adjacent, lane byte after lane byte,
/// so phase 2 reads a pair with one load; otherwise each register's lane bytes are contiguous.
#[inline(always)]
const fn staged_index(r: usize, a: usize, n_active: usize) -> usize {
    if cfg!(all(target_feature = "avx512f", target_feature = "avx512bw")) {
        2 * ((r / 2) * n_active + a) + r % 2
    } else {
        r * n_active + a
    }
}

/// Bit `n` of a weight.
#[inline(always)]
fn bit(w: F192, n: usize) -> u8 {
    ([w.c0, w.c1, w.c2][n / 64] >> (n % 64)) as u8 & 1
}

/// The 24 matrices of a lane byte's weights: `M_b` maps a column byte (bit `i` = position
/// `COLUMN_BIT_POSITION[i]`) to byte `b` of the sum of the weights it selects. An affine byte map
/// reads output bit `i` off matrix byte `7 - i`, whose bit `k` is then bit `8 b + i` of
/// `w[COLUMN_BIT_POSITION[k]]`.
fn lane_byte_matrices(w: &[F192]) -> [u64; WEIGHT_BYTES] {
    std::array::from_fn(|b| {
        (0..8).fold(0u64, |m, i| {
            let row = (0..8).fold(0u8, |row, k| row | bit(w[COLUMN_BIT_POSITION[k]], 8 * b + i) << k);
            m | (row as u64) << (8 * (7 - i))
        })
    })
}

/// One layer's product sums by outer products: the weights' matrices, in the order the blocks visit
/// the lane bytes.
pub struct ProductSums {
    /// Row bytes `(y, z / 8)` with a nonzero weight, and the mask of their active lanes `x`.
    row_bytes: Vec<(u8, u8, u8)>,
    /// The active lane bytes' matrices, in the order the row bytes visit them (`row_bytes`, then `x`).
    matrices: Vec<[u64; WEIGHT_BYTES]>,
}

/// A thread's buffers.
pub struct Scratch {
    /// The staged registers of a block, laid out by [`staged_index`].
    staged: Vec<V>,
    acc: Box<[[V; WEIGHT_BYTES]; STAGED]>,
    /// Per payload bit, its weighted sum's three words.
    pub out: Box<[[u64; 3]; PAYLOAD_BITS]>,
}

impl ProductSums {
    pub fn new(weights: &[F192]) -> Self {
        assert!(weights.len() >= BITS);
        let lane_bytes: Vec<Option<[u64; WEIGHT_BYTES]>> = (0..BITS / 8)
            .map(|o| {
                let w = &weights[8 * o..8 * o + 8];
                w.iter().any(|&x| x != F192::ZERO).then(|| lane_byte_matrices(w))
            })
            .collect();
        let mut row_bytes = Vec::new();
        let mut matrices = Vec::new();
        for y in 0..5usize {
            for zb in 0..8usize {
                let at = |x: usize| &lane_bytes[8 * (x + 5 * y) + zb];
                let mask = (0..5).fold(0u8, |m, x| m | u8::from(at(x).is_some()) << x);
                if mask != 0 {
                    row_bytes.push((y as u8, zb as u8, mask));
                    matrices.extend((0..5).filter_map(|x| *at(x)));
                }
            }
        }
        Self { row_bytes, matrices }
    }

    pub fn scratch(&self) -> Scratch {
        // SAFETY: AVX2 is enabled at compile time.
        let zero = unsafe { _mm256_setzero_si256() };
        Scratch {
            staged: vec![zero; STAGED * self.matrices.len()],
            acc: Box::new([[zero; WEIGHT_BYTES]; STAGED]),
            out: Box::new([[0; 3]; PAYLOAD_BITS]),
        }
    }

    /// The weighted bit sums of a block (`BITS` positions of eight words) into `s.out`: entry
    /// `48 q + c` is `sum over j of weights[j] * coefficient c of product(q, j)`.
    pub fn block_sums(&self, s: &mut Scratch, block: &[u64]) {
        let n_active = self.matrices.len();
        self.stage(block, &mut s.staged, n_active);
        self.accumulate(&s.staged, n_active, &mut s.acc);
        Self::to_field_elements(&s.acc, &mut s.out);
    }

    /// Phase 1: every active lane byte's column bytes into `staged[staged_index(r, a, n_active)]`.
    fn stage(&self, block: &[u64], staged: &mut [V], n_active: usize) {
        assert!(staged.len() >= STAGED * n_active);
        let mut embedded = [[[0u32; PACKS]; 8]; 5];
        let mut prod = [[0u64; PACKS]; 8];
        let mut a = 0;
        for &(y, zb, mask) in &self.row_bytes {
            let (y, zb) = (y as usize, zb as usize);
            for (x, lane) in embedded.iter_mut().enumerate() {
                for (k, e) in lane.iter_mut().enumerate() {
                    *e = embed(words(block, 64 * (x + 5 * y) + 8 * zb + k));
                }
            }
            for x in (0..5).filter(|x| mask >> x & 1 == 1) {
                let (e0, e1, e2) = (&embedded[x], &embedded[(x + 1) % 5], &embedded[(x + 2) % 5]);
                for (k, p) in prod.iter_mut().enumerate() {
                    *p = products(&e0[k], &e1[k], &e2[k]);
                }
                assert!(a < n_active, "one staged column per active lane byte");
                // SAFETY: AVX2 and GFNI are enabled at compile time; `a < n_active` (asserted) and
                // `stage_lane_byte` writes registers `r < STAGED` only (`3 * 15 + 2`), so every store
                // is inside `staged` (asserted size).
                unsafe { Self::stage_lane_byte(&prod, staged.as_mut_ptr(), a, n_active) };
                a += 1;
            }
        }
        // Phase 2 reads every active lane byte's registers: none may be left from another block.
        assert_eq!(a, n_active, "every active lane byte staged");
    }

    /// The column bytes of one lane byte's products (`prod[k][q]`: position `k`, pack `q`): register
    /// `r` holds column qwords `4 r .. 4 r + 4`, qword `6 q + m` being coefficient byte `m` of pack
    /// `q` (bit `i` of its byte `b`: coefficient `8 m + b` of position `COLUMN_BIT_POSITION[i]`).
    ///
    /// # Safety
    /// AVX2 and GFNI; `staged + staged_index(r, a, n_active)` writable for `r < STAGED`.
    #[inline(always)]
    unsafe fn stage_lane_byte(prod: &[[u64; PACKS]; 8], staged: *mut V, a: usize, n_active: usize) {
        unsafe {
            let bit_transpose = _mm256_set1_epi64x(BIT_TRANSPOSE);
            let ld = |k: usize, q: usize| _mm256_loadu_si256(prod[k].as_ptr().add(q).cast());
            for qq in (0..PACKS).step_by(4) {
                // t[h][i] qword k = the product of pack qq + i at position 4 h + k.
                let t = [
                    transpose_qwords4x4([ld(0, qq), ld(1, qq), ld(2, qq), ld(3, qq)]),
                    transpose_qwords4x4([ld(4, qq), ld(5, qq), ld(6, qq), ld(7, qq)]),
                ];
                let columns: [[V; 2]; 4] = std::array::from_fn(|i| {
                    let [lo, hi] = transpose_bytes8x8(t[0][i], t[1][i]);
                    [
                        _mm256_gf2p8affine_epi64_epi8(bit_transpose, lo, 0),
                        _mm256_gf2p8affine_epi64_epi8(bit_transpose, hi, 0),
                    ]
                });
                for pair in 0..2 {
                    // Packs q, q + 1 take three registers: bytes 0..4 of q; 4, 5 of q and 0, 1
                    // of q + 1; 2..4 and 4, 5 of q + 1.
                    let (c0, c1) = (columns[2 * pair], columns[2 * pair + 1]);
                    let r = 3 * ((qq + 2 * pair) / 2);
                    *staged.add(staged_index(r, a, n_active)) = c0[0];
                    *staged.add(staged_index(r + 1, a, n_active)) = _mm256_permute2x128_si256(c0[1], c1[0], 0x20);
                    *staged.add(staged_index(r + 2, a, n_active)) = _mm256_permute2x128_si256(c1[0], c1[1], 0x21);
                }
            }
        }
    }

    /// Phase 2: per staged register, every active lane byte through its 24 matrices, eight
    /// accumulators at a time in registers.
    #[cfg(not(all(target_feature = "avx512f", target_feature = "avx512bw")))]
    fn accumulate(&self, staged: &[V], n_active: usize, acc: &mut [[V; WEIGHT_BYTES]; STAGED]) {
        assert!(staged.len() >= STAGED * n_active);
        for (r, acc) in acc.iter_mut().enumerate() {
            for b0 in (0..WEIGHT_BYTES).step_by(8) {
                // SAFETY: AVX2 and GFNI are enabled at compile time (module cfg), and
                // `staged_index(r, a, n_active) < STAGED * n_active <= staged.len()` (asserted).
                unsafe {
                    let mut a8 = [_mm256_setzero_si256(); 8];
                    for (a, m) in self.matrices.iter().enumerate() {
                        let column = staged.get_unchecked(staged_index(r, a, n_active));
                        for (o, ao) in a8.iter_mut().enumerate() {
                            let g = _mm256_gf2p8affine_epi64_epi8(*column, _mm256_set1_epi64x(m[b0 + o] as i64), 0);
                            *ao = _mm256_xor_si256(*ao, g);
                        }
                    }
                    acc[b0..b0 + 8].copy_from_slice(&a8);
                }
            }
        }
    }

    /// Phase 2 with AVX-512: per pair of staged registers (one 512-bit load), every active lane byte
    /// through its 24 matrices, all 24 accumulators in registers, two lane bytes per three-way XOR.
    #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw"))]
    fn accumulate(&self, staged: &[V], n_active: usize, acc: &mut [[V; WEIGHT_BYTES]; STAGED]) {
        assert!(staged.len() >= STAGED * n_active);
        let matrices = &self.matrices;
        for pair in 0..STAGED / 2 {
            // SAFETY: AVX-512F/BW and GFNI are enabled at compile time; lane byte `a`'s registers
            // `2 pair`, `2 pair + 1` are the 64 bytes at `staged_index(2 pair, a, n_active)`
            // (asserted size).
            unsafe {
                let ld = |a: usize| _mm512_loadu_si512(staged.as_ptr().add(staged_index(2 * pair, a, n_active)).cast());
                let bc = |m: u64| _mm512_set1_epi64(m as i64);
                let mut a24 = [_mm512_setzero_si512(); WEIGHT_BYTES];
                let mut a = 0;
                while a + 1 < n_active {
                    let (c0, c1, m0, m1) = (ld(a), ld(a + 1), &matrices[a], &matrices[a + 1]);
                    for (b, ab) in a24.iter_mut().enumerate() {
                        let g0 = _mm512_gf2p8affine_epi64_epi8(c0, bc(m0[b]), 0);
                        let g1 = _mm512_gf2p8affine_epi64_epi8(c1, bc(m1[b]), 0);
                        *ab = _mm512_ternarylogic_epi64(*ab, g0, g1, 0x96);
                    }
                    a += 2;
                }
                if a < n_active {
                    let (c0, m0) = (ld(a), &matrices[a]);
                    for (b, ab) in a24.iter_mut().enumerate() {
                        *ab = _mm512_xor_si512(*ab, _mm512_gf2p8affine_epi64_epi8(c0, bc(m0[b]), 0));
                    }
                }
                // The low half is staged register `2 pair`, the high one `2 pair + 1`.
                for (b, ab) in a24.iter().enumerate() {
                    acc[2 * pair][b] = _mm512_castsi512_si256(*ab);
                    acc[2 * pair + 1][b] = _mm512_extracti64x4_epi64::<1>(*ab);
                }
            }
        }
    }

    /// The accumulators as field elements: register `r`'s accumulator `b` byte `n` is byte `b` of
    /// payload bit `32 r + n`'s sum.
    fn to_field_elements(acc: &[[V; WEIGHT_BYTES]; STAGED], out: &mut [[u64; 3]; PAYLOAD_BITS]) {
        for (r, acc) in acc.iter().enumerate() {
            // SAFETY: AVX2 is enabled at compile time; the stores write 16 bytes into checked
            // `[u64; 3]` entries.
            unsafe {
                let mut lo: [V; 16] = std::array::from_fn(|b| acc[b]);
                let z = _mm256_setzero_si256();
                let mut hi: [V; 16] = std::array::from_fn(|b| if b < 8 { acc[16 + b] } else { z });
                primitives::bits::transpose_bytes16x16_per_lane256(&mut lo);
                primitives::bits::transpose_bytes16x16_per_lane256(&mut hi);
                // lo[k] lane l: bytes 0..16 of payload bit 32 r + 16 l + k; hi[k]: bytes 16..24.
                for k in 0..16 {
                    for l in 0..2 {
                        let o = &mut out[32 * r + 16 * l + k];
                        let (v, w) = if l == 0 {
                            (_mm256_castsi256_si128(lo[k]), _mm256_castsi256_si128(hi[k]))
                        } else {
                            (_mm256_extracti128_si256(lo[k], 1), _mm256_extracti128_si256(hi[k], 1))
                        };
                        _mm_storeu_si128(o.as_mut_ptr().cast(), v);
                        o[2] = _mm_cvtsi128_si64(w) as u64;
                    }
                }
            }
        }
    }
}
