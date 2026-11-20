//! The product polynomial's bit sums by GFNI outer products (x86-64 with AVX2 and GFNI): once
//! [`coefficients`] has turned them back, the same values as [`crate::prover`]'s digit buckets,
//! `sum over positions j of weights[j] (x) product(q, j)` for every pack `q` of a block and every
//! coefficient of its product.
//!
//! A product of two embeddings has degree below `8 * POINTS`, so it is fixed by its values at
//! [`POINTS`] points of GF(2^8), the field of GF2P8MULB, with distinct minimal polynomials. A value
//! is a byte: the embeddings' values are affine byte maps of the witness's bytes ([`EVAL`]), and
//! a product's are byte products. The sums are taken over the values' bits, which the inverse of
//! the evaluation map ([`CRT`]) sends back to coefficients once a layer ([`coefficients`]).
//!
//! Eight consecutive `z` of one lane are a *lane byte*. For a lane byte's positions `j_0 .. j_7`
//! and one byte `b` of their weights, GF2P8AFFINEQB with the matrix `M_b` maps a *column byte*
//! (bit `k` = one bit of a value of `product(q, j_k)`) to byte `b` of the sum of the weights of
//! the positions whose bit is set: the lane byte's share of that bit's sum. One instruction does
//! this for 32 (pack, bit) column bytes at once.
//!
//! Per block, two phases:
//! 1. per *row byte* with a nonzero weight (the same byte of the five lanes of a row, which `chi`
//!    mixes): the five lane bytes' values, the products of each active lane byte, and their byte
//!    and bit transposes into column bytes, staged register by register in a per-thread buffer;
//! 2. per staged register, every active lane byte's 16 matrices applied into accumulators held in
//!    registers (eight at a time on AVX2, all 16 with AVX-512), then one byte transpose back to
//!    field elements.
//!
//! The two-phase outer-product scheme follows hashmancer-keccak's GFNI kernels; the code here is
//! written for this crate's layout (16-instance packs, 128-bit weights).

use core::arch::x86_64::*;

use primitives::field::F128;
use verifier::keccak::{BITS, EMBED_BITS, PRODUCT_BITS};

use crate::kernels::PACKS;
use crate::prover::PAYLOAD_BITS;
use crate::rmfe::RMFE;
use crate::table_maps::interleave_planes;
use crate::witness::{BLOCK_WORDS, words};

/// Points a product is held at, a byte each.
const POINTS: usize = 6;
const _: () = assert!(PRODUCT_BITS <= 8 * POINTS && PAYLOAD_BITS == 8 * POINTS * PACKS);
/// Staged registers per active lane byte: 32 column bytes each, one per pack and bit of a value.
const STAGED: usize = PAYLOAD_BITS / 32;
/// Bytes of a weight.
const WEIGHT_BYTES: usize = 16;

type V = __m256i;

/// The GF2P8AFFINEQB source that turns the instruction into an 8x8 bit transpose of its matrix.
const BIT_TRANSPOSE: i64 = 0x8040_2010_0804_0201_u64 as i64;

/// The position that bit `i` of a column byte stands for, after the byte and bit transposes.
const COLUMN_BIT_POSITION: [usize; 8] = [7, 6, 5, 4, 3, 2, 1, 0];

/// The byte product: binary polynomials modulo `x^8 + x^4 + x^3 + x + 1`.
const fn gf_mul(a: u8, b: u8) -> u8 {
    let (mut a, mut product) = (a, 0);
    let mut i = 0;
    while i < 8 {
        if b >> i & 1 == 1 {
            product ^= a;
        }
        a = a << 1 ^ if a >> 7 == 1 { 0x1b } else { 0 };
        i += 1;
    }
    product
}

/// `POWERS[i][n]` is point `i` to the power `n`. A point is the least of its eight conjugates, the
/// roots of its irreducible, so no two share one; an element of a proper subfield has fewer.
const POWERS: [[u8; 8 * POINTS]; POINTS] = {
    let mut powers = [[1u8; 8 * POINTS]; POINTS];
    let (mut i, mut t) = (0, 0u8);
    while i < POINTS {
        t += 1;
        let (mut conjugate, mut least) = (t, true);
        let mut k = 1;
        while k < 8 {
            conjugate = gf_mul(conjugate, conjugate);
            least &= conjugate > t;
            k += 1;
        }
        if least {
            let mut n = 1;
            while n < 8 * POINTS {
                powers[i][n] = gf_mul(powers[i][n - 1], t);
                n += 1;
            }
            i += 1;
        }
    }
    powers
};

/// The value at point `i` of the polynomial with coefficient bits `p`.
const fn value(p: u32, i: usize) -> u8 {
    let (mut v, mut n) = (0, 0);
    while n < EMBED_BITS {
        if p >> n & 1 == 1 {
            v ^= POWERS[i][n];
        }
        n += 1;
    }
    v
}

/// The matrix of the affine byte map sending bit `i` of a byte to `images[i]`: the map reads
/// output bit `t` off matrix byte `7 - t`.
const fn byte_map(images: [u8; 8]) -> u64 {
    let mut matrix = 0u64;
    let mut t = 0;
    while t < 8 {
        let mut i = 0;
        while i < 8 {
            matrix |= ((images[i] >> t & 1) as u64) << (8 * (7 - t) + i);
            i += 1;
        }
        t += 1;
    }
    matrix
}

/// `EVAL[h][i]` sends byte `h` of a pack to its share of the value of the pack's embedding at
/// point `i`.
const EVAL: [[u64; POINTS]; 2] = {
    let mut maps = [[0u64; POINTS]; 2];
    let mut h = 0;
    while h < 2 {
        let mut i = 0;
        while i < POINTS {
            let mut images = [0u8; 8];
            let mut b = 0;
            while b < 8 {
                images[b] = value(RMFE.emb[8 * h + b], i);
                b += 1;
            }
            maps[h][i] = byte_map(images);
            i += 1;
        }
        h += 1;
    }
    maps
};

/// The value of `ones` at each point.
const ONES: [u8; POINTS] = {
    let mut ones = [0u8; POINTS];
    let mut i = 0;
    while i < POINTS {
        ones[i] = value(RMFE.ones, i);
        i += 1;
    }
    ones
};

/// `CRT[n]` is the mask of the value bits (bit `t` of the value at point `i` at bit `8 i + t`)
/// whose sum is coefficient `n`: row `n` of the inverse of the evaluation map on polynomials of
/// fewer than `8 * POINTS` coefficients, by Gauss-Jordan elimination.
const CRT: [u64; 8 * POINTS] = {
    const N: usize = 8 * POINTS;
    // Row `8 i + t` sends a polynomial to bit `t` of its value at point `i`, beside the row of the
    // identity that the row operations turn into the inverse's.
    let mut rows = [[0u64; 2]; N];
    let mut r = 0;
    while r < N {
        let mut n = 0;
        while n < N {
            rows[r][0] |= ((POWERS[r / 8][n] >> (r % 8) & 1) as u64) << n;
            n += 1;
        }
        rows[r][1] = 1 << r;
        r += 1;
    }
    let mut c = 0;
    while c < N {
        let mut p = c;
        while rows[p][0] >> c & 1 == 0 {
            p += 1;
        }
        let pivot = rows[p];
        rows.swap(p, c);
        let mut r = 0;
        while r < N {
            if r != c && rows[r][0] >> c & 1 == 1 {
                rows[r][0] ^= pivot[0];
                rows[r][1] ^= pivot[1];
            }
            r += 1;
        }
        c += 1;
    }
    let mut crt = [0u64; N];
    let mut n = 0;
    while n < N {
        crt[n] = rows[n][1];
        n += 1;
    }
    crt
};

/// `SLOT[q][8 i + t]` is the entry of [`Scratch::out`] holding bit `t` of pack `q`'s values at
/// point `i`. Value registers ([`evaluate`]) hold pack `16 s + 8 l + u` at byte `16 l + 8 s + u`,
/// and [`ProductSums::stage_lane_byte`] puts byte `16 l + 2 j + d` at qword `2 l + d` of register
/// `8 i + j`, whose byte `n` is entry `32 r + n`.
const SLOT: [[u16; 8 * POINTS]; PACKS] = {
    let mut slot = [[0u16; 8 * POINTS]; PACKS];
    let mut i = 0;
    while i < POINTS {
        let mut j = 0;
        while j < 8 {
            let mut l = 0;
            while l < 2 {
                let mut d = 0;
                while d < 2 {
                    let byte = 2 * j + d;
                    let q = 16 * (byte / 8) + 8 * l + byte % 8;
                    let mut t = 0;
                    while t < 8 {
                        slot[q][8 * i + t] = (32 * (8 * i + j) + 8 * (2 * l + d) + t) as u16;
                        t += 1;
                    }
                    d += 1;
                }
                l += 1;
            }
            j += 1;
        }
        i += 1;
    }
    slot
};

/// Per-lane byte shuffle of a pack's two bytes apart: the lane's low bytes, then its high ones.
const SPLIT: [u8; 32] = {
    let mut t = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        let j = i % 16;
        t[i] = if j < 8 { 2 * j as u8 } else { 2 * (j - 8) as u8 + 1 };
        i += 1;
    }
    t
};

/// The values of a block position's 32 packs' embeddings at each point: register `i` holds point
/// `i`, pack `16 s + 8 l + u` at byte `16 l + 8 s + u`.
#[inline(always)]
fn evaluate(words: &[u64; BLOCK_WORDS]) -> [V; POINTS] {
    // SAFETY: AVX2 and GFNI are enabled at compile time (module cfg); the loads are of the eight
    // words and of `SPLIT`.
    unsafe {
        let split = _mm256_loadu_si256(SPLIT.as_ptr().cast());
        let w0 = _mm256_shuffle_epi8(_mm256_loadu_si256(words.as_ptr().cast()), split);
        let w1 = _mm256_shuffle_epi8(_mm256_loadu_si256(words.as_ptr().add(4).cast()), split);
        let (low, high) = (_mm256_unpacklo_epi64(w0, w1), _mm256_unpackhi_epi64(w0, w1));
        std::array::from_fn(|i| {
            _mm256_xor_si256(
                _mm256_gf2p8affine_epi64_epi8(low, _mm256_set1_epi64x(EVAL[0][i] as i64), 0),
                _mm256_gf2p8affine_epi64_epi8(high, _mm256_set1_epi64x(EVAL[1][i] as i64), 0),
            )
        })
    }
}

/// Per pack, the coefficients of the weighted sums of its products, from the weighted sums of
/// their value bits (entry [`SLOT`]`[q][8 i + t]` of `sums`).
pub fn coefficients(sums: &[F128]) -> Vec<[F128; PRODUCT_BITS]> {
    assert_eq!(sums.len(), PAYLOAD_BITS);
    SLOT.iter()
        .map(|slot| {
            let bits: [F128; 8 * POINTS] = std::array::from_fn(|r| sums[slot[r] as usize]);
            std::array::from_fn(|n| {
                let mut mask = CRT[n];
                let mut c = F128::ZERO;
                while mask != 0 {
                    c += bits[mask.trailing_zeros() as usize];
                    mask &= mask - 1;
                }
                c
            })
        })
        .collect()
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
fn bit(w: F128, n: usize) -> u8 {
    (w.to_limbs()[n / 64] >> (n % 64)) as u8 & 1
}

/// The 16 matrices of a lane byte's weights: `M_b` maps a column byte (bit `i` = position
/// `COLUMN_BIT_POSITION[i]`) to byte `b` of the sum of the weights it selects. An affine byte map
/// reads output bit `i` off matrix byte `7 - i`, whose bit `k` is then bit `8 b + i` of
/// `w[COLUMN_BIT_POSITION[k]]`.
fn lane_byte_matrices(w: &[F128]) -> [u64; WEIGHT_BYTES] {
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
    /// Per payload bit, its weighted sum's two words.
    pub out: Box<[[u64; 2]; PAYLOAD_BITS]>,
}

impl ProductSums {
    pub fn new(weights: &[F128]) -> Self {
        assert!(weights.len() >= BITS);
        let lane_bytes: Vec<Option<[u64; WEIGHT_BYTES]>> = (0..BITS / 8)
            .map(|o| {
                let w = &weights[8 * o..8 * o + 8];
                w.iter().any(|&x| x != F128::ZERO).then(|| lane_byte_matrices(w))
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
            out: Box::new([[0; 2]; PAYLOAD_BITS]),
        }
    }

    /// The weighted bit sums of a block (`BITS` positions of eight words) into `s.out`: entry
    /// [`SLOT`]`[q][8 i + t]` is `sum over j of weights[j] * bit t of product(q, j) at point i`.
    pub fn block_sums(&self, s: &mut Scratch, block: &[u64]) {
        let n_active = self.matrices.len();
        self.stage(block, &mut s.staged, n_active);
        self.accumulate(&s.staged, n_active, &mut s.acc);
        Self::to_field_elements(&s.acc, &mut s.out);
    }

    /// Phase 1: every active lane byte's column bytes into `staged[staged_index(r, a, n_active)]`.
    fn stage(&self, block: &[u64], staged: &mut [V], n_active: usize) {
        assert!(staged.len() >= STAGED * n_active);
        // SAFETY: AVX2 is enabled at compile time.
        let mut values = [[[unsafe { _mm256_setzero_si256() }; POINTS]; 8]; 5];
        let mut a = 0;
        for &(y, zb, mask) in &self.row_bytes {
            let (y, zb) = (y as usize, zb as usize);
            for (x, lane) in values.iter_mut().enumerate() {
                for (k, v) in lane.iter_mut().enumerate() {
                    *v = evaluate(words(block, 64 * (x + 5 * y) + 8 * zb + k));
                }
            }
            for x in (0..5).filter(|x| mask >> x & 1 == 1) {
                assert!(a < n_active, "one staged column per active lane byte");
                // SAFETY: AVX2 and GFNI are enabled at compile time; `a < n_active` (asserted) and
                // `stage_lane_byte` writes registers `r < STAGED` only (`8 * 5 + 7`), so every store
                // is inside `staged` (asserted size).
                unsafe {
                    Self::stage_lane_byte(
                        [&values[x], &values[(x + 1) % 5], &values[(x + 2) % 5]],
                        staged.as_mut_ptr(),
                        a,
                        n_active,
                    )
                };
                a += 1;
            }
        }
        // Phase 2 reads every active lane byte's registers: none may be left from another block.
        assert_eq!(a, n_active, "every active lane byte staged");
    }

    /// The column bytes of one lane byte's products, from the values of its three factors'
    /// embeddings (`e[f][k][i]`: factor `f`, position `k`, point `i`): register `8 i + j` holds, in
    /// qword `2 l + d`, the column byte of each bit of the products' values at point `i` for the
    /// pack at byte `16 l + 2 j + d` of a value register ([`SLOT`]).
    ///
    /// # Safety
    /// AVX2 and GFNI; `staged + staged_index(r, a, n_active)` writable for `r < STAGED`.
    #[inline(always)]
    unsafe fn stage_lane_byte(e: [&[[V; POINTS]; 8]; 3], staged: *mut V, a: usize, n_active: usize) {
        unsafe {
            let bit_transpose = _mm256_set1_epi64x(BIT_TRANSPOSE);
            for i in 0..POINTS {
                let ones = _mm256_set1_epi8(ONES[i] as i8);
                // `ones * (a + c) + b * c` at point `i`, per position.
                let p: [V; 8] = std::array::from_fn(|k| {
                    let (a, b, c) = (e[0][k][i], e[1][k][i], e[2][k][i]);
                    _mm256_xor_si256(
                        _mm256_gf2p8mul_epi8(_mm256_xor_si256(a, c), ones),
                        _mm256_gf2p8mul_epi8(b, c),
                    )
                });
                // 8x32 byte transpose: qword `d` of lane `l` of `w[j]` holds byte `16 l + 2 j + d` of each position.
                let w = interleave_planes!(
                    p,
                    _mm256_unpacklo_epi8,
                    _mm256_unpackhi_epi8,
                    _mm256_unpacklo_epi16,
                    _mm256_unpackhi_epi16,
                    _mm256_unpacklo_epi32,
                    _mm256_unpackhi_epi32
                );
                for (j, w) in w.into_iter().enumerate() {
                    *staged.add(staged_index(8 * i + j, a, n_active)) =
                        _mm256_gf2p8affine_epi64_epi8(bit_transpose, w, 0);
                }
            }
        }
    }

    /// Phase 2: per staged register, every active lane byte through its 16 matrices, eight
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
    /// through its 16 matrices, all 16 accumulators in registers, two lane bytes per three-way XOR.
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
                let mut sums = [_mm512_setzero_si512(); WEIGHT_BYTES];
                let mut a = 0;
                while a + 1 < n_active {
                    let (c0, c1, m0, m1) = (ld(a), ld(a + 1), &matrices[a], &matrices[a + 1]);
                    for (b, ab) in sums.iter_mut().enumerate() {
                        let g0 = _mm512_gf2p8affine_epi64_epi8(c0, bc(m0[b]), 0);
                        let g1 = _mm512_gf2p8affine_epi64_epi8(c1, bc(m1[b]), 0);
                        *ab = _mm512_ternarylogic_epi64(*ab, g0, g1, 0x96);
                    }
                    a += 2;
                }
                if a < n_active {
                    let (c0, m0) = (ld(a), &matrices[a]);
                    for (b, ab) in sums.iter_mut().enumerate() {
                        *ab = _mm512_xor_si512(*ab, _mm512_gf2p8affine_epi64_epi8(c0, bc(m0[b]), 0));
                    }
                }
                // The low half is staged register `2 pair`, the high one `2 pair + 1`.
                for (b, ab) in sums.iter().enumerate() {
                    acc[2 * pair][b] = _mm512_castsi512_si256(*ab);
                    acc[2 * pair + 1][b] = _mm512_extracti64x4_epi64::<1>(*ab);
                }
            }
        }
    }

    /// The accumulators as field elements: register `r`'s accumulator `b` byte `n` is byte `b` of
    /// payload bit `32 r + n`'s sum.
    fn to_field_elements(acc: &[[V; WEIGHT_BYTES]; STAGED], out: &mut [[u64; 2]; PAYLOAD_BITS]) {
        for (r, acc) in acc.iter().enumerate() {
            // SAFETY: AVX2 is enabled at compile time; each store writes one 16-byte `[u64; 2]` entry.
            unsafe {
                let mut sums = *acc;
                primitives::bits::transpose_bytes16x16_per_lane256(&mut sums);
                // sums[k] lane l: the 16 bytes of payload bit 32 r + 16 l + k.
                for (k, &sum) in sums.iter().enumerate() {
                    let halves = [_mm256_castsi256_si128(sum), _mm256_extracti128_si256::<1>(sum)];
                    for (l, v) in halves.into_iter().enumerate() {
                        _mm_storeu_si128(out[32 * r + 16 * l + k].as_mut_ptr().cast(), v);
                    }
                }
            }
        }
    }
}
