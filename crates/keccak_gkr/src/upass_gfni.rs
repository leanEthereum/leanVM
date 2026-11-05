//! The product polynomial's bit sums by GFNI outer products (x86-64 with AVX2, GFNI and PCLMULQDQ): the
//! same values as [`crate::prover`]'s digit buckets, `sum over positions j of weights[j] (x)
//! product(q, j)` for every pack `q` of a block and every coefficient of its product.
//!
//! For eight positions `j_0 .. j_7` (an *octet*: eight consecutive `z` of one lane) and one byte
//! `b` of their weights, GF2P8AFFINEQB with the matrix `M_b` maps a byte whose bit `k` is a
//! coefficient of `product(q, j_k)` to byte `b` of the sum of the weights of the positions whose
//! coefficient is set, the octet's contribution to that coefficient's sum. One instruction does
//! this for 32 (pack, coefficient) bytes at once, with no table and no lookup.
//!
//! Per block, two phases:
//! 1. per row and slice octet whose weights are not all zero (the five lanes of a row, which
//!    `chi` mixes, at eight consecutive `z`): the embeddings of the five lane octets, the
//!    products of each active one, and their bit transposes into *slot bytes* (bit `k` =
//!    position `k`), staged register by register in a per-thread buffer;
//! 2. per staged register, every active octet's 24 matrices applied into accumulators held in
//!    registers, eight at a time (AVX2 has sixteen registers), then one byte transpose back to
//!    the field elements.
//!
//! The 8x8 byte transpose without VPERMB ([`bt8`]) leaves the positions in a fixed order
//! ([`SIGMA`]), which the matrices absorb ([`PI`]).
//!
//! The two-phase outer-product scheme follows the GFNI U pass of hashmancer-keccak; the code
//! here is written for this crate's layout (16-instance packs, 192-bit weights).

use core::arch::x86_64::*;

use primitives::field::F192;

use crate::keccak::BITS;
use crate::kernels::{PACKS, embed, products};
use crate::witness::words;

/// The bits of a block position's products, 48 to each pack, in the prover's payload order.
pub const PAYLOAD: usize = 48 * PACKS;
/// Registers of 32 slot bytes per block position octet: a pack's six coefficient bytes for each
/// of the eight positions.
const REGS: usize = PAYLOAD / 32;
/// Bytes of a weight.
const WBYTES: usize = 24;

type V = __m256i;

/// GF2P8AFFINEQB's identity source: the affine map of matrix `A` is the transpose of `A`.
const IDENT: i64 = 0x8040_2010_0804_0201_u64 as i64;

/// The qword order [`bt8`] leaves: output qword `d` byte `n` is byte `d` of input `SIGMA[n]`.
const SIGMA: [usize; 8] = [0, 1, 4, 5, 2, 3, 6, 7];
/// The position of slot bit `i`, after [`bt8`] and a bit transpose: `SIGMA[7 - i]`.
const PI: [usize; 8] = {
    let mut p = [0; 8];
    let mut i = 0;
    while i < 8 {
        p[i] = SIGMA[7 - i];
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

/// 8x8 byte transpose of the qwords `a_0 .. a_7` (`p` = `a_0 .. a_3`, `q` = `a_4 .. a_7`):
/// output qword `d` (`d < 4` in the first register) byte `n` = byte `d` of `a_{SIGMA[n]}`. Two
/// in-lane byte shuffles, two 16-bit unpacks and two dword permutes.
///
/// # Safety
/// AVX2 (the module's build).
#[inline(always)]
unsafe fn bt8(p: V, q: V) -> [V; 2] {
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
unsafe fn transpose4(r: [V; 4]) -> [V; 4] {
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

/// Where staged register `r` of active octet `a` lies in the buffer (`na` active octets). With
/// AVX-512 the register pairs `2 R`, `2 R + 1` are adjacent, octet after octet, so phase 2 reads
/// a pair with one load; otherwise each register's octets are contiguous.
#[inline(always)]
const fn at(r: usize, a: usize, na: usize) -> usize {
    if cfg!(all(target_feature = "avx512f", target_feature = "avx512bw")) {
        2 * ((r / 2) * na + a) + r % 2
    } else {
        r * na + a
    }
}

/// Bit `n` of a weight.
#[inline(always)]
fn bit(w: F192, n: usize) -> u8 {
    ([w.c0, w.c1, w.c2][n / 64] >> (n % 64)) as u8 & 1
}

/// The 24 matrices of an octet's weights: `M_b` maps a slot byte (bit `i` = position
/// `PI[i]`) to byte `b` of the sum of the weights it selects. An affine byte map reads output
/// bit `i` off matrix byte `7 - i`, whose bit `k` is then bit `8 b + i` of `w[PI[k]]`.
fn octet_matrices(w: &[F192]) -> [u64; WBYTES] {
    std::array::from_fn(|b| {
        (0..8).fold(0u64, |m, i| {
            let row = (0..8).fold(0u8, |row, k| row | bit(w[PI[k]], 8 * b + i) << k);
            m | (row as u64) << (8 * (7 - i))
        })
    })
}

/// One layer's U pass by outer products: the weights' matrices, in the order the blocks visit
/// the octets.
pub struct UPass {
    /// Rows and slice octets `(y, z / 8)` with a nonzero weight, and the mask of their active `x`.
    rows: Vec<(u8, u8, u8)>,
    /// The active octets' matrices, in the order the rows visit them (`rows`, then `x`).
    mats: Vec<[u64; WBYTES]>,
}

/// A thread's buffers.
pub struct Scratch {
    /// The staged registers of a block, laid out by [`at`].
    buf: Vec<V>,
    acc: Box<[[V; WBYTES]; REGS]>,
    /// Per payload bit, its weighted sum's three words.
    pub out: Box<[[u64; 3]; PAYLOAD]>,
}

impl UPass {
    pub fn new(weights: &[F192]) -> Self {
        assert!(weights.len() >= BITS);
        let mats: Vec<Option<[u64; WBYTES]>> = (0..BITS / 8)
            .map(|o| {
                let w = &weights[8 * o..8 * o + 8];
                w.iter().any(|&x| x != F192::ZERO).then(|| octet_matrices(w))
            })
            .collect();
        let mut rows = Vec::new();
        let mut active = Vec::new();
        for y in 0..5usize {
            for zo in 0..8usize {
                let mask = (0..5).fold(0u8, |m, x| m | u8::from(mats[8 * (x + 5 * y) + zo].is_some()) << x);
                if mask != 0 {
                    rows.push((y as u8, zo as u8, mask));
                    for x in (0..5).filter(|x| mask >> x & 1 == 1) {
                        active.push(mats[8 * (x + 5 * y) + zo].expect("active"));
                    }
                }
            }
        }
        Self { rows, mats: active }
    }

    pub fn scratch(&self) -> Scratch {
        // SAFETY: AVX2 is enabled at compile time.
        let zero = unsafe { _mm256_setzero_si256() };
        Scratch {
            buf: vec![zero; REGS * self.mats.len()],
            acc: Box::new([[zero; WBYTES]; REGS]),
            out: Box::new([[0; 3]; PAYLOAD]),
        }
    }

    /// The weighted bit sums of a block (`BITS` positions of eight words) into `s.out`: entry
    /// `48 q + c` is `sum over j of weights[j] * coefficient c of product(q, j)`.
    pub fn block_sums(&self, s: &mut Scratch, block: &[u64]) {
        let na = self.mats.len();
        self.stage(block, &mut s.buf, na);
        self.accumulate(&s.buf, na, &mut s.acc);
        Self::readout(&s.acc, &mut s.out);
    }

    /// Phase 1: every active octet's slot bytes into `buf[at(r, a, na)]`.
    fn stage(&self, block: &[u64], buf: &mut [V], na: usize) {
        assert!(buf.len() >= REGS * na);
        let mut e = [[[0u32; PACKS]; 8]; 5];
        let mut prod = [[0u64; PACKS]; 8];
        let mut a = 0;
        for &(y, zo, mask) in &self.rows {
            let (y, zo) = (y as usize, zo as usize);
            for (x, ex) in e.iter_mut().enumerate() {
                for (k, ek) in ex.iter_mut().enumerate() {
                    *ek = embed(words(block, 64 * (x + 5 * y) + 8 * zo + k));
                }
            }
            for x in (0..5).filter(|x| mask >> x & 1 == 1) {
                let (e0, e1, e2) = (&e[x], &e[(x + 1) % 5], &e[(x + 2) % 5]);
                for (k, p) in prod.iter_mut().enumerate() {
                    *p = products(&e0[k], &e1[k], &e2[k]);
                }
                assert!(a < na, "one staged column per active octet");
                // SAFETY: AVX2 and GFNI are enabled at compile time; `a < na` (asserted) and
                // `stage_octet` writes registers `r < REGS` only (`3 * 15 + 2`), so every store is
                // inside `buf` (asserted size).
                unsafe { Self::stage_octet(&prod, buf.as_mut_ptr(), a, na) };
                a += 1;
            }
        }
        // Phase 2 reads every active octet's registers: none may be left from another block.
        assert_eq!(a, na, "every active octet staged");
    }

    /// The slot registers of one octet's products (`prod[k][q]`: position `k`, pack `q`):
    /// register `r` holds slots `4 r .. 4 r + 4`, slot `6 q + m` being coefficient byte `m` of
    /// pack `q` (bit `i` of its byte `b`: coefficient `8 m + b` of position `PI[i]`).
    ///
    /// # Safety
    /// AVX2 and GFNI; `buf + at(r, a, na)` writable for `r < REGS`.
    #[inline(always)]
    unsafe fn stage_octet(prod: &[[u64; PACKS]; 8], buf: *mut V, a: usize, na: usize) {
        unsafe {
            let ident = _mm256_set1_epi64x(IDENT);
            let ld = |k: usize, q: usize| _mm256_loadu_si256(prod[k].as_ptr().add(q).cast());
            for qq in (0..PACKS).step_by(4) {
                // t[h][i] qword k = the product of pack qq + i at position 4 h + k.
                let t = [
                    transpose4([ld(0, qq), ld(1, qq), ld(2, qq), ld(3, qq)]),
                    transpose4([ld(4, qq), ld(5, qq), ld(6, qq), ld(7, qq)]),
                ];
                let slots: [[V; 2]; 4] = std::array::from_fn(|i| {
                    let [lo, hi] = bt8(t[0][i], t[1][i]);
                    [
                        _mm256_gf2p8affine_epi64_epi8(ident, lo, 0),
                        _mm256_gf2p8affine_epi64_epi8(ident, hi, 0),
                    ]
                });
                for pair in 0..2 {
                    // Packs q, q + 1 take three registers: bytes 0..4 of q; 4, 5 of q and 0, 1
                    // of q + 1; 2..4 and 4, 5 of q + 1.
                    let (s0, s1) = (slots[2 * pair], slots[2 * pair + 1]);
                    let r = 3 * ((qq + 2 * pair) / 2);
                    *buf.add(at(r, a, na)) = s0[0];
                    *buf.add(at(r + 1, a, na)) = _mm256_permute2x128_si256(s0[1], s1[0], 0x20);
                    *buf.add(at(r + 2, a, na)) = _mm256_permute2x128_si256(s1[0], s1[1], 0x21);
                }
            }
        }
    }

    /// Phase 2: per staged register, every active octet through its 24 matrices, eight
    /// accumulators at a time in registers.
    #[cfg(not(all(target_feature = "avx512f", target_feature = "avx512bw")))]
    fn accumulate(&self, buf: &[V], na: usize, acc: &mut [[V; WBYTES]; REGS]) {
        assert!(buf.len() >= REGS * na);
        for (r, acc) in acc.iter_mut().enumerate() {
            for b0 in (0..WBYTES).step_by(8) {
                // SAFETY: AVX2 and GFNI are enabled at compile time (module cfg), and
                // `at(r, a, na) < REGS * na <= buf.len()` (asserted).
                unsafe {
                    let mut a8 = [_mm256_setzero_si256(); 8];
                    for (a, m) in self.mats.iter().enumerate() {
                        let st = buf.get_unchecked(at(r, a, na));
                        for (o, ao) in a8.iter_mut().enumerate() {
                            let g = _mm256_gf2p8affine_epi64_epi8(*st, _mm256_set1_epi64x(m[b0 + o] as i64), 0);
                            *ao = _mm256_xor_si256(*ao, g);
                        }
                    }
                    acc[b0..b0 + 8].copy_from_slice(&a8);
                }
            }
        }
    }

    /// Phase 2 with AVX-512: per pair of staged registers (one 512-bit load), every active octet
    /// through its 24 matrices, all 24 accumulators in registers, two octets per three-way XOR.
    #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw"))]
    fn accumulate(&self, buf: &[V], na: usize, acc: &mut [[V; WBYTES]; REGS]) {
        assert!(buf.len() >= REGS * na);
        let mats = &self.mats;
        for pair in 0..REGS / 2 {
            // SAFETY: AVX-512F/BW and GFNI are enabled at compile time; octet `a`'s registers
            // `2 pair`, `2 pair + 1` are the 64 bytes at `at(2 pair, a, na)` (asserted size).
            unsafe {
                let ld = |a: usize| _mm512_loadu_si512(buf.as_ptr().add(at(2 * pair, a, na)).cast());
                let bc = |m: u64| _mm512_set1_epi64(m as i64);
                let mut a24 = [_mm512_setzero_si512(); WBYTES];
                let mut a = 0;
                while a + 1 < na {
                    let (s0, s1, m0, m1) = (ld(a), ld(a + 1), &mats[a], &mats[a + 1]);
                    for (b, ab) in a24.iter_mut().enumerate() {
                        let g0 = _mm512_gf2p8affine_epi64_epi8(s0, bc(m0[b]), 0);
                        let g1 = _mm512_gf2p8affine_epi64_epi8(s1, bc(m1[b]), 0);
                        *ab = _mm512_ternarylogic_epi64(*ab, g0, g1, 0x96);
                    }
                    a += 2;
                }
                if a < na {
                    let (s0, m0) = (ld(a), &mats[a]);
                    for (b, ab) in a24.iter_mut().enumerate() {
                        *ab = _mm512_xor_si512(*ab, _mm512_gf2p8affine_epi64_epi8(s0, bc(m0[b]), 0));
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

    /// The accumulators as field elements: register `r`'s accumulator `b` byte `n` is byte `b`
    /// of payload bit `32 r + n`'s sum.
    fn readout(acc: &[[V; WBYTES]; REGS], out: &mut [[u64; 3]; PAYLOAD]) {
        for (r, acc) in acc.iter().enumerate() {
            // SAFETY: AVX2 is enabled at compile time; the stores write 16 bytes into
            // checked `[u64; 3]` entries.
            unsafe {
                let mut lo: [V; 16] = std::array::from_fn(|b| acc[b]);
                let z = _mm256_setzero_si256();
                let mut hi: [V; 16] = std::array::from_fn(|b| if b < 8 { acc[16 + b] } else { z });
                primitives::bits::transpose16_lanes256(&mut lo);
                primitives::bits::transpose16_lanes256(&mut hi);
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
