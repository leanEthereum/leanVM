//! Keccak-256, the repo's one hash function: Ethereum's, which is the 256-bit hash of FIPS
//! 202 with Keccak's original padding.
//!
//! Three surfaces, in increasing order of how much of the machine they touch:
//!
//! - [`keccak_f`], the Keccak-f\[1600\] permutation, which the VM's `KECCAK` opcode computes
//!   and `keccak_gkr` proves, and [`keccak_f_many`], its batched form.
//! - [`hash`] / [`Hasher`], Keccak-256 over bytes.
//! - [`hash_many`], the batched form: [`LANES`] independent equal-length inputs
//!   hashed together with the state transposed across lanes, which is how the
//!   PCS Merkle tree gets SIMD out of hashes that are individually serial.
//!
//! The state is 25 little-endian 64-bit lanes, lane `x + 5y` holding
//! `A[x, y]`. The first `RATE / 8` lanes are the rate: a message block is
//! XORed into them before each permutation, and the digest is read off the first
//! `OUT_LEN / 8` of them after the last one.

/// Digest length in bytes. Keccak-256 throughout.
pub const OUT_LEN: usize = 32;
/// Digest length in lanes.
const OUT_LANES: usize = OUT_LEN / 8;
/// Sponge rate in bytes: `1600 - 2·256` bits.
pub const RATE: usize = 136;
/// Sponge rate in lanes.
const RATE_LANES: usize = RATE / 8;
/// Lanes in the state.
pub const STATE_LANES: usize = 25;
/// Rounds per permutation.
pub const ROUNDS: usize = 24;

/// The first bit of Keccak's `10*1` padding, as the byte XORed right after the
/// message. It is the only difference from FIPS 202's 256-bit hash, whose suffix makes it `0x06`.
pub const PAD_FIRST: u8 = 0x01;
/// The last bit of the `10*1` padding, XORed into the rate's last byte.
pub const PAD_LAST: u8 = 0x80;

/// The ι round constants.
pub const RC: [u64; ROUNDS] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808A,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808B,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008A,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000A,
    0x0000_0000_8000_808B,
    0x8000_0000_0000_008B,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800A,
    0x8000_0000_8000_000A,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// The ρ rotation (left) of lane `x + 5y`.
pub const RHO: [u32; STATE_LANES] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// Where π sends lane `x + 5y`: to lane `y + 5·((2x + 3y) mod 5)`.
pub const PI: [usize; STATE_LANES] = {
    let mut p = [0usize; STATE_LANES];
    let mut i = 0;
    while i < STATE_LANES {
        let (x, y) = (i % 5, i / 5);
        p[i] = y + 5 * ((2 * x + 3 * y) % 5);
        i += 1;
    }
    p
};

/// One state lane across all inputs of a batch: a vector of `WIDTH` 64-bit
/// lanes. The permutation is written once over this trait, so each backend
/// supplies only XOR, the χ step and the rotations.
///
/// `load` and `store` move the `WIDTH` words from `src[i]` on, unaligned and bounds-checked.
trait Lanes64: Copy {
    const WIDTH: usize;

    fn load(src: &[u64], i: usize) -> Self;
    fn store(self, dst: &mut [u64], i: usize);

    fn splat(x: u64) -> Self;
    fn xor(self, o: Self) -> Self;
    /// Rotate every lane left by `N`, `0 <= N < 64`.
    fn rotl<const N: i32>(self) -> Self;
    /// χ on one lane: `a ⊕ (¬b ∧ c)`.
    fn chi(a: Self, b: Self, c: Self) -> Self;

    /// XOR the first `words` little-endian words of every input into `st[..words]`.
    ///
    /// Input `l` is at `data[l * len..]`, and its words start `byte_offset` bytes in.
    /// Needs `words <= RATE_LANES` and `byte_offset + 8 * words <= len`.
    #[inline(always)]
    fn absorb_words(st: &mut [Self; STATE_LANES], data: &[u8], len: usize, byte_offset: usize, words: usize) {
        assert!(words <= RATE_LANES && byte_offset + 8 * words <= len);
        // `buf[w * WIDTH + l]` is input `l`'s word `w`.
        let mut buf = [0u64; RATE_LANES * MAX_WIDTH];
        for l in 0..Self::WIDTH {
            let src = &data[l * len + byte_offset..][..8 * words];
            for (w, word) in src.as_chunks::<8>().0.iter().enumerate() {
                buf[w * Self::WIDTH + l] = u64::from_le_bytes(*word);
            }
        }
        for (w, lane) in st[..words].iter_mut().enumerate() {
            *lane = lane.xor(Self::load(&buf, w * Self::WIDTH));
        }
    }

    /// Write the first [`OUT_LEN`] bytes of every input's state to `out[l * OUT_LEN..]`.
    #[inline(always)]
    fn store_digests(st: &[Self; STATE_LANES], out: &mut [u8]) {
        let mut lanes = [0u64; OUT_LANES * MAX_WIDTH];
        for (w, lane) in st[..OUT_LANES].iter().enumerate() {
            lane.store(&mut lanes, w * Self::WIDTH);
        }
        for (l, digest) in out.as_chunks_mut::<OUT_LEN>().0.iter_mut().enumerate() {
            for (w, bytes) in digest.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                *bytes = lanes[w * Self::WIDTH + l].to_le_bytes();
            }
        }
    }

    #[inline(always)]
    fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
        a.xor(b).xor(c).xor(d).xor(e)
    }
    /// θ's column effect: `c_prev ⊕ rotl(c_next, 1)`.
    #[inline(always)]
    fn theta_d(c_prev: Self, c_next: Self) -> Self {
        c_prev.xor(c_next.rotl::<1>())
    }
}

/// The 24 rounds, over any lane type. Straight-line, so every rotation is an
/// immediate and every lane index a register.
///
/// ρ and π are written by output row, χ takes the rows in turn, and the next round's column
/// parities accumulate from the lanes χ writes. Both x86 backends schedule this order better than
/// one that forms every lane before χ and every parity after it.
#[inline(always)]
fn permute<S: Lanes64>(a: &mut [S; STATE_LANES]) {
    let mut c: [S; 5] = std::array::from_fn(|x| S::xor5(a[x], a[x + 5], a[x + 10], a[x + 15], a[x + 20]));
    for &rc in &RC {
        let d: [S; 5] = std::array::from_fn(|x| S::theta_d(c[(x + 4) % 5], c[(x + 1) % 5]));
        let th = |i: usize| a[i].xor(d[i % 5]);
        // Row `y` holds the lanes π sends there, each rotated by its `RHO`.
        #[rustfmt::skip]
        let rows: [[S; 5]; 5] = [
            [th(0), th(6).rotl::<44>(), th(12).rotl::<43>(), th(18).rotl::<21>(), th(24).rotl::<14>()],
            [th(3).rotl::<28>(), th(9).rotl::<20>(), th(10).rotl::<3>(), th(16).rotl::<45>(), th(22).rotl::<61>()],
            [th(1).rotl::<1>(), th(7).rotl::<6>(), th(13).rotl::<25>(), th(19).rotl::<8>(), th(20).rotl::<18>()],
            [th(4).rotl::<27>(), th(5).rotl::<36>(), th(11).rotl::<10>(), th(17).rotl::<15>(), th(23).rotl::<56>()],
            [th(2).rotl::<62>(), th(8).rotl::<55>(), th(14).rotl::<39>(), th(15).rotl::<41>(), th(21).rotl::<2>()],
        ];
        for (y, &[b0, b1, b2, b3, b4]) in rows.iter().enumerate() {
            let mut row = [
                S::chi(b0, b1, b2),
                S::chi(b1, b2, b3),
                S::chi(b2, b3, b4),
                S::chi(b3, b4, b0),
                S::chi(b4, b0, b1),
            ];
            if y == 0 {
                row[0] = row[0].xor(S::splat(rc));
            }
            for x in 0..5 {
                a[5 * y + x] = row[x];
                c[x] = if y == 0 { row[x] } else { c[x].xor(row[x]) };
            }
        }
    }
}

/// A single lane: the scalar permutation, and the portable batched backend.
impl Lanes64 for u64 {
    const WIDTH: usize = 1;

    #[inline(always)]
    fn load(src: &[u64], i: usize) -> Self {
        src[i]
    }
    #[inline(always)]
    fn store(self, dst: &mut [u64], i: usize) {
        dst[i] = self;
    }
    #[inline(always)]
    fn splat(x: u64) -> Self {
        x
    }
    #[inline(always)]
    fn xor(self, o: Self) -> Self {
        self ^ o
    }
    #[inline(always)]
    fn rotl<const N: i32>(self) -> Self {
        self.rotate_left(N as u32)
    }
    #[inline(always)]
    fn chi(a: Self, b: Self, c: Self) -> Self {
        a ^ (!b & c)
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
mod single_avx512;

/// The Keccak-f\[1600\] permutation, in place.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
#[inline]
pub fn keccak_f(a: &mut [u64; STATE_LANES]) {
    single_avx512::permute(a);
}

/// The Keccak-f\[1600\] permutation, in place.
#[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f")))]
#[inline]
pub fn keccak_f(state: &mut [u64; STATE_LANES]) {
    permute(state);
}

/// The padding's last bit as it sits in lane 16, the rate's last lane.
pub const END_BIT: u64 = (PAD_LAST as u64) << 56;

/// One sponge step: XOR the rate block `block` into `state` and permute.
#[inline]
fn absorb(state: &mut [u64; STATE_LANES], block: &[u64; RATE_LANES]) {
    for (s, b) in state.iter_mut().zip(block) {
        *s ^= b;
    }
    keccak_f(state);
}

/// A full block of message bytes, as rate lanes.
#[inline]
fn block_of(bytes: &[u8; RATE]) -> [u64; RATE_LANES] {
    std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
}

/// The final block: the last `tail.len() < RATE` message bytes, then the padding, as rate lanes.
#[inline]
fn final_block(tail: &[u8]) -> [u64; RATE_LANES] {
    assert!(tail.len() < RATE, "a final block holds fewer than RATE message bytes");
    let mut bytes = [0u8; RATE];
    bytes[..tail.len()].copy_from_slice(tail);
    bytes[tail.len()] ^= PAD_FIRST;
    bytes[RATE - 1] ^= PAD_LAST;
    block_of(&bytes)
}

/// The digest: the first [`OUT_LEN`] bytes of the state.
#[inline]
pub fn digest_of(state: &[u64; STATE_LANES]) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];
    for (chunk, lane) in out.as_chunks_mut::<8>().0.iter_mut().zip(state) {
        *chunk = lane.to_le_bytes();
    }
    out
}

/// Streaming [`hash`].
#[derive(Clone)]
pub struct Hasher {
    state: [u64; STATE_LANES],
    buf: [u8; RATE],
    /// Bytes currently in `buf`, in `0..RATE`.
    buf_len: usize,
}

impl Hasher {
    pub fn new() -> Self {
        Self {
            state: [0; STATE_LANES],
            buf: [0; RATE],
            buf_len: 0,
        }
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            let take = (RATE - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == RATE {
                absorb(&mut self.state, &block_of(&self.buf));
                self.buf_len = 0;
            }
        }
        self
    }

    pub fn finalize(&self) -> [u8; OUT_LEN] {
        let mut state = self.state;
        absorb(&mut state, &final_block(&self.buf[..self.buf_len]));
        digest_of(&state)
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

/// Keccak-256 of `data`, Ethereum's `keccak256`: FIPS 202's sponge over Keccak-f\[1600\] with
/// rate [`RATE`] and Keccak's original padding.
pub fn hash(data: &[u8]) -> [u8; OUT_LEN] {
    hash_from_state(data, &[0; STATE_LANES])
}

/// The state after absorbing `n_blocks` all-zero blocks.
///
/// A leaf image that starts with whole zero blocks (the PCS's absent interleaving lanes) shares
/// that prefix with every other leaf, so the committer computes this once and starts each
/// leaf's sponge here. Nothing about the digest changes: a prefix's permutations depend on
/// nothing after them, so the result is still the hash of the whole image.
pub fn zero_prefix_state(n_blocks: usize) -> [u64; STATE_LANES] {
    let mut state = [0; STATE_LANES];
    for _ in 0..n_blocks {
        keccak_f(&mut state);
    }
    state
}

/// [`hash`] continued from a sponge state that has absorbed whole blocks (see
/// [`zero_prefix_state`]): `data` is the rest of the message.
fn hash_from_state(data: &[u8], state: &[u64; STATE_LANES]) -> [u8; OUT_LEN] {
    let mut state = *state;
    let (blocks, tail) = data.as_chunks::<RATE>();
    for block in blocks {
        absorb(&mut state, &block_of(block));
    }
    absorb(&mut state, &final_block(tail));
    digest_of(&state)
}

// ---------------------------------------------------------------------------
// Batched (transposed) hashing
//
// `LANES` independent equal-length inputs are hashed together with the state
// transposed across lanes: state lane `i` becomes one SIMD vector holding that
// lane for every input, so a round is elementwise 64-bit work with no
// cross-lane traffic. Equal lengths put every input's padding in the same place,
// which is what lets one instruction stream serve the whole batch.
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
mod x86 {
    use super::Lanes64;
    #[cfg(target_feature = "avx512f")]
    use super::{OUT_LEN, RATE_LANES, STATE_LANES};
    #[cfg(target_feature = "avx512f")]
    use crate::simd;
    use crate::{load_at, store_at};
    use core::arch::x86_64::*;

    /// AVX2: four lanes. No 64-bit rotate before AVX-512, so a rotation is a
    /// shift pair, and χ is one `vpandn`.
    ///
    /// Unused by the library on an AVX-512 target (the dispatch is compile
    /// time), but always exercised by `every_backend_matches_scalar`.
    #[cfg_attr(target_feature = "avx512f", allow(dead_code))]
    #[derive(Clone, Copy)]
    pub(super) struct Avx2(__m256i);

    impl Lanes64 for Avx2 {
        const WIDTH: usize = 4;

        #[inline(always)]
        fn load(src: &[u64], i: usize) -> Self {
            Self(load_at(src, i))
        }
        #[inline(always)]
        fn store(self, dst: &mut [u64], i: usize) {
            store_at(dst, i, self.0)
        }
        #[inline(always)]
        fn splat(x: u64) -> Self {
            Self(unsafe { _mm256_set1_epi64x(x as i64) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            Self(unsafe { _mm256_xor_si256(self.0, o.0) })
        }
        #[inline(always)]
        fn rotl<const N: i32>(self) -> Self {
            if N == 0 {
                return self;
            }
            unsafe {
                let l = _mm256_sll_epi64(self.0, _mm_cvtsi32_si128(N));
                let r = _mm256_srl_epi64(self.0, _mm_cvtsi32_si128(64 - N));
                Self(_mm256_or_si256(l, r))
            }
        }
        #[inline(always)]
        fn chi(a: Self, b: Self, c: Self) -> Self {
            Self(unsafe { _mm256_xor_si256(a.0, _mm256_andnot_si256(b.0, c.0)) })
        }
    }

    /// AVX-512: eight lanes, a native rotate, and `vpternlogq` for both χ and
    /// the five-way column parity.
    #[cfg(target_feature = "avx512f")]
    #[derive(Clone, Copy)]
    pub(super) struct Avx512(__m512i);

    #[cfg(target_feature = "avx512f")]
    impl Lanes64 for Avx512 {
        const WIDTH: usize = 8;

        #[inline(always)]
        fn load(src: &[u64], i: usize) -> Self {
            Self(load_at(src, i))
        }
        #[inline(always)]
        fn store(self, dst: &mut [u64], i: usize) {
            store_at(dst, i, self.0)
        }
        #[inline(always)]
        fn splat(x: u64) -> Self {
            Self(unsafe { _mm512_set1_epi64(x as i64) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            Self(unsafe { _mm512_xor_si512(self.0, o.0) })
        }
        #[inline(always)]
        fn rotl<const N: i32>(self) -> Self {
            Self(unsafe { _mm512_rol_epi64::<N>(self.0) })
        }
        #[inline(always)]
        fn chi(a: Self, b: Self, c: Self) -> Self {
            // Truth table of `a ^ (!b & c)` over (a, b, c) = (0xF0, 0xCC, 0xAA).
            Self(unsafe { _mm512_ternarylogic_epi64::<0xD2>(a.0, b.0, c.0) })
        }
        #[inline(always)]
        fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
            unsafe {
                let t = _mm512_ternarylogic_epi64::<0x96>(a.0, b.0, c.0);
                Self(_mm512_ternarylogic_epi64::<0x96>(t, d.0, e.0))
            }
        }

        #[inline(always)]
        fn absorb_words(st: &mut [Self; STATE_LANES], data: &[u8], len: usize, byte_offset: usize, words: usize) {
            assert!(words <= RATE_LANES && byte_offset + 8 * words <= len);
            for g in 0..words.div_ceil(8) {
                let n = (words - 8 * g).min(8);
                // Each load reads only the `n` valid words of its input, which `load_prefix` checks
                // against the sub-slice, and the assert above keeps them inside the input.
                let rows: [__m512i; 8] = std::array::from_fn(|l| {
                    let input = &data[l * len + byte_offset + 64 * g..];
                    simd::load_prefix(input, 0, n)
                });
                let cols = simd::transpose8(rows);
                for (w, col) in cols.into_iter().enumerate().take(n) {
                    st[8 * g + w] = Self(simd::xor(st[8 * g + w].0, col));
                }
            }
        }

        #[inline(always)]
        fn store_digests(st: &[Self; STATE_LANES], out: &mut [u8]) {
            assert_eq!(out.len(), 8 * OUT_LEN);
            // Rows are the four digest words of each input, then four zero words.
            let zero = simd::from_words([0; 8]);
            let rows = simd::transpose8([st[0].0, st[1].0, st[2].0, st[3].0, zero, zero, zero, zero]);
            for (pair, [first, second]) in rows.as_chunks::<2>().0.iter().enumerate() {
                // Low 256 bits of two inputs' rows side by side: lanes 0, 1 of the first, then of the second.
                // SAFETY: as above, a register-only intrinsic under compile-time AVX-512F.
                let both = unsafe { _mm512_shuffle_i64x2::<0x44>(*first, *second) };
                simd::store(out, pair, both);
            }
        }
    }
}

#[cfg(target_arch = "aarch64")]
mod arm {
    use super::Lanes64;
    use crate::{load_at, store_at};
    use core::arch::aarch64::*;

    /// NEON: two lanes. With the SHA3 extension, χ is one `BCAX`, the column
    /// parity two `EOR3` and θ's rotate-and-xor one `RAX1`.
    #[derive(Clone, Copy)]
    pub(super) struct Neon(uint64x2_t);

    impl Lanes64 for Neon {
        const WIDTH: usize = 2;

        #[inline(always)]
        fn load(src: &[u64], i: usize) -> Self {
            Self(load_at(src, i))
        }
        #[inline(always)]
        fn store(self, dst: &mut [u64], i: usize) {
            store_at(dst, i, self.0)
        }
        #[inline(always)]
        fn splat(x: u64) -> Self {
            Self(unsafe { vdupq_n_u64(x) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            Self(unsafe { veorq_u64(self.0, o.0) })
        }
        #[inline(always)]
        fn rotl<const N: i32>(self) -> Self {
            if N == 0 {
                return self;
            }
            unsafe {
                let l = vshlq_u64(self.0, vdupq_n_s64(N as i64));
                let r = vshlq_u64(self.0, vdupq_n_s64(N as i64 - 64));
                Self(vorrq_u64(l, r))
            }
        }
        #[inline(always)]
        fn chi(a: Self, b: Self, c: Self) -> Self {
            #[cfg(target_feature = "sha3")]
            {
                // BCAX(a, c, b) = a ^ (c & !b).
                Self(unsafe { vbcaxq_u64(a.0, c.0, b.0) })
            }
            #[cfg(not(target_feature = "sha3"))]
            {
                Self(unsafe { veorq_u64(a.0, vbicq_u64(c.0, b.0)) })
            }
        }
        #[cfg(target_feature = "sha3")]
        #[inline(always)]
        fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
            unsafe { Self(veor3q_u64(veor3q_u64(a.0, b.0, c.0), d.0, e.0)) }
        }
        #[cfg(target_feature = "sha3")]
        #[inline(always)]
        fn theta_d(c_prev: Self, c_next: Self) -> Self {
            Self(unsafe { vrax1q_u64(c_prev.0, c_next.0) })
        }
    }
}

/// The widest backend this build has, which the batched entry points use.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
type Backend = x86::Avx512;
#[cfg(all(target_arch = "x86_64", not(target_feature = "avx512f"), target_feature = "avx2"))]
type Backend = x86::Avx2;
#[cfg(target_arch = "aarch64")]
type Backend = arm::Neon;
#[cfg(not(any(all(target_arch = "x86_64", target_feature = "avx2"), target_arch = "aarch64")))]
type Backend = u64;

/// Inputs handled together by the widest backend. Batched entry points accept
/// any count and process the remainder serially.
pub const LANES: usize = Backend::WIDTH;

/// Widest batch any backend takes.
const MAX_WIDTH: usize = 8;

/// Hash `S::WIDTH` inputs of `len` bytes, input `l` at `data[l * len..]`, from the shared
/// sponge state `init`, writing the digests consecutively to `out`.
#[inline(always)]
fn hash_group<S: Lanes64>(data: &[u8], len: usize, init: &[u64; STATE_LANES], out: &mut [u8]) {
    debug_assert_eq!((data.len(), out.len()), (S::WIDTH * len, S::WIDTH * OUT_LEN));
    let mut st: [S; STATE_LANES] = std::array::from_fn(|i| S::splat(init[i]));
    let (blocks, tail) = (len / RATE, len % RATE);
    for blk in 0..blocks {
        S::absorb_words(&mut st, data, len, blk * RATE, RATE_LANES);
        permute(&mut st);
    }
    // The final block: its whole words, then the partial word, then the padding, which every input has in the same lanes.
    let (words, part) = (tail / 8, tail % 8);
    S::absorb_words(&mut st, data, len, blocks * RATE, words);
    if part > 0 {
        let lanes: [u64; MAX_WIDTH] = std::array::from_fn(|l| {
            if l >= S::WIDTH {
                return 0;
            }
            let rest = &data[l * len + blocks * RATE + 8 * words..][..part];
            rest.iter()
                .enumerate()
                .fold(0, |acc, (j, &b)| acc | u64::from(b) << (8 * j))
        });
        st[words] = st[words].xor(S::load(&lanes, 0));
    }
    st[words] = st[words].xor(S::splat(u64::from(PAD_FIRST) << (8 * part)));
    st[RATE_LANES - 1] = st[RATE_LANES - 1].xor(S::splat(END_BIT));
    permute(&mut st);
    S::store_digests(&st, out);
}

/// The batched hash over one backend: `out.len() / OUT_LEN` inputs of `len` bytes.
#[inline(always)]
fn hash_many_with<S: Lanes64>(data: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [u8]) {
    let n = out.len() / OUT_LEN;
    assert_eq!((data.len(), out.len()), (n * len, n * OUT_LEN));
    let groups = n / S::WIDTH;
    for g in 0..groups {
        let digests = &mut out[g * S::WIDTH * OUT_LEN..][..S::WIDTH * OUT_LEN];
        hash_group::<S>(&data[g * S::WIDTH * len..][..S::WIDTH * len], len, state, digests);
    }
    for i in groups * S::WIDTH..n {
        let d = hash_from_state(&data[i * len..(i + 1) * len], state);
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&d);
    }
}

/// Batched Keccak-256 of `data` split into `len`-byte inputs, writing one 32-byte
/// digest per input to `out`. Byte-identical to [`hash`] per input; the batching
/// only changes how the lanes are scheduled.
pub fn hash_many(data: &[u8], len: usize, out: &mut [u8]) {
    hash_many_from_state(data, len, &[0; STATE_LANES], out);
}

/// [`hash_many`] continued from one sponge state shared by every input, which has absorbed
/// whole blocks (see [`zero_prefix_state`]). Byte-identical to hashing each full image.
pub fn hash_many_from_state(data: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [u8]) {
    hash_many_with::<Backend>(data, len, state, out)
}

/// Keccak-f\[1600\] of every state in place, [`LANES`] at a time.
pub fn keccak_f_many(states: &mut [[u64; STATE_LANES]]) {
    let (groups, rest) = states.as_chunks_mut::<LANES>();
    for group in groups {
        permute_group::<Backend>(group);
    }
    for state in rest {
        keccak_f(state);
    }
}

/// Keccak-f of `S::WIDTH` states, transposed into one vector per lane and back.
#[inline(always)]
fn permute_group<S: Lanes64>(states: &mut [[u64; STATE_LANES]]) {
    debug_assert_eq!(states.len(), S::WIDTH);
    // `buf[i * WIDTH + l]` is state `l`'s lane `i`.
    let mut buf = [0u64; STATE_LANES * MAX_WIDTH];
    for (l, state) in states.iter().enumerate() {
        for (i, &lane) in state.iter().enumerate() {
            buf[i * S::WIDTH + l] = lane;
        }
    }
    let mut st: [S; STATE_LANES] = std::array::from_fn(|i| S::load(&buf, i * S::WIDTH));
    permute(&mut st);
    for (i, lane) in st.iter().enumerate() {
        lane.store(&mut buf, i * S::WIDTH);
    }
    for (l, state) in states.iter_mut().enumerate() {
        for (i, lane) in state.iter_mut().enumerate() {
            *lane = buf[i * S::WIDTH + l];
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|i| ((i * 7 + 3) & 0xff) as u8).collect()
    }

    /// A known answer from OpenSSL's `keccak-256`.
    #[test]
    fn matches_reference_vector() {
        assert_eq!(
            hex(&hash(b"abc")),
            "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
        );
    }

    /// Ethereum's `keccak256`, as an independent implementation computes it, across both sides of
    /// every block boundary up to five blocks.
    #[test]
    fn matches_ethereum_keccak256() {
        use sha3::Digest;
        for n in (0..700).chain([1023, 1024, 1025, 4096]) {
            let data = pattern(n);
            assert_eq!(&hash(&data)[..], &sha3::Keccak256::digest(&data)[..], "{n} bytes");
        }
    }

    /// Any split of the input into `update` calls gives the same digest as the
    /// one-shot hash.
    #[test]
    fn streaming_matches_one_shot() {
        for n in [0usize, 1, 63, 135, 136, 137, 272, 577] {
            let data = pattern(n);
            let want = hash(&data);
            for split in [1usize, 7, 64, 136, 137] {
                let mut h = Hasher::new();
                for chunk in data.chunks(split) {
                    h.update(chunk);
                }
                assert_eq!(h.finalize(), want, "{n} bytes in {split}-byte updates");
            }
        }
    }

    /// Starting from a precomputed zero-prefix state reproduces the hash of the
    /// whole image, one input at a time and batched.
    #[test]
    fn continued_from_zero_prefix_matches_whole_image() {
        for zero_blocks in [0usize, 1, 3] {
            for rest in [0usize, 8, 64, 135, 136, 200, 408] {
                let zlen = zero_blocks * RATE;
                let state = zero_prefix_state(zero_blocks);
                for n in [1usize, 4, 17] {
                    let data: Vec<u8> = (0..n * rest).map(|i| (i * 31 + zero_blocks) as u8).collect();
                    let mut got = vec![0u8; n * OUT_LEN];
                    hash_many_from_state(&data, rest, &state, &mut got);
                    for i in 0..n {
                        let mut whole = vec![0u8; zlen];
                        whole.extend_from_slice(&data[i * rest..(i + 1) * rest]);
                        let want = hash(&whole);
                        assert_eq!(
                            &got[i * OUT_LEN..(i + 1) * OUT_LEN],
                            &want[..],
                            "batched {zero_blocks} {rest} {n}"
                        );
                        assert_eq!(hash_from_state(&data[i * rest..(i + 1) * rest], &state), want);
                    }
                }
            }
        }
    }

    /// Batched hashing agrees with the one-shot hash for tails of every shape, over whole groups.
    #[test]
    fn batched_matches_one_shot_across_lengths() {
        for len in [
            1usize, 7, 8, 9, 63, 64, 65, 100, 135, 136, 137, 200, 271, 272, 273, 300, 511, 512, 513,
        ] {
            let n = 24;
            let data: Vec<u8> = (0..n * len).map(|i| (i * 131 + len) as u8).collect();
            let mut got = vec![0u8; n * OUT_LEN];
            hash_many(&data, len, &mut got);
            let mut from_state = vec![0u8; n * OUT_LEN];
            hash_many_from_state(&data, len, &zero_prefix_state(1), &mut from_state);
            for i in 0..n {
                let input = &data[i * len..(i + 1) * len];
                assert_eq!(
                    &got[i * OUT_LEN..(i + 1) * OUT_LEN],
                    &hash(input)[..],
                    "len {len} input {i}"
                );
                let mut whole = vec![0u8; RATE];
                whole.extend_from_slice(input);
                assert_eq!(
                    &from_state[i * OUT_LEN..(i + 1) * OUT_LEN],
                    &hash(&whole)[..],
                    "prefixed len {len} input {i}"
                );
            }
        }
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    #[test]
    fn single_state_matches_portable_permutation() {
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        for case in 0..256 {
            let mut state = std::array::from_fn(|_| {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                match case {
                    0 => 0,
                    1 => u64::MAX,
                    _ => seed,
                }
            });
            let mut expected = state;
            permute(&mut expected);
            keccak_f(&mut state);
            assert_eq!(state, expected, "case {case}");
        }
    }

    /// Every SIMD backend compiled into this build agrees with the scalar hash and permutation,
    /// not just the one the dispatch picks.
    #[test]
    fn every_backend_matches_scalar() {
        fn check<S: Lanes64>(name: &str) {
            for n in [1usize, S::WIDTH, S::WIDTH + 1, 3 * S::WIDTH + 1] {
                for len in [0usize, 8, 64, 135, 136, 137, 272, 1024] {
                    let data: Vec<u8> = (0..n * len).map(|i| ((i * 37 + 11) & 0xff) as u8).collect();
                    let mut got = vec![0u8; n * OUT_LEN];
                    hash_many_with::<S>(&data, len, &[0; STATE_LANES], &mut got);
                    for i in 0..n {
                        assert_eq!(
                            &got[i * OUT_LEN..(i + 1) * OUT_LEN],
                            &hash(&data[i * len..(i + 1) * len])[..],
                            "{name}: input {i} of {n}, len {len}"
                        );
                    }
                }
            }
            let states: Vec<[u64; STATE_LANES]> = (0..S::WIDTH as u64)
                .map(|l| std::array::from_fn(|i| (l << 32) ^ (i as u64 * 0x9E37_79B9)))
                .collect();
            let mut got = states.clone();
            permute_group::<S>(&mut got);
            for (mut want, got) in states.into_iter().zip(got) {
                keccak_f(&mut want);
                assert_eq!(got, want, "{name}: permutation");
            }
        }
        check::<u64>("scalar");
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        check::<x86::Avx2>("avx2");
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        check::<x86::Avx512>("avx512");
        #[cfg(target_arch = "aarch64")]
        check::<arm::Neon>("neon");
    }
}
