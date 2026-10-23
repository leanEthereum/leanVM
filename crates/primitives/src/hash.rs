//! Keccak-256, the repo's one hash function: Ethereum's, which is the 256-bit hash of FIPS
//! 202 with Keccak's original padding.
//!
//! Three surfaces, in increasing order of how much of the machine they touch:
//!
//! - [`keccak_f`], the Keccak-f\[1600\] permutation, which the VM's `KECCAK` opcode computes
//!   and `keccak_gkr` proves, and [`absorb`], one sponge step (XOR a block into the rate,
//!   permute).
//! - [`hash`] / [`Hasher`], Keccak-256 over bytes.
//! - [`hash_many`], the batched form: `LANES` independent equal-length inputs
//!   hashed together with the state transposed across lanes, which is how the
//!   PCS Merkle tree gets SIMD out of hashes that are individually serial.
//!
//! The state is 25 little-endian 64-bit lanes, lane `x + 5y` holding
//! `A[x, y]`. The first [`RATE_LANES`] lanes are the rate: a message block is
//! XORed into them before each permutation, and the digest is read off the first
//! [`OUT_LANES`] of them after the last one.

/// Digest length in bytes. Keccak-256 throughout.
pub const OUT_LEN: usize = 32;
/// Digest length in lanes.
pub const OUT_LANES: usize = OUT_LEN / 8;
/// Sponge rate in bytes: `1600 - 2·256` bits.
pub const RATE: usize = 136;
/// Sponge rate in lanes.
pub const RATE_LANES: usize = RATE / 8;
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
/// # Safety
///
/// `load` and `store` take raw pointers to `WIDTH` contiguous `u64`, and
/// implementors may use unaligned vector accesses, so callers must keep those
/// `WIDTH` elements in bounds.
trait Lanes64: Copy {
    const WIDTH: usize;

    /// # Safety
    /// `p` must be valid for reads of `WIDTH` `u64`.
    unsafe fn load(p: *const u64) -> Self;
    /// # Safety
    /// `p` must be valid for writes of `WIDTH` `u64`.
    unsafe fn store(self, p: *mut u64);

    fn splat(x: u64) -> Self;
    fn xor(self, o: Self) -> Self;
    /// Rotate every lane left by `N`, `0 <= N < 64`.
    fn rotl<const N: i32>(self) -> Self;
    /// χ on one lane: `a ⊕ (¬b ∧ c)`.
    fn chi(a: Self, b: Self, c: Self) -> Self;

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
    unsafe fn load(p: *const u64) -> Self {
        unsafe { p.read_unaligned() }
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u64) {
        unsafe { p.write_unaligned(self) }
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

/// The Keccak-f\[1600\] permutation, in place.
///
/// With AVX-512 the scalar rounds are not [`permute`]'s: LLVM's SLP vectorizer turns its
/// straight-line round into a mesh of vector inserts and extracts, where the round below,
/// ρ and π as one in-place cycle, stays in general-purpose registers. Out of line, so a
/// caller holding the state in locals cannot hand the vectorizer the same chance. Without
/// AVX-512 the straight-line round stays scalar and is the faster of the two.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
#[inline(never)]
pub fn keccak_f(a: &mut [u64; STATE_LANES]) {
    /// The π cycle from lane 1, and the ρ rotation each lane takes on arriving.
    const CYCLE: [(usize, u32); STATE_LANES - 1] = {
        let mut cycle = [(0, 0); STATE_LANES - 1];
        let mut from = 1;
        let mut i = 0;
        while i < cycle.len() {
            cycle[i] = (PI[from], RHO[from]);
            from = PI[from];
            i += 1;
        }
        cycle
    };
    for &rc in &RC {
        let c: [u64; 5] = std::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                a[x + 5 * y] ^= d;
            }
        }
        let mut carried = a[1];
        for (to, rot) in CYCLE {
            carried = std::mem::replace(&mut a[to], carried.rotate_left(rot));
        }
        for row in a.as_chunks_mut::<5>().0 {
            let b = *row;
            for x in 0..5 {
                row[x] = b[x] ^ (!b[(x + 1) % 5] & b[(x + 2) % 5]);
            }
        }
        a[0] ^= rc;
    }
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
pub fn absorb(state: &mut [u64; STATE_LANES], block: &[u64; RATE_LANES]) {
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
pub fn final_block(tail: &[u8]) -> [u64; RATE_LANES] {
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
pub fn hash_from_state(data: &[u8], state: &[u64; STATE_LANES]) -> [u8; OUT_LEN] {
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
        unsafe fn load(p: *const u64) -> Self {
            Self(unsafe { _mm256_loadu_si256(p.cast()) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            unsafe { _mm256_storeu_si256(p.cast(), self.0) }
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
        unsafe fn load(p: *const u64) -> Self {
            Self(unsafe { _mm512_loadu_si512(p.cast()) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            unsafe { _mm512_storeu_si512(p.cast(), self.0) }
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
    }
}

#[cfg(target_arch = "aarch64")]
mod arm {
    use super::Lanes64;
    use core::arch::aarch64::*;

    /// NEON: two lanes. With the SHA3 extension, χ is one `BCAX`, the column
    /// parity two `EOR3` and θ's rotate-and-xor one `RAX1`.
    #[derive(Clone, Copy)]
    pub(super) struct Neon(uint64x2_t);

    impl Lanes64 for Neon {
        const WIDTH: usize = 2;

        #[inline(always)]
        unsafe fn load(p: *const u64) -> Self {
            Self(unsafe { vld1q_u64(p) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            unsafe { vst1q_u64(p, self.0) }
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

/// Inputs handled together by the widest backend. Batched entry points accept
/// any count and process the remainder serially.
pub const LANES: usize = if cfg!(all(target_arch = "x86_64", target_feature = "avx512f")) {
    8
} else if cfg!(all(target_arch = "x86_64", target_feature = "avx2")) {
    4
} else if cfg!(target_arch = "aarch64") {
    2
} else {
    1
};

/// Widest batch any backend takes.
const MAX_WIDTH: usize = 8;

/// Hash `S::WIDTH` inputs of `len` bytes starting at `inputs[l]`, from the shared
/// sponge state `init`, writing the digests consecutively to `out`.
///
/// # Safety
/// Every `inputs[l]` must be valid for `len` readable bytes, and `out` for
/// `S::WIDTH * OUT_LEN` writable bytes.
#[inline(always)]
unsafe fn hash_group<S: Lanes64>(inputs: &[*const u8], len: usize, init: &[u64; STATE_LANES], out: *mut u8) {
    debug_assert_eq!(inputs.len(), S::WIDTH);
    let mut st: [S; STATE_LANES] = std::array::from_fn(|i| S::splat(init[i]));
    // `buf[w * WIDTH + l]` is input `l`'s lane `w` of the current block.
    let mut buf = [0u64; RATE_LANES * MAX_WIDTH];
    // XOR the first `n` lanes of `buf` into the rate.
    let xor_buf = |st: &mut [S; STATE_LANES], buf: &[u64], n: usize| {
        for (w, lane) in st[..n].iter_mut().enumerate() {
            // SAFETY: `buf` holds RATE_LANES * MAX_WIDTH >= (w + 1) * WIDTH words.
            *lane = lane.xor(unsafe { S::load(buf.as_ptr().add(w * S::WIDTH)) });
        }
    };
    let (blocks, tail) = (len / RATE, len % RATE);
    for blk in 0..blocks {
        for (l, &input) in inputs.iter().enumerate() {
            for w in 0..RATE_LANES {
                // SAFETY: the block lies inside the input's `len` bytes.
                let word = unsafe { input.add(blk * RATE + 8 * w).cast::<u64>().read_unaligned() };
                buf[w * S::WIDTH + l] = u64::from_le(word);
            }
        }
        xor_buf(&mut st, &buf, RATE_LANES);
        permute(&mut st);
    }
    // The final block, read in place: its words, then the padding, which every input has in the same lanes.
    let (words, part) = (tail / 8, tail % 8);
    for (l, &input) in inputs.iter().enumerate() {
        // SAFETY: the final block is the input's last `tail` bytes.
        let input = unsafe { input.add(blocks * RATE) };
        for w in 0..words {
            // SAFETY: as above.
            let word = unsafe { input.add(8 * w).cast::<u64>().read_unaligned() };
            buf[w * S::WIDTH + l] = u64::from_le(word);
        }
        if part > 0 {
            // SAFETY: as above.
            let byte = |j: usize| u64::from(unsafe { *input.add(8 * words + j) }) << (8 * j);
            buf[words * S::WIDTH + l] = (0..part).fold(0, |acc, j| acc | byte(j));
        }
    }
    xor_buf(&mut st, &buf, words + usize::from(part > 0));
    st[words] = st[words].xor(S::splat(u64::from(PAD_FIRST) << (8 * part)));
    st[RATE_LANES - 1] = st[RATE_LANES - 1].xor(S::splat(END_BIT));
    permute(&mut st);
    let mut lanes = [0u64; OUT_LANES * MAX_WIDTH];
    for (w, lane) in st[..OUT_LANES].iter().enumerate() {
        // SAFETY: `lanes` holds OUT_LANES * MAX_WIDTH >= (w + 1) * WIDTH words.
        unsafe { lane.store(lanes.as_mut_ptr().add(w * S::WIDTH)) };
    }
    for l in 0..S::WIDTH {
        for w in 0..OUT_LANES {
            let bytes = lanes[w * S::WIDTH + l].to_le_bytes();
            // SAFETY: `l * 32 + 8 * w + 8 <= WIDTH * 32`.
            unsafe { out.add(l * OUT_LEN + 8 * w).copy_from_nonoverlapping(bytes.as_ptr(), 8) };
        }
    }
}

/// The batched hash over one backend.
///
/// # Safety
/// `data.len() == n * len` and `out.len() == n * OUT_LEN` for some `n`.
#[inline(always)]
unsafe fn hash_many_with<S: Lanes64>(data: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [u8]) {
    let n = out.len() / OUT_LEN;
    let groups = n / S::WIDTH;
    let mut ptrs = [core::ptr::null::<u8>(); MAX_WIDTH];
    for g in 0..groups {
        let base = g * S::WIDTH;
        for (l, slot) in ptrs[..S::WIDTH].iter_mut().enumerate() {
            *slot = data[(base + l) * len..].as_ptr();
        }
        // SAFETY: each pointer has `len` readable bytes, and the output window
        // `[base, base + WIDTH)` is inside `out`.
        unsafe { hash_group::<S>(&ptrs[..S::WIDTH], len, state, out.as_mut_ptr().add(base * OUT_LEN)) };
    }
    for i in groups * S::WIDTH..n {
        let d = hash_from_state(&data[i * len..(i + 1) * len], state);
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&d);
    }
}

/// Batched Keccak-256 of `data` split into `LEN`-byte inputs, writing one 32-byte
/// digest per input to `out`. Byte-identical to [`hash`] per input; the batching
/// only changes how the lanes are scheduled.
pub fn hash_many<const LEN: usize>(data: &[u8], out: &mut [u8]) {
    hash_many_dyn(data, LEN, out);
}

/// [`hash_many`] with the input length known only at runtime.
pub fn hash_many_dyn(data: &[u8], len: usize, out: &mut [u8]) {
    hash_many_dyn_from_state(data, len, &[0; STATE_LANES], out);
}

/// [`hash_many_dyn`] continued from one sponge state shared by every input, as
/// [`hash_from_state`] is to [`hash`], under its precondition. Byte-identical to
/// hashing each full image.
pub fn hash_many_dyn_from_state(data: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [u8]) {
    let n = out.len() / OUT_LEN;
    assert_eq!(out.len(), n * OUT_LEN);
    assert_eq!(data.len(), n * len);
    // SAFETY (each arm): the asserts above pin the buffer sizes the backends
    // require, and every backend is gated on the feature its intrinsics need.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    unsafe {
        hash_many_with::<x86::Avx512>(data, len, state, out)
    }
    #[cfg(all(target_arch = "x86_64", not(target_feature = "avx512f"), target_feature = "avx2"))]
    unsafe {
        hash_many_with::<x86::Avx2>(data, len, state, out)
    }
    #[cfg(target_arch = "aarch64")]
    unsafe {
        hash_many_with::<arm::Neon>(data, len, state, out)
    }
    #[cfg(not(any(all(target_arch = "x86_64", target_feature = "avx2"), target_arch = "aarch64")))]
    unsafe {
        hash_many_with::<u64>(data, len, state, out)
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

    /// Known answers from OpenSSL's `keccak-256`.
    #[test]
    fn matches_reference_vectors() {
        assert_eq!(
            hex(&hash(b"abc")),
            "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
        );
        for (n, expected) in [
            (
                0usize,
                "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
            ),
            (1, "69c322e3248a5dfc29d73c5b0553b0185a35cd5bb6386747517ef7e53b15e287"),
            (63, "48d8e506b57c81c8257a8e1da7f04610191ef05bf96fa9dc4fb9bca39bbed2c6"),
            (64, "0251cf13aa5b18f1cbda7cddbe85f3dc536fc93df590c2d20ca9b28af1ed2c39"),
            (127, "fa3cd4a949bae0f7690ff5c8cbc6dc0332d192d790ab4d80dc97ba37b6569deb"),
            (128, "1c51c71b758998e7b841d7abde03b6f2b3e76b0313ed687269c30e16bb3aa488"),
        ] {
            assert_eq!(hex(&hash(&pattern(n))), expected, "{n} bytes");
        }
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
                    hash_many_dyn_from_state(&data, rest, &state, &mut got);
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

    /// Every SIMD backend compiled into this build agrees with the scalar hash,
    /// not just the one the dispatch picks.
    #[test]
    fn every_backend_matches_scalar() {
        fn check<S: Lanes64>(name: &str) {
            for n in [1usize, S::WIDTH, S::WIDTH + 1, 3 * S::WIDTH + 1] {
                for len in [0usize, 8, 64, 135, 136, 137, 272, 1024] {
                    let data: Vec<u8> = (0..n * len).map(|i| ((i * 37 + 11) & 0xff) as u8).collect();
                    let mut got = vec![0u8; n * OUT_LEN];
                    // SAFETY: `data` holds `n * len` bytes and `got` `n * 32`.
                    unsafe { hash_many_with::<S>(&data, len, &[0; STATE_LANES], &mut got) };
                    for i in 0..n {
                        assert_eq!(
                            &got[i * OUT_LEN..(i + 1) * OUT_LEN],
                            &hash(&data[i * len..(i + 1) * len])[..],
                            "{name}: input {i} of {n}, len {len}"
                        );
                    }
                }
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
