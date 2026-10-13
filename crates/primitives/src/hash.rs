//! SHA3-256 (FIPS 202), the repo's one hash function.
//!
//! Three surfaces, in increasing order of how much of the machine they touch:
//!
//! - [`keccak_f`], the Keccak-f\[1600\] permutation. Every hash in leanVM is a
//!   sponge over it, and it is what the VM's `SHA3` opcode computes and
//!   `keccak_gkr` proves.
//! - [`hash`] / [`Hasher`], SHA3-256 over bytes, in the cell encoding that
//!   makes a VM block eight whole 16-byte cells (plain SHA3-256 up to 128 bytes).
//! - [`hash_many`], the batched form: `LANES` independent equal-length inputs
//!   hashed together with the state transposed across lanes, which is how the
//!   PCS Merkle tree gets SIMD out of hashes that are individually serial.
//!
//! The state is 25 little-endian 64-bit lanes, lane `x + 5y` holding
//! `A[x, y]`. The first [`RATE_LANES`] lanes are the rate: a message block is
//! XORed into them before each permutation, and the digest is read off the first
//! [`OUT_LANES`] of them after the last one.

/// Digest length in bytes. SHA3-256 throughout.
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

/// SHA3's domain-separation suffix `01`, with the first bit of the `10*1`
/// padding, as the byte XORed right after the message.
pub const PAD_FIRST: u8 = 0x06;
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
#[inline(always)]
fn permute<S: Lanes64>(a: &mut [S; STATE_LANES]) {
    for &rc in &RC {
        let c: [S; 5] = std::array::from_fn(|x| S::xor5(a[x], a[x + 5], a[x + 10], a[x + 15], a[x + 20]));
        let d: [S; 5] = std::array::from_fn(|x| S::theta_d(c[(x + 4) % 5], c[(x + 1) % 5]));
        let mut b = [a[0]; STATE_LANES];
        // ρ and π together: lane `i` rotated by `RHO[i]` lands at `PI[i]`.
        b[0] = a[0].xor(d[0]);
        b[10] = a[1].xor(d[1]).rotl::<1>();
        b[20] = a[2].xor(d[2]).rotl::<62>();
        b[5] = a[3].xor(d[3]).rotl::<28>();
        b[15] = a[4].xor(d[4]).rotl::<27>();
        b[16] = a[5].xor(d[0]).rotl::<36>();
        b[1] = a[6].xor(d[1]).rotl::<44>();
        b[11] = a[7].xor(d[2]).rotl::<6>();
        b[21] = a[8].xor(d[3]).rotl::<55>();
        b[6] = a[9].xor(d[4]).rotl::<20>();
        b[7] = a[10].xor(d[0]).rotl::<3>();
        b[17] = a[11].xor(d[1]).rotl::<10>();
        b[2] = a[12].xor(d[2]).rotl::<43>();
        b[12] = a[13].xor(d[3]).rotl::<25>();
        b[22] = a[14].xor(d[4]).rotl::<39>();
        b[23] = a[15].xor(d[0]).rotl::<41>();
        b[8] = a[16].xor(d[1]).rotl::<45>();
        b[18] = a[17].xor(d[2]).rotl::<15>();
        b[3] = a[18].xor(d[3]).rotl::<21>();
        b[13] = a[19].xor(d[4]).rotl::<8>();
        b[14] = a[20].xor(d[0]).rotl::<18>();
        b[24] = a[21].xor(d[1]).rotl::<2>();
        b[9] = a[22].xor(d[2]).rotl::<61>();
        b[19] = a[23].xor(d[3]).rotl::<56>();
        b[4] = a[24].xor(d[4]).rotl::<14>();
        for y in 0..5 {
            let r = 5 * y;
            a[r] = S::chi(b[r], b[r + 1], b[r + 2]);
            a[r + 1] = S::chi(b[r + 1], b[r + 2], b[r + 3]);
            a[r + 2] = S::chi(b[r + 2], b[r + 3], b[r + 4]);
            a[r + 3] = S::chi(b[r + 3], b[r + 4], b[r]);
            a[r + 4] = S::chi(b[r + 4], b[r], b[r + 1]);
        }
        a[0] = a[0].xor(S::splat(rc));
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
#[inline]
pub fn keccak_f(state: &mut [u64; STATE_LANES]) {
    permute(state);
}

/// The last padding bit as it sits in lane 16, the rate's last lane.
pub const END_BIT: u64 = (PAD_LAST as u64) << 56;
/// The rate lane [`END_BIT`] lives in.
pub const END_LANE: usize = RATE_LANES - 1;
/// Message bytes one block of the cell encoding carries: the rate's first 16
/// lanes, eight whole 16-byte VM cells.
pub const CHUNK: usize = 128;
/// [`CHUNK`] in lanes.
pub const CHUNK_LANES: usize = CHUNK / 8;

/// One step of the cell sponge (see [`hash`]): XOR [`END_BIT`] into lane 16 and
/// permute. This is the relation the VM's `SHA3` opcode computes and `keccak_gkr`
/// proves. Its caller has already XORed the block's message into lanes `0..16`
/// (and, for a final block, the padding's first bit), while lane 16 carries the
/// previous state untouched: the step supplies the one bit every block puts
/// there.
#[inline]
pub fn step(input: &[u64; STATE_LANES]) -> [u64; STATE_LANES] {
    let mut state = *input;
    state[END_LANE] ^= END_BIT;
    keccak_f(&mut state);
    state
}

/// One sponge step: XOR the rate block `block` into `state` and permute.
#[inline]
fn absorb(state: &mut [u64; STATE_LANES], block: &[u64; RATE_LANES]) {
    for (s, b) in state.iter_mut().zip(block) {
        *s ^= b;
    }
    keccak_f(state);
}

/// A non-final block of the cell encoding: 128 message bytes, then the gap
/// `0^56 ‖ 0x80` in lane 16.
#[inline]
fn chunk_block(chunk: &[u8; CHUNK]) -> [u64; RATE_LANES] {
    std::array::from_fn(|i| {
        if i < CHUNK_LANES {
            u64::from_le_bytes(chunk[8 * i..8 * i + 8].try_into().unwrap())
        } else {
            END_BIT
        }
    })
}

/// The final block: the last `tail.len() <= CHUNK` message bytes, then SHA3's
/// suffix and padding, as rate lanes.
#[inline]
pub fn final_block(tail: &[u8]) -> [u64; RATE_LANES] {
    assert!(tail.len() <= CHUNK, "a final block holds at most CHUNK message bytes");
    let mut bytes = [0u8; RATE];
    bytes[..tail.len()].copy_from_slice(tail);
    bytes[tail.len()] ^= PAD_FIRST;
    bytes[RATE - 1] ^= PAD_LAST;
    std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
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

/// How a message of `len` bytes splits into blocks: the non-final 128-byte
/// chunks, and the length of the final one, in `0..=CHUNK` (zero only for the
/// empty message).
#[inline]
fn chunks_of(len: usize) -> (usize, usize) {
    let nonfinal = len.saturating_sub(1) / CHUNK;
    (nonfinal, len - nonfinal * CHUNK)
}

/// Streaming [`hash`].
///
/// The final block may be a full chunk, which is padded where a non-final one
/// takes the gap, so the hasher holds a full buffer back until it knows more
/// input follows.
#[derive(Clone)]
pub struct Hasher {
    state: [u64; STATE_LANES],
    buf: [u8; CHUNK],
    /// Bytes currently in `buf`, in `0..=CHUNK`.
    buf_len: usize,
}

impl Hasher {
    pub fn new() -> Self {
        Self {
            state: [0; STATE_LANES],
            buf: [0; CHUNK],
            buf_len: 0,
        }
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            if self.buf_len == CHUNK {
                absorb(&mut self.state, &chunk_block(&self.buf));
                self.buf_len = 0;
            }
            let take = (CHUNK - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
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

/// SHA3-256 of `data` under the cell encoding, the one hash of leanVM.
///
/// For inputs of at most [`CHUNK`] = 128 bytes this is plain SHA3-256. A longer
/// input is cut into 128-byte chunks, the last holding the remaining 1 to 128
/// bytes, and every chunk but the last is followed by the fixed 8-byte gap
/// `00 00 00 00 00 00 00 80`; the result is SHA3-256 of that byte string. The
/// encoding is injective, and it is what lets the VM absorb eight whole 16-byte
/// cells per permutation where SHA3's 136-byte rate would split a cell across two
/// blocks: the gap is lane 16, the one lane the opcode supplies itself
/// ([`step`]).
pub fn hash(data: &[u8]) -> [u8; OUT_LEN] {
    hash_from_state(data, &[0; STATE_LANES])
}

/// The state after absorbing `n_chunks` all-zero non-final chunks.
///
/// A leaf image that starts with whole zero chunks (the PCS's absent interleaving
/// lanes) shares that prefix with every other leaf, so the committer computes this
/// once and starts each leaf's sponge here. Nothing about the digest changes: a
/// prefix's permutations depend on nothing after them, so the result is still the
/// hash of the whole image.
pub fn zero_prefix_state(n_chunks: usize) -> [u64; STATE_LANES] {
    let mut state = [0; STATE_LANES];
    for _ in 0..n_chunks {
        state = step(&state);
    }
    state
}

/// [`hash`] continued from a sponge state that has absorbed whole non-final
/// chunks (see [`zero_prefix_state`]): `data` is the rest of the message, and
/// must not be empty.
pub fn hash_from_state(data: &[u8], state: &[u64; STATE_LANES]) -> [u8; OUT_LEN] {
    let mut state = *state;
    let (nonfinal, tail) = chunks_of(data.len());
    for chunk in data[..nonfinal * CHUNK].as_chunks::<CHUNK>().0 {
        absorb(&mut state, &chunk_block(chunk));
    }
    absorb(
        &mut state,
        &final_block(&data[nonfinal * CHUNK..nonfinal * CHUNK + tail]),
    );
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

#[cfg(target_arch = "x86_64")]
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
    let absorb_buf = |st: &mut [S; STATE_LANES], buf: &[u64]| {
        for (w, lane) in st[..RATE_LANES].iter_mut().enumerate() {
            // SAFETY: `buf` holds RATE_LANES * MAX_WIDTH >= (w + 1) * WIDTH words.
            *lane = lane.xor(unsafe { S::load(buf.as_ptr().add(w * S::WIDTH)) });
        }
        permute(st);
    };
    let (nonfinal, tail) = chunks_of(len);
    for w in CHUNK_LANES..RATE_LANES {
        for l in 0..S::WIDTH {
            buf[w * S::WIDTH + l] = END_BIT;
        }
    }
    for blk in 0..nonfinal {
        for (l, &input) in inputs.iter().enumerate() {
            for w in 0..CHUNK_LANES {
                // SAFETY: the chunk lies inside the input's `len` bytes.
                let word = unsafe { input.add(blk * CHUNK + 8 * w).cast::<u64>().read_unaligned() };
                buf[w * S::WIDTH + l] = u64::from_le(word);
            }
        }
        absorb_buf(&mut st, &buf);
    }
    for (l, &input) in inputs.iter().enumerate() {
        // SAFETY: the final chunk is the input's last `tail` bytes.
        let bytes = unsafe { std::slice::from_raw_parts(input.add(nonfinal * CHUNK), tail) };
        for (w, lane) in final_block(bytes).into_iter().enumerate() {
            buf[w * S::WIDTH + l] = lane;
        }
    }
    absorb_buf(&mut st, &buf);
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

/// Batched SHA3-256 of `data` split into `LEN`-byte inputs, writing one 32-byte
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
/// [`hash_from_state`] is to [`hash`]. Byte-identical to hashing each full image.
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

    /// Known answers from `hashlib.sha3_256`, of the input itself up to 128 bytes
    /// and of its cell encoding past that (`0^7 ‖ 0x80` after every 128 bytes but
    /// the last chunk). They span the empty input, both sides of the chunk
    /// boundary (128 puts the padding's first bit in lane 16), SHA3's own rate
    /// boundary, and multi-chunk inputs.
    #[test]
    fn matches_reference_vectors() {
        assert_eq!(
            hex(&hash(b"abc")),
            "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
        );
        for (n, expected) in [
            (
                0usize,
                "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a",
            ),
            (1, "e3ed56bd086d8958483a12734fa0ae7f5c8bb160ef9092c67e82ed9b19e4c7b2"),
            (63, "1275539a6596eb01fbc83a54af2f2994aa7ea8beb0b0d440ae07c620ad8eaa9f"),
            (64, "85c576bd8097a119432293d7b09da76d336aff9acda1c0708cf03bdd999911cd"),
            (127, "31578857f28c795c37ceb9bfffd3d24267d338e622927ae128330a5b07f22358"),
            (128, "fcb6ea7388b68266e5df9f9beaf980fca55fdc6393f4d97ce1bcb2096eb4a975"),
            (129, "3d0568183e17ed0ec5b304b306aa437a3f7105708312b88c81ac264ebe8e06ef"),
            (135, "4917e5da7a7d49b75b6e47bf9f7bf9efd73ce13d5fa591ad011065b9d720b5fb"),
            (136, "bc36c66b09b3db7f509d93baf09257f2393637b1784d5471103ad1ede347adcb"),
            (256, "9f74f1dc5390ddded8afd18a85997428435b11eaa9d97a7961c767e72b765e13"),
            (257, "71674412fe9842dcf4549f649fb12e8518b2363a399cb6ae28f9983c46b1de1e"),
            (1024, "6e7e70062c9f9875658a66998d5821194b4f2b0b1e285fba91241937ee98bd35"),
        ] {
            assert_eq!(hex(&hash(&pattern(n))), expected, "{n} bytes");
        }
    }

    /// A hash is the chain of [`step`]s the VM runs: message XORed into lanes
    /// `0..16`, the padding's first bit placed by the caller, lane 16 left to the
    /// step.
    #[test]
    fn hash_is_a_chain_of_steps() {
        for n in [0usize, 48, 127, 128, 129, 300, 384] {
            let data = pattern(n);
            let (nonfinal, tail) = chunks_of(n);
            let mut state = [0u64; STATE_LANES];
            for c in 0..=nonfinal {
                let len = if c == nonfinal { tail } else { CHUNK };
                let mut bytes = [0u8; RATE];
                bytes[..len].copy_from_slice(&data[c * CHUNK..c * CHUNK + len]);
                if c == nonfinal {
                    bytes[len] ^= PAD_FIRST;
                }
                for (i, lane) in state[..RATE_LANES].iter_mut().enumerate() {
                    *lane ^= u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap());
                }
                state = step(&state);
            }
            assert_eq!(digest_of(&state), hash(&data), "{n} bytes");
        }
    }

    /// Any split of the input into `update` calls gives the same digest as the
    /// one-shot hash.
    #[test]
    fn streaming_matches_one_shot() {
        for n in [0usize, 1, 63, 64, 127, 128, 129, 256, 577] {
            let data = pattern(n);
            let want = hash(&data);
            for split in [1usize, 7, 64, 128, 129] {
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
        for zero_chunks in [0usize, 1, 3] {
            for rest in [8usize, 64, 128, 200, 384] {
                let zlen = zero_chunks * CHUNK;
                let state = zero_prefix_state(zero_chunks);
                for n in [1usize, 4, 17] {
                    let data: Vec<u8> = (0..n * rest).map(|i| (i * 31 + zero_chunks) as u8).collect();
                    let mut got = vec![0u8; n * OUT_LEN];
                    hash_many_dyn_from_state(&data, rest, &state, &mut got);
                    for i in 0..n {
                        let mut whole = vec![0u8; zlen];
                        whole.extend_from_slice(&data[i * rest..(i + 1) * rest]);
                        let want = hash(&whole);
                        assert_eq!(
                            &got[i * OUT_LEN..(i + 1) * OUT_LEN],
                            &want[..],
                            "batched {zero_chunks} {rest} {n}"
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
                for len in [0usize, 8, 64, 128, 129, 192, 1024] {
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
