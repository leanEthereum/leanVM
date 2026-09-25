//! BLAKE2s (RFC 7693), the VM's hash function (SPHINCS+'s Keccak is [`crate::keccak`]).
//!
//! Three surfaces, in increasing order of how much of the machine they touch:
//!
//! - [`compress`], the 10-round compression. Every other BLAKE2s hash is a
//!   chain of these, and it is the one the VM's `Blake2s` opcode computes and
//!   `flock::hash` proves.
//! - [`hash`] / [`keyed_hash`] / [`Hasher`], ordinary BLAKE2s-256 over bytes.
//! - [`hash_many`], the batched form: `LANES` independent equal-length inputs
//!   hashed together with the state transposed across lanes, which is how the
//!   PCS Merkle tree gets SIMD out of hashes that are individually serial.
//!
//! Why BLAKE2s: the VM proves one compression per opcode, and BLAKE2s takes the
//! byte counter and the final-block flag as ordinary compression inputs, so one
//! opcode is a complete hash of any length. A hash whose multi-block mode is a
//! tree of chunks, with its own counters, flags and parent nodes, would instead
//! need that whole structure reproduced in-circuit.

/// BLAKE2s initial values: the SHA-256 IV.
pub const IV: [u32; 8] = [
    0x6A09_E667,
    0xBB67_AE85,
    0x3C6E_F372,
    0xA54F_F53A,
    0x510E_527F,
    0x9B05_688C,
    0x1F83_D9AB,
    0x5BE0_CD19,
];

/// Digest length in bytes. BLAKE2s-256 throughout.
pub const OUT_LEN: usize = 32;
/// Compression block length in bytes.
pub const BLOCK_LEN: usize = 64;
/// Rounds per compression.
pub const ROUNDS: usize = 10;

/// BLAKE2s message schedule.
pub const SIGMA: [[usize; 16]; ROUNDS] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

/// Lanes touched by G index `g` within a round: `[a, b, c, d]`.
pub const G_LANES: [[usize; 4]; 8] = [
    [0, 4, 8, 12],
    [1, 5, 9, 13],
    [2, 6, 10, 14],
    [3, 7, 11, 15],
    [0, 5, 10, 15],
    [1, 6, 11, 12],
    [2, 7, 8, 13],
    [3, 4, 9, 14],
];

/// The parameter block folded into `h[0]` for an unkeyed BLAKE2s-256:
/// digest length 32, key length 0, fanout 1, depth 1.
pub const PARAM_UNKEYED: u32 = 0x0101_0000 ^ OUT_LEN as u32;

/// The initial chaining value for a `key_len`-byte key (0 = unkeyed).
#[inline]
pub const fn init_state(key_len: usize) -> [u32; 8] {
    assert!(key_len <= 32, "BLAKE2s key is at most 32 bytes");
    let mut h = IV;
    h[0] ^= 0x0101_0000 ^ ((key_len as u32) << 8) ^ OUT_LEN as u32;
    h
}

/// The unkeyed BLAKE2s-256 initial chaining value: [`IV`] with the parameter
/// block folded into word 0. Hashing exactly 64 bytes is one [`compress`] from
/// this state at counter 64 with the final flag, which is what makes the VM's
/// one-compression opcode a complete hash.
pub const PARAM_IV: [u32; 8] = init_state(0);

/// The BLAKE2s compression: absorb one 64-byte block `m` at byte counter `t`
/// into the chaining value `h`. `last` sets the final-block flag `f0`.
///
/// This is the whole nonlinear core of every hash in leanVM. The `f1`
/// last-node flag is always zero: nothing here uses BLAKE2s's tree mode.
#[inline]
pub fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    if last {
        v[14] = !v[14];
    }
    for round in &SIGMA {
        for (g, &[a, b, c, d]) in G_LANES.iter().enumerate() {
            let (mx, my) = (m[round[2 * g]], m[round[2 * g + 1]]);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(mx);
            v[d] = (v[d] ^ v[a]).rotate_right(16);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(12);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(my);
            v[d] = (v[d] ^ v[a]).rotate_right(8);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(7);
        }
    }
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

/// Read a 64-byte block as 16 little-endian words.
#[inline]
fn block_words(block: &[u8; BLOCK_LEN]) -> [u32; 16] {
    std::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()))
}

/// Serialize a chaining value as the 32-byte digest.
#[inline]
fn state_bytes(h: &[u32; 8]) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];
    for (chunk, word) in out.as_chunks_mut::<4>().0.iter_mut().zip(h) {
        *chunk = word.to_le_bytes();
    }
    out
}

/// Streaming BLAKE2s-256.
///
/// The final block has to be compressed with the `last` flag, so the hasher
/// holds a full 64-byte buffer back until it knows more input follows. That is
/// the only subtlety; everything else is a straight block loop.
#[derive(Clone)]
pub struct Hasher {
    h: [u32; 8],
    buf: [u8; BLOCK_LEN],
    /// Bytes currently in `buf`, in `0..=BLOCK_LEN`.
    buf_len: usize,
    /// Bytes already compressed.
    counter: u64,
}

impl Hasher {
    pub fn new() -> Self {
        Self {
            h: init_state(0),
            buf: [0u8; BLOCK_LEN],
            buf_len: 0,
            counter: 0,
        }
    }

    /// Keyed BLAKE2s-256 (RFC 7693 §2.9): the zero-padded key is the first
    /// block. `key` must be at most 32 bytes.
    pub fn new_keyed(key: &[u8]) -> Self {
        assert!(key.len() <= 32, "BLAKE2s key is at most 32 bytes");
        let mut s = Self {
            h: init_state(key.len()),
            buf: [0u8; BLOCK_LEN],
            buf_len: 0,
            counter: 0,
        };
        if !key.is_empty() {
            // The key block counts toward the byte counter and is a full block
            // even when the key is shorter.
            s.buf[..key.len()].copy_from_slice(key);
            s.buf_len = BLOCK_LEN;
        }
        s
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            if self.buf_len == BLOCK_LEN {
                // More input follows, so this buffered block is not the last.
                self.counter += BLOCK_LEN as u64;
                compress(&mut self.h, &block_words(&self.buf), self.counter, false);
                self.buf_len = 0;
            }
            let take = (BLOCK_LEN - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
        }
        self
    }

    pub fn finalize(&self) -> [u8; OUT_LEN] {
        let mut h = self.h;
        let mut block = self.buf;
        block[self.buf_len..].fill(0);
        let t = self.counter + self.buf_len as u64;
        compress(&mut h, &block_words(&block), t, true);
        state_bytes(&h)
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

/// One-shot unkeyed BLAKE2s-256.
pub fn hash(data: &[u8]) -> [u8; OUT_LEN] {
    // Fast path for the shapes the protocol actually hashes in bulk: a whole
    // number of blocks, no buffering needed.
    if !data.is_empty() && data.len().is_multiple_of(BLOCK_LEN) {
        let mut h = init_state(0);
        let n = data.len() / BLOCK_LEN;
        for (b, block) in data.as_chunks::<BLOCK_LEN>().0.iter().enumerate() {
            let t = ((b + 1) * BLOCK_LEN) as u64;
            compress(&mut h, &block_words(block), t, b + 1 == n);
        }
        return state_bytes(&h);
    }
    let mut hasher = Hasher::new();
    hasher.update(data);
    hasher.finalize()
}

/// One-shot keyed BLAKE2s-256, the PRF form. `key` is at most 32 bytes.
pub fn keyed_hash(key: &[u8], data: &[u8]) -> [u8; OUT_LEN] {
    let mut hasher = Hasher::new_keyed(key);
    hasher.update(data);
    hasher.finalize()
}

// ---------------------------------------------------------------------------
// Batched (transposed) hashing
//
// `LANES` independent inputs are hashed together with the state transposed
// across lanes: state word `i` becomes one SIMD vector holding that word for
// every lane, so a round is elementwise 32-bit work with no cross-lane traffic.
// Independent hashes of equal-length inputs step their block counters in
// lockstep, which is what lets one vector counter serve the whole batch.
//
// The generic compression is instantiated per backend. Literal `SIGMA` indices avoid runtime cross-lane lookup, and keeping message blocks in memory avoids register spills.
//
// Whether that is enough depends on how the backend's vectors relate to the
// chain through one G function, which is what [`Lanes32::GROUPS`] exists for: a
// narrow backend runs out of independent work before it runs out of issue
// width, and then a second group has to be interleaved by hand.
// ---------------------------------------------------------------------------

/// One state word across all lanes of a batch: a vector of `WIDTH` 32-bit
/// lanes. The batched compression is written once over this trait, so each
/// backend supplies only add / xor / the four BLAKE2s rotations.
///
/// # Safety
///
/// `load` and `store` take raw pointers to `WIDTH` contiguous `u32`, and
/// implementors may use unaligned vector accesses, so callers must keep those
/// `WIDTH` elements in bounds.
trait Lanes32: Copy {
    const WIDTH: usize;

    /// Whether to drive two groups at once through [`compress_pair`].
    ///
    /// A round is 8 G functions, but only 4 of them are independent: the
    /// diagonal four consume the column four's outputs. So one group offers
    /// `4 * insns(G)` instructions of work per `chain(G)` cycles of latency, and
    /// can keep at most `4 * insns(G) / chain(G)` pipes busy. On NEON that is
    /// `4 * 16 / 28` = 2.3 against 4 pipes, so a single 4-lane group leaves a
    /// third of the width idle; a 16-lane vector carries enough work per
    /// instruction that AVX-512 does not.
    ///
    /// Interleaving requires `16 * GROUPS * WIDTH <= 2 * 16 * 16`, since the
    /// groups split the one transposed block buffer.
    const GROUPS: usize = 1;

    /// Load `WIDTH` contiguous `u32`.
    ///
    /// # Safety
    /// `p` must be valid for reads of `WIDTH` `u32`.
    unsafe fn load(p: *const u32) -> Self;

    /// Store `WIDTH` contiguous `u32`.
    ///
    /// # Safety
    /// `p` must be valid for writes of `WIDTH` `u32`.
    unsafe fn store(self, p: *mut u32);

    fn splat(x: u32) -> Self;
    fn add(self, o: Self) -> Self;
    fn xor(self, o: Self) -> Self;
    /// Rotate every lane right by `N`, `N` one of BLAKE2s's 16, 12, 8, 7.
    fn rotr<const N: u32>(self) -> Self;

    /// Transpose one 64-byte block from each of `WIDTH` inputs into `buf`, so
    /// that `buf[w * WIDTH + l]` is lane `l`'s word `w`.
    ///
    /// The default reads word by word, which the compiler turns into strided
    /// vector gathers: 32 `vpgatherqd` per block, enough to cost more than the
    /// ten rounds it feeds. Backends with a shuffle network override it.
    ///
    /// Write the finished chaining values out as `WIDTH` consecutive 32-byte
    /// digests: the reverse transpose of [`Lanes32::transpose`], over 8 words
    /// rather than 16.
    ///
    /// # Safety
    /// `out` must be valid for writes of `WIDTH * OUT_LEN` bytes.
    #[inline(always)]
    unsafe fn store_digests(h: &[Self; 8], out: *mut u8) {
        let mut words = [0u32; 8 * 16];
        for (i, hi) in h.iter().enumerate() {
            // SAFETY: `words` holds 8 * 16 >= 8 * WIDTH elements.
            unsafe { hi.store(words.as_mut_ptr().add(i * Self::WIDTH)) };
        }
        for lane in 0..Self::WIDTH {
            for i in 0..8 {
                let bytes = words[i * Self::WIDTH + lane].to_le_bytes();
                // SAFETY: `lane * 32 + i * 4 + 4 <= WIDTH * 32`.
                unsafe {
                    out.add(lane * OUT_LEN + 4 * i)
                        .copy_from_nonoverlapping(bytes.as_ptr(), 4)
                };
            }
        }
    }

    /// # Safety
    /// Every `inputs[l]` must be valid for 64 readable bytes at `off`, and
    /// `buf` must hold `16 * WIDTH` words.
    #[inline(always)]
    unsafe fn transpose(inputs: &[*const u8], off: usize, buf: &mut [u32]) {
        debug_assert_eq!(inputs.len(), Self::WIDTH);
        debug_assert!(buf.len() >= 16 * Self::WIDTH);
        for (lane, &input) in inputs.iter().enumerate() {
            for w in 0..16 {
                // SAFETY: the caller guarantees 64 readable bytes at `off`.
                let word = unsafe { input.add(off + 4 * w).cast::<u32>().read_unaligned() };
                buf[w * Self::WIDTH + lane] = word.to_le();
            }
        }
    }
}

/// The portable backend, and the reference the SIMD ones are checked against.
///
/// Unused by the library whenever a SIMD backend is available for the target,
/// since the dispatch is resolved at compile time, but always exercised by
/// `every_backend_matches_scalar`.
#[allow(dead_code)]
#[derive(Clone, Copy)]
struct Scalar8([u32; 8]);

impl Lanes32 for Scalar8 {
    const WIDTH: usize = 8;

    #[inline(always)]
    unsafe fn load(p: *const u32) -> Self {
        Self(std::array::from_fn(|i| unsafe { *p.add(i) }))
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u32) {
        for (i, x) in self.0.into_iter().enumerate() {
            unsafe { *p.add(i) = x };
        }
    }
    #[inline(always)]
    fn splat(x: u32) -> Self {
        Self([x; 8])
    }
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i].wrapping_add(o.0[i])))
    }
    #[inline(always)]
    fn xor(self, o: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i] ^ o.0[i]))
    }
    #[inline(always)]
    fn rotr<const N: u32>(self) -> Self {
        Self(std::array::from_fn(|i| self.0[i].rotate_right(N)))
    }
}

#[cfg(target_arch = "x86_64")]
mod x86 {
    use super::Lanes32;
    // Only `Avx512::store_digests` uses it, and that impl is gated too.
    #[cfg(target_feature = "avx512f")]
    use super::OUT_LEN;
    use core::arch::x86_64::*;

    /// AVX2: eight lanes. There is no 32-bit vector rotate before AVX-512, so
    /// the two byte-aligned rotations become one `vpshufb` and the other two a
    /// shift pair; that asymmetry is why BLAKE2's rotation set is 16/12/8/7.
    ///
    /// Unused by the library on an AVX-512 target (the dispatch is compile
    /// time), but always exercised by `every_backend_matches_scalar`.
    #[cfg_attr(target_feature = "avx512f", allow(dead_code))]
    #[derive(Clone, Copy)]
    pub(super) struct Avx2(__m256i);

    impl Lanes32 for Avx2 {
        const WIDTH: usize = 8;

        #[inline(always)]
        unsafe fn load(p: *const u32) -> Self {
            Self(unsafe { _mm256_loadu_si256(p.cast()) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u32) {
            unsafe { _mm256_storeu_si256(p.cast(), self.0) }
        }
        #[inline(always)]
        fn splat(x: u32) -> Self {
            Self(unsafe { _mm256_set1_epi32(x as i32) })
        }
        #[inline(always)]
        fn add(self, o: Self) -> Self {
            Self(unsafe { _mm256_add_epi32(self.0, o.0) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            Self(unsafe { _mm256_xor_si256(self.0, o.0) })
        }
        #[inline(always)]
        fn rotr<const N: u32>(self) -> Self {
            // `vpshufb` masks for a 2-byte and a 1-byte right rotation of each
            // 32-bit lane, given per 16-byte half.
            const ROT16: [i8; 16] = [2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13];
            const ROT8: [i8; 16] = [1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12];
            unsafe {
                let shuf = |m: [i8; 16]| {
                    let half = _mm_loadu_si128(m.as_ptr().cast());
                    Self(_mm256_shuffle_epi8(self.0, _mm256_set_m128i(half, half)))
                };
                match N {
                    16 => shuf(ROT16),
                    8 => shuf(ROT8),
                    12 => Self(_mm256_or_si256(
                        _mm256_srli_epi32(self.0, 12),
                        _mm256_slli_epi32(self.0, 20),
                    )),
                    7 => Self(_mm256_or_si256(
                        _mm256_srli_epi32(self.0, 7),
                        _mm256_slli_epi32(self.0, 25),
                    )),
                    _ => unreachable!("BLAKE2s rotates by 16, 12, 8 or 7"),
                }
            }
        }

        /// Two 8x8 32-bit transposes: each input's 64-byte block is two `ymm`,
        /// words 0..8 and 8..16, and each half transposes independently.
        #[inline(always)]
        unsafe fn transpose(inputs: &[*const u8], off: usize, buf: &mut [u32]) {
            debug_assert_eq!(inputs.len(), 8);
            debug_assert!(buf.len() >= 128);
            unsafe {
                for half in 0..2 {
                    let r: [__m256i; 8] =
                        std::array::from_fn(|l| _mm256_loadu_si256(inputs[l].add(off + 32 * half).cast()));
                    let mut t = [_mm256_setzero_si256(); 8];
                    for k in 0..4 {
                        t[2 * k] = _mm256_unpacklo_epi32(r[2 * k], r[2 * k + 1]);
                        t[2 * k + 1] = _mm256_unpackhi_epi32(r[2 * k], r[2 * k + 1]);
                    }
                    let s: [__m256i; 8] = [
                        _mm256_unpacklo_epi64(t[0], t[2]),
                        _mm256_unpackhi_epi64(t[0], t[2]),
                        _mm256_unpacklo_epi64(t[1], t[3]),
                        _mm256_unpackhi_epi64(t[1], t[3]),
                        _mm256_unpacklo_epi64(t[4], t[6]),
                        _mm256_unpackhi_epi64(t[4], t[6]),
                        _mm256_unpacklo_epi64(t[5], t[7]),
                        _mm256_unpackhi_epi64(t[5], t[7]),
                    ];
                    for k in 0..4 {
                        let w = 8 * half + k;
                        _mm256_storeu_si256(
                            buf.as_mut_ptr().add(w * 8).cast(),
                            _mm256_permute2x128_si256(s[k], s[k + 4], 0x20),
                        );
                        _mm256_storeu_si256(
                            buf.as_mut_ptr().add((w + 4) * 8).cast(),
                            _mm256_permute2x128_si256(s[k], s[k + 4], 0x31),
                        );
                    }
                }
            }
        }
    }

    /// AVX-512: sixteen lanes, and `vprold` makes every rotation one
    /// instruction.
    #[cfg(target_feature = "avx512f")]
    #[derive(Clone, Copy)]
    pub(super) struct Avx512(__m512i);

    #[cfg(target_feature = "avx512f")]
    impl Lanes32 for Avx512 {
        const WIDTH: usize = 16;

        #[inline(always)]
        unsafe fn load(p: *const u32) -> Self {
            Self(unsafe { _mm512_loadu_si512(p.cast()) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u32) {
            unsafe { _mm512_storeu_si512(p.cast(), self.0) }
        }
        #[inline(always)]
        fn splat(x: u32) -> Self {
            Self(unsafe { _mm512_set1_epi32(x as i32) })
        }
        #[inline(always)]
        fn add(self, o: Self) -> Self {
            Self(unsafe { _mm512_add_epi32(self.0, o.0) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            Self(unsafe { _mm512_xor_si512(self.0, o.0) })
        }
        #[inline(always)]
        fn rotr<const N: u32>(self) -> Self {
            unsafe {
                match N {
                    16 => Self(_mm512_ror_epi32(self.0, 16)),
                    12 => Self(_mm512_ror_epi32(self.0, 12)),
                    8 => Self(_mm512_ror_epi32(self.0, 8)),
                    7 => Self(_mm512_ror_epi32(self.0, 7)),
                    _ => unreachable!("BLAKE2s rotates by 16, 12, 8 or 7"),
                }
            }
        }

        /// An 8x16 -> 16x8 transpose for the digests. Phases 1 and 2 of the
        /// block network over eight rows leave lane `4L + c`'s first four words
        /// in `s[c]`'s 128-bit lane `L` and its last four in `s[4 + c]`'s, so
        /// each digest is two 128-bit extracts rather than eight scalar stores.
        #[inline(always)]
        unsafe fn store_digests(h: &[Self; 8], out: *mut u8) {
            unsafe {
                let mut s = [_mm512_setzero_si512(); 8];
                for a in 0..2 {
                    let (r0, r1, r2, r3) = (h[4 * a].0, h[4 * a + 1].0, h[4 * a + 2].0, h[4 * a + 3].0);
                    let lo01 = _mm512_unpacklo_epi32(r0, r1);
                    let hi01 = _mm512_unpackhi_epi32(r0, r1);
                    let lo23 = _mm512_unpacklo_epi32(r2, r3);
                    let hi23 = _mm512_unpackhi_epi32(r2, r3);
                    s[4 * a] = _mm512_unpacklo_epi64(lo01, lo23);
                    s[4 * a + 1] = _mm512_unpackhi_epi64(lo01, lo23);
                    s[4 * a + 2] = _mm512_unpacklo_epi64(hi01, hi23);
                    s[4 * a + 3] = _mm512_unpackhi_epi64(hi01, hi23);
                }
                macro_rules! lane {
                    ($l:expr, $c:expr) => {{
                        let p = out.add((4 * $l + $c) * OUT_LEN);
                        _mm_storeu_si128(p.cast(), _mm512_extracti32x4_epi32::<$l>(s[$c]));
                        _mm_storeu_si128(p.add(16).cast(), _mm512_extracti32x4_epi32::<$l>(s[4 + $c]));
                    }};
                }
                lane!(0, 0);
                lane!(0, 1);
                lane!(0, 2);
                lane!(0, 3);
                lane!(1, 0);
                lane!(1, 1);
                lane!(1, 2);
                lane!(1, 3);
                lane!(2, 0);
                lane!(2, 1);
                lane!(2, 2);
                lane!(2, 3);
                lane!(3, 0);
                lane!(3, 1);
                lane!(3, 2);
                lane!(3, 3);
            }
        }

        /// A 16x16 32-bit transpose: each input's 64-byte block is exactly one
        /// `zmm`, so the block loads are sixteen full-width loads and the
        /// transpose is a shuffle network. Two `unpack` phases put four rows'
        /// worth of one column into each 128-bit lane, then two
        /// `shuffle_i32x4` phases collect the four row groups.
        #[inline(always)]
        unsafe fn transpose(inputs: &[*const u8], off: usize, buf: &mut [u32]) {
            debug_assert_eq!(inputs.len(), 16);
            debug_assert!(buf.len() >= 256);
            unsafe {
                let r: [__m512i; 16] = std::array::from_fn(|l| _mm512_loadu_si512(inputs[l].add(off).cast()));
                // Phase 1 and 2: `s[4 * a + c]`'s 128-bit lane L holds column
                // `4L + c` of rows `4a .. 4a + 4`.
                let mut s = [_mm512_setzero_si512(); 16];
                for a in 0..4 {
                    let (r0, r1, r2, r3) = (r[4 * a], r[4 * a + 1], r[4 * a + 2], r[4 * a + 3]);
                    let lo01 = _mm512_unpacklo_epi32(r0, r1);
                    let hi01 = _mm512_unpackhi_epi32(r0, r1);
                    let lo23 = _mm512_unpacklo_epi32(r2, r3);
                    let hi23 = _mm512_unpackhi_epi32(r2, r3);
                    s[4 * a] = _mm512_unpacklo_epi64(lo01, lo23);
                    s[4 * a + 1] = _mm512_unpackhi_epi64(lo01, lo23);
                    s[4 * a + 2] = _mm512_unpacklo_epi64(hi01, hi23);
                    s[4 * a + 3] = _mm512_unpackhi_epi64(hi01, hi23);
                }
                // Word `w` needs 128-bit lane `w / 4` of the four `s` entries
                // whose `c` is `w % 4`. `IMM_L` broadcasts that lane, and 0x88
                // then takes lanes 0 and 2 of each half.
                macro_rules! word {
                    ($w:expr) => {{
                        const L: i32 = ($w / 4) as i32;
                        const C: usize = ($w % 4) as usize;
                        const IMM_L: i32 = L * 0x55;
                        let p = _mm512_shuffle_i32x4::<IMM_L>(s[C], s[4 + C]);
                        let q = _mm512_shuffle_i32x4::<IMM_L>(s[8 + C], s[12 + C]);
                        _mm512_storeu_si512(
                            buf.as_mut_ptr().add($w * 16).cast(),
                            _mm512_shuffle_i32x4::<0x88>(p, q),
                        );
                    }};
                }
                word!(0);
                word!(1);
                word!(2);
                word!(3);
                word!(4);
                word!(5);
                word!(6);
                word!(7);
                word!(8);
                word!(9);
                word!(10);
                word!(11);
                word!(12);
                word!(13);
                word!(14);
                word!(15);
            }
        }
    }
}

#[cfg(target_arch = "aarch64")]
mod arm {
    use super::{Lanes32, OUT_LEN};
    use core::arch::aarch64::*;

    /// NEON: four lanes, which is narrow enough that the G function's
    /// dependency chain, and not the four SIMD pipes, is what bounds this
    /// backend. Hence [`Lanes32::GROUPS`], and hence picking each rotation for
    /// latency in [`rot4`] rather than for instruction count.
    #[derive(Clone, Copy)]
    pub(super) struct Neon(uint32x4_t);

    impl Lanes32 for Neon {
        const WIDTH: usize = 4;
        // Interleave independent groups to cover the G function's dependency chain.
        const GROUPS: usize = 4;

        #[inline(always)]
        unsafe fn load(p: *const u32) -> Self {
            Self(unsafe { vld1q_u32(p) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u32) {
            unsafe { vst1q_u32(p, self.0) }
        }
        #[inline(always)]
        fn splat(x: u32) -> Self {
            Self(unsafe { vdupq_n_u32(x) })
        }
        #[inline(always)]
        fn add(self, o: Self) -> Self {
            Self(unsafe { vaddq_u32(self.0, o.0) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            Self(unsafe { veorq_u32(self.0, o.0) })
        }
        #[inline(always)]
        fn rotr<const N: u32>(self) -> Self {
            Self(rot4::<N>(self.0))
        }

        /// Four 4x4 32-bit transposes. Quarter `q` of every lane's block holds
        /// words `4q..4q+4`, which is 64 contiguous bytes of `buf`, so each
        /// quarter transposes independently: `trn` on 32-bit elements then on
        /// 64-bit ones.
        #[inline(always)]
        unsafe fn transpose(inputs: &[*const u8], off: usize, buf: &mut [u32]) {
            debug_assert_eq!(inputs.len(), 4);
            debug_assert!(buf.len() >= 64);
            unsafe {
                // `vld1q_u32` would claim 4-byte alignment, which a `&[u8]`
                // input does not have; the `u8` form is the unaligned load, and
                // the same instruction.
                let r: [uint32x4_t; 16] =
                    std::array::from_fn(|i| vreinterpretq_u32_u8(vld1q_u8(inputs[i / 4].add(off + 16 * (i % 4)))));
                for q in 0..4 {
                    let [a, b, c, d] = [r[q], r[4 + q], r[8 + q], r[12 + q]];
                    for (j, o) in transpose4(a, b, c, d).into_iter().enumerate() {
                        vst1q_u32(buf.as_mut_ptr().add(16 * q + 4 * j), o);
                    }
                }
            }
        }

        /// The same network over the eight chaining words: `h[0..4]` gives each
        /// lane's first 16 digest bytes and `h[4..8]` its second.
        #[inline(always)]
        unsafe fn store_digests(h: &[Self; 8], out: *mut u8) {
            unsafe {
                for half in 0..2 {
                    let [a, b, c, d] = [h[4 * half], h[4 * half + 1], h[4 * half + 2], h[4 * half + 3]];
                    for (lane, o) in transpose4(a.0, b.0, c.0, d.0).into_iter().enumerate() {
                        // Unaligned, as in `transpose`: `out` is bytes.
                        vst1q_u8(out.add(lane * OUT_LEN + 16 * half), vreinterpretq_u8_u32(o));
                    }
                }
            }
        }
    }

    /// Choose low-latency NEON rotations because each lies on the G function's dependency chain.
    #[inline(always)]
    fn rot4<const N: u32>(v: uint32x4_t) -> uint32x4_t {
        unsafe {
            match N {
                16 => vreinterpretq_u32_u16(vrev32q_u16(vreinterpretq_u16_u32(v))),
                8 => {
                    /// Byte `4l + j` of the result is byte `4l + (j + 1) % 4` of
                    /// the input: a rotation right by one byte within each
                    /// 32-bit element. Loop invariant, so this load is hoisted.
                    static ROT8: [u8; 16] = [1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12];
                    vreinterpretq_u32_u8(vqtbl1q_u8(vreinterpretq_u8_u32(v), vld1q_u8(ROT8.as_ptr())))
                }
                12 => rot_sri::<12, 20>(v),
                7 => rot_sri::<7, 25>(v),
                _ => unreachable!("BLAKE2s rotates by 16, 12, 8 or 7"),
            }
        }
    }

    /// `shl` then `sri`, kept in assembly because LLVM otherwise selects an accumulating form with a longer dependency chain.
    #[inline(always)]
    fn rot_sri<const N: u32, const SHL: i32>(v: uint32x4_t) -> uint32x4_t {
        unsafe {
            let mut out = vshlq_n_u32::<SHL>(v);
            std::arch::asm!(
                "sri {out:v}.4s, {v:v}.4s, #{n}",
                out = inout(vreg) out,
                v = in(vreg) v,
                n = const N,
                options(pure, nomem, nostack)
            );
            out
        }
    }

    /// Transpose four vectors of four 32-bit words: `out[j][i]` is `in[i][j]`.
    #[inline(always)]
    fn transpose4(a: uint32x4_t, b: uint32x4_t, c: uint32x4_t, d: uint32x4_t) -> [uint32x4_t; 4] {
        unsafe {
            let (ab0, ab1) = (vtrn1q_u32(a, b), vtrn2q_u32(a, b));
            let (cd0, cd1) = (vtrn1q_u32(c, d), vtrn2q_u32(c, d));
            let pair = |x, y| {
                (
                    vreinterpretq_u32_u64(vtrn1q_u64(vreinterpretq_u64_u32(x), vreinterpretq_u64_u32(y))),
                    vreinterpretq_u32_u64(vtrn2q_u64(vreinterpretq_u64_u32(x), vreinterpretq_u64_u32(y))),
                )
            };
            let ((o0, o2), (o1, o3)) = (pair(ab0, cd0), pair(ab1, cd1));
            [o0, o1, o2, o3]
        }
    }
}

/// The G function and the round over LITERAL state and message indices, then
/// all ten rounds. `$m` is a `*const u32` to the transposed block, so each
/// message operand is a load at a constant offset rather than a register.
macro_rules! g {
    ($v:ident, $m:ident, $a:expr, $b:expr, $c:expr, $d:expr, $x:expr, $y:expr) => {{
        $v[$a] = $v[$a].add($v[$b]).add(S::load($m.add($x * S::WIDTH)));
        $v[$d] = $v[$d].xor($v[$a]).rotr::<16>();
        $v[$c] = $v[$c].add($v[$d]);
        $v[$b] = $v[$b].xor($v[$c]).rotr::<12>();
        $v[$a] = $v[$a].add($v[$b]).add(S::load($m.add($y * S::WIDTH)));
        $v[$d] = $v[$d].xor($v[$a]).rotr::<8>();
        $v[$c] = $v[$c].add($v[$d]);
        $v[$b] = $v[$b].xor($v[$c]).rotr::<7>();
    }};
}

macro_rules! round {
    ($v:ident, $m:ident, [$s0:expr, $s1:expr, $s2:expr, $s3:expr, $s4:expr, $s5:expr, $s6:expr, $s7:expr,
      $s8:expr, $s9:expr, $s10:expr, $s11:expr, $s12:expr, $s13:expr, $s14:expr, $s15:expr]) => {{
        g!($v, $m, 0, 4, 8, 12, $s0, $s1);
        g!($v, $m, 1, 5, 9, 13, $s2, $s3);
        g!($v, $m, 2, 6, 10, 14, $s4, $s5);
        g!($v, $m, 3, 7, 11, 15, $s6, $s7);
        g!($v, $m, 0, 5, 10, 15, $s8, $s9);
        g!($v, $m, 1, 6, 11, 12, $s10, $s11);
        g!($v, $m, 2, 7, 8, 13, $s12, $s13);
        g!($v, $m, 3, 4, 9, 14, $s14, $s15);
    }};
}

/// The ten rounds as ten `#[inline(never)]` functions over a state in memory,
/// for [`compress_pair`].
macro_rules! round_fns {
    ($($name:ident [$($s:expr),*],)*) => {
        $(
            /// # Safety
            /// `m` must be valid for reads of `16 * S::WIDTH` `u32`.
            #[inline(never)]
            unsafe fn $name<S: Lanes32>(v: &mut [S; 16], m: *const u32) {
                unsafe { round!(v, m, [$($s),*]) }
            }
        )*
    };
}

round_fns! {
    round_0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    round_1 [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    round_2 [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    round_3 [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    round_4 [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    round_5 [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    round_6 [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    round_7 [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    round_8 [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    round_9 [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
}

macro_rules! rounds {
    ($v:ident, $m:ident) => {{
        round!($v, $m, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
        round!($v, $m, [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3]);
        round!($v, $m, [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4]);
        round!($v, $m, [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8]);
        round!($v, $m, [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13]);
        round!($v, $m, [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9]);
        round!($v, $m, [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11]);
        round!($v, $m, [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10]);
        round!($v, $m, [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5]);
        round!($v, $m, [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]);
    }};
}

/// One transposed compression across `S::WIDTH` lanes. `m` points to the
/// block as 16 groups of `S::WIDTH` words (state word `w`, lane `l`, at
/// `m[w * WIDTH + l]`). `t` and `last` are shared across the batch.
///
/// # Safety
/// `m` must be valid for reads of `16 * S::WIDTH` `u32`.
#[inline(always)]
unsafe fn compress_lanes<S: Lanes32>(h: &mut [S; 8], m: *const u32, t: u64, last: bool) {
    let mut v = [
        h[0],
        h[1],
        h[2],
        h[3],
        h[4],
        h[5],
        h[6],
        h[7],
        S::splat(IV[0]),
        S::splat(IV[1]),
        S::splat(IV[2]),
        S::splat(IV[3]),
        S::splat(IV[4] ^ t as u32),
        S::splat(IV[5] ^ (t >> 32) as u32),
        S::splat(if last { !IV[6] } else { IV[6] }),
        S::splat(IV[7]),
    ];
    unsafe { rounds!(v, m) };
    for i in 0..8 {
        h[i] = h[i].xor(v[i]).xor(v[i + 8]);
    }
}

/// Two independent groups, one round at a time each, with both working states
/// in memory rather than in registers.
///
/// This is the only way to interleave two groups on a 32-register machine. The
/// obvious form, a backend twice as wide (two vectors per state word), needs 32
/// state vectors live across a round, which is the whole NEON register file, so
/// the allocator spills and the reloads land on the very chain the interleaving
/// was meant to hide, so it buys back only a fraction of what this one does.
///
/// So the rounds are `#[inline(never)]` instead. Each call loads its 16 state
/// vectors, does its 128 instructions and stores 16 back, which keeps one
/// group's round inside the register file; the two calls are independent, so the
/// second one's work fills the first one's stalls. It costs 32 memory ops per
/// round per group, about a fifth of the instruction stream, and the store to
/// load round trip between rounds sits on the chain. Both are worth paying: the
/// chain had that much slack.
///
/// # Safety
/// `ma` and `mb` must each be valid for reads of `16 * S::WIDTH` `u32`.
#[inline(always)]
unsafe fn compress_groups<S: Lanes32, const G: usize>(h: &mut [[S; 8]; G], m: [*const u32; G], t: u64, last: bool) {
    let init = |h: &[S; 8]| {
        [
            h[0],
            h[1],
            h[2],
            h[3],
            h[4],
            h[5],
            h[6],
            h[7],
            S::splat(IV[0]),
            S::splat(IV[1]),
            S::splat(IV[2]),
            S::splat(IV[3]),
            S::splat(IV[4] ^ t as u32),
            S::splat(IV[5] ^ (t >> 32) as u32),
            S::splat(if last { !IV[6] } else { IV[6] }),
            S::splat(IV[7]),
        ]
    };
    let mut v: [[S; 16]; G] = std::array::from_fn(|g| init(&h[g]));
    // SAFETY: the caller guarantees every block.
    unsafe {
        macro_rules! round_all {
            ($($name:ident),*) => { $( for g in 0..G { $name(&mut v[g], m[g]); } )* };
        }
        round_all!(
            round_0, round_1, round_2, round_3, round_4, round_5, round_6, round_7, round_8, round_9
        );
    }
    for g in 0..G {
        for i in 0..8 {
            h[g][i] = h[g][i].xor(v[g][i]).xor(v[g][i + 8]);
        }
    }
}

/// [`hash_group`] over `G` groups at once, interleaved round by round.
///
/// # Safety
/// As [`hash_group`], for every group; `buf` must hold `16 * G * S::WIDTH`
/// words, the groups' transposed blocks.
#[inline(always)]
unsafe fn hash_groups<S: Lanes32, const G: usize>(
    inputs: &[[*const u8; 16]; G],
    len: usize,
    state: &[u32; 8],
    t_offset: u64,
    buf: &mut [u32],
    out: *mut u8,
) {
    let mut h: [[S; 8]; G] = [std::array::from_fn(|i| S::splat(state[i])); G];
    let n_blocks = len / BLOCK_LEN;
    let words = 16 * S::WIDTH;
    for blk in 0..n_blocks {
        // SAFETY: `blk < n_blocks` keeps the 64-byte window inside every input,
        // and the `G` windows of `buf` are disjoint.
        unsafe {
            let mut m = [std::ptr::null::<u32>(); G];
            for g in 0..G {
                let b = &mut buf[g * words..(g + 1) * words];
                S::transpose(&inputs[g][..S::WIDTH], blk * BLOCK_LEN, b);
                m[g] = b.as_ptr();
            }
            compress_groups::<S, G>(
                &mut h,
                m,
                t_offset + ((blk + 1) * BLOCK_LEN) as u64,
                blk + 1 == n_blocks,
            );
        }
    }
    // SAFETY: the caller guarantees `G * WIDTH * OUT_LEN` writable bytes.
    unsafe {
        for g in 0..G {
            S::store_digests(&h[g], out.add(g * S::WIDTH * OUT_LEN));
        }
    }
}

/// Hash `S::WIDTH` inputs of `len` bytes (a nonzero multiple of 64) into
/// `S::WIDTH` consecutive 32-byte digests at `out`.
///
/// # Safety
/// Every `inputs[l]` must be valid for `len` bytes, `out` for
/// `S::WIDTH * OUT_LEN` bytes, `buf` must hold `16 * S::WIDTH` words, and `len`
/// must be a nonzero multiple of 64.
#[inline(always)]
unsafe fn hash_group<S: Lanes32>(
    inputs: &[*const u8],
    len: usize,
    state: &[u32; 8],
    t_offset: u64,
    buf: &mut [u32],
    out: *mut u8,
) {
    debug_assert!(len > 0 && len.is_multiple_of(BLOCK_LEN));
    let mut h: [S; 8] = std::array::from_fn(|i| S::splat(state[i]));
    let n_blocks = len / BLOCK_LEN;
    for b in 0..n_blocks {
        // SAFETY: `b < n_blocks` keeps the 64-byte window inside every input.
        unsafe {
            S::transpose(inputs, b * BLOCK_LEN, buf);
            compress_lanes::<S>(
                &mut h,
                buf.as_ptr(),
                t_offset + ((b + 1) * BLOCK_LEN) as u64,
                b + 1 == n_blocks,
            );
        }
    }
    // SAFETY: the caller guarantees `WIDTH * OUT_LEN` writable bytes at `out`.
    unsafe { S::store_digests(&h, out) };
}

/// Drive the whole batch through one backend, scalar-tailing the last partial
/// group.
///
/// # Safety
/// `data` must hold `n * len` bytes and `out` `n * OUT_LEN`, with `len` a
/// nonzero multiple of 64.
/// The widest interleave any backend asks for.
const MAX_GROUPS: usize = 4;

#[inline(always)]
unsafe fn hash_many_with<S: Lanes32>(data: &[u8], len: usize, state: &[u32; 8], t_offset: u64, out: &mut [u8]) {
    let n = out.len() / OUT_LEN;
    let groups = n / S::WIDTH;
    let mut ptrs = [std::ptr::null::<u8>(); 16];
    // Room for two transposed blocks of the widest backend, 16 words by 16
    // lanes, since `PAIR` splits this in half. One buffer for the whole call
    // keeps the block on the stack, so the round's message operands are memory
    // loads, without paying to clear it per group.
    let mut buf = [0u32; 2 * 16 * 16];
    let mut g = 0;
    if S::GROUPS > 1 {
        let mut wide = [[std::ptr::null::<u8>(); 16]; MAX_GROUPS];
        while g + S::GROUPS <= groups {
            let base = g * S::WIDTH;
            for (gi, row) in wide[..S::GROUPS].iter_mut().enumerate() {
                for (l, slot) in row[..S::WIDTH].iter_mut().enumerate() {
                    *slot = data[(base + gi * S::WIDTH + l) * len..].as_ptr();
                }
            }
            // SAFETY: as the single-group call below, for every group.
            unsafe {
                let out_g = out.as_mut_ptr().add(base * OUT_LEN);
                match S::GROUPS {
                    4 => hash_groups::<S, 4>(wide[..4].try_into().unwrap(), len, state, t_offset, &mut buf, out_g),
                    2 => hash_groups::<S, 2>(wide[..2].try_into().unwrap(), len, state, t_offset, &mut buf, out_g),
                    _ => unreachable!("GROUPS is 1, 2 or 4"),
                }
            }
            g += S::GROUPS;
        }
    }
    for g in g..groups {
        let base = g * S::WIDTH;
        for (l, slot) in ptrs[..S::WIDTH].iter_mut().enumerate() {
            *slot = data[(base + l) * len..].as_ptr();
        }
        // SAFETY: each pointer has `len` readable bytes, and the output window
        // `[base, base + WIDTH)` is inside `out`.
        unsafe {
            hash_group::<S>(
                &ptrs[..S::WIDTH],
                len,
                state,
                t_offset,
                &mut buf,
                out.as_mut_ptr().add(base * OUT_LEN),
            );
        }
    }
    for i in groups * S::WIDTH..n {
        let d = hash_from_state(&data[i * len..(i + 1) * len], state, t_offset);
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&d);
    }
}

/// Inputs handled together by the widest backend. Batched entry points accept any count and process the remainder serially.
pub const LANES: usize = if cfg!(all(target_arch = "x86_64", target_feature = "avx512f")) {
    16
} else if cfg!(target_arch = "x86_64") {
    8
} else if cfg!(target_arch = "aarch64") {
    4
} else {
    8
};

/// Batched BLAKE2s-256 of `data` split into `LEN`-byte inputs, writing one
/// 32-byte digest per input to `out`.
///
/// Byte-identical to [`hash`] per input; the batching only changes how the
/// lanes are scheduled. `LEN` must be a nonzero multiple of 64.
pub fn hash_many<const LEN: usize>(data: &[u8], out: &mut [u8]) {
    const {
        assert!(LEN > 0 && LEN.is_multiple_of(BLOCK_LEN));
    }
    hash_many_dyn(data, LEN, out);
}

/// The chaining value after absorbing `n_blocks` all-zero 64-byte blocks from the
/// unkeyed IV.
///
/// A leaf image that starts with whole zero blocks (the PCS's absent interleaving
/// lanes) shares that prefix with every other leaf, so the committer computes this
/// once and starts each leaf's chain here. Nothing about the digest changes: a
/// prefix's compressions depend on nothing after them, so the result is still the
/// standard BLAKE2s of the whole image.
pub fn zero_prefix_state(n_blocks: usize) -> [u32; 8] {
    let mut h = init_state(0);
    for b in 0..n_blocks {
        compress(&mut h, &[0u32; 16], ((b + 1) * BLOCK_LEN) as u64, false);
    }
    h
}

/// [`hash`] continued from a chaining value: `data` is the rest of the image, a
/// nonzero whole number of blocks, and `t_offset` the bytes already absorbed into
/// `state` (see [`zero_prefix_state`]).
pub fn hash_from_state(data: &[u8], state: &[u32; 8], t_offset: u64) -> [u8; OUT_LEN] {
    assert!(
        !data.is_empty() && data.len().is_multiple_of(BLOCK_LEN),
        "a continued image is whole blocks"
    );
    let mut h = *state;
    let n = data.len() / BLOCK_LEN;
    for (b, block) in data.as_chunks::<BLOCK_LEN>().0.iter().enumerate() {
        let t = t_offset + ((b + 1) * BLOCK_LEN) as u64;
        compress(&mut h, &block_words(block), t, b + 1 == n);
    }
    state_bytes(&h)
}

/// [`hash_many_dyn`] continued from one chaining value shared by every input, as
/// [`hash_from_state`] is to [`hash`]. Byte-identical to hashing each full image.
pub fn hash_many_dyn_from_state(data: &[u8], len: usize, state: &[u32; 8], t_offset: u64, out: &mut [u8]) {
    assert!(
        len > 0 && len.is_multiple_of(BLOCK_LEN),
        "batched inputs are whole blocks"
    );
    let n = out.len() / OUT_LEN;
    assert_eq!(data.len(), n * len);
    assert_eq!(out.len(), n * OUT_LEN);
    // SAFETY (each arm): the asserts above pin the buffer sizes the backends
    // require, and every backend is gated on the feature its intrinsics need.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    unsafe {
        hash_many_with::<x86::Avx512>(data, len, state, t_offset, out)
    }
    #[cfg(all(target_arch = "x86_64", not(target_feature = "avx512f"), target_feature = "avx2"))]
    unsafe {
        hash_many_with::<x86::Avx2>(data, len, state, t_offset, out)
    }
    #[cfg(target_arch = "aarch64")]
    unsafe {
        hash_many_with::<arm::Neon>(data, len, state, t_offset, out)
    }
    #[cfg(not(any(all(target_arch = "x86_64", target_feature = "avx2"), target_arch = "aarch64")))]
    unsafe {
        hash_many_with::<Scalar8>(data, len, state, t_offset, out)
    }
}

/// [`hash_many`] with the input length known only at runtime. Same contract:
/// `len` a nonzero multiple of 64.
pub fn hash_many_dyn(data: &[u8], len: usize, out: &mut [u8]) {
    hash_many_dyn_from_state(data, len, &PARAM_IV, 0, out);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Starting from a precomputed zero-prefix state must reproduce the standard
    /// hash of the whole image, one leaf at a time and batched, at leaf counts that
    /// cross the widest backend's group width and its scalar tail.
    #[test]
    fn continued_from_zero_prefix_matches_whole_image() {
        for zero_blocks in [0usize, 1, 3, 7] {
            for rest_blocks in [1usize, 2, 5] {
                let (zlen, rlen) = (zero_blocks * BLOCK_LEN, rest_blocks * BLOCK_LEN);
                let state = zero_prefix_state(zero_blocks);
                for n in [1usize, 4, 17, 33] {
                    let rest: Vec<u8> = (0..n * rlen).map(|i| (i * 31 + zero_blocks) as u8).collect();
                    let mut got = vec![0u8; n * OUT_LEN];
                    hash_many_dyn_from_state(&rest, rlen, &state, zlen as u64, &mut got);
                    for i in 0..n {
                        let mut whole = vec![0u8; zlen];
                        whole.extend_from_slice(&rest[i * rlen..(i + 1) * rlen]);
                        let want = hash(&whole);
                        assert_eq!(
                            &got[i * OUT_LEN..(i + 1) * OUT_LEN],
                            &want[..],
                            "batched, zero_blocks={zero_blocks} rest_blocks={rest_blocks} n={n} i={i}"
                        );
                        assert_eq!(
                            hash_from_state(&rest[i * rlen..(i + 1) * rlen], &state, zlen as u64),
                            want,
                            "scalar, zero_blocks={zero_blocks} rest_blocks={rest_blocks}"
                        );
                    }
                }
            }
        }
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|i| ((i * 7 + 3) & 0xff) as u8).collect()
    }

    /// Known answers from `hashlib.blake2s`, spanning empty, sub-block,
    /// exactly-one-block, block+1 (the case that pins the held-back-buffer
    /// rule) and multi-block inputs.
    #[test]
    fn matches_reference_vectors() {
        for (n, expected) in [
            (
                0usize,
                "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9",
            ),
            (1, "a28ac19d6bcbe2cd1d7de183485768d598e996b07889b9b11f418cb1b4a4fb0d"),
            (63, "de27df0e375d83c49f1af9ca8270f9f2fe7b70bf800fc01672db0e9746021ebf"),
            (64, "5377e4ff957bda4d4535f4879876b71a61056c4cec31e78397c66ec47a86a130"),
            (65, "19b1b26fba093f4a670d8913e1b71cbb2916dfa701018cc6b05785c966593374"),
            (127, "6846f99493436241d0a6f289c9a911b1d0f4860db8f2b5df5295ffd37d03a3c4"),
            (128, "83470c75afa23d90cd7659906e4b47daa278131fbb225241dd37a40fd5355ac7"),
            (192, "8608895acbb0b5581cdfb5e84d11de01f722ab250285a172e8d59f2f67c46110"),
            (256, "080c6da49f3ef891dfbf1abdfe224490e30afbad3a24e4e689fd13e4a13de241"),
            (1024, "72dc5524951b8955c23b7e3e7f51fb9fff71d8650317f3b7d6e8572e78e230a6"),
        ] {
            assert_eq!(hex(&hash(&pattern(n))), expected, "unkeyed, {n} bytes");
        }
    }

    /// Keyed mode, same source. The key block is a full block and counts
    /// toward the counter, which is what these pin.
    #[test]
    fn matches_keyed_reference_vectors() {
        let key: Vec<u8> = (0..32u8).collect();
        for (n, expected) in [
            (
                0usize,
                "48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49",
            ),
            (1, "722ac21d94c3868234e075bb5692678e6460c23466b10b48acf133e6f89f9082"),
            (64, "ce3c22b930e6395797de1e490600d305294ff2e30eb187bb63120e3f5e3fc129"),
            (65, "82e02e62a066f2f3cd7a8a542581cbf441e35cf7a771fc7adb0965d8446b71cb"),
            (100, "6d76c967766118147e79a7528778f3c53125c42b357c86a97834339715a74bcd"),
        ] {
            assert_eq!(hex(&keyed_hash(&key, &pattern(n))), expected, "keyed, {n} bytes");
        }
    }

    /// Any split of the input into `update` calls gives the same digest, and
    /// agrees with the whole-block fast path in [`hash`].
    #[test]
    fn streaming_matches_one_shot() {
        for n in [0usize, 1, 63, 64, 65, 130, 192, 577] {
            let data = pattern(n);
            let want = {
                let mut h = Hasher::new();
                h.update(&data);
                h.finalize()
            };
            assert_eq!(hash(&data), want, "one-shot vs streaming, {n}");
            for split in [1usize, 7, 64, 65] {
                if split > n {
                    continue;
                }
                let mut h = Hasher::new();
                for chunk in data.chunks(split) {
                    h.update(chunk);
                }
                assert_eq!(h.finalize(), want, "{n} bytes in {split}-byte updates");
            }
        }
    }

    /// Every SIMD backend compiled into this build agrees with the scalar
    /// hash, not just the one the dispatch picks. Both the round arithmetic and
    /// the transpose network are per-backend, so this is what keeps an untaken
    /// path honest.
    #[test]
    fn every_backend_matches_scalar() {
        fn check<S: Lanes32>(name: &str) {
            for n in [1usize, S::WIDTH - 1, S::WIDTH, S::WIDTH + 1, 3 * S::WIDTH + 2] {
                for len in [64usize, 128, 192, 1024] {
                    let data: Vec<u8> = (0..n * len).map(|i| ((i * 37 + 11) & 0xff) as u8).collect();
                    let mut got = vec![0u8; n * OUT_LEN];
                    // SAFETY: `data` holds `n * len` bytes and `got` `n * 32`.
                    unsafe { hash_many_with::<S>(&data, len, &PARAM_IV, 0, &mut got) };
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
        check::<Scalar8>("scalar");
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        check::<x86::Avx2>("avx2");
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        check::<x86::Avx512>("avx512");
        #[cfg(target_arch = "aarch64")]
        check::<arm::Neon>("neon");
    }

    /// The transposed batch is byte-identical to the scalar hash per input,
    /// including a group that is not a multiple of `LANES`.
    #[test]
    fn batched_matches_scalar() {
        fn check<const LEN: usize>(n: usize) {
            let data: Vec<u8> = (0..n * LEN).map(|i| ((i * 31 + 7) & 0xff) as u8).collect();
            let mut got = vec![0u8; n * OUT_LEN];
            hash_many::<LEN>(&data, &mut got);
            for i in 0..n {
                assert_eq!(
                    &got[i * OUT_LEN..(i + 1) * OUT_LEN],
                    &hash(&data[i * LEN..(i + 1) * LEN])[..],
                    "LEN={LEN}, input {i} of {n}"
                );
            }
        }
        for n in [1usize, 7, 8, 9, 16, 21] {
            check::<64>(n);
            check::<128>(n);
            check::<192>(n);
            check::<1024>(n);
        }
    }
}
