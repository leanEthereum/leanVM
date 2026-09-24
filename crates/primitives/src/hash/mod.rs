//! BLAKE2s (RFC 7693), the repo's one hash function.
//!
//! - The 10-round compression: every hash here is a chain of them, and the VM proves one per opcode.
//! - Ordinary BLAKE2s-256 over bytes, one-shot, keyed or streaming.
//! - The batched form: many equal-length inputs at once, one SIMD lane each, for the PCS Merkle tree.
//!
//! Why BLAKE2s: the byte counter and final flag are ordinary compression inputs.
//!
//! So one opcode completes a hash of any length, with no tree of chunks to rebuild in-circuit.

mod batch;

#[cfg(target_arch = "aarch64")]
mod arm;
#[cfg(target_arch = "x86_64")]
mod x86;

#[cfg(not(any(all(target_arch = "x86_64", target_feature = "avx2"), target_arch = "aarch64")))]
use batch::Scalar8;
use batch::hash_many_with;

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

/// Digest length in bytes: BLAKE2s-256 throughout.
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

/// The parameter block folded into `h[0]` for an unkeyed BLAKE2s-256.
///
/// Digest length 32, key length 0, fanout 1, depth 1.
pub const PARAM_UNKEYED: u32 = 0x0101_0000 ^ OUT_LEN as u32;

/// The initial chaining value for a `key_len`-byte key (0 = unkeyed).
#[inline]
pub const fn init_state(key_len: usize) -> [u32; 8] {
    assert!(key_len <= 32, "BLAKE2s key is at most 32 bytes");
    let mut h = IV;
    h[0] ^= 0x0101_0000 ^ ((key_len as u32) << 8) ^ OUT_LEN as u32;
    h
}

/// The unkeyed BLAKE2s-256 initial chaining value: the IV with the parameter block in word 0.
///
/// Hashing 64 bytes is one compression from here, at counter 64 with the final flag.
pub const PARAM_IV: [u32; 8] = init_state(0);

/// The BLAKE2s compression: absorb block `m` at byte counter `t` into `h`.
///
/// `last` sets the final-block flag.
///
/// The last-node flag stays zero: nothing here uses the tree mode.
#[inline]
pub fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
    #[cfg(target_arch = "x86_64")]
    x86::compress(h, m, t, last);
    #[cfg(not(target_arch = "x86_64"))]
    compress_portable(h, m, t, last);
}

/// The compression as the RFC writes it: the reference every specialized path is pinned to.
#[cfg_attr(target_arch = "x86_64", allow(dead_code))]
fn compress_portable(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
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
/// The final block carries the final flag, so a full buffer is held back until more input arrives.
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

    /// Keyed BLAKE2s-256 (RFC 7693, section 2.9): the zero-padded key is the first block.
    ///
    /// The key is at most 32 bytes.
    pub fn new_keyed(key: &[u8]) -> Self {
        assert!(key.len() <= 32, "BLAKE2s key is at most 32 bytes");
        let mut s = Self {
            h: init_state(key.len()),
            buf: [0u8; BLOCK_LEN],
            buf_len: 0,
            counter: 0,
        };
        if !key.is_empty() {
            // A full block even for a shorter key, and it counts toward the byte counter.
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
    // Whole blocks, the shape hashed in bulk, need no buffering.
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

/// One-shot keyed BLAKE2s-256, the PRF form.
///
/// The key is at most 32 bytes.
pub fn keyed_hash(key: &[u8], data: &[u8]) -> [u8; OUT_LEN] {
    let mut hasher = Hasher::new_keyed(key);
    hasher.update(data);
    hasher.finalize()
}

/// Inputs one vector of the widest backend holds.
///
/// Batched calls accept any count, and hash the remainder one at a time.
pub const LANES: usize = if cfg!(all(target_arch = "x86_64", target_feature = "avx512f")) {
    16
} else if cfg!(target_arch = "x86_64") {
    8
} else if cfg!(target_arch = "aarch64") {
    4
} else {
    8
};

/// Batched BLAKE2s-256 of `LEN`-byte inputs, one 32-byte digest each.
///
/// Each digest equals the one-shot hash of its input.
///
/// `LEN` must be a nonzero multiple of 64.
pub fn hash_many<const LEN: usize>(data: &[u8], out: &mut [u8]) {
    const {
        assert!(LEN > 0 && LEN.is_multiple_of(BLOCK_LEN));
    }
    hash_many_dyn(data, LEN, out);
}

/// The chaining value after `n_blocks` all-zero blocks from the unkeyed IV.
///
/// PCS leaves share such a prefix, their absent interleaving lanes.
///
/// The committer absorbs it once and starts every leaf here.
///
/// Digests are unchanged: a prefix's compressions depend on nothing after them.
pub fn zero_prefix_state(n_blocks: usize) -> [u32; 8] {
    let mut h = init_state(0);
    for b in 0..n_blocks {
        compress(&mut h, &[0u32; 16], ((b + 1) * BLOCK_LEN) as u64, false);
    }
    h
}

/// The one-shot hash, continued from a chaining value.
///
/// - `data` is the rest of the image, a nonzero whole number of blocks.
/// - `t_offset` counts the bytes already absorbed into `state`.
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

/// The batched hash, every input continued from one shared chaining value.
///
/// Each digest equals the hash of its full image.
pub fn hash_many_dyn_from_state(data: &[u8], len: usize, state: &[u32; 8], t_offset: u64, out: &mut [u8]) {
    assert!(
        len > 0 && len.is_multiple_of(BLOCK_LEN),
        "batched inputs are whole blocks"
    );
    let n = out.len() / OUT_LEN;
    assert_eq!(data.len(), n * len);
    assert_eq!(out.len(), n * OUT_LEN);
    // SAFETY (each arm): the asserts pin the buffer sizes.
    // Every backend is gated on the feature its intrinsics need.
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

/// The batched hash with a runtime input length, a nonzero multiple of 64.
pub fn hash_many_dyn(data: &[u8], len: usize, out: &mut [u8]) {
    hash_many_dyn_from_state(data, len, &PARAM_IV, 0, out);
}

#[cfg(test)]
mod tests {
    use super::batch::{Lanes32, Scalar8};
    use super::*;
    use crate::test_rng::Rng;

    #[test]
    fn continued_from_zero_prefix_matches_whole_image() {
        // Invariant: continuing from a zero-prefix state gives the hash of the whole image.
        //
        // Checked one leaf at a time and batched, at counts crossing a group and the scalar tail.
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

    fn reference(data: &[u8]) -> [u8; OUT_LEN] {
        // Whole blocks through the RFC-literal compression, independent of the fast paths.
        let mut h = PARAM_IV;
        let n = data.len() / BLOCK_LEN;
        for (b, block) in data.as_chunks::<BLOCK_LEN>().0.iter().enumerate() {
            compress_portable(&mut h, &block_words(block), ((b + 1) * BLOCK_LEN) as u64, b + 1 == n);
        }
        state_bytes(&h)
    }

    #[test]
    fn compress_matches_portable() {
        // Invariant: the dispatched compression equals the RFC-literal one.
        let mut rng = Rng::new(0xB1A2);

        // Edge counters first: the low and high halves enter different state words.
        //
        //     t = 2^32 - 1    low word all ones
        //     t = 2^32        high word one
        let counters = [0u64, 64, u32::MAX as u64, 1 << 32, u64::MAX];
        for trial in 0..256 {
            // Random state and block, then an edge or random counter.
            let h: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            let t = counters.get(trial).copied().unwrap_or_else(|| rng.next_u64());
            let last = rng.bit();

            // Same start, same end.
            let (mut got, mut want) = (h, h);
            compress(&mut got, &m, t, last);
            compress_portable(&mut want, &m, t, last);
            assert_eq!(got, want, "t = {t:#x}, last = {last}");
        }
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|i| ((i * 7 + 3) & 0xff) as u8).collect()
    }

    #[test]
    fn matches_reference_vectors() {
        // Known answers from Python's `hashlib.blake2s`.
        //
        // 65 bytes pins the held-back buffer: the first block must not be compressed as final.
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

    #[test]
    fn matches_keyed_reference_vectors() {
        // Same source, keyed: the key block is a full block and counts toward the counter.
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

    #[test]
    fn streaming_matches_one_shot() {
        // Invariant: any split into updates gives the one-shot digest, whole-block fast path included.
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

    #[test]
    fn every_backend_matches_scalar() {
        // Invariant: every backend in this build matches the reference, not just the dispatched one.
        //
        // Rounds and transposes are per backend, so an untaken one is only checked here.
        fn check<S: Lanes32>(name: &str) {
            // One batch size per driver path:
            //
            //     1, WIDTH - 1    scalar only
            //     WIDTH           one group
            //     WIDTH + 1       a group and a tail
            //     last            two sets, a group and a tail
            let sets = 2 * S::GROUPS * S::WIDTH + S::WIDTH + 1;
            for n in [1usize, S::WIDTH - 1, S::WIDTH, S::WIDTH + 1, sets] {
                for len in [64usize, 128, 192, 1024] {
                    let data: Vec<u8> = (0..n * len).map(|i| ((i * 37 + 11) & 0xff) as u8).collect();
                    let mut got = vec![0u8; n * OUT_LEN];
                    // SAFETY: `data` holds `n * len` bytes and `got` `n * 32`.
                    unsafe { hash_many_with::<S>(&data, len, &PARAM_IV, 0, &mut got) };
                    for i in 0..n {
                        assert_eq!(
                            &got[i * OUT_LEN..(i + 1) * OUT_LEN],
                            &reference(&data[i * len..(i + 1) * len])[..],
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

    #[test]
    fn batched_matches_scalar() {
        // Invariant: each batched digest equals the one-shot hash, for counts off the lane width too.
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
