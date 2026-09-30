//! BLAKE2s (RFC 7693), the repo's one hash function.
//!
//! - The 10-round compression: every hash here is a chain of them, and the VM proves one per opcode.
//! - Ordinary BLAKE2s-256 over bytes, one-shot or streaming.
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

use batch::{Lanes32, hash_many_with};

/// The batched backend this build dispatches to.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
type Backend = x86::Avx512;
#[cfg(all(target_arch = "x86_64", not(target_feature = "avx512f"), target_feature = "avx2"))]
type Backend = x86::Avx2;
#[cfg(target_arch = "aarch64")]
type Backend = arm::Neon;
#[cfg(not(any(all(target_arch = "x86_64", target_feature = "avx2"), target_arch = "aarch64")))]
type Backend = batch::Scalar8;

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

/// The unkeyed BLAKE2s-256 initial chaining value: the IV with the parameter block in word 0.
///
/// Hashing 64 bytes is one compression from here, at counter 64 with the final flag.
pub const PARAM_IV: [u32; 8] = {
    let mut h = IV;
    // Digest length 32, key length 0, fanout 1, depth 1.
    h[0] ^= 0x0101_0000 ^ OUT_LEN as u32;
    h
};

/// The BLAKE2s compression: absorb block `m` at byte counter `t` into `h`.
///
/// `last` sets the final-block flag.
///
/// The last-node flag stays zero: nothing here uses the tree mode.
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
            h: PARAM_IV,
            buf: [0u8; BLOCK_LEN],
            buf_len: 0,
            counter: 0,
        }
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
        let mut h = PARAM_IV;
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

/// Inputs one vector of the widest backend holds.
///
/// Batched calls accept any count, and hash the remainder one at a time.
pub const LANES: usize = Backend::WIDTH;

/// Inputs one batched step hashes together.
///
/// A count that is a multiple of it has no remainder.
pub const BATCH: usize = Backend::GROUPS * Backend::WIDTH;

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
    let mut h = PARAM_IV;
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
    // SAFETY: the asserts pin the buffer sizes, and the backend is gated on the features its intrinsics need.
    unsafe { hash_many_with::<Backend>(data, len, state, t_offset, out) }
}

/// The batched hash with a runtime input length, a nonzero multiple of 64.
pub fn hash_many_dyn(data: &[u8], len: usize, out: &mut [u8]) {
    hash_many_dyn_from_state(data, len, &PARAM_IV, 0, out);
}

/// The official unkeyed BLAKE2s-256 test vectors, as `(input, digest)` pairs.
///
/// Input `n` is the `n` bytes `00 01 .. n-1`, for `n` in `0..256`: every length through four blocks.
///
/// `test_vectors.txt` is extracted from `testvectors/blake2-kat.json` of <https://github.com/BLAKE2/BLAKE2>:
///
/// ```text
/// jq -r '.[] | select(.hash == "blake2s" and .key == "") | .out' blake2-kat.json
/// ```
#[cfg(feature = "test-util")]
pub fn test_vectors() -> impl Iterator<Item = (Vec<u8>, [u8; OUT_LEN])> {
    let lines: Vec<&str> = include_str!("test_vectors.txt").lines().collect();
    assert_eq!(lines.len(), 256, "the vector file is truncated");
    lines.into_iter().enumerate().map(|(n, line)| {
        let input = (0..n).map(|i| i as u8).collect();
        let digest = std::array::from_fn(|i| u8::from_str_radix(&line[2 * i..2 * i + 2], 16).unwrap());
        (input, digest)
    })
}

#[cfg(test)]
mod tests {
    use super::batch::Scalar8;
    use super::*;

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
        // Whole blocks straight through `compress`, independent of the streaming and batched paths.
        let mut h = PARAM_IV;
        let n = data.len() / BLOCK_LEN;
        for (b, block) in data.as_chunks::<BLOCK_LEN>().0.iter().enumerate() {
            compress(&mut h, &block_words(block), ((b + 1) * BLOCK_LEN) as u64, b + 1 == n);
        }
        state_bytes(&h)
    }

    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|i| ((i * 7 + 3) & 0xff) as u8).collect()
    }

    #[test]
    fn matches_official_vectors() {
        // Whole blocks take the fast path, and 65 bytes pins the held-back buffer.
        for (input, digest) in test_vectors() {
            assert_eq!(hash(&input), digest, "{} bytes", input.len());
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
