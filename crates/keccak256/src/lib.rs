//! Ethereum's Keccak-256 (FIPS 202's 256-bit sponge with Keccak's original padding): what the signature schemes
//! hash with, what the zkDSL compiler lays its sponge out by, and both provers' Keccak. Depends on no prover
//! tree.
//!
//! - [`keccak_f`], the Keccak-f\[1600\] permutation, which the VM's `KECCAK` opcode computes and `keccak_gkr`
//!   proves, and [`keccak_f_many`], its batched form.
//! - [`hash`] / [`Hasher`], Keccak-256 over bytes, and [`hash_many`], its batched form over equal-length inputs.
//! - [`bits`], the permutation one bit position at a time, as `keccak_gkr` proves it.
//!
//! The batched forms permute [`LANES`] states at once in vector registers (AVX-512, AVX2 or NEON, the only
//! architecture-specific code here) and are byte-identical to the one-input forms.
//!
//! The state is 25 little-endian 64-bit lanes, lane `x + 5y` holding `A[x, y]`. The first `RATE / 8` lanes are the
//! rate: a message block is XORed into them before each permutation, and the digest is read off the first
//! `OUT_LEN / 8` of them after the last one.

/// Digest length in bytes. Keccak-256 throughout.
pub const OUT_LEN: usize = 32;
/// Sponge rate in bytes: `1600 - 2·256` bits.
pub const RATE: usize = 136;
/// Sponge rate in lanes.
const RATE_LANES: usize = RATE / 8;

/// Permutations Keccak-256 spends on an input of `len` bytes: one per block, the last
/// holding the padding.
pub const fn permutations(len: usize) -> usize {
    len / RATE + 1
}

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

/// The padding's last bit as it sits in lane 16, the rate's last lane.
pub const END_BIT: u64 = (PAD_LAST as u64) << 56;

pub mod bits;
mod lanes;

pub use lanes::{LANES, digest_halves_from, hash_many, hash_many_from_state, keccak_f_many};

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
mod single_avx512;

/// The Keccak-f\[1600\] permutation, in place: 24 rounds of θ, ρ, π, χ and ι. On AVX-512, one state in five vectors.
#[inline]
pub fn keccak_f(a: &mut [u64; STATE_LANES]) {
    cfg_select! {
        all(target_arch = "x86_64", target_feature = "avx512f") => single_avx512::permute(a),
        _ => lanes::permute(a),
    }
}

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

/// The tweakable hash of leanXMSS and leanSPHINCS is `Truncate_N(H(prefix | address | payload))`,
/// the prefix being the public parameter or `PK.seed` and the address each scheme's own: a hasher that
/// has absorbed `prefix | address`.
pub fn prefixed_hasher<const N: usize>(prefix: &[u8; N], address: &[u8]) -> Hasher {
    let mut hasher = Hasher::new();
    hasher.update(prefix).update(address);
    hasher
}

/// `Truncate_N`: an `N`-byte hash value from a Keccak-256 output.
pub fn truncate<const N: usize>(output: [u8; OUT_LEN]) -> [u8; N] {
    output[..N].try_into().unwrap()
}

/// The root that `leaf`, at index `e`, and its authentication `path` reach, showing `visit` the two
/// children of every node on the way up, `node(z, j, children)` hashing node `j` at height `z`.
pub fn path_fold<const N: usize>(
    leaf: [u8; N],
    e: usize,
    path: &[[u8; N]],
    mut visit: impl FnMut(&[[u8; N]; 2]),
    node: impl Fn(usize, usize, &[[u8; N]; 2]) -> [u8; N],
) -> [u8; N] {
    path.iter().enumerate().fold(leaf, |current, (z, &sibling)| {
        // Bit `z` of `e` says whether the node is the right child.
        let children = if (e >> z) & 1 == 0 {
            [current, sibling]
        } else {
            [sibling, current]
        };
        visit(&children);
        node(z + 1, e >> (z + 1), &children)
    })
}

/// Keccak-256 of `data`, Ethereum's `keccak256`: FIPS 202's sponge over Keccak-f\[1600\] with
/// rate [`RATE`] and Keccak's original padding.
pub fn hash(data: &[u8]) -> [u8; OUT_LEN] {
    hash_from_state(data, &[0; STATE_LANES])
}

/// A binary Merkle tree's node: the [`hash`] of its two children's digests, left then right.
pub fn hash_pair(left: &[u8; OUT_LEN], right: &[u8; OUT_LEN]) -> [u8; OUT_LEN] {
    let mut pair = [0; 2 * OUT_LEN];
    pair[..OUT_LEN].copy_from_slice(left);
    pair[OUT_LEN..].copy_from_slice(right);
    hash(&pair)
}

/// The state after absorbing `n_blocks` all-zero blocks.
///
/// A leaf image that starts with whole zero blocks (the PCS's absent interleaving lanes) shares that prefix with
/// every other leaf, so the committer computes this once and starts each leaf's sponge here. Nothing about the digest
/// changes: a prefix's permutations depend on nothing after them, so the result is still the hash of the whole image.
pub fn zero_prefix_state(n_blocks: usize) -> [u64; STATE_LANES] {
    let mut state = [0; STATE_LANES];
    for _ in 0..n_blocks {
        keccak_f(&mut state);
    }
    state
}

/// [`hash`] continued from a sponge state that has absorbed whole blocks (see [`zero_prefix_state`]): `data` is the
/// rest of the message.
fn hash_from_state(data: &[u8], state: &[u64; STATE_LANES]) -> [u8; OUT_LEN] {
    let mut state = *state;
    let (blocks, tail) = data.as_chunks::<RATE>();
    for block in blocks {
        absorb(&mut state, &block_of(block));
    }
    absorb(&mut state, &final_block(tail));
    digest_of(&state)
}

/// The state [`hash`] of `data` permutes last: every whole block absorbed and the padded final
/// block XORed in, not yet permuted, so `keccak_f` of it then [`digest_of`] is `hash(data)`.
///
/// Inputs that differ only in a few words of their final block share it: build it once with
/// those words zero, then [`digest_halves_from`] XORs each input's words in.
pub fn final_state(data: &[u8]) -> [u64; STATE_LANES] {
    let mut state = [0; STATE_LANES];
    let (blocks, tail) = data.as_chunks::<RATE>();
    for block in blocks {
        absorb(&mut state, &block_of(block));
    }
    for (s, b) in state.iter_mut().zip(&final_block(tail)) {
        *s ^= b;
    }
    state
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|i| ((i * 7 + 3) & 0xff) as u8).collect()
    }

    /// Ethereum's `keccak256`, as an independent implementation computes it, across both sides of every block
    /// boundary up to five blocks, one-shot and streamed in pieces of several sizes.
    #[test]
    fn matches_ethereum_keccak256() {
        use sha3::Digest;
        for n in (0..700).chain([1023, 1024, 1025, 4096]) {
            let data = pattern(n);
            let want = sha3::Keccak256::digest(&data);
            assert_eq!(&hash(&data)[..], &want[..], "{n} bytes");
            for split in [1, 37, 136, 137] {
                let mut h = Hasher::new();
                data.chunks(split).for_each(|chunk| {
                    h.update(chunk);
                });
                assert_eq!(&h.finalize()[..], &want[..], "{n} bytes in {split}-byte updates");
            }
        }
    }

    /// The batched hash, whole groups and the remainder, from the zero state and from a zero prefix, against hashing
    /// each whole image.
    #[test]
    fn batched_hash_matches_one_shot() {
        for zero_blocks in [0usize, 1, 3] {
            let state = zero_prefix_state(zero_blocks);
            for len in [0usize, 8, 64, 135, 136, 137, 200, 408, 512] {
                for n in [1, LANES, 2 * LANES + 1] {
                    let data: Vec<u8> = (0..n * len).map(|i| (i * 31 + zero_blocks) as u8).collect();
                    let mut got = vec![0u8; n * OUT_LEN];
                    hash_many_from_state(&data, len, &state, &mut got);
                    for i in 0..n {
                        let mut whole = vec![0u8; zero_blocks * RATE];
                        whole.extend_from_slice(&data[i * len..(i + 1) * len]);
                        assert_eq!(
                            &got[i * OUT_LEN..][..OUT_LEN],
                            &hash(&whole)[..],
                            "{zero_blocks} {len} {n}"
                        );
                    }
                    if zero_blocks == 0 {
                        let mut plain = vec![0u8; n * OUT_LEN];
                        hash_many(&data, len, &mut plain);
                        assert_eq!(plain, got);
                    }
                }
            }
        }
    }

    /// A value XORed into a final state's zeroed lanes gives the digest of the input holding it, batched and in the
    /// remainder.
    #[test]
    fn digest_halves_from_a_final_state_match_hashing() {
        for (len, at) in [(80, 64), (64, 48), (160, 144)] {
            let mut input = pattern(len);
            input[at..at + 16].fill(0);
            let template = final_state(&input);
            let values: Vec<u128> = (1..2 * LANES as u128 + 2)
                .map(|i| i * 0x9E37_79B9_7F4A_7C15_F39C_C060)
                .collect();
            let mut got = vec![0; values.len()];
            digest_halves_from(&template, at % RATE / 8, &values, &mut got);
            for (value, got) in values.iter().zip(got) {
                input[at..at + 16].copy_from_slice(&value.to_le_bytes());
                assert_eq!(got.to_le_bytes()[..], hash(&input)[..16], "len {len}");
            }
        }
    }

    /// The batched permutation, whole groups and the remainder, against the scalar one.
    #[test]
    fn keccak_f_many_matches_keccak_f() {
        let states: Vec<[u64; STATE_LANES]> = (0..2 * LANES as u64 + 1)
            .map(|l| std::array::from_fn(|i| (l << 32) ^ (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)))
            .collect();
        let mut got = states.clone();
        keccak_f_many(&mut got);
        for (mut want, got) in states.into_iter().zip(got) {
            keccak_f(&mut want);
            assert_eq!(got, want);
        }
    }
}
