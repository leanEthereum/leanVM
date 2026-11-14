//! Ethereum's Keccak-256 (FIPS 202's 256-bit sponge with Keccak's original padding), portable and scalar: what the
//! signature schemes hash with and what the zkDSL compiler lays its sponge out by. Each prover tree has its own,
//! faster Keccak; this one serves the crates both trees share.
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
const ROUNDS: usize = 24;

/// The first bit of Keccak's `10*1` padding, as the byte XORed right after the
/// message. It is the only difference from FIPS 202's 256-bit hash, whose suffix makes it `0x06`.
pub const PAD_FIRST: u8 = 0x01;
/// The last bit of the `10*1` padding, XORed into the rate's last byte.
pub const PAD_LAST: u8 = 0x80;

/// The ι round constants.
const RC: [u64; ROUNDS] = [
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

/// The Keccak-f\[1600\] permutation, in place: 24 rounds of θ, ρ, π, χ and ι.
pub fn keccak_f(a: &mut [u64; STATE_LANES]) {
    let chi = |[b0, b1, b2, b3, b4]: [u64; 5]| {
        [
            b0 ^ (!b1 & b2),
            b1 ^ (!b2 & b3),
            b2 ^ (!b3 & b4),
            b3 ^ (!b4 & b0),
            b4 ^ (!b0 & b1),
        ]
    };
    for &rc in &RC {
        let col = |x: usize| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        let c = [col(0), col(1), col(2), col(3), col(4)];
        let d = [
            c[4] ^ c[1].rotate_left(1),
            c[0] ^ c[2].rotate_left(1),
            c[1] ^ c[3].rotate_left(1),
            c[2] ^ c[4].rotate_left(1),
            c[3] ^ c[0].rotate_left(1),
        ];
        let t = |i: usize| a[i] ^ d[i % 5];
        #[rustfmt::skip]
        let rows = [
            chi([t(0), t(6).rotate_left(44), t(12).rotate_left(43), t(18).rotate_left(21), t(24).rotate_left(14)]),
            chi([t(3).rotate_left(28), t(9).rotate_left(20), t(10).rotate_left(3), t(16).rotate_left(45), t(22).rotate_left(61)]),
            chi([t(1).rotate_left(1), t(7).rotate_left(6), t(13).rotate_left(25), t(19).rotate_left(8), t(20).rotate_left(18)]),
            chi([t(4).rotate_left(27), t(5).rotate_left(36), t(11).rotate_left(10), t(17).rotate_left(15), t(23).rotate_left(56)]),
            chi([t(2).rotate_left(62), t(8).rotate_left(55), t(14).rotate_left(39), t(15).rotate_left(41), t(21).rotate_left(2)]),
        ];
        *a = std::array::from_fn(|i| rows[i / 5][i % 5]);
        a[0] ^= rc;
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
    let mut state = final_state(data);
    keccak_f(&mut state);
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

/// The first 128 bits of the digest, little endian, of `template`'s input with `values[i]` XORed into its lanes `at`
/// and `at + 1`, into `out[i]`. `template` is that input's [`final_state`] with those 16 bytes zero, so a value costs
/// one permutation.
pub fn digest_halves_from(template: &[u64; STATE_LANES], at: usize, values: &[u128], out: &mut [u128]) {
    // The final block ends in padding, so the value stops before its last lane.
    assert!(at + 2 < RATE_LANES && values.len() == out.len());
    for (&value, out) in values.iter().zip(out) {
        let mut state = *template;
        state[at] ^= value as u64;
        state[at + 1] ^= (value >> 64) as u64;
        keccak_f(&mut state);
        *out = u128::from(state[0]) | u128::from(state[1]) << 64;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|i| ((i * 7 + 3) & 0xff) as u8).collect()
    }

    /// Ethereum's `keccak256`, as an independent implementation computes it, across both sides of every block
    /// boundary up to five blocks, one-shot and streamed in pieces.
    #[test]
    fn matches_ethereum_keccak256() {
        use sha3::Digest;
        for n in (0..700).chain([1023, 1024, 1025, 4096]) {
            let data = pattern(n);
            let want = sha3::Keccak256::digest(&data);
            assert_eq!(&hash(&data)[..], &want[..], "{n} bytes");
            let mut h = Hasher::new();
            data.chunks(37).for_each(|chunk| {
                h.update(chunk);
            });
            assert_eq!(&h.finalize()[..], &want[..], "{n} bytes streamed");
        }
    }

    /// A value XORed into a final state's zeroed lanes gives the digest of the input holding it.
    #[test]
    fn digest_halves_from_a_final_state_match_hashing() {
        for (len, at) in [(80, 64), (64, 48), (160, 144)] {
            let mut input = pattern(len);
            input[at..at + 16].fill(0);
            let template = final_state(&input);
            let values: Vec<u128> = (1..6).map(|i| i * 0x9E37_79B9_7F4A_7C15).collect();
            let mut got = vec![0; values.len()];
            digest_halves_from(&template, at % RATE / 8, &values, &mut got);
            for (value, got) in values.iter().zip(got) {
                input[at..at + 16].copy_from_slice(&value.to_le_bytes());
                assert_eq!(got.to_le_bytes()[..], hash(&input)[..16], "len {len}");
            }
        }
    }
}
