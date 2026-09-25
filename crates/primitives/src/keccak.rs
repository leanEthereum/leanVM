//! Keccak (FIPS 202): the second hash, beside [`crate::hash`]'s BLAKE2s, there
//! for the SPHINCS+ profile whose on-chain verifier fixes Keccak-256.
//!
//! - [`keccak_f`], the Keccak-f\[1600\] permutation, and [`step`], what the VM's
//!   `SHA3` opcode computes and `flock::keccak` proves.
//! - [`keccak256`], the EVM's Keccak-256 over bytes.
//! - [`hash`] / [`Hasher`], SHA3-256 in the cell encoding that makes a VM block
//!   eight whole 16-byte cells (plain SHA3-256 up to 128 bytes): the sponge the
//!   opcode steps.
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

/// One state lane. The permutation is written once over this trait, so an
/// implementor supplies only XOR, the χ step and the rotations.
trait Lanes64: Copy {
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

/// A single lane: the scalar permutation.
impl Lanes64 for u64 {
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
/// permute. This is the relation the VM's `SHA3` opcode computes and flock
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

/// Keccak-256's padding byte: the `10*1` padding's first bit with no domain
/// suffix, as the original Keccak submission (and the EVM's `keccak256`) pads.
pub const KECCAK_PAD_FIRST: u8 = 0x01;

/// Keccak-256 of `data`, as the EVM's `keccak256` computes it: the plain sponge,
/// 136-byte blocks, padding `0x01 ‖ 0* ‖ 0x80`. Not a leanVM hash: it is here for
/// the SPHINCS+ profile of the `sphincs` crate, whose on-chain verifier
/// fixes the hash, and the VM absorbs it block by block with the same opcode,
/// lane 16 being message data in a non-final block.
pub fn keccak256(data: &[u8]) -> [u8; OUT_LEN] {
    let mut state = [0u64; STATE_LANES];
    let blocks = data.len() / RATE;
    let lanes = |bytes: &[u8]| -> [u64; RATE_LANES] {
        std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
    };
    for block in data[..blocks * RATE].as_chunks::<RATE>().0 {
        absorb(&mut state, &lanes(block));
    }
    let tail = &data[blocks * RATE..];
    let mut last = [0u8; RATE];
    last[..tail.len()].copy_from_slice(tail);
    last[tail.len()] ^= KECCAK_PAD_FIRST;
    last[RATE - 1] ^= PAD_LAST;
    absorb(&mut state, &lanes(&last));
    digest_of(&state)
}

/// SHA3-256 of `data` under the cell encoding.
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
    let mut state = [0; STATE_LANES];
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
    /// Keccak-256 known answers (tiny-keccak 2, `Keccak::v256`) across the
    /// 136-byte block boundary and at the lengths the SPHINCS+ profile hashes.
    #[test]
    fn keccak256_matches_reference_vectors() {
        assert_eq!(
            hex(&keccak256(b"abc")),
            "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
        );
        for (n, expected) in [
            (
                0usize,
                "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
            ),
            (1, "69c322e3248a5dfc29d73c5b0553b0185a35cd5bb6386747517ef7e53b15e287"),
            (127, "fa3cd4a949bae0f7690ff5c8cbc6dc0332d192d790ab4d80dc97ba37b6569deb"),
            (128, "1c51c71b758998e7b841d7abde03b6f2b3e76b0313ed687269c30e16bb3aa488"),
            (135, "00ef96af9cf4b24c7f269d922294444a197d0a33638c2e56634c57e892103a8f"),
            (136, "742061bcad767ed4c4f5883b1dcb1aad11afdcc140dc469d953759b127b9f9ed"),
            (137, "e3371f61e770abf254c34239c3b0099ad90594507415bc81dd0a10b9692bbf2a"),
            (160, "a48ec24131baa57375a56d951a0518753c0a3d48b909972e8b8dd0f22a6867c0"),
            (271, "4401c4afbe16ff911bdbf2d38e556e5b861f3fdf0f9d4306b1c46f6ae4f73584"),
            (272, "ac141fd7b0a0ffcd2e967254d508da3ec616596493c36fa304425647d90e6de5"),
            (288, "8d3abd266545cda2aadc7ce92b8811b63f1f3b70a22cef5a253c556149f1923e"),
            (1440, "42ddaf20fc11d6d41c6af9ae381abc07412a82e10b5de3f64d75cb40aa2f5e1f"),
        ] {
            assert_eq!(hex(&keccak256(&pattern(n))), expected, "{n} bytes");
        }
    }

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
}
