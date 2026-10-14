//! SHA3-256 of the cell encoding, the VM's `SHA3` step, and digests.

use crate::field::E;
use crate::{VerifierError, require};

pub const STATE_LANES: usize = 25;
/// The sponge rate in bytes.
const RATE: usize = 136;
/// Message bytes one block carries: the rate's first 16 lanes, eight whole 16-byte cells.
const CHUNK: usize = 128;
const ROUNDS: usize = 24;

pub const KECCAK_RC: [u64; ROUNDS] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];
pub const KECCAK_RHO: [u32; STATE_LANES] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];
/// Where lane `x + 5y` lands.
pub const KECCAK_PI: [usize; STATE_LANES] = {
    let mut pi = [0; STATE_LANES];
    let mut i = 0;
    while i < STATE_LANES {
        pi[i] = i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5);
        i += 1;
    }
    pi
};
/// The padding's last bit, which every step XORs into lane 16.
pub const KECCAK_END_BIT: u64 = 0x80 << 56;
const END_LANE: usize = 16;

pub fn keccak_f(a: &mut [u64; STATE_LANES]) {
    for rc in KECCAK_RC {
        let c: [u64; 5] = std::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
        for i in 0..STATE_LANES {
            a[i] ^= c[(i + 4) % 5] ^ c[(i + 1) % 5].rotate_left(1);
        }
        let mut b = [0u64; STATE_LANES];
        for i in 0..STATE_LANES {
            b[KECCAK_PI[i]] = a[i].rotate_left(KECCAK_RHO[i]);
        }
        for i in 0..STATE_LANES {
            let row = i - i % 5;
            a[i] = b[i] ^ (!b[row + (i + 1) % 5] & b[row + (i + 2) % 5]);
        }
        a[0] ^= rc;
    }
}

/// The VM's `SHA3` step: XOR the padding's last bit into lane 16, then Keccak-f\[1600\].
pub fn step(input: &[u64; STATE_LANES]) -> [u64; STATE_LANES] {
    let mut state = *input;
    state[END_LANE] ^= KECCAK_END_BIT;
    keccak_f(&mut state);
    state
}

fn xor_bytes(state: &mut [u64; STATE_LANES], bytes: &[u8]) {
    for (i, &byte) in bytes.iter().enumerate() {
        state[i / 8] ^= u64::from(byte) << (8 * (i % 8));
    }
}

/// SHA3-256 of `data` in the cell encoding: past 128 bytes, the fixed eight bytes `0^7 ‖ 0x80` after every 128,
/// so that a block is eight whole cells. Up to 128 bytes it is plain SHA3-256.
pub fn sha3_hash(data: &[u8]) -> Digest {
    let mut state = [0u64; STATE_LANES];
    let nonfinal = data.len().saturating_sub(1) / CHUNK;
    for chunk in data[..nonfinal * CHUNK].chunks(CHUNK) {
        xor_bytes(&mut state, chunk);
        state = step(&state);
    }
    // The last block: the remaining bytes, then SHA3's padding, whose last bit is the one `step` supplies.
    let tail = &data[nonfinal * CHUNK..];
    let mut block = [0u8; RATE];
    block[..tail.len()].copy_from_slice(tail);
    block[tail.len()] ^= 0x06;
    xor_bytes(&mut state, &block);
    state = step(&state);
    let mut value = [0u8; 32];
    for (bytes, lane) in value.as_chunks_mut().0.iter_mut().zip(state) {
        *bytes = lane.to_le_bytes();
    }
    Digest(value)
}

/// 256 bits
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Digest(pub [u8; 32]);

impl Digest {
    /// Its four 64-bit words, the form a seed takes in the sponge's lanes.
    pub fn words(&self) -> [u64; 4] {
        std::array::from_fn(|i| u64::from_le_bytes(self.0.as_chunks().0[i]))
    }

    /// Its two 128-bit halves, the one form a digest travels in.
    pub fn halves(&self) -> (E, E) {
        let [w0, w1, w2, w3] = self.words();
        (E::new(w0, w1, 0), E::new(w2, w3, 0))
    }

    pub fn from_halves(low: E, high: E) -> Result<Self, VerifierError> {
        require(low.c2 == 0 && high.c2 == 0, VerifierError::DigestHalf)?;
        let mut value = [0u8; 32];
        for (bytes, word) in value
            .as_chunks_mut()
            .0
            .iter_mut()
            .zip([low.c0, low.c1, high.c0, high.c1])
        {
            *bytes = word.to_le_bytes();
        }
        Ok(Self(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// SHA3-256 of the cell encoding of the bytes `00 01 ..` (mod 256), from Python's `hashlib`: plain SHA3-256 up to
    /// 128 bytes, then each side of a chunk boundary.
    const VECTORS: [(usize, &str); 9] = [
        (0, "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"),
        (1, "5d53469f20fef4f8eab52b88044ede69c77a6a68a60728609fc4a65ff531e7d0"),
        (127, "c66018e60c774d770cc6539d42c023fa974c29e3fe2db5925f226b9cc5cf8b05"),
        (128, "bec3ebfba06834f224543cca2a427cb9329147be93e19aeb0e33a7119c7f63ef"),
        (129, "634ed47904bb26db6a7bcf96954e869905711ca072f9499b8154150afd419f21"),
        (200, "45874a8fdf627c901808e12c41c4026a015933fba404cbd3139b5e97b362c099"),
        (256, "3e21e62a3c79ea292f52280b8ce0b674c52634d784077852506b0cb8741f9192"),
        (257, "becb0b05959b41d6ec97d7bee2c794dad8216f363736cba2336d93fc469c6865"),
        (512, "363ef36ec486dc1e6612a0254f0537054071069f0c268cfc637f9bae5666dd45"),
    ];

    #[test]
    fn matches_reference_vectors() {
        for (n, want) in VECTORS {
            let input: Vec<u8> = (0..n).map(|i| i as u8).collect();
            let got: String = sha3_hash(&input).0.iter().map(|byte| format!("{byte:02x}")).collect();
            assert_eq!(got, want, "{n} bytes");
        }
    }
}
