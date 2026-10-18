//! Keccak-256 of the cell encoding, the VM's `SHA3` step, and digests.

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

/// Keccak-256 of `data` in the cell encoding: up to 128 bytes it is plain Keccak-256. A longer input is cut into
/// 128-byte chunks, the last holding the remaining 1 to 128 bytes, and every chunk but the last is followed by the
/// fixed eight bytes `0^7 ‖ 0x80`, so that a block is eight whole cells.
pub fn keccak_hash(data: &[u8]) -> Digest {
    let mut state = [0u64; STATE_LANES];
    let nonfinal = data.len().saturating_sub(1) / CHUNK;
    for chunk in data[..nonfinal * CHUNK].chunks(CHUNK) {
        xor_bytes(&mut state, chunk);
        state = step(&state);
    }
    // The last block: the remaining bytes, then Keccak's padding, whose last bit is the one `step` supplies.
    let tail = &data[nonfinal * CHUNK..];
    let mut block = [0u8; RATE];
    block[..tail.len()].copy_from_slice(tail);
    block[tail.len()] ^= 0x01;
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

    /// Keccak-256 of the cell encoding of the bytes `00 01 ..` (mod 256), from OpenSSL's `keccak-256`: plain Keccak-256 up to
    /// 128 bytes, then each side of a chunk boundary.
    const VECTORS: [(usize, &str); 9] = [
        (0, "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
        (1, "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a"),
        (127, "c52f0bd08793b9e8601b29753539e1bf47f8e483eed0a901e8761982449c9b4c"),
        (128, "ed4c9adc183fb8cb025b1500ec3eeae1b45517314441a187605de1bb8a64726e"),
        (129, "2900f87118e525c6a28e5d3a37a7f37db1b0b17661931ba7ba0be4fbb202f766"),
        (200, "f4eb34198ddc4f2012a7791eb46292821d0904eb97640e9519ab735eef9c04ab"),
        (256, "d63969818e044e52f1c4bb4b58569816bb0c5e7efadcee96f83b02a355a42686"),
        (257, "2cc03e9f89462b48c53aae96d64d7a43482bdd896fa16f8308f8199538d0ba65"),
        (512, "63e0372d8c2e3203e0a6a80bbafa151aba520de0c9baeb89907af0c242ed4e6a"),
    ];

    #[test]
    fn matches_reference_vectors() {
        for (n, want) in VECTORS {
            let input: Vec<u8> = (0..n).map(|i| i as u8).collect();
            let got: String = keccak_hash(&input).0.iter().map(|byte| format!("{byte:02x}")).collect();
            assert_eq!(got, want, "{n} bytes");
        }
    }
}
