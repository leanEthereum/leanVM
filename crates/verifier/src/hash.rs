//! Keccak-256 (Ethereum's), the permutation the VM's `KECCAK` applies, and digests.

use crate::field::E;
use crate::{VerifierError, require};

pub const STATE_LANES: usize = 25;
/// The sponge rate in bytes.
const RATE: usize = 136;
pub const ROUNDS: usize = 24;

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
pub fn keccak_f(a: &mut [u64; STATE_LANES]) {
    for rc in KECCAK_RC {
        // Row by row, so every index is a constant: an index computed per lane vectorizes to gathers.
        let c: [u64; 5] = std::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
        let d: [u64; 5] = std::array::from_fn(|x| c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1));
        for row in a.as_chunks_mut::<5>().0 {
            for (lane, d) in row.iter_mut().zip(d) {
                *lane ^= d;
            }
        }
        let mut b = [0u64; STATE_LANES];
        for i in 0..STATE_LANES {
            b[KECCAK_PI[i]] = a[i].rotate_left(KECCAK_RHO[i]);
        }
        for (row, b) in a.as_chunks_mut::<5>().0.iter_mut().zip(b.as_chunks::<5>().0) {
            *row = std::array::from_fn(|x| b[x] ^ (!b[(x + 1) % 5] & b[(x + 2) % 5]));
        }
        a[0] ^= rc;
    }
}

fn xor_bytes(state: &mut [u64; STATE_LANES], bytes: &[u8]) {
    for (i, &byte) in bytes.iter().enumerate() {
        state[i / 8] ^= u64::from(byte) << (8 * (i % 8));
    }
}

/// Keccak-256 of `data`: 136-byte blocks, the last holding the remaining 0 to 135 bytes and the padding
/// `0x01 ‖ 0^* ‖ 0x80`.
pub fn keccak_hash(data: &[u8]) -> Digest {
    let mut state = [0u64; STATE_LANES];
    let (blocks, tail) = data.as_chunks::<RATE>();
    for block in blocks {
        xor_bytes(&mut state, block);
        keccak_f(&mut state);
    }
    let mut block = [0u8; RATE];
    block[..tail.len()].copy_from_slice(tail);
    block[tail.len()] ^= 0x01;
    block[RATE - 1] ^= 0x80;
    xor_bytes(&mut state, &block);
    keccak_f(&mut state);
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

    /// Keccak-256 of the bytes `00 01 ..` (mod 256), from the `sha3` crate's `Keccak256`, on each side of a block
    /// boundary.
    const VECTORS: [(usize, &str); 11] = [
        (0, "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
        (1, "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a"),
        (127, "c52f0bd08793b9e8601b29753539e1bf47f8e483eed0a901e8761982449c9b4c"),
        (128, "ed4c9adc183fb8cb025b1500ec3eeae1b45517314441a187605de1bb8a64726e"),
        (135, "cbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62"),
        (136, "7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e"),
        (137, "ac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db"),
        (200, "bfb0aa97863e797943cf7c33bb7e880bb4543f3d2703c0923c6901c2af57b890"),
        (271, "7c974895b2a88303ff2dc6b58f438ceb0b298cac91099ac0539cc0f477506191"),
        (272, "fdf2ec49e749960d3c8521a0219af8d03e30e2b3bf19bd16150ee0eaf133d66e"),
        (512, "f55ba327291604f0e5be6651752398b7be2331aad65f5763ce067df95cc13be1"),
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
