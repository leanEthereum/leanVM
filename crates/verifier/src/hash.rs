//! BLAKE2s and digests.

use crate::field::E;
use crate::{VerifierError, require};

pub const BLAKE2S_IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];
#[rustfmt::skip]
pub const BLAKE2S_SIGMA: [[usize; 16]; 10] = [
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
#[rustfmt::skip]
pub const BLAKE2S_G_LANES: [[usize; 4]; 8] = [
    [0, 4, 8, 12], [1, 5, 9, 13], [2, 6, 10, 14], [3, 7, 11, 15],
    [0, 5, 10, 15], [1, 6, 11, 12], [2, 7, 8, 13], [3, 4, 9, 14],
];

/// One round's eight gates.
#[inline(always)]
fn round(v: &mut [u32; 16], m: &[u32; 16], sigma: &[usize; 16]) {
    for (gate, &[a, b, c, d]) in BLAKE2S_G_LANES.iter().enumerate() {
        v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[sigma[2 * gate]]);
        v[d] = (v[d] ^ v[a]).rotate_right(16);
        v[c] = v[c].wrapping_add(v[d]);
        v[b] = (v[b] ^ v[c]).rotate_right(12);
        v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[sigma[2 * gate + 1]]);
        v[d] = (v[d] ^ v[a]).rotate_right(8);
        v[c] = v[c].wrapping_add(v[d]);
        v[b] = (v[b] ^ v[c]).rotate_right(7);
    }
}

fn compression(h: &mut [u32; 8], block: &[u8; 64], counter: u64, last: bool) {
    let m: [u32; 16] = std::array::from_fn(|i| u32::from_le_bytes(block.as_chunks().0[i]));
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&BLAKE2S_IV);
    v[12] ^= counter as u32;
    v[13] ^= (counter >> 32) as u32;
    if last {
        v[14] = !v[14];
    }
    // Spelled out: a loop over the rounds is kept rolled, and its message indices loaded and bounds checked.
    let [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] = &BLAKE2S_SIGMA;
    round(&mut v, &m, s0);
    round(&mut v, &m, s1);
    round(&mut v, &m, s2);
    round(&mut v, &m, s3);
    round(&mut v, &m, s4);
    round(&mut v, &m, s5);
    round(&mut v, &m, s6);
    round(&mut v, &m, s7);
    round(&mut v, &m, s8);
    round(&mut v, &m, s9);
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

/// Standard 32-byte unkeyed BLAKE2s-256 hash.
pub fn blake2s_hash(data: &[u8]) -> Digest {
    let mut h = BLAKE2S_IV;
    h[0] ^= 0x0101_0020;
    // The last block is the one compressed with the final flag, and is never empty unless the input is.
    let last_start = data.len().saturating_sub(1) / 64 * 64;
    for (index, block) in data[..last_start].as_chunks().0.iter().enumerate() {
        compression(&mut h, block, 64 * (index as u64 + 1), false);
    }
    let mut block = [0u8; 64];
    block[..data.len() - last_start].copy_from_slice(&data[last_start..]);
    compression(&mut h, &block, data.len() as u64, true);
    let mut value = [0u8; 32];
    for (bytes, word) in value.as_chunks_mut().0.iter_mut().zip(h) {
        *bytes = word.to_le_bytes();
    }
    Digest(value)
}

/// 256 bits
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Digest(pub [u8; 32]);

impl Digest {
    /// Its four 64-bit words, the form the compression chain runs in.
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

    /// Official unkeyed BLAKE2s-256 vectors: the digest of the bytes `00 01 .. n-1`, at lengths either side of every block boundary case.
    const VECTORS: [(usize, &str); 6] = [
        (0, "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9"),
        (1, "e34d74dbaf4ff4c6abd871cc220451d2ea2648846c7757fbaac82fe51ad64bea"),
        (63, "e57cb79487dd57902432b250733813bd96a84efce59f650fac26e6696aefafc3"),
        (64, "56f34e8b96557e90c1f24b52d0c89d51086acf1b00f634cf1dde9233b8eaaa3e"),
        (65, "1b53ee94aaf34e4b159d48de352c7f0661d0a40edff95a0b1639b4090e974472"),
        (199, "1d4e5487ae3c740f2ba6e541ac91bc2bfcd2999c518d807b426748803a350fd4"),
    ];

    #[test]
    fn matches_official_vectors() {
        for (n, want) in VECTORS {
            let input: Vec<u8> = (0..n).map(|i| i as u8).collect();
            let got: String = blake2s_hash(&input)
                .0
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect();
            assert_eq!(got, want, "{n} bytes");
        }
    }
}
