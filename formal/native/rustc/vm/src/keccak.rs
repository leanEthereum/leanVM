//! Keccak-f[1600], portable and scalar (`hash.rs`'s `keccak_f`, `crates/verifier`), and Keccak-256 of
//! words in memory (`Native.Keccak.hash`, the model's `hashWords`).

use crate::data::{KECCAK_RC, KECCAK_RHO};

pub type State = [u64; 25];
/// A digest as its four little-endian words.
pub type Digest = [u64; 4];

/// `keccakPi`: where lane `x + 5y` lands.
const KECCAK_PI: [usize; 25] = {
    let mut pi = [0; 25];
    let mut i = 0;
    while i < 25 {
        pi[i] = i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5);
        i += 1;
    }
    pi
};

/// `keccakF1600`.
#[inline(never)]
pub fn keccak_f(a: &mut State) {
    for rc in KECCAK_RC {
        let c: [u64; 5] = core::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
        let d: [u64; 5] = core::array::from_fn(|x| c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1));
        for i in 0..25 {
            a[i] ^= d[i % 5];
        }
        let mut b = [0u64; 25];
        for i in 0..25 {
            b[KECCAK_PI[i]] = a[i].rotate_left(KECCAK_RHO[i]);
        }
        for y in 0..5 {
            for x in 0..5 {
                a[5 * y + x] = b[5 * y + x] ^ (!b[5 * y + (x + 1) % 5] & b[5 * y + (x + 2) % 5]);
            }
        }
        a[0] ^= rc;
    }
}

/// The rate in words.
const RATE: usize = 17;

/// Keccak-256 (Ethereum's padding) of `len` bytes held little-endian in `count` words, word `i`
/// being `word(i)`, the bytes of the last word past `len` zero.
#[inline(never)]
pub fn keccak256_words(count: usize, len: usize, word: impl Fn(usize) -> u64) -> Digest {
    let word = |i: usize| if i < count { word(i) } else { 0 };
    let mut state = [0u64; 25];
    let blocks = len / (8 * RATE);
    for block in 0..blocks {
        for (k, lane) in state.iter_mut().take(RATE).enumerate() {
            *lane ^= word(RATE * block + k);
        }
        keccak_f(&mut state);
    }
    for (k, lane) in state.iter_mut().take(RATE).enumerate() {
        *lane ^= word(RATE * blocks + k);
    }
    let tail = len % (8 * RATE);
    state[(tail / 8) % RATE] ^= 1 << (8 * (tail % 8));
    state[RATE - 1] ^= 0x80 << 56;
    keccak_f(&mut state);
    [state[0], state[1], state[2], state[3]]
}

/// `hashWords`: Keccak-256 of the bytes of words.
#[inline(always)]
pub fn hash_words(ws: &[u64]) -> Digest {
    keccak256_words(ws.len(), 8 * ws.len(), |i| ws.get(i).copied().unwrap_or(0))
}

/// `hashPair`: Keccak-256 of two digests' eight words.
#[inline(never)]
pub fn hash_pair(left: &Digest, right: &Digest) -> Digest {
    let ws = [left[0], left[1], left[2], left[3], right[0], right[1], right[2], right[3]];
    hash_words(&ws)
}

/// Two digests are equal.
#[inline(always)]
pub fn digest_eq(a: &Digest, b: &Digest) -> bool {
    (a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]) | (a[3] ^ b[3]) == 0
}
