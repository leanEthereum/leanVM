//! Streaming BLAKE2s-256: the machine's compression instruction on the VM, portable Rust elsewhere.
//!
//! Words are the fast path.
//!
//! The machine moves a word in one instruction, and a byte-aligned value one byte at a time.

/// The initialization vector with the parameter block folded in, as little-endian words.
///
/// The parameter block says: no key, a 32-byte digest, so `0x0101_0020` is folded into the first lane.
const IV: [u64; 4] = [
    0xBB67_AE85_6A09_E667 ^ 0x0101_0020,
    0xA54F_F53A_3C6E_F372,
    0x9B05_688C_510E_527F,
    0x5BE0_CD19_1F83_D9AB,
];

/// Streaming BLAKE2s-256.
pub struct Blake2s {
    /// The chaining value.
    h: [u64; 4],
    /// The message block being filled.
    m: [u64; 8],
    /// Bytes in the message block.
    filled: usize,
    /// Bytes compressed before the message block.
    done: u64,
}

impl Default for Blake2s {
    fn default() -> Self {
        Self::new()
    }
}

impl Blake2s {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            h: IV,
            m: [0; 8],
            filled: 0,
            done: 0,
        }
    }

    /// Absorb bytes.
    #[inline(always)]
    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            // A full block is compressed only now, once more input is known to follow.
            self.make_room();
            // Copy as much as the block still takes.
            let (at, n) = (self.filled, data.len().min(64 - self.filled));
            self.m_bytes()[at..at + n].copy_from_slice(&data[..n]);
            self.filled += n;
            data = &data[n..];
        }
        self
    }

    /// Absorb the little-endian bytes of words, the same as absorbing those bytes.
    ///
    /// Inlined with its length known, a call folds to plain word stores.
    #[inline(always)]
    pub fn update_words(&mut self, mut words: &[u64]) -> &mut Self {
        // A block filled to a byte that is not a word boundary takes the byte path.
        if !self.filled.is_multiple_of(8) {
            for word in words {
                self.update(&word.to_le_bytes());
            }
            return self;
        }
        if !words.is_empty() {
            self.make_room();
        }
        // Whole blocks go straight from the input to the compression, with no copy.
        //
        // Why `> 8`: a block with nothing after it may be the last, which is compressed differently.
        while self.filled == 0 && words.len() > 8 {
            let (block, rest) = words.split_first_chunk::<8>().unwrap();
            self.done += 64;
            self.h = compress(&self.h, block, self.done, false);
            words = rest;
        }
        // The rest, at most one block, goes word by word into the buffer.
        for &word in words {
            self.make_room();
            self.m[self.filled / 8] = word;
            self.filled += 8;
        }
        self
    }

    /// The digest.
    #[inline(always)]
    pub fn finalize(self) -> [u8; 32] {
        let words = self.finalize_words();
        // Digest byte `i` is byte `i % 8` of word `i / 8`.
        core::array::from_fn(|i| (words[i / 8] >> (8 * (i % 8))) as u8)
    }

    /// The digest as four little-endian words.
    #[inline(always)]
    pub fn finalize_words(mut self) -> [u64; 4] {
        // BLAKE2s pads the last block with zeros.
        //
        // Each word keeps its first `filled - 8i` bytes, clamped to `0..=8`:
        //
        //     filled = 20:  word 0 keeps 8,  word 1 keeps 8,  word 2 keeps 4,  words 3..8 keep 0
        //
        // Why a mask: a zeroing loop of unknown length becomes a `memset` call.
        for (i, word) in self.m.iter_mut().enumerate() {
            let keep = self.filled.saturating_sub(8 * i).min(8);
            *word &= if keep == 8 { u64::MAX } else { (1 << (8 * keep)) - 1 };
        }
        // The counter of the last block counts every byte of the message.
        compress(&self.h, &self.m, self.done + self.filled as u64, true)
    }

    pub fn hash(data: &[u8]) -> [u8; 32] {
        let mut hasher = Self::new();
        hasher.update(data);
        hasher.finalize()
    }

    /// Compress the block if it is full.
    #[inline(always)]
    fn make_room(&mut self) {
        if self.filled == 64 {
            // The counter covers every byte up to the end of this block.
            self.done += 64;
            self.h = compress(&self.h, &self.m, self.done, false);
            self.filled = 0;
        }
    }

    /// The message block as its 64 bytes.
    #[inline(always)]
    fn m_bytes(&mut self) -> &mut [u8; 64] {
        const { assert!(cfg!(target_endian = "little"), "the message words are little-endian") };
        // SAFETY: eight words are readable and writable as their 64 bytes.
        unsafe { &mut *(&raw mut self.m).cast() }
    }
}

/// The compression of a message block onto a chaining value, `t` bytes into the message:
/// the machine's instruction on the VM, portable Rust elsewhere.
#[inline(always)]
fn compress(h: &[u64; 4], m: &[u64; 8], t: u64, last: bool) -> [u64; 4] {
    #[cfg(all(target_arch = "riscv64", target_os = "none"))]
    {
        crate::precompile::blake2s_compress(h, m, t, last)
    }
    #[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
    {
        portable::compress(h, m, t, last)
    }
}

/// The compression function of RFC 7693, section 3.2, for a host.
#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
mod portable {
    /// The initialization vector, which also seeds the second half of the working vector.
    const IV: [u32; 8] = [
        0x6A09_E667,
        0xBB67_AE85,
        0x3C6E_F372,
        0xA54F_F53A,
        0x510E_527F,
        0x9B05_688C,
        0x1F83_D9AB,
        0x5BE0_CD19,
    ];
    /// The message word each round feeds to each mixing step.
    const SIGMA: [[usize; 16]; 10] = [
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

    /// The 32-bit little-endian lane `i` of a word array.
    fn lane(words: &[u64], i: usize) -> u32 {
        (words[i / 2] >> (32 * (i % 2))) as u32
    }

    pub fn compress(h: &[u64; 4], block: &[u64; 8], t: u64, last: bool) -> [u64; 4] {
        // The message as sixteen 32-bit words.
        let m: [u32; 16] = core::array::from_fn(|i| lane(block, i));
        // The working vector: the chaining value, then the IV.
        let mut v: [u32; 16] = core::array::from_fn(|i| if i < 8 { lane(h, i) } else { IV[i - 8] });
        // The 64-bit byte counter enters lanes 12 and 13.
        v[12] ^= t as u32;
        v[13] ^= (t >> 32) as u32;
        // The last block inverts lane 14.
        if last {
            v[14] = !v[14];
        }
        // Ten rounds: four column steps, then four diagonal steps.
        for s in &SIGMA {
            let mut g = |a: usize, b: usize, c: usize, d: usize, x: u32, y: u32| {
                v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
                v[d] = (v[d] ^ v[a]).rotate_right(16);
                v[c] = v[c].wrapping_add(v[d]);
                v[b] = (v[b] ^ v[c]).rotate_right(12);
                v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
                v[d] = (v[d] ^ v[a]).rotate_right(8);
                v[c] = v[c].wrapping_add(v[d]);
                v[b] = (v[b] ^ v[c]).rotate_right(7);
            };
            g(0, 4, 8, 12, m[s[0]], m[s[1]]);
            g(1, 5, 9, 13, m[s[2]], m[s[3]]);
            g(2, 6, 10, 14, m[s[4]], m[s[5]]);
            g(3, 7, 11, 15, m[s[6]], m[s[7]]);
            g(0, 5, 10, 15, m[s[8]], m[s[9]]);
            g(1, 6, 11, 12, m[s[10]], m[s[11]]);
            g(2, 7, 8, 13, m[s[12]], m[s[13]]);
            g(3, 4, 9, 14, m[s[14]], m[s[15]]);
        }
        // The new chaining value `h ^ v_lo ^ v_hi`, packed back into words.
        let word = |i: usize| u64::from(lane(h, i) ^ v[i] ^ v[i + 8]);
        core::array::from_fn(|k| word(2 * k) | word(2 * k + 1) << 32)
    }
}
