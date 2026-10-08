//! SHAKE256 over 64-bit lanes: a sponge over the SDK's `Keccak-f[1600]` permutation.

use leanvm_guest::keccak::{RATE, f1600};

/// SHAKE256 absorbing whole 64-bit lanes: a message of whole words.
#[derive(Clone)]
pub struct Shake256 {
    /// The Keccak state.
    state: [u64; 25],
    /// The next lane of the rate to absorb into.
    lane: usize,
}

impl Shake256 {
    /// The empty sponge.
    pub const fn new() -> Self {
        Self {
            state: [0; 25],
            lane: 0,
        }
    }

    /// Absorb words, little-endian: each word is the next eight bytes.
    pub fn absorb(&mut self, words: &[u64]) {
        for &w in words {
            self.state[self.lane] ^= w;
            self.lane += 1;
            if self.lane == RATE {
                f1600(&mut self.state);
                self.lane = 0;
            }
        }
    }

    /// Pad and switch to squeezing.
    ///
    /// SHAKE's padding: the suffix bits `1111`, then `10*1`, at the byte after the message.
    pub fn finalize(mut self) -> Squeeze {
        self.state[self.lane] ^= 0x1F;
        self.state[RATE - 1] ^= 0x80 << 56;
        f1600(&mut self.state);
        Squeeze {
            state: self.state,
            lane: 0,
        }
    }
}

impl Default for Shake256 {
    fn default() -> Self {
        Self::new()
    }
}

/// SHAKE256's output, one lane at a time.
pub struct Squeeze {
    /// The Keccak state.
    state: [u64; 25],
    /// The next lane of the rate to output.
    lane: usize,
}

impl Squeeze {
    /// The next eight bytes of output, as a little-endian word.
    pub fn next_lane(&mut self) -> u64 {
        if self.lane == RATE {
            f1600(&mut self.state);
            self.lane = 0;
        }
        let lane = self.state[self.lane];
        self.lane += 1;
        lane
    }
}
