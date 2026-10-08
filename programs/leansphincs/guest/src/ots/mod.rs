//! The one-time signature: `v` hash chains, and the target-sum code that replaces
//! the Winternitz checksum (WOTS+C).
//!
//! Two codewords of equal sum are never ordered chunk by chunk.
//!
//! So a revealed signature gives a forger no chain value it could extend.

use crate::*;

/// `sk_{lay,tau,e,i}`: the start of chain `i`, derived from the master secret.
pub(crate) fn secret(pp: &PublicParam, master: &[u64; 4], pos: Pos, i: usize) -> Digest {
    th(pp, &tweak(TWEAK_PRF, pos.lay, pos.tau, i as u32, pos.e), master)
}

/// A key's one-time hashes, kept across its one-time keys: `Enc`'s, `tw | P | M | counter`, and `Chain`'s,
/// `tw | P | value`. Each writes only what changed: a one-time key its tweaks, an encoding its message and counter, a
/// step its tweak's position and its value.
pub(crate) struct Ots {
    encoding: Template<7>,
    step: Template<6>,
}

/// Bytes 4..8 of a tweak: its position `p`.
const TWEAK_POSITION: usize = 4;

/// The bytes `Enc` hashes: `tw | P | M`, then the counter's 4 bytes.
const ENCODING_LEN: usize = 8 * (PAYLOAD + 2) + 4;

impl Ots {
    pub(crate) fn new(pp: &PublicParam) -> Self {
        Self {
            encoding: Template::new([0, 0, pp[0], pp[1], 0, 0, 0]),
            step: Template::new([0, 0, pp[0], pp[1], 0, 0]),
        }
    }

    /// Move to the one-time key at `pos`.
    #[inline(always)]
    pub(crate) fn key(&mut self, pos: Pos) {
        self.encoding.set(0, tweak(TWEAK_ENC, pos.lay, pos.tau, 0, pos.e));
        self.step.set(0, tweak(TWEAK_CHAIN, pos.lay, pos.tau, 0, pos.e));
    }

    /// `Enc`: the codeword of `message` under `counter`, or `None` if it has none.
    ///
    /// Each 64-bit half of the digest is 21 chunks of `w` bits and a top bit pinned to zero.
    ///
    /// Pinning it makes the codeword determine the digest.
    #[inline(always)]
    pub(crate) fn encode(&mut self, message: &Digest, counter: u32) -> Option<Digits> {
        self.encoding.set(PAYLOAD, *message);
        // The counter is the message's last 4 bytes: the rest of its word is zero, as the hash pads it.
        self.encoding.set(PAYLOAD + 2, [u64::from(counter)]);
        let [low, high, ..] = self.encoding.digest_prefix::<ENCODING_LEN>();
        if (low | high) >> (W * V / 2) != 0 {
            return None;
        }
        let digits = Digits([low, high]);
        (digits.sum() == TARGET_SUM as u64).then_some(digits)
    }

    /// `Chain`: walk chain `i` for `steps` steps from value number `start`.
    ///
    /// The step out of value `s` is hashed at position `8i + s`, so no two steps share a tweak. Only the tweak's
    /// position field changes: the rest, `tau | e` included, is the key's.
    #[inline(always)]
    pub(crate) fn walk(&mut self, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
        let first = (CHAIN_LEN * i + start) as u32;
        self.step
            .chain::<TWEAK_POSITION, { 8 * PAYLOAD }>(first..first + steps as u32, value)
    }

    /// `Ots.leaf`: the leaf a one-time signature of the key at `pos` recovers, or `None` if `counter` gives no
    /// codeword.
    pub(crate) fn leaf(
        &mut self,
        pp: &PublicParam,
        pos: Pos,
        message: &Digest,
        counter: u32,
        ots: &[Digest; V],
    ) -> Option<Digest> {
        self.key(pos);
        let digits = self.encode(message, counter)?;
        // Chain `i` was opened at value `x_i`: walk it the rest of the way to value 7.
        Some(leaf_hash(pp, pos, |i| {
            let start = digits.get(i);
            self.walk(i, start, CHAIN_LEN - 1 - start, ots[i])
        }))
    }
}

/// The Merkle leaf of a one-time key: `Th` over its `v` chain ends, chain `i`'s being `end(i)`, the chains in
/// order, each written into the hash as it is reached.
///
/// The chains go in two halves, a codeword word each, so that a chain's chunk is at a fixed place in its word.
#[inline(always)]
pub(crate) fn leaf_hash(pp: &PublicParam, pos: Pos, mut end: impl FnMut(usize) -> Digest) -> Digest {
    digest(hash_with(|m| {
        m.write(tweak(TWEAK_LEAF, pos.lay, pos.tau, 0, pos.e))
            .write(*pp)
            .write_each(V / 2, &mut end)
            .write_each(V / 2, |i| end(V / 2 + i));
    }))
}

/// A codeword: `v` chunks of `w` bits, 21 to a word, where each chain is opened.
#[derive(Clone, Copy)]
pub(crate) struct Digits([u64; 2]);

impl Digits {
    /// Chunk `i`: bits `3r..3r+3` of word `i / 21`, `r = i % 21`.
    pub(crate) const fn get(self, i: usize) -> usize {
        (self.0[i / (V / 2)] >> (W * (i % (V / 2)))) as usize & (CHAIN_LEN - 1)
    }

    /// The sum of the chunks, by adding neighbouring fields in place.
    ///
    /// No field overflows into the next: the top bits are zero, a chunk is at most 7, and all of them sum to at
    /// most 294.
    const fn sum(self) -> u64 {
        let [low, high] = self.0;
        // 7 in every 6-bit field: the even chunks.
        const EVEN: u64 = 0x71C7_1C71_C71C_71C7;
        // 63 in every 12-bit field.
        const LOW6: u64 = 0xF03F_03F0_3F03_F03F;
        // Four chunks to a 6-bit field, two of each word: at most 28.
        let s = (low & EVEN) + (low >> W & EVEN) + (high & EVEN) + (high >> W & EVEN);
        // Two fields to a 12-bit field: at most 56.
        let s = (s & LOW6) + (s >> 6 & LOW6);
        // The six fields, folded into the lowest.
        let s = s + (s >> 12);
        let s = s + (s >> 24);
        (s + (s >> 48)) & 0xFFF
    }
}
