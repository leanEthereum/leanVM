//! One instance's packed tables, as a witness generator writes its rows into them.

/// A packed bit table being written: 64 bits a word, low bit first.
///
/// Writes only OR bits in, so a zeroed table can take its rows in any order.
struct BitsMut<'a>(&'a mut [u64]);

impl BitsMut<'_> {
    /// OR the bits of `words`, low word first, in from bit `at`.
    ///
    /// ```text
    ///     bit at + i  |=  bit i of words
    /// ```
    ///
    /// Bits that would land past the table's end must be zero, and are dropped.
    #[inline(always)]
    fn or_words(&mut self, at: usize, words: &[u64]) {
        let shift = at % 64;
        let mut targets = self.0[at / 64..].iter_mut();
        // The high bits of each word spill into the next target.
        let mut spill = 0;
        // `words` leads the zip: it is polled first, so no target is drawn past the last word.
        for (&word, target) in words.iter().zip(&mut targets) {
            *target |= (word << shift) | spill;
            // `(word >> 1) >> (63 - shift)` is `word >> (64 - shift)`, with no shift by 64 at `shift = 0`.
            spill = (word >> 1) >> (63 - shift);
        }
        if let Some(target) = targets.next() {
            *target |= spill;
        }
    }

    /// OR the bits of `value` in from bit `at`.
    #[inline(always)]
    fn or(&mut self, at: usize, value: u128) {
        self.or_words(at, &[value as u64, (value >> 64) as u64]);
    }
}

/// One instance's `z`, `A z` and `B z`, which a witness generator ORs its rows into.
///
/// Each table is the instance's `2^k_log / 64` packed words, zeroed before the rows are written.
pub(crate) struct InstanceRows<'a> {
    /// The witness bits.
    z: BitsMut<'a>,

    /// The left factor of every row, `A z`.
    az: BitsMut<'a>,

    /// The right factor of every row, `B z`.
    bz: BitsMut<'a>,
}

impl<'a> InstanceRows<'a> {
    /// The rows of the instance whose tables are `z`, `az` and `bz`.
    pub(crate) const fn new(z: &'a mut [u64], az: &'a mut [u64], bz: &'a mut [u64]) -> Self {
        Self {
            z: BitsMut(z),
            az: BitsMut(az),
            bz: BitsMut(bz),
        }
    }

    /// Product rows from `slot`, one per set position of `mask`, packed down to consecutive slots.
    ///
    /// ```text
    ///     A z = left      B z = right      z = left * right        at each position of mask
    /// ```
    #[inline]
    pub(crate) fn products(&mut self, slot: usize, mask: u128, left: u128, right: u128) {
        if mask != 0 {
            // The mask is one run of positions, so a shift packs it into consecutive slots.
            let shift = mask.trailing_zeros();
            self.z.or(slot, (left & right & mask) >> shift);
            self.az.or(slot, (left & mask) >> shift);
            self.bz.or(slot, (right & mask) >> shift);
        }
    }
}

#[cfg(test)]
mod tests {
    use primitives::test_util::Rng;

    use super::*;

    #[test]
    fn or_words_lands_every_bit_at_its_offset() {
        // Invariant: bit `i` of the words lands at bit `at + i`, at every alignment, and nothing else moves.
        //
        // Fixture state: three words ORed into a five-word table, at every offset that keeps them inside it.
        let mut rng = Rng::new(0xB175_0FF5);
        for at in 0..=64 * 5 - 192 {
            let words = [rng.next_u64(), rng.next_u64(), rng.next_u64()];
            let mut table = [0u64; 5];
            BitsMut(&mut table).or_words(at, &words);
            for bit in 0..64 * 5 {
                let want = bit >= at && bit < at + 192 && words[(bit - at) / 64] >> ((bit - at) % 64) & 1 == 1;
                assert_eq!(table[bit / 64] >> (bit % 64) & 1 == 1, want, "at={at}, bit={bit}");
            }
        }

        // Mutation: the same words ending exactly at the table's last bit drop no set bit.
        let mut table = [0u64; 3];
        BitsMut(&mut table).or_words(0, &[u64::MAX; 3]);
        assert_eq!(table, [u64::MAX; 3]);
    }
}
