// CREDIT: https://github.com/succinctlabs/flock (flock-prover), MIT OR Apache-2.0.
//! The packed witness tables, and the parallel drivers every witness generator fills them through.
//! A generator writes one instance's rows through `InstanceRows`.

use parallel::Chunks;
use primitives::stream::Stream;

/// The bytes of packed words, on a little-endian target.
pub(crate) const fn packed_bytes(words: &[u64]) -> &[u8] {
    const _: () = assert!(
        cfg!(target_endian = "little"),
        "packed witness bytes assume little-endian"
    );
    // SAFETY: `u64` has no padding or invalid bit patterns, and `u8`'s alignment divides `u64`'s.
    // So the words are a valid byte slice of eight times their length.
    unsafe { core::slice::from_raw_parts(words.as_ptr().cast::<u8>(), words.len() * 8) }
}

/// One circuit's witness over a batch of instances, as the prover holds it.
///
/// Each table packs 64 bits a word, `2^k_log / 64` words per instance, instance-major.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Witness {
    /// The witness bits.
    pub z: Vec<u64>,

    /// The left factor of every constraint, `A z`.
    pub az: Vec<u64>,

    /// The right factor of every constraint, `B z`.
    pub bz: Vec<u64>,
}

/// A witness whose bits live in the caller's buffer: the two factor tables.
///
/// A committed batch's bits are its column of the commitment, written there in place.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Tables {
    /// The left factor of every constraint, `A z`.
    pub az: Vec<u64>,

    /// The right factor of every constraint, `B z`.
    pub bz: Vec<u64>,
}

/// One group of instances' share of the three tables, in its worker's scratch.
///
/// Each table holds the group's instances one after another, `2^k_log / 64` words each.
pub(crate) struct GroupTables<'a> {
    /// The witness bits.
    pub z: &'a mut [u64],

    /// `A z`.
    pub a: &'a mut [u64],

    /// `B z`.
    pub b: &'a mut [u64],
}

/// The shape of a batch: `2^n_blocks_log` instances of `2^k_log` bits each.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Batch {
    /// The base-two logarithm of the instance count.
    pub n_blocks_log: usize,

    /// The base-two logarithm of the bits per instance.
    pub k_log: usize,
}

impl Batch {
    /// Packed words per instance.
    const fn words(self) -> usize {
        (1 << self.k_log) / 64
    }

    /// Packed words per table.
    const fn total_words(self) -> usize {
        self.words() << self.n_blocks_log
    }

    /// A whole witness: the bits are allocated here, then the driver fills them and builds the factor tables.
    pub(crate) fn witness(self, drive: impl FnOnce(&mut [u64]) -> Tables) -> Witness {
        let mut z = Box::<[u64]>::new_uninit_slice(self.total_words());
        // SAFETY: every driver writes all of the bits and reads none of them first.
        let Tables { az, bz } = drive(unsafe { primitives::write_only(&mut z) });
        Witness {
            // SAFETY: the driver wrote every word.
            z: unsafe { z.assume_init() }.into_vec(),
            az,
            bz,
        }
    }

    /// Fill the tables `group` instances at a time, the bits into `z`.
    ///
    /// - `fill(state, first, tables)` writes every word of the group whose first instance is `first`.
    /// - Each worker builds its `state` once, by `init`, and reuses it across its groups.
    /// - `check(i, z)` sees instance `i`'s bits while its group is still in cache.
    ///
    /// A group builds in its worker's scratch, which stays in cache, then streams out.
    /// Building in place instead would fetch every output line before writing it.
    ///
    /// # Panics
    ///
    /// When groups do not tile the batch, or `z` is not one table long.
    pub(crate) fn fill_groups<St, I, F>(
        self,
        z: &mut [u64],
        group: usize,
        init: I,
        fill: F,
        check: impl Fn(usize, &[u64]) + Sync,
    ) -> Tables
    where
        St: Send,
        I: Fn() -> St + Sync,
        F: Fn(&mut St, usize, GroupTables<'_>) + Sync,
    {
        let words = self.words();
        assert!(
            (1usize << self.n_blocks_log).is_multiple_of(group),
            "a group of {group} instances must tile 2^{} of them",
            self.n_blocks_log
        );
        assert_eq!(z.len(), self.total_words(), "z holds every instance's words");
        let mut a = Box::<[u64]>::new_uninit_slice(z.len());
        let mut b = Box::<[u64]>::new_uninit_slice(z.len());

        // Each group owns one chunk of every table.
        let group_words = group * words;
        let z_chunks = Chunks::new(z, group_words);
        let a_chunks = Chunks::new(&mut a, group_words);
        let b_chunks = Chunks::new(&mut b, group_words);

        parallel::map_reduce_with_state(
            z_chunks.count(),
            || (vec![0u64; 3 * group_words], init()),
            || (),
            |(scratch, state), (), g| {
                // Phase 1: build the group in the worker's scratch.
                let (z_grp, rest) = scratch.split_at_mut(group_words);
                let (a_grp, b_grp) = rest.split_at_mut(group_words);
                fill(
                    state,
                    g * group,
                    GroupTables {
                        z: z_grp,
                        a: a_grp,
                        b: b_grp,
                    },
                );

                // Phase 2: show each instance's bits while they are hot.
                for (i, z) in z_grp.chunks_exact(words).enumerate() {
                    check(g * group + i, z);
                }

                // Phase 3: publish the group without reading the destination first.
                let stream = Stream::new();
                // SAFETY: group `g` takes chunk `g` of each table exactly once.
                // All three tables stay borrowed for the whole dispatch.
                unsafe {
                    stream.copy(z_chunks.get(g), z_grp);
                    stream.write(a_chunks.get(g), a_grp);
                    stream.write(b_chunks.get(g), b_grp);
                }
            },
            |(), ()| (),
        );

        // SAFETY: group `g` wrote chunk `g` of both tables in full, and the chunks cover them.
        unsafe {
            Tables {
                az: a.assume_init().into_vec(),
                bz: b.assume_init().into_vec(),
            }
        }
    }

    /// Fill the tables one instance at a time, eight per group.
    ///
    /// - `instance(row, z, a, b)` sets one instance's bits in three zeroed buffers of `2^k_log / 64` words.
    /// - The instances past `rows` take `padding`: a real instance, so the constant wire is one in every instance.
    ///
    /// # Panics
    ///
    /// When there are more rows than instances.
    pub(crate) fn fill_instances<S: Sync>(
        self,
        z: &mut [u64],
        rows: &[S],
        padding: &S,
        instance: impl Fn(&S, &mut [u64], &mut [u64], &mut [u64]) + Sync,
        check: impl Fn(usize, &[u64]) + Sync,
    ) -> Tables {
        assert!(rows.len() <= 1 << self.n_blocks_log, "more rows than instances");
        let words = self.words();
        self.fill_groups(
            z,
            8,
            || (),
            |(), first, t| {
                // An instance only sets bits, so the group starts from zero.
                for table in [&mut *t.z, &mut *t.a, &mut *t.b] {
                    table.fill(0);
                }
                // Each instance owns `words` consecutive words of each table.
                let tables = (t.z.chunks_exact_mut(words))
                    .zip(t.a.chunks_exact_mut(words))
                    .zip(t.b.chunks_exact_mut(words));
                for (l, ((z, a), b)) in tables.enumerate() {
                    instance(rows.get(first + l).unwrap_or(padding), z, a, b);
                }
            },
            check,
        )
    }

    /// Fill the tables eight instances at a time.
    ///
    /// `batch(rows, z, a, b)` sets the eight instances' bits in three zeroed group buffers, instance-major.
    ///
    /// # Panics
    ///
    /// When there are more rows than instances.
    pub(crate) fn fill_batches8<S: Sync>(
        self,
        z: &mut [u64],
        rows: &[S],
        padding: &S,
        batch: impl Fn([&S; 8], &mut [u64], &mut [u64], &mut [u64]) + Sync,
        check: impl Fn(usize, &[u64]) + Sync,
    ) -> Tables {
        assert!(rows.len() <= 1 << self.n_blocks_log, "more rows than instances");
        self.fill_groups(
            z,
            8,
            || (),
            |(), first, t| {
                // The callback ORs product runs into a fresh group.
                for table in [&mut *t.z, &mut *t.a, &mut *t.b] {
                    table.fill(0);
                }
                let inputs = std::array::from_fn(|l| rows.get(first + l).unwrap_or(padding));
                batch(inputs, t.z, t.a, t.b);
            },
            check,
        )
    }
}

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
