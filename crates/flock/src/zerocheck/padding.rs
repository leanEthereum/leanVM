//! Where a batched witness is zero or repeats itself, so the zerocheck's kernels can skip it.

use primitives::field::F192;

/// Where the padding of a batched witness lies.
///
/// The witness is `2^(m - k_log)` blocks of `2^k_log` bits, each its data first and zero padding after.
/// A run of zero bits adds nothing to a round message, so skipping it leaves the message unchanged.
///
/// The blocks from `live_blocks` on are copies of one padding block.
/// While the rounds bind variables inside a block, the kernels sum one copy, weighted by the tail's eq mass.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Padding {
    /// The base-two logarithm of the bits in one block.
    pub k_log: usize,

    /// The bits at the start of each block that carry data; the rest are zero.
    pub useful_bits: usize,

    /// The blocks before the identical tail; at least the block count when there is none.
    pub live_blocks: usize,
}

impl Padding {
    /// Every bit of a cube of `2^m` bits useful, and no tail.
    #[cfg(test)]
    pub(crate) const fn dense(m: usize) -> Self {
        Self {
            k_log: m,
            useful_bits: 1 << m,
            live_blocks: 1,
        }
    }

    /// The same blocks, with no tail known.
    pub(crate) const fn without_tail(self) -> Self {
        Self {
            live_blocks: usize::MAX,
            ..self
        }
    }

    /// Split a kernel's cube of `2^m` bits at the tail, or `None` when that saves nothing.
    ///
    /// - The head is a whole number of groups and of `2^step_log`-bit steps, the kernel's unit of work.
    /// - A group is a block, or enough whole blocks for the kernel's smallest cube, `2^min_group_log` bits.
    /// - `r` are the kernel's eq challenges, the last of which index the groups.
    /// - The cube's last group stands for every group past the head: they are all copies of it.
    pub(crate) fn tail(&self, m: usize, min_group_log: usize, step_log: usize, r: &[F192]) -> Option<Tail> {
        // Groups of at least one block, and at most the cube.
        let group_log = self.k_log.max(min_group_log);
        if group_log >= m {
            return None;
        }
        let n_groups_log = m - group_log;

        // The groups holding a live block, rounded up to whole steps.
        let live_groups = self.live_blocks.div_ceil(1 << (group_log - self.k_log));
        if live_groups >= 1 << n_groups_log {
            return None;
        }
        let first = live_groups.next_multiple_of(1 << step_log.saturating_sub(group_log));
        if first >= 1 << n_groups_log {
            return None;
        }
        Some(Tail {
            head: first << group_log,
            group_log,
            r_inner: r.len() - n_groups_log,
            weight: eq_mass_from(&r[r.len() - n_groups_log..], first),
        })
    }
}

/// A kernel's cube split by its tail: the head it sums as is, then its last group once for the rest.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Tail {
    /// Bits in the head.
    pub head: usize,

    /// The base-two logarithm of the bits in a group.
    pub group_log: usize,

    /// The eq challenges inside a group: the kernel's first `r_inner`.
    pub r_inner: usize,

    /// The eq mass of the groups past the head.
    pub weight: F192,
}

impl Tail {
    /// The last group's bytes of a packed witness.
    pub(crate) fn group<'a>(&self, packed: &'a [u8]) -> &'a [u8] {
        &packed[packed.len() - (1 << self.group_log) / 8..]
    }
}

/// `sum_{x >= from} eq(r, x)`, `x` read low bit first.
///
/// The whole cube's mass is one, so this is one plus the mass below `from`.
fn eq_mass_from(r: &[F192], from: usize) -> F192 {
    let mut below = F192::ZERO;
    // The eq factor of the bits above the current one, set to `from`'s.
    let mut above = F192::ONE;
    for (k, &r_k) in r.iter().enumerate().rev() {
        if from >> k & 1 == 1 {
            // Every `x` agreeing above and with this bit clear lies below `from`.
            below += above * (F192::ONE + r_k);
            above *= r_k;
        } else {
            above *= F192::ONE + r_k;
        }
    }
    F192::ONE + below
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::eq_table;
    use primitives::test_util::Rng;

    #[test]
    fn eq_mass_from_is_the_tables_suffix_sum() {
        // Invariant: the closed form is the eq table summed from `from` on, at every index of a small cube.
        let mut rng = Rng::new(0xE0_3A55);
        for n in 0..6 {
            let r = rng.ext_vec(n);
            let table = eq_table(&r);
            for from in 0..1usize << n {
                let want = table[from..].iter().fold(F192::ZERO, |acc, &e| acc + e);
                assert_eq!(eq_mass_from(&r, from), want, "n={n}, from={from}");
            }
        }
    }
}
