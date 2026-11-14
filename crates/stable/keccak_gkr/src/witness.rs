//! The witness: every round's state before `chi`, sliced by bit position.
//!
//! A word holds one position of 64 instances, and a block is 512 instances: eight such words
//! per position, laid out position after position. Only every `depth`-th state is committed,
//! as lanes.

use primitives::field::F64;
use primitives::hash::{RC, ROUNDS};

use crate::keccak::{BITS, LANES, along, linear};

/// Instances a block holds, and the words one position of a block takes.
pub const BLOCK: usize = 512;
pub(crate) const BLOCK_WORDS: usize = 8;
/// Words one block of one state takes.
pub(crate) const BLOCK_LEN: usize = BITS * BLOCK_WORDS;

/// The eight words of position `j` of a sliced block.
#[inline(always)]
pub(crate) fn words(block: &[u64], j: usize) -> &[u64; BLOCK_WORDS] {
    block[j * BLOCK_WORDS..][..BLOCK_WORDS].try_into().expect("eight words")
}

/// Built only by [`Shape::new`], which bounds its sizes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    /// `log2` of the number of instances, at least 9.
    pub(crate) n_log: usize,
    /// Rounds between two committed states. Divides 24.
    pub(crate) depth: usize,
}

impl Shape {
    pub const fn new(n_instances: usize, depth: usize) -> Self {
        assert!(ROUNDS.is_multiple_of(depth), "depth must divide the round count");
        let n = if n_instances < BLOCK { BLOCK } else { n_instances };
        let n_log = n.next_power_of_two().ilog2() as usize;
        let shape = Self { n_log, depth };
        // Every size this crate derives is at most the `2^stack_log` words of the committed
        // block (`slots <= 2^slot_log`), so bounding that one keeps them all from wrapping.
        assert!(
            shape.stack_log() < usize::BITS as usize,
            "too many instances for one batch"
        );
        shape
    }

    pub const fn n_log(&self) -> usize {
        self.n_log
    }
    pub const fn depth(&self) -> usize {
        self.depth
    }
    pub const fn n(&self) -> usize {
        1 << self.n_log
    }
    pub const fn n_blocks(&self) -> usize {
        self.n() / BLOCK
    }
    pub const fn segments(&self) -> usize {
        ROUNDS / self.depth
    }
    pub const fn seg_log(&self) -> usize {
        self.segments().next_power_of_two().ilog2() as usize
    }
    /// Variables of a pack index: the instance index without its low four bits.
    pub(crate) const fn pack_vars(&self) -> usize {
        self.n_log - 4
    }
    /// Variables the layer sumcheck binds: a pack, then a segment.
    pub(crate) const fn y_vars(&self) -> usize {
        self.pack_vars() + self.seg_log()
    }
    /// Committed lanes per instance: the state each segment starts from.
    pub const fn slots(&self) -> usize {
        LANES * self.segments()
    }
    pub const fn slot_log(&self) -> usize {
        self.slots().next_power_of_two().ilog2() as usize
    }
    /// `log2` of the committed stack, in words.
    pub const fn stack_log(&self) -> usize {
        self.n_log + self.slot_log()
    }
    /// The round whose output segment `segment` claims after `step` layers.
    pub fn round(&self, segment: usize, step: usize) -> usize {
        self.depth * (segment + 1) - step
    }
}

pub struct Witness {
    pub shape: Shape,
    /// The blocks holding inputs, then, if blocks follow them, the padding block every later one
    /// equals: each every round's sliced state, round `r` at `r * BLOCK_LEN`, the input state
    /// being round 0.
    pub(crate) blocks: Vec<Vec<u64>>,
    pub(crate) written: usize,
}

/// Transpose a 64 by 64 bit matrix: bit `c` of row `r` becomes bit `r` of row `c`.
pub(crate) fn transpose64(a: &mut [u64; 64]) {
    let mut j = 32;
    let mut mask = 0x0000_0000_ffff_ffffu64;
    while j != 0 {
        for k in (0..64).filter(|k| k & j == 0) {
            let t = ((a[k] >> j) ^ a[k + j]) & mask;
            a[k + j] ^= t;
            a[k] ^= t << j;
        }
        j >>= 1;
        mask ^= mask << j;
    }
}

type Word = [u64; BLOCK_WORDS];

fn xor(a: Word, b: Word) -> Word {
    std::array::from_fn(|i| a[i] ^ b[i])
}

/// Run one block of instances, padded with all-zero inputs. Returns its committed lanes, slot `s`
/// at `s * BLOCK ..` and a word per instance, slot `s` being lane `s % 25` of the state after
/// `depth * (s / 25)` rounds: every state a segment starts from, the output not being committed.
/// With `keep`, it also returns its input state and the state each round applies `chi` to, all
/// sliced, round after round; without, the run ends at the last committed state.
pub(crate) fn run_block(depth: usize, inputs: &[[u64; LANES]], keep: bool) -> (Vec<u64>, Vec<u64>) {
    assert!(inputs.len() <= BLOCK);
    let mut state = vec![[0u64; BLOCK_WORDS]; BITS];
    let mut u = vec![[0u64; BLOCK_WORDS]; BITS];
    let mut rows = [0u64; 64];
    for lane in 0..LANES {
        for w in 0..BLOCK_WORDS {
            for (i, row) in rows.iter_mut().enumerate() {
                *row = inputs.get(64 * w + i).map_or(0, |x| x[lane]);
            }
            transpose64(&mut rows);
            for z in 0..64 {
                state[64 * lane + z][w] = rows[z];
            }
        }
    }
    let mut lanes = vec![0u64; LANES * (ROUNDS / depth) * BLOCK];
    let mut commit = |m: usize, state: &[Word]| {
        for lane in 0..LANES {
            for w in 0..BLOCK_WORDS {
                for z in 0..64 {
                    rows[z] = state[64 * lane + z][w];
                }
                transpose64(&mut rows);
                lanes[(LANES * m + lane) * BLOCK + 64 * w..][..64].copy_from_slice(&rows);
            }
        }
    };
    let mut rounds = Vec::with_capacity(if keep { (ROUNDS + 1) * BLOCK_LEN } else { 0 });
    let last = if keep { ROUNDS } else { ROUNDS - depth };
    if keep {
        rounds.extend_from_slice(state.as_flattened());
    }
    commit(0, &state);
    for round in 1..=last {
        linear(&state, &mut u, xor);
        if keep {
            rounds.extend_from_slice(u.as_flattened());
        }
        for lane in 0..LANES {
            let (a, b, c) = (64 * lane, along(64 * lane, 1), along(64 * lane, 2));
            // A lane's 64 positions are 512 consecutive words in each table: `chi` word by word
            // over them, which vectorizes with plain loads (by position, it took gathers).
            let flat = |at: usize| -> &[u64] { u[at..at + 64].as_flattened() };
            let (ua, ub, uc) = (flat(a), flat(b), flat(c));
            for (k, s) in state[a..a + 64].as_flattened_mut().iter_mut().enumerate() {
                *s = ua[k] ^ (!ub[k] & uc[k]);
            }
        }
        for z in (0..64).filter(|z| RC[round - 1] >> z & 1 == 1) {
            state[z] = state[z].map(|w| !w);
        }
        if round.is_multiple_of(depth) && round < ROUNDS {
            commit(round / depth, &state);
        }
    }
    (lanes, rounds)
}

/// One block's committed lanes alone: slot `s` at `s * BLOCK ..`, a word per instance.
///
/// Its rounds are not kept: the reduction rebuilds them from the committed column.
pub fn block_lanes(depth: usize, inputs: &[[u64; LANES]]) -> Vec<u64> {
    run_block(depth, inputs, false).0
}

impl Witness {
    /// Run every instance, padding the batch with all-zero inputs, and write the committed
    /// lanes into `committed`: lane `l` of the state after `depth * m` rounds, for `m` below the
    /// segment count, is slot `25 * m + l`, one word per instance. Whatever `committed` has past
    /// the last slot is zeroed, so a caller whose spare slots carry other columns (§cpu) passes
    /// the states' prefix alone. The blocks after the last input are run once, as the padding block.
    pub fn generate(shape: Shape, inputs: &[[u64; LANES]], committed: &mut [F64]) -> Self {
        assert!(inputs.len() <= shape.n());
        let written = inputs.len().div_ceil(BLOCK);
        let held = written + usize::from(written < shape.n_blocks());
        let (lanes, blocks): (Vec<_>, Vec<_>) = parallel::map_collect(held, |g| {
            let inputs = &inputs[(g * BLOCK).min(inputs.len())..((g + 1) * BLOCK).min(inputs.len())];
            run_block(shape.depth, inputs, true)
        })
        .into_iter()
        .unzip();
        Self::write_committed(shape, &lanes[..written], committed);
        Self { shape, blocks, written }
    }

    /// Write the committed lanes of every block into `committed`, laid out as `generate` does:
    /// `committed` holds at least the states' `slots * n` words and at most the whole block, and
    /// anything it has past the last slot is zeroed.
    ///
    /// - Block `g`'s lanes are `lanes[g]`.
    /// - The blocks past them are the padding block.
    pub fn write_committed(shape: Shape, lanes: &[Vec<u64>], committed: &mut [F64]) {
        let (n, slots) = (shape.n(), shape.slots());
        assert!(committed.len() >= slots * n && committed.len() <= 1 << shape.stack_log());
        let padding = (lanes.len() < shape.n_blocks()).then(|| block_lanes(shape.depth, &[]));
        let (states, spare) = committed.split_at_mut(slots * n);
        spare.fill(F64(0));
        parallel::chunks_mut(states, n, |slot, column| {
            for (g, out) in column.chunks_mut(BLOCK).enumerate() {
                let lanes = lanes.get(g).or(padding.as_ref()).expect("a padding block");
                for (out, &word) in out.iter_mut().zip(&lanes[slot * BLOCK..][..BLOCK]) {
                    *out = F64(word);
                }
            }
        });
    }

    /// The witness of the first `instances` instances, rebuilt from their committed inputs.
    ///
    /// - `committed` is laid out as `generate` writes it.
    /// - The blocks past the last input are the padding block.
    pub fn from_committed(shape: Shape, instances: usize, committed: &[F64]) -> Self {
        let n = shape.n();
        assert!(instances <= n && committed.len() >= LANES * n);
        let written = instances.div_ceil(BLOCK);
        let held = written + usize::from(written < shape.n_blocks());
        let blocks = parallel::map_collect(held, |g| {
            // Slot `l` holds lane `l` of every input, a word per instance. A step past the last
            // input reads the all-zero input the block pads with.
            let inputs: Vec<[u64; LANES]> = if g < written {
                (g * BLOCK..(g + 1) * BLOCK)
                    .map(|i| std::array::from_fn(|lane| committed[lane * n + i].0))
                    .collect()
            } else {
                Vec::new()
            };
            run_block(shape.depth, &inputs, true).1
        });
        Self { shape, blocks, written }
    }

    /// Blocks `written()..` of the batch are all the padding block, every instance of which is
    /// the all-zero input.
    pub fn written(&self) -> usize {
        self.written
    }

    /// Block `g` of the state round `round` applies `chi` to, rounds counted from 1, or of the
    /// input state for `round` 0, sliced.
    pub fn layer(&self, round: usize, g: usize) -> &[u64] {
        assert!(g < self.shape.n_blocks(), "a block of the batch");
        &self.blocks[g.min(self.written)][round * BLOCK_LEN..][..BLOCK_LEN]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keccak::{along, iota_bit};
    use primitives::test_rng::Rng;

    #[test]
    fn transpose_swaps_rows_and_columns() {
        let mut rng = Rng::new(8);
        let a: [u64; 64] = std::array::from_fn(|_| rng.next_u64());
        let mut t = a;
        transpose64(&mut t);
        for r in 0..64 {
            for c in 0..64 {
                assert_eq!(t[c] >> r & 1, a[r] >> c & 1);
            }
        }
    }

    #[test]
    fn committed_states_follow_the_permutation() {
        let mut rng = Rng::new(9);
        let inputs: Vec<[u64; LANES]> = (0..1100).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
        let shape = Shape::new(inputs.len(), 8);
        let mut committed = vec![F64(1); 1 << shape.stack_log()];
        Witness::generate(shape, &inputs, &mut committed);
        let n = shape.n();
        for x in (0..n).step_by(37) {
            let state = inputs.get(x).copied().unwrap_or([0; LANES]);
            for lane in 0..LANES {
                assert_eq!(committed[lane * n + x].0, state[lane]);
            }
            // The state after 16 rounds, bit by bit.
            let mut bits: Vec<bool> = (0..BITS).map(|j| state[j / 64] >> (j % 64) & 1 == 1).collect();
            for round in 1..=16 {
                let mut u = vec![false; BITS];
                linear(&bits, &mut u, |a, b| a ^ b);
                for j in 0..BITS {
                    bits[j] = u[j] ^ (!u[along(j, 1)] & u[along(j, 2)]) ^ (j < 64 && iota_bit(round, j));
                }
            }
            for lane in 0..LANES {
                let word = (0..64).fold(0u64, |w, z| w | (bits[64 * lane + z] as u64) << z);
                assert_eq!(committed[(2 * LANES + lane) * n + x].0, word, "instance {x}");
            }
        }
        assert!(committed[shape.slots() * n..].iter().all(|w| w.0 == 0));
    }

    /// A shape whose committed block would not fit a `usize` is refused, rather than wrapping.
    #[test]
    #[should_panic(expected = "too many instances")]
    fn an_unrepresentable_batch_is_refused() {
        Shape::new(1usize << 63, 12);
    }
}
