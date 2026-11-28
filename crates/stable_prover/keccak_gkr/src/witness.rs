//! The witness: every round's state before `chi`, sliced by bit position.
//!
//! A word holds one position of 64 instances, and a block is 512 instances: eight such words
//! per position, laid out position after position. Only every `depth`-th state is committed,
//! as lanes.

use primitives::field::F64;
use primitives::hash::positions::{iota_bit, linear};
use primitives::hash::{ROUNDS, STATE_LANES};
use verifier::keccak::BITS;

use crate::kernels::{along, xor};

/// Instances a block holds, and the words one position of a block takes.
pub const BLOCK: usize = 512;
pub(crate) const BLOCK_WORDS: usize = 8;
/// Words one block of one state takes.
pub(crate) const BLOCK_LEN: usize = BITS * BLOCK_WORDS;

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
    /// Committed lanes per instance: the state each segment starts from.
    pub const fn slots(&self) -> usize {
        STATE_LANES * self.segments()
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

/// Every round's state before `chi`, sliced, block by block.
pub struct Witness {
    pub shape: Shape,
    /// The blocks holding inputs, then the padding block if any block follows them, which every later one equals:
    /// per block, every round's sliced state, round `r` at `r * BLOCK_LEN`, the input state being round 0.
    pub(crate) blocks: Vec<Vec<u64>>,
    /// The blocks holding inputs: every later one is the padding block, each instance of which is the all-zero input.
    pub(crate) written: usize,
}

/// Transpose a 64 by 64 bit matrix: bit `c` of row `r` becomes bit `r` of row `c`. Out of line: one copy for every
/// caller.
#[inline(never)]
pub(crate) fn transpose64(a: &mut [u64; 64]) {
    // Swap the off-diagonal `j` by `j` blocks of every `2j` by `2j` block, `j` halving: rows `i` and `i + j` of a
    // block, which the compiler vectorizes over `i`.
    const MASKS: [u64; 6] = [
        0x0000_0000_ffff_ffff,
        0x0000_ffff_0000_ffff,
        0x00ff_00ff_00ff_00ff,
        0x0f0f_0f0f_0f0f_0f0f,
        0x3333_3333_3333_3333,
        0x5555_5555_5555_5555,
    ];
    for (level, mask) in MASKS.into_iter().enumerate() {
        let j = 32 >> level;
        for block in a.chunks_exact_mut(2 * j) {
            let (low, high) = block.split_at_mut(j);
            for (a, b) in low.iter_mut().zip(high) {
                let t = ((*a >> j) ^ *b) & mask;
                *b ^= t;
                *a ^= t << j;
            }
        }
    }
}

/// Where the blocks' inputs are read, lane `l` of instance `i`: the instances' lanes, or `count` instances of a
/// committed block, lane `l` of instance `i` at `l * n + i`. Past the inputs, every instance is the all-zero input.
#[derive(Clone, Copy)]
pub(crate) enum Inputs<'a> {
    Rows(&'a [[u64; STATE_LANES]]),
    Committed { words: &'a [F64], n: usize, count: usize },
}

impl Inputs<'_> {
    fn len(self) -> usize {
        match self {
            Self::Rows(rows) => rows.len(),
            Self::Committed { count, .. } => count,
        }
    }

    fn lane(self, i: usize, lane: usize) -> u64 {
        match self {
            Self::Rows(rows) => rows.get(i).map_or(0, |x| x[lane]),
            Self::Committed { words, n, count } => {
                if i < count {
                    words[lane * n + i].0
                } else {
                    0
                }
            }
        }
    }
}

/// Run block `g` of `inputs`. Without `keep`, returns its committed lanes, slot `s` at `s * BLOCK ..` and a word per
/// instance, slot `s` being lane `s % 25` of the state after `depth * (s / 25)` rounds: every state a segment starts
/// from, the output not being committed. With `keep`, returns its input state and the state each round applies `chi`
/// to, all sliced, round after round.
pub(crate) fn run_block(depth: usize, inputs: Inputs, g: usize, keep: bool) -> Vec<u64> {
    let (mut state, mut u) = (vec![0u64; BLOCK_LEN], vec![0u64; BLOCK_LEN]);
    let (state, u) = (
        state.as_chunks_mut::<BLOCK_WORDS>().0,
        u.as_chunks_mut::<BLOCK_WORDS>().0,
    );
    let mut rows = [0u64; 64];
    for lane in 0..STATE_LANES {
        for w in 0..BLOCK_WORDS {
            for (i, row) in rows.iter_mut().enumerate() {
                *row = inputs.lane(BLOCK * g + 64 * w + i, lane);
            }
            transpose64(&mut rows);
            for z in 0..64 {
                state[64 * lane + z][w] = rows[z];
            }
        }
    }
    let (len, last) = match keep {
        true => ((ROUNDS + 1) * BLOCK_LEN, ROUNDS),
        false => (STATE_LANES * (ROUNDS / depth) * BLOCK, ROUNDS - depth),
    };
    let mut out = Vec::with_capacity(len);
    for round in 0..=last {
        if round > 0 {
            linear(state, u, xor);
            for lane in 0..STATE_LANES {
                let (a, b, c) = (64 * lane, along(64 * lane, 1), along(64 * lane, 2));
                // A lane's 64 positions are 512 consecutive words in each table: `chi` word by word
                // over them, which vectorizes with plain loads (by position, it took gathers).
                let flat = |at: usize| -> &[u64] { u[at..at + 64].as_flattened() };
                let (ua, ub, uc) = (flat(a), flat(b), flat(c));
                for (k, s) in state[a..a + 64].as_flattened_mut().iter_mut().enumerate() {
                    *s = ua[k] ^ (!ub[k] & uc[k]);
                }
            }
            for z in (0..64).filter(|&z| iota_bit(round, z)) {
                for w in &mut state[z] {
                    *w = !*w;
                }
            }
        }
        if keep {
            out.extend_from_slice(if round == 0 { &*state } else { &*u }.as_flattened());
        } else if round.is_multiple_of(depth) {
            // The lanes of the state a segment starts from, slot after slot.
            for lane in 0..STATE_LANES {
                for w in 0..BLOCK_WORDS {
                    for z in 0..64 {
                        rows[z] = state[64 * lane + z][w];
                    }
                    transpose64(&mut rows);
                    out.extend_from_slice(&rows);
                }
            }
        }
    }
    out
}

/// [`run_block`] of each block holding inputs, then of the padding block if any block follows them.
fn run_blocks(shape: Shape, inputs: Inputs, keep: bool) -> Vec<Vec<u64>> {
    let written = inputs.len().div_ceil(BLOCK);
    let held = written + usize::from(written < shape.n_blocks());
    parallel::map_collect(held, |g| run_block(shape.depth, inputs, g, keep))
}

/// Run every instance of `inputs`, padding the batch with all-zero inputs, and write the committed states into
/// `states`, the first `slots * n` words of the committed block: lane `l` of the state after `depth * m` rounds, for
/// `m` below the segment count, is slot `25 * m + l`, one word per instance. The slots past them are the caller's: in
/// the VM other columns ride them (`lean_vm_core::cpu::keccak_value`). The blocks after the last input are run once,
/// as the padding block.
pub fn commit_states(shape: Shape, inputs: &[[u64; STATE_LANES]], states: &mut [F64]) {
    let n = shape.n();
    assert!(inputs.len() <= n);
    assert_eq!(
        states.len(),
        shape.slots() * n,
        "the committed states are the wrong size"
    );
    let lanes = run_blocks(shape, Inputs::Rows(inputs), false);
    parallel::chunks_mut(states, n, |slot, column| {
        for (g, out) in column.chunks_mut(BLOCK).enumerate() {
            let lanes = &lanes[g.min(lanes.len() - 1)];
            for (out, &word) in out.iter_mut().zip(&lanes[slot * BLOCK..][..BLOCK]) {
                *out = F64(word);
            }
        }
    });
}

impl Witness {
    /// [`commit_states`] over the first `slots * n` words of `committed`, then the witness rebuilt from them.
    pub fn generate(shape: Shape, inputs: &[[u64; STATE_LANES]], committed: &mut [F64]) -> Self {
        let states = &mut committed[..shape.slots() * shape.n()];
        commit_states(shape, inputs, states);
        Self::from_committed(shape, inputs.len(), states)
    }

    /// The witness of the first `instances` instances, rebuilt from their committed inputs.
    ///
    /// - `committed` is laid out as [`commit_states`] writes it.
    /// - The blocks past the last input are the padding block.
    pub fn from_committed(shape: Shape, instances: usize, committed: &[F64]) -> Self {
        let n = shape.n();
        assert!(instances <= n && committed.len() >= STATE_LANES * n);
        let inputs = Inputs::Committed {
            words: committed,
            n,
            count: instances,
        };
        Self {
            shape,
            blocks: run_blocks(shape, inputs, true),
            written: instances.div_ceil(BLOCK),
        }
    }

    /// The blocks held: those written, then the padding block if any block follows them.
    pub(crate) fn held(&self) -> usize {
        self.blocks.len()
    }

    /// Block `g` of the state round `round` applies `chi` to, rounds counted from 1, or of the
    /// input state for `round` 0, sliced.
    pub(crate) fn layer(&self, round: usize, g: usize) -> &[u64] {
        assert!(g < self.shape.n_blocks(), "a block of the batch");
        &self.blocks[g.min(self.written)][round * BLOCK_LEN..][..BLOCK_LEN]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let inputs: Vec<[u64; STATE_LANES]> = (0..1100).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
        let shape = Shape::new(inputs.len(), 8);
        let mut committed = vec![F64(0); 1 << shape.stack_log()];
        Witness::generate(shape, &inputs, &mut committed);
        let n = shape.n();
        for x in (0..n).step_by(37) {
            let state = inputs.get(x).copied().unwrap_or([0; STATE_LANES]);
            for lane in 0..STATE_LANES {
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
            for lane in 0..STATE_LANES {
                let word = (0..64).fold(0u64, |w, z| w | (bits[64 * lane + z] as u64) << z);
                assert_eq!(committed[(2 * STATE_LANES + lane) * n + x].0, word, "instance {x}");
            }
        }
    }

    /// A shape whose committed block would not fit a `usize` is refused, rather than wrapping.
    #[test]
    #[should_panic(expected = "too many instances")]
    fn an_unrepresentable_batch_is_refused() {
        Shape::new(1usize << 63, 12);
    }
}
