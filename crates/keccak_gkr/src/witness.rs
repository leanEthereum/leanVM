//! The witness: every round's state before `chi`, sliced by bit position.
//!
//! A word holds one position of 64 instances, and a block is 512 instances: eight such words
//! per position, laid out position after position. Only every `depth`-th state is committed,
//! as lanes.

use parallel::SendPtr;
use primitives::field::F64;
use primitives::hash::{RC, ROUNDS};

use crate::keccak::{BITS, LANES, linear};

/// Instances a block holds, and the words one position of a block takes.
pub const BLOCK: usize = 512;
pub const BLOCK_WORDS: usize = 8;
/// Words one block of one state takes.
pub const BLOCK_LEN: usize = BITS * BLOCK_WORDS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    /// `log2` of the number of instances, at least 9.
    pub n_log: usize,
    /// Rounds between two committed states. Divides 24.
    pub depth: usize,
}

impl Shape {
    pub fn new(n_instances: usize, depth: usize) -> Self {
        assert!(ROUNDS.is_multiple_of(depth), "depth must divide the round count");
        let n_log = n_instances.max(BLOCK).next_power_of_two().ilog2() as usize;
        Self { n_log, depth }
    }

    pub fn n(&self) -> usize {
        1 << self.n_log
    }
    pub fn n_blocks(&self) -> usize {
        self.n() / BLOCK
    }
    pub fn segments(&self) -> usize {
        ROUNDS / self.depth
    }
    pub fn seg_log(&self) -> usize {
        self.segments().next_power_of_two().ilog2() as usize
    }
    /// Variables of a pack index: the instance index without its low four bits.
    pub fn pack_vars(&self) -> usize {
        self.n_log - 4
    }
    /// Variables the layer sumcheck binds: a pack, then a segment.
    pub fn y_vars(&self) -> usize {
        self.pack_vars() + self.seg_log()
    }
    /// Committed lanes per instance: the state each segment starts from.
    pub fn slots(&self) -> usize {
        LANES * self.segments()
    }
    pub fn slot_log(&self) -> usize {
        self.slots().next_power_of_two().ilog2() as usize
    }
    /// `log2` of the committed stack, in words.
    pub fn stack_log(&self) -> usize {
        self.n_log + self.slot_log()
    }
    /// The round whose output segment `segment` claims after `step` layers.
    pub fn round(&self, segment: usize, step: usize) -> usize {
        self.depth * (segment + 1) - step
    }
}

/// A run of blocks, round after round: block `first + i` of round `r` (the input state being
/// round 0) is at word `(r * blocks + i) * BLOCK_LEN`.
pub struct Extent {
    first: usize,
    blocks: usize,
    words: Vec<u64>,
}

/// Where one block of an [`Extent`] goes.
#[derive(Clone, Copy)]
pub struct Slot {
    base: SendPtr<u64>,
    stride: usize,
}

impl Extent {
    /// An extent for blocks `first .. first + blocks`, none of them written yet. A block is
    /// read only through a [`Witness`], whose builder vouches for the ones [`block`] wrote.
    pub fn new(first: usize, blocks: usize) -> Self {
        // SAFETY: nothing reads a block that `Witness::from_extents` was not told is written.
        let words = unsafe { primitives::uninit_vec((ROUNDS + 1) * blocks * BLOCK_LEN) };
        Self { first, blocks, words }
    }

    pub fn end(&self) -> usize {
        self.first + self.blocks
    }

    /// The slot of block `g`, which must be one of this extent's. Slots of distinct blocks
    /// are disjoint.
    pub fn slot(&mut self, g: usize) -> Slot {
        assert!((self.first..self.end()).contains(&g));
        Slot {
            // SAFETY: the block's first round lies in the buffer.
            base: SendPtr(unsafe { self.words.as_mut_ptr().add((g - self.first) * BLOCK_LEN) }),
            stride: self.blocks * BLOCK_LEN,
        }
    }

    fn round(&self, round: usize, g: usize) -> &[u64] {
        &self.words[(round * self.blocks + g - self.first) * BLOCK_LEN..][..BLOCK_LEN]
    }
}

pub struct Witness {
    pub shape: Shape,
    /// The first `written` blocks of the batch, in order. The others are all `padding`.
    extents: Vec<Extent>,
    written: usize,
    padding: Option<Extent>,
}

/// Transpose a 64 by 64 bit matrix: bit `c` of row `r` becomes bit `r` of row `c`.
#[inline]
pub fn transpose64(a: &mut [u64; 64]) {
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

/// Run one block of instances, padded with all-zero inputs, and write its input state and the
/// state each round applies `chi` to, all sliced, into `slot`. `commit(slot, w, lanes)` receives lane `slot % 25`
/// of the state after `depth * (slot / 25)` rounds, for instances `64 * w ..` of the block: every
/// state a segment starts from, the output not being committed.
///
/// # Safety
/// `slot` is a slot of a live [`Extent`] that no other call is writing.
pub unsafe fn block(
    depth: usize,
    inputs: &[[u64; LANES]],
    slot: Slot,
    mut commit: impl FnMut(usize, usize, &[u64; 64]),
) {
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
    let mut lanes = |m: usize, state: &[Word]| {
        let mut rows = [0u64; 64];
        for lane in 0..LANES {
            for w in 0..BLOCK_WORDS {
                for z in 0..64 {
                    rows[z] = state[64 * lane + z][w];
                }
                transpose64(&mut rows);
                commit(LANES * m + lane, w, &rows);
            }
        }
    };
    // A round's state is next read by the layer that proves it, long after this pass.
    let stream = primitives::stream::Stream::new();
    // SAFETY: the slot holds a block of every round.
    let store = |round: usize, words: &[Word]| unsafe {
        stream.copy_uninit(slot.base.add(round * slot.stride), words.as_flattened());
    };
    store(0, &state);
    lanes(0, &state);
    for round in 1..=ROUNDS {
        linear(&state, &mut u, xor);
        store(round, &u);
        for row in 0..5 {
            for x in 0..5 {
                let (a, b, c) = (
                    64 * (x + 5 * row),
                    64 * ((x + 1) % 5 + 5 * row),
                    64 * ((x + 2) % 5 + 5 * row),
                );
                for z in 0..64 {
                    state[a + z] = std::array::from_fn(|i| u[a + z][i] ^ (!u[b + z][i] & u[c + z][i]));
                }
            }
        }
        for z in (0..64).filter(|z| RC[round - 1] >> z & 1 == 1) {
            state[z] = state[z].map(|w| !w);
        }
        if round.is_multiple_of(depth) && round < ROUNDS {
            lanes(round / depth, &state);
        }
    }
}

impl Witness {
    /// Run every instance, padding the batch with all-zero inputs, and write the committed
    /// lanes into `committed`: lane `l` of the state after `depth * m` rounds, for `m` below the
    /// segment count, is slot `25 * m + l`, one word per instance, and whatever follows the last
    /// slot is zeroed.
    pub fn generate(shape: Shape, inputs: &[[u64; LANES]], committed: &mut [F64]) -> Self {
        let n = shape.n();
        assert!(inputs.len() <= n);
        assert!(committed.len() >= shape.slots() * n && committed.len() <= 1 << shape.stack_log());
        committed[shape.slots() * n..].fill(F64(0));
        let committed_ptr = SendPtr(committed.as_mut_ptr());
        let mut extent = Extent::new(0, shape.n_blocks());
        let slots: Vec<Slot> = (0..shape.n_blocks()).map(|g| extent.slot(g)).collect();
        parallel::for_each(shape.n_blocks(), |g| {
            let inputs = &inputs[(g * BLOCK).min(inputs.len())..((g + 1) * BLOCK).min(inputs.len())];
            let stream = primitives::stream::Stream::new();
            // SAFETY: block `g` owns its slot, and its instances' words of every committed lane.
            unsafe {
                block(shape.depth, inputs, slots[g], |slot, w, lanes| {
                    stream.copy_uninit(committed_ptr.add(slot * n + g * BLOCK + 64 * w).cast::<u64>(), lanes)
                })
            };
        });
        Self {
            shape,
            extents: vec![extent],
            written: shape.n_blocks(),
            padding: None,
        }
    }

    /// The witness of extents whose first `written` blocks [`block`] wrote: consecutive from
    /// block 0, the batch's remaining blocks all being `padding`, a one-block extent of no
    /// instance.
    ///
    /// # Safety
    /// [`block`] has written blocks `0 .. written` of `extents`, and `padding`'s one block.
    pub unsafe fn from_extents(shape: Shape, extents: Vec<Extent>, written: usize, padding: Option<Extent>) -> Self {
        let mut end = 0;
        for extent in &extents {
            assert_eq!(extent.first, end, "extents are consecutive");
            end = extent.end();
        }
        assert!(written <= end && written <= shape.n_blocks());
        assert!(written == shape.n_blocks() || padding.as_ref().is_some_and(|p| p.blocks == 1));
        Self {
            shape,
            extents,
            written,
            padding,
        }
    }

    fn round(&self, round: usize, g: usize) -> &[u64] {
        if g >= self.written {
            let padding = self.padding.as_ref().expect("a block of the batch");
            return padding.round(round, padding.first);
        }
        let extent = self.extents.iter().find(|e| g < e.end()).expect("a written block");
        extent.round(round, g)
    }

    /// Block `g` of the input state, sliced.
    pub fn input(&self, g: usize) -> &[u64] {
        self.round(0, g)
    }

    /// Block `g` of the state round `round` applies `chi` to, rounds counted from 1.
    pub fn layer(&self, round: usize, g: usize) -> &[u64] {
        self.round(round, g)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keccak::{along, iota_bit};
    use primitives::test_rng::Rng;

    #[test]
    fn committed_states_follow_the_permutation() {
        let mut rng = Rng::new(9);
        let inputs: Vec<[u64; LANES]> = (0..700).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
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
}
