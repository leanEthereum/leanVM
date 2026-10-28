//! Bridge to the Keccak prover ([`keccak_gkr`]), single-PCS.
//!
//! The committed states of every `KECCAK` step are one column of leanVM's ONE stacked `F64`
//! witness (§sec:stacking), a lane per slot and a word per step, with no separate commitment:
//! the input and the state after every `DEPTH` rounds before the output. The output is not
//! committed. The VM's `KECCAK` table commits no value column of its own: a claim on an input lane is
//! a claim on its slot of that column, and the claims on the output lanes are the reduction's
//! claim on the permutation's output ([`keccak_gkr::OutputClaim`]). The GKR reduction proves the
//! rounds between, and its openings join the batch-mixed opening ([`::pcs::stack_open`]): the
//! column's bit slices as the ring-switched claim, the committed states after the input as a
//! point claim.
//!
//! ## The mapping
//!
//! The VM's `KECCAK` is Keccak-f\[1600\] of the 25 lanes thirteen cells hold, written to thirteen
//! cells, each side in one of two layouts ([`cell_lanes`]). The committed input is the lanes
//! the VM reads, and the output is the permutation's, written as it is.

use keccak_gkr::witness::{BLOCK, Extent, Slot, block_lanes};
use keccak_gkr::{Shape, Witness};
use primitives::field::{F64, F192};
use primitives::hash::STATE_LANES;

/// Rounds between two committed states.
pub const DEPTH: usize = 12;
/// The reduction's shape at its fewest steps.
const MIN_SHAPE: Shape = shape(0);
/// `log2` of the slots the committed column holds per step: one per lane of each state but the
/// output, rounded up to a power of two.
pub const SLOT_LOG: usize = MIN_SHAPE.slot_log();
/// Slots of a step the committed states occupy, one per lane of each: the ones from here to
/// `2^SLOT_LOG` carry no state, and the KECCAK table's own columns ride them
/// (`cpu::keccak_value`).
pub const SLOTS: usize = MIN_SHAPE.slots();
/// The fewest steps the reduction is sized for, one of its blocks.
pub const MIN_STEPS: usize = MIN_SHAPE.n();

/// `log2` of the steps the reduction proves for `n` executed ones.
pub fn n_steps_log(n: usize) -> usize {
    shape(n).n_log()
}

const fn shape(n_steps: usize) -> Shape {
    Shape::new(n_steps, DEPTH)
}

/// `log2` of the committed column, in words.
pub fn qkeccak_kappa(n_steps: usize) -> usize {
    shape(n_steps).stack_log()
}

/// Cells a sponge state occupies.
pub const STATE_CELLS: usize = 13;
/// The rate cells of a state, the nine a block of a message laid out in cells covers.
pub const RATE_CELLS: usize = 9;
/// Cells one `KECCAK` row touches: thirteen read, thirteen written.
pub const ROW_CELLS: usize = 2 * STATE_CELLS;

/// The lanes each state cell holds, `(lo, hi)`, in the even layout (`odd = false`) or the odd
/// one, `None` marking a limb that holds no lane: nine rate cells, lanes `0..16` two to a cell
/// then lane 16 in a low limb (even), or lane 0 in a high limb then lanes `1..17` two to a cell
/// (odd), then the capacity lanes `17..25` two to a cell. A block of a message laid out in cells
/// covers the nine rate cells of the layout of its parity.
pub const fn cell_lanes(odd: bool) -> [(Option<usize>, Option<usize>); STATE_CELLS] {
    let mut t = [(None, None); STATE_CELLS];
    let mut c = 0;
    while c < STATE_CELLS {
        t[c] = if c >= 9 || (odd && c >= 1) {
            (Some(2 * c - 1), Some(2 * c))
        } else if odd {
            (None, Some(0))
        } else if c == 8 {
            (Some(16), None)
        } else {
            (Some(2 * c), Some(2 * c + 1))
        };
        c += 1;
    }
    t
}

/// The 25 lanes thirteen state cells hold in a layout.
pub fn state_of_cells(cells: &[F192; STATE_CELLS], odd: bool) -> [u64; STATE_LANES] {
    let mut s = [0u64; STATE_LANES];
    for (cell, (lo, hi)) in cells.iter().zip(cell_lanes(odd)) {
        if let Some(lo) = lo {
            s[lo] = cell.c0;
        }
        if let Some(hi) = hi {
            s[hi] = cell.c1;
        }
    }
    s
}

/// The thirteen canonical state cells holding 25 lanes in a layout, a free lane zero.
pub fn cells_of_state(s: &[u64; STATE_LANES], odd: bool) -> [F192; STATE_CELLS] {
    let lanes = cell_lanes(odd);
    std::array::from_fn(|c| {
        let (lo, hi) = lanes[c];
        F192::new(lo.map_or(0, |l| s[l]), hi.map_or(0, |h| s[h]), 0)
    })
}

/// What a `KECCAK` instruction writes, given the cells it reads.
#[cfg(test)]
pub(crate) fn permute_cells(cells: &[F192; STATE_CELLS], in_odd: bool, out_odd: bool) -> [F192; STATE_CELLS] {
    let mut s = state_of_cells(cells, in_odd);
    primitives::hash::keccak_f(&mut s);
    cells_of_state(&s, out_odd)
}

/// The reduction's witness: every round's state of every step, kept from the pass that wrote
/// the committed column until the reduction has run.
pub(crate) type PreparedReductionWitness = Witness;

/// The reduction's witness for the steps a program ran, built while it ran: every whole block
/// of steps, its rounds in `extents` and its committed lanes in `lanes`, slot after slot.
pub(crate) struct Blocks {
    extents: Vec<Extent>,
    lanes: Vec<Vec<u64>>,
    steps: usize,
}

/// Run `run`, which reports the lanes of each step it executes, and build the reduction's
/// witness behind it: executing is one thread's work, so the others take each block of steps
/// as it completes instead of waiting for the last.
pub(crate) fn while_executing<R>(run: impl FnOnce(&mut dyn FnMut(&[u64; STATE_LANES])) -> R) -> (R, Blocks) {
    type Job = (usize, Vec<[u64; STATE_LANES]>, Slot);
    let (jobs, queue) = std::sync::mpsc::channel::<Job>();
    let queue = std::sync::Mutex::new(queue);
    // More workers than this slow the executing thread by more than they finish early.
    let workers = parallel::num_threads() / 2;
    // Outlives the scope: the workers write into it until they are joined, even on a panic.
    let mut extents: Vec<Extent> = Vec::new();
    let (result, lanes, steps) = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                scope.spawn(|| {
                    let mut done = Vec::new();
                    loop {
                        let job = queue.lock().expect("a worker panicked").recv();
                        let Ok((g, steps, slot)) = job else { break };
                        // SAFETY: the job owns its slot.
                        done.push((g, unsafe { block_lanes(DEPTH, &steps, slot) }));
                    }
                    done
                })
            })
            .collect();

        let mut inline = Vec::new();
        let mut pending = Vec::with_capacity(BLOCK);
        let mut blocks = 0;
        let mut steps = 0;
        let mut dispatch = |pending: &mut Vec<[u64; STATE_LANES]>, last: bool| {
            if extents.last().is_none_or(|e| e.end() == blocks) {
                extents.push(Extent::new(blocks, blocks.max(8)));
            }
            let slot = extents.last_mut().expect("an extent").slot(blocks);
            let block = std::mem::replace(pending, Vec::with_capacity(BLOCK));
            if workers == 0 || last {
                // SAFETY: the block owns its slot.
                inline.push((blocks, unsafe { block_lanes(DEPTH, &block, slot) }));
            } else {
                jobs.send((blocks, block, slot)).expect("the workers outlive the run");
            }
            blocks += 1;
        };
        let result = run(&mut |state| {
            pending.push(*state);
            steps += 1;
            if pending.len() == BLOCK {
                dispatch(&mut pending, false);
            }
        });
        if !pending.is_empty() {
            dispatch(&mut pending, true);
        }
        drop(jobs);
        let mut lanes = inline;
        for handle in handles {
            lanes.extend(handle.join().expect("a witness worker panicked"));
        }
        lanes.sort_unstable_by_key(|&(g, _)| g);
        let lanes = lanes.into_iter().map(|(_, lanes)| lanes).collect();
        (result, lanes, steps)
    });
    (result, Blocks { extents, lanes, steps })
}

impl Blocks {
    /// Write the committed states of the `steps` steps these blocks hold, padded with
    /// all-zero steps, and hand the reduction its witness. `q_keccak` is the states' part of
    /// the committed block, its first [`SLOTS`] slots: the spare slots past them belong to the
    /// columns that ride there and are written by their own fill.
    pub(crate) fn place(self, steps: usize, q_keccak: &mut [F64]) -> PreparedReductionWitness {
        assert_eq!(self.steps, steps, "the blocks are of another run");
        let shape = shape(self.steps);
        assert_eq!(
            q_keccak.len(),
            shape.slots() * shape.n(),
            "the committed states are the wrong size"
        );
        // SAFETY: `while_executing` ran block `g` into its slot of `extents`, in order, its
        // lanes being `lanes[g]`.
        unsafe { Witness::from_blocks(shape, self.extents, &self.lanes, q_keccak) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::ProverState;
    use keccak_gkr::OutputClaim;

    fn f(x: u64) -> F64 {
        F64(x)
    }

    /// The committed column for `instances`, padded with all-zero steps, and the reduction's
    /// witness.
    fn build_qkeccak(instances: &[[u64; STATE_LANES]]) -> (Vec<F64>, Witness) {
        let mut q_keccak = vec![F64::ZERO; 1 << qkeccak_kappa(instances.len())];
        let states = SLOTS * (1 << n_steps_log(instances.len()));
        let witness = Witness::generate(shape(instances.len()), instances, &mut q_keccak[..states]);
        (q_keccak, witness)
    }

    fn sample_instances(n: usize) -> Vec<[u64; STATE_LANES]> {
        (0..n as u64)
            .map(|i| std::array::from_fn(|l| 0x0101_0101_0101_0101u64.wrapping_mul(i + 1) ^ l as u64))
            .collect()
    }

    /// The witness built behind a run is the one a single pass over its steps builds: the same
    /// committed column and the same reduction, whether the steps fill whole blocks, leave a
    /// partial one, or leave blocks of the batch with no step at all.
    #[test]
    fn blocks_built_while_executing_match_one_pass() {
        for n in [0, 1, 511, 512, 513, 1500, 4099] {
            let instances = sample_instances(n);
            let (expected, reference) = build_qkeccak(&instances);
            let ((), blocks) = while_executing(|step| {
                for state in &instances {
                    step(state);
                }
            });
            let mut q_keccak = vec![f(0xdead_beef); expected.len()];
            let states = SLOTS * (1 << n_steps_log(n));
            let witness = blocks.place(n, &mut q_keccak[..states]);
            assert_eq!(q_keccak[..states], expected[..states], "{n} steps");
            // What the columns riding the spare slots left there is none of the reduction's
            // business, but both openings fold it, so the two runs have to see the same.
            q_keccak[states..].fill(f(0x5151_5151));
            let point = (0..n_steps_log(n)).map(|i| F192::new(3 + i as u64, 5, 7)).collect();
            let output = OutputClaim::of_inputs(shape(n), &instances, point);
            let stream = |witness: &Witness| {
                let mut ps = ProverState::from_label(b"blocks");
                let openings = witness.prove(&mut ps, &q_keccak, &output);
                (openings, ps.into_proof())
            };
            assert!(stream(&witness) == stream(&reference), "{n} steps");
        }
    }

    /// Both layouts round-trip, and a padded message laid out in cells, block `k`'s nine cells
    /// from cell `17k / 2` XORed into the previous output, read and written in the layout of each
    /// block's parity, the last written even, hashes to its Keccak-256.
    #[test]
    fn layouts_absorb_a_message() {
        use primitives::hash::{PAD_FIRST, PAD_LAST, RATE};
        let s: [u64; STATE_LANES] = std::array::from_fn(|i| 0x1111 * (i as u64 + 1));
        for odd in [false, true] {
            assert_eq!(state_of_cells(&cells_of_state(&s, odd), odd), s);
        }
        for n in [0, 1, 64, 127, 135, 136, 137, 200, 271, 272, 300, 543, 1000] {
            let msg: Vec<u8> = (0..n).map(|i| (i * 7 + 3) as u8).collect();
            let blocks = n / RATE + 1;
            let mut padded = msg.clone();
            padded.resize(blocks * RATE + 8, 0);
            padded[n] ^= PAD_FIRST;
            padded[blocks * RATE - 1] ^= PAD_LAST;
            let cells: Vec<F192> = padded
                .as_chunks::<16>()
                .0
                .iter()
                .map(|c| {
                    let w = |k: usize| u64::from_le_bytes(c[8 * k..8 * k + 8].try_into().unwrap());
                    F192::new(w(0), w(1), 0)
                })
                .collect();
            let mut state = [F192::ZERO; STATE_CELLS];
            for k in 0..blocks {
                for (j, cell) in state.iter_mut().take(9).enumerate() {
                    *cell += cells[17 * k / 2 + j];
                }
                state = permute_cells(&state, k % 2 == 1, k + 1 < blocks && k % 2 == 0);
            }
            let digest: Vec<u8> = [state[0].c0, state[0].c1, state[1].c0, state[1].c1]
                .iter()
                .flat_map(|w| w.to_le_bytes())
                .collect();
            assert_eq!(digest, primitives::hash::hash(&msg), "{n} bytes");
        }
    }

    /// The committed column holds every step's input lanes, a word per step. The output lanes
    /// have no slot.
    #[test]
    fn qkeccak_words_match_layout() {
        let instances = sample_instances(5);
        let (q_keccak, _) = build_qkeccak(&instances);
        let n = 1usize << n_steps_log(instances.len());
        for (j, input) in instances.iter().enumerate() {
            for i in 0..STATE_LANES {
                assert_eq!(q_keccak[i * n + j], f(input[i]));
            }
        }
    }
}
