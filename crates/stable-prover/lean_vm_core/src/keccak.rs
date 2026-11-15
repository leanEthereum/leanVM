//! The `KECCAK` glue to the Keccak reduction ([`keccak_gkr`], Annex C), over the one commitment.
//!
//! The VM's `KECCAK` is Keccak-f\[1600\] of the 25 lanes thirteen cells hold, read and written each in one of two
//! layouts ([`cell_lanes`]). The committed column `q_keccak` holds every step's input lanes and its state every
//! [`DEPTH`] rounds before the output, a slot per lane and a word per step; the output is not committed. The
//! `KECCAK` table commits no lane of its own: a claim on an input lane is a claim on its slot of `q_keccak`, and the
//! claims on the output lanes are the reduction's claim on the permutation's output ([`keccak_gkr::OutputClaim`]).
//! The reduction proves the rounds between, and its two claims on `q_keccak` join the one opening.

use fiat_shamir::transcript::ProverState;
use keccak_gkr::witness::{BLOCK, block_lanes};
use keccak_gkr::{Openings, OutputClaim, Shape, Witness};
use primitives::field::{F64, F128};
use primitives::hash::STATE_LANES;

pub use isa::STATE_CELLS;

/// Rounds between two committed states.
pub const DEPTH: usize = 12;
/// The reduction's shape at its fewest steps.
pub const MIN_SHAPE: Shape = shape(0);
/// `log2` of `q_keccak`'s slots a step: one per lane of each committed state, rounded up to a power of two.
pub const SLOT_LOG: usize = MIN_SHAPE.slot_log();
/// Slots a step's committed states occupy: the ones from here to `2^SLOT_LOG` carry the KECCAK table's own columns
/// (`cpu::keccak_value`).
pub const SLOTS: usize = MIN_SHAPE.slots();
/// The fewest steps the reduction is sized for, one of its blocks.
pub const MIN_STEPS: usize = MIN_SHAPE.n();
/// Cells one `KECCAK` row flushes: thirteen read, thirteen written or, past what it writes, cancelled.
pub(crate) const ROW_CELLS: usize = 2 * STATE_CELLS;

const fn shape(n_steps: usize) -> Shape {
    Shape::new(n_steps, DEPTH)
}

/// `log2` of the steps the reduction proves for `n` executed ones.
pub(crate) fn n_steps_log(n: usize) -> usize {
    shape(n).n_log()
}

/// The lanes each state cell holds, `(lo, hi)`, in the even layout (`odd = false`) or the odd one, `None` marking a
/// limb that holds no lane: nine rate cells, lanes `0..16` two to a cell then lane 16 in a low limb (even), or lane 0
/// in a high limb then lanes `1..17` two to a cell (odd), then the capacity lanes `17..25` two to a cell. A block of a
/// message laid out in cells covers the nine rate cells of the layout of its parity.
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

/// The 25 lanes the thirteen state cells `cell(0..13)` hold in a layout.
pub(crate) fn state_of_cells(odd: bool, cell: impl Fn(usize) -> F128) -> [u64; STATE_LANES] {
    // The layout a constant, the loop compiles to straight-line moves.
    fn read<const ODD: bool>(cell: impl Fn(usize) -> F128) -> [u64; STATE_LANES] {
        let mut s = [0; STATE_LANES];
        for c in 0..STATE_CELLS {
            let (lo, hi) = const { cell_lanes(ODD) }[c];
            let w = cell(c);
            if let Some(l) = lo {
                s[l] = w.c0;
            }
            if let Some(h) = hi {
                s[h] = w.c1;
            }
        }
        s
    }
    if odd { read::<true>(cell) } else { read::<false>(cell) }
}

/// The thirteen state cells holding 25 lanes in a layout, a free limb zero.
pub(crate) fn cells_of_state(s: &[u64; STATE_LANES], odd: bool) -> [F128; STATE_CELLS] {
    let lanes = cell_lanes(odd);
    std::array::from_fn(|c| {
        let (lo, hi) = lanes[c];
        F128::new(lo.map_or(0, |l| s[l]), hi.map_or(0, |h| s[h]))
    })
}

/// What a `KECCAK` instruction writes, given the cells it reads.
#[cfg(test)]
pub(crate) fn permute_cells(cells: &[F128; STATE_CELLS], in_odd: bool, out_odd: bool) -> [F128; STATE_CELLS] {
    let mut s = state_of_cells(in_odd, |c| cells[c]);
    primitives::hash::keccak_f(&mut s);
    cells_of_state(&s, out_odd)
}

/// The reduction's sizes. Its witness, every round's state of every step, is rebuilt from `q_keccak`'s input states
/// when it runs: held from the witness build instead, it would sit beside the bus's trees, at the prover's peak.
pub(crate) struct Reduction {
    shape: Shape,
    steps: usize,
}

impl Reduction {
    /// Rebuild the witness from `q_keccak`, the whole committed column, and run the reduction.
    pub(crate) fn prove(self, ps: &mut ProverState, q_keccak: &[F64], output: &OutputClaim) -> Openings {
        let witness =
            tracing::info_span!("Witness").in_scope(|| Witness::from_committed(self.shape, self.steps, q_keccak));
        witness.prove(ps, q_keccak, output)
    }
}

/// Write the committed states of the steps `inputs`, padded with all-zero steps, over `q_keccak`'s first [`SLOTS`]
/// slots, `states`: the spare slots past them are their columns' to fill.
pub(crate) fn place(inputs: &[[u64; STATE_LANES]], states: &mut [F64]) -> Reduction {
    let shape = shape(inputs.len());
    assert_eq!(
        states.len(),
        shape.slots() * shape.n(),
        "the committed states are the wrong size"
    );
    let lanes = parallel::map_collect(inputs.len().div_ceil(BLOCK), |g| {
        block_lanes(shape.depth(), &inputs[g * BLOCK..((g + 1) * BLOCK).min(inputs.len())])
    });
    Witness::write_committed(shape, &lanes, states);
    Reduction {
        shape,
        steps: inputs.len(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(x: u64) -> F64 {
        F64(x)
    }

    /// The committed column for `instances`, padded with all-zero steps, and the reduction's
    /// witness.
    fn build_qkeccak(instances: &[[u64; STATE_LANES]]) -> (Vec<F64>, Witness) {
        let mut q_keccak = vec![F64::ZERO; 1 << shape(instances.len()).stack_log()];
        let states = SLOTS * (1 << n_steps_log(instances.len()));
        let witness = Witness::generate(shape(instances.len()), instances, &mut q_keccak[..states]);
        (q_keccak, witness)
    }

    fn sample_instances(n: usize) -> Vec<[u64; STATE_LANES]> {
        (0..n as u64)
            .map(|i| std::array::from_fn(|l| 0x0101_0101_0101_0101u64.wrapping_mul(i + 1) ^ l as u64))
            .collect()
    }

    /// The witness the reduction rebuilds from the committed column proves as the one built in one pass, whether
    /// the steps fill whole blocks, leave a partial one, or leave blocks of the batch with no step at all.
    #[test]
    fn rebuilt_witness_matches_one_pass() {
        for n in [0, 1, 511, 512, 513, 1500, 4099] {
            let instances = sample_instances(n);
            let (expected, reference) = build_qkeccak(&instances);
            let mut q_keccak = vec![f(0xdead_beef); expected.len()];
            let states = SLOTS * (1 << n_steps_log(n));
            let witness = place(&instances, &mut q_keccak[..states]);
            assert_eq!(q_keccak[..states], expected[..states], "{n} steps");
            // What the columns riding the spare slots left there is none of the reduction's
            // business, but both openings fold it, so the two runs have to see the same.
            q_keccak[states..].fill(f(0x5151_5151));
            let point = (0..n_steps_log(n)).map(|i| F128::new(3 + i as u64, 5)).collect();
            let output = OutputClaim::of_inputs(shape(n), &instances, point);
            let mut ps = ProverState::from_label(b"blocks");
            let deferred = (witness.prove(&mut ps, &q_keccak, &output), ps.into_proof());
            let mut ps = ProverState::from_label(b"blocks");
            let one_pass = (reference.prove(&mut ps, &q_keccak, &output), ps.into_proof());
            assert!(deferred == one_pass, "{n} steps");
        }
    }

    /// Both layouts round-trip, and a padded message laid out in cells, block `k`'s nine cells
    /// from cell `17k / 2` XORed into the previous output, read and written in the layout of each
    /// block's parity, the last written even, hashes to its Keccak-256.
    #[test]
    fn layouts_absorb_a_message() {
        use primitives::hash::{PAD_FIRST, PAD_LAST, RATE, permutations};
        let s: [u64; STATE_LANES] = std::array::from_fn(|i| 0x1111 * (i as u64 + 1));
        for odd in [false, true] {
            let cells = cells_of_state(&s, odd);
            assert_eq!(state_of_cells(odd, |c| cells[c]), s);
        }
        for n in [0, 1, 64, 127, 135, 136, 137, 200, 271, 272, 300, 543, 1000] {
            let msg: Vec<u8> = (0..n).map(|i| (i * 7 + 3) as u8).collect();
            let blocks = permutations(n);
            let mut padded = msg.clone();
            padded.resize(blocks * RATE + 8, 0);
            padded[n] ^= PAD_FIRST;
            padded[blocks * RATE - 1] ^= PAD_LAST;
            let cells: Vec<F128> = padded
                .as_chunks::<16>()
                .0
                .iter()
                .map(|c| {
                    let w = |k: usize| u64::from_le_bytes(c[8 * k..8 * k + 8].try_into().unwrap());
                    F128::new(w(0), w(1))
                })
                .collect();
            let mut state = [F128::ZERO; STATE_CELLS];
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
