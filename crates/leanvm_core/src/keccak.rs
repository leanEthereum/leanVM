//! Bridge to the Keccak prover ([`keccak_gkr`]), single-PCS.
//!
//! The committed states of every `SHA3` step are one column of leanVM's ONE stacked `F64`
//! witness (§sec:stacking), a lane per slot and a word per step, with no separate commitment:
//! the input and the state after every `DEPTH` rounds before the output. The output is not
//! committed. The VM's `SHA3` table has no value column of its own: a claim on an input lane is
//! a claim on its slot of that column, and the claims on the output lanes are the reduction's
//! claim on the permutation's output ([`keccak_gkr::OutputClaim`]). The GKR reduction proves the
//! rounds between, and its openings join the batch-mixed opening ([`::pcs::stack_open`]): the
//! column's bit slices as the ring-switched claim, the committed states after the input as a
//! point claim.
//!
//! ## The mapping
//!
//! The VM's `SHA3(m, tail, cap) -> out` is one [`primitives::hash::step`] on the
//! 25 lanes those thirteen cells hold, written to thirteen cells in the same
//! order ([`CELL_LANES`]). A step is the permutation after [`END_BIT`] is XORed into lane 16,
//! so the committed input is the lanes the VM reads with that bit flipped, and a claim on the
//! VM's lane 16 moves to the committed one by that constant ([`value_slot`]). The output is the
//! permutation's, written as it is.

use crate::pcs::SlotClaim;
use crate::transcript::{ProverState, VerifierState};
use keccak_gkr::witness::{BLOCK, Extent, Slot};
use keccak_gkr::{Openings, OutputClaim, Shape, VerifyError};
use primitives::field::{F64, F192};
use primitives::hash::{END_BIT, END_LANE, STATE_LANES};

pub use crate::pcs::{RingSwitchClaim, RingSwitchOpen, RingSwitchVerify};

/// Rounds between two committed states.
pub const DEPTH: usize = 12;
/// Committed states of a step: its input and those between, not its output.
const STATES: usize = primitives::hash::ROUNDS / DEPTH;
/// `log2` of the slots the committed column holds per step: one per lane of each state, rounded
/// up to a power of two.
pub const SLOT_LOG: usize = (STATE_LANES * STATES).next_power_of_two().ilog2() as usize;
/// The fewest steps the reduction is sized for, one of its blocks, and its `log2`.
pub const MIN_STEPS: usize = 1 << MIN_STEPS_LOG;
const MIN_STEPS_LOG: usize = 9;

/// `log2` of the steps the reduction proves for `n` executed ones.
pub fn n_blocks_log(n: usize) -> usize {
    (n.max(1).next_power_of_two().ilog2() as usize).max(MIN_STEPS_LOG)
}

fn shape(n_blocks: usize) -> Shape {
    Shape {
        n_log: n_blocks_log(n_blocks),
        depth: DEPTH,
    }
}

/// Domain separator for the relation in the Fiat-Shamir seed (`leanvm_core::cpu`): the hash of
/// a label naming the reduction and everything fixed about it. A deliberate change bumps the
/// label, and the digest is mirrored in `python-verifier/verifier.py` and in the recursion guest.
pub fn relation_digest() -> [u8; 32] {
    primitives::hash::hash(RELATION_LABEL)
}
pub const RELATION_LABEL: &[u8] =
    b"leanVM keccak GKR: step, depth 12, packs of 16 in degree 23, lane slots, output claimed by the bus";

/// `log2` of the committed column, in words.
pub fn qkeccak_kappa(n_blocks: usize) -> usize {
    n_blocks_log(n_blocks) + SLOT_LOG
}

/// Cells a sponge state occupies.
pub const STATE_CELLS: usize = 13;
/// Cells one `SHA3` row touches: thirteen read, thirteen written.
pub const ROW_CELLS: usize = 2 * STATE_CELLS;
/// The state cell holding lane 16 alone, its high lane zero.
pub const LONE_CELL: usize = 8;

/// The lanes each state cell holds, `(lo, hi)`, where a `None` high lane is a
/// literal zero: lanes 0..16 two to a cell (the eight cells a block's 128 message
/// bytes fill), then lane 16 alone, then the capacity lanes 17..25.
pub const CELL_LANES: [(usize, Option<usize>); STATE_CELLS] = {
    let mut t = [(0usize, None); STATE_CELLS];
    let mut c = 0;
    while c < STATE_CELLS {
        t[c] = if c < LONE_CELL {
            (2 * c, Some(2 * c + 1))
        } else if c == LONE_CELL {
            (16, None)
        } else {
            (2 * c - 1, Some(2 * c))
        };
        c += 1;
    }
    t
};

/// What a claim on value column `i`, in `tables::SHA3_VALUE_COLS` order, is of the committed
/// column: an input lane's slot, and the constant the committed lane differs from the VM's by.
/// An output lane has none.
pub fn value_slot(i: usize) -> Option<(usize, F192)> {
    let shift = if i == END_LANE {
        F192::new(END_BIT, 0, 0)
    } else {
        F192::ZERO
    };
    (i < STATE_LANES).then_some((i, shift))
}

/// The 25 lanes thirteen state cells hold.
pub fn state_of_cells(cells: &[F192; STATE_CELLS]) -> [u64; STATE_LANES] {
    let mut s = [0u64; STATE_LANES];
    for (cell, &(lo, hi)) in cells.iter().zip(&CELL_LANES) {
        s[lo] = cell.c0;
        if let Some(hi) = hi {
            s[hi] = cell.c1;
        }
    }
    s
}

/// The thirteen state cells holding 25 lanes (canonical: top limbs zero, and the
/// lone cell's high lane zero).
pub fn cells_of_state(s: &[u64; STATE_LANES]) -> [F192; STATE_CELLS] {
    std::array::from_fn(|c| {
        let (lo, hi) = CELL_LANES[c];
        F192::new(s[lo], hi.map_or(0, |hi| s[hi]), 0)
    })
}

/// What a `SHA3` instruction writes, given the thirteen cells it reads.
pub fn step_cells(cells: &[F192; STATE_CELLS]) -> [F192; STATE_CELLS] {
    cells_of_state(&primitives::hash::step(&state_of_cells(cells)))
}

/// The reduction's witness: every round's state of every step, kept from the pass that wrote
/// the committed column until the reduction has run.
pub(crate) struct PreparedReductionWitness(keccak_gkr::Witness);

impl PreparedReductionWitness {
    /// The openings of the committed column the reduction leaves, the output being `output`.
    pub(crate) fn prove(&self, ps: &mut ProverState, q_keccak: &[F64], output: &OutputClaim) -> Openings {
        keccak_gkr::prove(ps, &self.0, q_keccak, output)
    }
}

/// The permutation's input for the lanes a step reads. A padding step reads zeros.
fn permuted(mut state: [u64; STATE_LANES]) -> [u64; STATE_LANES] {
    state[END_LANE] ^= END_BIT;
    state
}

/// Build the committed column for `instances`, the lanes each step reads, padded with all-zero
/// steps to `2^n_blocks_log(instances.len())`, and keep the reduction's witness.
#[cfg(test)]
pub(crate) fn build_qkeccak_prepared(
    instances: &[[u64; STATE_LANES]],
    q_keccak: &mut [F64],
) -> PreparedReductionWitness {
    let shape = shape(instances.len());
    assert_eq!(
        q_keccak.len(),
        1 << shape.stack_log(),
        "the committed column is the wrong size"
    );
    let inputs: Vec<[u64; STATE_LANES]> = parallel::map_collect(shape.n(), |i| {
        permuted(instances.get(i).copied().unwrap_or([0; STATE_LANES]))
    });
    PreparedReductionWitness(keccak_gkr::Witness::generate(shape, &inputs, q_keccak))
}

/// The reduction's witness for the steps a program ran, built while it ran: every whole block
/// of steps, its rounds in `extents` and its committed lanes in `lanes`, slot after slot.
pub(crate) struct Blocks {
    extents: Vec<Extent>,
    lanes: Vec<Vec<u64>>,
    steps: usize,
}

/// One block's rounds into `slot`, and its committed lanes.
///
/// # Safety
/// As [`keccak_gkr::witness::block`].
unsafe fn run_block(steps: &[[u64; STATE_LANES]], slot: Slot) -> Vec<u64> {
    let mut inputs = [permuted([0; STATE_LANES]); BLOCK];
    inputs[..steps.len()].copy_from_slice(steps);
    // SAFETY: every word is written, a slot's lanes for each of the block's eight words.
    let mut lanes = unsafe { primitives::uninit_vec::<u64>((STATE_LANES * STATES) * BLOCK) };
    // SAFETY: forwarded to the caller.
    unsafe {
        keccak_gkr::witness::block(DEPTH, &inputs, slot, |slot, w, words| {
            lanes[slot * BLOCK + 64 * w..][..64].copy_from_slice(words)
        })
    };
    lanes
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
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                scope.spawn(|| {
                    let mut done = Vec::new();
                    loop {
                        let job = queue.lock().expect("a worker panicked").recv();
                        let Ok((g, steps, slot)) = job else { break };
                        // SAFETY: the job owns its slot.
                        done.push((g, unsafe { run_block(&steps, slot) }));
                    }
                    done
                })
            })
            .collect();

        let mut extents: Vec<Extent> = Vec::new();
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
                inline.push((blocks, unsafe { run_block(&block, slot) }));
            } else {
                jobs.send((blocks, block, slot)).expect("the workers outlive the run");
            }
            blocks += 1;
        };
        let result = run(&mut |state| {
            pending.push(permuted(*state));
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
        (result, Blocks { extents, lanes, steps })
    })
}

impl Blocks {
    /// Write the committed column of the `steps` steps these blocks hold, padded with
    /// all-zero steps, and hand the reduction its witness.
    pub(crate) fn place(self, steps: usize, q_keccak: &mut [F64]) -> PreparedReductionWitness {
        let shape = shape(steps);
        assert_eq!(self.steps, steps, "the blocks are of another run");
        assert_eq!(
            q_keccak.len(),
            1 << shape.stack_log(),
            "the committed column is the wrong size"
        );
        let n = shape.n();
        let written = self.lanes.len();
        let padding = (written < shape.n_blocks()).then(|| {
            let mut extent = Extent::new(written, 1);
            let slot = extent.slot(written);
            // SAFETY: the extent's one slot, written here alone.
            let lanes = unsafe { run_block(&[], slot) };
            (extent, lanes)
        });
        q_keccak[shape.slots() * n..].fill(F64::ZERO);
        let column = parallel::SendPtr(q_keccak.as_mut_ptr());
        parallel::for_each(shape.n_blocks(), |g| {
            let lanes = self
                .lanes
                .get(g)
                .unwrap_or_else(|| &padding.as_ref().expect("a padding block").1);
            let stream = primitives::stream::Stream::new();
            for slot in 0..shape.slots() {
                // SAFETY: block `g` owns its steps' words of every slot.
                unsafe {
                    stream.copy_uninit(
                        column.add(slot * n + g * BLOCK).cast::<u64>(),
                        &lanes[slot * BLOCK..][..BLOCK],
                    )
                };
            }
        });
        // SAFETY: `while_executing` ran a block into each of the first `written` slots, in
        // order, and the padding block was written just above.
        PreparedReductionWitness(unsafe {
            keccak_gkr::Witness::from_extents(shape, self.extents, written, padding.map(|(extent, _)| extent))
        })
    }
}

/// The reduction's openings as claims on the committed column at `offset`: the inputs'
/// ring-switched, the committed outputs' an ordinary point claim to append to the batch.
pub fn ring_switch_open(n_blocks: usize, offset: usize, openings: Openings) -> (RingSwitchOpen, Option<SlotClaim>) {
    let ring = RingSwitchOpen {
        offset,
        qkeccak_vars: qkeccak_kappa(n_blocks),
        claims: vec![RingSwitchClaim {
            suffix_point: openings.inputs.point,
            s_hat_v: Some(openings.inputs.slices),
        }],
    };
    let outputs = openings.outputs.map(|outputs| SlotClaim::Point {
        offset,
        low_point: outputs.point,
        value: outputs.value,
    });
    (ring, outputs)
}

/// Verifier mirror of [`ring_switch_open`].
pub fn ring_switch_verify(
    n_blocks: usize,
    offset: usize,
    openings: &Openings,
) -> (RingSwitchVerify<'_>, Option<SlotClaim>) {
    let ring = RingSwitchVerify {
        offset,
        qkeccak_vars: qkeccak_kappa(n_blocks),
        claims: vec![::pcs::stack_open::RingSwitchVerifyClaim {
            suffix_point: &openings.inputs.point,
            s_hat_v: openings.inputs.slices.as_slice().try_into().expect("64 slices"),
        }],
    };
    let outputs = openings.outputs.as_ref().map(|outputs| SlotClaim::Point {
        offset,
        low_point: outputs.point.clone(),
        value: outputs.value,
    });
    (ring, outputs)
}

/// The reduction (verifier): replay its layers straight off the shared stream, and recover
/// the openings of the committed column for the PCS to discharge.
pub fn verify_reduction(
    n_blocks: usize,
    vs: &mut VerifierState,
    output: &OutputClaim,
) -> Result<Openings, VerifyError> {
    keccak_gkr::verify(vs, shape(n_blocks), output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::transcript::{Challenger, Receiver, Transmitter};

    fn f(x: u64) -> F64 {
        F64(x)
    }

    /// The committed column on its own, and the reduction's witness.
    fn build_qkeccak(instances: &[[u64; STATE_LANES]]) -> (Vec<F64>, PreparedReductionWitness) {
        let mut q_keccak = vec![F64::ZERO; 1 << qkeccak_kappa(instances.len())];
        let witness = build_qkeccak_prepared(instances, &mut q_keccak);
        (q_keccak, witness)
    }

    /// The true claim on the steps' outputs at `point`.
    fn output_claim(instances: &[[u64; STATE_LANES]], point: Vec<F192>) -> OutputClaim {
        let shape = shape(instances.len());
        let inputs: Vec<[u64; STATE_LANES]> = (0..shape.n())
            .map(|i| permuted(instances.get(i).copied().unwrap_or([0; STATE_LANES])))
            .collect();
        OutputClaim::of_inputs(shape, &inputs, point)
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
            let witness = blocks.place(n, &mut q_keccak);
            assert_eq!(q_keccak, expected, "{n} steps");
            let point = (0..n_blocks_log(n)).map(|i| F192::new(3 + i as u64, 5, 7)).collect();
            let output = output_claim(&instances, point);
            let stream = |witness: &PreparedReductionWitness| {
                let mut ps = ProverState::from_label(b"blocks");
                let openings = witness.prove(&mut ps, &q_keccak, &output);
                (openings, ps.into_proof())
            };
            assert!(stream(&witness) == stream(&reference), "{n} steps");
        }
    }

    /// The relation's label names the constants it stands for.
    #[test]
    fn relation_label_names_the_depth() {
        let label = std::str::from_utf8(RELATION_LABEL).unwrap();
        assert!(label.contains(&format!("depth {DEPTH},")));
    }

    /// The cell layout round-trips, and a zero-state step over 64 message bytes
    /// and the padding is the hash of those bytes.
    #[test]
    fn cells_carry_the_state() {
        let s: [u64; STATE_LANES] = std::array::from_fn(|i| 0x1111 * (i as u64 + 1));
        assert_eq!(state_of_cells(&cells_of_state(&s)), s);
        let msg: Vec<u8> = (0..64u8).collect();
        let mut cells = [F192::ZERO; STATE_CELLS];
        for (c, cell) in cells.iter_mut().enumerate().take(4) {
            let w = |k: usize| u64::from_le_bytes(msg[8 * k..8 * k + 8].try_into().unwrap());
            *cell = F192::new(w(2 * c), w(2 * c + 1), 0);
        }
        cells[4] = F192::new(primitives::hash::PAD_FIRST as u64, 0, 0);
        let out = step_cells(&cells);
        let digest: Vec<u8> = [out[0].c0, out[0].c1, out[1].c0, out[1].c1]
            .iter()
            .flat_map(|w| w.to_le_bytes())
            .collect();
        assert_eq!(digest, primitives::hash::hash(&msg));
    }

    /// The committed column holds every step's input lanes, a word per step: what the VM reads,
    /// with the padding's last bit in lane 16. The output lanes have no slot.
    #[test]
    fn qkeccak_words_match_layout() {
        let instances = sample_instances(5);
        let (q_keccak, _) = build_qkeccak(&instances);
        let n = 1usize << n_blocks_log(instances.len());
        for (j, input) in instances.iter().enumerate() {
            for i in 0..STATE_LANES {
                let (slot, shift) = value_slot(i).expect("an input lane");
                assert_eq!(F192::from(q_keccak[slot * n + j]), F192::from(f(input[i])) + shift);
                assert_eq!(value_slot(STATE_LANES + i), None);
            }
        }
    }

    /// The reduction's openings, discharged by ONE stacked WHIR over a hand-stacked witness
    /// holding the committed column (plus a dummy column) together with an ordinary point
    /// claim. A mismatched domain and a tampered point value are rejected.
    #[test]
    fn validity_stacked_roundtrip() {
        let instances = sample_instances(4);
        let (q_keccak, witness) = build_qkeccak(&instances);
        let dummy: Vec<F64> = (0..8u64).map(|i| f(0x9000 + i)).collect();
        let stacked = crate::witness::stack(&[q_keccak.clone(), dummy.clone()]);
        let offset = stacked.placements[0].offset;

        let dummy_pl = stacked.placements[1];
        let low_point: Vec<F192> = (0..dummy_pl.n_vars)
            .map(|i| F192::new(0x100 + i as u64, 0x7, 0x55))
            .collect();
        let pd_value = primitives::multilinear::mle_eval(&dummy, &low_point);
        let points = vec![crate::pcs::SlotClaim::Point {
            offset: dummy_pl.offset,
            low_point: low_point.clone(),
            value: pd_value,
        }];

        let mut ps = ProverState::from_label(b"vstack");
        let committed = crate::pcs::commit(&mut ps, &stacked.q, stacked.shape, crate::pcs::TEST_LOG_INV_RATE);
        let output = output_claim(&instances, ps.sample_vec(n_blocks_log(instances.len())));
        ps.add_scalars(&output.lanes);
        let (ring, outputs) = ring_switch_open(instances.len(), offset, witness.prove(&mut ps, &q_keccak, &output));
        let all = [&points[..], &Vec::from_iter(outputs)].concat();
        crate::pcs::open(&mut ps, &committed, &stacked.q, &all, &ring);
        let bundle = ps.into_proof();

        let run = |label: &'static [u8], points: &[crate::pcs::SlotClaim]| -> Result<(), &'static str> {
            let mut vs = VerifierState::from_label(label, &bundle);
            let root = crate::pcs::read_commitment(&mut vs).map_err(|_| "root")?;
            let output = OutputClaim {
                instance: vs.sample_vec(n_blocks_log(instances.len())),
                lanes: vs
                    .next_scalars(STATE_LANES)
                    .map_err(|_| "lanes")?
                    .try_into()
                    .expect("25 lanes"),
            };
            let openings = verify_reduction(instances.len(), &mut vs, &output).map_err(|_| "reduction")?;
            let (ring, outputs) = ring_switch_verify(instances.len(), offset, &openings);
            let points = &[points, &Vec::from_iter(outputs)].concat();
            crate::pcs::verify(
                &mut vs,
                points,
                &ring,
                stacked.shape,
                crate::pcs::TEST_LOG_INV_RATE,
                &root,
            )
            .map_err(|_| "opening")?;
            vs.finish().map_err(|_| "leftover")
        };

        run(b"vstack", &points).expect("validity verifies");
        assert!(
            run(b"different-domain", &points).is_err(),
            "validity under a mismatched transcript must fail"
        );
        let mut bad_points = points.clone();
        if let crate::pcs::SlotClaim::Point { value, .. } = &mut bad_points[0] {
            *value += F192::ONE;
        }
        assert!(run(b"vstack", &bad_points).is_err(), "tampered point value must fail");
    }
}
