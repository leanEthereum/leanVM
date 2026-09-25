//! Bridge to the flock Keccak prover ([`flock::keccak`]) for the `SHA3` opcode, single-PCS.
//!
//! `q_flock` (flock's packed witness, 64 bits per `F64` word) is committed as a
//! column in leanVM's ONE stacked `F64` witness (§sec:stacking), with no separate
//! flock commitment. The VM's `SHA3` table binds to it by point-eval equality (its
//! value columns and `q_flock`'s slots are point-evals of the same committed
//! stack), and flock's R1CS validity is discharged by the same stacked WHIR: the
//! reduction's tower-field claim passes through [`ring_switch_open`] /
//! [`ring_switch_verify`] and joins the batch-mixed opening ([`::pcs::stack_open`]).
//!
//! ## The mapping
//!
//! The VM's `SHA3(m, cap) -> out` is one [`primitives::keccak::step`] on the
//! 25 lanes those thirteen cells hold, written to thirteen cells in the same
//! order ([`CELL_LANES`]). Every lane is one whole packed word of the instance:
//! input lane `i` is slot `i`, output lane `i` slot `25 + i`, so the memory
//! interaction binds every input and output of the relation, bar the output a
//! `digest` step leaves unwritten, which no cell holds and nothing reads.

use crate::transcript::{ProverState, VerifierState};
use ::pcs::pack::LOG_PACKING;
use flock::keccak::{IN_WORD, Instance, K_LOG, KeccakSetup, OUT_WORD, ReductionReplay};
use flock::verifier::VerifyError;
use primitives::field::{F64, F192};
use primitives::keccak::STATE_LANES;
use primitives::stream::Stream;
use zk_alloc::ArenaVec;

pub use flock::keccak::{
    SliceClaim, min_n_blocks_log as n_blocks_log, qflock_kappa, ring_switch_open, ring_switch_verify,
};

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

/// The fifty within-instance value slots in canonical order: the input lanes
/// `0..25`, then the output lanes, matching `tables::SHA3_VALUE_COLS`.
pub const SLOTS: [usize; 2 * STATE_LANES] = {
    let mut s = [0usize; 2 * STATE_LANES];
    let mut i = 0;
    while i < STATE_LANES {
        s[i] = IN_WORD + i;
        s[STATE_LANES + i] = OUT_WORD + i;
        i += 1;
    }
    s
};

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
    cells_of_state(&primitives::keccak::step(&state_of_cells(cells)))
}

/// Flock-native reduction buffers emitted in the same fused pass as the
/// committed, flattened `q_flock`. They stay alive across commit, bus, and
/// constraint proving so reduction needs no second witness pass.
pub(crate) struct PreparedReductionWitness {
    n_blocks: usize,
    z_packed: ArenaVec<u64>,
    a_packed: ArenaVec<u64>,
    b_packed: ArenaVec<u64>,
    z_lincheck: ArenaVec<u8>,
}

impl PreparedReductionWitness {
    pub(crate) fn n_blocks(&self) -> usize {
        self.n_blocks
    }

    pub(crate) fn prove(&self, ps: &mut ProverState) -> SliceClaim {
        KeccakSetup::new(self.n_blocks).prove_reduction_precomputed(
            &self.z_packed,
            &self.a_packed,
            &self.b_packed,
            &self.z_lincheck,
            ps,
        )
    }
}

/// Lift flock's packed witness (64 bits per word, bit `i` at position `i`) into
/// the committed `F64` column: word for word, which is exactly `pack_witness`'s
/// convention on the same bit string.
fn flatten_packed_into(packed: &[u64], out: &mut [F64]) {
    assert_eq!(out.len(), packed.len(), "q_flock's window is the wrong size");
    // Write directly into the committed window and publish it with streaming stores.
    // SAFETY: `F64` is `repr(transparent)` over `u64`, so the two slices are the
    // same bytes.
    let words: &mut [u64] = unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr().cast(), out.len()) };
    parallel::chunks_mut_zip(words, packed, 1 << 14, |_, dst, src| Stream::new().copy(dst, src));
}

/// Build the committed `q_flock` column (flock's packed witness) for `instances`,
/// padded to `2^n_blocks_log(max(instances.len(),1))` instances (the unused ones
/// flock's own padding instance), and retain the Flock-native layouts produced by
/// that same fused pass so reduction does not regenerate them later. An empty
/// `instances` yields one padding cube.
pub(crate) fn build_qflock_prepared(instances: &[Instance], q_flock: &mut [F64]) -> PreparedReductionWitness {
    let n_blocks = instances.len().max(1);
    let (z_packed, a_packed, b_packed, z_lincheck) =
        flock::keccak::generate_witness_with_ab_packed_and_lincheck(instances, n_blocks_log(n_blocks));
    flatten_packed_into(&z_packed, q_flock);
    PreparedReductionWitness {
        n_blocks,
        z_packed,
        a_packed,
        b_packed,
        z_lincheck,
    }
}

/// `log2` of the within-instance packed span (`2^10` words): the number of low
/// coords of a `q_flock` point that carry the slot's bits, and the stride between
/// consecutive instances' same-slot words in `q_flock`. A value claim on `q_flock`
/// is thus a boolean-selector (strided) claim with this stride.
pub const SLOT_STRIDE_LOG: usize = K_LOG - LOG_PACKING;

/// **Flock reduction only** (prover): run flock's zerocheck + lincheck over
/// `instances` and return the one [`SliceClaim`] on the committed witness
/// `q_flock`, along with the regenerated packed witness. Does NOT open the PCS.
#[cfg(test)]
fn prove_reduction(instances: &[Instance], ps: &mut ProverState) -> (Vec<F64>, SliceClaim) {
    let (z_packed, reduced) = KeccakSetup::new(instances.len()).prove_reduction(instances, ps);
    let mut q_flock = vec![F64::ZERO; z_packed.len()];
    flatten_packed_into(&z_packed, &mut q_flock);
    (q_flock, reduced)
}

/// `q_flock` on its own, for the tests that only need the committed column.
#[cfg(test)]
fn build_qflock(instances: &[Instance]) -> Vec<F64> {
    let mut q_flock = vec![F64::ZERO; 1 << qflock_kappa(instances.len())];
    build_qflock_prepared(instances, &mut q_flock);
    q_flock
}

/// **Flock reduction only** (verifier): mirror of `prove_reduction`. Replay the
/// zerocheck + lincheck sub-proofs straight off the shared stream, and recover the
/// one claim on `q_flock` for the PCS to discharge.
pub fn verify_reduction(n_blocks: usize, vs: &mut VerifierState) -> Result<ReductionReplay, VerifyError> {
    KeccakSetup::new(n_blocks).verify_reduction(vs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(x: u64) -> F64 {
        F64(x)
    }

    fn sample_instances(n: usize) -> Vec<Instance> {
        (0..n as u64)
            .map(|i| std::array::from_fn(|l| 0x0101_0101_0101_0101u64.wrapping_mul(i + 1) ^ l as u64))
            .collect()
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
        cells[4] = F192::new(primitives::keccak::PAD_FIRST as u64, 0, 0);
        let out = step_cells(&cells);
        let digest: Vec<u8> = [out[0].c0, out[0].c1, out[1].c0, out[1].c1]
            .iter()
            .flat_map(|w| w.to_le_bytes())
            .collect();
        assert_eq!(digest, primitives::keccak::hash(&msg));
    }

    /// `q_flock`'s packed slots hold the input and output lanes.
    #[test]
    fn qflock_words_match_layout() {
        let instances = sample_instances(5);
        let q_flock = build_qflock(&instances);
        assert_eq!(q_flock.len(), 1 << qflock_kappa(instances.len()));
        let slot = |j: usize, s: usize| q_flock[j * (1 << SLOT_STRIDE_LOG) + s];
        for (j, input) in instances.iter().enumerate() {
            let out = primitives::keccak::step(input);
            for i in 0..STATE_LANES {
                assert_eq!(slot(j, SLOTS[i]), f(input[i]));
                assert_eq!(slot(j, SLOTS[STATE_LANES + i]), f(out[i]));
            }
        }
    }

    /// The Flock reduction (zerocheck + lincheck) is a clean, self-contained
    /// unit: run WITHOUT any PCS open, the prover's claim on the committed witness
    /// `q_flock` is exactly what the verifier recovers by replaying the sub-proofs.
    #[test]
    fn reduction_roundtrip() {
        let instances = sample_instances(4);
        let q_flock = build_qflock(&instances);
        let dummy = vec![f(7); 8];
        let stacked = crate::witness::stack(&[q_flock.clone(), dummy]);
        let offset = stacked.placements[0].offset;

        let mut ps = ProverState::from_label(b"reduce");
        let _committed = crate::pcs::commit(&mut ps, &stacked.q, stacked.shape, crate::pcs::TEST_LOG_INV_RATE);
        let (z_packed, reduced) = prove_reduction(&instances, &mut ps);
        let bundle = ps.into_proof();

        assert_eq!(z_packed, q_flock, "reduction witness must equal committed q_flock");
        assert_eq!(&stacked.q[offset..offset + z_packed.len()], z_packed.as_slice());

        let mut vs = VerifierState::from_label(b"reduce", &bundle);
        let _root = crate::pcs::read_commitment(&mut vs).unwrap();
        let replay = verify_reduction(instances.len(), &mut vs).expect("reduction verifies");
        assert_eq!(reduced, replay.claim, "reduction claim mismatch");

        let mut vs_bad = VerifierState::from_label(b"different", &bundle);
        let _root_b = crate::pcs::read_commitment(&mut vs_bad).unwrap();
        if let Ok(replay_b) = verify_reduction(instances.len(), &mut vs_bad) {
            assert!(
                replay_b.claim != replay.claim,
                "a diverged transcript must not reproduce the prover's claim"
            );
        }
    }

    /// flock's validity claims, discharged by ONE stacked WHIR over a hand-stacked
    /// witness containing `q_flock` (plus a dummy column) together with an ordinary
    /// point claim. A mismatched domain and a tampered point value are rejected.
    #[test]
    fn validity_stacked_roundtrip() {
        let instances = sample_instances(4);
        let q_flock = build_qflock(&instances);
        let dummy: Vec<F64> = (0..8u64).map(|i| f(0x9000 + i)).collect();
        let stacked = crate::witness::stack(&[q_flock.clone(), dummy.clone()]);
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
        let (_z, reduced) = prove_reduction(&instances, &mut ps);
        let ring = ring_switch_open(instances.len(), offset, &reduced);
        crate::pcs::open(&mut ps, &committed, &stacked.q, &points, std::slice::from_ref(&ring));
        let bundle = ps.into_proof();

        let run = |label: &'static [u8], points: &[crate::pcs::SlotClaim]| -> Result<(), &'static str> {
            let mut vs = VerifierState::from_label(label, &bundle);
            let root = crate::pcs::read_commitment(&mut vs).map_err(|_| "root")?;
            let replay = verify_reduction(instances.len(), &mut vs).map_err(|_| "reduction")?;
            let ring = ring_switch_verify(instances.len(), offset, &replay.claim);
            crate::pcs::verify(
                &mut vs,
                points,
                std::slice::from_ref(&ring),
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
