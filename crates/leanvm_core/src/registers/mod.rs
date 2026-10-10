//! The register file by Twist (§sec:regchan).
//!
//! The registers are a log of the run's cycles, one row each: two reads and a write.
//!
//! ```text
//!     Val(k, j) = sum_{j' < j} wa(k, j') inc(j')
//!     read      = Val(cell, j)
//!     write     = Val(cell, j) + inc(j)
//! ```
//!
//! - A live row pushes its cycle onto the bus at time `g^j`, which the tables' rows pull.
//! - The read-write sumcheck reduces the bus's share of the log to its committed columns.
//! - The evaluation sumcheck proves `Val`, the outputs, and that every cell word is one-hot.
//!
//! What varies with the run is the verifier's input, not the shape: the live rows' count, as bits, and the outputs.

mod prove;
mod rounds;
mod verify;

pub(crate) use prove::{LogWitness, leaves, prove};
pub(crate) use verify::{live_bits, verify};

use crate::pcs::SliceClaim;
use fiat_shamir::arith::Arith;
use fiat_shamir::transcript::TranscriptError;
use primitives::field::{F64, F192};
use thiserror::Error;

/// Bits of a register cell.
pub(crate) const CELL_BITS: usize = 6;

/// Register cells: a one-hot word has a bit per cell.
pub(crate) const CELLS: usize = 1 << CELL_BITS;

/// The cells a row names: two reads, then the write.
pub(crate) const GROUPS: usize = 3;

/// The group the row's increment is written at.
pub(crate) const WRITE: usize = 2;

/// A slot of the log's bus tuple.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Slot {
    /// `base`, plus `delta` on a flagged row.
    Flagged { base: F64, delta: F64 },
    /// The row's time `g^j`.
    Time,
    /// The number of the group's cell.
    Address(usize),
    /// The group's cell before the row writes.
    Read(usize),
    /// The written cell after the row writes.
    Written,
}

/// The log's public structure, which both sides derive from the announced height.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LogShape {
    /// The base-two logarithm of its rows.
    pub(crate) log_rows: usize,
    /// The bus tuple a live row pushes.
    pub(crate) slots: Vec<Slot>,
    /// The cells whose final values the statement claims.
    pub(crate) outputs: Vec<usize>,
}

impl LogShape {
    /// The read-write sumcheck's coefficients per cycle round: `u sum_g E_g inner_g`.
    pub(crate) const READ_WRITE_COEFFS: usize = 4;

    /// The evaluation sumcheck's coefficients: `eq x^3` for the collisions.
    pub(crate) const EVALUATION_COEFFS: usize = 5;
}

/// The slot weights of the log's tuple, gathered by role.
pub(crate) struct Link<E> {
    /// Each group's weight on its cell's value.
    pub(crate) value: [E; GROUPS],
    /// Each group's weight on its cell's number.
    pub(crate) address: [E; GROUPS],
    /// The weight on the increment, at the write group.
    pub(crate) inc: E,
    /// The weight on the flag.
    pub(crate) flag: E,
    /// The weight on the constant slots.
    pub(crate) constant: E,
    /// The weight on the time.
    pub(crate) time: E,
}

impl<E: Copy> Link<E> {
    /// Gather the fingerprint's slot weights.
    pub(crate) fn new<A: Arith<E = E>>(a: &mut A, shape: &LogShape, weights: &[E]) -> Self {
        let zero = a.zero();
        let mut link = Self {
            value: [zero; GROUPS],
            address: [zero; GROUPS],
            inc: zero,
            flag: zero,
            constant: zero,
            time: zero,
        };
        for (slot, &w) in shape.slots.iter().zip(weights) {
            match *slot {
                Slot::Flagged { base, delta } => {
                    link.constant = a.mul_const_add(w, F192::from(base), link.constant);
                    link.flag = a.mul_const_add(w, F192::from(delta), link.flag);
                }
                Slot::Time => link.time = a.add(link.time, w),
                Slot::Address(g) => link.address[g] = a.add(link.address[g], w),
                Slot::Read(g) => link.value[g] = a.add(link.value[g], w),
                Slot::Written => {
                    link.value[WRITE] = a.add(link.value[WRITE], w);
                    link.inc = a.add(link.inc, w);
                }
            }
        }
        link
    }
}

/// What the verifier knows of a run's log beyond its shape.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Statement<'a, E> {
    /// The live rows' count, by its bits, lowest first: one per row bit, and one past.
    pub(crate) live: &'a [E],
    /// The final values of the shape's output cells.
    pub(crate) outputs: &'a [E],
}

/// What the bus leaves the log: its block's leaves at the bus point.
#[derive(Clone, Debug)]
pub(crate) struct LinkShare<E> {
    /// The bus point over the log's rows.
    pub(crate) point: Vec<E>,
    /// The leaves' multilinear extension there.
    pub(crate) value: E,
    /// The fingerprint's slot weights.
    pub(crate) weights: Vec<E>,
    /// The fingerprint's shift.
    pub(crate) beta: E,
}

/// What the log leaves the opening, at the read-write point then the evaluation point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LogOpening<E> {
    /// Each group's cell word: its slices at the two points.
    pub(crate) cells: [[SliceClaim<E>; 2]; GROUPS],
    /// The increments at the two points.
    pub(crate) inc: [(Vec<E>, E); 2],
    /// The packed flags' slices at the two points.
    pub(crate) flag: [SliceClaim<E>; 2],
}

/// Why the log's argument refuses.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum RegisterError {
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// The read-write sumcheck does not end at the opened values.
    #[error("the read-write sumcheck does not close")]
    ReadWrite,
    /// The evaluation sumcheck does not end at the opened values.
    #[error("the evaluation sumcheck does not close")]
    Evaluation,
    /// A cell word has a row of even weight.
    #[error("a cell word has a row of even weight")]
    Parity,
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::transcript::{ProverState, VerifierState};
    use primitives::multilinear::{eq_table, inner_product, mle_eval};
    use primitives::test_util::Rng;

    /// The registers' tuple: a flagged separator, the three register numbers around the time, the values.
    fn slots() -> Vec<Slot> {
        vec![
            Slot::Flagged {
                base: F64(8),
                delta: F64(24),
            },
            Slot::Address(0),
            Slot::Time,
            Slot::Address(1),
            Slot::Address(2),
            Slot::Read(0),
            Slot::Read(1),
            Slot::Written,
        ]
    }

    /// A random register file's log: reads of 33 cells, writes of 32, some rows flagged.
    fn registers(rng: &mut Rng, log_rows: usize, live: usize) -> (LogShape, LogWitness) {
        let mut regs = [0u64; CELLS];
        let mut w = LogWitness {
            live,
            ..LogWitness::default()
        };
        for j in 0..1 << log_rows {
            let is_live = j < live;
            let (rd, flag) = if is_live {
                (1 + rng.below(32), rng.below(7) == 0)
            } else {
                (0, false)
            };
            let new = if is_live && !flag { rng.next_u64() } else { regs[rd] };
            w.cells[0].push(rng.below(33) as u8);
            w.cells[1].push(rng.below(33) as u8);
            w.cells[WRITE].push(rd as u8);
            w.inc.push(F64(std::mem::replace(&mut regs[rd], new) ^ new));
            w.flag.push(flag);
        }
        let shape = LogShape {
            log_rows,
            slots: slots(),
            outputs: vec![10, 17],
        };
        (shape, w)
    }

    /// The output cells' values after the log's live rows.
    fn final_values(shape: &LogShape, w: &LogWitness) -> Vec<F192> {
        let mut regs = [0u64; CELLS];
        for j in 0..w.live {
            regs[w.cells[WRITE][j] as usize] ^= w.inc[j].0;
        }
        shape.outputs.iter().map(|&cell| F192::from(F64(regs[cell]))).collect()
    }

    /// Prove and verify a log against a bus share and claimed outputs, then settle what it leaves against the witness.
    ///
    /// `forge` alters the leaves the share is of, as a table pulling a tuple the log never pushed would.
    fn run(
        shape: &LogShape,
        w: &LogWitness,
        outputs: &[F192],
        forge: impl FnOnce(&mut [F192], &[F192]),
    ) -> Result<(), RegisterError> {
        let mut rng = Rng::new(shape.log_rows as u64);
        let (weights, beta, point) = (rng.ext_vec(16), rng.ext(), rng.ext_vec(shape.log_rows));
        let mut leaves = leaves(shape, w, &weights, beta);
        forge(&mut leaves, &weights);
        let value = inner_product(&eq_table(&point), &leaves);
        let share = LinkShare {
            point,
            value,
            weights,
            beta,
        };

        let mut ps = ProverState::from_label(b"registers");
        let proven = prove(&mut ps, shape, w, &share);
        let proof = ps.into_proof();
        let mut vs = VerifierState::from_label(b"registers", &proof);
        let live = live_bits(w.live, shape.log_rows);
        let statement = Statement { live: &live, outputs };
        let opening = verify(&mut vs, shape, statement, &share)?;
        vs.finish()?;
        assert_eq!(proven, opening);

        // The opening's claims, which a proof's commitment settles.
        for (g, claims) in opening.cells.iter().enumerate() {
            let mut words = vec![F64::ZERO; w.inc.len()];
            w.cell_words(g, &mut words);
            for claim in claims {
                for (k, &slice) in claim.s_hat_v.iter().enumerate() {
                    let bit: Vec<F64> = words.iter().map(|x| F64(x.0 >> k & 1)).collect();
                    assert_eq!(slice, mle_eval(&bit, &claim.suffix_point));
                }
            }
        }
        for (point, value) in &opening.inc {
            assert_eq!(mle_eval(&w.inc, point), *value);
        }
        Ok(())
    }

    #[test]
    fn an_honest_log_verifies() {
        let mut rng = Rng::new(1);
        for (log_rows, live) in [(7, 128), (13, 5000), (14, 1 << 14)] {
            let (shape, w) = registers(&mut rng, log_rows, live);
            run(&shape, &w, &final_values(&shape, &w), |_, _| {}).expect("an honest log verifies");
        }
    }

    #[test]
    fn a_stale_read_is_refused() {
        // The table's tuple says row 100's first read returned one more than its cell held.
        //
        //     leaf = beta + sum_i w_i slot_i,   slot 5 = the first read
        let mut rng = Rng::new(3);
        let (shape, w) = registers(&mut rng, 10, 1000);
        let forge = |leaves: &mut [F192], weights: &[F192]| leaves[100] += weights[5];
        assert_eq!(
            run(&shape, &w, &final_values(&shape, &w), forge),
            Err(RegisterError::ReadWrite)
        );
    }

    #[test]
    fn a_write_under_the_flag_is_refused() {
        let mut rng = Rng::new(5);
        let (shape, mut w) = registers(&mut rng, 9, 500);
        let j = w.flag.iter().position(|&f| f).expect("a flagged row");
        w.inc[j] = F64(1);
        assert_eq!(
            run(&shape, &w, &final_values(&shape, &w), |_, _| {}),
            Err(RegisterError::Evaluation)
        );
    }

    #[test]
    fn a_wrong_output_is_refused() {
        // The statement claims each output register one more than the log leaves in it.
        let mut rng = Rng::new(7);
        let (shape, w) = registers(&mut rng, 9, 500);
        let honest = final_values(&shape, &w);
        for i in 0..honest.len() {
            let mut outputs = honest.clone();
            outputs[i] += F192::ONE;
            assert_eq!(
                run(&shape, &w, &outputs, |_, _| {}),
                Err(RegisterError::Evaluation),
                "output {i}"
            );
        }
    }
}
