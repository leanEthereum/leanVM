//! Circuits of independent parts, one per signature of a batch: built once, then replayed for their values alone.
//!
//! A part's wires are numbered as its build numbered them when it makes the same calls and folds the same constants
//! and rows. Folding depends on wire numbers, never on values, so the build records each fold's outcome and a replay
//! reads it back, with no rows, no wire classes and no maps. A part reads its own wires and, of earlier parts', only
//! the constants and the rows over them that folding hands it, whose values are the circuit's own, the same in every
//! run. So the parts replay at once, each into its own stretch of the values, and each checks its own step and link
//! rows: if every part's dynamic tuples balance, so do the circuit's.

use super::chain::{BALANCE, Dynamic};
use super::{Builder, RowHasher, Units};
use crate::rec::circuit::{Assignment, Finished, Limbs, TableSlots, Unsatisfied};
use crate::rec::table::Table;
use parallel::SendPtr;
use std::collections::HashMap;
use std::hash::BuildHasherDefault;
use std::sync::Arc;

/// A fold's outcome when the constant or row is new.
const NEW: u32 = u32::MAX;

/// What a build of parts records, or what a replay of one reads back.
#[derive(Debug, Default)]
pub(super) enum Parts {
    /// A builder of one whole circuit.
    #[default]
    Whole,
    /// A build of parts under way.
    Recording(Box<Recording>),
    /// A part replayed for its values.
    Replaying(Box<Replaying>),
}

/// The folds of a build of parts, which its wire numbers depend on.
#[derive(Debug, Default)]
struct Folds {
    /// Per constant and per arithmetic row made, in call order: the earlier wire it folds into, or `NEW`.
    tape: Vec<u32>,
    /// The wires a part may read of earlier parts, with their values: constants and the rows over them.
    shared: HashMap<u32, Limbs, BuildHasherDefault<RowHasher>>,
}

/// Where a part starts: its first wire, fold, hash row, statement word and row of each dynamic table, and the units
/// made before it.
#[derive(Clone, Copy, Debug)]
struct Start {
    wire: u32,
    fold: usize,
    hash: usize,
    statement: usize,
    dynamic: [usize; 2],
    units: Units,
}

/// A build of parts under way: where each part so far starts, and the folds.
#[derive(Debug, Default)]
pub(super) struct Recording {
    starts: Vec<Start>,
    folds: Folds,
}

/// A part replayed: the build's folds, the part's next and end on the tape, and its first statement word.
#[derive(Debug)]
pub(super) struct Replaying {
    folds: Arc<Folds>,
    next: usize,
    end: usize,
    statement: usize,
}

/// What a prover reuses of a circuit of parts built once: each slot's wire, where each part starts, and the folds.
#[derive(Debug)]
pub struct Replay {
    /// Each slot's own wire.
    wires: Arc<TableSlots>,
    /// Each part's start, then the end of the last.
    starts: Vec<Start>,
    /// The build's folds.
    folds: Arc<Folds>,
}

impl Parts {
    /// Whether this is a part replayed for its values, which makes no rows.
    pub(super) const fn replaying(&self) -> bool {
        matches!(self, Self::Replaying(_))
    }

    /// The value of a wire of an earlier part than the replayed one.
    pub(super) fn shared(&self, w: u32) -> Limbs {
        let Self::Replaying(r) = self else {
            unreachable!("only a replayed part's wires start past zero")
        };
        *(r.folds.shared.get(&w)).expect("a part reads of earlier parts only the constants and rows its folds hand it")
    }

    /// A new constant: every later part may read it.
    pub(super) fn share(&mut self, w: u32, value: Limbs) {
        if let Self::Recording(r) = self {
            r.folds.shared.insert(w, value);
        }
    }

    /// The number of the statement word the part exposes first.
    pub(super) fn first_statement_word(&self) -> usize {
        match self {
            Self::Replaying(r) => r.statement,
            _ => 0,
        }
    }
}

impl Builder {
    /// A circuit of `n` parts, part `i` made by `part(b, i)`, and what replays them on other values.
    ///
    /// A part may read the wires of earlier parts only through the constants and rows it folds into, which the build
    /// checks for rows.
    pub fn parts(n: usize, part: impl Fn(&mut Self, usize)) -> (Finished, Replay) {
        let mut b = Self::new();
        b.parts = Parts::Recording(Box::default());
        for i in 0..n {
            b.start_part();
            part(&mut b, i);
        }
        b.start_part();
        let Parts::Recording(r) = std::mem::take(&mut b.parts) else {
            unreachable!("a build of parts records")
        };
        let finished = b.finish();
        let replay = Replay {
            wires: Arc::clone(&finished.assignment.wires),
            starts: r.starts,
            folds: Arc::new(r.folds),
        };
        (finished, replay)
    }

    /// Record where the next part starts.
    fn start_part(&mut self) {
        let wire = u32::try_from(self.values.len()).expect("fewer than 2^32 wires");
        let (hash, statement, units) = (self.hash.len(), self.statement.len(), self.units);
        let dynamic = Table::DYNAMIC.map(|t| self.rows.len(t));
        if let Parts::Recording(r) = &mut self.parts {
            let fold = r.folds.tape.len();
            r.starts.push(Start {
                wire,
                fold,
                hash,
                statement,
                dynamic,
                units,
            });
        }
    }

    /// The earlier wire a constant or an arithmetic row over `inputs` folds into, if any: `find`'s in a build, its
    /// build's read back in a replay.
    ///
    /// Recording, a row of an earlier part folded into is shared, its inputs being shared.
    pub(super) fn earlier(&mut self, inputs: &[u32], find: impl FnOnce(&Self) -> Option<u32>) -> Option<u32> {
        if let Parts::Replaying(r) = &mut self.parts {
            assert!(r.next < r.end, "a replayed part folds as its build did");
            let w = r.folds.tape[r.next];
            r.next += 1;
            return (w != NEW).then_some(w);
        }
        let found = find(self);
        if let Parts::Recording(r) = &mut self.parts {
            r.folds.tape.push(found.unwrap_or(NEW));
            let first = r.starts.last().map_or(0, |s| s.wire);
            if let Some(w) = found
                && w < first
            {
                assert!(
                    inputs.iter().all(|i| r.folds.shared.contains_key(i)),
                    "a part folds into an earlier part's row over shared wires only"
                );
                r.folds.shared.insert(w, self.values[w as usize]);
            }
        }
        found
    }
}

/// What a part's replay gives besides its values: the checks it failed, its step and link rows' checks, and whether
/// its dynamic tuples balance.
struct Checked {
    failures: Vec<Unsatisfied>,
    dynamic: [Vec<&'static str>; 2],
    balanced: bool,
}

impl Replay {
    /// The values of the parts `part` makes, the calls `Builder::parts` was given made on other values, and the checks
    /// that failed on them: what the build's `finish` would give, the parts made in parallel.
    ///
    /// # Panics
    ///
    /// Panics if a part makes other calls than its build.
    pub fn values(&self, part: impl Fn(&mut Builder, usize) + Sync) -> (Assignment, Vec<Unsatisfied>) {
        let n = self.starts.len() - 1;
        let end = self.starts[n];
        let mut values = Vec::with_capacity(end.wire as usize);
        let mut hash = Vec::with_capacity(end.hash);
        let mut statement = Vec::with_capacity(end.statement);
        let out = (
            SendPtr(values.as_mut_ptr()),
            SendPtr(hash.as_mut_ptr()),
            SendPtr(statement.as_mut_ptr()),
        );
        let parts = parallel::map_collect(n, |i| {
            let (start, next) = (self.starts[i], self.starts[i + 1]);
            let n_wires = (next.wire - start.wire) as usize;
            let mut b = Builder {
                values: Vec::with_capacity(n_wires),
                first: start.wire,
                units: start.units,
                hash: Vec::with_capacity(next.hash - start.hash),
                statement: Vec::with_capacity(next.statement - start.statement),
                parts: Parts::Replaying(Box::new(Replaying {
                    folds: Arc::clone(&self.folds),
                    next: start.fold,
                    end: next.fold,
                    statement: start.statement,
                })),
                ..Builder::default()
            };
            part(&mut b, i);
            let made = (b.values.len(), b.hash.len(), b.statement.len());
            assert!(
                matches!(&b.parts, Parts::Replaying(r) if r.next == next.fold)
                    && made == (n_wires, next.hash - start.hash, next.statement - start.statement),
                "a replayed part makes its build's calls"
            );
            let rows = std::array::from_fn(|k| {
                let (table, from, to) = (Table::DYNAMIC[k], start.dynamic[k], next.dynamic[k]);
                &self.wires.of(table)[from * table.n_slots()..to * table.n_slots()]
            });
            let mut dynamic = Dynamic::of(rows, |w| b.value(w));
            let balanced = dynamic.balance();
            // SAFETY: the parts' stretches tile each output's capacity, and part `i` writes its own only.
            unsafe {
                put(out.0, start.wire as usize, &b.values);
                put(out.1, start.hash, &b.hash);
                put(out.2, start.statement, &b.statement);
            }
            Checked {
                failures: b.failures,
                dynamic: dynamic.failures,
                balanced,
            }
        });
        // SAFETY: the parts' stretches tile `0..end`, and each part wrote all of its own.
        unsafe {
            values.set_len(end.wire as usize);
            hash.set_len(end.hash);
            statement.set_len(end.statement);
        }
        // The build's order: the parts' checks, then each dynamic table's rows', then the balance. Parts that balance
        // make a circuit that balances, and otherwise the circuit's tuples are counted together.
        let unbalanced = !parts.iter().all(|p| p.balanced) && {
            let rows = Table::DYNAMIC.map(|t| self.wires.of(t));
            !Dynamic::of(rows, |w| values[w as usize]).balance()
        };
        let dynamic = (0..2).flat_map(|k| parts.iter().flat_map(move |p| p.dynamic[k].iter().copied()));
        let failures = (parts.iter().flat_map(|p| p.failures.iter().cloned()))
            .chain(dynamic.chain(unbalanced.then_some(BALANCE)).map(|check| Unsatisfied {
                scope: Vec::new(),
                check,
            }))
            .take(Builder::RECORDED_FAILURES)
            .collect();
        let assignment = Assignment {
            wires: Arc::clone(&self.wires),
            values,
            hash,
            statement,
        };
        (assignment, failures)
    }
}

/// Copy `items` to `dst` from `at` on.
///
/// # Safety
///
/// `at..at + items.len()` lies in `dst`'s allocation, and no other task touches it.
const unsafe fn put<T: Copy>(dst: SendPtr<T>, at: usize, items: &[T]) {
    // SAFETY: the caller's.
    unsafe { std::ptr::copy_nonoverlapping(items.as_ptr(), dst.add(at), items.len()) };
}

#[cfg(test)]
impl Replay {
    /// Replay the parts `part` makes and assert the replay gives `built`'s values and failures, `built` being the
    /// build of the same calls; the failures.
    pub(crate) fn assert_replays(
        &self,
        part: impl Fn(&mut Builder, usize) + Sync,
        built: &Finished,
    ) -> Vec<Unsatisfied> {
        let (a, failures) = self.values(part);
        let b = &built.assignment;
        assert_eq!(a.wires, b.wires);
        assert!(a.values == b.values, "the values");
        assert_eq!(a.hash, b.hash);
        assert_eq!(a.statement, b.statement);
        assert_eq!(failures, built.failures);
        failures
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::circuit::chains::{Planned, step, tweak};
    use crate::rec::circuit::{Ew, PARAM_IV};
    use fiat_shamir::arith::Arith;
    use primitives::field::F192;

    /// A part's values: `x`, its claimed square, and its chains.
    type Input = (F192, F192, Vec<Planned>);

    /// Part `i`: the square of `x` held to the claim, times a row over constants that later parts fold into, exposed
    /// and compressed; then its chains.
    fn part(inputs: &[Input]) -> impl Fn(&mut Builder, usize) + Sync + '_ {
        move |b, i| {
            b.scope(format!("part {i}"), |b| {
                let (x, claim, chains) = &inputs[i];
                let x = b.free_e(*x);
                let square = b.square(x);
                let claim = b.free_e(*claim);
                b.eq(square, claim);
                let (one, seven, zero) = (b.one(), b.k_const(7), b.zero());
                let seven_e = b.mul_k_add(one, seven, zero);
                let w = b.mul(square, seven_e);
                b.expose(w);
                let ds = b.free_k(i as u64);
                let iv = b.d_const(PARAM_IV);
                let (h, _) = b.compress(iv, w, ds);
                b.expose(h);
                b.emit_chains(chains);
            });
        }
    }

    /// Part `i`'s honest chains with digits 2, 3 and 6, from tips of its own.
    fn chains(i: u64) -> Vec<Planned> {
        let mut rows = Vec::new();
        for (c, d) in (0..).zip([2, 3, 6]) {
            let tip = [0x1000 + c + (i << 8), 0x2000 + c];
            let mut v = tip;
            for s in d..7 {
                rows.push(Planned::Step { tweak: tweak(c, s), v });
                v = step(tweak(c, s), v);
            }
            rows.push(Planned::Link { c, d, tip, end: v });
        }
        rows
    }

    fn honest(n: u64) -> Vec<Input> {
        (0..n)
            .map(|i| {
                let x = F192::new(3 + i, 5, 7 * i);
                (x, x * x, chains(i))
            })
            .collect()
    }

    #[test]
    fn a_replay_is_its_build() {
        let n = 4;
        let zeros: Vec<Input> = (honest(n).into_iter())
            .map(|(_, _, chains)| (F192::ZERO, F192::ZERO, chains))
            .collect();
        let (zero_build, replay) = Builder::parts(n as usize, part(&zeros));

        // A build of parts is the build of the same calls on one builder.
        let mut whole = Builder::new();
        (0..n as usize).for_each(|i| part(&zeros)(&mut whole, i));
        assert_eq!(whole.finish().circuit, zero_build.circuit);

        // Mutation: a part's claimed square, a step's input, both, or two parts' steps swapped.
        //
        //     the replay makes the build's wires with the run's values
        //     → the build's values and failures: the part's unequal wires, the unbalanced dynamic tuples, none when
        //       the parts' tuples are unbalanced but the circuit's balance
        let mut wrong_square = honest(n);
        wrong_square[2].1 += F192::ONE;
        let mut wrong_step = honest(n);
        let Planned::Step { v, .. } = &mut wrong_step[1].2[0] else {
            unreachable!("a chain from digit 2 steps")
        };
        v[0] ^= 1;
        let mut both = wrong_step.clone();
        both[2].1 = wrong_square[2].1;
        let mut swapped = honest(n);
        let (one, two) = swapped.split_at_mut(2);
        // Chain 0's five steps, from digit 2.
        one[1].2[..5].swap_with_slice(&mut two[0].2[..5]);
        let checks = |failures: &[Unsatisfied]| -> Vec<String> { failures.iter().map(ToString::to_string).collect() };
        for (inputs, expected) in [
            (honest(n), vec![]),
            (wrong_square, vec!["part 2: unequal wires"]),
            (wrong_step, vec![": the dynamic tuples balance"]),
            (both, vec!["part 2: unequal wires", ": the dynamic tuples balance"]),
            (swapped, vec![]),
        ] {
            let (built, _) = Builder::parts(n as usize, part(&inputs));
            assert_eq!(checks(&replay.assert_replays(part(&inputs), &built)), expected);
        }
    }

    #[test]
    #[should_panic(expected = "a part reads of earlier parts only the constants and rows its folds hand it")]
    fn a_part_reads_no_other_part_s_wire() {
        // Part 1 adds the first part's `x`, wire 0, which is the prover's.
        let foreign = |b: &mut Builder, i: usize| {
            let x = b.free_e(F192::new(i as u64 + 2, 0, 0));
            let sum = if i == 0 { x } else { b.add(x, Ew(0)) };
            b.expose(sum);
        };
        let (_, replay) = Builder::parts(2, foreign);
        let _ = replay.values(foreign);
    }
}
