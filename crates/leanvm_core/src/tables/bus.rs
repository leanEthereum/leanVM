//! State, bytecode, and memory tuples for the offline bus.

use crate::leaf::Coord::{self, Col, Const};
use primitives::field::F64;
use std::iter::Enumerate;
use std::vec::IntoIter;

/// Domain of a bus tuple, encoded in its first coordinate.
///
/// Explicit discriminants keep the Rust and Python protocol encodings fixed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum Separator {
    /// Instruction state transitions.
    State = 0,
    /// RAM and advice, whose address ranges are disjoint.
    Memory = 1,
    /// Reads of the public decoded instruction table.
    Bytecode = 2,
    /// Register cells, inaccessible through memory addresses.
    Registers = 3,
}

impl Separator {
    /// The monomial field element assigned to this domain.
    pub(crate) const fn value(self) -> F64 {
        // Degrees 0..3 are below the field modulus, so the monomials need no reduction.
        F64(1 << self as u8)
    }

    /// A constant bus coordinate identifying this domain.
    pub(crate) const fn coordinate(self) -> Coord {
        Coord::Const(self.value())
    }
}

/// Bus tuples expressed in a table's local column indices.
pub struct FlushBuilder {
    /// Tuples produced by state transitions and memory writes.
    pub(crate) push: Vec<Vec<Coord>>,

    /// Tuples consumed by state transitions, lookups, and memory reads.
    pub(crate) pull: Vec<Vec<Coord>>,
}

impl FlushBuilder {
    /// Start collecting paired state and memory tuples, plus lookup reads.
    pub(crate) const fn new() -> Self {
        Self {
            push: Vec::new(),
            pull: Vec::new(),
        }
    }

    fn pair(&mut self, push: Vec<Coord>, pull: Vec<Coord>) {
        self.push.push(push);
        self.pull.push(pull);
    }

    /// Pull the current instruction and clock, then push the derived successor.
    ///
    /// The exit marker binds the last row to the final state.
    pub(super) fn state(&mut self, pc: usize, ts: usize, step: usize, npc: Coord, exit: Coord) {
        self.pair(
            vec![
                Separator::State.coordinate(),
                npc,
                Coord::Sum(vec![Col(ts), Col(step)]),
                exit,
            ],
            vec![Separator::State.coordinate(), Col(pc), Col(ts), Const(F64::ZERO)],
        );
    }

    /// Pull a lookup tuple supplied by the array's multiplicity-weighted producer.
    pub(super) fn read(&mut self, tuple: Vec<Coord>) {
        self.pull.push(tuple);
    }

    /// Bind each access to its clock slot and previous-timestamp column.
    pub(super) fn accesses(&mut self, ts: usize, prev: usize, slots: Vec<u32>) -> Accesses<'_> {
        Accesses {
            bus: self,

            ts,
            prev,
            slots: slots.into_iter().enumerate(),
        }
    }
}

/// A row's memory accesses in the same order as its clock ports.
pub(super) struct Accesses<'a> {
    /// Bus tuples collected for this row.
    bus: &'a mut FlushBuilder,

    /// Local column holding the row's current timestamp.
    ts: usize,

    /// First local column holding an access's previous timestamp.
    prev: usize,

    /// Remaining clock slots paired with their previous-timestamp indices.
    slots: Enumerate<IntoIter<u32>>,
}

impl Accesses<'_> {
    /// Read a cell and put back the same value at the new timestamp.
    pub(super) fn read(&mut self, separator: Coord, address: Coord, value: Coord) {
        self.write(separator, address, value.clone(), value);
    }

    /// Pull the previous cell value and push its replacement at this access's timestamp.
    pub(super) fn write(&mut self, separator: Coord, address: Coord, old: Coord, new: Coord) {
        // Every tuple shares the row's clock, with one distinct slot per access.
        let (i, slot) = self.slots.next().expect("one slot per access");
        let at = match slot {
            0 => Col(self.ts),
            _ => Coord::Sum(vec![Col(self.ts), Const(F64(u64::from(slot)))]),
        };
        self.bus.pair(
            vec![separator.clone(), address.clone(), at, new],
            vec![separator, address, Col(self.prev + i), old],
        );
    }

    /// Check that every clock port has exactly one memory tuple.
    pub(super) fn finish(mut self) {
        assert!(self.slots.next().is_none(), "a clock slot has no memory access");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn separators_keep_the_protocol_encodings() {
        // The Python verifier reads these four field words without Rust's enum discriminants.
        for (separator, expected) in [
            (Separator::State, 1),
            (Separator::Memory, 2),
            (Separator::Bytecode, 4),
            (Separator::Registers, 8),
        ] {
            assert_eq!(separator.value(), F64(expected));
            assert!(matches!(separator.coordinate(), Const(value) if value == F64(expected)));
        }
    }

    #[test]
    #[should_panic(expected = "a clock slot has no memory access")]
    fn unused_access_slots_are_refused() {
        // A clock port without a corresponding memory tuple cannot be left unbound.
        let mut bus = FlushBuilder::new();
        let mut accesses = bus.accesses(0, 1, vec![0, 3]);
        accesses.read(Separator::Registers.coordinate(), Col(2), Col(3));
        accesses.finish();
    }

    #[test]
    #[should_panic(expected = "one slot per access")]
    fn extra_accesses_are_refused() {
        // Every tuple needs its own previous-timestamp port and clock slot.
        let mut bus = FlushBuilder::new();
        bus.accesses(0, 1, vec![])
            .read(Separator::Registers.coordinate(), Col(2), Col(3));
    }
}
