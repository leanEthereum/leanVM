//! The state, bytecode, and log-link tuples a table's rows put on the bus.

use crate::leaf::Coord::{self, Col, Const, Scaled};
use primitives::field::{F64, G};

/// Domain of a bus tuple, encoded in its first coordinate.
///
/// Explicit discriminants fix the protocol encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum Separator {
    /// Instruction state transitions.
    State = 0,
    /// The memory log's accesses: RAM and the advice, whose address ranges are disjoint.
    Memory = 1,
    /// Reads of the public decoded instruction table.
    Bytecode = 2,
    /// The register log's cycles.
    Registers = 3,
    /// The register log's cycles whose destination holds an address, and is not written.
    Pointer = 4,
}

impl Separator {
    /// The monomial field element assigned to this domain.
    pub(crate) const fn value(self) -> F64 {
        // Degrees 0..4 are below the field modulus, so the monomials need no reduction.
        F64(1 << self as u8)
    }

    /// A constant bus coordinate identifying this domain.
    pub(crate) const fn coordinate(self) -> Coord {
        Coord::Const(self.value())
    }
}

/// Bus tuples expressed in a table's local column indices.
///
/// Every tuple has its position, or a padding row's zero, at coordinate 2.
pub struct FlushBuilder {
    /// Tuples a row pushes: its successor state.
    pub(crate) push: Vec<Vec<Coord>>,

    /// Tuples a row pulls: its state, its entry, its register cycle, and its memory accesses.
    pub(crate) pull: Vec<Vec<Coord>>,
}

impl FlushBuilder {
    pub(crate) const fn new() -> Self {
        Self {
            push: Vec::new(),
            pull: Vec::new(),
        }
    }

    /// Pull the current state, then push the successor: the next instruction, one cycle on, `next_position` in memory.
    ///
    /// The exit marker binds the last row to the final state.
    pub(super) fn state(
        &mut self,
        pc: usize,
        time: usize,
        position: usize,
        npc: Coord,
        next_position: Coord,
        exit: Coord,
    ) {
        let state = Separator::State.coordinate();
        self.push
            .push(vec![state.clone(), npc, Scaled(G, time), next_position, exit]);
        self.pull
            .push(vec![state, Col(pc), Col(time), Col(position), Const(F64::ZERO)]);
    }

    /// Pull a tuple another side pushes: a lookup's entry, or a log's access.
    pub(super) fn pull(&mut self, tuple: Vec<Coord>) {
        self.pull.push(tuple);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn separators_keep_the_protocol_encodings() {
        for (separator, expected) in [
            (Separator::State, 1),
            (Separator::Memory, 2),
            (Separator::Bytecode, 4),
            (Separator::Registers, 8),
            (Separator::Pointer, 16),
        ] {
            assert_eq!(separator.value(), F64(expected));
            assert!(matches!(separator.coordinate(), Const(value) if value == F64(expected)));
        }
    }
}
