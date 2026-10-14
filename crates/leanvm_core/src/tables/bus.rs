//! State, bytecode, and memory tuples for the offline bus.

use crate::bus::Coord;
use primitives::field::F64;

/// Domain of a bus tuple, encoded in its first coordinate.
///
/// Explicit discriminants fix the protocol encoding.
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
