//! Instruction tables: class specifications, local columns, bus tuples, and witness filling.
//!
//! Column and port order are protocol data.
//! Circuit words are virtual columns bound to the machine through the bus.

mod bus;
mod columns;
mod fill;
mod id;
pub(crate) mod spec;
mod table;
mod word;

pub use id::{N_TABLES, PerTable, TableId, TableKey};
pub use spec::{BAD_SLOT, ClassSpec, EXIT_SLOT, Fill, Ram};
pub use table::ClassTable;
pub use word::Word;

pub(crate) use bus::Separator;
pub(crate) use fill::FillContext;

/// One of a table's flock circuits: its class's function, or for a class with none, what it checks of its operands.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Part {
    /// Instruction semantics.
    Class,
    /// Operand checks of a class proven by identities.
    Operands,
}
