//! Instruction tables: class specifications, local columns, bus tuples, and witness filling.
//!
//! Column and port order are protocol data.
//! Circuit words are virtual columns bound to the machine through the bus.

mod bus;
mod circuits;
mod clean;
mod clock;
mod columns;
mod fill;
mod id;
pub(crate) mod spec;
mod table;
mod word;

pub use circuits::{CircuitId, MIN_CUBE_LOG, N_CIRCUITS, Part, batch_log};
pub use clock::Clock;
pub use id::{N_TABLES, PerTable, TableId, TableKey};
pub use spec::{BAD_SLOT, ClassSpec, EXIT_SLOT, Fill, N_CLASS_CIRCUITS};
pub use table::ClassTable;
pub use word::Word;

pub(crate) use bus::Separator;
pub(crate) use fill::FillContext;
