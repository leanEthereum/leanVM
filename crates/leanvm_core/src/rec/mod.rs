//! The recursion machine: a circuit of rows over six tables, wired by copy cycles, and its proof (Annex E).

mod bus;
pub mod circuit;
mod clean;
mod error;
mod fixed;
mod layout;
pub mod proof;
pub mod table;
pub mod transcript;
pub mod tree;
pub mod verifier;

pub use error::RecError;
pub(crate) use fixed::FixedColumn;
