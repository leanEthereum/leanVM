//! The padding rows: what fills each table from its height up to the power of two it is proven over (doc §sec:jagged).
//!
//! A table is proven over `2^tau` rows, at least flock's instance floor, while the run fills only its first `height` of them.
//!
//! The rest repeat one row, which the bus leaves out (its blocks take the identity there) and the commitment stores once ([`crate::cpu::committed_rows`]).
//!
//! Flock still proves every row's instance, so that row has to be an honest one: a no-op of the table's class at clock zero, on zero registers, which the text carries for the purpose ([`append_noops`]).

use crate::tables::{CLASSES, N_TABLES};

/// The words the no-ops take in the text: one per table.
pub const WORDS: usize = N_TABLES;

/// Append one no-op per table to `text`, returning where each landed: the entry its padding rows read.
///
/// A no-op touches only `x0` and address zero, which a padding row at clock zero never touches for real.
pub fn append_noops(text: &mut Vec<u32>) -> [usize; N_TABLES] {
    std::array::from_fn(|t| {
        let nop = CLASSES[t].class.nop().expect("every table's class has an instruction");
        text.push(nop.bits());
        text.len() - 1
    })
}
