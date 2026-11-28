//! Hotwire: one-hot pointer links checked by two chained sum-checks.
//!
//! Every row of an instruction table names what it touches by pointers: its cycle, the memory cells it reads and
//! writes, and its instruction in the program. Each pointer is committed one-hot ([`mod@pointer`]), so a sum-check over
//! the index `j` ([`index`]) and one over the rows and pointer columns ([`row`], with the tables' own terms in
//! [`base`]) together show that every row reads the memory, program and neighbouring state its pointers name, and that
//! the cycle pointers enumerate `0..T` once each (`prove`). The mirror test of Emile Wambsgans shows each executed
//! pointer is one-hot; one-hot addressing follows Shout (Setty and Thaler). A `KECCAK` block's later cells are read
//! inside their pointer's window, its lowest chunk.

pub mod base;
pub mod index;
#[cfg(test)]
mod negative;
pub mod pointer;
pub(crate) mod prove;
pub mod row;
