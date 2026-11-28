//! Hotwire: one-hot pointer links checked by two chained sum-checks.
//!
//! Every row of an instruction table names what it touches by pointers: its cycle, the memory cells it reads
//! and writes, and its instruction in the program. Each pointer is committed one-hot ([`mod@pointer`]), so a
//! sum-check over the index `j` (`index`) and one over the rows and pointer columns ([`row`]) together show
//! that every row reads the memory, program and neighbouring state its pointers name, and that the cycle
//! pointers enumerate `0..T` once each. The mirror test of Emile Wambsgans shows each executed pointer is
//! one-hot; one-hot addressing follows Shout (Setty and Thaler). A `KECCAK` block's later cells are read inside
//! their pointer's window, its lowest chunk.

use primitives::field::F128;

pub mod base;
pub(crate) mod index;
pub mod pointer;
pub(crate) mod prove;
pub mod row;

#[cfg(test)]
mod negative;

/// `v[i]`, zero past the end of `v`.
#[inline(always)]
fn at(v: &[F128], i: usize) -> F128 {
    v.get(i).copied().unwrap_or(F128::ZERO)
}

/// The line through `a` at 0 and `b` at 1, at `x`: no product when the two agree.
#[inline(always)]
fn fold(a: F128, b: F128, x: F128) -> F128 {
    if a == b { a } else { a + x * (a + b) }
}
