// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! A framework for finite fields.

extern crate alloc;

pub mod exponentiation;
mod field;
mod helpers;
pub mod integers;
pub mod op_assign_macros;
mod packed;

pub use field::*;
pub use helpers::*;
pub use packed::*;

pub type VarCount = usize;

pub trait ToUsize {
    fn to_usize(self) -> usize;
}

impl<F: PrimeField64> ToUsize for F {
    fn to_usize(self) -> usize {
        self.as_canonical_u64() as usize
    }
}
