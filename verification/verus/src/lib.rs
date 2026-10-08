//! Verus proofs of leanVM's portable field arithmetic, bit transposes and additive NTT.
#![allow(unused_parens, unused_imports, unused_variables, dead_code, clippy::all)]

pub mod bits;
pub mod clmul;
pub mod gf2_64;
pub mod gf2_64x3;
pub mod gf2_8;
pub mod ntt;
