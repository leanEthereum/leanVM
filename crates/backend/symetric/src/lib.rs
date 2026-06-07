// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod permutation;
pub use permutation::*;

mod sponge;
pub use sponge::*;

mod compression;
pub use compression::*;

pub mod merkle;

mod poseidon_utils;
pub use poseidon_utils::*;

pub const DIGEST_ELEMS: usize = 8;
pub const RATE: usize = 8;
pub const WIDTH: usize = RATE * 2;
pub const CAPACITY: usize = WIDTH - RATE;
