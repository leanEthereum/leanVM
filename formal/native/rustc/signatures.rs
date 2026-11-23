//! Both deployed signature verifiers in one LTO module, sharing their Keccak and memory routines.

#![no_std]
#![no_builtins]

mod mem;
mod runtime;
mod sphincs;
mod xmss;
