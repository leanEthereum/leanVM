//! The `verifier` crate, pinned against `cpu::prove`, on the proof of a real program
//! (`fixture.rs`, a zkDSL program the Lean back end compiled).

extern crate stable_lean_vm_core as lean_vm_core;
mod fixture;
mod portable_verifier;
