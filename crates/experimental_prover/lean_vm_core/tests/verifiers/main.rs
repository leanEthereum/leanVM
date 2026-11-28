//! The `verifier` crate, pinned against this tree's `cpu::prove`, and both verifiers' WHIR query table and grinds,
//! pinned against the security search only this tree keeps.
//!
//! An integration test rather than a `src` module: pinning it needs a proof of a real program, so it needs the zkDSL
//! compiler, and `zkdsl_compiler` depends on this crate. Cargo allows that cycle through dev-dependencies, but only for
//! a target that links the ordinary library.

extern crate experimental_lean_vm_core as lean_vm_core;
mod fixture;
mod portable_verifier;
mod whir_query_table;
