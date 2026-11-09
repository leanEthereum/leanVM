//! The `verifier` crate, pinned against `cpu::prove`.
//!
//! An integration test rather than a `src` module: pinning it needs a proof
//! of a real program, so it needs the zkDSL compiler, and `lean_compiler`
//! depends on this crate. Cargo allows that cycle through dev-dependencies,
//! but only for a target that links the ordinary library.

mod fixture;
mod portable_verifier;
mod whir_query_table;
