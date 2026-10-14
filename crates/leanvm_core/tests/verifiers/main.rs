//! The `verifier` crate and the Python verifier, pinned against `cpu::prove` and each other.
//!
//! An integration test rather than a `src` module: pinning them needs a proof
//! of a real program, so it needs the zkDSL compiler, and `lean_compiler`
//! depends on this crate. Cargo allows that cycle through dev-dependencies,
//! but only for a target that links the ordinary library.

mod portable_verifier;
mod python_verifier;
mod whir_query_table;
