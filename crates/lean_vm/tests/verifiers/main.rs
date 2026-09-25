//! The Python verifier of this protocol, pinned against `cpu::verify` on
//! hand-assembled programs and on Rust guests.

mod constants;
mod corrupted;
mod guests;
mod programs;
mod python_verifier;
mod whir_query_table;
