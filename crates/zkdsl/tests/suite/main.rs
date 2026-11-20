//! The zkDSL crate's integration tests share one binary and its initialization caches.

mod common;

mod const_placeholder;
mod disassemble;
mod miscompiles;
mod py_source;
mod range_check;
mod statements;
mod vm;
mod vm_proofs;
