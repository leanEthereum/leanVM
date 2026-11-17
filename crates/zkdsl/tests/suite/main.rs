//! The zkDSL crate's integration tests share one binary and its initialization caches.

mod common;

mod assert_ne;
mod const_placeholder;
mod disassemble;
mod miscompiles;
mod py_source;
mod range_check;
mod stack_bits;
mod stack_buf;
mod statements;
mod vm_proofs;
