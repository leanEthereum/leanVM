//! Compiler integration tests share one binary and its initialization caches.
//!
//! These tests leave the proving arena disabled. A test that enables it needs
//! its own process (see `rec_aggregation`'s `arena_prove`).

mod common;

mod assert_ne;
mod const_placeholder;
mod determinism;
mod disassemble;
mod field_div;
mod field_towers;
mod filler;
mod hint_log2_ceil;
mod inline_expr;
mod pack64x2;
mod print_debug;
mod py_source;
mod range_check;
mod sharing;
mod soundness;
mod stack_bits;
mod stack_buf;
mod statements;
mod transcript_helpers;
mod vm_proofs;
