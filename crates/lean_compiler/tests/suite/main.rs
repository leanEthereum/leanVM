//! Compiler integration tests share one binary and its initialization caches.

mod common;

mod assert_ne;
mod const_placeholder;
mod deref_copies;
mod determinism;
mod disassemble;
mod dispatch_frames;
mod field_div;
mod field_towers;
mod hint_log2_ceil;
mod inline_expr;
mod inline_returns;
mod loop_frames;
mod miscompiles;
mod pack64x2;
mod print_debug;
mod py_source;
mod range_check;
mod sharing;
mod stack_bits;
mod stack_buf;
mod statements;
mod transcript_helpers;
mod vm_proofs;
