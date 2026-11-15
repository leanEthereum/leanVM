//! leanVM's `aggregation`, compiled from its own sources (see `build.rs`), with the Lean
//! exporters as its child module `aggregation::lean_export`.

#![allow(dead_code, unused_imports, clippy::all)]

include!(concat!(env!("OUT_DIR"), "/aggregation/overlay.rs"));

pub use aggregation::lean_export;
