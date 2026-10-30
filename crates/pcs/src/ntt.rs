// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The additive NTT (Lin-Chung-Han novel polynomial basis) WHIR commits with.
//!
//! It is the Reed-Solomon encoder of every WHIR commitment over K = F_{2^64}.
//!
//! # The model
//!
//! - A buffer is `2^log_d` rows of `num_ntts` words. Each word of a row is one lane: an independent transform.
//! - A codeword row is a Merkle leaf, so finished rows go to a [`RowSink`] while they are still in cache.
//! - A codeword is `2^r` cosets of one message, `r` the log inverse rate. The cosets split at layer `r`.
//! - Layers run neighbors-last: layer 0 pairs rows half the domain apart.
//! - A transform is bound by memory bandwidth, so the encode minimizes sweeps of the buffer.
//!
//! # The far and near layers
//!
//! ```text
//!     layers:  start ............ deep_start ............ log_d
//!              |---- gathered passes ----|---- deep pass ----|
//!              far layers: strided groups   near layers: contiguous sub-blocks
//!              gathered into L2 scratch     run in L2, rows to the sink
//! ```
//!
//! # Where the message comes from
//!
//! - `Source::Replicas`: the buffer already holds the blocks. Every pass after the first, and the tests.
//! - `Source::InPlace`: each block copies the buffer's own block 0. This is the in-place encode.
//! - `Source::Rows`: each block copies a row-major message held apart.
//! - `Source::Lanes`: each block is a lane-major message, transposed through a stage by the first pass.
//! - With a lane-major message and no kept codeword, the encode runs once per half of the cosets.
//!
//! # The components
//!
//! ```text
//!     AdditiveNttF64 (facade)
//!          |
//!          +-- Encoder::transform(Window, Source)
//!          |       Plan                 where the layers split, and the task sizes
//!          |       GatheredPass         far layers, one sweep each      -> Stage, Drain
//!          |       DeepPass             near layers, rows to the sink
//!          |            both run their groups through Layers::run over the Twiddles
//!          +-- Openings::rows(Kept)     rows read back from what the encode kept
//! ```
//!
//! # Reading order
//!
//! 1. `encode.rs`: the three encodes, then `Encoder::transform`, which is the spine.
//! 2. `plan.rs`: why the layers split where they do.
//! 3. `source.rs` and `window.rs`: the message, and the buffer it becomes.
//! 4. `layers.rs`: a range of layers on one sub-block, with global twiddles.
//! 5. `twiddles.rs`: the points of the domain. Optional.
//! 6. `gathered.rs`, `stage.rs` and `drain.rs`: the far layers, the lane-major stage and the write-back.
//! 7. `deep.rs`: the near layers.
//! 8. `openings.rs`: the rows read back.
//! 9. `kernels.rs`, `scratch.rs` and `tests.rs`.

mod deep;
mod drain;
mod encode;
mod facade;
mod gathered;
mod kernels;
mod layers;
mod openings;
mod plan;
mod scratch;
mod source;
mod stage;
#[cfg(test)]
mod tests;
mod twiddles;
mod window;

pub use encode::{Encoded, Keep, RowSink};
pub use facade::AdditiveNttF64;
pub(crate) use kernels::transpose_butterfly_lanes;
pub use openings::{Kept, Openings, gather_rows};
pub use plan::Plan;
