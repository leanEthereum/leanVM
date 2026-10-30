// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Pack each 64 consecutive witness bits into one `F64`, least significant bit first.

/// `log_2` of the packing width. F_{2^64} holds 64 bits = 2^6.
pub const LOG_PACKING: usize = 6;

/// Packing width (number of bits per F_{2^64} element).
pub const PACKING_WIDTH: usize = 1 << LOG_PACKING;
