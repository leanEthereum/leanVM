// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Reed-Solomon encoding over `E = GF(2^192)` with base-field twiddles.
//!
//! Deeper WHIR levels encode an E-valued, folded witness on the same K-domain.
//!
//! # Why it is the base transform
//!
//! ```text
//!     an E element is three K coefficients:   a = (a_0, a_1, a_2)
//!
//!     twiddle t in K:     a * t  =  (a_0 * t, a_1 * t, a_2 * t)
//!     addition:           a + b  =  (a_0 + b_0, a_1 + b_1, a_2 + b_2)
//!
//!     so one E lane is three independent K lanes:
//!     row = [ a_0 a_1 a_2 | b_0 b_1 b_2 | ... ]   n E lanes  =  3n K lanes
//! ```
//!
//! Every butterfly acts on each coefficient alone, so the encode runs as the base transform over `3n` lanes.

use crate::ntt::{AdditiveNttF64, RowSink};
use primitives::field::{F64, F192};

// An E element is exactly three K words, with no padding, so the two views line up.
const _: () = assert!(size_of::<F192>() == 3 * size_of::<F64>());
const _: () = assert!(align_of::<F192>() == align_of::<F64>());

/// RS-encode a row-major E-valued message into a codeword, overwriting all of it.
///
/// - The codeword is `2^r` copies of the message, each transformed from layer `r` on.
/// - Here `r` is the log inverse rate.
/// - The codeword may start uninitialized.
/// - `on_rows` gets every finished block of rows, as K words.
///
/// # Panics
///
/// Panics unless the lane count is a power of two.
pub(crate) fn encode_interleaved_ext(
    ntt: &AdditiveNttF64,
    mat: &mut [F192],
    msg: &[F192],
    num_ntts: usize,
    log_inv_rate: usize,
    on_rows: &RowSink<'_>,
) {
    assert!(num_ntts.is_power_of_two());
    // View both buffers as K words: each row of n E lanes becomes 3n K lanes.
    //
    // SAFETY:
    // - An E element is laid out as three K words, and a K element as one word.
    // - So each view covers exactly the same memory as the slice it came from.
    let (mat, msg) = unsafe {
        (
            std::slice::from_raw_parts_mut(mat.as_mut_ptr().cast::<F64>(), 3 * mat.len()),
            std::slice::from_raw_parts(msg.as_ptr().cast::<F64>(), 3 * msg.len()),
        )
    };
    ntt.encode_interleaved_with(mat, msg, 3 * num_ntts, log_inv_rate, on_rows);
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::log2_strict_usize;
    use primitives::test_util::Rng;

    /// Reference E-valued transform: one butterfly at a time, with the E-by-K product.
    fn forward_scalar(ntt: &AdditiveNttF64, data: &mut [F192], num_ntts: usize, start_layer: usize) {
        let log_d = log2_strict_usize(data.len() / num_ntts);
        for layer in start_layer..log_d {
            // At this layer, each block pairs its top half with its bottom half.
            let half = 1usize << (log_d - layer - 1);
            for block in 0..1usize << layer {
                // One twiddle per block.
                let twiddle = ntt.twiddle(layer, block);
                for row in block * 2 * half..block * 2 * half + half {
                    for lane in 0..num_ntts {
                        // Butterfly: u' = u + v * t, then v' = v + u'.
                        let (top, bot) = (row * num_ntts + lane, (row + half) * num_ntts + lane);
                        let new_u = data[top] + data[bot].mul_base(twiddle);
                        data[bot] += new_u;
                        data[top] = new_u;
                    }
                }
            }
        }
    }

    #[test]
    fn encode_matches_replicate_then_scalar_transform() {
        // Invariant: the encode equals replicating the message, then an E-valued transform.
        //
        // The reference multiplies true E elements by K twiddles.
        // So a match also proves the three-coefficient view is exact.
        //
        // Each shape forces one plan for a message held apart from the codeword, under the budgets used off Apple silicon:
        //
        //     (log_d, lanes, rate)   K words a row   plan
        //     (3, 1, 1)              3               deep sub-blocks built in scratch
        //     (8, 4, 2)              12              deep sub-blocks built in scratch
        //     (12, 16, 1)            48              one gathered pass reading the message
        //     (14, 16, 4)            48              one gathered pass reading the message
        //     (15, 16, 7)            48              deep sub-blocks built in scratch
        //     (16, 2, 1)             6               one gathered pass reading the message
        //     (12, 1024, 1)          3072            two gathered passes, with streaming stores
        //     (4, 2, 4)              6               rate = log_d: no layer left, copies only
        let mut rng = Rng::new(0xE192);
        for (log_d, lanes, rate) in [
            (3usize, 1usize, 1usize),
            (8, 4, 2),
            (12, 16, 1),
            (14, 16, 4),
            (15, 16, 7),
            (16, 2, 1),
            (12, 1024, 1),
            (4, 2, 4),
        ] {
            let ntt = AdditiveNttF64::standard(log_d);
            let msg = rng.ext_vec((lanes << log_d) >> rate);
            // Reference: 2^rate explicit copies, then the E-valued transform from the rate layer.
            let mut want: Vec<F192> = msg.iter().copied().cycle().take(msg.len() << rate).collect();
            forward_scalar(&ntt, &mut want, lanes, rate);
            // Under test: a zeroed codeword, filled by the encode alone.
            let mut got = vec![F192::ZERO; want.len()];
            encode_interleaved_ext(&ntt, &mut got, &msg, lanes, rate, &|_, _| {});
            assert_eq!(got, want, "log_d={log_d}, lanes={lanes}, rate={rate}");
        }
    }
}
