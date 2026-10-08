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
//! A row of the codeword is evaluated the same way, one K lane per coefficient.

use crate::ntt::{AdditiveNttF64, RowSink};
use primitives::field::{F64, F192};

// An E element is exactly three K words, with no padding, so the two views line up.
const _: () = assert!(size_of::<F192>() == 3 * size_of::<F64>());
const _: () = assert!(align_of::<F192>() == align_of::<F64>());

/// RS-encode a row-major E-valued message, handing `on_rows` every row of the codeword as K words and keeping none.
///
/// - The codeword is `2^r` copies of the message, each transformed from layer `r` on.
/// - Here `r` is the log inverse rate.
///
/// # Panics
///
/// Panics unless the lane count is a power of two.
pub(crate) fn encode_rows_ext(
    ntt: &AdditiveNttF64,
    msg: &[F192],
    num_ntts: usize,
    log_inv_rate: usize,
    on_rows: &RowSink<'_>,
) {
    assert!(num_ntts.is_power_of_two());
    ntt.encode_rows_with(words(msg), 3 * num_ntts, log_inv_rate, on_rows);
}

/// The rows at `positions` of the codeword [`encode_rows_ext`] encodes `msg` into, one after another.
pub(crate) fn rows_at_ext(ntt: &AdditiveNttF64, msg: &[F192], num_ntts: usize, positions: &[usize]) -> Vec<F192> {
    let rows = ntt.rows_at(words(msg), 3 * num_ntts, positions);
    rows.as_chunks::<3>()
        .0
        .iter()
        .map(|&[c0, c1, c2]| F192::new(c0.0, c1.0, c2.0))
        .collect()
}

/// An E slice as its K words: each row of n E lanes becomes 3n K lanes.
const fn words(msg: &[F192]) -> &[F64] {
    // SAFETY:
    // - An E element is laid out as three K words, and a K element as one word.
    // - So the view covers exactly the same memory as the slice.
    unsafe { std::slice::from_raw_parts(msg.as_ptr().cast::<F64>(), 3 * msg.len()) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::log2_strict_usize;
    use primitives::test_util::Rng;
    use std::sync::Mutex;

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
    fn encode_and_rows_match_replicate_then_scalar_transform() {
        // Invariant: the encode hands over every row of the replicated, E-valued transform exactly once.
        // And a row evaluated from the message is that same row.
        //
        // The reference multiplies true E elements by K twiddles.
        // So a match also proves the three-coefficient view is exact.
        //
        // Each shape forces one plan, under the budgets used off Apple silicon:
        //
        //     (log_d, lanes, rate)   K words a row   plan
        //     (3, 1, 1)              3               whole replicas built in scratch
        //     (8, 4, 2)              12              whole replicas built in scratch
        //     (12, 16, 1)            48              whole replicas built in scratch
        //     (14, 16, 4)            48              whole replicas built in scratch
        //     (15, 16, 2)            48              one replica at a time: a gathered pass, then deep sub-blocks
        //     (17, 16, 4)            48              one replica at a time, sixteen of them
        //     (16, 2, 1)             6               whole replicas built in scratch, two tasks
        //     (12, 1024, 1)          3072            one replica at a time: two gathered passes, then deep sub-blocks
        //     (4, 2, 4)              6               rate = log_d: no layer left, copies only
        let mut rng = Rng::new(0xE192);
        for (log_d, lanes, rate) in [
            (3usize, 1usize, 1usize),
            (8, 4, 2),
            (12, 16, 1),
            (14, 16, 4),
            (15, 16, 2),
            (17, 16, 4),
            (16, 2, 1),
            (12, 1024, 1),
            (4, 2, 4),
        ] {
            let ntt = AdditiveNttF64::standard(log_d);
            let msg = rng.ext_vec((lanes << log_d) >> rate);
            // Reference: 2^rate explicit copies, then the E-valued transform from the rate layer.
            let mut want: Vec<F192> = msg.iter().copied().cycle().take(msg.len() << rate).collect();
            forward_scalar(&ntt, &mut want, lanes, rate);
            let want_words = words(&want);

            // Under test: the rows the encode hands over, each written once into a zeroed codeword.
            let row_words = 3 * lanes;
            let got = Mutex::new((vec![F64::ZERO; want_words.len()], vec![0u32; 1 << log_d]));
            encode_rows_ext(&ntt, &msg, lanes, rate, &|row, rows| {
                let (codeword, seen) = &mut *got.lock().unwrap();
                codeword[row * row_words..][..rows.len()].copy_from_slice(rows);
                for count in &mut seen[row..row + rows.len() / row_words] {
                    *count += 1;
                }
            });
            let (codeword, seen) = got.into_inner().unwrap();
            assert!(
                seen.iter().all(|&count| count == 1),
                "log_d={log_d}, lanes={lanes}, rate={rate}"
            );
            assert_eq!(codeword, want_words, "log_d={log_d}, lanes={lanes}, rate={rate}");

            // Rows at spread positions, the first and last included, from the message alone.
            let positions: Vec<usize> = (0..1 << log_d)
                .step_by(((1 << log_d) / 37).max(1))
                .chain([(1 << log_d) - 1, 0])
                .collect();
            let rows = rows_at_ext(&ntt, &msg, lanes, &positions);
            for (&p, row) in positions.iter().zip(rows.chunks_exact(lanes)) {
                assert_eq!(
                    row,
                    &want[p * lanes..][..lanes],
                    "position {p}, log_d={log_d}, lanes={lanes}"
                );
            }
        }
    }
}
