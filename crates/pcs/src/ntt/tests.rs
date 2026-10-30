//! Tests of the additive NTT: its encoders and the openings that read rows back.

use std::sync::atomic::{AtomicUsize, Ordering};

use primitives::field::F64;
use primitives::log2_strict_usize;
use primitives::test_rng::Rng;

use super::encode::{Encoded, Encoder, Keep};
use super::facade::AdditiveNttF64;
use super::openings::Kept;
use super::source::Source;
use super::stage::transpose_lane_major;
use super::window::Window;

/// Test oracle: fill every replica with a copy of a message held elsewhere.
fn replicate_rows(data: &mut [F64], msg: &[F64]) {
    for replica in data.chunks_mut(msg.len()) {
        replica.copy_from_slice(msg);
    }
}

/// A row sink that copies each handed-over block into `dst` at its row, without locking.
/// Every row is handed over exactly once, so the blocks written from pool tasks are disjoint.
fn sink_into(dst: &mut [F64], row_words: usize) -> impl Fn(usize, &[F64]) + Sync + '_ {
    let len = dst.len();
    let base = parallel::SendPtr(dst.as_mut_ptr());
    move |row, rows| {
        assert!((row * row_words).checked_add(rows.len()).is_some_and(|end| end <= len));
        // SAFETY: in bounds, and the sink contract hands each row over once, so no
        // other task writes this range. `dst` is borrowed for as long as the sink lives.
        unsafe { base.slice(row * row_words, rows.len()) }.copy_from_slice(rows);
    }
}

/// Scalar reference: one butterfly at a time over `num_ntts` interleaved lanes.
fn forward_scalar_from_layer(ntt: &AdditiveNttF64, data: &mut [F64], num_ntts: usize, start_layer: usize) {
    let n_total = data.len();
    let log_d = log2_strict_usize(n_total / num_ntts);

    for layer in start_layer..log_d {
        let num_blocks = 1usize << layer;
        let block_size = 1usize << (log_d - layer);
        let block_size_half = block_size >> 1;
        let block_elems = block_size * num_ntts;
        for block in 0..num_blocks {
            let twiddle = ntt.twiddle(layer, block);
            let block_start = block * block_elems;
            for row in 0..block_size_half {
                let off_top = block_start + row * num_ntts;
                let off_bot = off_top + block_size_half * num_ntts;
                for lane in 0..num_ntts {
                    let v = data[off_bot + lane];
                    let new_u = data[off_top + lane] + v * twiddle;
                    data[off_top + lane] = new_u;
                    data[off_bot + lane] = v + new_u;
                }
            }
        }
    }
}

/// Check forward∘inverse = id and scalar == parallel.
#[test]
fn inverse_roundtrip_and_variants_agree() {
    let ntt = AdditiveNttF64::standard(12);
    let mut rng = Rng::new(1);
    for log_d in [1usize, 3, 6, 10] {
        let n = 1usize << log_d;
        let orig: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();

        let mut a = orig.clone();
        forward_scalar_from_layer(&ntt, &mut a, 1, 0);
        let mut c = orig.clone();
        Encoder::new(&ntt.tw).transform(&mut Window::new(&mut c, 1, 0), 0, Source::Replicas, None, false);
        assert_eq!(a, c, "parallel == scalar at log_d={log_d}");

        ntt.inverse_transform(&mut a);
        assert_eq!(a, orig, "inverse roundtrip at log_d={log_d}");
    }
}

#[test]
fn interleaved_parallel_matches_scalar() {
    // Invariant: the parallel transform equals the scalar reference, word for word.
    //
    // Each shape forces one plan of the driver, under the budgets used off Apple silicon:
    //
    //     (log_d, lanes, start)   plan
    //     (7, 3, 0)               deep pass only, a single sub-block
    //     (7, 17 or 24, 0)        the same, with a vector tail or whole vectors
    //     (12, 8, 0 or 1)         one gathered pass, then deep sub-blocks
    //     (14, 64, 0 or 1)        one gathered pass, then deep sub-blocks
    //     (10, 2048, 0)           wide rows shrink the cache budgets: one gathered pass
    //     (12, 2048, 1)           two gathered passes, with streaming stores
    //     (18, 48, 1)             one gathered pass whose groups drain a line at a time
    //     (20, 9, 1)              streaming stores, rows that are not whole cache lines
    //
    // A non-zero start is the commit path, which enters at the rate layer.
    let mut rng = Rng::new(0xC0FFEE);
    for (log_d, lanes, start_layer) in [
        (7usize, 3usize, 0usize),
        (7, 17, 0),
        (7, 24, 0),
        (12, 8, 0),
        (12, 8, 1),
        (14, 64, 0),
        (14, 64, 1),
        (10, 2048, 0),
        (12, 2048, 1),
        (18, 48, 1),
        (20, 9, 1),
    ] {
        let ntt = AdditiveNttF64::standard(log_d);
        let original: Vec<F64> = (0..lanes << log_d).map(|_| F64(rng.next_u64())).collect();

        // Reference: one butterfly at a time.
        let mut want = original.clone();
        forward_scalar_from_layer(&ntt, &mut want, lanes, start_layer);
        // Under test: the pass-planning driver.
        let mut got = original;
        let mut win = Window::new(&mut got, lanes, 0);
        Encoder::new(&ntt.tw).transform(&mut win, start_layer, Source::Replicas, None, false);

        assert_eq!(got, want, "log_d={log_d}, lanes={lanes}, start_layer={start_layer}");
    }
}

#[test]
fn fused_encode_matches_replicate_then_transform() {
    // Invariant: encoding in place equals replicating the message, then transforming.
    //
    // The in-place encode never materializes the replicas up front.
    // Its message is the buffer's own first replica, which the plan must overwrite last.
    // The plans are those of the budgets used off Apple silicon.
    //
    //     (log_d, lanes, rate)   plan
    //     (9, 8, 1)              replicate first, then deep pass only
    //     (12, 64, 2)            one gathered pass reading the first replica
    //     (14, 8, 1)             one gathered pass reading the first replica
    //     (14, 64, 2)            one gathered pass reading the first replica
    //     (12, 2048, 1)          two gathered passes, with streaming stores
    //     (18, 48, 2)            one gathered pass reading the first replica, groups draining a line at a time
    //     (20, 9, 2)             the same with rows that are not whole cache lines
    //     (4, 8, 4)              rate = log_d: no layer left, rows handed over at the end
    //
    // The handed-over rows must tile the codeword once, each block already final.
    let mut rng = Rng::new(0xE0C0DE);
    for (log_d, lanes, log_inv_rate) in [
        (9usize, 8usize, 1usize),
        (12, 64, 2),
        (14, 8, 1),
        (14, 64, 2),
        (12, 2048, 1),
        (18, 48, 2),
        (20, 9, 2),
        (4, 8, 4),
    ] {
        let ntt = AdditiveNttF64::standard(log_d);
        let msg_len = (lanes << log_d) >> log_inv_rate;
        let msg: Vec<F64> = (0..msg_len).map(|_| F64(rng.next_u64())).collect();

        // Reference: 2^rate explicit copies, then the scalar transform from the rate layer.
        let mut want = vec![F64::ZERO; msg_len << log_inv_rate];
        replicate_rows(&mut want, &msg);
        forward_scalar_from_layer(&ntt, &mut want, lanes, log_inv_rate);

        // Under test: only the first replica holds the message, the rest is zero.
        let mut got = vec![F64::ZERO; msg_len << log_inv_rate];
        got[..msg_len].copy_from_slice(&msg);
        ntt.encode_interleaved_in_place(&mut got, lanes, log_inv_rate);
        assert_eq!(got, want, "log_d={log_d}, lanes={lanes}, rate={log_inv_rate}");

        // Under test: a separate message, with the rows handed to a sink.
        let mut sep = vec![F64::ZERO; got.len()];
        let mut handed = vec![F64::ZERO; got.len()];
        let hits: Vec<AtomicUsize> = (0..1usize << log_d).map(|_| AtomicUsize::new(0)).collect();
        let write = sink_into(&mut handed, lanes);
        ntt.encode_interleaved_with(&mut sep, &msg, lanes, log_inv_rate, false, &|row, rows| {
            for hit in &hits[row..row + rows.len() / lanes] {
                hit.fetch_add(1, Ordering::Relaxed);
            }
            write(row, rows)
        });
        drop(write);
        assert_eq!(
            sep, want,
            "separate message, log_d={log_d}, lanes={lanes}, rate={log_inv_rate}"
        );
        // Every row handed over exactly once, so the blocks tile the rows, and each is final.
        assert!(
            hits.iter().all(|h| h.load(Ordering::Relaxed) == 1),
            "blocks tile the rows, log_d={log_d}"
        );
        assert_eq!(handed, want, "a handed-over block is final, log_d={log_d}");
    }
}

/// Every lane of the codeword must be exactly the single-lane RS codeword of
/// that lane's contiguous message block, which is what makes a commitment over
/// `n_lanes` lanes equal to the `2^log_batch_size`-lane one with a zero tail.
/// The shapes cover the transposing fused first pass, its fallback, and lane
/// counts that are not powers of two (the padding-free commit's whole point).
#[test]
fn lane_major_msg_encode_matches_per_lane_reference() {
    let mut rng = Rng::new(0x1A2E);
    for (log_rows, log_inv_rate, n_lanes) in [
        (2usize, 1usize, 3usize),
        (3, 1, 1),
        (5, 2, 7),
        (9, 1, 5),
        (12, 2, 37),
        (14, 1, 64),
    ] {
        let log_d = log_rows + log_inv_rate;
        let ntt = AdditiveNttF64::standard(log_d);
        let rows = 1usize << log_rows;
        let msg: Vec<F64> = (0..rows * n_lanes).map(|_| F64(rng.next_u64())).collect();

        let row_words = n_lanes.next_multiple_of(8);
        let mut got = vec![F64::ZERO; (row_words << log_rows) << log_inv_rate];
        transpose_lane_major(&mut got[..row_words << log_rows], &msg, n_lanes, row_words, log_rows);
        ntt.encode_interleaved_in_place(&mut got, row_words, log_inv_rate);

        let block_len = 1usize << log_d;
        for lane in 0..row_words {
            // The leading lanes are zero padding, the rest encode message block `row_words - 1 - lane`.
            let mut want = vec![F64::ZERO; block_len];
            if lane >= row_words - n_lanes {
                let block = row_words - 1 - lane;
                replicate_rows(&mut want, &msg[block * rows..(block + 1) * rows]);
                let mut win = Window::new(&mut want, 1, 0);
                Encoder::new(&ntt.tw).transform(&mut win, log_inv_rate, Source::Replicas, None, false);
            }
            for pos in 0..block_len {
                assert_eq!(
                    got[pos * row_words + lane],
                    want[pos],
                    "lane {lane} pos {pos} at log_rows={log_rows}, rate={log_inv_rate}, n_lanes={n_lanes}"
                );
            }
        }
    }
}

/// The lane-major encode reads the message in its first gathered pass, so it must equal the
/// transpose into block 0 followed by the in-place encode: rows handed over and rows opened.
/// The shapes cover a fused first pass (with and without padding lanes, at both rates),
/// a deep-only plan, and a domain too small for any gathered pass.
#[test]
fn lane_major_encode_matches_transpose_then_in_place() {
    let mut rng = Rng::new(0x7A5E);
    for (log_rows, log_inv_rate, n_lanes) in [
        (13usize, 2usize, 47usize),
        (14, 1, 40),
        (13, 1, 17),
        (12, 2, 64),
        (5, 2, 7),
    ] {
        let log_d = log_rows + log_inv_rate;
        let ntt = AdditiveNttF64::standard(log_d);
        let msg: Vec<F64> = (0..n_lanes << log_rows).map(|_| F64(rng.next_u64())).collect();
        let row_words = n_lanes.next_multiple_of(8);
        let mut want = vec![F64::ZERO; (row_words << log_rows) << log_inv_rate];
        transpose_lane_major(&mut want[..row_words << log_rows], &msg, n_lanes, row_words, log_rows);
        ntt.encode_interleaved_in_place(&mut want, row_words, log_inv_rate);

        for keep in [Keep::Whole, Keep::BeforeDeep, Keep::Nothing] {
            let mut handed = vec![F64::ZERO; want.len()];
            let on_rows = sink_into(&mut handed, row_words);
            let encoded = ntt.encode_lane_major(&msg, n_lanes, row_words, log_inv_rate, keep, &on_rows);
            let Encoded { words, deep } = encoded;
            drop(on_rows);
            let keep_nothing = keep == Keep::Nothing;
            let context =
                format!("log_rows={log_rows}, rate={log_inv_rate}, n_lanes={n_lanes}, keep_nothing={keep_nothing}");
            assert_eq!(handed, want, "handed-over rows, {context}");
            let mut positions: Vec<usize> = (0..40).map(|_| rng.next_u64() as usize % (1 << log_d)).collect();
            positions.sort_unstable();
            let rows = match deep {
                Some(plan) if words.is_empty() => {
                    let kept = Kept::Nothing {
                        msg: &msg,
                        n_lanes,
                        plan,
                    };
                    ntt.openings().rows(kept, &positions)
                }
                Some(deep) => ntt.openings().rows(
                    Kept::BeforeDeep {
                        words: &words,
                        plan: deep,
                    },
                    &positions,
                ),
                None => {
                    assert_eq!(words, want, "codeword, {context}");
                    positions
                        .iter()
                        .flat_map(|&q| words[q * row_words..][..row_words].iter().copied())
                        .collect()
                }
            };
            for (&q, row) in positions.iter().zip(rows.chunks_exact(row_words)) {
                assert_eq!(row[..], want[q * row_words..][..row_words], "row {q}, {context}");
            }
        }
    }
}

/// Without the deep writeback, the handed-over rows and the rows finished on demand
/// must equal the full encode's, wherever the plan splits off a deep pass.
///
/// A deep-only plan with a separate message builds the whole codeword and returns `None`.
/// The in-place, deep-only, deferred branch runs in `lane_major_encode_matches_transpose_then_in_place`,
/// at shape `(5, 2, 7)`.
#[test]
fn deferred_deep_rows_match_the_full_encode() {
    let mut rng = Rng::new(0xDEE9);
    let shapes = [
        (14usize, 51usize, 1usize, true),
        (15, 64, 2, true),
        (9, 8, 1, false),
        (4, 8, 4, false),
    ];
    for (log_d, lanes, log_inv_rate, split) in shapes {
        let ntt = AdditiveNttF64::standard(log_d);
        let msg_len = (lanes << log_d) >> log_inv_rate;
        let msg: Vec<F64> = (0..msg_len).map(|_| F64(rng.next_u64())).collect();
        let mut want = vec![F64::ZERO; msg_len << log_inv_rate];
        want[..msg_len].copy_from_slice(&msg);
        ntt.encode_interleaved_in_place(&mut want, lanes, log_inv_rate);

        let mut got = vec![F64::ZERO; msg_len << log_inv_rate];
        let mut handed = vec![F64::ZERO; got.len()];
        let sink = sink_into(&mut handed, lanes);
        let deep = ntt.encode_interleaved_with(&mut got, &msg, lanes, log_inv_rate, true, &sink);
        drop(sink);
        assert_eq!(handed, want, "handed-over rows, log_d={log_d}, lanes={lanes}");
        assert_eq!(deep.is_some(), split, "plan, log_d={log_d}, lanes={lanes}");
        let mut positions: Vec<usize> = (0..40).map(|_| rng.next_u64() as usize % (1 << log_d)).collect();
        positions.sort_unstable();
        let rows = match deep {
            Some(deep) => ntt.openings().rows(
                Kept::BeforeDeep {
                    words: &got,
                    plan: deep,
                },
                &positions,
            ),
            None => positions
                .iter()
                .flat_map(|&q| got[q * lanes..][..lanes].iter().copied())
                .collect(),
        };
        for (&q, row) in positions.iter().zip(rows.chunks_exact(lanes)) {
            assert_eq!(
                row[..],
                want[q * lanes..][..lanes],
                "row {q}, log_d={log_d}, lanes={lanes}"
            );
        }
    }
}
