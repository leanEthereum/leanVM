//! A committed codeword whose last layers run only on the rows an opening reads.
//!
//! - A commitment hashes every row of its codeword, but an opening reads only a few of them.
//! - So the encode hashes each deep sub-block from scratch and never writes it back.
//! - The buffer keeps every row as the gathered passes left it.
//! - An opened row is finished by running the deep layers again on the one sub-block holding it.
//! - That sub-block fits a cache, so an opening costs a few small transforms instead of a write sweep of the codeword.

use super::{AdditiveNttF64, RowSink, SendPtr, transpose_lane_major, with_scratch};
use primitives::field::F64;
use primitives::log2_strict_usize;

/// A message to encode, as its caller holds it.
#[derive(Clone, Copy)]
pub(crate) enum Message<'a> {
    /// Row-major: word `row * width + lane`.
    Rows(&'a [F64]),
    /// Lane-major: codeword lane `t` encodes the contiguous block `width - 1 - t`.
    Lanes(&'a [F64]),
}

/// A row-major RS codeword of interleaved lanes, its deep layers pending.
///
/// Its rows are read through an opening, which runs those layers.
pub struct Codeword {
    words: Vec<F64>,
    /// Words a row.
    width: usize,
    ntt: AdditiveNttF64,
    /// First layer the buffer has not run: the domain's depth when it is final.
    pending: usize,
}

impl Codeword {
    /// RS-encode a message at rate `2^-log_inv_rate`, handing `on_rows` every finished block of rows.
    ///
    /// - It is called as `on_rows(first_row, rows)`, from pool tasks.
    /// - Each row is handed over exactly once, while it is still in cache.
    /// - Blocks are aligned, and all of one power-of-two size.
    pub(crate) fn encode(
        ntt: AdditiveNttF64,
        msg: Message<'_>,
        width: usize,
        log_inv_rate: usize,
        on_rows: &RowSink<'_>,
    ) -> Self {
        let len = match msg {
            Message::Rows(m) | Message::Lanes(m) => m.len(),
        };
        let mut words = Box::new_uninit_slice(len << log_inv_rate);
        // SAFETY: every word is written before it is read.
        // The message reaches the buffer through the transpose or through the first pass.
        // Either way it fills its replicas, and the deep layers then read only what those wrote.
        let data = unsafe { primitives::write_only(&mut words) };
        let pending = match msg {
            // Read-only from here on: the pointer only feeds the first pass's reads.
            Message::Rows(m) => ntt.transform(
                data,
                width,
                log_inv_rate,
                Some(SendPtr(m.as_ptr().cast_mut())),
                Some(on_rows),
            ),
            // The transpose fills the first replica, which is then the message.
            Message::Lanes(m) => {
                transpose_lane_major(&mut data[..len], m, width, log2_strict_usize(len / width));
                let first = SendPtr(data.as_mut_ptr());
                ntt.transform(data, width, log_inv_rate, Some(first), Some(on_rows))
            }
        };
        // SAFETY: the encode wrote the whole buffer.
        let words = unsafe { words.assume_init() }.into_vec();
        Self {
            words,
            width,
            ntt,
            pending,
        }
    }

    /// Words in the codeword.
    pub const fn len(&self) -> usize {
        self.words.len()
    }

    /// Whether the codeword has no words.
    pub const fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    /// The finished rows at `positions`, each pending sub-block run once.
    pub(crate) fn open(&self, positions: &[usize]) -> Opened {
        let mut positions = positions.to_vec();
        positions.sort_unstable();
        positions.dedup();

        let log_d = log2_strict_usize(self.words.len() / self.width);
        let log_sub = log_d - self.pending;
        let sub_len = self.width << log_sub;
        let mut subs: Vec<usize> = positions.iter().map(|&q| q >> log_sub).collect();
        subs.dedup();

        // One task per sub-block: its opened rows, in order.
        let rows = parallel::map_collect(subs.len(), |k| {
            let s = subs[k];
            with_scratch(sub_len, |sub| {
                sub.copy_from_slice(&self.words[s * sub_len..][..sub_len]);
                self.ntt
                    .run_layers(sub, log_d, self.width, self.pending, log_d, self.pending, s);
                let first = positions.partition_point(|&q| q >> log_sub < s);
                let mut out = Vec::new();
                for &q in positions[first..].iter().take_while(|&&q| q >> log_sub == s) {
                    out.extend_from_slice(&sub[(q - (s << log_sub)) * self.width..][..self.width]);
                }
                out
            })
        });
        Opened {
            positions,
            words: rows.concat(),
            width: self.width,
        }
    }
}

/// Finished rows of a codeword, by position.
pub(crate) struct Opened {
    /// Sorted and distinct.
    positions: Vec<usize>,
    words: Vec<F64>,
    width: usize,
}

impl Opened {
    /// The row at `position`.
    ///
    /// # Panics
    ///
    /// Panics unless the row was opened.
    pub(crate) fn row(&self, position: usize) -> &[F64] {
        let i = self.positions.binary_search(&position).expect("an opened row");
        &self.words[i * self.width..][..self.width]
    }
}
