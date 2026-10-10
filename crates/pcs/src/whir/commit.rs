// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The WHIR commitments, each Merkle-committed one leaf per codeword row.
//!
//! - L0 encodes the witness's words of `K`.
//! - Every deeper level encodes a folded witness over `E`, with twiddles in `K`.

use crate::merkle::{Hash, MerkleBuilder};
use crate::ntt::AdditiveNttF64;
use primitives::field::{F64, F192};
use std::sync::Arc;

/// The L0 commitment as its prover keeps it: the codeword and its Merkle tree.
///
/// The message itself is not kept: the caller holds it for opening.
pub(crate) struct ProverData {
    /// The committed lanes' codeword, row-major: position `q` holds `n_lanes` words, lane-descending.
    pub(crate) codeword: Vec<F64>,
    /// Every node of the Merkle tree, the root last.
    pub(crate) merkle_tree: Vec<Hash>,
}

impl ProverData {
    /// The Merkle root.
    pub(crate) fn root(&self) -> Hash {
        *self.merkle_tree.last().expect("a tree has a root")
    }
}

/// Commit to the words of `K` of a `2^log_n`-word witness, one RS codeword per lane.
///
/// # Layout
///
/// - `message` is the witness's leading `n_lanes` lane blocks, each `2^(log_n - log_batch_size)` words.
/// - `n_lanes` is read off the message length and lies in `1..=2^log_batch_size`.
/// - Each lane is RS-encoded at rate `2^-log_inv_rate`.
/// - A leaf is one codeword position across all `2^log_batch_size` lanes, `8 * 2^log_batch_size` bytes.
///
/// # Absent lanes
///
/// The stacked witness's zero tail is whole lanes, so those lanes are never encoded.
/// The encoding is linear, so their codeword is zero.
///
/// The leaf image is therefore the one a full-width commitment would hash, with those zeros leading it:
///
/// ```text
///     codeword lane t  =  message block n_lanes - 1 - t
///     leaf image       =  [ 2^log_batch_size - n_lanes zeros | block n_lanes-1, ..., block 0 ]
/// ```
///
/// - The leading zeros' whole BLAKE2s blocks are one chaining value that every leaf shares.
/// - Only the image's tail, the committed lanes, rides the proof.
/// - A verifier derives `n_lanes` from the announced layout to read a row, and supplies the zeros itself.
///
/// # Panics
///
/// - If `log_inv_rate` is 0, or the witness is no wider than the interleaving.
/// - If the message is not between one and `2^log_batch_size` whole lane blocks.
pub(crate) fn commit(message: &[F64], log_n: usize, log_batch_size: usize, log_inv_rate: usize) -> ProverData {
    assert!(log_inv_rate >= 1, "log_inv_rate must be >= 1 for a non-trivial RS code");
    assert!(log_n > log_batch_size, "witness must be wider than the interleaving");
    let log_rows = log_n - log_batch_size;
    let n_lanes = message.len() >> log_rows;
    assert_eq!(message.len(), n_lanes << log_rows, "message is whole lane blocks");
    assert!(
        n_lanes >= 1 && n_lanes <= 1usize << log_batch_size,
        "at most 2^log_batch_size lanes carry data"
    );
    let k_code = log_rows + log_inv_rate;
    let n_positions = 1usize << k_code;
    let codeword_len = n_positions * n_lanes;

    let mut codeword = Box::new_uninit_slice(codeword_len);

    // Leaves are hashed as the encode finishes each block of rows.
    let tree = MerkleBuilder::new(n_positions, n_lanes, 1usize << log_batch_size);
    tracing::info_span!("NTT", kind = "base encode", log_domain = k_code, lanes = n_lanes).in_scope(|| {
        // SAFETY: every codeword word is written before it is read.
        // - The transpose writes every word of the message region, the first `message.len()` words.
        // - Its tiling asserts that it covers the whole region.
        // - The encode fills every other replica from that region before transforming it in place.
        let codeword = unsafe { primitives::write_only(&mut codeword) };
        crate::ntt::transpose_lane_major(&mut codeword[..message.len()], message, n_lanes, log_rows);
        let ntt = AdditiveNttF64::standard(k_code);
        ntt.encode_interleaved_in_place_with(codeword, n_lanes, log_inv_rate, &|row, rows| {
            tree.absorb(row, rows);
        });
    });
    // SAFETY: the transpose and the encode above wrote every word of the codeword.
    let codeword = unsafe { codeword.assume_init() }.into_vec();
    let merkle_tree = tracing::info_span!("Merkle").in_scope(|| tree.finish());
    ProverData { codeword, merkle_tree }
}

/// One deeper WHIR commitment level: its message and Merkle tree.
///
/// Each codeword row is one Merkle leaf of `num_interleaved` elements of `E`.
///
/// The codeword is not kept: an opened row is evaluated again from the message.
pub(crate) struct LigeroWitness {
    /// The folded witness this level commits, row-major, `num_interleaved` values a row.
    msg: Arc<Vec<F192>>,
    /// The transform over the level's codeword domain.
    ntt: AdditiveNttF64,
    /// Every node of the Merkle tree, the root last.
    pub tree: Vec<Hash>,
    /// Codeword positions, one leaf each.
    pub(crate) block_len: usize,
    /// Elements of `E` in one row.
    num_interleaved: usize,
}

impl LigeroWitness {
    /// The Merkle root.
    #[inline]
    pub(super) fn root(&self) -> Hash {
        self.tree[self.tree.len() - 1]
    }

    /// The codeword rows at `positions`, each evaluated once however often it repeats.
    pub(super) fn open(&self, positions: &[usize]) -> OpenedRows {
        let mut unique = positions.to_vec();
        unique.sort_unstable();
        unique.dedup();
        let rows = self.ntt.rows_at_ext(&self.msg, self.num_interleaved, &unique);
        OpenedRows {
            positions: unique,
            rows,
            width: self.num_interleaved,
        }
    }
}

/// Codeword rows of one level, by position.
pub(super) struct OpenedRows {
    /// The positions, ascending.
    positions: Vec<usize>,
    /// Their rows, one after another.
    rows: Vec<F192>,
    /// Elements of `E` in one row.
    width: usize,
}

impl OpenedRows {
    /// The row at `position`.
    ///
    /// # Panics
    ///
    /// Panics unless the row was opened.
    pub(super) fn row(&self, position: usize) -> &[F192] {
        let index = self.positions.binary_search(&position).expect("an opened position");
        &self.rows[index * self.width..][..self.width]
    }
}

/// Commit a polynomial over `E` at one recursive WHIR level.
///
/// - `poly` is row-major: `2^log_msg_cols` rows of `2^log_num_interleaved` values.
/// - Each lane, one column of that layout, is RS-encoded at rate `2^-log_inv_rate` with twiddles in `K`.
/// - Each codeword row is hashed as one Merkle leaf as the encode finishes it, then dropped.
///
/// # Panics
///
/// Panics unless `poly` holds exactly `2^(log_msg_cols + log_num_interleaved)` values.
pub(crate) fn ligero_commit_ext(
    poly: Arc<Vec<F192>>,
    log_msg_cols: usize,
    log_num_interleaved: usize,
    log_inv_rate: usize,
) -> LigeroWitness {
    let msg_cols = 1usize << log_msg_cols;
    let num_interleaved = 1usize << log_num_interleaved;
    let block_len = msg_cols << log_inv_rate;
    let log_block_len = log_msg_cols + log_inv_rate;
    assert_eq!(poly.len(), num_interleaved * msg_cols);
    let ntt = AdditiveNttF64::standard(log_block_len);

    // One leaf per row, each element of `E` as its three words of `K`.
    let row_words = 3 * num_interleaved;
    let builder = MerkleBuilder::new(block_len, row_words, row_words);
    tracing::info_span!(
        "NTT",
        kind = "extension encode",
        log_domain = log_block_len,
        lanes = num_interleaved
    )
    .in_scope(|| {
        ntt.encode_rows_ext(&poly, num_interleaved, log_inv_rate, &|row, rows| {
            builder.absorb(row, rows);
        });
    });
    let tree = tracing::info_span!("Merkle").in_scope(|| builder.finish());

    LigeroWitness {
        msg: poly,
        ntt,
        tree,
        block_len,
        num_interleaved,
    }
}
