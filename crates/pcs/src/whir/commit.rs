// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The WHIR commitments, each Merkle-committed one leaf per codeword row.
//!
//! - L0 encodes the witness's words of `K`.
//! - Every deeper level encodes a folded witness over `E`, with twiddles in `K`.

use crate::merkle::{Hash, MerkleBuilder, MerkleTree, sorted_unique};
use crate::ntt::{AdditiveNtt, Pad, transpose_lane_major};
use crate::verifier::OpeningVerifier;
use crate::whir::anchor::anchor_value;
use crate::whir::query::Padding;
use crate::whir::verify::WhirError;
use fiat_shamir::{ProverState, TranscriptContext};
use primitives::field::{F64, F192};
use std::sync::Arc;

/// The public shape of the committed, zero-padded witness.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CommitmentShape {
    pub log_n: usize,
    pub log_batch_size: usize,
    pub log_inv_rate: usize,
    pub n_lanes: usize,
}

impl CommitmentShape {
    /// Check the raw encoding shape before any shape-dependent shifts or reads.
    pub(crate) fn valid(self) -> bool {
        self.log_n > self.log_batch_size
            && self.log_n < usize::BITS as usize
            && self.log_inv_rate >= 1
            && (self.log_n - self.log_batch_size)
                .checked_add(self.log_inv_rate)
                .is_some_and(|log_code| log_code < usize::BITS as usize)
            && self.n_lanes >= 1
            && self.n_lanes <= 1usize << self.log_batch_size
    }
}

/// Immutable commitment identity: its pre-commit context, shape, root, and MLE anchor.
#[derive(Clone, Debug)]
pub struct Commitment<E = F192, R = Hash, K = F64> {
    pub(crate) root: R,
    pub(crate) shape: CommitmentShape,
    pub(crate) context: TranscriptContext<K, R>,
    pub(crate) point: Vec<E>,
    pub(crate) value: E,
}

/// The commitment's scalar, digest and pending-word representations selected by a verifier.
pub(crate) type VerifierCommitment<V> =
    Commitment<<V as fiat_shamir::arith::Arith>::E, <V as OpeningVerifier>::Root, <V as OpeningVerifier>::K>;

impl<E, R, K> Commitment<E, R, K> {
    pub const fn root(&self) -> R
    where
        R: Copy,
    {
        self.root
    }

    pub const fn shape(&self) -> CommitmentShape {
        self.shape
    }

    pub const fn context(&self) -> TranscriptContext<K, R>
    where
        K: Copy,
        R: Copy,
    {
        self.context
    }

    pub fn point(&self) -> &[E] {
        &self.point
    }

    pub const fn value(&self) -> E
    where
        E: Copy,
    {
        self.value
    }

    pub(crate) const fn valid_context(&self) -> bool {
        if self.context.pending_bytes > 64 {
            return false;
        }
        let words = self.context.pending_bytes.div_ceil(8);
        let mut i = 0;
        while i < 8 {
            if self.context.pending[i].is_some() != (i < words) {
                return false;
            }
            i += 1;
        }
        true
    }
}

// Little-endian bytes "whir-anchor-v1", padded with zeros to three limbs.
const ANCHOR_DOMAIN: F192 = F192::new(0x636e612d72696877, 0x000031762d726f68, 0);

// Little-endian bytes "whir-opening-v1", padded with zeros to three limbs.
const OPENING_DOMAIN: F192 = F192::new(0x65706f2d72696877, 0x0031762d676e696e, 0);

fn commitment_constants(shape: CommitmentShape) -> [F192; 3] {
    [
        ANCHOR_DOMAIN,
        F192::new(
            shape.log_n as u64,
            shape.log_batch_size as u64,
            shape.log_inv_rate as u64,
        ),
        F192::from(F64(shape.n_lanes as u64)),
    ]
}

/// Bind the whole immutable record before any opening challenge, including in a fresh session.
/// The root and chaining value are each a raw32 prover message; all remaining fields keep their F192 packing and order.
pub(crate) fn send_record_binding(ps: &mut ProverState, commitment: &Commitment) {
    let mut constants = commitment_constants(commitment.shape);
    constants[0] = OPENING_DOMAIN;
    let mut i = 0;
    while i < constants.len() {
        ps.prover_message(&constants[i]);
        i += 1;
    }
    ps.prover_message(&commitment.root);
    ps.prover_message(&commitment.context.state);
    let context = &commitment.context;
    ps.prover_message(&F192::new(
        context.pending_bytes as u64,
        u64::from(context.first),
        context.previous,
    ));
    ps.prover_message(&F192::new(context.squeezed, 0, 0));
    let words = context.pending_bytes.div_ceil(8);
    let mut i = 0;
    while i + 3 <= words {
        ps.prover_message(&F192::new(
            context.pending[i].unwrap().0,
            context.pending[i + 1].unwrap().0,
            context.pending[i + 2].unwrap().0,
        ));
        i += 3;
    }
    if i < words {
        let second = if i + 1 < words {
            context.pending[i + 1].unwrap().0
        } else {
            0
        };
        ps.prover_message(&F192::new(context.pending[i].unwrap().0, second, 0));
    }
    let mut i = 0;
    while i < commitment.shape.log_n {
        ps.prover_message(&commitment.point[i]);
        i += 1;
    }
    ps.prover_message(&commitment.value);
}

fn verify_record_constants<V: OpeningVerifier>(v: &mut V, constants: &[F192]) -> Result<(), WhirError> {
    let mut i = 0;
    while i < constants.len() {
        let actual = v.prover_message()?;
        let expected = v.constant(constants[i]);
        v.ensure_eq(actual, expected, || WhirError::CommitmentMismatch)?;
        i += 1;
    }
    Ok(())
}

fn verify_record_values<V: OpeningVerifier>(v: &mut V, values: &[V::E], len: usize) -> Result<(), WhirError> {
    let mut i = 0;
    while i < len {
        let actual = v.prover_message()?;
        v.ensure_eq(actual, values[i], || WhirError::CommitmentMismatch)?;
        i += 1;
    }
    Ok(())
}

fn verify_record_pending<V: OpeningVerifier>(
    v: &mut V,
    context: &TranscriptContext<V::K, V::Root>,
) -> Result<(), WhirError> {
    let words = context.pending_bytes.div_ceil(8);
    let mut i = 0;
    while i + 3 <= words {
        let actual = v.prover_message()?;
        let expected = v.e_of_limbs([
            context.pending[i].unwrap(),
            context.pending[i + 1].unwrap(),
            context.pending[i + 2].unwrap(),
        ]);
        v.ensure_eq(actual, expected, || WhirError::CommitmentMismatch)?;
        i += 3;
    }
    if i < words {
        let actual = v.prover_message()?;
        let zero = v.zero_k();
        let second = if i + 1 < words {
            context.pending[i + 1].unwrap()
        } else {
            zero
        };
        let expected = v.e_of_limbs([context.pending[i].unwrap(), second, zero]);
        v.ensure_eq(actual, expected, || WhirError::CommitmentMismatch)?;
    }
    Ok(())
}

/// Check every record field before opening batching; reads are determined only by the supplied record.
pub(crate) fn verify_record_binding<V: OpeningVerifier>(
    v: &mut V,
    commitment: &Commitment<V::E, V::Root, V::K>,
) -> Result<(), WhirError> {
    let mut constants = commitment_constants(commitment.shape);
    constants[0] = OPENING_DOMAIN;
    verify_record_constants(v, &constants)?;
    let root = v.next_root()?;
    v.ensure_root_eq(root, commitment.root)?;
    let state = v.next_root()?;
    v.ensure_root_eq(state, commitment.context.state)?;
    let context = &commitment.context;
    verify_record_constants(
        v,
        &[
            F192::new(context.pending_bytes as u64, u64::from(context.first), context.previous),
            F192::new(context.squeezed, 0, 0),
        ],
    )?;
    verify_record_pending(v, context)?;
    verify_record_values(v, &commitment.point, commitment.shape.log_n)?;
    let actual = v.prover_message()?;
    v.ensure_eq(actual, commitment.value, || WhirError::CommitmentMismatch)?;
    Ok(())
}

/// Receive one commitment, retaining the pre-header context and binding its public shape before drawing its anchor.
///
/// # Errors
///
/// Rejects an invalid expected shape or different public constants with
/// [`WhirError::CommitmentMismatch`], and propagates malformed transcript errors.
pub(crate) fn receive_commitment<V: OpeningVerifier>(
    v: &mut V,
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
    n_lanes: usize,
) -> Result<VerifierCommitment<V>, WhirError> {
    let shape = CommitmentShape {
        log_n,
        log_batch_size,
        log_inv_rate,
        n_lanes,
    };
    if !shape.valid() {
        return Err(WhirError::CommitmentMismatch);
    }
    let context = v.context();
    let mut constants_match = Ok(());
    for expected in commitment_constants(shape) {
        constants_match = match v.prover_message() {
            Ok(actual) => {
                let expected = v.constant(expected);
                v.ensure_eq(actual, expected, || WhirError::CommitmentMismatch)
            }
            Err(error) => Err(error.into()),
        };
        if constants_match.is_err() {
            break;
        }
    }
    constants_match?;
    let root = v.next_root()?;
    let point = v.verifier_messages(log_n);
    let value = v.prover_message()?;
    Ok(Commitment {
        root,
        shape,
        context,
        point,
        value,
    })
}

/// Commit to `message` under an immutable anchored record, as [`BaseCommitment::new`] encodes it without padding.
///
/// After encoding, retain the pre-header context, transmit the domain and shape as three scalars, then the raw32 root; draw one anchor point and transmit the zero-padded witness's MLE there.
///
/// A hiding commitment takes no anchor: its value would publish an evaluation of the hidden witness.
pub(crate) fn commit(
    ps: &mut ProverState,
    message: &[F64],
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
) -> (Commitment, BaseCommitment) {
    let mut shape = CommitmentShape {
        log_n,
        log_batch_size,
        log_inv_rate,
        n_lanes: 1,
    };
    assert!(shape.valid(), "invalid commitment encoding shape");
    let log_rows = log_n - log_batch_size;
    let n_lanes = message.len() >> log_rows;
    shape.n_lanes = n_lanes;
    assert!(shape.valid(), "at most 2^log_batch_size lanes carry data");
    assert_eq!(message.len(), n_lanes << log_rows, "message is whole lane blocks");
    let data = BaseCommitment::new(message, log_n, log_batch_size, log_inv_rate, &[]);
    let root = data.root();
    let context = ps.context();
    ps.prover_messages(&commitment_constants(shape));
    ps.prover_message(&root);
    let point = ps.verifier_messages(log_n);
    let value = anchor_value(message, log_rows, &point);
    ps.prover_message(&value);
    (
        Commitment {
            root,
            shape,
            context,
            point,
            value,
        },
        data,
    )
}

/// The L0 commitment as its prover keeps it: the codeword and its Merkle tree.
///
/// The message itself is not kept: the caller holds it for opening.
pub(crate) struct BaseCommitment {
    /// The committed lanes' codeword, row-major: position `q` holds `n_lanes` words, lane-descending.
    codeword: Vec<F64>,
    /// The Merkle tree, one leaf per codeword position.
    tree: MerkleTree,
    /// The padding of a hiding commitment, lane block `u`'s `k` coefficients at `[u k, (u + 1) k)`; empty otherwise.
    pub(crate) pads: Vec<F64>,
}

impl BaseCommitment {
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
    /// # Padding
    ///
    /// Non-empty `pads` make each lane's code longer by `k = pads.len() / n_lanes` coefficients.
    ///
    /// With `m = log_n - log_batch_size` and `r = log_inv_rate`, lane `u` encodes:
    ///
    /// ```text
    ///     P_u(X) + W_m(X + s) * R_u(X),   s = F64(2^(m + r))
    /// ```
    ///
    /// - `P_u` is the lane's `2^m` words as novel-basis coefficients.
    /// - `R_u` is its padding, `pads[u k..(u + 1) k]`.
    /// - `W_m(X + s) = W_m(X) + W_m(s)` and `X_{2^m + j} = W_m X_j`, so the lane is `2^m + k` coefficients on one domain.
    /// - The encode adds one butterfly layer pairing the message with the padding.
    /// - The factor `W_m(X + s)` vanishes nowhere on the domain, so any `k` symbols of a lane are uniform.
    ///
    /// # Panics
    ///
    /// - If `log_inv_rate` is 0, or the witness is no wider than the interleaving.
    /// - If the message is not between one and `2^log_batch_size` whole lane blocks.
    /// - Unless every lane has the same `k <= 2^m` padding coefficients.
    pub(crate) fn new(message: &[F64], log_n: usize, log_batch_size: usize, log_inv_rate: usize, pads: &[F64]) -> Self {
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
        let k = pads.len() / n_lanes;
        assert_eq!(pads.len(), k * n_lanes, "every lane takes as many padding coefficients");
        assert!(k <= 1 << log_rows, "a lane's padding is at most its message's length");
        // Row `j` of the padding is coefficient `j` of every codeword lane's `R`, lane `t` being block `n_lanes - 1 - t`.
        let pad_rows: Vec<F64> = (0..k * n_lanes)
            .map(|w| pads[(n_lanes - 1 - w % n_lanes) * k + w / n_lanes])
            .collect();
        let pad = (k > 0).then(|| Pad {
            rows: &pad_rows,
            offset: Padding::new(log_rows, log_inv_rate).shift(),
        });
        let mut codeword = Box::new_uninit_slice(codeword_len);

        // Leaves are hashed as the encode finishes each block of rows.
        let builder = MerkleBuilder::new(n_positions, n_lanes, 1usize << log_batch_size);
        tracing::info_span!("NTT", kind = "base encode", log_domain = k_code, lanes = n_lanes).in_scope(|| {
            // SAFETY: every codeword word is written before it is read.
            // - The transpose writes every word of the message region, the first `message.len()` words.
            // - Its tiling asserts that it covers the whole region.
            // - The encode fills every other replica from that region before transforming it in place.
            let codeword = unsafe { primitives::write_only(&mut codeword) };
            transpose_lane_major(&mut codeword[..message.len()], message, n_lanes, log_rows);
            let ntt = AdditiveNtt::standard(k_code);
            ntt.encode_interleaved_in_place_with(codeword, n_lanes, log_inv_rate, pad, &|row, rows| {
                builder.absorb(row, rows);
            });
        });
        // SAFETY: the transpose and the encode above wrote every word of the codeword.
        let codeword = unsafe { codeword.assume_init() }.into_vec();
        let tree = tracing::info_span!("Merkle").in_scope(|| builder.finish());
        Self {
            codeword,
            tree,
            pads: pads.to_vec(),
        }
    }

    /// The Merkle root.
    pub(crate) fn root(&self) -> Hash {
        self.tree.root()
    }

    /// Codeword positions, one leaf each.
    pub(crate) const fn num_positions(&self) -> usize {
        self.tree.num_leaves()
    }

    /// The committed lanes.
    pub(crate) const fn n_lanes(&self) -> usize {
        self.codeword.len() / self.num_positions()
    }

    /// The committed lanes' words at a position, lane-descending.
    pub(crate) fn row(&self, position: usize) -> &[F64] {
        let n_lanes = self.n_lanes();
        &self.codeword[position * n_lanes..][..n_lanes]
    }

    /// Open the rows at `queries`: one hint with each distinct row once, and their paths.
    ///
    /// A stored row is the committed lanes alone: the leaf image's tail, its leading zeros the absent lanes.
    pub(crate) fn open(&self, ps: &mut ProverState, queries: &[usize]) {
        ps.prover_hint(&self.tree.prune(queries, |q| self.row(q)).to_hint());
    }
}

/// One deeper WHIR commitment level: its message and Merkle tree.
///
/// Each codeword row is one Merkle leaf of `num_interleaved` elements of `E`.
///
/// The codeword is not kept: an opened row is evaluated again from the message.
pub(crate) struct LevelCommitment {
    /// The folded witness this level commits, row-major, `num_interleaved` values a row.
    msg: Arc<Vec<F192>>,
    /// The transform over the level's codeword domain.
    ntt: AdditiveNtt,
    /// The Merkle tree, one leaf per codeword position.
    tree: MerkleTree,
    /// Elements of `E` in one row.
    num_interleaved: usize,
}

impl LevelCommitment {
    /// Commit a polynomial over `E` at one recursive WHIR level.
    ///
    /// - `poly` is row-major: `2^log_msg_cols` rows of `2^log_num_interleaved` values.
    /// - Each lane, one column of that layout, is RS-encoded at rate `2^-log_inv_rate` with twiddles in `K`.
    /// - Each codeword row is hashed as one Merkle leaf as the encode finishes it, then dropped.
    ///
    /// # Panics
    ///
    /// Panics unless `poly` holds exactly `2^(log_msg_cols + log_num_interleaved)` values.
    pub(crate) fn new(
        poly: Arc<Vec<F192>>,
        log_msg_cols: usize,
        log_num_interleaved: usize,
        log_inv_rate: usize,
    ) -> Self {
        let msg_cols = 1usize << log_msg_cols;
        let num_interleaved = 1usize << log_num_interleaved;
        let log_block_len = log_msg_cols + log_inv_rate;
        assert_eq!(poly.len(), num_interleaved * msg_cols);
        let ntt = AdditiveNtt::standard(log_block_len);

        // One leaf per row, each element of `E` as its three words of `K`.
        let row_words = 3 * num_interleaved;
        let builder = MerkleBuilder::new(1 << log_block_len, row_words, row_words);
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

        Self {
            msg: poly,
            ntt,
            tree,
            num_interleaved,
        }
    }

    /// The Merkle root.
    pub(crate) fn root(&self) -> Hash {
        self.tree.root()
    }

    /// Codeword positions, one leaf each.
    pub(crate) const fn num_positions(&self) -> usize {
        self.tree.num_leaves()
    }

    /// Open the rows at `queries`, each evaluated once however often it repeats.
    ///
    /// The proof gets one hint with each distinct row once, and their paths.
    ///
    /// # Returns
    ///
    /// The rows in query order, repeats included.
    pub(crate) fn open(&self, ps: &mut ProverState, queries: &[usize]) -> Vec<Vec<F192>> {
        let positions = sorted_unique(queries);
        let rows = self.ntt.rows_at_ext(&self.msg, self.num_interleaved, &positions);
        let row = |q: usize| {
            let index = positions.binary_search(&q).expect("an opened position");
            &rows[index * self.num_interleaved..][..self.num_interleaved]
        };
        ps.prover_hint(
            &self
                .tree
                .prune(queries, |q| F192::coefficients(row(q)).to_vec())
                .to_hint(),
        );
        queries.iter().map(|&q| row(q).to_vec()).collect()
    }
}

#[cfg(test)]
#[test]
fn record_frame_packs_exact_duplex_context() {
    use fiat_shamir::{Blake2sDuplex, Encoding, SessionId, VerifierState};

    let input: [u8; 64] = std::array::from_fn(|i| (i + 1) as u8);
    for mode in 0..3 {
        for pending_bytes in 0usize..=64 {
            let mut duplex = Blake2sDuplex::new(SessionId::new(b"original-context").0);
            if mode == 1 {
                duplex.absorb(&input[..17]);
                duplex.squeeze(&mut [0; 3]);
            } else if mode == 2 && pending_bytes > 0 {
                duplex.absorb(&input);
            }
            duplex.absorb(&input[..pending_bytes]);
            let context = duplex.context();
            assert_eq!(context.pending_bytes, pending_bytes);
            let record = Commitment {
                root: [71; 32],
                shape: CommitmentShape {
                    log_n: 4,
                    log_batch_size: 1,
                    log_inv_rate: 1,
                    n_lanes: 1,
                },
                context,
                point: vec![F192::new(2, 3, 4); 4],
                value: F192::new(5, 6, 7),
            };
            assert!(record.valid_context());
            let mut ps = ProverState::new(&SessionId::new(b"fresh-frame"), &0u64);
            send_record_binding(&mut ps, &record);
            let proof = ps.into_proof();
            let mut expected = Vec::new();
            for scalar in [
                F192::new(0x65706f2d72696877, 0x0031762d676e696e, 0),
                F192::new(4, 1, 1),
                F192::new(1, 0, 0),
            ] {
                expected.extend_from_slice(scalar.encode().as_ref());
            }
            // Roots and chaining values are raw32 messages, not padded scalar halves.
            expected.extend_from_slice(&record.root);
            expected.extend_from_slice(&context.state);
            for scalar in [
                F192::new(pending_bytes as u64, u64::from(context.first), context.previous),
                F192::new(context.squeezed, 0, 0),
            ] {
                expected.extend_from_slice(scalar.encode().as_ref());
            }
            for bytes in input[..pending_bytes].chunks(24) {
                let mut padded = [0u8; 24];
                padded[..bytes.len()].copy_from_slice(bytes);
                expected.extend_from_slice(&padded);
            }
            for scalar in record.point.iter().chain(std::iter::once(&record.value)) {
                expected.extend_from_slice(scalar.encode().as_ref());
            }
            assert_eq!(proof.narg, expected, "mode {mode}, {pending_bytes} bytes");
            assert_eq!(
                proof.narg.len(),
                64 + 24 * (6 + record.shape.log_n + pending_bytes.div_ceil(24))
            );
            let mut vs = VerifierState::new(&SessionId::new(b"fresh-frame"), &0u64, &proof);
            verify_record_binding(&mut vs, &record).expect("all record fields match");
            vs.check_eof().expect("the frame is consumed exactly");
            if mode == 0 && pending_bytes == 0 {
                let mut legacy = proof.clone();
                let mut padded_roots = Vec::new();
                for digest in [record.root, context.state] {
                    for half in digest.as_chunks::<16>().0 {
                        padded_roots.extend_from_slice(half);
                        padded_roots.extend_from_slice(&[0; 8]);
                    }
                }
                legacy.narg.splice(3 * 24..3 * 24 + 64, padded_roots);
                let mut vs = VerifierState::new(&SessionId::new(b"fresh-frame"), &0u64, &legacy);
                assert_eq!(
                    verify_record_binding(&mut vs, &record),
                    Err(WhirError::CommitmentMismatch)
                );
            }
            for index in 0..proof.narg.len() {
                let mut bad = proof.clone();
                bad.narg[index] ^= 1;
                let mut vs = VerifierState::new(&SessionId::new(b"fresh-frame"), &0u64, &bad);
                assert_eq!(
                    verify_record_binding(&mut vs, &record),
                    Err(WhirError::CommitmentMismatch),
                    "mode {mode}, {pending_bytes} bytes, byte {index}",
                );
            }
        }
    }
}

#[cfg(test)]
#[test]
fn commitment_retains_context_and_the_single_sampled_anchor() {
    use fiat_shamir::{SessionId, VerifierState};

    let label = b"commitment-record";
    let prefix = F192::new(7, 11, 13);
    let witness = [F64(3), F64(5), F64(7), F64(11)];
    let mut ps = ProverState::new(&SessionId::new(label), &0u64);
    ps.prover_message(&prefix);
    let expected_context = ps.context();
    let (record, data) = commit(&mut ps, &witness, 3, 1, 1);
    assert_eq!(record.context(), expected_context);
    assert_eq!(data.root(), record.root());
    assert_eq!(record.value(), anchor_value(&witness, 2, record.point()));
    let proof = ps.into_proof();
    assert_eq!(
        proof.narg.len(),
        5 * 24 + 32,
        "prefix, three shape scalars, raw32 root, anchor value"
    );
    let mut vs = VerifierState::new(&SessionId::new(label), &0u64, &proof);
    assert_eq!(vs.prover_message::<F192>().unwrap(), prefix);
    let received = receive_commitment(&mut vs, 3, 1, 1, 1).unwrap();
    assert_eq!(received.context(), record.context());
    assert_eq!(received.shape(), record.shape());
    assert_eq!(received.root(), record.root());
    assert_eq!(received.point(), record.point());
    assert_eq!(received.value(), record.value());
    vs.check_eof().unwrap();
}

#[cfg(test)]
#[test]
fn malformed_commitment_shape_rejects_without_reading_or_sampling() {
    use fiat_shamir::{SessionId, VerifierState};

    let proof = ProverState::new(&SessionId::new(b"shape-guards"), &0u64).into_proof();
    for shape in [
        CommitmentShape {
            log_n: 3,
            log_batch_size: 3,
            log_inv_rate: 1,
            n_lanes: 1,
        },
        CommitmentShape {
            log_n: usize::MAX,
            log_batch_size: 1,
            log_inv_rate: 1,
            n_lanes: 1,
        },
        CommitmentShape {
            log_n: 3,
            log_batch_size: 1,
            log_inv_rate: usize::MAX,
            n_lanes: 1,
        },
        CommitmentShape {
            log_n: 3,
            log_batch_size: 1,
            log_inv_rate: 1,
            n_lanes: 0,
        },
        CommitmentShape {
            log_n: 3,
            log_batch_size: 1,
            log_inv_rate: 1,
            n_lanes: 3,
        },
    ] {
        let mut vs = VerifierState::new(&SessionId::new(b"shape-guards"), &0u64, &proof);
        let before = vs.context();
        assert!(matches!(
            receive_commitment(
                &mut vs,
                shape.log_n,
                shape.log_batch_size,
                shape.log_inv_rate,
                shape.n_lanes,
            ),
            Err(WhirError::CommitmentMismatch)
        ));
        assert_eq!(vs.context(), before);
    }
}
