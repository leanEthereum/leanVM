//! What the opening's verifier reads beyond scalars: roots, queries and opened rows.
//!
//! The same verifier code runs natively and as its replay in rows of the recursion machine.
//!
//! - Natively a root is a digest, a query an index, and a committed word a `K` value.
//! - In rows they are the wires holding them, and an opened row is authenticated by hash rows.

use super::whir::sample_queries_ordered;
use fiat_shamir::Hashing;
use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::{Receiver, TranscriptError, VerifierState};
use primitives::field::{F64, F192};

/// A verifier of the stacked opening: its commitments, its queries, and the rows they open.
///
/// It extends the scalar verifier with the operations that touch roots, query indices and words of `K`.
pub trait OpeningVerifier: Verifier {
    /// A commitment's root.
    type Root: Copy;
    /// A committed word of `K`.
    type K: Copy;
    /// A query's index.
    type Query;

    /// Read the next commitment's root, bound into the transcript.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the stream, or on a root that is no canonical digest.
    fn next_root(&mut self) -> Result<Self::Root, TranscriptError>;

    /// Sample `count` query indices of `depth` bits, in transcript order.
    ///
    /// - Each challenge is cut into as many `depth`-bit indices as its 192 bits hold, lowest bits first.
    /// - Each index then takes its stratum: its top bits are replaced by the stratum's.
    /// - Indices are neither sorted nor deduplicated.
    fn sample_queries(&mut self, depth: usize, count: usize) -> Vec<Self::Query>;

    /// Each query's row of the oracle committed at `root`, a tree of `2^depth` leaves, authenticated by its path.
    ///
    /// - A leaf image is `leaf_words` words, its first `leaf_words - row_words` zero.
    /// - A row is the image's last `row_words` words, in the order of `queries`.
    ///
    /// # Errors
    ///
    /// Returns an error on a missing or unauthenticated opening.
    fn open_rows(
        &mut self,
        root: &Self::Root,
        depth: usize,
        queries: &[Self::Query],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<Self::K>>, TranscriptError>;

    /// `a * k + d`, for `a` and `d` in `E` and a word `k` of `K`.
    fn mul_k_add(&mut self, a: Self::E, k: Self::K, d: Self::E) -> Self::E;

    /// The element of `E` with these limbs, lowest first.
    fn e_of_limbs(&mut self, limbs: [Self::K; 3]) -> Self::E;

    /// A query's index as a point: the element of `K`, embedded in `E`, whose bits are the index's.
    fn query_point(&mut self, query: &Self::Query) -> Self::E;
}

impl<A: Arith<E = F192> + Hashing> OpeningVerifier for VerifierState<'_, A> {
    type Root = Hash;
    type K = F64;
    type Query = usize;

    fn next_root(&mut self) -> Result<Hash, TranscriptError> {
        Receiver::next_root(self)
    }

    fn sample_queries(&mut self, depth: usize, count: usize) -> Vec<usize> {
        sample_queries_ordered(self, 1 << depth, count)
    }

    fn open_rows(
        &mut self,
        root: &Hash,
        depth: usize,
        queries: &[usize],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<F64>>, TranscriptError> {
        let mut rows = self.next_merkle_batch(root, 1 << depth, queries, row_words, leaf_words)?;
        for row in &mut rows {
            row.drain(..leaf_words - row_words);
        }
        Ok(rows)
    }

    fn mul_k_add(&mut self, a: F192, k: F64, d: F192) -> F192 {
        self.mul_const_add(a, F192::from(k), d)
    }

    fn e_of_limbs(&mut self, limbs: [F64; 3]) -> F192 {
        F192::new(limbs[0].0, limbs[1].0, limbs[2].0)
    }

    fn query_point(&mut self, query: &usize) -> F192 {
        F192::new(*query as u64, 0, 0)
    }
}
