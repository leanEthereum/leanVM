//! What the opening's verifier reads beyond scalars: roots, queries and opened rows.
//!
//! The same verifier code runs natively and as its replay in rows of the recursion machine.
//!
//! - Natively a root is a digest, a query an index, and a committed word a `K` value.
//! - In rows they are the wires holding them, and an opened row is authenticated by hash rows.

use crate::merkle::{Hash, Openings, PrunedMerklePaths, sorted_unique};
use crate::whir::sample_queries;
use fiat_shamir::arith::{Arith, PublicMle, Stage, Verifier};
use fiat_shamir::{TranscriptContext, TranscriptError, VerifierState};
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

    /// Copy the exact context without changing the transcript.
    fn context(&mut self) -> TranscriptContext<Self::K, Self::Root>;

    /// A zero word for canonical padding when a context is packed into a record frame.
    fn zero_k(&mut self) -> Self::K;

    /// Check two raw commitment roots are equal.
    ///
    /// # Errors
    ///
    /// Returns [`crate::whir::WhirError::CommitmentMismatch`] when the native roots differ.
    fn ensure_root_eq(&mut self, actual: Self::Root, expected: Self::Root) -> Result<(), crate::whir::WhirError>;

    /// The next commitment's root, bound into the transcript.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the proof.
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

impl OpeningVerifier for VerifierState<'_> {
    type Root = Hash;
    type K = F64;
    type Query = usize;

    fn context(&mut self) -> TranscriptContext<F64, Hash> {
        Self::context(self)
    }

    fn zero_k(&mut self) -> F64 {
        F64::ZERO
    }

    fn ensure_root_eq(&mut self, actual: Hash, expected: Hash) -> Result<(), crate::whir::WhirError> {
        if actual == expected {
            Ok(())
        } else {
            Err(crate::whir::WhirError::CommitmentMismatch)
        }
    }

    fn next_root(&mut self) -> Result<Hash, TranscriptError> {
        self.prover_message()
    }

    fn sample_queries(&mut self, depth: usize, count: usize) -> Vec<usize> {
        sample_queries(self, depth, count)
    }

    fn open_rows(
        &mut self,
        root: &Hash,
        depth: usize,
        queries: &[usize],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<F64>>, TranscriptError> {
        open_rows_native(self, root, depth, queries, row_words, leaf_words)
    }

    fn mul_k_add(&mut self, a: F192, k: F64, d: F192) -> F192 {
        a.mul_base(k) + d
    }

    fn e_of_limbs(&mut self, limbs: [F64; 3]) -> F192 {
        F192::new(limbs[0].0, limbs[1].0, limbs[2].0)
    }

    fn query_point(&mut self, query: &usize) -> F192 {
        F192::new(*query as u64, 0, 0)
    }
}

/// The native [`OpeningVerifier::open_rows`]: authenticate the next hint's paths, then each opening's row.
fn open_rows_native(
    vs: &mut VerifierState<'_>,
    root: &Hash,
    depth: usize,
    queries: &[usize],
    row_words: usize,
    leaf_words: usize,
) -> Result<Vec<Vec<F64>>, TranscriptError> {
    let openings = authenticate(vs, root, depth, queries, row_words, leaf_words)?;
    Ok(openings.rows(row_words))
}

/// Read the next hint as Merkle paths and authenticate them against `root`: each query's opening, in query order.
fn authenticate(
    vs: &mut VerifierState<'_>,
    root: &Hash,
    depth: usize,
    queries: &[usize],
    row_words: usize,
    leaf_words: usize,
) -> Result<Openings, TranscriptError> {
    // The hint holds one row per distinct query, which the verifier counts itself.
    let distinct = sorted_unique(queries).len();
    vs.prover_hint_with(|hint| {
        let paths = PrunedMerklePaths::from_hint(hint, distinct, row_words)?;
        paths.open(root, 1 << depth, queries, row_words, leaf_words)
    })
}

/// A native verifier that keeps every opening it authenticates, for a recursive verifier to hash.
///
/// The recursive verifier then reads the openings rather than decoding and hashing the hints again.
pub struct Recording<'a> {
    /// The transcript the proof is read from.
    vs: VerifierState<'a>,
    /// Every phase's openings, in transcript order.
    openings: Vec<Openings>,
}

impl<'a> Recording<'a> {
    /// A recording verifier over a transcript.
    #[must_use]
    pub const fn new(vs: VerifierState<'a>) -> Self {
        Self {
            vs,
            openings: Vec::new(),
        }
    }

    /// The transcript the proof is read from.
    pub const fn transcript(&mut self) -> &mut VerifierState<'a> {
        &mut self.vs
    }

    /// Every phase's openings, in transcript order.
    #[must_use]
    pub fn into_openings(self) -> Vec<Openings> {
        self.openings
    }
}

impl Arith for Recording<'_> {
    type E = F192;

    fn constant(&mut self, c: F192) -> F192 {
        self.vs.constant(c)
    }

    fn mul_add(&mut self, a: F192, b: F192, d: F192) -> F192 {
        self.vs.mul_add(a, b, d)
    }

    fn add(&mut self, a: F192, d: F192) -> F192 {
        self.vs.add(a, d)
    }

    fn mul_const_add(&mut self, a: F192, c: F192, d: F192) -> F192 {
        self.vs.mul_const_add(a, c, d)
    }

    fn inv(&mut self, a: F192) -> F192 {
        self.vs.inv(a)
    }

    fn frobenius2(&mut self, a: F192) -> F192 {
        self.vs.frobenius2(a)
    }
}

impl PublicMle for Recording<'_> {
    fn public_mle(&mut self, values: &[F64], point: &[F192]) -> F192 {
        self.vs.public_mle(values, point)
    }
}

impl Verifier for Recording<'_> {
    fn prover_message(&mut self) -> Result<F192, TranscriptError> {
        Verifier::prover_message(&mut self.vs)
    }

    fn verifier_message(&mut self) -> F192 {
        Verifier::verifier_message(&mut self.vs)
    }

    fn check_pow(&mut self, bits: u32) -> Result<(), TranscriptError> {
        self.vs.check_pow(bits)
    }

    fn ensure_eq<Er>(&mut self, a: F192, b: F192, err: impl FnOnce() -> Er) -> Result<(), Er> {
        self.vs.ensure_eq(a, b, err)
    }

    fn check_eof(&mut self) -> Result<(), TranscriptError> {
        self.vs.check_eof()
    }

    fn begin_scope(&mut self, stage: Stage) {
        self.vs.begin_scope(stage);
    }

    fn end_scope(&mut self) {
        self.vs.end_scope();
    }

    fn set_hidden(&mut self, hidden: bool) {
        self.vs.set_hidden(hidden);
    }

    fn is_hidden(&self) -> bool {
        self.vs.is_hidden()
    }
}

impl OpeningVerifier for Recording<'_> {
    type Root = Hash;
    type K = F64;
    type Query = usize;

    fn context(&mut self) -> TranscriptContext<F64, Hash> {
        self.vs.context()
    }

    fn zero_k(&mut self) -> F64 {
        self.vs.zero_k()
    }

    fn ensure_root_eq(&mut self, actual: Hash, expected: Hash) -> Result<(), crate::whir::WhirError> {
        self.vs.ensure_root_eq(actual, expected)
    }

    fn next_root(&mut self) -> Result<Hash, TranscriptError> {
        self.vs.next_root()
    }

    fn sample_queries(&mut self, depth: usize, count: usize) -> Vec<usize> {
        self.vs.sample_queries(depth, count)
    }

    fn open_rows(
        &mut self,
        root: &Hash,
        depth: usize,
        queries: &[usize],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<F64>>, TranscriptError> {
        // Authenticate as the plain verifier does, then keep the openings.
        let openings = authenticate(&mut self.vs, root, depth, queries, row_words, leaf_words)?;
        let rows = openings.rows(row_words);
        self.openings.push(openings);
        Ok(rows)
    }

    fn mul_k_add(&mut self, a: F192, k: F64, d: F192) -> F192 {
        self.vs.mul_k_add(a, k, d)
    }

    fn e_of_limbs(&mut self, limbs: [F64; 3]) -> F192 {
        self.vs.e_of_limbs(limbs)
    }

    fn query_point(&mut self, query: &usize) -> F192 {
        self.vs.query_point(query)
    }
}
