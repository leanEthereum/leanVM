//! Recursive proofs of leanXMSS and leanSPHINCS signature claims and LeanDA blob well-formedness.
//! One bytecode (`guests/lean_ethereum.py`) serves every node of an aggregation tree.
//!
//! A node verifies `n_raw_lean_xmss` leanXMSS signatures, `n_raw_lean_sphincs` leanSPHINCS
//! signatures and `n_children` sub-proofs **of this same bytecode**, and
//! by default publishes the sorted deduplicated union of their signer sets. A claim
//! of either scheme is a `(pubkey, message)` pair; a leanXMSS signature carries its own
//! leaf index, which the statement does not record. Coverage is what carries the
//! security claim: a write-once slot per declared claim, written once by each raw
//! signature and each child claim, plus a final count, so every declared claim is
//! backed by a real signature or a verified child.
//!
//! Those slots are one contiguous region per scheme, so the one range check a write
//! already needs also keeps a signature off the other scheme's declared claims: that
//! is what makes the published split mean which scheme verified which claim, at
//! every level of the tree.
//!
//! A duplicate slot sits outside the prefix the digest hashes, so a claim in one is
//! covered and not published. `aggregate`'s `declare` rests on that. A slot holds
//! four cells, the pubkey and its message, so the guest reads each signature's message
//! out of the slot it verifies.
//!
//! The bytecode is compiled to a fixed point on its own size
//! ([`unified_guest`]): the recursion placeholders depend on the inner bytecode
//! size, and here the inner bytecode is this one. Its digest does not need a
//! fixed point, riding the statement instead of the code.
//!
//! Three fixed polynomials (the stacked bytecode and flock's `A0`/`B0`) are too
//! big to evaluate in-circuit, so each node exports one deferred claim on each
//! and batches its children's carried claims with the fresh ones its
//! verifications raise (`doc/leanvm/main.tex` §Deferred evaluation claims). Only
//! the root's are discharged natively, by [`EthereumProof::verify`].
//!
//! `gen_verify` derives the guest's whole witness for a child from the real
//! `cpu::layout` of the inner program and the summary the `verifier` crate
//! reads out of the child's proof, so there is no hand-mirrored copy of the
//! protocol to drift.

use bincode::Options as _;
use pcs::whir::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use lean_compiler::{compile, parse_with_replacements};
use lean_da::{BLOB_SYMBOLS, CELL_SYMBOLS, CELLS_PER_ROW, CODEWORD_SYMBOLS};
pub use lean_da::{DA_LOG_CELL, DA_LOG_K, DA_MAX_ROWS};
use leanvm_core::cpu::{Program, ProveError, from_scalar, prove, public_input_bytes, scalar_proof, to_scalar};
use leanvm_core::leaf::{Block, Coord};
use leanvm_core::tables::N_TABLES;
use leanvm_core::transcript::FiatShamirState;
use primitives::field::{F64, F192, G, g_pow};
use primitives::multilinear::mle_eval_par;
use signatures::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use signatures::{lean_sphincs, lean_xmss};

use signatures::lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};

/// One leanXMSS claim: a pubkey, and the message it signed at whatever leaf index its
/// signature carries.
pub type LeanXmssClaim = (LeanXmssPublicKey, lean_xmss::Message);

/// One leanSPHINCS claim: a pubkey, and the message it signed.
pub type LeanSphincsClaim = (LeanSphincsPublicKey, lean_sphincs::Message);

/// Why the guest reads every `q_flock` slot claim's instance point off `chi`: a
/// virtual value column is referenced only by its own table's bus blocks, which
/// the table sumcheck settles, so no framework block can raise one at `zeta`.
const VALCOL_FRAMEWORK: &str = "a framework block must not reference a virtual value column";
const RECURSION_AGG_LABEL: &[u8] = b"leanvm/recursion-aggregation/v1";

/// The most earlier aggregates one [`aggregate`] call can take, so the arity of
/// an aggregation tree.
pub const MAX_RECURSIONS: usize = 16;

/// Exclusive cap on coverage slots: signatures of both schemes and DA roots,
/// including duplicates and omitted claims. Exactly this many is already too many.
///
/// It is where the coverage indices' range check has to sit to stay below
/// `2^MIN_LOG_MEM`, so the bound means the same at every announced memory size.
/// The guest checks it against a COMPILE-TIME bound, so raising it past
/// `2^MIN_LOG_MEM` fails the build rather than weakening the index bound.
pub const MAX_KEYS: usize = 1 << 16;

/// Maximum number of LeanDA roots in one statement, including inherited and direct roots.
pub const MAX_DA_ROOTS: usize = 16;
const _: () = assert!(MAX_DA_ROOTS < MAX_KEYS);

/// Blocks the guest absorbs per loop frame when it hashes a declared list, and so
/// how many share one byte-counter base (`doc/leanvm` §Byte counters for a hash of
/// runtime length). Larger amortizes the base's bit decomposition over more blocks
/// and costs bytecode in the tail's dispatch arms; the split it induces is what
/// [`signers_split`] hands the guest.
const SIGNERS_WINDOW: usize = 32;
// The counter split is a bit split: a window's base is `64·SIGNERS_WINDOW·q`, which
// has to be a power of two for its bits to sit clear of the window's own offsets.
const _: () = assert!(SIGNERS_WINDOW.is_power_of_two());

/// The window bound the guest range-checks its hinted window count against. A
/// range check takes a COUNT (`assert log(x) < k` bounds the exponent by `k`), so
/// this has to cover the most windows a list can hold, which a bit width would not:
/// under the bound every list still hashes, so the mistake shows up only past it.
const SIGNERS_MAX_WINDOWS: usize = MAX_KEYS / SIGNERS_WINDOW;
// A list is one block a claim, so at most MAX_KEYS blocks, of which the last is
// absorbed apart.
const _: () = assert!((MAX_KEYS - 1) / SIGNERS_WINDOW < SIGNERS_MAX_WINDOWS);
// The guest decomposes a count into SIGNERS_COUNT_BITS bits and shifts the result
// left to make a byte counter, so a count has to fit and the shift must not reduce.
const SIGNERS_COUNT_BITS: u32 = MAX_KEYS.ilog2();
const _: () = assert!(MAX_KEYS.is_power_of_two());
const _: () = assert!(SIGNERS_COUNT_BITS + 6 + SIGNERS_WINDOW.ilog2() <= 64);

// The guest bakes a bytecode claim's width from `N_TUPLE_BITS` while `bytecode_vars`
// reads it off the stacked table, which is `N_BYTECODE_SELECTORS` wide. Two constants
// that happen to agree: were they to drift, a leaf's claim point would be one length in
// the guest and another in the statement, and nothing else would notice.
const _: () = assert!(leanvm_core::leaf::N_TUPLE_BITS == leanvm_core::leaf::N_BYTECODE_SELECTORS);
// Both schemes' one-time keys go through the guest's one WOTS+C walk: the same chain
// length, digits dispatched DIGIT_GROUP at a time and the last chain alone, and the
// same address types (`primitives::hash`'s). A chain step's address leaves out the
// chain index in leanXMSS, where it follows the value.
const DIGIT_GROUP: usize = 3;
const _: () = assert!(lean_sphincs::W * lean_sphincs::V == 128 && lean_sphincs::V % DIGIT_GROUP == 1);
const _: () = assert!(lean_xmss::W == lean_sphincs::W && lean_xmss::V % DIGIT_GROUP == 1);
// leanXMSS's one-time leaf fills whole blocks, and a leaf index is the two layers'
// indices, which the guest decomposes into bits at once.
const _: () = assert!((2 + lean_xmss::V).is_multiple_of(4));
const _: () = assert!(lean_xmss::LOG_LIFETIME == 32);
// The guest takes the leanSPHINCS message digest's first cell as its sixteen
// codewords, and reads the index and what the digest leaves unused from the bits
// of the second, where it weighs each leaf and each WOTS key as one word of a
// 64-bit lane.
const _: () = assert!(lean_sphincs::DIGEST_WORD_BYTES == 16 && lean_sphincs::DIGEST_BITS <= 256);
const _: () = {
    let mut at = lean_sphincs::H;
    let mut k = 0;
    while k < lean_sphincs::FOREST_TREES * (1 + lean_sphincs::SUBTREES) {
        let bits = if k < lean_sphincs::FOREST_TREES {
            lean_sphincs::TREE_HEIGHT
        } else {
            lean_sphincs::SUBTREE_HEIGHT
        };
        assert!(at / 64 == (at + bits - 1) / 64);
        at += bits;
        k += 1;
    }
};
// The index and the bits after the last field are each read in one lane: the
// first, and the second up to the cell's end.
const _: () = assert!(lean_sphincs::H <= 64 && lean_sphincs::DIGEST_BITS - 128 >= 64);
// Its hashes of the one-time leaf and of the few-time key end on half a block.
const _: () = assert!(lean_sphincs::V.is_multiple_of(4) && (2 * lean_sphincs::FOREST_TREES).is_multiple_of(4));
// It hashes a tree leaf over two subtrees, and places the forest's positions in
// an address as `lean_sphincs::forest` packs them: the tree in 3 bits, then the leaf
// in 4, the subtree in 1, the key in 3 and the chain.
const _: () = assert!(lean_sphincs::SUBTREES == 2 && lean_sphincs::FOREST_TREES <= 1 << 3);
const _: () = assert!(lean_sphincs::TREE_HEIGHT <= 4 && lean_sphincs::SUBTREE_HEIGHT <= 3);

/// A count as the guest carries it: in the exponent, `g^n`.
fn count(n: usize) -> F192 {
    F192::new(g_pow(n).0, 0, 0)
}

/// A field element as the decimal `u128` literal the zkDSL parser accepts.
fn dsl_u128(value: F192) -> u128 {
    assert_eq!(value.c2, 0, "u128 DSL literal cannot encode the top F192 limb");
    (value.c0 as u128) | ((value.c1 as u128) << 64)
}

fn f192_literal(f: F192) -> String {
    format!("f192({},{},{})", f.c0, f.c1, f.c2)
}

/// Pack the Fiat-Shamir state's four K lanes as two canonical 128-bit VM cells.
fn pack_state(state: [F64; 4]) -> [F192; 2] {
    [
        F192::new(state[0].0, state[1].0, 0),
        F192::new(state[2].0, state[3].0, 0),
    ]
}

/// Pack a 32-byte Merkle node as the same canonical 128+128 cell pair used by
/// the VM's sole BLAKE2s representation.
fn pack_hash_state(hash: &[u8; 32]) -> [F192; 2] {
    let word_at = |offset: usize| u64::from_le_bytes(hash[offset..offset + 8].try_into().unwrap());
    [
        F192::new(word_at(0), word_at(8), 0),
        F192::new(word_at(16), word_at(24), 0),
    ]
}

/// A 16-byte native value as one canonical 128-bit cell.
fn pack_16_bytes(bytes: &[u8]) -> F192 {
    let word_at = |offset: usize| u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap());
    F192::new(word_at(0), word_at(8), 0)
}

/// A run of canonical 128-bit cells as the byte string BLAKE2s hashes: each cell
/// is its two low limbs, little-endian, which is the order the VM's compression
/// reads a memory cell in.
fn cell_bytes(cells: impl IntoIterator<Item = F192>) -> Vec<u8> {
    let mut bytes = Vec::new();
    for cell in cells {
        bytes.extend_from_slice(&cell.c0.to_le_bytes());
        bytes.extend_from_slice(&cell.c1.to_le_bytes());
    }
    bytes
}

/// How the guest splits a list's `n - 1` non-final blocks: whole windows, then the
/// tail. Its own product identity and range check pin both, so this only has to
/// agree with them (`claim_list_digest` in the guest). A list is never empty
/// here: both claim lists are guarded at the call, since the guest hashes an empty
/// one without a split at all.
fn signers_split(blocks: usize) -> Vec<F192> {
    assert!(blocks > 0, "an empty list has no window split");
    let leading = blocks - 1;
    vec![count(leading / SIGNERS_WINDOW), count(leading % SIGNERS_WINDOW)]
}

/// One scheme's declared claims under plain BLAKE2s: one 64-byte block per claim,
/// its pubkey then the message it signed, so the hashed string is exactly `64n` bytes
/// and an empty list hashes the empty string. The guest computes this same digest a
/// window of blocks at a time (`claim_list_digest`).
fn claim_list_digest(claims: impl IntoIterator<Item = [F192; 4]>) -> [F192; 2] {
    pack_hash_state(&primitives::hash::hash(&cell_bytes(claims.into_iter().flatten())))
}

/// A claim as the four cells the guest hashes and its verifier reads: the pubkey's
/// root and public parameter (`flatten`), then the message that pubkey signed.
fn claim_cells(pk: &[u8; 32], message: &[u8; 32]) -> [F192; 4] {
    [
        pack_16_bytes(&pk[..16]),
        pack_16_bytes(&pk[16..]),
        pack_16_bytes(&message[..16]),
        pack_16_bytes(&message[16..]),
    ]
}

fn lean_xmss_claim_cells((pk, message): &LeanXmssClaim) -> [F192; 4] {
    claim_cells(&pk.flatten(), message)
}

fn lean_sphincs_claim_cells((pk, message): &LeanSphincsClaim) -> [F192; 4] {
    claim_cells(&pk.flatten(), message)
}

/// The signer-set digest: plain BLAKE2s of the leanXMSS list's digest then the leanSPHINCS
/// list's, one 64-byte block (`main` in the guest). Each list digest binds its own
/// length through BLAKE2s's byte counter, so the pair binds both lists whole.
fn signers_hash(xmss_signers: &[LeanXmssClaim], lean_sphincs_signers: &[LeanSphincsClaim]) -> [F192; 2] {
    let xmss = claim_list_digest(xmss_signers.iter().map(lean_xmss_claim_cells));
    let lean_sphincs = claim_list_digest(lean_sphincs_signers.iter().map(lean_sphincs_claim_cells));
    pack_hash_state(&primitives::hash::hash(&cell_bytes([
        xmss[0],
        xmss[1],
        lean_sphincs[0],
        lean_sphincs[1],
    ])))
}

/// The claims on the three fixed polynomials that a node defers rather than
/// evaluating in-circuit: one point and value on the stacked bytecode, one point
/// and two values on flock's `A0`/`B0` (`doc/leanvm/main.tex` §Deferred
/// evaluation claims).
///
/// Only the points are transmitted; the values are derived from them on receipt,
/// so a prover that lies about a value changes the statement its proof has to
/// satisfy rather than the claim anyone checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeferredClaim {
    bytecode_point: Vec<F192>,
    bytecode_value: F192,
    matrix_point: Vec<F192>,
    matrix_a_value: F192,
    matrix_b_value: F192,
}

impl DeferredClaim {
    /// What a leaf defers: the all-zeros point on each polynomial, where the
    /// value is just the table's first entry.
    fn leaf() -> Self {
        Self::recompute(
            vec![F192::ZERO; bytecode_vars()],
            vec![F192::ZERO; 2 * flock::hash::K_LOG],
        )
        .expect("the all-zeros point has the right shape")
    }

    /// Evaluate the three fixed polynomials at `bytecode_point` / `matrix_point`, on the prover's field kernels and thread pool.
    fn recompute(bytecode_point: Vec<F192>, matrix_point: Vec<F192>) -> Result<Self, AggregateVerifyError> {
        let bytecode_at = |point: &[F192]| {
            let _span = tracing::info_span!("bytecode mle").entered();
            mle_eval_par(stacked_bytecode(), point)
        };
        let matrices_at = |point: &[F192]| {
            let _span = tracing::info_span!("matrix walk").entered();
            let (row, column) = point.split_at(flock::hash::K_LOG);
            let eq_r = pcs::whir::build_eq_table_ext(row);
            let eq_c = pcs::whir::build_eq_table_ext(column);
            flock::hash::bilinear_walk_pair(&eq_r, &eq_c)
        };
        Self::evaluate(bytecode_point, matrix_point, bytecode_at, matrices_at)
    }

    /// [`Self::recompute`] in the `verifier` crate: scalar and single threaded, what a received aggregate is checked with.
    fn recompute_scalar(bytecode_point: Vec<F192>, matrix_point: Vec<F192>) -> Result<Self, AggregateVerifyError> {
        let scalars = |point: &[F192]| point.iter().map(to_scalar).collect::<Vec<_>>();
        let bytecode_at = |point: &[F192]| {
            let _span = tracing::info_span!("bytecode mle").entered();
            let value = scalar_bytecode().evaluate(&scalars(point));
            from_scalar(value.expect("the point's length was checked"))
        };
        let matrices_at = |point: &[F192]| {
            let _span = tracing::info_span!("matrix walk").entered();
            let (a, b) = verifier::deferred::matrix_values(&scalars(point)).expect("the point's length was checked");
            (from_scalar(a), from_scalar(b))
        };
        Self::evaluate(bytecode_point, matrix_point, bytecode_at, matrices_at)
    }

    fn evaluate(
        bytecode_point: Vec<F192>,
        matrix_point: Vec<F192>,
        bytecode_at: impl FnOnce(&[F192]) -> F192,
        matrices_at: impl FnOnce(&[F192]) -> (F192, F192),
    ) -> Result<Self, AggregateVerifyError> {
        if bytecode_point.len() != bytecode_vars() || matrix_point.len() != 2 * flock::hash::K_LOG {
            return Err(AggregateVerifyError::MalformedClaim);
        }
        // Every leaf defers the all-zeros point, where the bytecode polynomial is
        // just its table's first entry. Still worth special-casing that half: the
        // general path is a pass over 2^23 entries, and a leaf is the aggregate
        // people verify most. The matrix half needs no special case, its walk
        // being O(circuit) either way.
        let zero_point = bytecode_point.iter().chain(&matrix_point).all(|x| *x == F192::ZERO);
        let bytecode_value = if zero_point {
            F192::from(stacked_bytecode()[0])
        } else {
            bytecode_at(&bytecode_point)
        };
        let (matrix_a_value, matrix_b_value) = matrices_at(&matrix_point);
        Ok(Self {
            bytecode_point,
            bytecode_value,
            matrix_point,
            matrix_a_value,
            matrix_b_value,
        })
    }

    /// The cells the statement digest absorbs, in the guest's `defer_stmt` order.
    fn cells(&self) -> Vec<F192> {
        let mut cells = self.bytecode_point.clone();
        cells.push(self.bytecode_value);
        cells.extend_from_slice(&self.matrix_point);
        cells.push(self.matrix_a_value);
        cells.push(self.matrix_b_value);
        cells
    }
}

/// The statement's fixed header, ahead of the deferred cells: the seed, the
/// signer-set digest (which itself binds both claim lists), and
/// the DA root-list digest. Fed to the guest as `STMT_HEADER`, so the two cannot drift.
const STATEMENT_HEADER: usize = 6;

/// A plain BLAKE2s over a lane stream, zero-filled to a whole 64-byte block:
/// what the guest gets by streaming four 128-bit cells a block.
fn lane_hash(lanes: impl Iterator<Item = u64>) -> [F192; 2] {
    let mut bytes: Vec<u8> = lanes.flat_map(u64::to_le_bytes).collect();
    bytes.resize(bytes.len().next_multiple_of(64), 0);
    pack_hash_state(&primitives::hash::hash(&bytes))
}

/// A node's public statement, hashed to the two words the VM publishes. The
/// guest's `statement_digest` computes exactly this, both for itself and when it
/// rebuilds a child's, which is what forces a whole tree onto one bytecode and
/// each child's claims, bound by the signer-set digest,
/// onto its parent's lists.
///
/// Fixed-length preimage, so a plain BLAKE2s, with no domain tag of its own: the
/// header leads with the environment digest, which binds this bytecode and
/// flock's R1CS and so already separates the preimage from every other use of
/// BLAKE2s here. The header is hashed as the canonical cells it already is (two
/// lanes each, whence the assert, the guest being unable to hash a third), then
/// all three lanes of each deferred cell.
fn statement_digest(signers_hash: [F192; 2], da_digest: [u8; 32], defer: &DeferredClaim) -> [F192; 2] {
    let seed = leanvm_core::cpu::fs_seed(unified_guest());
    let da_digest = pack_hash_state(&da_digest);
    let header = [
        seed[0],
        seed[1],
        signers_hash[0],
        signers_hash[1],
        da_digest[0],
        da_digest[1],
    ];
    assert_eq!(header.len(), STATEMENT_HEADER);
    let mut cells = defer.cells();
    if !cells.len().is_multiple_of(2) {
        cells.push(F192::ZERO); // the guest pairs the odd cell with a zero scalar
    }
    let head = header.iter().flat_map(|x| {
        assert_eq!(x.c2, 0, "a header value is a canonical cell");
        [x.c0, x.c1]
    });
    lane_hash(head.chain(cells.iter().flat_map(|x| [x.c0, x.c1, x.c2])))
}

/// The deferred-claim data the guest binds to the outer public input: the outer
/// verifier checks each claim natively (`doc/leanvm/main.tex` §Deferred evaluation claims;
/// n_rec = 1 forwards fresh claims without batching).
struct DeferredSubproof {
    public_input: [F192; 2],
    bytecode_row_point: Vec<F192>,
    bytecode_selector_point: Vec<F192>,
    bytecode_value: F192,
    matrix_a_coefficient: F192,
    skip_point: F192,
    zerocheck_row_point: Vec<F192>,
    lincheck_round_point: Vec<F192>,
    lincheck_terminal_values: Vec<F192>,
    matrix_claim: F192,
}

/// A proof that every `(pubkey, message)` in [`Self::xmss_signers`] is backed by a
/// valid leanXMSS signature, at a leaf index the statement does not record, and every
/// one in [`Self::lean_sphincs_signers`] by a valid leanSPHINCS signature. Each root in
/// [`Self::da_commitments`] also attests that the committed blob rows are valid Reed-Solomon codewords.
/// These claims can be established directly or carried from verified child proofs.
///
/// The two lists describe the signature claims and remain separate because the proof says which scheme
/// verified which claim (the module docs give the coverage argument). Until
/// [`Self::verify`] returns `Ok` they are claims, not attestation, and even then
/// the messages are the prover's, so a caller that reads either list
/// as attestation of something must compare it against what it expected.
///
/// **Neither length counts signers, only claims.** One pubkey may appear under several
/// messages, so a committee threshold has to count distinct pubkeys itself.
#[derive(Clone, Debug)]
pub struct EthereumProof {
    /// Strictly sorted and deduplicated on the whole `(pubkey, message)` pair. The
    /// claims of both schemes together are strictly fewer than [`MAX_KEYS`].
    xmss_signers: Vec<LeanXmssClaim>,
    /// Strictly sorted and deduplicated on the whole `(pubkey, message)` pair.
    lean_sphincs_signers: Vec<LeanSphincsClaim>,
    /// Strictly sorted LeanDA roots. Their list digest rides the public statement.
    da_roots: Vec<[u8; 32]>,
    /// What this aggregate defers to whoever discharges it: its parent, in
    /// circuit, or [`Self::verify`], natively.
    defer: DeferredClaim,
    proof: leanvm_core::cpu::Proof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregateVerifyError {
    /// The signer set is unsorted, holds a duplicate, or has [`MAX_KEYS`] claims or more.
    MalformedSignerSet,
    /// The DA root list is unsorted, holds duplicates, or exceeds [`MAX_DA_ROOTS`].
    MalformedDaCommitments,
    /// A deferred claim's point has the wrong number of coordinates.
    MalformedClaim,
    /// The bytes are not a valid encoding of an aggregate.
    MalformedEncoding,
    /// The snark did not verify. From [`aggregate`], which does not verify its children, it means a child's proof could not be read, or its flock claim on the fixed matrices is false.
    Snark(verifier::VerifierError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregationError {
    /// A child's statement is malformed, its proof cannot be walked, or the claim it raises on flock's matrices is false. The walk fails on most tampering, the openings having to sit at query positions the transcript draws, so a statement that does not match the proof usually lands here as a Merkle opening error. Any other child that does not verify is a [`Self::ProofError`]: the guest's run fails on it.
    InvalidChild(AggregateVerifyError),
    /// No signature claims or DA roots to publish.
    Empty,
    /// A declared claim is not one the contributions cover. A claim is a pubkey and a
    /// message, so another message is another claim.
    NotCovered,
    /// A raw signature's randomness does not decode to a target-sum encoding,
    /// so there is no witness to build for it.
    MalformedRawSignature,
    /// More than [`MAX_RECURSIONS`] children, or [`MAX_KEYS`] signers or more
    /// once the duplicate slots are counted, or more than [`MAX_DA_ROOTS`] DA roots.
    TooLarge,
    /// The payload has a partial row or exceeds [`DA_MAX_ROWS`].
    InvalidBlobSize { symbols: usize },
    /// A requested DA commitment is absent from the children and the direct blob check.
    BlobNotCovered,
    /// `log_inv_rate` is outside the range the WHIR configuration accepts.
    InvalidRate { log_inv_rate: usize },
    /// A child's committed witness falls outside the opening arms the guest was
    /// compiled with. Small aggregates are padded up to the floor, so this means
    /// a child too big: more signatures than one node can hold.
    ChildOutOfRange { log_committed: usize },
    /// The prover made no proof of this node: the guest rejects its input (a
    /// forged signature fails the guest's run), or its witness is larger than any
    /// verifier accepts (too many signatures for one proof).
    ProofError(ProveError),
}

impl std::fmt::Display for AggregateVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedSignerSet => write!(f, "malformed signer set"),
            Self::MalformedDaCommitments => write!(f, "malformed DA commitment list"),
            Self::MalformedClaim => write!(f, "malformed deferred claim"),
            Self::MalformedEncoding => write!(f, "not a valid aggregate encoding"),
            Self::Snark(e) => write!(f, "the snark did not verify: {e}"),
        }
    }
}

impl std::error::Error for AggregateVerifyError {}

impl std::fmt::Display for AggregationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidChild(_) => write!(f, "invalid child aggregate"),
            Self::Empty => write!(f, "no signature claims or DA roots to publish"),
            Self::NotCovered => write!(f, "a declared claim is not covered by the children and raw signatures"),
            Self::MalformedRawSignature => write!(f, "a raw signature does not decode to a target-sum encoding"),
            Self::TooLarge => {
                write!(f, "too many children, signature claims, or DA roots")
            }
            Self::InvalidBlobSize { symbols } => {
                write!(
                    f,
                    "{symbols} blob symbols do not form 1..={DA_MAX_ROWS} rows of {} symbols",
                    1 << DA_LOG_K
                )
            }
            Self::BlobNotCovered => write!(f, "the requested blob commitment is not carried by any child"),
            Self::InvalidRate { log_inv_rate } => {
                write!(
                    f,
                    "log_inv_rate {log_inv_rate} is outside {}..={}",
                    MIN_LOG_INV_RATE, MAX_LOG_INV_RATE
                )
            }
            Self::ChildOutOfRange { log_committed } => {
                write!(
                    f,
                    "a child commits 2^{log_committed} words, outside the guest's opening arms"
                )
            }
            Self::ProofError(e) => write!(f, "proving failed: {e}"),
        }
    }
}

impl std::error::Error for AggregationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidChild(e) => Some(e),
            Self::ProofError(e) => Some(e),
            _ => None,
        }
    }
}

/// Everything but the signer set, which a receiver may already hold.
type WireCore = (Vec<[u8; 32]>, Vec<F192>, Vec<F192>, leanvm_core::cpu::Proof);

/// Signature claims grouped by scheme, each a `(pubkey, message)` pair.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SignatureClaims {
    pub xmss: Vec<LeanXmssClaim>,
    pub lean_sphincs: Vec<LeanSphincsClaim>,
}

/// Exactly the claims to publish. Empty lists publish no claims of that kind.
#[derive(Clone, Copy)]
pub struct ClaimSelection<'a> {
    pub signatures: &'a SignatureClaims,
    pub da_commitments: &'a [[u8; 32]],
}

/// The wire encoding: bincode's fixed-width integers, as the free functions use,
/// but rejecting trailing bytes, which they do not. Without that an accepted
/// aggregate has unboundedly many encodings, so anything downstream that dedupes
/// or indexes on the serialized bytes can be made to see one aggregate as many.
fn wire() -> impl bincode::Options {
    bincode::DefaultOptions::new().with_fixint_encoding()
}

/// Reject a signer set that the coverage argument does not cover: strict sorting
/// within each list is what stops one claim being counted many times, so each
/// list's length is a count of distinct `(pubkey, message)` claims. Either list may be
/// empty; both may be empty for a blob proof. [`MAX_KEYS`] is exclusive here, as in
/// the guest.
fn check_signer_set(
    xmss_signers: &[LeanXmssClaim],
    lean_sphincs_signers: &[LeanSphincsClaim],
) -> Result<(), AggregateVerifyError> {
    if xmss_signers.len() + lean_sphincs_signers.len() >= MAX_KEYS
        || !xmss_signers.windows(2).all(|w| w[0] < w[1])
        || !lean_sphincs_signers.windows(2).all(|w| w[0] < w[1])
    {
        return Err(AggregateVerifyError::MalformedSignerSet);
    }
    Ok(())
}

fn check_da_roots(roots: &[[u8; 32]]) -> Result<(), AggregateVerifyError> {
    if roots.len() > MAX_DA_ROOTS || roots.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(AggregateVerifyError::MalformedDaCommitments);
    }
    Ok(())
}

fn da_claim_cells(root: &[u8; 32]) -> Vec<F192> {
    let vector_hash = lean_da::vector_digest(&lean_da::membership_vector(root));
    [pack_hash_state(root), pack_hash_state(&vector_hash)].concat()
}

fn da_list_digest(roots: &[[u8; 32]]) -> [u8; 32] {
    // Recompute vector hashes from the roots, including when verifying a received proof.
    // Trusting prover-supplied hashes would let zero weights certify any matrix.
    let cells = roots.iter().flat_map(da_claim_cells);
    primitives::hash::hash(&cell_bytes(cells))
}

impl EthereumProof {
    /// This aggregate's own public statement, as the VM publishes it.
    fn public_input(&self) -> [F192; 2] {
        statement_digest(
            signers_hash(&self.xmss_signers, &self.lean_sphincs_signers),
            self.da_commitments_digest(),
            &self.defer,
        )
    }

    /// Strictly sorted and deduplicated on the whole `(pubkey, message)` pair. May be
    /// empty, including in a blob-only proof.
    pub fn xmss_signers(&self) -> &[LeanXmssClaim] {
        &self.xmss_signers
    }

    /// Strictly sorted and deduplicated on the whole `(pubkey, message)` pair.
    pub fn lean_sphincs_signers(&self) -> &[LeanSphincsClaim] {
        &self.lean_sphincs_signers
    }

    /// Strictly sorted, distinct LeanDA roots proved directly or inherited from children.
    /// An empty list makes no blob claim.
    pub fn da_commitments(&self) -> &[[u8; 32]] {
        &self.da_roots
    }

    /// BLAKE2s of the concatenated `(root, vector hash)` pairs, or of empty input.
    /// Each vector hash is derived from its root outside the SNARK.
    /// This digest is bound into the public statement.
    pub fn da_commitments_digest(&self) -> [u8; 32] {
        da_list_digest(&self.da_roots)
    }

    /// The declared claims, as many as the coverage table's declared slots.
    ///
    /// NOT a count of distinct signers: a pubkey of either scheme may hold several
    /// claims, one per message it signed. A caller that wants signers has to
    /// deduplicate by pubkey itself.
    pub fn num_signature_claims(&self) -> usize {
        self.xmss_signers.len() + self.lean_sphincs_signers.len()
    }

    /// The wire format: the signer set, the DA root list, the two deferred points,
    /// and the VM proof. The claim *values* are not transmitted;
    /// [`Self::from_bytes`] recomputes them, so there is nothing to lie about.
    pub fn to_bytes(&self) -> Vec<u8> {
        wire()
            .serialize(&((&self.xmss_signers, &self.lean_sphincs_signers), self.core()))
            .expect("an aggregate serializes")
    }

    /// Parsing does NOT verify: the proof is untouched, only shapes are checked.
    /// Call [`Self::verify`] before believing any of it.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, AggregateVerifyError> {
        let (claims, core): (SignatureClaims, WireCore) = wire()
            .deserialize(bytes)
            .map_err(|_| AggregateVerifyError::MalformedEncoding)?;
        Self::from_parts(claims, core)
    }

    /// Without the signer set, for a receiver that already knows it. A set other
    /// than the one aggregated fails verification.
    pub fn to_bytes_without_pubkeys(&self) -> Vec<u8> {
        wire().serialize(&self.core()).expect("an aggregate serializes")
    }

    /// The underlying VM proof, whose serialized size the CLI's benchmarks report.
    pub fn proof(&self) -> &leanvm_core::cpu::Proof {
        &self.proof
    }

    /// Inverse of [`Self::to_bytes_without_pubkeys`], verifying nothing either.
    pub fn from_bytes_without_pubkeys(bytes: &[u8], claims: SignatureClaims) -> Result<Self, AggregateVerifyError> {
        Self::from_parts(
            claims,
            wire()
                .deserialize(bytes)
                .map_err(|_| AggregateVerifyError::MalformedEncoding)?,
        )
    }

    fn core(&self) -> (&[[u8; 32]], &[F192], &[F192], &leanvm_core::cpu::Proof) {
        (
            &self.da_roots,
            &self.defer.bytecode_point,
            &self.defer.matrix_point,
            &self.proof,
        )
    }

    fn from_parts(claims: SignatureClaims, core: WireCore) -> Result<Self, AggregateVerifyError> {
        let SignatureClaims {
            xmss: xmss_signers,
            lean_sphincs: lean_sphincs_signers,
        } = claims;
        let (da_roots, bytecode_point, matrix_point, proof) = core;
        // Cheap rejections first. `recompute_scalar` below is a pass over the whole stacked
        // bytecode plus a walk of the BLAKE2s circuit, on points a peer chose, so
        // anything decidable without it has to be decided before it.
        check_signer_set(&xmss_signers, &lean_sphincs_signers)?;
        check_da_roots(&da_roots)?;
        Ok(Self {
            xmss_signers,
            lean_sphincs_signers,
            da_roots,
            // The wire carries no value, only the points to derive it from.
            defer: DeferredClaim::recompute_scalar(bytecode_point, matrix_point)?,
            proof,
        })
    }

    /// Verify the aggregate's internal consistency: the signer set and DA root list are well
    /// formed, the three deferred fixed-polynomial claims hold at their
    /// transmitted points, and the VM proof satisfies the statement built from
    /// all of it.
    ///
    /// This says "every `(pubkey, message)` in `xmss_signers` is a valid leanXMSS signature,
    /// and every one in `lean_sphincs_signers` a valid leanSPHINCS signature", with the
    /// messages chosen by whoever produced the aggregate: an aggregate over the same
    /// pubkeys under different messages verifies just as well. Which leaf index each
    /// leanXMSS signature used is not part of the claim. A caller that
    /// expects particular pairs has to check the two lists against them. Every root in
    /// [`Self::da_commitments`] also attests to a well-formed blob matrix; callers check
    /// that this list contains the commitments they require.
    ///
    /// Every field operation, the proof check and its Merkle hashing run in the `verifier` crate: one thread, no explicit SIMD.
    pub fn verify(&self) -> Result<(), AggregateVerifyError> {
        check_signer_set(&self.xmss_signers, &self.lean_sphincs_signers)?;
        check_da_roots(&self.da_roots)?;
        // Discharging the deferred claims IS recomputing them: their values have
        // to be the true evaluations, or the recursion below proves nothing about
        // the fixed polynomials.
        let _s = tracing::info_span!("Recompute deferred claims").entered();
        let defer =
            DeferredClaim::recompute_scalar(self.defer.bytecode_point.clone(), self.defer.matrix_point.clone())?;
        drop(_s);
        if defer != self.defer {
            return Err(AggregateVerifyError::MalformedClaim);
        }
        let _s = tracing::info_span!("Statement digest").entered();
        let pi = statement_digest(
            signers_hash(&self.xmss_signers, &self.lean_sphincs_signers),
            verifier::da::list_digest(&self.da_roots),
            &self.defer,
        );
        drop(_s);
        verifier::verify_execution(scalar_bytecode(), &public_input_bytes(&pi), &scalar_proof(&self.proof))
            .map(|_| ())
            .map_err(AggregateVerifyError::Snark)
    }
}

/// [`stacked_bytecode`] as the `verifier` crate takes it, hashed once: what [`EthereumProof::verify`] checks proofs against, and [`aggregate`] reads its children with.
fn scalar_bytecode() -> &'static verifier::Bytecode {
    static BYTECODE: std::sync::OnceLock<verifier::Bytecode> = std::sync::OnceLock::new();
    BYTECODE.get_or_init(|| {
        let words: Vec<u64> = stacked_bytecode().iter().map(|word| word.0).collect();
        verifier::Bytecode::new(&words)
    })
}

/// The stacked bytecode polynomial of the aggregation guest: the one fixed
/// table every node's bytecode claims are about. Cached, because verification
/// evaluates it and building it walks the whole program.
fn stacked_bytecode() -> &'static [F64] {
    static TABLE: std::sync::OnceLock<Vec<F64>> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| leanvm_core::cpu::layout::bytecode_table(&unified_guest().prog))
}

/// The slots of the stacked bytecode that are not structurally zero.
///
/// Eight encoding columns sit inside sixteen stacking slots, so half the
/// table is zero and contributes nothing to any round of the batching sumcheck.
/// Read off the table rather than from the column count, so an all-zero column
/// at the edge only ever shrinks the window.
fn bytecode_window() -> Range<usize> {
    static WINDOW: std::sync::OnceLock<Range<usize>> = std::sync::OnceLock::new();
    WINDOW
        .get_or_init(|| {
            let table = stacked_bytecode();
            let kbc = bytecode_vars() - leanvm_core::leaf::N_BYTECODE_SELECTORS;
            let live = |s: usize| table[s << kbc..(s + 1) << kbc].iter().any(|v| *v != F64::ZERO);
            let slots = 1 << leanvm_core::leaf::N_BYTECODE_SELECTORS;
            let start = (0..slots).find(|&s| live(s)).expect("the bytecode is not all zero");
            let end = (0..slots).rfind(|&s| live(s)).expect("the bytecode is not all zero") + 1;
            start..end
        })
        .clone()
}

/// One round message against a K-valued table: `bt` is the bytecode itself, so
/// the products are base-by-extension.
fn round_msg_base(bytecode: &[F64], weights: &[F192]) -> (F192, F192) {
    let half = bytecode.len() / 2;
    let term = |i: usize| {
        let (bytecode_0, bytecode_1) = (bytecode[2 * i], bytecode[2 * i + 1]);
        let (weight_0, weight_1) = (weights[2 * i], weights[2 * i + 1]);
        (
            weight_1.mul_base(bytecode_1),
            (weight_0 + weight_1).mul_base(bytecode_0 + bytecode_1),
        )
    };
    if half >= PAR_MIN {
        parallel::fold_reduce(
            half,
            || (F192::ZERO, F192::ZERO),
            |acc: &mut (F192, F192), i| {
                let (x, y) = term(i);
                acc.0 += x;
                acc.1 += y;
            },
            |a: (F192, F192), b: (F192, F192)| (a.0 + b.0, a.1 + b.1),
        )
    } else {
        (0..half).fold((F192::ZERO, F192::ZERO), |acc, i| {
            let (x, y) = term(i);
            (acc.0 + x, acc.1 + y)
        })
    }
}

/// The first fold of a K-valued table, which is where it becomes extension-valued.
fn fold_lsb_base(table: &[F64], challenge: F192) -> Vec<F192> {
    parallel::map_collect(table.len() / 2, |i| {
        let (left, right) = (table[2 * i], table[2 * i + 1]);
        F192::from(left) + challenge.mul_base(left + right)
    })
}

/// `Σ_t γ_t · eq(points[t], (r_row, ·))` over the stacking slots, once the row
/// variables are bound. A closed form, so the row rounds never have to carry the
/// slot half of a `2^kbcv` weight table.
fn slot_weights(points: &[Vec<F192>], lambdas: &[F192], r_row: &[F192], kbc: usize) -> Vec<F192> {
    let slots = leanvm_core::leaf::N_BYTECODE_SELECTORS;
    let mut weights = vec![F192::ZERO; 1 << slots];
    for (point, &lambda) in points.iter().zip(lambdas) {
        let row_weight: F192 = (0..kbc).fold(lambda, |acc, k| acc * (F192::ONE + point[k] + r_row[k]));
        for (slot, weight) in weights.iter_mut().enumerate() {
            let slot_weight = (0..slots).fold(row_weight, |acc, bit| {
                let coordinate = point[kbc + bit];
                acc * if (slot >> bit) & 1 == 1 {
                    coordinate
                } else {
                    F192::ONE + coordinate
                }
            });
            *weight += slot_weight;
        }
    }
    weights
}

/// Variables of a bytecode claim's point: the log row count plus the stacking
/// selectors.
fn bytecode_vars() -> usize {
    stacked_bytecode().len().trailing_zeros() as usize
}

/// Below this a parallel dispatch costs more than the loop it replaces.
const PAR_MIN: usize = 1 << 16;

fn fold_lsb(table: &mut Vec<F192>, challenge: F192) {
    let half = table.len() / 2;
    if half >= PAR_MIN {
        let source: &[F192] = table;
        let folded = parallel::map_collect(half, |i| {
            let (left, right) = (source[2 * i], source[2 * i + 1]);
            left + challenge * (left + right)
        });
        *table = folded;
        return;
    }
    for i in 0..half {
        table[i] = table[2 * i] + challenge * (table[2 * i] + table[2 * i + 1]);
    }
    table.truncate(half);
}

/// Compressed product-sumcheck round message over γ-weighted table pairs:
/// (g1, g∞) with g0 recovered from the running claim.
fn round_msg(pairs: &[(&[F192], &[F192], F192)]) -> (F192, F192) {
    let (mut g1, mut gi) = (F192::ZERO, F192::ZERO);
    for &(u, m, lambda) in pairs {
        let half = u.len() / 2;
        let term = |i: usize| {
            let (u0, u1) = (u[2 * i], u[2 * i + 1]);
            let (m0, m1) = (m[2 * i], m[2 * i + 1]);
            (u1 * m1, (u0 + u1) * (m0 + m1))
        };
        let (a1, ai) = if half >= PAR_MIN {
            parallel::fold_reduce(
                half,
                || (F192::ZERO, F192::ZERO),
                |acc: &mut (F192, F192), i| {
                    let (x, y) = term(i);
                    acc.0 += x;
                    acc.1 += y;
                },
                |a: (F192, F192), b: (F192, F192)| (a.0 + b.0, a.1 + b.1),
            )
        } else {
            (0..half).fold((F192::ZERO, F192::ZERO), |acc, i| {
                let (x, y) = term(i);
                (acc.0 + x, acc.1 + y)
            })
        };
        g1 += lambda * a1;
        gi += lambda * ai;
    }
    (g1, gi)
}

/// One round of a batching sumcheck, in the transcript order the guest mirrors
/// word for word: observe `(g1, g_inf)`, squeeze the fold challenge, record
/// both, and advance the running claim through the compressed round polynomial.
/// Returns the challenge, which the caller folds its tables with.
fn absorb_round(
    transcript: &mut FiatShamirState,
    messages: &mut Vec<F192>,
    challenges: &mut Vec<F192>,
    claim: &mut F192,
    (g1, gi): (F192, F192),
) -> F192 {
    transcript.observe(g1);
    transcript.observe(gi);
    let challenge = transcript.sample();
    messages.extend([g1, gi]);
    challenges.push(challenge);
    let g0 = *claim + g1;
    let c1 = g0 + g1 + gi;
    *claim = (gi * challenge + c1) * challenge + g0;
    challenge
}

/// `Σ_t γ_t · eq(points[t], ·)`, over the `active` window of `2^vars` entries.
///
/// Each point splits in half; the halves' eq tables are small and serial, and
/// the full table is their outer product, one fused multiply-add per entry,
/// parallel over the high index. Materializing a `2^vars` eq table per claim and
/// summing them is the same arithmetic done twice, serially.
fn weighted_eq_table(points: &[Vec<F192>], lambdas: &[F192], vars: usize, active: Range<usize>) -> Vec<F192> {
    let lo_vars = vars / 2;
    let lo_len = 1usize << lo_vars;
    debug_assert!(active.start.is_multiple_of(lo_len) && active.end.is_multiple_of(lo_len));
    // `build_eq_table_ext` is LSB-first, so the low variables index the low bits
    // and entry `hi * lo_len + lo` is `eq_lo[lo] * eq_hi[hi]`.
    let halves: Vec<(Vec<F192>, Vec<F192>)> = points
        .iter()
        .zip(lambdas)
        .map(|(point, &lambda)| {
            let low = pcs::whir::build_eq_table_ext(&point[..lo_vars]);
            let mut high = pcs::whir::build_eq_table_ext(&point[lo_vars..]);
            high.iter_mut().for_each(|weight| *weight *= lambda);
            (low, high)
        })
        .collect();
    let mut weights = vec![F192::ZERO; active.len()];
    let first = active.start / lo_len;
    parallel::chunks_mut(&mut weights, lo_len, |high_index, chunk| {
        for (low, high) in &halves {
            let scale = high[first + high_index];
            for (output, &low_weight) in chunk.iter_mut().zip(low) {
                *output += scale * low_weight;
            }
        }
    });
    weights
}

/// Mirror the guest's `aggregate_claims` transcript and prove the two batching
/// sumchecks: dense for the bytecode, two-phase sparse for the matrices.
///
/// Each child brings two claims per fixed polynomial: the one it deferred and
/// the fresh one its verification raised. They differ
/// only in the weight they enter with. A fresh matrix claim carries flock's
/// zerocheck/lincheck structure; a carried one is a plain point, so its weight
/// is an eq table on each side. Returns the guest hints and the single claim
/// per polynomial they reduce to.
///
/// Fails on a child whose fresh matrix claim is false. That value is the one batched here that is read out of a
/// child's proof unchecked; every other is an evaluation this prover made, of the bytecode in `gen_verify` and of
/// a carried claim in `DeferredClaim::evaluate`, so the remaining asserts guard against a prover bug only.
fn aggregate_deferred_claims(
    subproofs: &[DeferredSubproof],
    carried_claims: &[&DeferredClaim],
) -> Result<(SubHints, DeferredClaim), AggregateVerifyError> {
    let child_count = subproofs.len();
    assert_eq!(child_count, carried_claims.len(), "one carried claim per child");
    let kbcv = bytecode_vars();
    let klog = flock::hash::K_LOG;

    let mut transcript = FiatShamirState::from_label(RECURSION_AGG_LABEL);
    transcript.observe(count(child_count));
    for (subproof, carried) in subproofs.iter().zip(carried_claims) {
        transcript.observe(subproof.public_input[0]);
        transcript.observe(subproof.public_input[1]);
        for &value in &subproof.bytecode_row_point {
            transcript.observe(value);
        }
        for &value in &subproof.bytecode_selector_point {
            transcript.observe(value);
        }
        transcript.observe(subproof.bytecode_value);
        transcript.observe(subproof.matrix_a_coefficient);
        transcript.observe(subproof.skip_point);
        for &value in &subproof.zerocheck_row_point {
            transcript.observe(value);
        }
        for &value in &subproof.lincheck_round_point {
            transcript.observe(value);
        }
        for &value in &subproof.lincheck_terminal_values {
            transcript.observe(value);
        }
        transcript.observe(subproof.matrix_claim);
        for value in carried.cells() {
            transcript.observe(value);
        }
    }

    let _span = tracing::info_span!("Bytecode batch", vars = kbcv).entered();
    let gbc: Vec<F192> = (0..2 * child_count).map(|_| transcript.sample()).collect();
    let points: Vec<Vec<F192>> = subproofs
        .iter()
        .zip(carried_claims)
        .flat_map(|(subproof, carried)| {
            [
                subproof
                    .bytecode_row_point
                    .iter()
                    .chain(&subproof.bytecode_selector_point)
                    .copied()
                    .collect::<Vec<_>>(),
                carried.bytecode_point.clone(),
            ]
        })
        .collect();
    let values: Vec<F192> = subproofs
        .iter()
        .zip(carried_claims)
        .flat_map(|(subproof, carried)| [subproof.bytecode_value, carried.bytecode_value])
        .collect();
    let mut brun: F192 = (0..2 * child_count)
        .map(|index| gbc[index] * values[index])
        .fold(F192::ZERO, |acc, value| acc + value);
    let mut bscr = Vec::new();
    let mut r_bc = Vec::new();
    // The row variables, over the populated slot window only: the rest of the
    // stacked table is structurally zero and contributes nothing to any round
    // message, and folding LSB-first pairs entries within a slot, so the window's
    // blocks stay aligned all the way down.
    let n_slots = 1 << leanvm_core::leaf::N_BYTECODE_SELECTORS;
    let slot_window = bytecode_window();
    let kbc = kbcv - leanvm_core::leaf::N_BYTECODE_SELECTORS;
    let mut wt = weighted_eq_table(
        &points,
        &gbc,
        kbcv,
        (slot_window.start << kbc)..(slot_window.end << kbc),
    );
    // Round zero runs against the K-valued table itself: the bytecode never needs
    // to exist as `2^kbcv` extension elements (three times the memory traffic),
    // and base-by-extension is cheaper than extension-by-extension. Every later
    // round is extension-valued anyway.
    let bc = &stacked_bytecode()[(slot_window.start << kbc)..(slot_window.end << kbc)];
    let mut bt = {
        let msg = round_msg_base(bc, &wt);
        let r = absorb_round(&mut transcript, &mut bscr, &mut r_bc, &mut brun, msg);
        let folded = fold_lsb_base(bc, r);
        fold_lsb(&mut wt, r);
        folded
    };
    for _ in 1..kbc {
        let msg = round_msg(&[(&bt, &wt, F192::ONE)]);
        let r = absorb_round(&mut transcript, &mut bscr, &mut r_bc, &mut brun, msg);
        fold_lsb(&mut bt, r);
        fold_lsb(&mut wt, r);
    }
    // The slot variables. The window has folded to one entry per populated slot;
    // put those back among the zeros. The weights come from a closed form rather
    // than from having carried a `2^kbcv` table through the rows.
    let mut bt_slots = vec![F192::ZERO; n_slots];
    bt_slots[slot_window.clone()].copy_from_slice(&bt);
    let wt_slots = slot_weights(&points, &gbc, &r_bc, kbc);
    let (mut bt, mut wt) = (bt_slots, wt_slots);
    for _ in 0..leanvm_core::leaf::N_BYTECODE_SELECTORS {
        let msg = round_msg(&[(&bt, &wt, F192::ONE)]);
        let r = absorb_round(&mut transcript, &mut bscr, &mut r_bc, &mut brun, msg);
        fold_lsb(&mut bt, r);
        fold_lsb(&mut wt, r);
    }
    let v_bc = bt[0];
    assert_eq!(brun, v_bc * wt[0], "bytecode sumcheck terminal");

    drop(_span);
    let _span = tracing::info_span!("Matrix batch").entered();
    // One group per claim: the row weights, the column weights, and the
    // coefficient each matrix enters with. Downstream is shape-blind.
    let mut us: Vec<Vec<F192>> = Vec::with_capacity(2 * child_count);
    let mut ws: Vec<Vec<F192>> = Vec::with_capacity(2 * child_count);
    let mut ga: Vec<F192> = Vec::with_capacity(2 * child_count);
    let mut gb: Vec<F192> = Vec::with_capacity(2 * child_count);
    let mut mrun = F192::ZERO;
    for (subproof, carried) in subproofs.iter().zip(carried_claims) {
        let (gf, cga, cgb) = (transcript.sample(), transcript.sample(), transcript.sample());
        us.push(flock::lincheck::build_quirky_eq_table(
            subproof.skip_point,
            &subproof.zerocheck_row_point,
            6,
        ));
        ws.push(
            (0..1usize << klog)
                .map(|col| {
                    let mut w = subproof.lincheck_terminal_values[col & 63];
                    for (j, &rj) in subproof.lincheck_round_point.iter().enumerate() {
                        let bit = (col >> (klog - 1 - j)) & 1;
                        w *= if bit == 1 { rj } else { F192::ONE + rj };
                    }
                    w
                })
                .collect(),
        );
        ga.push(gf);
        gb.push(gf * subproof.matrix_a_coefficient);
        us.push(pcs::whir::build_eq_table_ext(&carried.matrix_point[..klog]));
        ws.push(pcs::whir::build_eq_table_ext(&carried.matrix_point[klog..]));
        ga.push(cga);
        gb.push(cgb);
        mrun += gf * subproof.matrix_claim + cga * carried.matrix_a_value + cgb * carried.matrix_b_value;
    }
    let _cols = tracing::info_span!("Contract columns").entered();
    // One forward walk of the circuit per claim yields that claim's two row
    // tables `(A_0 w, B_0 w)` directly, in O(circuit): no matrix, and no pass
    // over the ~89M nonzeros. A before B, the order `ga`/`gb` index.
    let mut ms: Vec<Vec<F192>> = Vec::with_capacity(2 * ws.len());
    for w in &ws {
        let (ra, rb) = flock::hash::row_values_walk(w);
        ms.push(ra);
        ms.push(rb);
    }
    drop(_cols);
    // sanity: every carried claim really is the bilinear form over the matrices.
    #[cfg(debug_assertions)]
    for (child, carried) in carried_claims.iter().enumerate() {
        let t = 2 * child + 1;
        let form = |m: &[F192]| {
            m.iter()
                .zip(&us[t])
                .map(|(&m, &u)| m * u)
                .fold(F192::ZERO, |a, x| a + x)
        };
        assert_eq!(
            (form(&ms[2 * t]), form(&ms[2 * t + 1])),
            (carried.matrix_a_value, carried.matrix_b_value),
            "carried matrix claim"
        );
    }
    let mut mscr = Vec::new();
    let mut r_row = Vec::new();
    let _rounds = tracing::info_span!("Row rounds").entered();
    for _ in 0..klog {
        let pairs: Vec<(&[F192], &[F192], F192)> = (0..2 * child_count)
            .flat_map(|t| {
                [
                    (&us[t][..], &ms[2 * t][..], ga[t]),
                    (&us[t][..], &ms[2 * t + 1][..], gb[t]),
                ]
            })
            .collect();
        let msg = round_msg(&pairs);
        let r = absorb_round(&mut transcript, &mut mscr, &mut r_row, &mut mrun, msg);
        for u in us.iter_mut() {
            fold_lsb(u, r);
        }
        for m in ms.iter_mut() {
            fold_lsb(m, r);
        }
    }
    drop(_rounds);
    let eq_rstar = pcs::whir::build_eq_table_ext(&r_row);
    let _rows = tracing::info_span!("Contract rows").entered();
    // `A_0ᵀ eq` and `B_0ᵀ eq` are the column marginals, which the circuit walks
    // backwards (`gf2`'s `back_*`) in O(circuit).
    let (mut acol, mut bcol) = flock::hash::marginal_walk_pair(&eq_rstar);
    drop(_rows);
    let mut wa = vec![F192::ZERO; 1 << klog];
    let mut wb = vec![F192::ZERO; 1 << klog];
    for t in 0..2 * child_count {
        let (sa, sb) = (ga[t] * us[t][0], gb[t] * us[t][0]);
        for j in 0..1 << klog {
            wa[j] += sa * ws[t][j];
            wb[j] += sb * ws[t][j];
        }
    }
    let mut r_col = Vec::new();
    for _ in 0..klog {
        let pairs: Vec<(&[F192], &[F192], F192)> = vec![(&acol, &wa, F192::ONE), (&bcol, &wb, F192::ONE)];
        let msg = round_msg(&pairs);
        let r = absorb_round(&mut transcript, &mut mscr, &mut r_col, &mut mrun, msg);
        for tb in [&mut acol, &mut bcol, &mut wa, &mut wb] {
            fold_lsb(tb, r);
        }
    }
    let (v_a, v_b) = (acol[0], bcol[0]);
    // A fresh matrix claim is the bilinear form exactly when its child's lincheck closes, which the replay did
    // not check. A false one leaves this honest sumcheck off by its error.
    if mrun != v_a * wa[0] + v_b * wb[0] {
        return Err(AggregateVerifyError::Snark(
            verifier::VerifierError::FlockLincheckTerminal,
        ));
    }
    // The guest reaches the same two weights by a succinct formula rather than by
    // folding these tables, and nothing else compares the two: the aggregation
    // layer has no other implementation the way the snark's verifier does. So this runs
    // unconditionally (it is O(n) against a 2^28 sumcheck), and it compares the
    // weights COMPONENT-WISE. Checking only the combination `v_a·wa + v_b·wb`
    // would let two correlated errors through.
    {
        let eqr = pcs::whir::build_eq_table_ext(&r_row[..6]);
        let eqc = pcs::whir::build_eq_table_ext(&r_col[..6]);
        let (mut wam, mut wbm) = (F192::ZERO, F192::ZERO);
        for (t, (subproof, carried)) in subproofs.iter().zip(carried_claims).enumerate() {
            let lam = primitives::multilinear::lagrange_weights_naive(6, subproof.skip_point);
            let mut urow: F192 = (0..64).map(|i| lam[i] * eqr[i]).fold(F192::ZERO, |a, x| a + x);
            for (k, &z) in subproof.zerocheck_row_point.iter().enumerate() {
                urow *= F192::ONE + z + r_row[6 + k];
            }
            let mut wcol: F192 = (0..64)
                .map(|i| subproof.lincheck_terminal_values[i] * eqc[i])
                .fold(F192::ZERO, |a, x| a + x);
            for (j, &rj) in subproof.lincheck_round_point.iter().enumerate() {
                wcol *= F192::ONE + rj + r_col[klog - 1 - j];
            }
            let fresh = urow * wcol;
            let mut plain = F192::ONE;
            for (k, &p) in carried.matrix_point.iter().enumerate() {
                let r = if k < klog { r_row[k] } else { r_col[k - klog] };
                plain *= F192::ONE + p + r;
            }
            wam += ga[2 * t] * fresh + ga[2 * t + 1] * plain;
            wbm += gb[2 * t] * fresh + gb[2 * t + 1] * plain;
        }
        assert_eq!(wa[0], wam, "guest row-weight formula for A0");
        assert_eq!(wb[0], wbm, "guest row-weight formula for B0");
    }

    drop(_span);
    let hints = vec![
        ("bc_sumcheck_msgs", bscr),
        ("mat_sumcheck_msgs", mscr),
        ("bc_star_hint", vec![v_bc]),
        ("mat_stars_hint", vec![v_a, v_b]),
    ];
    Ok((
        hints,
        DeferredClaim {
            bytecode_point: r_bc,
            bytecode_value: v_bc,
            matrix_point: r_row.iter().chain(&r_col).copied().collect(),
            matrix_a_value: v_a,
            matrix_b_value: v_b,
        },
    ))
}
/// The verifier-side WHIR config for one committed size and rate, plus the
/// query packing derived from it. The hint builder needs it for the real
/// opening and the placeholder map for every candidate size, so it lives here:
/// a candidate whose shape differed from the real one would compile a guest
/// that cannot open the proof it is handed.
struct WhirShape {
    config: pcs::whir::ProverConfig,
    levels: pcs::whir::LevelShapes,
    /// Merkle tree depth per level.
    depth: Vec<usize>,
    /// Query positions carried by one squeezed F192 word, per level.
    per_squeeze: Vec<usize>,
}

fn whir_shape(mu: usize, log_inv_rate: usize) -> WhirShape {
    let config = pcs::whir::config_for_rate(mu, log_inv_rate).expect("stacked whir config");
    let levels = config.level_shapes(mu);
    let depth: Vec<usize> = levels.block_len.iter().map(|b| b.trailing_zeros() as usize).collect();
    let per_squeeze = depth.iter().map(|&d| 192 / d).collect();
    WhirShape {
        config,
        levels,
        depth,
        per_squeeze,
    }
}

fn merkle_cap_depth(queries: usize, depth: usize) -> usize {
    (queries.next_power_of_two().ilog2() as usize).min(depth)
}

/// The BLAKE2s table's virtual value columns, in `hash_flock::SLOTS` order.
fn blake2s_value_columns() -> Vec<usize> {
    let base = leanvm_core::cpu::schema().base[5];
    leanvm_core::tables::BLAKE2S_VALUE_COLS
        .iter()
        .map(|&c| base + c)
        .collect()
}

/// One entry of the guest's claim pool.
enum ClaimSite {
    /// A committed column read by a framework bus block.
    Framework { column: usize },
    /// A table column; `is_virtual` marks the q_flock-backed value
    /// columns, whose claim is a strided slot rather than a plain column.
    TableColumn { column: usize, is_virtual: bool },
    /// One of the three PI memory limbs (MEM_LO, MEM_HI, MEM_TOP).
    MemoryLimb { column: usize },
}

/// The guest's `COORD_KIND_*` code for a coordinate (`guests/lean_ethereum.py`),
/// shared by its `COORD_TYPE` and `TERM_TYPE` arrays.
fn coord_kind(c: &Coord) -> usize {
    match c {
        Coord::Const(_) => 0,
        Coord::Col(_) => 1,
        Coord::GCol(..) => 2,
        Coord::Index => 3,
        Coord::Public(_) => 4,
        Coord::Prod(..) => 5,
        Coord::Sum(..) => 6,
    }
}

/// The `K` scalar a coordinate carries beside its columns: the constant itself,
/// or the `g^k` a `GCol`/`Prod` scales by. Zero for every other kind.
fn coord_scale(c: &Coord) -> F192 {
    match c {
        Coord::Const(v) => F192::new(v.0, 0, 0),
        Coord::GCol(_, k) | Coord::Prod(_, _, k) => F192::new(g_pow(*k as usize).0, 0, 0),
        _ => F192::ZERO,
    }
}

/// Flatten one table-block coordinate into the guest's term arrays, in local
/// column indices. A [`Coord::Sum`]'s children are its terms; every other kind is
/// one term. `Index`/`Public` never reach a table block.
fn push_coord_terms(c: &Coord, base: usize, terms: &mut Vec<Term>) {
    let (column_a, column_b) = match c {
        Coord::Const(_) => (0, 0),
        Coord::Col(i) | Coord::GCol(i, _) => (*i - base, 0),
        Coord::Prod(i, j, _) => (*i - base, *j - base),
        Coord::Sum(cs) => {
            for c in cs {
                push_coord_terms(c, base, terms);
            }
            return;
        }
        Coord::Index | Coord::Public(_) => unreachable!("a table's bus block carries no virtual coordinate"),
    };
    terms.push(Term {
        kind: coord_kind(c),
        constant: dsl_u128(coord_scale(c)),
        column_a,
        column_b,
    });
}

/// Visit the claim pool in the exact order the guest indexes it: the framework
/// bus claims (deduped by `(column, kappa)`, as `leaf.rs` pools them), then every
/// table's committed columns, then the PI memory triple. The placeholder map's
/// claim descriptors follow this order.
fn walk_claims(layout: &leanvm_core::cpu::Layout, kbc: usize, mut visit: impl FnMut(ClaimSite)) {
    let sides: [&[Block]; 3] = [&layout.push, &layout.pull, &layout.count];
    let valcols = blake2s_value_columns();
    // Only the framework blocks raise claims: a table's coords are settled inside
    // the table sumcheck.
    let is_framework: Vec<bool> = leanvm_core::cpu::block_kappa_sources(kbc)
        .into_iter()
        .map(|(src, _)| src < 2)
        .collect();
    let mut seen: std::collections::HashSet<(usize, usize)> = Default::default();
    let mut bi = 0usize;
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            let framework = is_framework[bi];
            bi += 1;
            if !framework {
                continue;
            }
            for c in &blk.coords {
                if let Coord::Col(i) | Coord::GCol(i, _) = c {
                    if !seen.insert((*i, blk.kappa)) {
                        continue; // deduped: pooled once at its first occurrence
                    }
                    assert!(!valcols.contains(i), "{VALCOL_FRAMEWORK}");
                    visit(ClaimSite::Framework { column: *i });
                }
            }
        }
    }
    let sch = leanvm_core::cpu::schema();
    for (t, table) in leanvm_core::tables::tables().iter().enumerate() {
        for c in 0..table.n_committed_columns() {
            let column = sch.base[t] + c;
            visit(ClaimSite::TableColumn {
                column,
                is_virtual: layout.placements[column].is_virtual(),
            });
        }
    }
    for &column in &[
        leanvm_core::cpu::MEM_LO,
        leanvm_core::cpu::MEM_HI,
        leanvm_core::cpu::MEM_TOP,
    ] {
        visit(ClaimSite::MemoryLimb { column });
    }
}

/// Config + hints for the recursion guest (`guests/lean_ethereum.py`), built
/// from the REAL `cpu::layout` of the inner program and the `summary` the
/// `verifier` crate read out of the child's proof, whose scalars are
/// `proof_stream` (zero hand-mirroring drift). Nothing here says the child
/// verifies: the guest's run does.
fn gen_verify(
    program: &Program,
    public_input: [F192; 2],
    proof_stream: &[F192],
    summary: verifier::Summary,
) -> Result<(SubHints, DeferredSubproof), AggregationError> {
    let layout = leanvm_core::cpu::layout(
        &program.prog,
        summary.log_memory,
        std::array::from_fn(|t| summary.table_rows[t] as usize),
        public_input,
    );
    let sides: [&[Block]; 3] = [&layout.push, &layout.pull, &layout.count];
    let side_layouts = sides.map(leanvm_core::leaf::layout);
    // The guest holds one opening arm per candidate committed size, so a child
    // outside that window has no arm to dispatch to. `min_log_committed` keeps
    // every aggregate above the low end, leaving only the ceiling reachable.
    // Fixed capacities: every buffer/stride placeholder is a global cap so
    // the placeholder map is SHAPE-INDEPENDENT (the definition of generic). A
    // child that verifies and has an arm fits them; one that does not need not.
    let fits = side_layouts.iter().all(|side| side.mu <= MU_CAP) && proof_stream.len() <= STREAM_CAP;
    if !(MU_MIN..=MU_MAX).contains(&layout.shape.mu) || !fits {
        return Err(AggregationError::ChildOutOfRange {
            log_committed: layout.shape.mu,
        });
    }

    // ---- typed extraction: the proof's stream + the verifier's summary ----
    let scalars = |values: &[verifier::E]| -> Vec<F192> { values.iter().copied().map(from_scalar).collect() };
    // Push and pull share the bytecode point.
    let bytecode_point = scalars(&summary.bytecode_point);
    let kbc = bytecode_point.len() - leanvm_core::leaf::N_BYTECODE_SELECTORS;

    let taus = layout.taus;
    // Flock replay data, all named struct fields.
    let lcrounds = flock::hash::K_LOG - 6;
    let flock = &summary.flock;
    let zcf = [from_scalar(flock.v_a), from_scalar(flock.v_b)];
    let zc_z = from_scalar(flock.z_skip);
    let zchi = scalars(&flock.chi);
    let lc_alpha = from_scalar(flock.alpha);
    let lrr = scalars(&flock.round_challenges);

    // ---- the stacked opening: config + the opening summary ----
    let stack = whir_shape(layout.shape.mu, summary.log_inv_rate);

    // flock's reduction ends at `flock_stream_end`, where the WHIR opening's own
    // scalars start: its last 64 scalars are lincheck's `z_partial` (which the
    // summary already carries as `s`), immediately preceded by the
    // coefficient PAIRS of the `lcrounds` lincheck rounds: the linear one is not
    // sent, the running claim fixing it.
    let ns = summary.flock_stream_end;
    let lcr = &proof_stream[ns - 64 - 2 * lcrounds..ns - 64];
    let lcz = scalars(&flock.s);

    // matpart = the deferred weighted matrix evaluation: the lincheck running
    // claim minus (= plus, char 2) the const-pin and c-claim contributions,
    // which every verifier weighs by α³ and α².
    let lc_sq = lc_alpha.square();
    let lc_beta = lc_sq * lc_alpha;
    let mut lrun = zcf[0] + lc_alpha * zcf[1] + lc_sq * from_scalar(flock.v_c) + lc_beta;
    for i in 0..lcrounds {
        let (c0, c2) = (lcr[2 * i], lcr[2 * i + 1]);
        lrun = primitives::multilinear::poly_eval(&[c0, lrun + c2, c2], lrr[i]);
    }
    let mut pinw = lc_beta;
    for (j, &rv) in lrr.iter().enumerate() {
        let bit = (flock::hash::Z_CONST_POS >> (flock::hash::K_LOG - 1 - j)) & 1;
        pinw *= if bit == 1 { rv } else { F192::ONE + rv };
    }
    pinw *= lcz[flock::hash::Z_CONST_POS % 64];
    // The c term: eq(ρ_in, ρ'_in) times the φ8-Lagrange combination of the 64
    // slices, ρ'_in being the lincheck challenges read back in coordinate order.
    let mut c_point_eq = F192::ONE;
    for (t, &rin) in zchi[..lcrounds].iter().enumerate() {
        c_point_eq *= F192::ONE + rin + lrr[lcrounds - 1 - t];
    }
    let c_slice_value = primitives::multilinear::lagrange_weights_naive(6, zc_z)
        .iter()
        .zip(&lcz)
        .fold(F192::ZERO, |acc, (&w, &s)| acc + w * s);
    let matpart = lrun + pinw + lc_sq * c_point_eq * c_slice_value;

    // ---- hints ----
    // The program's whole share of a bytecode leaf: ONE value, the stacked
    // polynomial at (ζ_lo, α⃗), the slot coordinates of the claim's own point being
    // the fingerprint challenges (§sec:e2e-bc). The summary carries the point
    // only, so this is the prover's own evaluation, `program` being the guest.
    let bytecode_value = mle_eval_par(stacked_bytecode(), &bytecode_point);
    let bcv = vec![bytecode_value];

    // ---- per-sub HINT data (the placeholder map is built once, elsewhere) ----
    // Per side, the packing order read straight off `leaf::layout`'s offsets:
    // sort_order[side_base + rank] = g^{global index of the rank-r block}. The
    // guest certifies it is the native verifier's order (descending kappa, then
    // ascending index) before deriving offsets from it.
    let mut sort_order: Vec<F192> = Vec::new();
    let mut gbase = 0usize;
    for (s, blocks) in sides.iter().enumerate() {
        let mut order: Vec<usize> = (0..blocks.len()).collect();
        order.sort_by_key(|&i| side_layouts[s].offsets[i]);
        for &i in &order {
            sort_order.push(F192::new(g_pow(gbase + i).0, 0, 0)); // g^{global block index}
        }
        gbase += blocks.len();
    }
    // The stacked commitment uses witness::placements_of: committed columns
    // sorted by descending kappa, then by their native column index. Transport
    // compact committed-column indices; the guest certifies the permutation,
    // ordering, and accumulated offsets before using them as claim selectors.
    let col_sources = leanvm_core::cpu::col_kappa_sources(kbc);
    let committed_globals: Vec<usize> = col_sources
        .iter()
        .enumerate()
        .filter_map(|(i, source)| source.map(|_| i))
        .collect();
    let mut compact_col = vec![usize::MAX; col_sources.len()];
    for (compact, &global) in committed_globals.iter().enumerate() {
        compact_col[global] = compact;
    }
    let mut col_order = committed_globals;
    col_order.sort_by_key(|&global| layout.placements[global].offset);
    let col_sort_order: Vec<F192> = col_order
        .iter()
        .map(|&global| F192::new(g_pow(compact_col[global]).0, 0, 0))
        .collect();

    // ---- Phase E2 hints (the stacked WHIR opening) ----
    // Share the upper Merkle tree across queries. Unknown, unused subtrees stay
    // opaque; the guest authenticates every cap leaf a query reaches.
    let mut query_hints = Vec::new();
    let (mut caps, mut cap_active) = (Vec::new(), Vec::new());
    let mut openings = summary.merkle_paths.iter();
    for (&queries, &depth) in stack.config.queries.iter().zip(&stack.depth) {
        let cap_depth = merkle_cap_depth(queries, depth);
        let n = 1 << cap_depth;
        let path_depth = depth - cap_depth;
        let mut nodes = vec![[0u8; 32]; 2 * n];
        let mut active = vec![F192::ZERO; n];
        for opening in openings.by_ref().take(queries) {
            query_hints.push((
                "merkle_leaf_rows",
                opening.leaf.iter().map(|x| F192::new(x.0, 0, 0)).collect(),
            ));
            let mut path_children = Vec::with_capacity(4 * path_depth);
            let bytes: Vec<_> = opening.leaf.iter().flat_map(|x| x.to_bytes()).collect();
            let mut node = pcs::merkle::hash_leaf(&bytes);
            let mut index = (1 << depth) + opening.leaf_index as usize;
            for (height, sibling) in opening.siblings.iter().enumerate() {
                if height >= path_depth {
                    nodes[index] = node;
                    nodes[index ^ 1] = *sibling;
                    active[index >> 1] = F192::ONE;
                }
                let (left, right) = if index & 1 == 0 {
                    (&node, sibling)
                } else {
                    (sibling, &node)
                };
                if height < path_depth {
                    path_children.extend(pack_hash_state(left));
                    path_children.extend(pack_hash_state(right));
                }
                node = pcs::merkle::hash_pair(left, right);
                index >>= 1;
            }
            nodes[1] = node;
            query_hints.push(("merkle_children", path_children));
        }
        caps.extend(nodes.iter().flat_map(pack_hash_state));
        cap_active.extend(active);
    }
    let mut bytecode_row_point = bytecode_point;
    let bytecode_selector_point = bytecode_row_point.split_off(kbc);
    let deferred = DeferredSubproof {
        public_input,
        bytecode_row_point,
        bytecode_selector_point,
        bytecode_value,
        matrix_a_coefficient: lc_alpha,
        skip_point: zc_z,
        zerocheck_row_point: zchi[..lcrounds].to_vec(),
        lincheck_round_point: lrr,
        lincheck_terminal_values: lcz,
        matrix_claim: matpart,
    };

    let mut hints = vec![
        ("stream", {
            // The guest replays the WHIR opening off the same stream the native
            // verifier reads: every transmitted scalar (sumcheck messages, level
            // roots, OOD claims, grind nonces, `yr`) is already there in protocol
            // order, so there is nothing to reassemble. The guest's `open_stacked`
            // picks it up at `msg_cursor = cursor`, which sits where the flock
            // reduction stopped; the ring-switch messages are struct-observed and
            // still do not advance that cursor.
            let mut stream = proof_stream.to_vec();
            stream.resize(STREAM_CAP, F192::ZERO);
            stream
        }),
        ("bytecode_val", bcv),
        ("matpart", vec![matpart]),
        ("merkle_caps", caps),
        ("merkle_cap_active", cap_active),
        // the table sumcheck's round count: max_t tau_t, certified in-guest as a
        // maximum (one of the taus, and dominating them all).
        (
            "zc_tau_max",
            vec![F192::new(g_pow(*taus.iter().max().unwrap()).0, 0, 0)],
        ),
        // Every table's log height, which the guest certifies against its row count.
        ("table_logs", taus.iter().map(|&t| count(t)).collect()),
        ("col_sort_order", col_sort_order),
        ("sort_order", sort_order),
    ];
    hints.extend(query_hints);
    Ok((hints, deferred))
}

/// The guest's stacked-size dispatch range: one `match_range` opening arm per
/// candidate `mu` in `MU_MIN..=MU_MAX` (mirrored by the soundness test's
/// residual-log cap).
const MU_MIN: usize = 22;
const MU_MAX: usize = leanvm_core::pcs::MAX_MU;

const _: () = assert!(MU_MIN >= leanvm_core::pcs::MIN_MU);

/// The guest's baked buffer caps, which `placeholder_map` compiles in and
/// `gen_verify` admits against: one definition, so a hinted shape can never
/// outgrow the buffer the guest was compiled with.
const MU_CAP: usize = 40;
const STREAM_CAP: usize = 8192;
/// Named hint entries for a single sub-proof, ordered within each stream.
type SubHints = Vec<(&'static str, Vec<F192>)>;

/// One `hint_witness` stream: a name and its entries, in the order the guest
/// pops them.
#[derive(Default)]
pub(crate) struct Hints(Vec<(String, Vec<Vec<F192>>)>);

#[cfg(test)]
thread_local! {
    /// The streams the last `aggregate` on this thread installed (`guest_diff`).
    static INSTALLED: std::cell::RefCell<Vec<(String, Vec<Vec<F192>>)>> = const { std::cell::RefCell::new(Vec::new()) };
}

impl Hints {
    fn push(&mut self, name: &str, entry: Vec<F192>) {
        match self.0.iter_mut().find(|(n, _)| n == name) {
            Some((_, entries)) => entries.push(entry),
            None => self.0.push((name.to_string(), vec![entry])),
        }
    }

    fn install(self, guest: &mut Program) {
        #[cfg(test)]
        INSTALLED.set(self.0.clone());
        for (name, entries) in self.0 {
            guest.set_witness(name, entries);
        }
    }
}

/// The coverage slot each write in the guest's coverage walk targets, in walk
/// order: the raw signatures first, then each child's claim lists.
///
/// The table is one contiguous region per scheme, each its declared claims followed
/// by its own duplicate slots:
///
/// | slots | holds |
/// | --- | --- |
/// | `[0, n_lean_xmss)` | the declared leanXMSS claims |
/// | `[n_lean_xmss, X)` | leanXMSS duplicate slots |
/// | `[X, X + n_lean_sphincs)` | the declared leanSPHINCS claims |
/// | `[X + n_lean_sphincs, n_total)` | leanSPHINCS duplicate slots |
///
/// A claim the declared set holds takes its slot there, one it does not takes a
/// fresh duplicate slot in the same region, so the walk hits every one of the
/// `n_total` slots exactly once. That bijection, enforced in-circuit by write-once
/// memory plus the final count, is what makes every declared claim covered by a real
/// signature or a verified child.
///
/// Keeping each region contiguous is what binds the scheme: the guest addresses
/// every writer as an offset into one region, bounded by that region's size, one
/// range check per write, so no signature can reach a claim of the other scheme.
struct Coverage {
    xmss: Region<LeanXmssClaim>,
    lean_sphincs: Region<LeanSphincsClaim>,
}

/// One scheme's region of the coverage table.
struct Region<K> {
    /// The declared claims, strictly sorted.
    signers: Vec<K>,
    dups: Vec<K>,
    /// The slot of each raw signature, in the order given.
    raw: Vec<usize>,
    /// Per child, the slot of each of its claims.
    children: Vec<Vec<usize>>,
}

impl<K: Ord + Clone> Region<K> {
    /// Declares the union of the raw claims and the children's, or exactly
    /// `declare`, which they must cover.
    fn plan<'a>(
        raw: &[K],
        children: impl Iterator<Item = &'a [K]> + Clone,
        declare: Option<&[K]>,
    ) -> Result<Self, AggregationError>
    where
        K: 'a,
    {
        let mut signers = raw.to_vec();
        for child in children.clone() {
            signers.extend_from_slice(child);
        }
        signers.sort();
        signers.dedup();
        if let Some(declare) = declare {
            let mut wanted: BTreeSet<&K> = declare.iter().collect();
            signers.retain(|claim| wanted.remove(claim));
            if !wanted.is_empty() {
                return Err(AggregationError::NotCovered);
            }
        }
        let mut claimed = vec![false; signers.len()];
        let mut dups = Vec::new();
        let raw = raw
            .iter()
            .map(|claim| take_slot(&signers, &mut claimed, &mut dups, claim))
            .collect();
        let children = children
            .map(|child| {
                child
                    .iter()
                    .map(|claim| take_slot(&signers, &mut claimed, &mut dups, claim))
                    .collect()
            })
            .collect();
        Ok(Self {
            signers,
            dups,
            raw,
            children,
        })
    }

    fn n_slots(&self) -> usize {
        self.signers.len() + self.dups.len()
    }
}

impl Coverage {
    fn n_total(&self) -> usize {
        self.xmss.n_slots() + self.lean_sphincs.n_slots()
    }
}

/// A claim takes its declared slot once; subsequent or omitted occurrences take
/// fresh slots outside the hashed prefix.
fn take_slot<K: Ord + Clone>(claims: &[K], claimed: &mut [bool], duplicates: &mut Vec<K>, claim: &K) -> usize {
    match claims.binary_search(claim) {
        Ok(pos) if !claimed[pos] => {
            claimed[pos] = true;
            pos
        }
        _ => {
            duplicates.push(claim.clone());
            claims.len() + duplicates.len() - 1
        }
    }
}

fn plan_coverage(
    raw_lean_xmss: &[LeanXmssClaim],
    raw_lean_sphincs: &[LeanSphincsClaim],
    children: &[EthereumProof],
    declare: Option<&SignatureClaims>,
) -> Result<Coverage, AggregationError> {
    let cover = Coverage {
        xmss: Region::plan(
            raw_lean_xmss,
            children.iter().map(|child| child.xmss_signers.as_slice()),
            declare.map(|claims| claims.xmss.as_slice()),
        )?,
        lean_sphincs: Region::plan(
            raw_lean_sphincs,
            children.iter().map(|child| child.lean_sphincs_signers.as_slice()),
            declare.map(|claims| claims.lean_sphincs.as_slice()),
        )?,
    };
    if cover.n_total() >= MAX_KEYS {
        return Err(AggregationError::TooLarge);
    }
    Ok(cover)
}

/// The digits of a WOTS+C codeword as the guest dispatches on them: `DIGIT_GROUP` at
/// a time, then the last alone, each group's index little endian in base
/// `CHAIN_LEN`, in the exponent.
fn digit_hints(codeword: &[u8]) -> impl Iterator<Item = Vec<F192>> + '_ {
    codeword.chunks(DIGIT_GROUP).map(|group| {
        let index = group
            .iter()
            .rev()
            .fold(0, |index, &digit| index * lean_xmss::CHAIN_LEN + digit as usize);
        vec![count(index)]
    })
}

/// One leanXMSS signature's witness: the bits of its leaf index, then per layer,
/// bottom first, the randomizer, the codeword's digits, the chain values they start
/// from, and the ordered children of every node on the path.
fn lean_xmss_hints(
    pk: &LeanXmssPublicKey,
    sig: &LeanXmssSignature,
    message: &lean_xmss::Message,
) -> Result<SubHints, AggregationError> {
    let pp = &pk.public_param;
    let bits = (0..lean_xmss::LOG_LIFETIME).map(|b| F192::new(u64::from(sig.leaf_index >> b & 1), 0, 0));
    let mut hints: SubHints = vec![("leaf_index_bits", bits.collect())];
    let mut root: Vec<u8> = message.to_vec();
    for (layer, layer_sig) in [&sig.bottom, &sig.top].into_iter().enumerate() {
        let e = lean_xmss::layer_index(sig.leaf_index, layer);
        let (codeword, reached) = lean_xmss::layer_root(pp, layer, e, &root, layer_sig, |pair| {
            hints.push(("siblings", vec![pack_16_bytes(&pair[0]), pack_16_bytes(&pair[1])]));
        })
        .ok_or(AggregationError::MalformedRawSignature)?;
        hints.push(("randomizer", vec![pack_16_bytes(&layer_sig.randomizer)]));
        hints.extend(digit_hints(&codeword).map(|entry| ("digits", entry)));
        for value in &layer_sig.chain_values {
            hints.push(("chain_starts", vec![pack_16_bytes(value)]));
        }
        root = reached.to_vec();
    }
    Ok(hints)
}

/// One leanSPHINCS signature's witness: the randomizer, the forest's opened chain
/// values, each tree's leaf and each subtree's key as the guest dispatches on
/// them, the forest's path nodes in signature order, the encoding counter, the
/// codeword digits (three at a time, in the exponent), the chain values they
/// start from, and the ordered children of every node on the tree's path.
///
/// The guest derives the index and every tree's choices from the digest itself,
/// so nothing here carries them. The signer's own message is not hinted either:
/// it rides its slot in the coverage table.
fn push_lean_sphincs_hints(
    hints: &mut Hints,
    (pk, message): &LeanSphincsClaim,
    sig: &LeanSphincsSignature,
) -> Result<(), AggregationError> {
    let pp = &pk.public_param;
    hints.push("sp_rand", vec![pack_16_bytes(&sig.randomizer)]);
    let subtrees = sig.forest.iter().flat_map(|tree| &tree.subtrees);
    for value in subtrees.flat_map(|subtree| &subtree.values) {
        hints.push("sp_forest_values", vec![pack_16_bytes(value)]);
    }
    let (idx, marks) = lean_sphincs::message_digest(pp, &sig.randomizer, message);
    for word in marks.iter().flat_map(|mark| mark.words) {
        hints.push("sp_words", vec![count(word)]);
    }
    // A field the guest dispatches on: in the exponent, and as an address holds it.
    let mark = |index: usize, field: u32| {
        let address = lean_sphincs::address(&lean_sphincs::tweak(0, field, 0));
        vec![count(index), pack_16_bytes(&address)]
    };
    for (tree, mark_of) in sig.forest.iter().zip(&marks) {
        hints.push("sp_leaves", mark(mark_of.leaf, lean_sphincs::leaf_field(mark_of.leaf)));
        for (subtree, &key) in tree.subtrees.iter().zip(&mark_of.keys) {
            hints.push("sp_keys", mark(key, lean_sphincs::key_field(key)));
            for node in &subtree.path {
                hints.push("sp_forest_nodes", vec![pack_16_bytes(node)]);
            }
        }
        for node in &tree.path {
            hints.push("sp_forest_nodes", vec![pack_16_bytes(node)]);
        }
    }
    let forest_key = lean_sphincs::forest_recover(pp, idx as u32, &marks, &sig.forest);
    let codeword = lean_sphincs::encode(pp, idx as u32, &forest_key, sig.counter)
        .ok_or(AggregationError::MalformedRawSignature)?;
    hints.push("sp_counter", vec![F192::new(u64::from(sig.counter), 0, 0)]);
    for entry in digit_hints(&codeword) {
        hints.push("digits", entry);
    }
    for opened in &sig.wots {
        hints.push("chain_starts", vec![pack_16_bytes(opened)]);
    }
    let leaf = lean_sphincs::wots_leaf(pp, idx as u32, &forest_key, sig.counter, &sig.wots)
        .ok_or(AggregationError::MalformedRawSignature)?;
    // On the tree's path the guest does not order a node and its sibling: it is
    // handed the two children in order and checks that the node it holds is the
    // one its bit names.
    let root = lean_sphincs::tree_fold_with(pp, idx, leaf, &sig.path, |pair| {
        hints.push("siblings", vec![pack_16_bytes(&pair[0]), pack_16_bytes(&pair[1])]);
    });
    debug_assert_eq!(root, pk.root, "the hinted walk reaches the public key");
    Ok(())
}

/// Prove existence of signatures and valid encoding of PQ-blobs, potentially using recursive children.
///
/// - `children`: child proofs; at most [`MAX_RECURSIONS`].
/// - `raw_lean_xmss`: list of `(public_key, message, signature)`, any order, each signature at
///   the leaf index it carries.
/// - `raw_lean_sphincs`: list of `(public_key, message, signature)`, any order.
/// - `blobs`: concatenated blobs, each containing [`BLOB_SYMBOLS`] little-endian `u64` symbols;
///   at most [`DA_MAX_ROWS`] blobs.
/// - `declare`: `None` keeps all claims; `Some` specifies exactly the signatures and DA roots
///   to publish. Every declared claim must be covered by the inputs above.
/// - `log_inv_rate`: PCS code rate `2^-log_inv_rate`, higher `log_inv_rate` means a smaller proof
///   but slower proving; in [`MIN_LOG_INV_RATE`]..=[`MAX_LOG_INV_RATE`].
///
/// The combined leanXMSS and leanSPHINCS claim count, including duplicate coverage slots, must be strictly below [`MAX_KEYS`].
///
/// IMPORTANT:
/// - `aggregate` should not be called more than once at a time in parallel per process.
/// - Raw signatures are assumed valid (otherwise `aggregate` will panic).
/// - Children are assumed verified by the caller ([`EthereumProof::verify`]): any invalid child
///   proof ends up returning the error [`AggregationError::ProofError`] (TODO return the index of invalid proof).
pub fn aggregate(
    children: &[EthereumProof],
    raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: &[u64],
    declare: Option<ClaimSelection<'_>>,
    log_inv_rate: usize,
) -> Result<EthereumProof, AggregationError> {
    aggregate_with_stats(children, raw_lean_xmss, raw_lean_sphincs, blobs, declare, log_inv_rate).map(|(sig, _)| sig)
}

/// [`aggregate`], under the same contract, also returning the prover's statistics (what the CLI's benchmarks report).
pub fn aggregate_with_stats(
    children: &[EthereumProof],
    raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: &[u64],
    declare: Option<ClaimSelection<'_>>,
    log_inv_rate: usize,
) -> Result<(EthereumProof, leanvm_core::cpu::Stats), AggregationError> {
    let declared_roots = declare.map(|claims| claims.da_commitments);
    let declare = declare.map(|claims| claims.signatures);
    // Otherwise this reaches `cpu::prove`, which asserts rather than reporting.
    if !(leanvm_core::pcs::MIN_LOG_INV_RATE..=leanvm_core::pcs::MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(AggregationError::InvalidRate { log_inv_rate });
    }
    if children.len() > MAX_RECURSIONS {
        return Err(AggregationError::TooLarge);
    }
    if !blobs.len().is_multiple_of(BLOB_SYMBOLS) || blobs.len() / BLOB_SYMBOLS > DA_MAX_ROWS {
        return Err(AggregationError::InvalidBlobSize { symbols: blobs.len() });
    }
    let mut available_roots = BTreeSet::new();
    for child in children {
        check_da_roots(&child.da_roots).map_err(AggregationError::InvalidChild)?;
        available_roots.extend(child.da_roots.iter().copied());
    }
    let mut da_roots = match declared_roots {
        Some(roots) => roots.iter().copied().collect::<BTreeSet<_>>().into_iter().collect(),
        None => available_roots.iter().copied().collect::<Vec<_>>(),
    };
    if da_roots.len() > MAX_DA_ROOTS {
        return Err(AggregationError::TooLarge);
    }
    if blobs.is_empty() && da_roots.iter().any(|root| !available_roots.contains(root)) {
        return Err(AggregationError::BlobNotCovered);
    }

    let guest = unified_guest();
    // On the whole (pubkey, message) pair, so a signer may appear once per message. One
    // claim needs one signature, whatever leaf index a leanXMSS one carries.
    let mut raw_lean_xmss = raw_lean_xmss;
    raw_lean_xmss.sort_by_key(|(pk, message, _)| (*pk, *message));
    raw_lean_xmss.dedup_by(|(a, am, _), (b, bm, _)| (a, am) == (b, bm));
    let mut raw_lean_sphincs = raw_lean_sphincs;
    raw_lean_sphincs.sort_by_key(|(pk, message, _)| (*pk, *message));
    raw_lean_sphincs.dedup_by(|(a, am, _), (b, bm, _)| (a, am) == (b, bm));

    // The children are assumed checked. Nothing here verifies one: the replay
    // only reads out of its proof the summary `gen_verify` derives the guest's
    // witness from, and fails on a proof it cannot walk. A child that does not
    // verify fails in the guest instead, which verifies every child in the VM,
    // so `prove` below returns the error, unless its false flock claim already
    // failed the batching. Its deferred claim is likewise not
    // recomputed: the batching sumcheck below forces every batched value to be
    // the true evaluation, and the root discharges the one claim they reduce to.
    let _span = tracing::info_span!("Replay children").entered();
    let mut statements = Vec::with_capacity(children.len());
    for child in children {
        check_signer_set(&child.xmss_signers, &child.lean_sphincs_signers).map_err(AggregationError::InvalidChild)?;
        statements.push(child.public_input());
    }
    // One single-threaded replay per worker: nothing inside dispatches.
    let bytecode = scalar_bytecode();
    let summaries = parallel::map_collect(children.len(), |i| {
        let public_input = public_input_bytes(&statements[i]);
        verifier::replay_unchecked(bytecode, &public_input, &scalar_proof(&children[i].proof))
    });
    let mut replayed = Vec::with_capacity(children.len());
    for (pi, summary) in statements.into_iter().zip(summaries) {
        let summary = summary.map_err(|e| AggregationError::InvalidChild(AggregateVerifyError::Snark(e)))?;
        replayed.push((pi, summary));
    }

    drop(_span);

    let _span = tracing::info_span!("Build witness").entered();
    let raw_xmss_claims: Vec<LeanXmssClaim> = raw_lean_xmss.iter().map(|(pk, message, _)| (*pk, *message)).collect();
    let raw_lean_sphincs_claims: Vec<LeanSphincsClaim> = raw_lean_sphincs
        .iter()
        .map(|(pk, message, _)| (*pk, *message))
        .collect();
    let cover = plan_coverage(&raw_xmss_claims, &raw_lean_sphincs_claims, children, declare)?;
    let da_contributions =
        usize::from(!blobs.is_empty()) + children.iter().map(|child| child.da_roots.len()).sum::<usize>();
    if cover.n_total() + da_contributions >= MAX_KEYS {
        return Err(AggregationError::TooLarge);
    }

    let mut hints = Hints::default();
    hints.push(
        "meta",
        vec![
            count(cover.xmss.signers.len()),
            count(cover.xmss.dups.len()),
            count(raw_lean_xmss.len()),
            count(cover.lean_sphincs.signers.len()),
            count(cover.lean_sphincs.dups.len()),
            count(raw_lean_sphincs.len()),
            count(children.len()),
            count(usize::from(!blobs.is_empty())),
        ],
    );
    let fs_seed = leanvm_core::cpu::fs_seed(guest);
    hints.push("fs_seed", vec![fs_seed[0], fs_seed[1]]);
    // Both lists in the guest's order, leanXMSS first: each one's split, its declared
    // claims, then its duplicates.
    let lean_xmss_cells: Vec<[F192; 4]> = cover.xmss.signers.iter().map(lean_xmss_claim_cells).collect();
    let lean_sphincs_cells: Vec<[F192; 4]> = cover
        .lean_sphincs
        .signers
        .iter()
        .map(lean_sphincs_claim_cells)
        .collect();
    for cells in [&lean_xmss_cells, &lean_sphincs_cells] {
        if !cells.is_empty() {
            hints.push("signers_split", signers_split(cells.len()));
        }
        for claim in cells {
            hints.push("claims", claim.to_vec());
        }
    }
    let dups = cover.xmss.dups.iter().map(lean_xmss_claim_cells);
    for claim in dups.chain(cover.lean_sphincs.dups.iter().map(lean_sphincs_claim_cells)) {
        hints.push("dup_claims", claim.to_vec());
    }
    // Each slot is hinted as an offset into its scheme's region, which is how one
    // range check keeps a scheme's writers off the other's claims.
    let lean_xmss_hints = parallel::map_collect(raw_lean_xmss.len(), |i| {
        let (pk, message, sig) = &raw_lean_xmss[i];
        lean_xmss_hints(pk, sig, message)
    });
    for (&offset, sub) in cover.xmss.raw.iter().zip(lean_xmss_hints) {
        hints.push("raw_index", vec![count(offset)]);
        for (name, entry) in sub? {
            hints.push(name, entry);
        }
    }
    for (&offset, (pk, message, sig)) in cover.lean_sphincs.raw.iter().zip(&raw_lean_sphincs) {
        hints.push("sp_raw_index", vec![count(offset)]);
        push_lean_sphincs_hints(&mut hints, &(*pk, *message), sig)?;
    }

    let mut subs = Vec::with_capacity(children.len());
    let mut carried = Vec::with_capacity(children.len());
    for (i, (child, (pi, summary))) in children.iter().zip(replayed).enumerate() {
        hints.push(
            "child_meta",
            vec![count(child.xmss_signers.len()), count(child.lean_sphincs_signers.len())],
        );
        for offsets in [&cover.xmss.children[i], &cover.lean_sphincs.children[i]] {
            if !offsets.is_empty() {
                hints.push("signers_split", signers_split(offsets.len()));
            }
            for &offset in offsets {
                hints.push("child_claim_index", vec![count(offset)]);
            }
        }
        hints.push("child_defer", child.defer.cells());
        hints.push("child_da_count", vec![count(child.da_roots.len())]);
        let (sub_hints, defer) = gen_verify(guest, pi, &child.proof.stream, summary)?;
        for (name, entry) in sub_hints {
            hints.push(name, entry);
        }
        subs.push(defer);
        carried.push(&child.defer);
    }

    drop(_span);

    let defer = if children.is_empty() {
        let leaf = DeferredClaim::leaf();
        hints.push(
            "leaf_defer",
            vec![leaf.bytecode_value, leaf.matrix_a_value, leaf.matrix_b_value],
        );
        leaf
    } else {
        let _span = tracing::info_span!("Batch deferred claims").entered();
        let (agg_hints, reduced) =
            aggregate_deferred_claims(&subs, &carried).map_err(AggregationError::InvalidChild)?;
        for (name, entry) in agg_hints {
            hints.push(name, entry);
        }
        reduced
    };

    let direct_root = if blobs.is_empty() {
        None
    } else {
        let _span = tracing::info_span!("LeanDA commit").entered();
        let n_rows = blobs.len() / BLOB_SYMBOLS;
        let (commitment, witness) = lean_da::commit(blobs);
        for block in lean_da::membership_vector(&commitment.root)
            .as_chunks::<CELL_SYMBOLS>()
            .0
        {
            hints.push("da_weights", block.to_vec());
        }
        hints.push(
            "da_shape",
            vec![count(n_rows), count(n_rows.next_power_of_two().ilog2() as usize)],
        );
        // Padding rows are constants the guest bakes, so only the real rows'
        // symbols ride the stream.
        let (c, m) = (CELL_SYMBOLS, CODEWORD_SYMBOLS);
        for j in 0..CELLS_PER_ROW {
            for i in 0..n_rows {
                hints.push(
                    "da_symbols",
                    witness.codewords[i * m + j * c..i * m + (j + 1) * c]
                        .iter()
                        .map(|&w| F192::from(F64(w)))
                        .collect(),
                );
            }
        }
        Some(commitment.root)
    };
    if let Some(root) = direct_root {
        available_roots.insert(root);
        if declared_roots.is_none() {
            da_roots = available_roots.iter().copied().collect();
        }
        if da_roots.len() > MAX_DA_ROOTS {
            return Err(AggregationError::TooLarge);
        }
    }
    if cover.xmss.signers.is_empty() && cover.lean_sphincs.signers.is_empty() && da_roots.is_empty() {
        return Err(AggregationError::Empty);
    }
    let mut claimed = vec![false; da_roots.len()];
    let mut da_dups = Vec::new();
    for root in direct_root
        .iter()
        .chain(children.iter().flat_map(|child| &child.da_roots))
    {
        let slot = take_slot(&da_roots, &mut claimed, &mut da_dups, root);
        hints.push("da_index", vec![count(slot)]);
    }
    if claimed.contains(&false) {
        return Err(AggregationError::BlobNotCovered);
    }
    hints.push("da_meta", vec![count(da_roots.len()), count(da_dups.len())]);
    for root in da_roots.iter().chain(&da_dups) {
        hints.push("da_roots", da_claim_cells(root));
    }

    let public_input = statement_digest(
        signers_hash(&cover.xmss.signers, &cover.lean_sphincs.signers),
        da_list_digest(&da_roots),
        &defer,
    );
    let mut program = guest.clone();
    // Every aggregate is a potential child, and the guest has no opening arm below
    // `2^MU_MIN`. A run smaller than that (a leaf of a few dozen signatures) grows
    // its SET table until it clears the floor.
    program.min_log_committed = MU_MIN;
    hints.install(&mut program);
    let (proof, stats) = prove(&program, public_input, log_inv_rate).map_err(AggregationError::ProofError)?;
    Ok((
        EthereumProof {
            xmss_signers: cover.xmss.signers,
            lean_sphincs_signers: cover.lean_sphincs.signers,
            da_roots,
            defer,
            proof,
        },
        stats,
    ))
}
struct CoordinateDescriptor {
    kind: usize,
    constant: u128,
    /// Its value on its table's padding row; zero for a framework coordinate.
    padding: u64,
    fresh: usize,
    claim_slot: usize,
    terms: Range<usize>,
}

struct Term {
    kind: usize,
    constant: u128,
    column_a: usize,
    column_b: usize,
}

struct ClaimDescriptor {
    buffer: usize,
    column: usize,
    qflock_slot: usize,
}

fn literals(values: impl IntoIterator<Item = impl std::fmt::Display>) -> String {
    format!(
        "[{}]",
        values.into_iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")
    )
}

struct OpeningShape {
    n_levels: usize,
    yr_level: usize,
    yr_log_len: usize,
    folds: Vec<usize>,
    log_message_columns: Vec<usize>,
    queries: Vec<usize>,
    tree_depths: Vec<usize>,
    positions_per_squeeze: Vec<usize>,
    squeezes: Vec<usize>,
    interleaving: Vec<usize>,
    query_grinding_bits: Vec<usize>,
    cap_depths: Vec<usize>,
    cap_offsets: Vec<usize>,
    positions_offsets: Vec<usize>,
    vanish_offsets: Vec<usize>,
    fold_offsets: Vec<usize>,
    residual_fold_offsets: Vec<usize>,
    vanish_values: Vec<F192>,
    vanish_inverses: Vec<F192>,
    ood_samples: Vec<usize>,
}

/// The recursion program's placeholder map depends on table structure and bytecode
/// size, so one compiled guest serves every proof layout.
fn placeholder_map(kbc: usize) -> BTreeMap<String, String> {
    // Only block and coordinate structure is used here; dummy instructions and
    // table sizes let us derive it before the guest's bytecode exists.
    let stand_in = vec![leanvm_core::cpu::Op::Xor { a: 0, b: 0, c: 0 }; 1 << kbc];
    let layout = leanvm_core::cpu::layout(&stand_in, 20, [1 << 10; N_TABLES], [F192::ZERO, F192::ZERO]);
    let sides: [&[Block]; 3] = [&layout.push, &layout.pull, &layout.count];
    let lcrounds = flock::hash::K_LOG - 6;

    // ---- flattened block/coord descriptors (structural) ----
    let mut sblk = vec![0usize];
    let mut block_coords = Vec::new();
    let mut coordinates = Vec::new();
    let mut terms = Vec::new();
    let (mut nclaims, mut nbcv, mut nblocks) = (0usize, 0usize, 0usize);
    // Claim dedup (mirrors leaf.rs): per coord, fresh = first (group, col,
    // kappa) occurrence gets the next pool slot; duplicates point at it.
    let mut slot_of: std::collections::HashMap<(usize, usize), usize> = Default::default();
    // A TABLE block's coordinates, flattened into terms: the guest rebuilds each as
    // `Σ_terms`, so a derived value (an XOR/MUL result, a DEREF store, a JUMP
    // successor) costs terms rather than columns. A framework coordinate has none:
    // it decomposes into pooled claims instead.
    // The table sumcheck settles table claims; only framework blocks stream column values.
    let sch_pm = leanvm_core::cpu::schema();
    let owner_pm: Vec<Option<usize>> = leanvm_core::cpu::block_kappa_sources(kbc)
        .into_iter()
        .map(|(src, _)| src.checked_sub(2))
        .collect();
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            block_coords.push(coordinates.len()..coordinates.len() + blk.coords.len());
            let owner = owner_pm[nblocks];
            nblocks += 1;
            for (i, c) in blk.coords.iter().enumerate() {
                // One COORD_FRESH/COORD_CLAIM_SLOT entry PER coord (the guest
                // indexes them by global coord offset); only a framework block's
                // Col/GCol raises a claim.
                let (mut fresh, mut slot) = (0usize, 0usize);
                if let (Coord::Col(i) | Coord::GCol(i, _), None) = (c, owner) {
                    let key = (*i, blk.kappa);
                    if let Some(&known) = slot_of.get(&key) {
                        slot = known;
                    } else {
                        slot_of.insert(key, nclaims);
                        fresh = 1;
                        slot = nclaims;
                        nclaims += 1;
                    }
                }
                let start = terms.len();
                if let Some(t) = owner {
                    push_coord_terms(c, sch_pm.base[t], &mut terms);
                }
                nbcv += usize::from(matches!(c, Coord::Public(_)));
                coordinates.push(CoordinateDescriptor {
                    kind: coord_kind(c),
                    constant: dsl_u128(coord_scale(c)),
                    padding: blk.padding.get(i).map_or(0, |v| v.0),
                    fresh,
                    claim_slot: slot,
                    terms: start..terms.len(),
                });
            }
        }
        sblk.push(nblocks);
    }
    let evtot: usize = leanvm_core::tables::tables()
        .iter()
        .map(|t| t.n_committed_columns())
        .sum();
    let ncl = nclaims + evtot + 3; // bus + constraint + the three PI memory-limb claims

    // ---- claim descriptor buffer ids (structural) ----
    let valcols = blake2s_value_columns();
    let col_sources_pm = leanvm_core::cpu::col_kappa_sources(kbc);
    let mut compact_col_pm = vec![usize::MAX; col_sources_pm.len()];
    let mut n_committed = 0usize;
    for (global, source) in col_sources_pm.iter().enumerate() {
        if source.is_some() {
            compact_col_pm[global] = n_committed;
            n_committed += 1;
        }
    }
    let qflock_compact = compact_col_pm[leanvm_core::cpu::QFLOCK];
    assert_ne!(qflock_compact, usize::MAX, "QFLOCK must be committed");
    // Buffer codes are the guest's POINT_BUF_*: zeta, chi, pi, qflock-chi.
    let mut claims = Vec::new();
    walk_claims(&layout, kbc, |site| {
        let descriptor = match site {
            ClaimSite::Framework { column, .. } => {
                let column = compact_col_pm[column];
                assert_ne!(column, usize::MAX, "framework claim must target a committed column");
                ClaimDescriptor {
                    buffer: 0,
                    column,
                    qflock_slot: 0,
                }
            }
            ClaimSite::TableColumn { column, is_virtual, .. } => ClaimDescriptor {
                buffer: if is_virtual { 3 } else { 1 },
                column: if is_virtual {
                    qflock_compact
                } else {
                    compact_col_pm[column]
                },
                qflock_slot: if is_virtual {
                    leanvm_core::hash_flock::SLOTS[valcols.iter().position(|&v| v == column).unwrap()]
                } else {
                    0
                },
            },
            ClaimSite::MemoryLimb { column } => ClaimDescriptor {
                buffer: 2,
                column: compact_col_pm[column],
                qflock_slot: 0,
            },
        };
        claims.push(descriptor);
    });
    assert_eq!(claims.len(), ncl, "descriptor count == pool size");

    // ---- the placeholder map ----
    let flds = |v: &[F192]| {
        format!(
            "[{}]",
            v.iter().map(|&x| f192_literal(x)).collect::<Vec<_>>().join(", ")
        )
    };
    let mut rep = BTreeMap::new();
    let mut ps = |k: &str, v: String| {
        rep.insert(format!("{k}_PLACEHOLDER"), v);
    };
    ps("STREAM_CAP", STREAM_CAP.to_string());
    ps("MIN_LOG_MEM", leanvm_core::cpu::MIN_LOG_MEM.to_string());
    ps("INV_GEN", dsl_u128(F192::new(G.inv().0, 0, 0)).to_string());
    ps("MU_CAP", MU_CAP.to_string());
    ps("NO_TABLE", N_TABLES.to_string());
    ps("GKR_ROUNDS_CAP", (MU_CAP * (MU_CAP + 1) / 2 + MU_CAP + 2).to_string());
    ps("GKR_POINTS_CAP", ((MU_CAP + 1) * MU_CAP).to_string());
    ps("SIDE_BLOCK_START", literals(&sblk));
    ps("N_BLOCKS", nblocks.to_string());
    let bks = leanvm_core::cpu::block_kappa_sources(kbc);
    // Push and pull emit bus blocks in matched pairs, so their baked kappa-source
    // segments are identical; the guest computes only push's side total and
    // aliases pull's mu to push's on this basis.
    assert_eq!(
        bks[sblk[0]..sblk[1]],
        bks[sblk[1]..sblk[2]],
        "push/pull kappa sources must match"
    );
    // The guest also reuses push's padding term for pull, which needs the same padding
    // tuples (a padding row's counts are zero, so a count's `g·` changes nothing).
    assert!(
        layout
            .push
            .iter()
            .zip(&layout.pull)
            .all(|(a, b)| a.padding == b.padding),
        "push/pull padding tuples must match"
    );
    ps("BLOCK_KAPPA_SRC", literals(bks.iter().map(|&(s, _)| s)));
    ps("BLOCK_KAPPA_ADJ", literals(bks.iter().map(|&(_, a)| a)));
    ps(
        "BLOCK_TABLE",
        literals(bks.iter().map(|&(s, _)| if s >= 2 { s - 2 } else { N_TABLES })),
    );
    let mut block_side = Vec::new();
    for (s, blocks) in sides.iter().enumerate() {
        block_side.extend(std::iter::repeat_n(s, blocks.len()));
    }
    ps("BLOCK_SIDE", literals(&block_side));
    ps("BLOCK_COORD_OFF", literals(block_coords.iter().map(|r| r.start)));
    ps("BLOCK_COORD_COUNT", literals(block_coords.iter().map(|r| r.len())));
    ps("COORD_TYPE", literals(coordinates.iter().map(|c| c.kind)));
    ps("COORD_CONST", literals(coordinates.iter().map(|c| c.constant)));
    ps("COORD_PADDING", literals(coordinates.iter().map(|c| c.padding)));
    ps("COORD_FRESH", literals(coordinates.iter().map(|c| c.fresh)));
    ps("COORD_CLAIM_SLOT", literals(coordinates.iter().map(|c| c.claim_slot)));
    ps("COORD_TERM_OFF", literals(coordinates.iter().map(|c| c.terms.start)));
    ps("COORD_TERM_COUNT", literals(coordinates.iter().map(|c| c.terms.len())));
    ps("TERM_TYPE", literals(terms.iter().map(|t| t.kind)));
    ps("TERM_CONST", literals(terms.iter().map(|t| t.constant)));
    ps("TERM_COL_A", literals(terms.iter().map(|t| t.column_a)));
    ps("TERM_COL_B", literals(terms.iter().map(|t| t.column_b)));
    ps("N_BUS_CLAIMS", nclaims.to_string());
    let idxc: Vec<u128> = (0..34)
        .map(|i| {
            let mut g2k = F192::new(G.0, 0, 0);
            for _ in 0..i {
                g2k = g2k * g2k;
            }
            dsl_u128(F192::ONE + g2k)
        })
        .collect();
    ps("INDEX_MLE_FACTORS", literals(&idxc));
    ps("N_CLAIMS", ncl.to_string());
    ps("N_TABLES", N_TABLES.to_string());
    // The table sumcheck's xi layout, from the native verifier's own numbers:
    // a disjoint range of identities per table, then THREE powers shared by every
    // table, one per bus side. Sharing is what lets the target be derived from the
    // three leaf claims instead of trusted (leanvm_core::cpu::xi_form_base).
    let n_id: Vec<usize> = leanvm_core::tables::tables()
        .iter()
        .map(|t| t.n_constraints())
        .collect();
    let form_base = leanvm_core::cpu::xi_form_base();
    ps(
        "ETA_OFFSET",
        literals(leanvm_core::constraints::xi_offsets(n_id.iter().copied())),
    );
    ps("ETA_FORM_BASE", form_base.to_string());
    ps("N_ETA_POWS", (form_base + 3).to_string());
    let committed: Vec<usize> = leanvm_core::tables::tables()
        .iter()
        .map(|t| t.n_committed_columns())
        .collect();
    ps("N_TABLE_COLS", literals(&committed));
    ps("TABLE_COLS_CAP", (committed.iter().max().unwrap() + 1).to_string());
    let fixed_challenges: Vec<F192> = flock::zerocheck::univariate_skip_optimized::small_challenges()
        .into_iter()
        .chain(flock::zerocheck::univariate_skip_optimized::medium_challenges())
        .collect();
    ps("FIXED_CHALLENGES", flds(&fixed_challenges));
    // Flock univariate skip: 6 skipped variables, then the fixed inner rounds.
    ps("K_SKIP", "6".to_string());
    ps("N_FIXED_CHALLENGE_ROUNDS", fixed_challenges.len().to_string());
    ps("PHI8_NODES", flds(&primitives::field::PHI_8_TABLE_192[..128]));
    // Tower F192 = F64[Y]/(Y^3+Y+1), Y = new(0,1,0). Y_TOWER embeds Y for
    // AIR lane reassembly; Y_INV splits a canonical word into its two K limbs.
    let y_tower = F192::new(0, 1, 0);
    ps("Y_TOWER", dsl_u128(y_tower).to_string());
    ps("Y_INV", f192_literal(y_tower.inv()));
    // Coordinate basis e_i of F192 over F2 (spans the whole field): the 64
    // binary basis vectors in each of the three tower limbs. The guest uses
    // these vectors to reconstruct a word from its 192 coordinate bits.
    let coord_basis: Vec<F192> = (0..192)
        .map(|i| match i / 64 {
            0 => F192::new(1u64 << i, 0, 0),
            1 => F192::new(0, 1u64 << (i - 64), 0),
            2 => F192::new(0, 0, 1u64 << (i - 128)),
            _ => unreachable!(),
        })
        .collect();
    ps("COORD_BASIS", flds(&coord_basis));
    // One constant per domain, not one per node: every barycentric denominator over an aligned φ₈
    // window is the same element (`primitives::multilinear::window_denominator`).
    ps(
        "LAGRANGE_INV_COMBINED",
        f192_literal(primitives::multilinear::window_denominator(128)),
    );
    ps(
        "LAGRANGE_INV_S",
        f192_literal(primitives::multilinear::window_denominator(64)),
    );
    ps("LINCHECK_ROUNDS", lcrounds.to_string());
    ps("PIN_COLUMN", flock::hash::Z_CONST_POS.to_string());
    ps("K_LOG", flock::hash::K_LOG.to_string());
    // The q_flock Strided-claim slot stride is K_LOG - LOG_PACKING (= 8), so the
    // qflock point-claim slot must use THIS, not LOG2_FIELD_BITS.
    ps("SLOT_STRIDE_LOG", leanvm_core::hash_flock::SLOT_STRIDE_LOG.to_string());

    // ---- LIG candidate tables (fixed [minm, maxm] range; open_stacked config) ----
    let oshape = |m: usize, log_inv_rate: usize| {
        let shape = whir_shape(m, log_inv_rate);
        let (vc, sh) = (&shape.config, &shape.levels);
        let (cn, cr) = (sh.levels, vc.level_steps);
        // Every cap root must match a transcript-bound root, including the final level.
        assert_eq!(cr, cn - 1, "the yr level must be the last one");
        let (ck, cl, cyr) = (&sh.ks, &sh.log_msg_cols, sh.yr_log_n);
        let cq = &vc.queries;
        let (cd, cp) = (&shape.depth, &shape.per_squeeze);
        let cs: Vec<usize> = (0..cn).map(|i| cq[i].div_ceil(cp[i])).collect();
        let cni: Vec<usize> = ck.iter().map(|&k| 1usize << k).collect();
        assert!(
            cni.iter().enumerate().all(|(lv, &n)| {
                let (bytes, whole_blocks) = if lv == 0 {
                    (8 * n, n % 8 == 0)
                } else {
                    (24 * n, (3 * n) % 8 == 0)
                };
                bytes <= 1024 && whole_blocks
            }),
            "recursive WHIR guest supports whole-block Merkle rows of at most one 1024-byte BLAKE2s chunk"
        );
        let psum = |f: &dyn Fn(usize) -> usize| -> Vec<usize> {
            let mut offsets = Vec::with_capacity(cn);
            let mut acc = 0;
            for lv in 0..cn {
                offsets.push(acc);
                acc += f(lv);
            }
            offsets
        };
        let cap_depths: Vec<_> = (0..cn).map(|lv| merkle_cap_depth(cq[lv], cd[lv])).collect();
        let cap_offsets = psum(&|lv| 1 << cap_depths[lv]);
        let c_qpoff = psum(&|lv| cs[lv] * cp[lv]);
        let c_svkoff = psum(&|lv| cl[lv] + 1);
        let c_foldbase = psum(&|lv| ck[lv]);
        let c_risstart: Vec<usize> = (0..cn).map(|k| c_foldbase[k] + ck[k]).collect();
        let mut c_svk = Vec::new();
        let mut c_ivk = Vec::new();
        for &cl_lv in cl.iter().take(cn) {
            for &v in &pcs::whir::eval_sk_at_vks(cl_lv) {
                c_svk.push(F192::new(v.0, 0, 0));
                c_ivk.push(if v == F64::ZERO {
                    F192::ZERO
                } else {
                    F192::new(v.inv().0, 0, 0)
                });
            }
        }
        OpeningShape {
            n_levels: cn,
            yr_level: cr,
            yr_log_len: cyr,
            folds: shape.levels.ks,
            log_message_columns: shape.levels.log_msg_cols,
            queries: shape.config.queries,
            tree_depths: shape.depth,
            positions_per_squeeze: shape.per_squeeze,
            squeezes: cs,
            interleaving: cni,
            query_grinding_bits: shape.config.grinding_bits,
            cap_depths,
            cap_offsets,
            positions_offsets: c_qpoff,
            vanish_offsets: c_svkoff,
            fold_offsets: c_foldbase,
            residual_fold_offsets: c_risstart,
            vanish_values: c_svk,
            vanish_inverses: c_ivk,
            ood_samples: shape.config.ood_samples,
        }
    };
    let (minm, maxm) = (MU_MIN, MU_MAX);
    let rates = pcs::whir::MIN_LOG_INV_RATE..=pcs::whir::MAX_LOG_INV_RATE;
    let cands: Vec<_> = rates
        .clone()
        .flat_map(|r| (minm..=maxm).map(move |m| oshape(m, r)))
        .collect();
    let maxlev = cands.iter().map(|c| c.n_levels).max().unwrap();
    let maxsvk = cands.iter().map(|c| c.vanish_values.len()).max().unwrap();
    let maxood = cands.iter().flat_map(|c| &c.ood_samples).copied().max().unwrap_or(0);
    ps("LIG_MAX_LEVELS", maxlev.to_string());
    ps("LIG_MAX_VANISH_LEN", maxsvk.to_string());
    ps("LIG_MAX_OOD_SAMPLES", maxood.to_string());
    ps("LIG_MIN_LOG_SIZE", minm.to_string());
    let cks: Vec<(usize, usize)> = leanvm_core::cpu::col_kappa_sources(kbc).into_iter().flatten().collect();
    ps("N_COMMITTED_COLS", cks.len().to_string());
    ps("N_COLUMN_LOGS", (MU_MAX + 1).to_string());
    ps("COL_KAPPA_SRC", literals(cks.iter().map(|&(s, _)| s)));
    ps("COL_KAPPA_ADJ", literals(cks.iter().map(|&(_, a)| a)));
    ps("PCS_MIN_MU", leanvm_core::pcs::MIN_MU.to_string());
    ps(
        "LIG_LOG_MSG_COLS_CAP",
        cands
            .iter()
            .map(|c| *c.log_message_columns.iter().max().unwrap())
            .max()
            .unwrap()
            .to_string(),
    );
    ps(
        "YR_LOG_CAP",
        cands.iter().map(|c| c.yr_log_len).max().unwrap().to_string(),
    );
    {
        let flat = |f: &dyn Fn(&OpeningShape) -> Vec<usize>| {
            let rows: Vec<usize> = cands
                .iter()
                .flat_map(|c| {
                    let mut row = f(c);
                    row.resize(maxlev, 0);
                    row
                })
                .collect();
            literals(rows)
        };
        let scal = |f: &dyn Fn(&OpeningShape) -> usize| literals(cands.iter().map(f));
        ps("LIG_N_LEVELS", scal(&|c| c.n_levels));
        ps("LIG_YR_LEVEL", scal(&|c| c.yr_level));
        // The guest rotates the terminal point by the lane-fold count to index it by
        // witness coordinate, and the residual segment is what it rotates the last
        // lane challenges past, so the residual may never be longer than that fold
        // (`RESIDUAL_MAX_LOG` < `INITIAL_FOLDING_FACTOR` keeps this true by a margin).
        assert!(
            cands.iter().all(|c| c.yr_log_len <= c.folds[0]),
            "residual longer than the lane fold: the guest's point rotation has no room"
        );
        ps("LIG_YR_LOG_LEN", scal(&|c| c.yr_log_len));
        ps("LIG_YR_LEN", scal(&|c| 1usize << c.yr_log_len));
        ps("LIG_TOTAL_FOLDS", scal(&|c| c.folds.iter().sum()));
        ps("LIG_MAX_QUERIES", scal(&|c| *c.queries.iter().max().unwrap()));
        ps("LIG_MAX_SQUEEZES", scal(&|c| *c.squeezes.iter().max().unwrap()));
        ps("LIG_MAX_INTERLEAVE", scal(&|c| *c.interleaving.iter().max().unwrap()));
        ps(
            "LIG_POSITIONS_LEN",
            scal(&|c| {
                (0..c.n_levels)
                    .map(|level| c.squeezes[level] * c.positions_per_squeeze[level])
                    .sum()
            }),
        );
        let row_cap = cands
            .iter()
            .flat_map(|c| {
                c.interleaving
                    .iter()
                    .enumerate()
                    .map(|(level, &n)| n * if level == 0 { 1 } else { 3 })
            })
            .max()
            .unwrap();
        ps("LIG_ROW_CAP", row_cap.to_string());
        ps("LIG_PACKED_ROW_CAP", (row_cap / 2).to_string());
        ps(
            "LIG_PATH_CAP",
            cands
                .iter()
                .flat_map(|c| {
                    c.tree_depths
                        .iter()
                        .zip(&c.cap_depths)
                        .map(|(depth, cap)| 4 * (depth - cap))
                })
                .max()
                .unwrap()
                .to_string(),
        );
        ps("LIG_QUERY_GRIND_BITS", flat(&|c| c.query_grinding_bits.clone()));
        ps("LIG_OOD_SAMPLES", flat(&|c| c.ood_samples.clone()));
        ps("LIG_QUERIES", flat(&|c| c.queries.clone()));
        ps("LIG_FOLDS", flat(&|c| c.folds.clone()));
        ps("LIG_INTERLEAVE", flat(&|c| c.interleaving.clone()));
        // 64-byte BLAKE2s blocks per leaf row: level 0's committed rows are
        // base-field F64 (8 bytes/lane); deeper levels are native F192
        // (24 bytes/word, received as three embedded K limbs each). Rows are
        // whole blocks only (asserted at candidate construction).
        ps(
            "LIG_LEAF_BLOCKS",
            flat(&|c| {
                c.interleaving
                    .iter()
                    .enumerate()
                    .map(|(level, &n)| if level == 0 { n / 8 } else { 3 * n / 8 })
                    .collect()
            }),
        );
        ps("LIG_TREE_DEPTH", flat(&|c| c.tree_depths.clone()));
        ps("LIG_CAP_DEPTH", flat(&|c| c.cap_depths.clone()));
        ps("LIG_CAP_OFF", flat(&|c| c.cap_offsets.clone()));
        ps("LIG_CAP_LEN", scal(&|c| c.cap_depths.iter().map(|&d| 1 << d).sum()));
        ps("LIG_SQUEEZES", flat(&|c| c.squeezes.clone()));
        ps("LIG_POSITIONS_OFF", flat(&|c| c.positions_offsets.clone()));
        ps("LIG_LOG_MSG_COLS", flat(&|c| c.log_message_columns.clone()));
        ps("LIG_RESIDUAL_FOLD_OFF", flat(&|c| c.residual_fold_offsets.clone()));
        ps(
            "LIG_RESIDUAL_PREFIX_LEN",
            flat(&|c| {
                c.log_message_columns
                    .iter()
                    .map(|&columns| columns - c.yr_log_len)
                    .collect()
            }),
        );
        ps("LIG_FOLDS_OFF", flat(&|c| c.fold_offsets.clone()));
        ps("LIG_VANISH_OFF", flat(&|c| c.vanish_offsets.clone()));
        let mut svk2 = Vec::with_capacity(cands.len() * maxsvk);
        let mut ivk2 = Vec::with_capacity(cands.len() * maxsvk);
        for candidate in &cands {
            let padded_len = svk2.len() + maxsvk;
            svk2.extend_from_slice(&candidate.vanish_values);
            ivk2.extend_from_slice(&candidate.vanish_inverses);
            svk2.resize(padded_len, F192::ZERO);
            ivk2.resize(padded_len, F192::ZERO);
        }
        ps("LIG_VANISH_VALS", flds(&svk2));
        ps("LIG_VANISH_INVS", flds(&ivk2));
    }
    let n_log_sizes = maxm - minm + 1;
    let n_rates = MAX_LOG_INV_RATE - MIN_LOG_INV_RATE + 1;
    ps("LIG_N_LOG_SIZES", n_log_sizes.to_string());
    ps("LIG_N_RATES", n_rates.to_string());
    ps("LIG_N_CANDIDATES", (n_log_sizes * n_rates).to_string());
    ps(
        "LIG_MIN_SHIFT_INV",
        dsl_u128(F192::new(g_pow(minm).inv().0, 0, 0)).to_string(),
    );
    ps("CLAIM_POINT_BUF", literals(claims.iter().map(|c| c.buffer)));
    ps("CLAIM_COMMITTED_COL", literals(claims.iter().map(|c| c.column)));
    let slot_stride_log = leanvm_core::hash_flock::SLOT_STRIDE_LOG;
    let cpqbits: Vec<usize> = claims
        .iter()
        .flat_map(|c| (0..slot_stride_log).map(move |k| (c.qflock_slot >> k) & 1))
        .collect();
    ps("CLAIM_QFLOCK_SLOT_BITS", literals(&cpqbits));
    ps("QFLOCK_COMMITTED_COL", qflock_compact.to_string());
    ps("QFLOCK_VARS_CAP", (33 + slot_stride_log).to_string());
    ps("BYTECODE_LOG", kbc.to_string());
    // The stacked bytecode: nbcv/2 encoding columns per side, aligned with the bus
    // tuple, so their slots span the fingerprint's own bits. The defer region is
    // 2*kbc points + sel bits + 2 reduced + alpha + z_skip + 2*lcrounds rounds
    // + 64 z_partial + 1 matpart.
    let bc_cols = nbcv / 2;
    let log2_bc_cols = leanvm_core::leaf::N_TUPLE_BITS;
    ps("BYTECODE_COLS", bc_cols.to_string());
    ps("LOG2_BYTECODE_COLS", log2_bc_cols.to_string());
    ps("DEFER_SIZE", (kbc + log2_bc_cols + 2 * lcrounds + 68).to_string());
    ps("BYTECODE_VARS", (kbc + log2_bc_cols).to_string());
    let agg_state = pack_state(FiatShamirState::from_label(RECURSION_AGG_LABEL).state());
    ps("AGG_SEED_0", dsl_u128(agg_state[0]).to_string());
    ps("AGG_SEED_1", dsl_u128(agg_state[1]).to_string());

    // ---- LeanDA (`doc/leanvm` §sec:leanda) ----
    let (pad_cell, pad_row) = lean_da::padding_digests();
    let (pad_cell, pad_row) = (pack_hash_state(&pad_cell), pack_hash_state(&pad_row));
    ps("DA_LOG_K", DA_LOG_K.to_string());
    ps("DA_LOG_CELL", DA_LOG_CELL.to_string());
    ps("DA_MAX_ROWS", DA_MAX_ROWS.to_string());
    ps("DA_LOG_MAX_ROWS", DA_MAX_ROWS.ilog2().to_string());
    ps("DA_PAD_CELL_0", f192_literal(pad_cell[0]));
    ps("DA_PAD_CELL_1", f192_literal(pad_cell[1]));
    ps("DA_PAD_ROW_0", f192_literal(pad_row[0]));
    ps("DA_PAD_ROW_1", f192_literal(pad_row[1]));
    let defer_cells = kbc + log2_bc_cols + 1 + 2 * flock::hash::K_LOG + 2;
    ps("STMT_HEADER", STATEMENT_HEADER.to_string());
    let (off, pairs) = (STATEMENT_HEADER, defer_cells.div_ceil(2));
    let blocks = (off + 3 * pairs).div_ceil(4);
    ps("STMT_ODD", (defer_cells % 2).to_string());
    ps("STMT_PAIRS", pairs.to_string());
    ps("STMT_PAD_CELLS", (4 * blocks - off - 3 * pairs).to_string());
    ps("STMT_BLOCKS", blocks.to_string());
    // A list is at most MAX_KEYS blocks (one a claim is the widest it gets), so it
    // holds fewer than that many windows; a declared count is below MAX_KEYS, hence
    // decomposes into that many bits. The first two bound a range check, which takes
    // a COUNT, the third a bit decomposition.
    ps("SIGNERS_WINDOW", SIGNERS_WINDOW.to_string());
    ps("SIGNERS_WINDOW_LOG", SIGNERS_WINDOW.ilog2().to_string());
    ps("SIGNERS_MAX_WINDOWS", SIGNERS_MAX_WINDOWS.to_string());
    ps("SIGNERS_COUNT_BITS", SIGNERS_COUNT_BITS.to_string());
    ps(
        "BLAKE2S_IV_0",
        dsl_u128(leanvm_core::hash_flock::IV_CELLS[0]).to_string(),
    );
    ps(
        "BLAKE2S_IV_1",
        dsl_u128(leanvm_core::hash_flock::IV_CELLS[1]).to_string(),
    );
    ps(
        "MD_FINAL",
        dsl_u128(leanvm_core::hash_flock::metadata(
            0,
            leanvm_core::hash_flock::FINAL_FLAG,
            0,
        ))
        .to_string(),
    );

    // Both schemes' WOTS+C: the chain length, the digit sums of a dispatched group,
    // and the hash types they share, as the address lane holds them.
    ps("W", lean_xmss::W.to_string());
    ps("DIGIT_GROUP", DIGIT_GROUP.to_string());
    let digit_sums: Vec<String> = (0..lean_xmss::CHAIN_LEN.pow(DIGIT_GROUP as u32))
        .map(|k| {
            let digits = (0..DIGIT_GROUP).map(|r| k / lean_xmss::CHAIN_LEN.pow(r as u32) % lean_xmss::CHAIN_LEN);
            digits.sum::<usize>().to_string()
        })
        .collect();
    ps("DIGIT_SUMS", format!("[{}]", digit_sums.join(", ")));
    let address = |tw| dsl_u128(pack_16_bytes(&lean_xmss::address(&tw))).to_string();
    for (name, tag) in [
        ("TW_CHAIN", lean_xmss::TWEAK_CHAIN),
        ("TW_LEAF", lean_xmss::TWEAK_LEAF),
        ("TW_NODE", lean_xmss::TWEAK_NODE),
        ("TW_MSG", lean_xmss::TWEAK_MSG),
    ] {
        ps(name, address(lean_xmss::tweak(tag, 0, 0)));
    }
    // leanXMSS. Its addresses are derived per signature from the leaf index the
    // signature carries.
    ps("LX_V", lean_xmss::V.to_string());
    ps("LX_TARGET_SUM", lean_xmss::TARGET_SUM.to_string());
    ps("LX_HEIGHT", lean_xmss::LAYER_HEIGHT.to_string());
    ps("LX_TOP", address(lean_xmss::tweak(0, lean_xmss::TOP, 0)));
    ps("MAX_KEYS", MAX_KEYS.to_string());
    ps("MAX_DA_ROOTS", MAX_DA_ROOTS.to_string());
    ps("DA_ROOT_COUNTS", (MAX_DA_ROOTS + 1).to_string());
    ps("MAX_RECURSIONS", MAX_RECURSIONS.to_string());

    // The leanSPHINCS instance. Its addresses are derived per signature from the
    // index the message digest picks, so the guest receives the shape, the codeword
    // table and each hash type of its own as the address lane holds it.
    ps("SP_V", lean_sphincs::V.to_string());
    ps("SP_TARGET_SUM", lean_sphincs::TARGET_SUM.to_string());
    ps("SP_H", lean_sphincs::H.to_string());
    ps("SP_TREES", lean_sphincs::FOREST_TREES.to_string());
    ps("SP_TREE_HEIGHT", lean_sphincs::TREE_HEIGHT.to_string());
    ps("SP_SUBTREE_HEIGHT", lean_sphincs::SUBTREE_HEIGHT.to_string());
    ps("SP_FCHAINS", lean_sphincs::FOREST_CHAINS.to_string());
    ps("SP_FTOP", lean_sphincs::FOREST_CHAIN_TOP.to_string());
    ps("SP_WORD_BITS", lean_sphincs::CODEWORD_BITS.to_string());
    let digits: Vec<String> = (0..1 << lean_sphincs::CODEWORD_BITS)
        .flat_map(lean_sphincs::codeword)
        .map(|digit| digit.to_string())
        .collect();
    ps("SP_CODEWORDS", format!("[{}]", digits.join(", ")));
    for (name, tag) in [
        ("SP_TW_ENC", lean_sphincs::TWEAK_ENC),
        ("SP_TW_FCHAIN", lean_sphincs::TWEAK_FOREST_CHAIN),
        ("SP_TW_FKEY_LEAF", lean_sphincs::TWEAK_FOREST_KEY_LEAF),
        ("SP_TW_FSUBNODE", lean_sphincs::TWEAK_FOREST_SUBNODE),
        ("SP_TW_FTREE_LEAF", lean_sphincs::TWEAK_FOREST_TREE_LEAF),
        ("SP_TW_FNODE", lean_sphincs::TWEAK_FOREST_NODE),
        ("SP_TW_FKEY", lean_sphincs::TWEAK_FOREST_KEY),
    ] {
        ps(
            name,
            dsl_u128(pack_16_bytes(&lean_sphincs::address(&lean_sphincs::tweak(tag, 0, 0)))).to_string(),
        );
    }
    rep
}

/// Build the guest bytecode and the stacked table its claims are about. Both are
/// cached, so this only moves the cost out of the first prove or verify.
pub fn warm_up() {
    unified_guest();
    stacked_bytecode();
    scalar_bytecode();
}

/// The aggregation bytecode, compiled to a fixed point on its own size.
///
/// The recursion placeholders are a function of the inner bytecode's log size,
/// and here the inner bytecode is this one, so the size has to agree with
/// itself. Its *digest* needs no such loop: it rides the statement rather than
/// the code. The guess converges in one or two rounds because the map's only
/// size-dependent part is a handful of unrolled sumcheck rounds.
pub fn unified_guest() -> &'static Program {
    static GUEST: std::sync::OnceLock<Program> = std::sync::OnceLock::new();
    GUEST.get_or_init(|| {
        let mut guess = 20;
        for _ in 0..8 {
            let guest = compile_guest(guess);
            let actual = guest.prog.len().trailing_zeros() as usize;
            if actual == guess {
                return guest;
            }
            guess = actual;
        }
        panic!("the aggregation bytecode's self-referential compile did not converge");
    })
}

fn compile_guest(kbc: usize) -> Program {
    let replacements = placeholder_map(kbc);
    // `DBG_PLACEHOLDERS=path`: dump the baked guest constants, to read alongside
    // a `DBG_PROF_DUMP` profile (the guest's shape is entirely in these).
    if let Ok(path) = std::env::var("DBG_PLACEHOLDERS") {
        let dump: String = replacements.iter().map(|(k, v)| format!("{k} = {v}\n")).collect();
        std::fs::write(&path, dump).expect("write DBG_PLACEHOLDERS");
    }
    let guest = compile(
        &parse_with_replacements(include_str!("../guests/lean_ethereum.py"), &replacements)
            .expect("the repository aggregation guest must parse"),
    );
    // `DBG_DISASM=path`: dump the guest's disassembly, to read alongside a
    // `DBG_PROF_DUMP` per-pc profile. Function boundaries lead the dump, so the
    // pc a failed guest check reports can be resolved to a source function
    // without re-deriving the layout by hand.
    if let Ok(path) = std::env::var("DBG_DISASM") {
        let mut ranges: Vec<_> = guest.fn_ranges.iter().collect();
        ranges.sort_by_key(|(_, entry, _)| *entry);
        let mut dump = String::new();
        for (name, entry, len) in ranges {
            dump += &format!("# fn {entry:>7}..{:<7} {name}\n", entry + len);
        }
        dump += &lean_compiler::disassemble(&guest.prog);
        std::fs::write(&path, dump).expect("write DBG_DISASM");
    }
    guest
}

#[cfg(test)]
mod guest_bytecode;

#[cfg(test)]
mod node_vectors;

#[cfg(test)]
mod guest_source;

#[cfg(test)]
mod guest_diff;

#[cfg(test)]
mod tests {
    use super::*;
    use leanvm_core::cpu::verify;
    use rand::SeedableRng;
    use rand::rngs::StdRng;

    use crate::signers_cache::{
        LEAN_LEAN_SPHINCS_KEPT_HEIGHT, get_lean_sphincs_signers, get_signers, get_signers_for, message, message_for,
    };

    /// A second cached message, sorting after [`message`]; signer `i` holds the same
    /// pubkey under both, at another leaf index.
    const MESSAGE_B: u32 = 2;
    const SMALL_LEAF_SIZE: usize = 6;
    const LOG_INV_RATE: usize = leanvm_core::pcs::TEST_LOG_INV_RATE;

    /// Cached `(pubkey, signature)` pairs as the API takes them, with the message of
    /// cache `message_id` they signed.
    fn signing(
        signers: &[(LeanXmssPublicKey, LeanXmssSignature)],
        message_id: u32,
    ) -> Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)> {
        signers
            .iter()
            .map(|(pk, sig)| (*pk, message_for(message_id), sig.clone()))
            .collect()
    }

    /// Distinct pubkeys, strictly increasing, without generating any.
    fn signer_set(len: usize) -> Vec<LeanXmssPublicKey> {
        (0..len)
            .map(|i| LeanXmssPublicKey {
                merkle_root: (i as u128).to_be_bytes(),
                public_param: [0; lean_xmss::PUBLIC_PARAM_LEN],
            })
            .collect()
    }

    #[test]
    fn signature_claims_keep_the_wire_layout() {
        let claims = SignatureClaims {
            xmss: signer_set(2).into_iter().map(|pk| (pk, message())).collect(),
            lean_sphincs: vec![(
                LeanSphincsPublicKey::from_bytes(&[0xa5; lean_sphincs::PUB_KEY_SIZE]),
                [0x3c; lean_sphincs::MESSAGE_LEN],
            )],
        };
        let bytes = wire().serialize(&(&claims.xmss, &claims.lean_sphincs)).unwrap();
        assert_eq!(wire().serialize(&claims).unwrap(), bytes);
        assert_eq!(wire().deserialize::<SignatureClaims>(&bytes).unwrap(), claims);
    }

    /// The guest compiles to one program, always.
    ///
    /// `unified_guest` finds a fixed point by compiling repeatedly and comparing
    /// the result's log size, so a compiler that read a hash seed would not just
    /// produce two incompatible transcripts, it could fail to converge at all.
    /// The small programs in `lean_compiler`'s `determinism` suite pin the
    /// digests; this pins the one program large enough to hit every path that
    /// walks a map. A fixed `kbc` is enough: reproducibility does not depend on
    /// the size being the fixed point.
    #[test]
    fn guest_compiles_reproducibly() {
        let (one, two) = (compile_guest(20), compile_guest(20));
        assert_eq!(
            format!("{:?}", one.prog),
            format!("{:?}", two.prog),
            "two compilations of the guest produced different bytecode, \
                 so the compiler is reading a hash seed"
        );
    }

    /// `MAX_KEYS` is exclusive at both host checks: one claim short of it passes,
    /// the cap itself is the documented error. The cap counts both schemes, so
    /// one leanXMSS claim short of it plus one leanSPHINCS claim is already over. No proof
    /// involved.
    #[test]
    fn max_keys_bound_is_exclusive() {
        let claims: Vec<LeanXmssClaim> = signer_set(MAX_KEYS).into_iter().map(|pk| (pk, message())).collect();
        let lean_sphincs = [(
            LeanSphincsPublicKey::from_bytes(&[0; lean_sphincs::PUB_KEY_SIZE]),
            [0; lean_sphincs::MESSAGE_LEN],
        )];
        let short = &claims[..MAX_KEYS - 1];
        check_signer_set(short, &[]).expect("one short of the cap");
        assert_eq!(
            check_signer_set(&claims, &[]),
            Err(AggregateVerifyError::MalformedSignerSet)
        );
        assert_eq!(
            check_signer_set(short, &lean_sphincs),
            Err(AggregateVerifyError::MalformedSignerSet)
        );
        plan_coverage(short, &[], &[], None).expect("one short of the cap");
        assert_eq!(
            plan_coverage(&claims, &[], &[], None).err(),
            Some(AggregationError::TooLarge)
        );
        assert_eq!(
            plan_coverage(short, &lean_sphincs, &[], None).err(),
            Some(AggregationError::TooLarge)
        );
    }

    fn prove_leaf(signers: &[(LeanXmssPublicKey, LeanXmssSignature)]) -> EthereumProof {
        aggregate(&[], signing(signers, 0), vec![], &[], None, LOG_INV_RATE).expect("leaf aggregates")
    }

    /// The guest builds a leanXMSS address as its type's cell plus `lo`,
    /// `hi · 2^32` and `step · 2^61` in the low lane, and the top layer's flag, which
    /// must be the native address's bytes.
    #[test]
    fn guest_addresses_are_the_native_ones() {
        let cell = |tw| pack_16_bytes(&lean_xmss::address(&tw));
        let top = cell(lean_xmss::tweak(0, lean_xmss::TOP, 0));
        for tag in [
            lean_xmss::TWEAK_CHAIN,
            lean_xmss::TWEAK_LEAF,
            lean_xmss::TWEAK_NODE,
            lean_xmss::TWEAK_MSG,
        ] {
            for layer in 0..2 {
                for (hi, lo, step) in [(0u32, 0u32, 0usize), (5, 0x1234_5678, 2), (16, u32::MAX, 0)] {
                    let tw = lean_xmss::tweak(tag, lean_xmss::layer_hi(layer, hi), lo).step(step);
                    let fields = F192::new(u64::from(lo) | u64::from(hi) << 32 | (step as u64) << 61, 0, 0);
                    let guest = cell(lean_xmss::tweak(tag, 0, 0)) + fields + if layer == 1 { top } else { F192::ZERO };
                    assert_eq!(guest, cell(tw));
                }
            }
        }
    }

    type RawSphincs = (LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature);

    fn prove_lean_sphincs_leaf(signers: &[RawSphincs]) -> EthereumProof {
        aggregate(&[], vec![], signers.to_vec(), &[], None, LOG_INV_RATE).expect("leaf aggregates")
    }

    #[test]
    fn aggregate_one_lean_sphincs_signer() {
        leanvm_core::init_prover();
        let aggregate = prove_lean_sphincs_leaf(&get_lean_sphincs_signers(1));
        aggregate.verify().expect("verifies");
        assert!(aggregate.xmss_signers.is_empty());
        assert_eq!(aggregate.lean_sphincs_signers.len(), 1);
    }

    #[test]
    fn aggregate_one_signer() {
        leanvm_core::init_prover();
        let aggregate = prove_leaf(&get_signers(1));
        aggregate.verify().expect("verifies");
        assert_eq!(aggregate.xmss_signers[0].1, message());
    }

    /// A leaf holding claims of both schemes, each list in its own region.
    #[test]
    fn aggregate_mixed_leaf() {
        leanvm_core::init_prover();
        let aggregate = aggregate(
            &[],
            signing(&get_signers(3), 0),
            get_lean_sphincs_signers(3),
            &[],
            None,
            LOG_INV_RATE,
        )
        .expect("leaf aggregates");
        aggregate.verify().expect("verifies");
        assert_eq!(
            (aggregate.xmss_signers.len(), aggregate.lean_sphincs_signers.len()),
            (3, 3)
        );
    }

    /// A node over children of both schemes, overlapping in one signer of each:
    /// the coverage table then needs a duplicate slot in both regions, and each
    /// child's two claim lists have to land in their own.
    #[test]
    fn aggregate_mixed_two_to_one() {
        leanvm_core::init_prover();
        let xmss = get_signers(6);
        let lean_sphincs = get_lean_sphincs_signers(4);
        let leaf = |x: &[(LeanXmssPublicKey, LeanXmssSignature)], s: &[RawSphincs]| {
            aggregate(&[], signing(x, 0), s.to_vec(), &[], None, LOG_INV_RATE).expect("leaf aggregates")
        };
        let left = leaf(&xmss[..4], &lean_sphincs[..3]);
        let right = leaf(&xmss[3..], &lean_sphincs[2..]);
        let node = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!((node.xmss_signers.len(), node.lean_sphincs_signers.len()), (6, 4));
        assert!(node.xmss_signers.windows(2).all(|w| w[0] < w[1]));
        assert!(node.lean_sphincs_signers.windows(2).all(|w| w[0] < w[1]));
    }

    /// A node whose children are each of one scheme only: every claim list it
    /// rebuilds is empty on one side, which is the only way the guest's
    /// claim-absorbing loops run over an empty range and its bound `log(x) <
    /// log(g^0)` (unsatisfiable, so nothing may be written there) is reached.
    #[test]
    fn aggregate_one_scheme_per_child() {
        leanvm_core::init_prover();
        let lean_xmss_child = prove_leaf(&get_signers(3));
        let lean_sphincs_child = prove_lean_sphincs_leaf(&get_lean_sphincs_signers(2));
        let node = aggregate(
            &[lean_xmss_child, lean_sphincs_child],
            vec![],
            vec![],
            &[],
            None,
            LOG_INV_RATE,
        )
        .expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!((node.xmss_signers.len(), node.lean_sphincs_signers.len()), (3, 2));
    }

    /// The repeat the statement allows: one pubkey signing two messages is two
    /// claims, ordered by the pair, each needing its own signature. Generated
    /// here rather than cached, the cache holding one message per pubkey.
    #[test]
    fn aggregate_one_key_two_messages() {
        leanvm_core::init_prover();
        let mut rng = StdRng::seed_from_u64(77);
        let (secret_key, public_key) = lean_sphincs::key_gen(&mut rng, LEAN_LEAN_SPHINCS_KEPT_HEIGHT);
        let raw: Vec<RawSphincs> = [3u8, 9]
            .into_iter()
            .map(|tag| {
                let signed: lean_sphincs::Message = std::array::from_fn(|i| tag.wrapping_mul(i as u8 + 1));
                let signature = lean_sphincs::sign(&secret_key, &signed).expect("signs");
                (public_key, signed, signature)
            })
            .collect();
        let aggregate = prove_lean_sphincs_leaf(&raw);
        aggregate.verify().expect("verifies");
        assert_eq!(aggregate.lean_sphincs_signers.len(), 2);
        let (first, second) = (aggregate.lean_sphincs_signers[0], aggregate.lean_sphincs_signers[1]);
        assert_eq!(first.0, second.0, "the same pubkey, twice");
        assert!(first.1 < second.1, "ordered by the message");
    }

    #[test]
    fn guest_column_selectors_match_native_eq() {
        leanvm_core::init_prover();
        let (helpers, _) = include_str!("../guests/lean_ethereum.py")
            .split_once("\ndef main():")
            .unwrap();
        let source = format!(
            r#"{helpers}
def main():
    point = HeapBuf(MAX_STACK_LOG)
    hint_witness(point[0:MAX_STACK_LOG], "point")
    offset = hint_witness("offset")
    kappa_g = hint_witness("kappa")
    weight = match(log(kappa_g), range(0, N_COLUMN_LOGS), lambda kappa: column_selector(offset, point, kappa))
    public = GEN ** 0
    assert public[1] == weight
    return
"#
        );
        let guest = compile(&parse_with_replacements(&source, &placeholder_map(18)).unwrap());
        let run = |point: &[F192], offset: usize, kappa: usize, expected: F192| {
            let mut hints = Hints::default();
            hints.push("point", point.to_vec());
            hints.push("offset", vec![count(offset)]);
            hints.push("kappa", vec![count(kappa)]);
            let mut program = guest.clone();
            hints.install(&mut program);
            program.execute([expected, F192::ZERO])
        };
        let mut rng = StdRng::seed_from_u64(813);
        for mu in MU_MIN..=MU_MAX {
            let mut point: Vec<F192> = (0..mu)
                .map(|_| {
                    let (c0, c1, c2) = rand::Rng::random(&mut rng);
                    F192::new(c0, c1, c2)
                })
                .collect();
            point.resize(MU_MAX, F192::ZERO);
            for kappa in 0..=mu {
                let mask = ((1usize << mu) - 1) & !((1usize << kappa) - 1);
                for offset in [0, mask, 0x0555_5555 & mask] {
                    let selector: Vec<_> = (kappa..mu)
                        .map(|k| F192::from(F64(((offset >> k) & 1) as u64)))
                        .collect();
                    let expected = primitives::multilinear::eq_eval(&selector, &point[kappa..mu]);
                    assert!(
                        run(&point, offset, kappa, expected)
                            .unwrap()
                            .unconstrained_reads
                            .is_empty()
                    );
                }
            }
        }
    }

    #[test]
    fn guest_merkle_path_reaches_the_root() {
        leanvm_core::init_prover();
        let (helpers, _) = include_str!("../guests/lean_ethereum.py")
            .split_once("\ndef main():")
            .unwrap();
        let source = format!(
            r#"{helpers}
def main():
    bits = StackBuf(3)
    hint_witness(bits[0:3], "bits")
    for k in unroll(0, 3):
        bits[k] = bits[k] * bits[k]
    direction = addr(bits)
    leaf = StackBuf(2)
    hint_witness(leaf[0:2], "leaf")
    a, b = verify_merkle_path(leaf[0], leaf[1], direction, 3)
    public = GEN ** 0
    assert public[1] == a
    assert public[GEN] == b
    return
"#
        );
        let guest = compile(&parse_with_replacements(&source, &placeholder_map(18)).unwrap());
        let mut tree = vec![[0u8; 32]; 16];
        for (i, leaf) in tree[8..].iter_mut().enumerate() {
            *leaf = pcs::merkle::hash_leaf(&[i as u8; 64]);
        }
        for i in (1..8).rev() {
            tree[i] = pcs::merkle::hash_pair(&tree[2 * i], &tree[2 * i + 1]);
        }
        let run = |index: usize, leaf: [u8; 32], pairs: &[[[u8; 32]; 2]], root: [u8; 32]| {
            let mut hints = Hints::default();
            hints.push(
                "bits",
                (0..3).map(|k| F192::from(F64(((index >> k) & 1) as u64))).collect(),
            );
            hints.push("leaf", pack_hash_state(&leaf).to_vec());
            hints.push(
                "merkle_children",
                pairs.iter().flatten().flat_map(pack_hash_state).collect(),
            );
            let mut program = guest.clone();
            hints.install(&mut program);
            program.execute(pack_hash_state(&root))
        };
        for index in 0..8 {
            let pairs: Vec<_> = (0..3)
                .map(|level| {
                    let left = ((8 + index) >> level) & !1;
                    [tree[left], tree[left + 1]]
                })
                .collect();
            assert!(
                run(index, tree[8 + index], &pairs, tree[1])
                    .unwrap()
                    .unconstrained_reads
                    .is_empty()
            );
        }
    }

    /// The right leaf holds more claims than one absorb window of its list hash
    /// (`SIGNERS_WINDOW` blocks of one claim), so both that leaf and the parent
    /// rebuilding it run the window loop and then a non-empty tail, while the left
    /// leaf's list is a tail alone. Under a window everywhere, the loop would never
    /// execute and neither would the byte counter's base.
    #[test]
    fn aggregate_two_to_one() {
        leanvm_core::init_prover();
        let big = 2 * SIGNERS_WINDOW + 6;
        let signers = get_signers(SMALL_LEAF_SIZE + big);
        let left = prove_leaf(&signers[..SMALL_LEAF_SIZE]);
        let right = prove_leaf(&signers[SMALL_LEAF_SIZE..]);
        let children = [left, right];
        let node = aggregate(&children, vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        // `cpu::verify` accepts the same proof of the same statement.
        verify(unified_guest(), &node.public_input(), &node.proof).expect("node verifies natively");
        assert_eq!(node.xmss_signers.len(), SMALL_LEAF_SIZE + big);
    }

    fn da_rows(n_rows: usize, seed: u64) -> Vec<u64> {
        let mut rng = <rand::rngs::StdRng as rand::SeedableRng>::seed_from_u64(seed);
        (0..n_rows * (1 << DA_LOG_K))
            .map(|_| rand::Rng::random(&mut rng))
            .collect()
    }

    /// A LeanDA payload, proven without signatures and published in the
    /// statement. The node has to reach the native committer's root, and the
    /// aggregate has to verify against a statement that carries it.
    #[test]
    fn aggregate_with_a_da_payload() {
        leanvm_core::init_prover();
        let rows = da_rows(3, 97);

        let node = aggregate(&[], vec![], vec![], &rows, None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!(node.num_signature_claims(), 0);

        let (commitment, _) = lean_da::commit(&rows);
        assert_eq!(
            node.da_roots,
            vec![commitment.root],
            "the guest committed to something else"
        );
        let received = EthereumProof::from_bytes(&node.to_bytes()).unwrap();
        assert_eq!(received.da_commitments(), &[commitment.root]);
        received.verify().unwrap();
    }

    #[test]
    fn invalid_da_selections_are_rejected_before_building_the_proof() {
        let unknown = [[0xa5; 32]];
        assert_eq!(
            aggregate(
                &[],
                vec![],
                vec![],
                &[],
                Some(ClaimSelection {
                    signatures: &SignatureClaims::default(),
                    da_commitments: &unknown
                }),
                LOG_INV_RATE
            )
            .unwrap_err(),
            AggregationError::BlobNotCovered
        );
        let too_many: Vec<_> = (0..=MAX_DA_ROOTS).map(|i| [i as u8; 32]).collect();
        assert_eq!(
            aggregate(
                &[],
                vec![],
                vec![],
                &[],
                Some(ClaimSelection {
                    signatures: &SignatureClaims::default(),
                    da_commitments: &too_many
                }),
                LOG_INV_RATE
            )
            .unwrap_err(),
            AggregationError::TooLarge
        );
    }

    #[test]
    fn da_roots_accumulate_and_can_be_selected_or_omitted() {
        leanvm_core::init_prover();
        let signers = get_signers(SMALL_LEAF_SIZE);
        let mut children = Vec::new();
        for seed in [509, 510] {
            let rows = da_rows(1, seed);
            children.push(aggregate(&[], signing(&signers, 0), vec![], &rows, None, LOG_INV_RATE).unwrap());
        }
        let signatures = SignatureClaims {
            xmss: children[0].xmss_signers.clone(),
            lean_sphincs: children[0].lean_sphincs_signers.clone(),
        };
        let first = children[0].da_roots[0];
        let second = children[1].da_roots[0];
        assert_ne!(first, second);
        let mut both = vec![first, second];
        both.sort();
        for selected in [
            None,
            Some(vec![]),
            Some(vec![first]),
            Some(vec![second]),
            Some(vec![second, first, second]),
        ] {
            let node = aggregate(
                &children,
                vec![],
                vec![],
                &[],
                selected.as_deref().map(|roots| ClaimSelection {
                    signatures: &signatures,
                    da_commitments: roots,
                }),
                LOG_INV_RATE,
            )
            .unwrap();
            node.verify().unwrap();
            let mut expected = selected.unwrap_or_else(|| both.clone());
            expected.sort();
            expected.dedup();
            assert_eq!(node.da_roots, expected);
            assert_eq!(node.da_commitments_digest(), da_list_digest(&expected));
        }
        let repeated = aggregate(
            &[children[0].clone(), children[0].clone()],
            vec![],
            vec![],
            &[],
            None,
            LOG_INV_RATE,
        )
        .unwrap();
        repeated.verify().unwrap();
        assert_eq!(repeated.da_roots, vec![first]);
        let same_rows = da_rows(1, 509);
        let repeated_direct = aggregate(
            std::slice::from_ref(&repeated),
            vec![],
            vec![],
            &same_rows,
            None,
            LOG_INV_RATE,
        )
        .unwrap();
        repeated_direct.verify().unwrap();
        assert_eq!(repeated_direct.da_roots, vec![first]);

        let rows = da_rows(1, 511);
        let new_root = lean_da::commit(&rows).0.root;
        for selected in [vec![new_root], vec![first], vec![]] {
            let node = aggregate(
                &children,
                vec![],
                vec![],
                &rows,
                Some(ClaimSelection {
                    signatures: &signatures,
                    da_commitments: &selected,
                }),
                LOG_INV_RATE,
            )
            .unwrap();
            node.verify().unwrap();
            assert_eq!(node.da_roots, selected);
        }
        assert!(matches!(
            aggregate(
                &children,
                vec![],
                vec![],
                &rows,
                Some(ClaimSelection {
                    signatures: &signatures,
                    da_commitments: &[[0xa5; 32]]
                }),
                LOG_INV_RATE
            ),
            Err(AggregationError::BlobNotCovered)
        ));
        let direct = aggregate(&children, vec![], vec![], &rows, None, LOG_INV_RATE).unwrap();
        direct.verify().unwrap();
        let mut three = both.clone();
        three.push(new_root);
        three.sort();
        assert_eq!(direct.da_roots, three);
        let received = EthereumProof::from_bytes(&direct.to_bytes()).unwrap();
        received.verify().unwrap();
        let nested = aggregate(&[received, repeated], vec![], vec![], &[], None, LOG_INV_RATE).unwrap();
        nested.verify().unwrap();
        assert_eq!(nested.da_roots, three);
        let narrowed = aggregate(
            &[nested],
            vec![],
            vec![],
            &[],
            Some(ClaimSelection {
                signatures: &signatures,
                da_commitments: &[second],
            }),
            LOG_INV_RATE,
        )
        .unwrap();
        narrowed.verify().unwrap();
        assert_eq!(narrowed.da_roots, vec![second]);
        let dropped = aggregate(
            &[narrowed],
            vec![],
            vec![],
            &[],
            Some(ClaimSelection {
                signatures: &signatures,
                da_commitments: &[],
            }),
            LOG_INV_RATE,
        )
        .unwrap();
        dropped.verify().unwrap();
        assert!(dropped.da_roots.is_empty());
        assert_eq!(dropped.da_commitments_digest(), primitives::hash::hash(&[]));
        assert!(matches!(
            aggregate(
                &[dropped],
                vec![],
                vec![],
                &[],
                Some(ClaimSelection {
                    signatures: &signatures,
                    da_commitments: &[second]
                }),
                LOG_INV_RATE
            ),
            Err(AggregationError::BlobNotCovered)
        ));
        assert!(matches!(
            aggregate(
                &children,
                vec![],
                vec![],
                &[],
                Some(ClaimSelection {
                    signatures: &signatures,
                    da_commitments: &[[0xa5; 32]]
                }),
                LOG_INV_RATE
            ),
            Err(AggregationError::BlobNotCovered)
        ));
    }

    #[test]
    fn da_root_lists_merge_two_and_three() {
        leanvm_core::init_prover();
        let mut leaves = Vec::new();
        let mut expected = Vec::new();
        for seed in 600..605 {
            let rows = da_rows(1, seed);
            let leaf = aggregate(&[], vec![], vec![], &rows, None, LOG_INV_RATE).unwrap();
            expected.extend_from_slice(leaf.da_commitments());
            leaves.push(leaf);
        }
        let left = aggregate(&leaves[..2], vec![], vec![], &[], None, LOG_INV_RATE).unwrap();
        let right = aggregate(&leaves[2..], vec![], vec![], &[], None, LOG_INV_RATE).unwrap();
        assert_eq!(left.da_commitments().len(), 2);
        assert_eq!(right.da_commitments().len(), 3);
        let root = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).unwrap();
        let root = EthereumProof::from_bytes(&root.to_bytes()).unwrap();
        root.verify().unwrap();
        expected.sort();
        assert_eq!(root.num_signature_claims(), 0);
        assert_eq!(root.da_commitments().len(), 5);
        assert_eq!(root.da_commitments(), expected);
        assert_eq!(root.da_commitments_digest(), da_list_digest(&expected));

        let boundary: Vec<_> = (0..MAX_DA_ROOTS).map(|i| [i as u8; 32]).collect();
        check_da_roots(&boundary).unwrap();
    }

    #[test]
    fn da_guest_hashes_root_lists() {
        leanvm_core::init_prover();
        let (helpers, _) = include_str!("../guests/lean_ethereum.py")
            .split_once("\ndef main():")
            .unwrap();
        let source = format!(
            r#"{helpers}
def main():
    n_g = hint_witness("n")
    assert log(n_g) < MAX_DA_ROOTS + 1
    roots = HeapBuf((n_g * GEN) ** 4)
    for x in mul_range(1, n_g):
        root = roots * (x ** 4)
        hint_witness(root[0:4], "root")
    a, b = da_list_digest(roots, n_g)
    public = GEN ** 0
    assert public[1] == a
    assert public[GEN] == b
    return
"#
        );
        let guest = compile(&parse_with_replacements(&source, &placeholder_map(20)).unwrap());
        for n in 0..=MAX_DA_ROOTS {
            let roots: Vec<_> = (0..n)
                .map(|i| primitives::hash::hash(&(i as u64).to_le_bytes()))
                .collect();
            let mut hints = Hints::default();
            hints.push("n", vec![count(n)]);
            for root in &roots {
                hints.push("root", da_claim_cells(root));
            }
            let mut program = guest.clone();
            hints.install(&mut program);
            let public = pack_hash_state(&da_list_digest(&roots));
            let execution = program.execute(public).unwrap();
            assert!(execution.unconstrained_reads.is_empty(), "{n} roots");
        }
    }

    #[test]
    fn da_guest_covers_a_root_per_slot() {
        leanvm_core::init_prover();
        let (helpers, _) = include_str!("../guests/lean_ethereum.py")
            .split_once("\ndef main():")
            .unwrap();
        let source = format!(
            r#"{helpers}
def main():
    roots = HeapBuf(12)
    hint_witness(roots[0:12], "roots")
    n_slots = hint_witness("n_slots")
    assert log(n_slots) < 3
    cover = HeapBuf(4)
    # Adjacent signature slots must stay outside the DA writer's range.
    cover[1] = 1
    a, b, v0, v1 = cover_da_root(roots, cover * GEN, n_slots, GEN)
    digest = StackBuf(2)
    blake2s([a, b], [v0, v1], digest)
    public = GEN ** 0
    assert public[1] == digest[0]
    assert public[GEN] == digest[1]
    return
"#
        );
        let guest = compile(&parse_with_replacements(&source, &placeholder_map(20)).unwrap());
        let first = [0x13; 32];
        let second = [0x27; 32];
        let outside = [0x39; 32];
        let run = |slots: usize, index: F192, claimed: [u8; 32]| {
            let mut hints = Hints::default();
            hints.push(
                "roots",
                [
                    da_claim_cells(&first),
                    da_claim_cells(&second),
                    da_claim_cells(&outside),
                ]
                .concat(),
            );
            hints.push("n_slots", vec![count(slots)]);
            hints.push("da_index", vec![index]);
            let mut program = guest.clone();
            hints.install(&mut program);
            program.execute(pack_hash_state(&da_list_digest(&[claimed])))
        };
        assert!(run(2, count(0), first).unwrap().unconstrained_reads.is_empty());
        assert!(run(2, count(1), second).unwrap().unconstrained_reads.is_empty());
    }

    #[test]
    fn da_guest_accepts_committed_codewords() {
        leanvm_core::init_prover();
        let source = include_str!("../guests/lean_ethereum.py");
        let (helpers, _) = source.split_once("\ndef main():").unwrap();
        let source = format!(
            "{helpers}\ndef main():\n    _, squares = exponent_tables()\n    a, b, v0, v1 = da_verify(squares)\n    digest = StackBuf(2)\n    blake2s([a, b], [v0, v1], digest)\n    public = GEN ** 0\n    assert public[1] == digest[0]\n    assert public[GEN] == digest[1]\n    return\n"
        );
        let guest = compile(&parse_with_replacements(&source, &placeholder_map(20)).unwrap());
        let n_rows = 3usize;
        let codewords = lean_da::encode_rows(&da_rows(3, 101));
        let run = |words: &[u64]| {
            let (commitment, _) = lean_da::commit_codewords(words.to_vec());
            let public = pack_hash_state(&da_list_digest(&[commitment.root]));
            let mut hints = Hints::default();
            hints.push(
                "da_shape",
                vec![count(n_rows), count(n_rows.next_power_of_two().ilog2() as usize)],
            );
            for j in 0..CELLS_PER_ROW {
                for i in 0..n_rows {
                    let start = i * CODEWORD_SYMBOLS + j * CELL_SYMBOLS;
                    hints.push(
                        "da_symbols",
                        words[start..start + CELL_SYMBOLS]
                            .iter()
                            .map(|&w| F192::from(F64(w)))
                            .collect(),
                    );
                }
            }
            for block in lean_da::membership_vector(&commitment.root)
                .as_chunks::<CELL_SYMBOLS>()
                .0
            {
                hints.push("da_weights", block.to_vec());
            }
            let mut program = guest.clone();
            hints.install(&mut program);
            program.execute(public)
        };
        let honest = run(&codewords).unwrap();
        assert!(honest.unconstrained_reads.is_empty());
    }

    #[test]
    fn invalid_blob_sizes_are_rejected() {
        for symbols in [1, BLOB_SYMBOLS - 1, BLOB_SYMBOLS + 1, (DA_MAX_ROWS + 1) * BLOB_SYMBOLS] {
            let rows = vec![0; symbols];
            assert!(matches!(
                aggregate(&[], vec![], vec![], &rows, None, LOG_INV_RATE),
                Err(AggregationError::InvalidBlobSize { symbols: n }) if n == symbols
            ));
        }
    }

    /// The row count is a run-time parameter, so payloads of different heights
    /// must prove against the *same* bytecode and each reach its own committer's
    /// root. Powers of two and the counts between them alike: 3 pads to 4 and 5 to
    /// 8, exercising two different arms of the tree dispatch and a non-empty gap.
    #[test]
    fn da_row_count_is_a_run_time_parameter() {
        leanvm_core::init_prover();
        let signers = get_signers(SMALL_LEAF_SIZE);
        for n_rows in [1usize, 3, 4, 5] {
            let rows = da_rows(n_rows, 200 + n_rows as u64);
            let node =
                aggregate(&[], signing(&signers, 0), vec![], &rows, None, LOG_INV_RATE).expect("node aggregates");
            node.verify().expect("node verifies");
            let (commitment, _) = lean_da::commit(&rows);
            assert_eq!(node.da_roots, vec![commitment.root], "{n_rows} rows");
        }
    }

    /// What one blob-carrying proof costs, at the shape EIP-4844 and EIP-7594 fix.
    /// Reported, not asserted: run it by name when the shape or the sweep changes.
    #[test]
    #[ignore]
    fn da_blob_proof() {
        leanvm_core::init_prover();
        let signers = get_signers(SMALL_LEAF_SIZE);
        // One discarded proof: the first pays the flock circuit build and the
        // allocator's page faults, which would otherwise land entirely on the first row
        // count reported.
        warm_up();
        println!(
            "bytecode: {} instructions, DA_MAX_ROWS = {DA_MAX_ROWS}",
            unified_guest().prog.len()
        );
        let _ = aggregate_with_stats(&[], signing(&signers, 0), vec![], &da_rows(1, 7), None, LOG_INV_RATE);
        for n_rows in [1usize, 6, 14, 32] {
            let rows = da_rows(n_rows, 300 + n_rows as u64);
            let started = std::time::Instant::now();
            let (node, stats) = aggregate_with_stats(&[], signing(&signers, 0), vec![], &rows, None, LOG_INV_RATE)
                .expect("node aggregates");
            let elapsed = started.elapsed();
            let payload = n_rows * (1 << DA_LOG_K) * 8;
            println!(
                "{n_rows:>3} blobs ({:>5} KiB): {:>8.2?}  {:>6.0} KiB/s  cycles 2^{:.1}  mem 2^{:.1}  proof {:.0} KiB",
                payload / 1024,
                elapsed,
                payload as f64 / 1024.0 / elapsed.as_secs_f64(),
                (stats.cycles as f64).log2(),
                (stats.mem_used as f64).log2(),
                node.to_bytes().len() as f64 / 1024.0,
            );
        }
    }

    /// A leaf carrying no payload publishes the digest of an empty root list.
    #[test]
    fn no_payload_publishes_the_empty_root_list() {
        leanvm_core::init_prover();
        let signers = get_signers(SMALL_LEAF_SIZE);
        let node = prove_leaf(&signers);
        assert!(node.da_roots.is_empty());
        assert_eq!(node.da_commitments_digest(), primitives::hash::hash(&[]));
    }

    /// Claims left undeclared take duplicate slots. The first narrowing drops every
    /// claim on one message, the second all but one claim.
    #[test]
    fn a_node_may_publish_less_than_it_covers() {
        leanvm_core::init_prover();
        let at_a = get_signers(3);
        let at_b = get_signers_for(2, MESSAGE_B);
        let mut raw = signing(&at_a, 0);
        raw.extend(signing(&at_b, MESSAGE_B));
        let wide = aggregate(&[], raw, vec![], &[], None, LOG_INV_RATE).expect("the wide leaf aggregates");
        wide.verify().expect("the wide leaf verifies");
        assert_eq!(wide.xmss_signers.len(), 5);

        let narrowed = |wide: &EthereumProof, declare: &SignatureClaims| {
            aggregate(
                std::slice::from_ref(wide),
                vec![],
                vec![],
                &[],
                Some(ClaimSelection {
                    signatures: declare,
                    da_commitments: &[],
                }),
                LOG_INV_RATE,
            )
        };
        let only = |xmss: Vec<LeanXmssClaim>| SignatureClaims {
            xmss,
            lean_sphincs: vec![],
        };
        let on_b: Vec<LeanXmssClaim> = wide
            .xmss_signers
            .iter()
            .filter(|(_, message)| *message == message_for(MESSAGE_B))
            .cloned()
            .collect();
        assert_eq!(on_b.len(), 2);

        let narrow = narrowed(&wide, &only(on_b.clone())).expect("narrows to one message");
        narrow.verify().expect("the one-message narrowing verifies");
        assert_eq!(narrow.xmss_signers, on_b);

        let one = vec![(at_a[0].0, message())];
        let part = narrowed(&wide, &only(one.clone())).expect("narrows to one claim");
        part.verify().expect("the one-claim narrowing verifies");
        assert_eq!(part.xmss_signers, one);

        assert_eq!(
            narrowed(&wide, &SignatureClaims::default()).err(),
            Some(AggregationError::Empty),
            "a declaration has to publish something"
        );
        // A pubkey that signed A only, declared on B: the cache reuses pubkeys.
        assert_eq!(
            narrowed(&wide, &only(vec![(at_a[2].0, message_for(MESSAGE_B))])).err(),
            Some(AggregationError::NotCovered)
        );
        // A covered pubkey, against a message nobody signed.
        assert_eq!(
            narrowed(&wide, &only(vec![(at_a[0].0, message_for(MESSAGE_B + 1))])).err(),
            Some(AggregationError::NotCovered)
        );
    }

    /// A raw signature whose claim goes undeclared covers a duplicate slot.
    #[test]
    fn raw_signatures_may_go_undeclared() {
        leanvm_core::init_prover();
        let a = get_signers(1);
        let b = get_signers_for(1, MESSAGE_B);
        let mut raw = signing(&a, 0);
        raw.extend(signing(&b, MESSAGE_B));
        let claim_b = vec![(b[0].0, message_for(MESSAGE_B))];
        let sig = aggregate(
            &[],
            raw,
            vec![],
            &[],
            Some(ClaimSelection {
                signatures: &SignatureClaims {
                    xmss: claim_b.clone(),
                    lean_sphincs: vec![],
                },
                da_commitments: &[],
            }),
            LOG_INV_RATE,
        )
        .expect("the narrowing leaf aggregates");
        sig.verify().expect("it verifies");
        assert_eq!(sig.xmss_signers, claim_b);
    }

    /// Two messages in one tree. Signer `i` holds the same pubkey under both, at
    /// different leaf indices, so its claims on B are distinct from those on A; the
    /// left leaf holds one message, the right both, and the node needs a duplicate
    /// slot for the claim both leaves cover.
    #[test]
    fn aggregate_two_messages() {
        leanvm_core::init_prover();
        let at_a = get_signers(4);
        let at_b = get_signers_for(2, MESSAGE_B);
        assert_eq!(at_a[0].0, at_b[0].0, "the cache reuses pubkeys across messages");
        assert_ne!(at_a[0].1.leaf_index, at_b[0].1.leaf_index);
        let left = aggregate(&[], signing(&at_a[..3], 0), vec![], &[], None, LOG_INV_RATE).expect("left");
        let mut right_raw = signing(&at_a[2..], 0);
        right_raw.extend(signing(&at_b, MESSAGE_B));
        let right = aggregate(&[], right_raw, vec![], &[], None, LOG_INV_RATE).expect("right");
        right.verify().expect("the two-message leaf verifies");
        // A pubkey of `left` signing a second message is a second claim of that pubkey.
        let crossed = aggregate(
            std::slice::from_ref(&left),
            signing(&at_b[..1], MESSAGE_B),
            vec![],
            &[],
            None,
            LOG_INV_RATE,
        )
        .expect("one pubkey under two messages aggregates");
        crossed.verify().expect("the crossed node verifies");
        let of_first: Vec<lean_xmss::Message> = crossed
            .xmss_signers
            .iter()
            .filter(|(pubkey, _)| *pubkey == at_a[0].0)
            .map(|(_, message)| *message)
            .collect();
        assert_eq!(of_first, vec![message(), message_for(MESSAGE_B)]);
        assert_eq!(crossed.xmss_signers.len(), 4);
        let node = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).expect("node");
        node.verify().expect("the two-message node verifies");
        let mut expected = signing(&at_a, 0);
        expected.extend(signing(&at_b, MESSAGE_B));
        let mut expected: Vec<LeanXmssClaim> = expected
            .into_iter()
            .map(|(pubkey, message, _)| (pubkey, message))
            .collect();
        expected.sort();
        assert_eq!(node.xmss_signers, expected);
    }

    #[test]
    fn aggregate_overlapping_signers() {
        leanvm_core::init_prover();
        let signers = get_signers(40);
        let left = prove_leaf(&signers[..25]);
        let right = prove_leaf(&signers[15..]);
        let node = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!(node.xmss_signers.len(), 40);
        assert!(node.xmss_signers.windows(2).all(|w| w[0] < w[1]));
    }

    /// Three levels, both schemes. The leanSPHINCS claims are rebuilt twice over, once
    /// into each node and again into the root, and the two nodes share one claim,
    /// so the root needs a leanSPHINCS duplicate slot for a claim it never saw
    /// directly. The root also adds a raw signature of each scheme alongside its
    /// children.
    #[test]
    #[ignore]
    fn aggregate_three_levels() {
        leanvm_core::init_prover();
        let signers = get_signers(4 * SMALL_LEAF_SIZE);
        let claims = get_lean_sphincs_signers(5);
        let leaf = |index: usize, lean_sphincs: &[RawSphincs]| {
            aggregate(
                &[],
                signing(&signers[index * SMALL_LEAF_SIZE..(index + 1) * SMALL_LEAF_SIZE], 0),
                lean_sphincs.to_vec(),
                &[],
                None,
                LOG_INV_RATE,
            )
            .expect("leaf aggregates")
        };
        let node = |children: &[EthereumProof]| {
            aggregate(children, vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates")
        };
        // Claim 1 is under both nodes; claim 4 arrives raw at the root, and so
        // do two leanXMSS signatures of a second message, claims its children never
        // carried.
        let left = node(&[leaf(0, &claims[..2]), leaf(1, &[])]);
        let right = node(&[leaf(2, &claims[1..3]), leaf(3, &[])]);
        let root = aggregate(
            &[left, right],
            signing(&get_signers_for(2, MESSAGE_B), MESSAGE_B),
            claims[4..].to_vec(),
            &[],
            None,
            LOG_INV_RATE,
        )
        .expect("root aggregates");
        root.verify().expect("root verifies");
        assert_eq!(root.xmss_signers.len(), 4 * SMALL_LEAF_SIZE + 2);
        assert_eq!(
            root.lean_sphincs_signers.len(),
            4,
            "claims 0, 1, 2 and 4, the repeat merged"
        );
        assert!(root.xmss_signers.windows(2).all(|w| w[0] < w[1]));
        assert!(root.lean_sphincs_signers.windows(2).all(|w| w[0] < w[1]));
    }

    #[test]
    #[ignore]
    fn aggregate_round_trips_through_the_wire() {
        leanvm_core::init_prover();
        let signers = get_signers(2 * SMALL_LEAF_SIZE);
        let left = prove_leaf(&signers[..SMALL_LEAF_SIZE]);
        let right = prove_leaf(&signers[SMALL_LEAF_SIZE..]);
        // Mixed, so both published lists are non-empty.
        let node = aggregate(
            &[left, right],
            vec![],
            get_lean_sphincs_signers(3),
            &[],
            None,
            LOG_INV_RATE,
        )
        .expect("node");
        node.verify().expect("the honest node verifies");

        assert_eq!(
            EthereumProof::from_bytes(&node.to_bytes())
                .expect("round trip")
                .to_bytes(),
            node.to_bytes(),
            "the wire format round-trips, recomputed claim values included"
        );
        let without = EthereumProof::from_bytes_without_pubkeys(
            &node.to_bytes_without_pubkeys(),
            SignatureClaims {
                xmss: node.xmss_signers.clone(),
                lean_sphincs: node.lean_sphincs_signers.clone(),
            },
        )
        .expect("round trip");
        without.verify().expect("a caller-supplied signer set verifies");
    }

    /// The all-zeros fast path in `DeferredClaim::recompute` must agree with the
    /// two full passes it replaces, or every leaf would verify against the wrong
    /// statement.
    #[test]
    fn leaf_claim_matches_the_general_path() {
        let klog = flock::hash::K_LOG;
        let leaf = DeferredClaim::leaf();
        let general = {
            let bytecode_value = mle_eval_par(stacked_bytecode(), &leaf.bytecode_point);
            let eq_r = pcs::whir::build_eq_table_ext(&leaf.matrix_point[..klog]);
            let eq_c = pcs::whir::build_eq_table_ext(&leaf.matrix_point[klog..]);
            let (matrix_a_value, matrix_b_value) = flock::hash::bilinear_walk_pair(&eq_r, &eq_c);
            (bytecode_value, matrix_a_value, matrix_b_value)
        };
        assert_eq!((leaf.bytecode_value, leaf.matrix_a_value, leaf.matrix_b_value), general);
    }

    /// The scalar verifier's deferred values are the prover's, away from the leaf shortcut.
    #[test]
    fn scalar_deferred_claim_matches_the_prover() {
        let mut rng = StdRng::seed_from_u64(7);
        let mut point = |len: usize| -> Vec<F192> {
            let limbs = (0..len).map(|_| rand::Rng::random::<(u64, u64, u64)>(&mut rng));
            limbs.map(|(c0, c1, c2)| F192::new(c0, c1, c2)).collect()
        };
        let (bytecode_point, matrix_point) = (point(bytecode_vars()), point(2 * flock::hash::K_LOG));
        assert_eq!(
            DeferredClaim::recompute_scalar(bytecode_point.clone(), matrix_point.clone()),
            DeferredClaim::recompute(bytecode_point, matrix_point)
        );
    }

    /// The scalar verifier derives a root's membership vector, and the list digest over it, as `lean_da` does.
    #[test]
    fn scalar_da_digest_matches_lean_da() {
        let roots = [[0u8; 32], [0xff; 32], std::array::from_fn(|i| 7 * i as u8 + 1)];
        for root in &roots {
            let vector = lean_da::membership_vector(root);
            let scalar = verifier::da::membership_vector(root);
            assert_eq!(scalar.iter().copied().map(from_scalar).collect::<Vec<_>>(), vector);
            assert_eq!(verifier::da::vector_digest(&scalar), lean_da::vector_digest(&vector));
        }
        for count in 0..=roots.len() {
            assert_eq!(
                verifier::da::list_digest(&roots[..count]),
                da_list_digest(&roots[..count])
            );
        }
    }

    /// A randomizer whose digest is not a codeword used to panic the hint builder;
    /// it is a typed error now, and the abandoned builder leaves nothing behind.
    #[test]
    fn malformed_raw_signature_is_an_error() {
        let message = message();
        let pk = LeanXmssPublicKey {
            merkle_root: [0; lean_xmss::N],
            public_param: [0; lean_xmss::PUBLIC_PARAM_LEN],
        };
        let randomizer = (0..=u8::MAX)
            .map(|byte| [byte; lean_xmss::RANDOMIZER_LEN])
            .find(|r| {
                let digest = lean_xmss::message_digest(&pk.public_param, 0, 0, r, &message);
                lean_xmss::codeword(&digest).is_none()
            })
            .expect("some randomizer fails the codeword");
        let layer = lean_xmss::LayerSignature {
            randomizer,
            chain_values: [[0; lean_xmss::N]; lean_xmss::V],
            path: [[0; lean_xmss::N]; lean_xmss::LAYER_HEIGHT],
        };
        let sig = LeanXmssSignature {
            leaf_index: 0,
            bottom: layer.clone(),
            top: layer,
        };

        assert_eq!(
            lean_xmss_hints(&pk, &sig, &message).err(),
            Some(AggregationError::MalformedRawSignature)
        );
        assert_eq!(
            aggregate(&[], vec![(pk, message, sig)], vec![], &[], None, LOG_INV_RATE).err(),
            Some(AggregationError::MalformedRawSignature)
        );
    }

    /// The same for a leanSPHINCS claim, whose witness walk is equally fallible: a
    /// counter that does not encode has no witness, and that is an error rather
    /// than a panic inside the prover.
    #[test]
    fn malformed_raw_lean_sphincs_signature_is_an_error() {
        let (public_key, signed, mut signature) = get_lean_sphincs_signers(1).pop().expect("one signer");
        signature.counter ^= 1;
        assert!(lean_sphincs::verify(&public_key, &signed, &signature).is_err());
        let raw = vec![(public_key, signed, signature)];
        assert_eq!(
            aggregate(&[], vec![], raw, &[], None, LOG_INV_RATE).err(),
            Some(AggregationError::MalformedRawSignature)
        );
    }

    /// Every `BLAKE2s` the guest itself runs reads a metadata cell an earlier
    /// instruction of its own function wrote: a `SET` for a compile-time counter,
    /// an `XOR` for a window's base plus its offset. An unwritten cell is
    /// prover-chosen (write-once memory constrains only what something writes), so
    /// a compression whose metadata nothing writes would hand the prover that
    /// hash's byte counter and both flags, and every guest digest rests on those
    /// being the ones the scheme specifies.
    ///
    /// This is a scan by pc, not a dominance check: a writer sitting in a branch
    /// nobody took would satisfy it. What makes naming such a cell impossible is
    /// `FnLower::scoped` reverting the constant pool at every join, and the
    /// `blake2s_default_iv_*` tests are what guard that, by proving both paths.
    #[test]
    fn every_guest_blake2s_metadata_cell_is_written_first() {
        use leanvm_core::cpu::{DerefMode, Op};

        // Which frame cell an instruction writes, if any. A `DEREF` in cell mode is
        // bidirectional under write-once, so its local operand counts as a write.
        let written = |op: &Op| match *op {
            Op::Set { o, .. } => vec![o],
            Op::Xor { c, .. } | Op::Mul { c, .. } => vec![c],
            Op::Deref { o3, mode, .. } => {
                if mode == DerefMode::Cell {
                    vec![o3]
                } else {
                    vec![]
                }
            }
            Op::Blake2s { out, .. } => vec![out, out + 1],
            Op::Jump { .. } => vec![],
        };
        let program = unified_guest();
        let mut unwritten = Vec::new();
        for (name, entry, len) in &program.fn_ranges {
            let range = *entry as usize..(*entry + *len) as usize;
            for pc in range.clone() {
                let Op::Blake2s { md, .. } = program.prog[pc] else {
                    continue;
                };
                if !program.prog[range.start..pc].iter().any(|op| written(op).contains(&md)) {
                    unwritten.push(format!("{name} pc {pc} md fp[{md}]"));
                }
            }
        }
        assert!(unwritten.is_empty(), "metadata cell never written: {unwritten:?}");
    }
}
