//! Recursive aggregation of XMSS and SPHINCS signatures: one bytecode
//! (`guests/aggregate.py`) for every node of an aggregation tree.
//!
//! A node verifies `n_raw_xmss` XMSS signatures, `n_raw_sphincs` SPHINCS
//! signatures and `n_children` sub-proofs **of this same bytecode**, and
//! publishes the sorted deduplicated union of their signer sets. The XMSS
//! signers are grouped by epoch, each group
//! carrying its own message. A SPHINCS
//! signer carries its own message, so that half of the statement is a list of
//! `(key, message)` pairs. Coverage is what carries the security claim: a write-once slot per
//! declared signer, written once by each raw signature and each child key, plus
//! a final count, so every declared signer is backed by a real signature or a
//! verified child.
//!
//! Those slots are one contiguous region per XMSS epoch group and one for
//! SPHINCS, so the one range check a write already needs also keeps a
//! signature off another group's declared keys, of either scheme: that is what
//! makes the published split mean which scheme verified which key against
//! which `(epoch, message)`, at every level of the tree.
//!
//! A duplicate slot sits outside the prefix the digest hashes, so a key in one is
//! covered and not claimed. `aggregate`'s `declare` rests on that, the table also
//! holding undeclared groups so a whole `(epoch, message)` can go unpublished.
//! A child's groups need
//! not equal its parent's: a hinted map, checked by the guest, ties each
//! non-empty child group to a parent group with the same epoch and message,
//! so a parent's list is the union of what sits below it. An XMSS slot holds the
//! key's two cells and a SPHINCS slot four, its key and its message, so the
//! guest reads each SPHINCS signature's message out of the slot it verifies.
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
//! the root's are discharged natively, by [`AggregateSignature::verify`].
//!
//! `gen_verify` derives the guest's whole witness for a child from the real
//! `cpu::layout` of the inner program and the summary of a real `cpu::verify`
//! run, so there is no hand-mirrored copy of the protocol to drift.

use bincode::Options as _;
use pcs::whir::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use lean_compiler::{compile, parse_with_replacements};
use lean_vm::cpu::{Program, prove, verify};
use lean_vm::leaf::{Block, Coord};
use lean_vm::transcript::FiatShamirState;
use primitives::field::{F64, F192, G, g_pow};
use primitives::multilinear::mle_eval_par;
use xmss::{XmssPublicKey, XmssSignature};

use sphincs::{SphincsPublicKey, SphincsSignature};

/// One SPHINCS claim: a key, and the message it signed. Where an XMSS group
/// shares one message, every SPHINCS signer carries its own.
pub type SphincsSigner = (SphincsPublicKey, sphincs::Message);

/// The XMSS signers sharing one epoch: the epoch, the message they all signed
/// at it, and their strictly sorted keys.
pub type XmssGroup = (xmss::Epoch, xmss::Message, Vec<XmssPublicKey>);

/// Why the guest reads every `q_flock` slot claim's instance point off `chi`: a
/// virtual value column is referenced only by its own table's bus blocks, which
/// the table sumcheck settles, so no framework block can raise one at `zeta`.
const VALCOL_FRAMEWORK: &str = "a framework block must not reference a virtual value column";
const RECURSION_AGG_LABEL: &[u8] = b"leanvm/recursion-aggregation/v1";
const SIGNERS_LABEL: &[u8] = b"leanvm/aggregation-signers/v1";

/// The most earlier aggregates one [`aggregate`] call can take, so the arity of
/// an aggregation tree.
pub const MAX_RECURSIONS: usize = 16;

/// The cap on [`AggregateSignature::num_total_sigs`], both schemes together, counting
/// the coverage table's duplicate slots. Exclusive: exactly this many is already
/// too many.
///
/// It is where the coverage indices' range check has to sit to stay below
/// `2^MIN_LOG_MEM`, so the bound means the same at every announced memory size.
/// The guest checks it against a COMPILE-TIME bound, so raising it past
/// `2^MIN_LOG_MEM` fails the build rather than weakening the index bound.
pub const MAX_KEYS: usize = 1 << 16;

/// The most [`XmssGroup`]s one aggregate can carry: headroom over the few epochs
/// expected in practice. An empty group is in-circuit unprovable, its list hash
/// having no valid window split, so this is a bound on cost, not on soundness.
pub const MAX_EPOCHS: usize = 1024;

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
// The widest list is one block a claim, so at most MAX_KEYS blocks, of which the
// last is absorbed apart. The set's own string is 2 + 2·MAX_EPOCHS blocks, hashed
// the same way, so it needs the bound too.
const _: () = assert!((MAX_KEYS - 1) / SIGNERS_WINDOW < SIGNERS_MAX_WINDOWS);
const _: () = assert!((2 * MAX_EPOCHS + 1) / SIGNERS_WINDOW < SIGNERS_MAX_WINDOWS);
// The guest decomposes a count into SIGNERS_COUNT_BITS bits and shifts the result
// left to make a byte counter, so a count has to fit and the shift must not reduce.
const SIGNERS_COUNT_BITS: u32 = MAX_KEYS.ilog2();
const _: () = assert!(MAX_KEYS.is_power_of_two() && 2 * MAX_EPOCHS + 2 < 1 << SIGNERS_COUNT_BITS);
const _: () = assert!(SIGNERS_COUNT_BITS + 6 + SIGNERS_WINDOW.ilog2() <= 64);

// The guest bakes a bytecode claim's width from `N_TUPLE_BITS` while `bytecode_vars`
// reads it off the stacked table, which is `N_BYTECODE_SELECTORS` wide. Two constants
// that happen to agree: were they to drift, a leaf's claim point would be one length in
// the guest and another in the statement, and nothing else would notice.
const _: () = assert!(lean_vm::leaf::N_TUPLE_BITS == lean_vm::leaf::N_BYTECODE_SELECTORS);
// The epoch fills a tweak's four-byte index field, so a longer lifetime would
// need a weight per bit that `xmss::make_tweak` cannot express.
const _: () = assert!(xmss::LOG_LIFETIME <= 32);
// The guest's `WOTS_PK_BLOCKS = (2 + V) / 4` truncates, so a bad `V` would drop
// the last tips.
const _: () = assert!((2 + xmss::V).is_multiple_of(4));
// The SPHINCS side of the same shape. `SP_LEAF_BLOCKS = (2 + V) / 4` and
// `SP_ROOT_BLOCKS = (2 + NUM_FTS_TREES) / 4` truncate, and a truncated loop
// would leave the last tips or roots out of the hash while the signature still
// carries them: revealed values no longer bound by the leaf they belong to.
const _: () = assert!((2 + sphincs::V).is_multiple_of(4));
const _: () = assert!((2 + sphincs::NUM_FTS_TREES).is_multiple_of(4));
// The guest reads the message digest's bits out of three 64-bit lanes, and a
// dynamically sized `HeapBuf` gets no compile-time index check, so a wider
// digest would read leaf indices from cells nothing writes.
const _: () = assert!(sphincs::DIGEST_BITS <= 3 * 64);
// Every tweak field the guest packs must stay inside the byte range the native
// `enc` gives it: `tau` at bit 16 below `p` at 48, `p` below the 64-bit lane
// boundary, and `j` inside its four bytes at bit 80.
const _: () = assert!(sphincs::H <= 32);
const _: () = assert!(sphincs::CHAIN_LEN * sphincs::V < 1 << 16);
const _: () = assert!(sphincs::A <= 32 && sphincs::HEIGHTS[0] <= 32);

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

/// A domain-separating two-cell tag: it leads the hashed string of a signer set,
/// so that string cannot be read as either list's or as a Fiat-Shamir state.
fn domain_tag(label: &[u8]) -> [F192; 2] {
    pack_state(FiatShamirState::from_label(label).state())
}

/// A 16-byte native value as one canonical 128-bit cell.
fn pack_16_bytes(bytes: &[u8]) -> F192 {
    let word_at = |offset: usize| u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap());
    F192::new(word_at(0), word_at(8), 0)
}

/// A public key as the two cells the guest hashes and `verify_sig` reads: the
/// root then the public parameter. Both schemes lay a key out the same way, and
/// the statement keeps them in separate lists rather than telling them apart by
/// their bytes.
fn key_cells(pk: &XmssPublicKey) -> [F192; 2] {
    [pack_16_bytes(&pk.merkle_root), pack_16_bytes(&pk.public_param)]
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
/// agree with them (`sphincs_list_digest` in the guest). A list is never empty
/// here: a group holds at least one key, and both claim lists are guarded at the
/// call, since the guest hashes an empty one without a split at all.
fn signers_split(blocks: usize) -> Vec<F192> {
    assert!(blocks > 0, "an empty list has no window split");
    let leading = blocks - 1;
    vec![count(leading / SIGNERS_WINDOW), count(leading % SIGNERS_WINDOW)]
}

/// One epoch group's declared keys under plain BLAKE2s: 32 bytes a key, so the
/// hashed string is `32n` bytes and only its last block is partial. The guest
/// computes this same digest a window of blocks at a time (`key_list_digest`).
fn key_list_digest(keys: &[XmssPublicKey]) -> [F192; 2] {
    let cells = keys.iter().flat_map(key_cells);
    pack_hash_state(&primitives::hash::hash(&cell_bytes(cells)))
}

/// The declared SPHINCS claims under plain BLAKE2s: one 64-byte block per claim,
/// its key then the message it signed, so the hashed string is exactly `64n` bytes
/// and an empty list hashes the empty string. The guest computes this same digest a
/// window of blocks at a time (`sphincs_list_digest`).
fn sphincs_list_digest(signers: &[SphincsSigner]) -> [F192; 2] {
    let cells = signers.iter().flat_map(sphincs_signer_cells);
    pack_hash_state(&primitives::hash::hash(&cell_bytes(cells)))
}

/// A SPHINCS signer as the four cells the guest hashes and `verify_sig_sphincs`
/// reads: the key, then the message that key signed.
fn sphincs_signer_cells((pk, message): &SphincsSigner) -> [F192; 4] {
    [
        pack_16_bytes(&pk.root),
        pack_16_bytes(&pk.public_param),
        pack_16_bytes(&message[..16]),
        pack_16_bytes(&message[16..]),
    ]
}

/// One XMSS tweak as the cell the guest adds into: `xmss::make_tweak`'s own
/// output, packed. The guest holds no byte layout of its own, building a tweak
/// as this constant half plus one [`tweak_index_weight`] per set epoch bit, so a
/// field that moves in `make_tweak` moves both halves together.
fn tweak_cell(tweak_type: u8, sub_position: u32) -> F192 {
    pack_16_bytes(&xmss::make_tweak(tweak_type, sub_position, 0))
}

/// What bit `b` of the epoch weighs in a tweak's index field, so an index is its
/// set bits summed. The one property of the layout this assumes is that the
/// index field is linear in the index, which a leaf proof at the benchmark epoch
/// exercises for every bit.
fn tweak_index_weight(b: usize) -> F192 {
    pack_16_bytes(&xmss::make_tweak(0, 0, 1 << b))
}

/// The signer-set digest: plain BLAKE2s of one byte string, laid out in whole
/// 64-byte blocks so the guest can absorb it four cells at a time
/// (`signer_set_digest` there). A tag block carries both list lengths, the next
/// block the SPHINCS list's own digest, and then two blocks a group: its `(epoch,
/// count, message)`, then its key list's digest. Leading with both lengths makes
/// the encoding prefix-free, so no set's string is a prefix of another's, and the
/// digest binds its own lengths, the groups' epochs and messages, and every split.
/// The two list digests carry the bulk, each a stock hash of its own
/// ([`key_list_digest`], [`sphincs_list_digest`]).
fn signers_hash(xmss_signers: &[XmssGroup], sphincs_signers: &[SphincsSigner]) -> [F192; 2] {
    let tag = domain_tag(SIGNERS_LABEL);
    let mut cells = vec![tag[0], tag[1], count(xmss_signers.len()), count(sphincs_signers.len())];
    let sphincs = sphincs_list_digest(sphincs_signers);
    cells.extend([sphincs[0], sphincs[1], F192::ZERO, F192::ZERO]);
    for (epoch, message, keys) in xmss_signers {
        cells.extend([
            F192::new(*epoch as u64, 0, 0),
            count(keys.len()),
            pack_16_bytes(&message[..16]),
            pack_16_bytes(&message[16..]),
        ]);
        let keys = key_list_digest(keys);
        cells.extend([keys[0], keys[1], F192::ZERO, F192::ZERO]);
    }
    pack_hash_state(&primitives::hash::hash(&cell_bytes(cells)))
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

    /// Evaluate the three fixed polynomials at `bytecode_point` / `matrix_point`.
    fn recompute(bytecode_point: Vec<F192>, matrix_point: Vec<F192>) -> Result<Self, AggregateVerifyError> {
        let klog = flock::hash::K_LOG;
        if bytecode_point.len() != bytecode_vars() || matrix_point.len() != 2 * klog {
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
            let sp = tracing::info_span!("bytecode mle").entered();
            let value = mle_eval_par(stacked_bytecode(), &bytecode_point);
            drop(sp);
            value
        };
        let sp = tracing::info_span!("matrix walk").entered();
        let eq_r = pcs::whir::build_eq_table_ext(&matrix_point[..klog]);
        let eq_c = pcs::whir::build_eq_table_ext(&matrix_point[klog..]);
        let (matrix_a_value, matrix_b_value) = flock::hash::bilinear_walk_pair(&eq_r, &eq_c);
        drop(sp);
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

/// The statement's fixed header, ahead of the deferred cells: the seed and
/// the signer-set digest, which itself binds the epoch groups and every
/// count. Fed to the guest as `STMT_HEADER`, so the two cannot drift.
const STATEMENT_HEADER: usize = 4;

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
/// each child's `(epoch, message)` groups, bound by the signer-set digest,
/// onto its parent's list.
///
/// Fixed-length preimage, so a plain BLAKE2s, with no domain tag of its own: the
/// header leads with the environment digest, which binds this bytecode and
/// flock's R1CS and so already separates the preimage from every other use of
/// BLAKE2s here. The header is hashed as the canonical cells it already is (two
/// lanes each, whence the assert, the guest being unable to hash a third), then
/// all three lanes of each deferred cell.
fn statement_digest(signers_hash: [F192; 2], defer: &DeferredClaim) -> [F192; 2] {
    let seed = lean_vm::cpu::fs_seed(unified_guest());
    let header = [seed[0], seed[1], signers_hash[0], signers_hash[1]];
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

/// A proof that every key in [`Self::xmss_signers`] signed its group's message
/// at its group's epoch under XMSS, and that every `(key, message)` in
/// [`Self::sphincs_signers`] is a valid SPHINCS signature.
///
/// The two lists are everything the aggregate covers, signed directly into it or
/// carried up from one below, and separate because the proof says which scheme
/// verified which key (the module docs give the coverage argument). Until
/// [`Self::verify`] returns `Ok` they are claims, not attestation, and even then
/// the epochs and messages are the prover's, so a caller that reads either list
/// as attestation of something must compare it against what it expected.
///
/// **Neither length counts signers, only claims.** One key may appear in several
/// XMSS groups or under several SPHINCS messages, so a committee threshold has
/// to count distinct keys itself.
#[derive(Clone, Debug)]
pub struct AggregateSignature {
    /// The XMSS signers: strictly increasing epochs,
    /// each group non-empty and strictly sorted. May be empty, but not
    /// together with `sphincs_signers`; the claims of both together are
    /// strictly fewer than [`MAX_KEYS`].
    xmss_signers: Vec<XmssGroup>,
    /// Strictly sorted and deduplicated on the whole `(key, message)` pair.
    sphincs_signers: Vec<SphincsSigner>,
    /// What this aggregate defers to whoever discharges it: its parent, in
    /// circuit, or [`Self::verify`], natively.
    defer: DeferredClaim,
    proof: lean_vm::cpu::Proof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregateVerifyError {
    /// The signer set is empty, unsorted, holds a duplicate, or has [`MAX_KEYS`] keys or more.
    MalformedSignerSet,
    /// A deferred claim's point has the wrong number of coordinates.
    MalformedClaim,
    /// The bytes are not a valid encoding of an aggregate.
    MalformedEncoding,
    /// The snark itself did not verify.
    Snark(lean_vm::cpu::CpuError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregationError {
    /// Two claims at one epoch, raw or through children, carry different
    /// messages: within an aggregate the message is a function of the epoch.
    ConflictingMessages,
    /// The union of the epochs, over the raw signatures and the children,
    /// exceeds [`MAX_EPOCHS`].
    TooManyEpochs,
    /// A child aggregate does not verify.
    InvalidChild(AggregateVerifyError),
    /// No signer set to publish: no contributions, or an empty declaration.
    Empty,
    /// A declared claim is not one the contributions cover. A claim is a key, an
    /// epoch and a message, so another epoch or another message is another claim.
    NotCovered,
    /// A raw signature's randomness does not decode to a target-sum encoding,
    /// so there is no witness to build for it.
    MalformedRawSignature,
    /// More than [`MAX_RECURSIONS`] children, or [`MAX_KEYS`] signers or more
    /// once the duplicate slots are counted.
    TooLarge,
    /// `log_inv_rate` is outside the range the WHIR configuration accepts.
    InvalidRate { log_inv_rate: usize },
    /// A child's committed witness falls outside the opening arms the guest was
    /// compiled with. Small aggregates are padded up to the floor, so this means
    /// a child too big: more signatures than one node can hold.
    ChildOutOfRange { log_committed: usize },
}

impl std::fmt::Display for AggregateVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedSignerSet => write!(f, "malformed signer set"),
            Self::MalformedClaim => write!(f, "malformed deferred claim"),
            Self::MalformedEncoding => write!(f, "not a valid aggregate encoding"),
            Self::Snark(e) => write!(f, "the snark did not verify: {e:?}"),
        }
    }
}

impl std::error::Error for AggregateVerifyError {}

impl std::fmt::Display for AggregationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConflictingMessages => write!(f, "two claims at one epoch carry different messages"),
            Self::TooManyEpochs => write!(f, "more than MAX_EPOCHS ({MAX_EPOCHS}) epochs"),
            Self::InvalidChild(_) => write!(f, "invalid child aggregate"),
            Self::Empty => write!(f, "no signer set to publish"),
            Self::NotCovered => write!(f, "a declared claim is not covered by the children and raw signatures"),
            Self::MalformedRawSignature => write!(f, "a raw signature does not decode to a target-sum encoding"),
            Self::TooLarge => {
                write!(
                    f,
                    "more than MAX_RECURSIONS ({MAX_RECURSIONS}) children, or MAX_KEYS ({MAX_KEYS}) claims or more"
                )
            }
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
        }
    }
}

impl std::error::Error for AggregationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidChild(e) => Some(e),
            _ => None,
        }
    }
}

/// Everything but the signer set, which a receiver may already hold.
type WireCore = (Vec<F192>, Vec<F192>, lean_vm::cpu::Proof);

/// The signer lists as [`AggregateSignature::to_bytes`] writes them: the XMSS
/// groups, then the SPHINCS claims.
pub type WireKeys = (Vec<XmssGroup>, Vec<SphincsSigner>);

/// The wire encoding: bincode's fixed-width integers, as the free functions use,
/// but rejecting trailing bytes, which they do not. Without that an accepted
/// aggregate has unboundedly many encodings, so anything downstream that dedupes
/// or indexes on the serialized bytes can be made to see one aggregate as many.
fn wire() -> impl bincode::Options {
    bincode::DefaultOptions::new().with_fixint_encoding()
}

/// Reject a signer set that the coverage argument does not cover: strict sorting
/// within each list is what stops one signer being counted many times: the XMSS
/// list's length is a count of distinct `(epoch, key)` claims, the SPHINCS
/// list's of distinct `(key, message)` claims. The epoch groups are strictly
/// increasing, non-empty (an absent epoch is an absent group, the one
/// encoding of each set) and at most [`MAX_EPOCHS`]. Either list may be empty;
/// both may not. [`MAX_KEYS`] is exclusive here, as in the guest.
fn check_signer_set(xmss_signers: &[XmssGroup], sphincs_signers: &[SphincsSigner]) -> Result<(), AggregateVerifyError> {
    let total = xmss_signers.iter().map(|(_, _, keys)| keys.len()).sum::<usize>() + sphincs_signers.len();
    if total == 0
        || total >= MAX_KEYS
        || xmss_signers.len() > MAX_EPOCHS
        || !xmss_signers.windows(2).all(|w| w[0].0 < w[1].0)
        || xmss_signers
            .iter()
            .any(|(_, _, keys)| keys.is_empty() || !keys.windows(2).all(|w| w[0] < w[1]))
        || !sphincs_signers.windows(2).all(|w| w[0] < w[1])
    {
        return Err(AggregateVerifyError::MalformedSignerSet);
    }
    Ok(())
}

impl AggregateSignature {
    /// This aggregate's own public statement, as the VM publishes it.
    fn public_input(&self) -> [F192; 2] {
        statement_digest(signers_hash(&self.xmss_signers, &self.sphincs_signers), &self.defer)
    }

    /// Strictly increasing epochs, each group non-empty and strictly sorted.
    /// May be empty, but not together with [`Self::sphincs_signers`].
    pub fn xmss_signers(&self) -> &[XmssGroup] {
        &self.xmss_signers
    }

    /// Strictly sorted and deduplicated on the whole `(key, message)` pair.
    pub fn sphincs_signers(&self) -> &[SphincsSigner] {
        &self.sphincs_signers
    }

    /// The declared claims, as many as the coverage table's declared slots.
    ///
    /// NOT a count of distinct signers: a SPHINCS key may hold several claims,
    /// one per message it signed, and an XMSS key one per epoch it signed at
    /// (see the notes on the two lists). A caller that wants signers has to
    /// deduplicate by key itself.
    pub fn num_total_sigs(&self) -> usize {
        self.xmss_signers.iter().map(|(_, _, keys)| keys.len()).sum::<usize>() + self.sphincs_signers.len()
    }

    /// The wire format: the signer set (each group with its epoch and
    /// message), the two deferred points, and the VM proof. The claim *values* are not transmitted;
    /// [`Self::from_bytes`] recomputes them, so there is nothing to lie about.
    pub fn to_bytes(&self) -> Vec<u8> {
        wire()
            .serialize(&((&self.xmss_signers, &self.sphincs_signers), self.core()))
            .expect("an aggregate serializes")
    }

    /// Parsing does NOT verify: the proof is untouched, only shapes are checked.
    /// Call [`Self::verify`] before believing any of it.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, AggregateVerifyError> {
        let (keys, core): (WireKeys, WireCore) = wire()
            .deserialize(bytes)
            .map_err(|_| AggregateVerifyError::MalformedEncoding)?;
        Self::from_parts(keys, core)
    }

    /// Without the signer set, for a receiver that already knows it. A set other
    /// than the one aggregated fails verification.
    pub fn to_bytes_without_pubkeys(&self) -> Vec<u8> {
        wire().serialize(&self.core()).expect("an aggregate serializes")
    }

    pub(crate) fn proof(&self) -> &lean_vm::cpu::Proof {
        &self.proof
    }

    /// Inverse of [`Self::to_bytes_without_pubkeys`], verifying nothing either.
    pub fn from_bytes_without_pubkeys(bytes: &[u8], keys: WireKeys) -> Result<Self, AggregateVerifyError> {
        Self::from_parts(
            keys,
            wire()
                .deserialize(bytes)
                .map_err(|_| AggregateVerifyError::MalformedEncoding)?,
        )
    }

    fn core(&self) -> WireCore {
        (
            self.defer.bytecode_point.clone(),
            self.defer.matrix_point.clone(),
            self.proof.clone(),
        )
    }

    fn from_parts(keys: WireKeys, core: WireCore) -> Result<Self, AggregateVerifyError> {
        let (xmss_signers, sphincs_signers) = keys;
        let (bytecode_point, matrix_point, proof) = core;
        // Cheap rejections first. `recompute` below is a pass over the whole stacked
        // bytecode plus a walk of the BLAKE2s circuit, on points a peer chose, so
        // anything decidable without it has to be decided before it.
        check_signer_set(&xmss_signers, &sphincs_signers)?;
        Ok(Self {
            xmss_signers,
            sphincs_signers,
            // The wire carries no value, only the points to derive it from.
            defer: DeferredClaim::recompute(bytecode_point, matrix_point)?,
            proof,
        })
    }

    /// Verify the aggregate's internal consistency: the signer set is well
    /// formed, the three deferred fixed-polynomial claims hold at their
    /// transmitted points, and the VM proof satisfies the statement built from
    /// all of it.
    ///
    /// This says "every key in `xmss_signers` signed its group's message at its
    /// group's epoch, and every `(key, message)` in `sphincs_signers` is a valid
    /// SPHINCS signature", with the epochs and messages chosen by whoever
    /// produced the aggregate: an aggregate over the same keys at different
    /// epochs, or under different messages, verifies just as well. A caller that
    /// expects particular pairs has to check the two lists against them.
    pub fn verify(&self) -> Result<(), AggregateVerifyError> {
        check_signer_set(&self.xmss_signers, &self.sphincs_signers)?;
        // Discharging the deferred claims IS recomputing them: their values have
        // to be the true evaluations, or the recursion below proves nothing about
        // the fixed polynomials.
        let _s = tracing::info_span!("Recompute deferred claims").entered();
        let defer = DeferredClaim::recompute(self.defer.bytecode_point.clone(), self.defer.matrix_point.clone())?;
        drop(_s);
        if defer != self.defer {
            return Err(AggregateVerifyError::MalformedClaim);
        }
        let _s = tracing::info_span!("Statement digest").entered();
        let pi = self.public_input();
        drop(_s);
        verify(unified_guest(), &pi, &self.proof).map_err(AggregateVerifyError::Snark)?;
        Ok(())
    }
}

/// The stacked bytecode polynomial of the aggregation guest: the one fixed
/// table every node's bytecode claims are about. Cached, because verification
/// evaluates it and building it walks the whole program.
fn stacked_bytecode() -> &'static [F64] {
    static TABLE: std::sync::OnceLock<Vec<F64>> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| lean_vm::cpu::layout::bytecode_table(&unified_guest().prog))
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
            let kbc = bytecode_vars() - lean_vm::leaf::N_BYTECODE_SELECTORS;
            let live = |s: usize| table[s << kbc..(s + 1) << kbc].iter().any(|v| *v != F64::ZERO);
            let slots = 1 << lean_vm::leaf::N_BYTECODE_SELECTORS;
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
    let slots = lean_vm::leaf::N_BYTECODE_SELECTORS;
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
fn aggregate_deferred_claims(
    subproofs: &[DeferredSubproof],
    carried_claims: &[DeferredClaim],
) -> (SubHints, DeferredClaim) {
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
    let n_slots = 1 << lean_vm::leaf::N_BYTECODE_SELECTORS;
    let slot_window = bytecode_window();
    let kbc = kbcv - lean_vm::leaf::N_BYTECODE_SELECTORS;
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
    for _ in 0..lean_vm::leaf::N_BYTECODE_SELECTORS {
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
    // sanity: every claim really is the bilinear form over the matrices.
    #[cfg(debug_assertions)]
    for t in 0..2 * child_count {
        let form = |m: &[F192]| {
            m.iter()
                .zip(&us[t])
                .map(|(&m, &u)| m * u)
                .fold(F192::ZERO, |a, x| a + x)
        };
        let (fa, fb) = (form(&ms[2 * t]), form(&ms[2 * t + 1]));
        if t % 2 == 0 {
            let subproof = &subproofs[t / 2];
            assert_eq!(
                fa + subproof.matrix_a_coefficient * fb,
                subproof.matrix_claim,
                "fresh matrix claim, child {}",
                t / 2
            );
        } else {
            let carried = &carried_claims[t / 2];
            assert_eq!(
                (fa, fb),
                (carried.matrix_a_value, carried.matrix_b_value),
                "carried matrix claim"
            );
        }
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
    assert_eq!(mrun, v_a * wa[0] + v_b * wb[0], "matrix sumcheck terminal");
    // The guest reaches the same two weights by a succinct formula rather than by
    // folding these tables, and nothing else compares the two: the aggregation
    // layer has no third implementation the way `cpu::verify` does. So this runs
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
        ("bc_sumcheck_msgs".to_string(), bscr),
        ("mat_sumcheck_msgs".to_string(), mscr),
        ("bc_star_hint".to_string(), vec![v_bc]),
        ("mat_stars_hint".to_string(), vec![v_a, v_b]),
    ];
    (
        hints,
        DeferredClaim {
            bytecode_point: r_bc,
            bytecode_value: v_bc,
            matrix_point: r_row.iter().chain(&r_col).copied().collect(),
            matrix_a_value: v_a,
            matrix_b_value: v_b,
        },
    )
}

/// The verifier-side WHIR config for one committed size and rate, plus the
/// query packing derived from it. The hint builder needs it for the real
/// opening and the placeholder map for every candidate size, so it lives here:
/// a candidate whose shape differed from the real one would compile a guest
/// that cannot open the proof it is handed.
struct WhirShape {
    config: pcs::whir::VerifierConfig,
    levels: pcs::whir::LevelShapes,
    /// Merkle tree depth per level.
    depth: Vec<usize>,
    /// Query positions carried by one squeezed F192 word, per level.
    per_squeeze: Vec<usize>,
}

fn whir_shape(mu: usize, log_inv_rate: usize) -> WhirShape {
    let config = pcs::whir::WhirSecurityConfig::derive_config_with_log_inv_rate(mu + pcs::LOG_PACKING, log_inv_rate)
        .and_then(|s| s.to_prover_verifier_configs())
        .expect("stacked whir config")
        .1;
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

/// The BLAKE2s table's virtual value columns, in `hash_flock::SLOTS` order.
fn blake2s_value_columns() -> Vec<usize> {
    let base = lean_vm::cpu::schema().base[5];
    lean_vm::tables::BLAKE2S_VALUE_COLS.iter().map(|&c| base + c).collect()
}

/// One entry of the guest's claim pool.
enum ClaimSite {
    /// A framework bus block reads a committed column at this kappa.
    Framework { column: usize, kappa: usize },
    /// A committed column of `table`; `is_virtual` marks the q_flock-backed value
    /// columns, whose claim is a strided slot rather than a plain column.
    TableColumn {
        table: usize,
        column: usize,
        is_virtual: bool,
    },
    /// One of the three PI memory limbs (MEM_LO, MEM_HI, MEM_TOP).
    MemoryLimb { column: usize },
}

/// The guest's `COORD_KIND_*` code for a coordinate (`guests/aggregate.py`),
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
fn push_coord_terms(
    c: &Coord,
    base: usize,
    ty: &mut Vec<usize>,
    val: &mut Vec<u128>,
    col_a: &mut Vec<usize>,
    col_b: &mut Vec<usize>,
) {
    let (a, b) = match c {
        Coord::Const(_) => (0, 0),
        Coord::Col(i) | Coord::GCol(i, _) => (*i - base, 0),
        Coord::Prod(i, j, _) => (*i - base, *j - base),
        Coord::Sum(cs) => {
            for c in cs {
                push_coord_terms(c, base, ty, val, col_a, col_b);
            }
            return;
        }
        Coord::Index | Coord::Public(_) => unreachable!("a table's bus block carries no virtual coordinate"),
    };
    ty.push(coord_kind(c));
    val.push(dsl_u128(coord_scale(c)));
    col_a.push(a);
    col_b.push(b);
}

/// Visit the claim pool in the exact order the guest indexes it: the framework
/// bus claims (deduped by `(column, kappa)`, as `leaf.rs` pools them), then every
/// table's committed columns, then the PI memory triple. Both the per-sub hints
/// and the placeholder map descriptors are built from this one walk, so the two
/// stay index-aligned by construction rather than by two matching count asserts.
fn walk_claims(layout: &lean_vm::cpu::Layout, kbc: usize, mut visit: impl FnMut(ClaimSite)) {
    let sides: [&[Block]; 3] = [&layout.push, &layout.pull, &layout.count];
    let valcols = blake2s_value_columns();
    // Only the framework blocks raise claims: a table's coords are settled inside
    // the table sumcheck.
    let is_framework: Vec<bool> = lean_vm::cpu::block_kappa_sources(kbc)
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
                    visit(ClaimSite::Framework {
                        column: *i,
                        kappa: blk.kappa,
                    });
                }
            }
        }
    }
    let sch = lean_vm::cpu::schema();
    for (t, table) in lean_vm::tables::tables().iter().enumerate() {
        for c in 0..table.n_committed_columns() {
            let column = sch.base[t] + c;
            visit(ClaimSite::TableColumn {
                table: t,
                column,
                is_virtual: layout.placements[column].is_virtual(),
            });
        }
    }
    for &column in &[lean_vm::cpu::MEM_LO, lean_vm::cpu::MEM_HI, lean_vm::cpu::MEM_TOP] {
        visit(ClaimSite::MemoryLimb { column });
    }
}

/// Config + hints for the recursion guest (`guests/aggregate.py`), built
/// from the REAL `cpu::layout` of the inner program and the summary of a real
/// `cpu::verify` run (zero hand-mirroring drift).
fn gen_verify(
    program: &Program,
    public_input: [F192; 2],
    summary: &lean_vm::cpu::VerifySummary,
) -> Result<(SubHints, DeferredSubproof), AggregationError> {
    let proof_stream = &summary.raw.stream;
    let layout = lean_vm::cpu::layout(
        &program.prog,
        proof_stream[0].c0 as usize,
        std::array::from_fn(|i| proof_stream[1 + i].c0 as usize),
        public_input,
    );
    let sides: [&[Block]; 3] = [&layout.push, &layout.pull, &layout.count];
    let side_layouts: Vec<lean_vm::leaf::Layout> = sides.iter().map(|blocks| lean_vm::leaf::layout(blocks)).collect();
    let side_mus: Vec<usize> = side_layouts.iter().map(|side| side.mu).collect();
    // Fixed capacities: every buffer/stride placeholder is a global cap so
    // the placeholder map is SHAPE-INDEPENDENT (the definition of generic).
    assert!(*side_mus.iter().max().unwrap() <= MU_CAP && proof_stream.len() <= STREAM_CAP);
    // The guest holds one opening arm per candidate committed size, so a child
    // outside that window has no arm to dispatch to. `min_log_committed` keeps
    // every aggregate above the low end, leaving only the ceiling reachable.
    if !(MU_MIN..=MU_MAX).contains(&layout.shape.mu) {
        return Err(AggregationError::ChildOutOfRange {
            log_committed: layout.shape.mu,
        });
    }

    // ---- typed extraction: proof structs + the verifier's summary ----
    // Bus: the bytecode claims carry the push/pull ζ_lo points and sb.
    let kbc = summary.bytecode_claims[0].point.len() - lean_vm::leaf::N_BYTECODE_SELECTORS;
    let zeta: Vec<F192> = summary.bytecode_claims[0].point[..kbc].to_vec();
    let sb: Vec<F192> = summary.bytecode_claims[0].point[kbc..].to_vec();

    let taus = layout.taus;
    // Flock replay data, all named struct fields.
    let lcrounds = flock::hash::K_LOG - 6;
    let zcf = [summary.zc_claim.a_eval, summary.zc_claim.b_eval];
    let zc_z = summary.zc_claim.z;
    let zchi = summary.zc_claim.mlv_challenges.clone();
    let lc_alpha = summary.lc_claim.alpha;
    let lc_beta = summary.lc_claim.beta;
    let lrr = summary.lc_claim.r_rounds.clone();

    // ---- the stacked opening: config + the opening summary ----
    let stack = whir_shape(layout.shape.mu, summary.log_inv_rate);
    let klvl = &stack.levels.ks;

    // flock's reduction ends at `flock_stream_end`, where the WHIR opening's own
    // scalars start: its last 64 scalars are lincheck's `z_partial` (which the
    // summary already carries as `s_hat_v`), immediately preceded by the
    // coefficient PAIRS of the `lcrounds` lincheck rounds: the linear one is not
    // sent, the running claim fixing it.
    let ns = summary.flock_stream_end;
    let lcr: Vec<F192> = proof_stream[ns - 64 - 2 * lcrounds..ns - 64].to_vec();
    let lcz: Vec<F192> = summary.lc_claim.s_hat_v.clone();

    // matpart = the deferred weighted matrix evaluation: the lincheck running
    // claim minus (= plus, char 2) the const-pin and c-claim contributions.
    // α² from α, not from β: `LincheckClaim::beta` (the pin, at α³) is zero for
    // a circuit with no const-pin column, while every verifier draws the
    // c-claim's coefficient unconditionally.
    let lc_sq = lc_alpha.square();
    let mut lrun = zcf[0] + lc_alpha * zcf[1] + lc_sq * summary.zc_claim.c_eval + lc_beta;
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
    // the fingerprint challenges (§sec:e2e-bc).
    let bytecode_value = summary.bytecode_claims[0].value;
    let bcv = vec![bytecode_value];

    // ---- per-sub HINT data (the placeholder map is built once, elsewhere) ----
    // Per side, the packing order read straight off `leaf::layout`'s offsets:
    // sort_order[side_base + rank] = g^{side-local index of the rank-r block}.
    // The guest only perm-checks it and derives offsets; any aligned tiling is
    // sound, so this canonical order just has to match the committed leaf.
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
    let col_sources = lean_vm::cpu::col_kappa_sources(kbc);
    let committed_globals: Vec<usize> = col_sources
        .iter()
        .enumerate()
        .filter_map(|(i, source)| source.map(|_| i))
        .collect();
    let mut compact_col = vec![usize::MAX; col_sources.len()];
    for (compact, &global) in committed_globals.iter().enumerate() {
        compact_col[global] = compact;
    }
    let mut col_order = committed_globals.clone();
    col_order.sort_by_key(|&global| layout.placements[global].offset);
    let col_sort_order: Vec<F192> = col_order
        .iter()
        .map(|&global| F192::new(g_pow(compact_col[global]).0, 0, 0))
        .collect();
    let log_mem = proof_stream[0].c0 as usize;

    // ---- Phase E2 hints (the stacked WHIR opening) ----
    let lenris: usize = klvl.iter().sum();
    // The verifier already authenticated every queried row and expanded the
    // pruned phases into one full path per query, in level order. The guest
    // re-hashes exactly that: a leaf is its `F64` words (one per interleaved K
    // value at level 0, three per `E` value deeper), then a walk up the path.
    let (mut lrows_flat, mut lpaths_flat): (Vec<F192>, Vec<F192>) = (Vec::new(), Vec::new());
    for opening in &summary.raw.merkle {
        lrows_flat.extend(opening.leaf_data.iter().map(|x| F192::new(x.0, 0, 0)));
        for h in &opening.path {
            lpaths_flat.extend_from_slice(&pack_hash_state(h));
        }
    }
    // claim descriptors, in exact clv order.
    let mut nover_v = Vec::new();
    walk_claims(&layout, program.prog.len().trailing_zeros() as usize, |site| {
        // Per claim, `nvt` is the full low span; when it exceeds `lenris` the point
        // overlaps the residual y region by `nover` coords. Stack selectors are not
        // emitted: the guest derives them from the certified committed-column offsets.
        let nvt = match site {
            ClaimSite::Framework { kappa, .. } => kappa,
            ClaimSite::TableColumn { table, is_virtual, .. } => {
                if is_virtual {
                    lean_vm::hash_flock::SLOT_STRIDE_LOG + taus[table]
                } else {
                    taus[table]
                }
            }
            // The three PI memory lanes share one point [r_m, 0, 0, ...]; the coords
            // beyond `lenris` are const zero, so they fold into the y pattern instead
            // of a runtime overlap factor.
            ClaimSite::MemoryLimb { column } => layout.placements[column].n_vars.min(lenris),
        };
        nover_v.push(nvt.saturating_sub(lenris));
    });

    // The ring-switch weight's own residual overlap: the q_flock claim spans
    // `qflockv` coordinates, and a BLAKE2s-dominated inner proof pushes that past
    // the fold rounds. Same quantity as the q_flock point claim's `nover`, but
    // the guest pins it independently, in the rs block.
    let qflockv = lean_vm::hash_flock::SLOT_STRIDE_LOG + taus[5];
    let rs_nover = qflockv.saturating_sub(lenris);

    let deferred = DeferredSubproof {
        public_input,
        bytecode_row_point: zeta,
        bytecode_selector_point: sb.clone(),
        bytecode_value,
        matrix_a_coefficient: lc_alpha,
        skip_point: zc_z,
        zerocheck_row_point: zchi[..lcrounds].to_vec(),
        lincheck_round_point: lrr.clone(),
        lincheck_terminal_values: lcz.clone(),
        matrix_claim: matpart,
    };

    let hints = vec![
        ("stream".to_string(), {
            // The guest replays the WHIR opening off the same stream the native
            // verifier reads: every transmitted scalar (sumcheck messages, level
            // roots, OOD claims, grind nonces, `yr`) is already there in protocol
            // order, so there is nothing to reassemble. The guest's `open_stacked`
            // picks it up at `msg_cursor = cursor`, which sits where the flock
            // reduction stopped; the ring-switch messages are struct-observed and
            // still do not advance that cursor.
            let mut stream = proof_stream.clone();
            assert!(
                stream.len() <= STREAM_CAP,
                "stream {} exceeds cap {STREAM_CAP}",
                stream.len()
            );
            stream.resize(STREAM_CAP, F192::ZERO);
            stream
        }),
        ("bytecode_val".to_string(), bcv),
        ("matpart".to_string(), vec![matpart]),
        ("merkle_leaf_rows".to_string(), lrows_flat),
        ("merkle_paths".to_string(), lpaths_flat),
        // per-claim overlap count, for the exact length pin: nover = the
        // amount by which the claim's total vars exceed the fold rounds.
        (
            "claim_nover".to_string(),
            nover_v.iter().map(|&n| F192::new(g_pow(n).0, 0, 0)).collect(),
        ),
        // the pi claim's low dimension is min(log_mem, lenris); certify it as
        // a min (<= both, == one) so pi is pinned like every other claim.
        (
            "pi_cplen".to_string(),
            vec![F192::new(g_pow(log_mem.min(lenris)).0, 0, 0)],
        ),
        // the table sumcheck's round count: max_t tau_t, certified in-guest as a
        // maximum (one of the taus, and dominating them all).
        (
            "zc_tau_max".to_string(),
            vec![F192::new(g_pow(*taus.iter().max().unwrap()).0, 0, 0)],
        ),
        ("rs_nover".to_string(), vec![F192::new(g_pow(rs_nover).0, 0, 0)]),
        ("col_sort_order".to_string(), col_sort_order),
        ("sort_order".to_string(), sort_order),
    ];
    Ok((hints, deferred))
}

/// The guest's stacked-size dispatch range: one `match_range` opening arm per
/// candidate `mu` in `MU_MIN..=MU_MAX` (mirrored by the soundness test's
/// residual-log cap).
const MU_MIN: usize = 22;
const MU_MAX: usize = lean_vm::pcs::MAX_MU;

const _: () = assert!(MU_MIN >= lean_vm::pcs::MIN_MU);

/// The guest's baked buffer caps, which `placeholder_map` compiles in and
/// `gen_verify` admits against: one definition, so a hinted shape can never
/// outgrow the buffer the guest was compiled with.
const MU_CAP: usize = 40;
const STREAM_CAP: usize = 8192;

/// One entry per named hint stream, for a single sub-proof.
type SubHints = Vec<(String, Vec<F192>)>;

/// One `hint_witness` stream: a name and its entries, in the order the guest
/// pops them.
#[derive(Default)]
pub(crate) struct Hints(Vec<(String, Vec<Vec<F192>>)>);

impl Hints {
    fn push(&mut self, name: &str, entry: Vec<F192>) {
        match self.0.iter_mut().find(|(n, _)| n == name) {
            Some((_, entries)) => entries.push(entry),
            None => self.0.push((name.to_string(), vec![entry])),
        }
    }

    /// The entries of one stream, for the adversarial test to corrupt.
    #[cfg(test)]
    fn entries(&mut self, name: &str) -> &mut Vec<Vec<F192>> {
        &mut self
            .0
            .iter_mut()
            .find(|(n, _)| n == name)
            .unwrap_or_else(|| panic!("no hint stream `{name}`"))
            .1
    }

    fn install(self, guest: &mut Program) {
        for (name, entries) in self.0 {
            guest.set_witness(name, entries);
        }
    }
}

/// The coverage slot each write in the guest's coverage walk targets, in walk
/// order: the raw signatures first (grouped by epoch, as the guest loops over
/// them), then each child's key lists.
///
/// The table is one contiguous region per XMSS epoch group, then the SPHINCS
/// pair, each region its declared keys followed by its own duplicate slots:
///
/// | slots | holds |
/// | --- | --- |
/// | `[0, n_0 + d_0)` | epoch group 0: declared keys, then duplicates |
/// | ... | one such region per declared group, in epoch order |
/// | ... | then one per covered-but-undeclared group, all duplicates |
/// | `[X, X + n_sphincs)` | the declared SPHINCS keys |
/// | `[X + n_sphincs, n_total)` | SPHINCS duplicate slots |
///
/// with `X` the sum of every group's slots. A key the declared set holds takes its
/// slot there, one it does not takes a fresh duplicate slot in the same region, so
/// the walk hits every one of the `n_total` slots exactly once.
/// That bijection, enforced in-circuit by write-once memory plus the final
/// count, is what makes every declared key covered by a real signature or a
/// verified child.
///
/// Keeping each region contiguous is what binds the scheme and the epoch: the
/// guest addresses every writer as an offset into one region, bounded by that
/// region's size, one range check per write, so no signature can reach a key
/// declared under another epoch or the other scheme.
struct Coverage {
    /// Declared groups in statement order, then undeclared ones, all duplicates.
    xmss_groups: Vec<XmssGroup>,
    /// How many of `xmss_groups` the signer set declares.
    n_declared: usize,
    /// One duplicate list per group, aligned with `xmss_groups`.
    xmss_dups: Vec<Vec<XmssPublicKey>>,
    sphincs_signers: Vec<SphincsSigner>,
    sphincs_dups: Vec<SphincsSigner>,
    /// Offsets within each raw signature's own group region, indexed as `raw_xmss`.
    raw_xmss: Vec<usize>,
    /// `raw_xmss` indices in the guest's walk order: it walks the table, whose
    /// groups are declared-first rather than epoch-sorted.
    raw_walk: Vec<usize>,
    /// Offsets past `X`, in the SPHINCS region.
    raw_sphincs: Vec<usize>,
    /// Per child, per child group: the parent group it maps to, and the offset
    /// of each child key within that parent group's region.
    child_xmss: Vec<Vec<(usize, Vec<usize>)>>,
    child_sphincs: Vec<Vec<usize>>,
}

impl Coverage {
    fn declared(&self) -> &[XmssGroup] {
        &self.xmss_groups[..self.n_declared]
    }

    fn n_keys(&self) -> usize {
        self.xmss_groups.iter().map(|(_, _, keys)| keys.len()).sum::<usize>() + self.sphincs_signers.len()
    }

    fn n_total(&self) -> usize {
        self.n_keys() + self.xmss_dups.iter().map(Vec::len).sum::<usize>() + self.sphincs_dups.len()
    }
}

/// The slot a key takes within its own scheme's region: its position in the
/// declared list, or a fresh duplicate slot past it if the list does not declare
/// the key. A duplicate slot is outside the hashed prefix: covered, not claimed.
fn take_slot<K: Ord + Clone>(keys: &[K], claimed: &mut [bool], duplicates: &mut Vec<K>, pk: &K) -> usize {
    match keys.binary_search(pk) {
        Ok(pos) if !claimed[pos] => {
            claimed[pos] = true;
            pos
        }
        _ => {
            duplicates.push(pk.clone());
            keys.len() + duplicates.len() - 1
        }
    }
}

/// Record one epoch's message, rejecting a second, different one: within an
/// aggregate the message is a function of the epoch.
fn bind_message(
    messages: &mut BTreeMap<xmss::Epoch, xmss::Message>,
    epoch: xmss::Epoch,
    message: xmss::Message,
) -> Result<(), AggregationError> {
    match messages.insert(epoch, message) {
        Some(previous) if previous != message => Err(AggregationError::ConflictingMessages),
        _ => Ok(()),
    }
}

fn plan_coverage(
    raw_xmss: &[(XmssPublicKey, xmss::Epoch, xmss::Message)],
    raw_sphincs: &[SphincsSigner],
    children: &[AggregateSignature],
    declare: Option<&WireKeys>,
) -> Result<Coverage, AggregationError> {
    // The union, as `(epoch, key)` claims plus the epoch-to-message function
    // every contributor must agree on, then grouped: consecutive equal epochs
    // of the sorted deduplicated list are one group.
    let mut messages: BTreeMap<xmss::Epoch, xmss::Message> = BTreeMap::new();
    let mut claims: Vec<(xmss::Epoch, XmssPublicKey)> = Vec::with_capacity(raw_xmss.len());
    for (pk, epoch, message) in raw_xmss {
        bind_message(&mut messages, *epoch, *message)?;
        claims.push((*epoch, pk.clone()));
    }
    let mut sphincs_signers = raw_sphincs.to_vec();
    for child in children {
        for (epoch, message, keys) in &child.xmss_signers {
            bind_message(&mut messages, *epoch, *message)?;
            claims.extend(keys.iter().map(|pk| (*epoch, pk.clone())));
        }
        sphincs_signers.extend_from_slice(&child.sphincs_signers);
    }
    claims.sort();
    claims.dedup();
    // On the whole pair, so one key signing two messages is two claims.
    sphincs_signers.sort();
    sphincs_signers.dedup();
    if claims.is_empty() && sphincs_signers.is_empty() {
        return Err(AggregationError::Empty);
    }
    let mut union_groups: Vec<XmssGroup> = Vec::new();
    for (epoch, pk) in claims {
        match union_groups.last_mut() {
            Some((last, _, keys)) if *last == epoch => keys.push(pk),
            _ => union_groups.push((epoch, messages[&epoch], vec![pk])),
        }
    }
    // Groups the declaration holds nothing of go last, so the declared ones are the
    // prefix the digest hashes. Claims are struck off, so leftovers are uncovered.
    let mut wanted: BTreeSet<(xmss::Epoch, XmssPublicKey)> = BTreeSet::new();
    let mut wanted_sphincs: BTreeSet<SphincsSigner> = BTreeSet::new();
    if let Some((groups, signers)) = declare {
        for (epoch, message, keys) in groups {
            if messages.get(epoch) != Some(message) {
                return Err(AggregationError::NotCovered);
            }
            wanted.extend(keys.iter().map(|key| (*epoch, key.clone())));
        }
        wanted_sphincs.extend(signers.iter().copied());
    }
    let mut xmss_groups: Vec<XmssGroup> = Vec::new();
    let mut covered_only: Vec<XmssGroup> = Vec::new();
    for (epoch, message, keys) in union_groups {
        let declared: Vec<XmssPublicKey> = keys
            .into_iter()
            .filter(|key| declare.is_none() || wanted.remove(&(epoch, key.clone())))
            .collect();
        if declared.is_empty() {
            covered_only.push((epoch, message, Vec::new()));
        } else {
            xmss_groups.push((epoch, message, declared));
        }
    }
    let n_declared = xmss_groups.len();
    xmss_groups.append(&mut covered_only);
    if xmss_groups.len() > MAX_EPOCHS {
        return Err(AggregationError::TooManyEpochs);
    }
    if declare.is_some() {
        sphincs_signers.retain(|signer| wanted_sphincs.remove(signer));
        if !wanted.is_empty() || !wanted_sphincs.is_empty() {
            return Err(AggregationError::NotCovered);
        }
    }
    if n_declared == 0 && sphincs_signers.is_empty() {
        return Err(AggregationError::Empty);
    }
    // The table is no longer sorted by epoch.
    let region_of: BTreeMap<xmss::Epoch, usize> = xmss_groups
        .iter()
        .enumerate()
        .map(|(j, (epoch, _, _))| (*epoch, j))
        .collect();
    let group_of = |epoch: xmss::Epoch, _: &[XmssGroup]| region_of[&epoch];
    let mut xmss_claimed: Vec<Vec<bool>> = xmss_groups.iter().map(|(_, _, keys)| vec![false; keys.len()]).collect();
    let mut xmss_dups: Vec<Vec<XmssPublicKey>> = vec![Vec::new(); xmss_groups.len()];
    let mut sphincs_claimed = vec![false; sphincs_signers.len()];
    let mut sphincs_dups = Vec::new();
    let raw_xmss_slots: Vec<usize> = raw_xmss
        .iter()
        .map(|(pk, epoch, _)| {
            let g = group_of(*epoch, &xmss_groups);
            take_slot(&xmss_groups[g].2, &mut xmss_claimed[g], &mut xmss_dups[g], pk)
        })
        .collect();
    let raw_sphincs_slots: Vec<usize> = raw_sphincs
        .iter()
        .map(|signer| take_slot(&sphincs_signers, &mut sphincs_claimed, &mut sphincs_dups, signer))
        .collect();
    let mut child_xmss = Vec::with_capacity(children.len());
    let mut child_sphincs = Vec::with_capacity(children.len());
    for child in children {
        child_xmss.push(
            child
                .xmss_signers
                .iter()
                .map(|(epoch, _, keys)| {
                    let g = group_of(*epoch, &xmss_groups);
                    let offsets = keys
                        .iter()
                        .map(|pk| take_slot(&xmss_groups[g].2, &mut xmss_claimed[g], &mut xmss_dups[g], pk))
                        .collect();
                    (g, offsets)
                })
                .collect::<Vec<(usize, Vec<usize>)>>(),
        );
        child_sphincs.push(
            child
                .sphincs_signers
                .iter()
                .map(|signer| take_slot(&sphincs_signers, &mut sphincs_claimed, &mut sphincs_dups, signer))
                .collect(),
        );
    }
    // Stable, so signatures within a group keep the order their slots were taken in.
    let mut raw_walk: Vec<usize> = (0..raw_xmss.len()).collect();
    raw_walk.sort_by_key(|&i| region_of[&raw_xmss[i].1]);
    let cover = Coverage {
        xmss_groups,
        n_declared,
        xmss_dups,
        sphincs_signers,
        sphincs_dups,
        raw_xmss: raw_xmss_slots,
        raw_walk,
        raw_sphincs: raw_sphincs_slots,
        child_xmss,
        child_sphincs,
    };
    if cover.n_total() >= MAX_KEYS {
        return Err(AggregationError::TooLarge);
    }
    Ok(cover)
}

/// One signature's witness: the WOTS randomness, the encoding digits (in the
/// exponent), the chain tips they start from, and the Merkle siblings.
fn push_signature_hints(
    hints: &mut Hints,
    pk: &XmssPublicKey,
    sig: &XmssSignature,
    message: &xmss::Message,
    xmss_epoch: xmss::Epoch,
) -> Result<(), AggregationError> {
    let wots = &sig.wots_signature;
    let encoding = xmss::wots_encode(message, xmss_epoch, &pk.public_param, &wots.randomness)
        .ok_or(AggregationError::MalformedRawSignature)?;
    let mut randomness = [0u8; xmss::STATE_LEN];
    randomness[..xmss::RANDOMNESS_LEN].copy_from_slice(&wots.randomness);
    hints.push(
        "rand",
        vec![pack_16_bytes(&randomness[..16]), pack_16_bytes(&randomness[16..])],
    );
    for &e in &encoding {
        hints.push("digits", vec![count(e as usize)]);
    }
    for tip in &wots.chain_tips {
        hints.push("chain_starts", vec![pack_16_bytes(tip)]);
    }
    for sibling in &sig.merkle_proof {
        hints.push("siblings", vec![pack_16_bytes(sibling)]);
    }
    Ok(())
}

/// One SPHINCS signature's witness: the randomizer, the few-time opening, and
/// per layer the encoding counter, the codeword digits (in the exponent), the
/// chain values they start from, and the Merkle siblings.
///
/// The guest derives the index and the leaf indices from the digest itself, so
/// nothing here carries them; what it does carry is the per-layer message, which
/// this walk recomputes exactly as the guest will. The signer's own message is
/// not hinted either: it rides its slot in the coverage table.
fn push_sphincs_hints(
    hints: &mut Hints,
    (pk, message): &SphincsSigner,
    sig: &SphincsSignature,
) -> Result<(), AggregationError> {
    let pp = &pk.public_param;
    hints.push("sp_rand", vec![pack_16_bytes(&sig.randomizer)]);
    let (idx, u) = sphincs::message_digest(pp, &pk.root, &sig.randomizer, message);
    for kappa in 0..sphincs::NUM_FTS_TREES {
        hints.push("sp_fts_secrets", vec![pack_16_bytes(&sig.fts.secrets[kappa])]);
        for sibling in &sig.fts.paths[kappa] {
            hints.push("sp_fts_paths", vec![pack_16_bytes(sibling)]);
        }
    }
    let mut signed = sphincs::fts_recover(pp, idx, &u, &sig.fts);
    for lay in (0..sphincs::D).rev() {
        let pos = sphincs::Pos::new(lay, sphincs::tree_of(idx, lay), sphincs::leaf_of(idx, lay));
        let counter = sig.counters[lay];
        let codeword = sphincs::encode(pp, pos, &signed, counter).ok_or(AggregationError::MalformedRawSignature)?;
        hints.push("sp_counter", vec![F192::new(u64::from(counter), 0, 0)]);
        for (&digit, opened) in codeword.iter().zip(&sig.ots[lay]) {
            hints.push("sp_digits", vec![count(digit as usize)]);
            hints.push("sp_chain_starts", vec![pack_16_bytes(opened)]);
        }
        let path = &sig.paths[sphincs::path_range(lay)];
        for sibling in path {
            hints.push("sp_siblings", vec![pack_16_bytes(sibling)]);
        }
        let leaf = sphincs::ots_leaf(pp, pos, &signed, counter, &sig.ots[lay])
            .ok_or(AggregationError::MalformedRawSignature)?;
        signed = sphincs::tree_fold(pp, pos, leaf, path);
    }
    debug_assert_eq!(signed, pk.root, "the hinted walk reaches the public key");
    Ok(())
}

/// - `children`: previously aggregated signatures; at most [`MAX_RECURSIONS`].
/// - `raw_xmss`: list of `(public_key, epoch, message, signature)`, any order; one message per
///   epoch across the whole result, at most [`MAX_EPOCHS`] epochs.
/// - `raw_sphincs`: list of `(public_key, message, signature)`, any order.
/// - `declare`: only useful to remove signatures the children carry, in which case pass `Some` of
///   the signatures to keep, a subset of the ones being aggregated. `None` keeps them all.
/// - `log_inv_rate`: PCS code rate `2^-log_inv_rate`, higher `log_inv_rate` means a smaller proof
///   but slower proving; in [`MIN_LOG_INV_RATE`]..=[`MAX_LOG_INV_RATE`].
///
/// The aggregated signature should contain at most [`MAX_KEYS`] many XMSS and SPHINCS combined.
///
/// IMPORTANT:
/// - `aggregate` should not be called more than once at a time in parallel per process.
/// - Raw signatures are assumed valid (otherwise `aggregate` will panic).
///
/// XMSS Performance: it is optimized for a small set of different (epoch, message), and many XMSS
/// sharing each such pair.
pub fn aggregate(
    children: &[AggregateSignature],
    raw_xmss: Vec<(XmssPublicKey, xmss::Epoch, xmss::Message, XmssSignature)>,
    raw_sphincs: Vec<(SphincsPublicKey, sphincs::Message, SphincsSignature)>,
    declare: Option<&WireKeys>,
    log_inv_rate: usize,
) -> Result<AggregateSignature, AggregationError> {
    aggregate_with_stats(children, raw_xmss, raw_sphincs, declare, log_inv_rate).map(|(sig, _)| sig)
}

/// [`aggregate`], keeping the prover statistics the benchmark reports.
pub(crate) fn aggregate_with_stats(
    children: &[AggregateSignature],
    raw_xmss: Vec<(XmssPublicKey, xmss::Epoch, xmss::Message, XmssSignature)>,
    raw_sphincs: Vec<(SphincsPublicKey, sphincs::Message, SphincsSignature)>,
    declare: Option<&WireKeys>,
    log_inv_rate: usize,
) -> Result<(AggregateSignature, lean_vm::cpu::Stats), AggregationError> {
    aggregate_tampered(children, raw_xmss, raw_sphincs, declare, log_inv_rate, |_| {})
}

/// [`aggregate`], with a hook to corrupt the witness before proving.
///
/// The coverage argument and the claim batching are enforced entirely by guest
/// asserts over prover advice, so the only way to test them is to lie in a hint
/// and require the guest to notice. That is what `tamper` is for
/// (`aggregate_hints_bind`); with an empty hook this is the production path.
pub(crate) fn aggregate_tampered(
    children: &[AggregateSignature],
    raw_xmss: Vec<(XmssPublicKey, xmss::Epoch, xmss::Message, XmssSignature)>,
    raw_sphincs: Vec<(SphincsPublicKey, sphincs::Message, SphincsSignature)>,
    declare: Option<&WireKeys>,
    log_inv_rate: usize,
    tamper: impl FnOnce(&mut Hints),
) -> Result<(AggregateSignature, lean_vm::cpu::Stats), AggregationError> {
    // Otherwise this reaches `cpu::prove`, which asserts rather than reporting.
    if !(lean_vm::pcs::MIN_LOG_INV_RATE..=lean_vm::pcs::MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(AggregationError::InvalidRate { log_inv_rate });
    }
    if children.len() > MAX_RECURSIONS {
        return Err(AggregationError::TooLarge);
    }
    let guest = unified_guest();
    // Sorted by `(epoch, key)` to group them; `Coverage::raw_walk` then puts the
    // groups in the guest's order. Dedup is on the whole triple, so one
    // `(epoch, key)` under two messages reaches `plan_coverage`, whose message
    // binding rejects it.
    let mut raw_xmss = raw_xmss;
    raw_xmss.sort_by(|(a, ae, _, _), (b, be, _, _)| (ae, a).cmp(&(be, b)));
    raw_xmss.dedup_by(|(a, ae, am, _), (b, be, bm, _)| ae == be && a == b && am == bm);
    // On the whole (key, message) pair, so a signer may appear once per message.
    let mut raw_sphincs = raw_sphincs;
    raw_sphincs.sort_by_key(|(pk, message, _)| (*pk, *message));
    raw_sphincs.dedup_by(|(a, am, _), (b, bm, _)| (a, am) == (b, bm));

    // Verifying a child here is not a courtesy: `gen_verify` derives the guest's
    // whole witness for it from a real verification's summary. Its deferred
    // claim is deliberately NOT recomputed, which would cost a full pass over
    // each fixed polynomial per child: the batching sumcheck below already
    // forces every batched value to be the true evaluation, and the root
    // discharges the one claim they reduce to.
    let mut verified = Vec::with_capacity(children.len());
    let _span = tracing::info_span!("Verify children").entered();
    for child in children {
        check_signer_set(&child.xmss_signers, &child.sphincs_signers).map_err(AggregationError::InvalidChild)?;
        let pi = child.public_input();
        let summary = verify(guest, &pi, &child.proof)
            .map_err(|e| AggregationError::InvalidChild(AggregateVerifyError::Snark(e)))?;
        verified.push((pi, summary));
    }

    drop(_span);

    let _span = tracing::info_span!("Build witness").entered();
    let raw_xmss_claims: Vec<(XmssPublicKey, xmss::Epoch, xmss::Message)> = raw_xmss
        .iter()
        .map(|(pk, epoch, message, _)| (pk.clone(), *epoch, *message))
        .collect();
    let raw_sphincs_keys: Vec<SphincsSigner> = raw_sphincs.iter().map(|(pk, message, _)| (*pk, *message)).collect();
    let cover = plan_coverage(&raw_xmss_claims, &raw_sphincs_keys, children, declare)?;
    let n_sphincs = cover.sphincs_signers.len();
    let group_cells = |(epoch, message, _): &XmssGroup| {
        [
            F192::new(*epoch as u64, 0, 0),
            pack_16_bytes(&message[..16]),
            pack_16_bytes(&message[16..]),
        ]
    };

    let mut hints = Hints::default();
    hints.push(
        "meta",
        vec![
            count(cover.n_declared),
            count(cover.xmss_groups.len() - cover.n_declared),
            count(n_sphincs),
            count(cover.sphincs_dups.len()),
            count(raw_sphincs.len()),
            count(children.len()),
        ],
    );
    let fs_seed = lean_vm::cpu::fs_seed(guest);
    hints.push("fs_seed", vec![fs_seed[0], fs_seed[1]]);
    // Per group: its epoch, its two message cells, and its declared, duplicate
    // and raw-signature counts, in the guest's geometry-pass order. The keys
    // then ride two per `pubkeys` entry, so the guest can halve its loop
    // frames, the odd key out on a final one-key entry; each group's
    // duplicates follow its keys.
    for (j, group) in cover.xmss_groups.iter().enumerate() {
        let (epoch, _, keys) = group;
        let mut entry = group_cells(group).to_vec();
        entry.extend([
            count(keys.len()),
            count(cover.xmss_dups[j].len()),
            count(raw_xmss.iter().filter(|(_, e, _, _)| e == epoch).count()),
        ]);
        hints.push("group", entry);
    }
    for (_, _, keys) in cover.declared() {
        hints.push("pk_halves", vec![count(keys.len() / 2), count(keys.len() % 2)]);
        hints.push("signers_split", signers_split(keys.len().div_ceil(2)));
        for pair in keys.chunks(2) {
            let mut entry = key_cells(&pair[0]).to_vec();
            if let Some(second) = pair.get(1) {
                entry.extend_from_slice(&key_cells(second));
            }
            hints.push("pubkeys", entry);
        }
    }
    for dups in &cover.xmss_dups {
        for pk in dups {
            hints.push("dup_pubkeys", key_cells(pk).to_vec());
        }
    }
    if !cover.sphincs_signers.is_empty() {
        hints.push("signers_split", signers_split(cover.sphincs_signers.len()));
    }
    hints.push("signers_split", signers_split(2 + 2 * cover.n_declared));
    for signer in &cover.sphincs_signers {
        hints.push("sphincs_signers", sphincs_signer_cells(signer).to_vec());
    }
    for signer in &cover.sphincs_dups {
        hints.push("dup_sphincs", sphincs_signer_cells(signer).to_vec());
    }
    // Group-major over the table, not over the epochs `raw_xmss` is sorted by: a
    // declaration puts the undeclared groups last. Each index is an offset within
    // the signature's own group region.
    for &i in &cover.raw_walk {
        let (pk, epoch, message, sig) = &raw_xmss[i];
        hints.push("raw_index", vec![count(cover.raw_xmss[i])]);
        push_signature_hints(&mut hints, pk, sig, message, *epoch)?;
    }
    // A SPHINCS slot is hinted as an offset into the SPHINCS region, which is
    // how one range check keeps the scheme's writers off the other's keys.
    for (&offset, (pk, message, sig)) in cover.raw_sphincs.iter().zip(&raw_sphincs) {
        hints.push("sp_raw_index", vec![count(offset)]);
        push_sphincs_hints(&mut hints, &(*pk, *message), sig)?;
    }

    let mut subs = Vec::with_capacity(children.len());
    let mut carried = Vec::with_capacity(children.len());
    for (i, child) in children.iter().enumerate() {
        hints.push(
            "child_meta",
            vec![count(child.xmss_signers.len()), count(child.sphincs_signers.len())],
        );
        for (group, (parent_group, offsets)) in child.xmss_signers.iter().zip(&cover.child_xmss[i]) {
            let mut entry = group_cells(group).to_vec();
            entry.push(count(group.2.len()));
            hints.push("child_group", entry);
            hints.push("child_group_map", vec![count(*parent_group)]);
            hints.push("child_halves", vec![count(offsets.len() / 2), count(offsets.len() % 2)]);
            hints.push("signers_split", signers_split(offsets.len().div_ceil(2)));
            for pair in offsets.chunks(2) {
                hints.push("child_index", pair.iter().map(|&idx| count(idx)).collect());
            }
        }
        if !cover.child_sphincs[i].is_empty() {
            hints.push("signers_split", signers_split(cover.child_sphincs[i].len()));
        }
        for &offset in &cover.child_sphincs[i] {
            hints.push("child_sphincs_index", vec![count(offset)]);
        }
        hints.push("signers_split", signers_split(2 + 2 * child.xmss_signers.len()));
        hints.push("child_defer", child.defer.cells());
        let (pi, summary) = &verified[i];
        let (sub_hints, defer) = gen_verify(guest, *pi, summary)?;
        for (name, entry) in sub_hints {
            hints.push(&name, entry);
        }
        subs.push(defer);
        carried.push(child.defer.clone());
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
        let (agg_hints, reduced) = aggregate_deferred_claims(&subs, &carried);
        for (name, entry) in agg_hints {
            hints.push(&name, entry);
        }
        reduced
    };

    let public_input = statement_digest(signers_hash(cover.declared(), &cover.sphincs_signers), &defer);
    let mut program = guest.clone();
    // Every aggregate is a potential child, and the guest has no opening arm below
    // `2^MU_MIN`. A run smaller than that (a leaf of a few dozen signatures) grows
    // its SET table until it clears the floor.
    program.min_log_committed = MU_MIN;
    tamper(&mut hints);
    hints.install(&mut program);
    let (proof, stats) = prove(&program, public_input, log_inv_rate);
    Ok((
        AggregateSignature {
            xmss_signers: cover.declared().to_vec(),
            sphincs_signers: cover.sphincs_signers,
            defer,
            proof,
        },
        stats,
    ))
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
    row_offsets: Vec<usize>,
    path_offsets: Vec<usize>,
    positions_offsets: Vec<usize>,
    vanish_offsets: Vec<usize>,
    fold_offsets: Vec<usize>,
    residual_fold_offsets: Vec<usize>,
    vanish_values: Vec<F192>,
    vanish_inverses: Vec<F192>,
    ood_samples: Vec<usize>,
}

/// The recursion program's placeholder map (the SHAPE-INDEPENDENT constants the
/// generic guest is compiled from), built from the inner program's STRUCTURE and
/// bytecode SIZE alone: no proof. Dummy layout sizes are fine: `rep` reads only the
/// size-independent block/coord structure and `kbc = log2(bytecode)`, so the guest
/// can be compiled BEFORE any inner proof exists. Because the map is a function of
/// the inner bytecode size alone, one compiled guest serves every shape.
fn placeholder_map(kbc: usize) -> BTreeMap<String, String> {
    // Any valid sizes drive the layout: rep depends only on structure + kbc,
    // and the layout reads a program's length, never its instructions, so a
    // stand-in of the right size is what lets the map exist before the bytecode
    // it describes does.
    let stand_in = vec![lean_vm::cpu::Op::Xor { a: 0, b: 0, c: 0 }; 1 << kbc];
    let layout = lean_vm::cpu::layout(
        &stand_in,
        20,
        [1usize << 10; lean_vm::tables::N_TABLES],
        [F192::ZERO, F192::ZERO],
    );
    let sides: [&[Block]; 3] = [&layout.push, &layout.pull, &layout.count];
    let lcrounds = flock::hash::K_LOG - 6;

    // ---- flattened block/coord descriptors (structural) ----
    let (mut sblk, mut bc0, mut bcn) = (vec![0usize], vec![], vec![]);
    let (mut ct, mut cval) = (vec![], vec![]);
    let (mut nclaims, mut nbcv, mut nblocks) = (0usize, 0usize, 0usize);
    // Claim dedup (mirrors leaf.rs): per coord, fresh = first (group, col,
    // kappa) occurrence gets the next pool slot; duplicates point at it.
    let mut slot_of: std::collections::HashMap<(usize, usize), usize> = Default::default();
    let (mut coord_fresh, mut coord_slot) = (vec![], vec![]);
    // A TABLE block's coordinates, flattened into terms: the guest rebuilds each as
    // `Σ_terms`, so a derived value (an XOR/MUL result, a DEREF store, a JUMP
    // successor) costs terms rather than columns. A framework coordinate has none:
    // it decomposes into pooled claims instead.
    let (mut coord_toff, mut coord_tcount) = (vec![], vec![]);
    let (mut term_type, mut term_const) = (vec![], vec![]);
    let (mut term_col_a, mut term_col_b) = (vec![], vec![]);
    // A table's blocks raise no claim any more: the table sumcheck settles them
    //, so only the framework blocks stream column values.
    let sch_pm = lean_vm::cpu::schema();
    let owner_pm: Vec<Option<usize>> = lean_vm::cpu::block_kappa_sources(kbc)
        .into_iter()
        .map(|(src, _)| src.checked_sub(2))
        .collect();
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            bc0.push(ct.len());
            bcn.push(blk.coords.len());
            let owner = owner_pm[nblocks];
            nblocks += 1;
            for c in &blk.coords {
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
                coord_fresh.push(fresh);
                coord_slot.push(slot);
                // A table's coord becomes terms; a framework one has none, having
                // decomposed into the pooled claim above.
                let toff = term_type.len();
                if let Some(t) = owner {
                    push_coord_terms(
                        c,
                        sch_pm.base[t],
                        &mut term_type,
                        &mut term_const,
                        &mut term_col_a,
                        &mut term_col_b,
                    );
                }
                coord_toff.push(toff);
                coord_tcount.push(term_type.len() - toff);
                nbcv += usize::from(matches!(c, Coord::Public(_)));
                ct.push(coord_kind(c) as u128);
                cval.push(dsl_u128(coord_scale(c)));
            }
        }
        sblk.push(nblocks);
    }
    let evtot: usize = lean_vm::tables::tables().iter().map(|t| t.n_committed_columns()).sum();
    let ncl = nclaims + evtot + 3; // bus + constraint + the three PI memory-limb claims

    // ---- claim descriptor buffer ids (structural) ----
    let valcols = blake2s_value_columns();
    let col_sources_pm = lean_vm::cpu::col_kappa_sources(kbc);
    let mut compact_col_pm = vec![usize::MAX; col_sources_pm.len()];
    let mut n_committed = 0usize;
    for (global, source) in col_sources_pm.iter().enumerate() {
        if source.is_some() {
            compact_col_pm[global] = n_committed;
            n_committed += 1;
        }
    }
    let qflock_compact = compact_col_pm[lean_vm::cpu::QFLOCK];
    assert_ne!(qflock_compact, usize::MAX, "QFLOCK must be committed");
    let (mut cpbuf, mut cpcol, mut cpqslot): (Vec<usize>, Vec<usize>, Vec<usize>) = (vec![], vec![], vec![]);
    // `cpbuf` codes are the guest's POINT_BUF_*: 0 zeta, 1 chi, 2 pi, 3 qflock-chi.
    walk_claims(&layout, kbc, |site| match site {
        ClaimSite::Framework { column, .. } => {
            let compact = compact_col_pm[column];
            assert_ne!(compact, usize::MAX, "framework claim must target a committed column");
            cpbuf.push(0);
            cpcol.push(compact);
            cpqslot.push(0);
        }
        ClaimSite::TableColumn { column, is_virtual, .. } => {
            cpbuf.push(if is_virtual { 3 } else { 1 });
            cpcol.push(if is_virtual {
                qflock_compact
            } else {
                compact_col_pm[column]
            });
            cpqslot.push(if is_virtual {
                lean_vm::hash_flock::SLOTS[valcols.iter().position(|&v| v == column).unwrap()]
            } else {
                0
            });
        }
        ClaimSite::MemoryLimb { column } => {
            cpbuf.push(2);
            cpcol.push(compact_col_pm[column]);
            cpqslot.push(0);
        }
    });
    assert_eq!(cpbuf.len(), ncl, "descriptor count == pool size");
    assert_eq!(cpcol.len(), ncl, "every descriptor has a committed-column target");
    assert_eq!(cpqslot.len(), ncl, "every descriptor has a fixed QFLOCK slot");

    // ---- the placeholder map ----
    let ints = |v: &[usize]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let us = |v: &[u128]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
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
    ps("MIN_LOG_MEM", lean_vm::cpu::MIN_LOG_MEM.to_string());
    ps("INV_GEN", dsl_u128(F192::new(G.inv().0, 0, 0)).to_string());
    ps("MU_CAP", MU_CAP.to_string());
    ps("NO_TABLE", layout.taus.len().to_string());
    ps("GKR_ROUNDS_CAP", (MU_CAP * (MU_CAP + 1) / 2 + MU_CAP + 2).to_string());
    ps("GKR_POINTS_CAP", ((MU_CAP + 1) * MU_CAP).to_string());
    ps("SIDE_BLOCK_START", ints(&sblk));
    ps("N_BLOCKS", nblocks.to_string());
    let bks = lean_vm::cpu::block_kappa_sources(kbc);
    // Push and pull emit bus blocks in matched pairs, so their baked kappa-source
    // segments are identical; the guest computes only push's side total and
    // aliases pull's mu to push's on this basis.
    assert_eq!(
        bks[sblk[0]..sblk[1]],
        bks[sblk[1]..sblk[2]],
        "push/pull kappa sources must match"
    );
    ps(
        "BLOCK_KAPPA_SRC",
        ints(&bks.iter().map(|&(s, _)| s).collect::<Vec<_>>()),
    );
    ps(
        "BLOCK_KAPPA_ADJ",
        ints(&bks.iter().map(|&(_, a)| a).collect::<Vec<_>>()),
    );
    ps(
        "BLOCK_TABLE",
        ints(
            &bks.iter()
                .map(|&(s, _)| if s >= 2 { s - 2 } else { layout.taus.len() })
                .collect::<Vec<_>>(),
        ),
    );
    let mut block_side = Vec::new();
    for (s, blocks) in sides.iter().enumerate() {
        block_side.extend(std::iter::repeat_n(s, blocks.len()));
    }
    ps("BLOCK_SIDE", ints(&block_side));
    ps("BLOCK_COORD_OFF", ints(&bc0));
    ps("BLOCK_COORD_COUNT", ints(&bcn));
    ps("COORD_TYPE", us(&ct));
    ps("COORD_CONST", us(&cval));
    ps("COORD_FRESH", ints(&coord_fresh));
    ps("COORD_CLAIM_SLOT", ints(&coord_slot));
    ps("COORD_TERM_OFF", ints(&coord_toff));
    ps("COORD_TERM_COUNT", ints(&coord_tcount));
    ps("TERM_TYPE", ints(&term_type));
    ps("TERM_CONST", us(&term_const));
    ps("TERM_COL_A", ints(&term_col_a));
    ps("TERM_COL_B", ints(&term_col_b));
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
    ps("INDEX_MLE_FACTORS", us(&idxc));
    ps("N_CLAIMS", ncl.to_string());
    ps("N_TABLES", layout.taus.len().to_string());
    // The table sumcheck's xi layout, from the native verifier's own numbers:
    // a disjoint range of identities per table, then THREE powers shared by every
    // table, one per bus side. Sharing is what lets the target be derived from the
    // three leaf claims instead of trusted (lean_vm::cpu::xi_form_base).
    let n_id: Vec<usize> = lean_vm::tables::tables().iter().map(|t| t.n_constraints()).collect();
    let form_base = lean_vm::cpu::xi_form_base();
    ps(
        "ETA_OFFSET",
        ints(&lean_vm::constraints::xi_offsets(n_id.iter().copied())),
    );
    ps("ETA_FORM_BASE", form_base.to_string());
    ps("N_ETA_POWS", (form_base + 3).to_string());
    let committed: Vec<usize> = lean_vm::tables::tables()
        .iter()
        .map(|t| t.n_committed_columns())
        .collect();
    ps("N_TABLE_COLS", ints(&committed));
    ps("TABLE_COLS_CAP", (committed.iter().max().unwrap() + 1).to_string());
    // Flock univariate skip: 6 skipped variables, then the sampled rounds.
    ps("K_SKIP", flock::zerocheck::K_SKIP.to_string());
    let phi: Vec<F192> = primitives::field::PHI_8_TABLE_192[..128].to_vec();
    ps("PHI8_NODES", flds(&phi));
    // Tower F192 = F64[Y]/(Y^3+Y+1), Y = new(0,1,0). Y_TOWER embeds Y for
    // AIR lane reassembly; Y_INV helps derive the top PI-memory limb.
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
    ps("SLOT_STRIDE_LOG", lean_vm::hash_flock::SLOT_STRIDE_LOG.to_string());

    // ---- LIG candidate tables (fixed [minm, maxm] range; open_stacked config) ----
    let oshape = |m: usize, log_inv_rate: usize| {
        let shape = whir_shape(m, log_inv_rate);
        let (vc, sh) = (&shape.config, &shape.levels);
        let (cn, cr) = (sh.levels, vc.level_steps);
        // The final message sits at the LAST level. The guest fills level_roots slot 0
        // with the commitment root and every later slot from that level's root read,
        // then checks each query's Merkle walk with a write-once store into its slot.
        // A slot no read had filled would turn that check into a write, so this
        // relation is what keeps the query phase binding.
        assert_eq!(cr, cn - 1, "the yr level must be the last one");
        let (ck, cl, cyr) = (sh.ks.clone(), sh.log_msg_cols.clone(), sh.yr_log_n);
        let cq = vc.queries.clone();
        let (cd, cp) = (&shape.depth, &shape.per_squeeze);
        let cs: Vec<usize> = (0..cn).map(|i| cq[i].div_ceil(cp[i])).collect();
        let cni: Vec<usize> = ck.iter().map(|&k| 1usize << k).collect();
        let cqb: Vec<usize> = (0..cn).map(|lvl| vc.grinding_bits[lvl]).collect();
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
        let c_rowoff = psum(&|lv| cq[lv] * cni[lv] * if lv == 0 { 1 } else { 3 });
        let c_pathoff = psum(&|lv| cq[lv] * cd[lv] * 2);
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
            folds: ck,
            log_message_columns: cl,
            queries: cq,
            tree_depths: cd.clone(),
            positions_per_squeeze: cp.clone(),
            squeezes: cs,
            interleaving: cni,
            query_grinding_bits: cqb,
            row_offsets: c_rowoff,
            path_offsets: c_pathoff,
            positions_offsets: c_qpoff,
            vanish_offsets: c_svkoff,
            fold_offsets: c_foldbase,
            residual_fold_offsets: c_risstart,
            vanish_values: c_svk,
            vanish_inverses: c_ivk,
            ood_samples: vc.ood_samples.clone(),
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
    let cks: Vec<(usize, usize)> = lean_vm::cpu::col_kappa_sources(kbc).into_iter().flatten().collect();
    ps("N_COMMITTED_COLS", cks.len().to_string());
    ps("COL_KAPPA_SRC", ints(&cks.iter().map(|&(s, _)| s).collect::<Vec<_>>()));
    ps("COL_KAPPA_ADJ", ints(&cks.iter().map(|&(_, a)| a).collect::<Vec<_>>()));
    ps("PCS_MIN_MU", lean_vm::pcs::MIN_MU.to_string());
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
        let pad = |v: &[usize], stride: usize| -> Vec<usize> {
            let mut padded = v.to_vec();
            padded.resize(stride, 0);
            padded
        };
        let flat = |f: &dyn Fn(&OpeningShape) -> Vec<usize>, stride: usize| -> Vec<usize> {
            cands.iter().flat_map(|c| pad(&f(c), stride)).collect()
        };
        let scal = |f: &dyn Fn(&OpeningShape) -> usize| -> Vec<usize> { cands.iter().map(f).collect() };
        ps("LIG_N_LEVELS", ints(&scal(&|c| c.n_levels)));
        ps("LIG_YR_LEVEL", ints(&scal(&|c| c.yr_level)));
        // The guest rotates the terminal point by the lane-fold count to index it by
        // witness coordinate, and the residual segment is what it rotates the last
        // lane challenges past, so the residual may never be longer than that fold
        // (`RESIDUAL_MAX_LOG` < `INITIAL_FOLDING_FACTOR` keeps this true by a margin).
        assert!(
            cands.iter().all(|c| c.yr_log_len <= c.folds[0]),
            "residual longer than the lane fold: the guest's point rotation has no room"
        );
        ps("LIG_YR_LOG_LEN", ints(&scal(&|c| c.yr_log_len)));
        ps("LIG_YR_LEN", ints(&scal(&|c| 1usize << c.yr_log_len)));
        ps("LIG_TOTAL_FOLDS", ints(&scal(&|c| c.folds.iter().sum())));
        ps("LIG_MAX_QUERIES", ints(&scal(&|c| *c.queries.iter().max().unwrap())));
        ps("LIG_MAX_SQUEEZES", ints(&scal(&|c| *c.squeezes.iter().max().unwrap())));
        ps(
            "LIG_MAX_INTERLEAVE",
            ints(&scal(&|c| *c.interleaving.iter().max().unwrap())),
        );
        // StackBuf cap for the packed leaf row AND the raw-limb `lanes` scratch
        // that shares it (`open_stacked`). Level 0 packs 2 base-field lanes per
        // cell (n/2 cells). Deeper levels first load 3 raw tower limbs per word
        // into `lanes` (3n cells), then pack them into the 3n/2-cell leaf row,
        // so `lanes` (3n) is the binding size there. Sizing the deeper term at
        // 3n/2 happened to hold only while L0's n/2 dominated (small folds);
        // it under-provisions once a deeper interleave exceeds L0's.
        let packed_cells = |c: &Vec<usize>| -> usize {
            c.iter()
                .enumerate()
                .map(|(lv, &n)| if lv == 0 { n / 2 } else { 3 * n })
                .max()
                .unwrap()
        };
        ps(
            "LIG_PACKED_ROW_CAP",
            cands
                .iter()
                .map(|c| packed_cells(&c.interleaving))
                .max()
                .unwrap()
                .to_string(),
        );
        ps(
            "LIG_POSITIONS_LEN",
            ints(&scal(&|c| {
                (0..c.n_levels)
                    .map(|level| c.squeezes[level] * c.positions_per_squeeze[level])
                    .sum()
            })),
        );
        ps(
            "LIG_ROWS_LEN",
            ints(&scal(&|c| {
                (0..c.n_levels)
                    .map(|level| c.queries[level] * c.interleaving[level] * if level == 0 { 1 } else { 3 })
                    .sum()
            })),
        );
        ps(
            "LIG_PATHS_LEN",
            ints(&scal(&|c| {
                (0..c.n_levels)
                    .map(|level| c.queries[level] * c.tree_depths[level] * 2)
                    .sum()
            })),
        );
        ps(
            "LIG_QUERY_GRIND_BITS",
            ints(&flat(&|c| c.query_grinding_bits.clone(), maxlev)),
        );
        ps(
            "LIG_OOD_SAMPLES",
            ints(
                &cands
                    .iter()
                    .flat_map(|shape| pad(&shape.ood_samples, maxlev))
                    .collect::<Vec<_>>(),
            ),
        );
        ps("LIG_QUERIES", ints(&flat(&|c| c.queries.clone(), maxlev)));
        ps("LIG_FOLDS", ints(&flat(&|c| c.folds.clone(), maxlev)));
        ps("LIG_INTERLEAVE", ints(&flat(&|c| c.interleaving.clone(), maxlev)));
        ps(
            "LIG_LEAF_PAIRS",
            ints(&flat(
                &|c| {
                    c.interleaving
                        .iter()
                        .enumerate()
                        .map(|(lv, &n)| if lv == 0 { n / 4 } else { 3 * n / 4 })
                        .collect()
                },
                maxlev,
            )),
        );
        // 64-byte BLAKE2s blocks per leaf row: level 0's committed rows are
        // base-field F64 (8 bytes/lane); deeper levels are native F192
        // (24 bytes/word, received as three embedded K limbs each). Rows are
        // whole blocks only (asserted at candidate construction).
        ps(
            "LIG_LEAF_BLOCKS",
            ints(&flat(
                &|c| {
                    c.interleaving
                        .iter()
                        .enumerate()
                        .map(|(lv, &n)| if lv == 0 { n / 8 } else { 3 * n / 8 })
                        .collect()
                },
                maxlev,
            )),
        );
        ps("LIG_TREE_DEPTH", ints(&flat(&|c| c.tree_depths.clone(), maxlev)));
        ps("LIG_SQUEEZES", ints(&flat(&|c| c.squeezes.clone(), maxlev)));
        ps(
            "LIG_POSITIONS_OFF",
            ints(&flat(&|c| c.positions_offsets.clone(), maxlev)),
        );
        ps(
            "LIG_LOG_MSG_COLS",
            ints(&flat(&|c| c.log_message_columns.clone(), maxlev)),
        );
        ps(
            "LIG_RESIDUAL_FOLD_OFF",
            ints(&flat(&|c| c.residual_fold_offsets.clone(), maxlev)),
        );
        ps(
            "LIG_RESIDUAL_PREFIX_LEN",
            ints(&flat(
                &|c| {
                    c.log_message_columns
                        .iter()
                        .map(|&columns| columns - c.yr_log_len)
                        .collect()
                },
                maxlev,
            )),
        );
        ps("LIG_FOLDS_OFF", ints(&flat(&|c| c.fold_offsets.clone(), maxlev)));
        ps("LIG_ROWS_OFF", ints(&flat(&|c| c.row_offsets.clone(), maxlev)));
        ps("LIG_PATHS_OFF", ints(&flat(&|c| c.path_offsets.clone(), maxlev)));
        ps("LIG_VANISH_OFF", ints(&flat(&|c| c.vanish_offsets.clone(), maxlev)));
        let mut svk2 = Vec::new();
        let mut ivk2 = Vec::new();
        for candidate in &cands {
            let mut values = candidate.vanish_values.clone();
            let mut inverses = candidate.vanish_inverses.clone();
            values.resize(maxsvk, F192::ZERO);
            inverses.resize(maxsvk, F192::ZERO);
            svk2.extend(values);
            ivk2.extend(inverses);
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
    ps("CLAIM_POINT_BUF", ints(&cpbuf));
    ps("CLAIM_COMMITTED_COL", ints(&cpcol));
    let slot_stride_log = lean_vm::hash_flock::SLOT_STRIDE_LOG;
    let cpqbits: Vec<usize> = cpqslot
        .iter()
        .flat_map(|&slot| (0..slot_stride_log).map(move |k| (slot >> k) & 1))
        .collect();
    ps("CLAIM_QFLOCK_SLOT_BITS", ints(&cpqbits));
    ps("QFLOCK_COMMITTED_COL", qflock_compact.to_string());
    ps("QFLOCK_VARS_CAP", (33 + slot_stride_log).to_string());
    ps("BYTECODE_LOG", kbc.to_string());
    // The stacked bytecode: nbcv/2 encoding columns per side, aligned with the bus
    // tuple, so their slots span the fingerprint's own bits. The defer region is
    // 2*kbc points + sel bits + 2 reduced + alpha + z_skip + 2*lcrounds rounds
    // + 64 z_partial + 1 matpart.
    let bc_cols = nbcv / 2;
    let log2_bc_cols = lean_vm::leaf::N_TUPLE_BITS;
    ps("BYTECODE_COLS", bc_cols.to_string());
    ps("LOG2_BYTECODE_COLS", log2_bc_cols.to_string());
    ps("DEFER_SIZE", (kbc + log2_bc_cols + 2 * lcrounds + 68).to_string());
    ps("BYTECODE_VARS", (kbc + log2_bc_cols).to_string());
    let agg_state = pack_state(FiatShamirState::from_label(RECURSION_AGG_LABEL).state());
    ps("AGG_SEED_0", dsl_u128(agg_state[0]).to_string());
    ps("AGG_SEED_1", dsl_u128(agg_state[1]).to_string());
    let defer_cells = kbc + log2_bc_cols + 1 + 2 * flock::hash::K_LOG + 2;
    ps("STMT_HEADER", STATEMENT_HEADER.to_string());
    let (off, pairs) = (STATEMENT_HEADER, defer_cells.div_ceil(2));
    let blocks = (off + 3 * pairs).div_ceil(4);
    ps("STMT_ODD", (defer_cells % 2).to_string());
    ps("STMT_PAIRS", pairs.to_string());
    ps("STMT_PAD_CELLS", (4 * blocks - off - 3 * pairs).to_string());
    ps("STMT_BLOCKS", blocks.to_string());
    let signers_tag = domain_tag(SIGNERS_LABEL);
    ps("SIGNERS_TAG_0", dsl_u128(signers_tag[0]).to_string());
    ps("SIGNERS_TAG_1", dsl_u128(signers_tag[1]).to_string());
    // A list is at most MAX_KEYS blocks (one a claim is the widest it gets), so it
    // holds fewer than that many windows; a declared count is below MAX_KEYS, hence
    // decomposes into that many bits. The first two bound a range check, which takes
    // a COUNT, the third a bit decomposition.
    ps("SIGNERS_WINDOW", SIGNERS_WINDOW.to_string());
    ps("SIGNERS_WINDOW_LOG", SIGNERS_WINDOW.ilog2().to_string());
    ps("SIGNERS_MAX_WINDOWS", SIGNERS_MAX_WINDOWS.to_string());
    ps("SIGNERS_COUNT_BITS", SIGNERS_COUNT_BITS.to_string());
    ps("BLAKE2S_IV_0", dsl_u128(lean_vm::hash_flock::IV_CELLS[0]).to_string());
    ps("BLAKE2S_IV_1", dsl_u128(lean_vm::hash_flock::IV_CELLS[1]).to_string());
    ps(
        "MD_FINAL",
        dsl_u128(lean_vm::hash_flock::metadata(0, lean_vm::hash_flock::FINAL_FLAG, 0)).to_string(),
    );

    // The XMSS instance, from which the guest derives every table width by
    // compile-time integer arithmetic.
    ps("V", xmss::V.to_string());
    ps("W", xmss::W.to_string());
    ps("TARGET_SUM", xmss::TARGET_SUM.to_string());
    ps("LOG_LIFETIME", xmss::LOG_LIFETIME.to_string());
    // Every XMSS tweak the guest builds is one of these constants plus the
    // epoch's weighed bits, so the byte layout lives in `xmss::make_tweak` and
    // nowhere else. The chain table is indexed `CHAIN_STEPS * i + s` and the
    // Merkle one by level, exactly as `verify_sig` walks them.
    ps(
        "XM_ENC_TWEAK",
        dsl_u128(tweak_cell(xmss::TWEAK_TYPE_ENCODING, 0)).to_string(),
    );
    ps(
        "XM_PK_TWEAK",
        dsl_u128(tweak_cell(xmss::TWEAK_TYPE_WOTS_PK, 0)).to_string(),
    );
    let chain_tweaks: Vec<F192> = (0..xmss::V)
        .flat_map(|i| {
            (0..xmss::CHAIN_LENGTH - 1)
                .map(move |s| tweak_cell(xmss::TWEAK_TYPE_CHAIN, (i * xmss::CHAIN_LENGTH + s) as u32))
        })
        .collect();
    ps("XM_CHAIN_TWEAKS", flds(&chain_tweaks));
    let merkle_tweaks: Vec<F192> = (0..xmss::LOG_LIFETIME)
        .map(|level| tweak_cell(xmss::TWEAK_TYPE_MERKLE, (level + 1) as u32))
        .collect();
    ps("XM_MERKLE_TWEAKS", flds(&merkle_tweaks));
    let index_weights: Vec<F192> = (0..xmss::LOG_LIFETIME).map(tweak_index_weight).collect();
    ps("XM_INDEX_WEIGHT", flds(&index_weights));
    ps("MAX_KEYS", MAX_KEYS.to_string());
    ps("MAX_RECURSIONS", MAX_RECURSIONS.to_string());
    ps("MAX_EPOCHS", MAX_EPOCHS.to_string());

    // The SPHINCS instance. Its tweaks are derived per signature from the index
    // the message digest picks, where XMSS's come from one public epoch, so the
    // guest needs only the shape.
    let dsl_list = |values: &[usize]| {
        let inner: Vec<String> = values.iter().map(usize::to_string).collect();
        format!("[{}]", inner.join(", "))
    };
    ps("SP_V", sphincs::V.to_string());
    ps("SP_W", sphincs::W.to_string());
    ps("SP_TARGET_SUM", sphincs::TARGET_SUM.to_string());
    ps("SP_D", sphincs::D.to_string());
    ps("SP_A", sphincs::A.to_string());
    ps("SP_K", sphincs::K.to_string());
    ps("SP_H", sphincs::H.to_string());
    ps("SP_HEIGHTS", dsl_list(&sphincs::HEIGHTS));
    ps("SP_SUFFIX", dsl_list(&sphincs::SUFFIX));
    rep
}

/// Build the guest bytecode and the stacked table its claims are about. Both are
/// cached, so this only moves the cost out of the first prove or verify.
pub fn warm_up() {
    unified_guest();
    stacked_bytecode();
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
        &parse_with_replacements(include_str!("../guests/aggregate.py"), &replacements)
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
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand::rngs::StdRng;

    use crate::signers_cache::{
        KEY_START, XMSS_EPOCH_A, XMSS_EPOCH_B, get_signers, get_signers_at, get_sphincs_signers, message, message_for,
    };

    const SMALL_LEAF_SIZE: usize = 6;
    const LOG_INV_RATE: usize = lean_vm::pcs::TEST_LOG_INV_RATE;

    /// Cached `(key, signature)` pairs as the API takes them, every one at
    /// `epoch` over the cache's message for it.
    fn at_epoch(
        signers: &[(XmssPublicKey, XmssSignature)],
        epoch: xmss::Epoch,
    ) -> Vec<(XmssPublicKey, xmss::Epoch, xmss::Message, XmssSignature)> {
        signers
            .iter()
            .map(|(pk, sig)| (pk.clone(), epoch, message_for(epoch), sig.clone()))
            .collect()
    }

    fn xmss_claims(sig: &AggregateSignature) -> usize {
        sig.xmss_signers.iter().map(|(_, _, keys)| keys.len()).sum()
    }

    /// Distinct keys, strictly increasing, without generating any.
    fn signer_set(len: usize) -> Vec<XmssPublicKey> {
        (0..len)
            .map(|i| XmssPublicKey {
                merkle_root: (i as u128).to_be_bytes(),
                public_param: [0; xmss::PUBLIC_PARAM_LEN],
            })
            .collect()
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

    /// `MAX_KEYS` is exclusive at both host checks: one key short of it passes,
    /// the cap itself is the documented error. The cap counts both schemes, so
    /// one XMSS key short of it plus one SPHINCS claim is already over. No proof
    /// involved, and the epoch cap has its own error alongside.
    #[test]
    fn max_keys_bound_is_exclusive() {
        let full = signer_set(MAX_KEYS);
        let group = |keys: &[XmssPublicKey]| vec![(XMSS_EPOCH_A, message(), keys.to_vec())];
        let claims = |keys: &[XmssPublicKey]| -> Vec<(XmssPublicKey, xmss::Epoch, xmss::Message)> {
            keys.iter().map(|pk| (pk.clone(), XMSS_EPOCH_A, message())).collect()
        };
        let claim = [(
            SphincsPublicKey::from_bytes(&[0; sphincs::PUB_KEY_SIZE]),
            [0; sphincs::MESSAGE_LEN],
        )];
        check_signer_set(&group(&full[..MAX_KEYS - 1]), &[]).expect("one short of the cap");
        assert_eq!(
            check_signer_set(&group(&full), &[]),
            Err(AggregateVerifyError::MalformedSignerSet)
        );
        assert_eq!(
            check_signer_set(&group(&full[..MAX_KEYS - 1]), &claim),
            Err(AggregateVerifyError::MalformedSignerSet)
        );
        // One group per epoch: MAX_EPOCHS groups pass, one more is malformed.
        let spread =
            |n: usize| -> Vec<XmssGroup> { (0..n).map(|e| (e as u32, message(), vec![full[e].clone()])).collect() };
        check_signer_set(&spread(MAX_EPOCHS), &[]).expect("at the epoch cap");
        assert_eq!(
            check_signer_set(&spread(MAX_EPOCHS + 1), &[]),
            Err(AggregateVerifyError::MalformedSignerSet)
        );
        plan_coverage(&claims(&full[..MAX_KEYS - 1]), &[], &[], None).expect("one short of the cap");
        assert_eq!(
            plan_coverage(&claims(&full), &[], &[], None).err(),
            Some(AggregationError::TooLarge)
        );
        assert_eq!(
            plan_coverage(&claims(&full[..MAX_KEYS - 1]), &claim, &[], None).err(),
            Some(AggregationError::TooLarge)
        );
        let spread_claims = |n: usize| -> Vec<(XmssPublicKey, xmss::Epoch, xmss::Message)> {
            (0..n).map(|e| (full[e].clone(), e as u32, message())).collect()
        };
        plan_coverage(&spread_claims(MAX_EPOCHS), &[], &[], None).expect("at the epoch cap");
        assert_eq!(
            plan_coverage(&spread_claims(MAX_EPOCHS + 1), &[], &[], None).err(),
            Some(AggregationError::TooManyEpochs)
        );
    }

    fn prove_leaf(signers: &[(XmssPublicKey, XmssSignature)]) -> AggregateSignature {
        aggregate(&[], at_epoch(signers, XMSS_EPOCH_A), vec![], None, LOG_INV_RATE).expect("leaf aggregates")
    }

    type RawSphincs = (SphincsPublicKey, sphincs::Message, SphincsSignature);

    fn prove_sphincs_leaf(signers: &[RawSphincs]) -> AggregateSignature {
        aggregate(&[], vec![], signers.to_vec(), None, LOG_INV_RATE).expect("leaf aggregates")
    }

    #[test]
    fn aggregate_one_sphincs_signer() {
        lean_vm::init_prover_pool();
        let aggregate = prove_sphincs_leaf(&get_sphincs_signers(1));
        aggregate.verify().expect("verifies");
        assert!(aggregate.xmss_signers.is_empty());
        assert_eq!(aggregate.sphincs_signers.len(), 1);
    }

    #[test]
    fn aggregate_one_signer() {
        lean_vm::init_prover_pool();
        let aggregate = prove_leaf(&get_signers(1));
        aggregate.verify().expect("verifies");
        assert_eq!(aggregate.xmss_signers[0].0, XMSS_EPOCH_A);
        assert_eq!(aggregate.xmss_signers[0].1, message());
    }

    /// An odd XMSS count, so its digest chain takes its odd-key-out branch and
    /// the `pubkeys` stream ends in a short entry; the SPHINCS list has no parity
    /// case, absorbing one entry a frame.
    #[test]
    fn aggregate_mixed_leaf() {
        lean_vm::init_prover_pool();
        let aggregate = aggregate(
            &[],
            at_epoch(&get_signers(3), XMSS_EPOCH_A),
            get_sphincs_signers(3),
            None,
            LOG_INV_RATE,
        )
        .expect("leaf aggregates");
        aggregate.verify().expect("verifies");
        assert_eq!((xmss_claims(&aggregate), aggregate.sphincs_signers.len()), (3, 3));
    }

    /// A node over children of both schemes, overlapping in one signer of each:
    /// the coverage table then needs a duplicate slot in both regions, and each
    /// child's two key lists have to land in their own.
    #[test]
    fn aggregate_mixed_two_to_one() {
        lean_vm::init_prover_pool();
        let xmss = get_signers(6);
        let sphincs = get_sphincs_signers(4);
        let leaf = |x: &[(XmssPublicKey, XmssSignature)], s: &[RawSphincs]| {
            aggregate(&[], at_epoch(x, XMSS_EPOCH_A), s.to_vec(), None, LOG_INV_RATE).expect("leaf aggregates")
        };
        let left = leaf(&xmss[..4], &sphincs[..3]);
        let right = leaf(&xmss[3..], &sphincs[2..]);
        let node = aggregate(&[left, right], vec![], vec![], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!((xmss_claims(&node), node.sphincs_signers.len()), (6, 4));
        assert!(node.xmss_signers[0].2.windows(2).all(|w| w[0] < w[1]));
        assert!(node.sphincs_signers.windows(2).all(|w| w[0] < w[1]));
    }

    /// A node whose children are each of one scheme only: every key list it
    /// rebuilds is empty on one side, which is the only way the guest's
    /// key-absorbing loops run over an empty range and its bound `log(x) <
    /// log(g^0)` (unsatisfiable, so nothing may be written there) is reached.
    #[test]
    fn aggregate_one_scheme_per_child() {
        lean_vm::init_prover_pool();
        let xmss_child = prove_leaf(&get_signers(3));
        let sphincs_child = prove_sphincs_leaf(&get_sphincs_signers(2));
        let node =
            aggregate(&[xmss_child, sphincs_child], vec![], vec![], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!((xmss_claims(&node), node.sphincs_signers.len()), (3, 2));
    }

    /// The repeat the statement allows: one key signing two messages is two
    /// claims, ordered by the pair, each needing its own signature. Generated
    /// here rather than cached, the cache holding one message per key.
    #[test]
    fn aggregate_one_key_two_messages() {
        lean_vm::init_prover_pool();
        let mut rng = StdRng::seed_from_u64(77);
        let (secret_key, public_key) = sphincs::key_gen(&mut rng);
        let raw: Vec<RawSphincs> = [3u8, 9]
            .into_iter()
            .map(|tag| {
                let signed: sphincs::Message = std::array::from_fn(|i| tag.wrapping_mul(i as u8 + 1));
                let signature = sphincs::sign(&mut rng, &secret_key, &signed).expect("signs");
                (public_key, signed, signature)
            })
            .collect();
        let aggregate = prove_sphincs_leaf(&raw);
        aggregate.verify().expect("verifies");
        assert_eq!(aggregate.sphincs_signers.len(), 2);
        let (first, second) = (aggregate.sphincs_signers[0], aggregate.sphincs_signers[1]);
        assert_eq!(first.0, second.0, "the same key, twice");
        assert!(first.1 < second.1, "ordered by the message");
    }

    /// The right leaf holds more keys than one absorb window of its list hash
    /// (`SIGNERS_WINDOW` blocks of two keys), so both that leaf and the parent
    /// rebuilding it run the window loop and then a non-empty tail, while the left
    /// leaf's list is a tail alone. Under a window everywhere, the loop would never
    /// execute and neither would the byte counter's base.
    #[test]
    fn aggregate_two_to_one() {
        lean_vm::init_prover_pool();
        let big = 2 * SIGNERS_WINDOW + 6;
        let signers = get_signers(SMALL_LEAF_SIZE + big);
        let left = prove_leaf(&signers[..SMALL_LEAF_SIZE]);
        let right = prove_leaf(&signers[SMALL_LEAF_SIZE..]);
        let node = aggregate(&[left, right], vec![], vec![], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!(xmss_claims(&node), SMALL_LEAF_SIZE + big);
    }

    /// Two epochs in one tree. Signer `i` holds the same key at both epochs, so
    /// group B repeats keys of group A as distinct claims; the left leaf holds
    /// one epoch, the right both, and the node maps each child group onto its
    /// own region, with a duplicate slot for the key both leaves cover at A.
    /// Enough epoch groups that the set's own hash runs its window loop: its string
    /// is two blocks a group plus a leading two, so it takes sixteen groups to fill
    /// one window of SIGNERS_WINDOW blocks. Every other test stays inside the tail,
    /// where `plain_window` never executes and neither does the byte counter's base.
    #[test]
    fn aggregate_many_epoch_groups() {
        lean_vm::init_prover_pool();
        // Two blocks a group plus a leading two, so SIGNERS_WINDOW / 2 groups make
        // SIGNERS_WINDOW + 2 blocks: one whole window and a tail of one. The cached
        // keys are activated over exactly that many epochs, and one key may claim
        // once per epoch, so a single signer covers them all.
        let groups = SIGNERS_WINDOW / 2;
        let raw: Vec<_> = (0..groups)
            .map(|i| {
                let epoch = KEY_START + i as xmss::Epoch;
                let (public_key, signature) = get_signers_at(1, epoch).remove(0);
                (public_key, epoch, message_for(epoch), signature)
            })
            .collect();
        let leaf = aggregate(&[], raw, vec![], None, LOG_INV_RATE).expect("many-group leaf aggregates");
        leaf.verify().expect("it verifies");
        assert_eq!(leaf.xmss_signers.len(), groups);
        assert!(leaf.xmss_signers.iter().all(|(_, _, keys)| keys.len() == 1));
    }

    /// A whole `(epoch, message)` needs the table's undeclared groups; keys of a group
    /// that stays need only its duplicate slots. The first narrowing does one, the
    /// second both.
    #[test]
    fn a_node_may_publish_less_than_it_covers() {
        lean_vm::init_prover_pool();
        let at_a = get_signers(3);
        let at_b = get_signers_at(2, XMSS_EPOCH_B);
        let mut raw = at_epoch(&at_a, XMSS_EPOCH_A);
        raw.extend(at_epoch(&at_b, XMSS_EPOCH_B));
        let wide = aggregate(&[], raw, vec![], None, LOG_INV_RATE).expect("the wide leaf aggregates");
        wide.verify().expect("the wide leaf verifies");
        assert_eq!(wide.xmss_signers.len(), 2);
        assert_eq!(xmss_claims(&wide), 5);

        let narrowed = |wide: &AggregateSignature, declare: &WireKeys| {
            aggregate(std::slice::from_ref(wide), vec![], vec![], Some(declare), LOG_INV_RATE)
        };
        let (group_a, group_b) = (wide.xmss_signers[0].clone(), wide.xmss_signers[1].clone());

        // One group declared: the other's epoch and message go with it.
        let narrow = narrowed(&wide, &(vec![group_b.clone()], vec![])).expect("narrows to one group");
        narrow.verify().expect("the one-group narrowing verifies");
        assert_eq!(narrow.xmss_signers, vec![group_b.clone()]);

        // One key of one group: B goes whole, A keeps one of three.
        let one_of_a = (XMSS_EPOCH_A, message(), vec![group_a.2[0].clone()]);
        let part = narrowed(&wide, &(vec![one_of_a.clone()], vec![])).expect("narrows to one key");
        part.verify().expect("the one-key narrowing verifies");
        assert_eq!(part.xmss_signers, vec![one_of_a]);

        assert_eq!(
            narrowed(&wide, &(vec![], vec![])).err(),
            Some(AggregationError::Empty),
            "a declaration has to publish something"
        );
        // A key A holds and B does not, declared at B: the cache reuses keys.
        let only_at_a = group_a
            .2
            .iter()
            .find(|key| !group_b.2.contains(key))
            .expect("A holds a key B does not")
            .clone();
        assert_eq!(
            narrowed(
                &wide,
                &(vec![(XMSS_EPOCH_B, message_for(XMSS_EPOCH_B), vec![only_at_a])], vec![])
            )
            .err(),
            Some(AggregationError::NotCovered)
        );
        // A covered key, against another message.
        assert_eq!(
            narrowed(
                &wide,
                &(
                    vec![(XMSS_EPOCH_A, message_for(XMSS_EPOCH_B), group_a.2.clone())],
                    vec![]
                )
            )
            .err(),
            Some(AggregationError::NotCovered)
        );

        // Putting the group back is a different signer set, whatever it covered.
        let mut rewidened = narrow.clone();
        rewidened.xmss_signers.insert(0, wide.xmss_signers[0].clone());
        assert!(
            rewidened.verify().is_err(),
            "a split may not be re-widened after the fact"
        );
    }

    /// The guest walks raw signatures group by group over the table, and a
    /// declaration puts the undeclared groups last, so the table stops agreeing with
    /// the epoch order `raw_xmss` is sorted by. Declaring only the HIGHER epoch is
    /// what separates the two: the table becomes [B, A] while the raw stream starts
    /// with A, and a signature verified against the wrong group's tweaks fails.
    #[test]
    fn raw_signatures_follow_the_table_not_the_epochs() {
        lean_vm::init_prover_pool();
        const _: () = assert!(XMSS_EPOCH_A < XMSS_EPOCH_B, "A must sort first for this to bite");
        let a = get_signers(1);
        let b = get_signers_at(1, XMSS_EPOCH_B);
        let mut raw = at_epoch(&a, XMSS_EPOCH_A);
        raw.extend(at_epoch(&b, XMSS_EPOCH_B));
        let group_b = (XMSS_EPOCH_B, message_for(XMSS_EPOCH_B), vec![b[0].0.clone()]);
        let sig = aggregate(&[], raw, vec![], Some(&(vec![group_b.clone()], vec![])), LOG_INV_RATE)
            .expect("the narrowing leaf aggregates");
        sig.verify().expect("it verifies");
        assert_eq!(sig.xmss_signers, vec![group_b]);
    }

    #[test]
    fn aggregate_two_epochs() {
        lean_vm::init_prover_pool();
        let at_a = get_signers(4);
        let at_b = get_signers_at(2, XMSS_EPOCH_B);
        assert_eq!(at_a[0].0, at_b[0].0, "the cache reuses keys across epochs");
        let left = aggregate(&[], at_epoch(&at_a[..3], XMSS_EPOCH_A), vec![], None, LOG_INV_RATE).expect("left");
        let mut right_raw = at_epoch(&at_a[2..], XMSS_EPOCH_A);
        right_raw.extend(at_epoch(&at_b, XMSS_EPOCH_B));
        let right = aggregate(&[], right_raw, vec![], None, LOG_INV_RATE).expect("right");
        right.verify().expect("the two-epoch leaf verifies");
        // A claim at epoch A under B's message conflicts with `left`'s group:
        // within an aggregate the message is a function of the epoch.
        let (pk, _, _, sig) = at_epoch(&at_a[3..], XMSS_EPOCH_A).remove(0);
        assert_eq!(
            aggregate(
                std::slice::from_ref(&left),
                vec![(pk, XMSS_EPOCH_A, message_for(XMSS_EPOCH_B), sig)],
                vec![],
                None,
                LOG_INV_RATE,
            )
            .err(),
            Some(AggregationError::ConflictingMessages)
        );
        let node = aggregate(&[left, right], vec![], vec![], None, LOG_INV_RATE).expect("node");
        node.verify().expect("the two-epoch node verifies");
        let messages: Vec<xmss::Message> = node.xmss_signers.iter().map(|(_, message, _)| *message).collect();
        assert_eq!(messages, vec![message(), message_for(XMSS_EPOCH_B)]);
        let epochs: Vec<xmss::Epoch> = node.xmss_signers.iter().map(|(epoch, _, _)| *epoch).collect();
        assert_eq!(epochs, vec![XMSS_EPOCH_A, XMSS_EPOCH_B]);
        assert_eq!(node.xmss_signers[0].2.len(), 4);
        let mut b_keys: Vec<XmssPublicKey> = at_b.iter().map(|(pk, _)| pk.clone()).collect();
        b_keys.sort();
        assert_eq!(
            node.xmss_signers[1].2, b_keys,
            "the same keys, at B, are their own claims"
        );
        // Statement tampers: no proving, the mutated aggregate just has to fail.
        let tampered = |mutate: &dyn Fn(&mut AggregateSignature)| {
            let mut bad = node.clone();
            mutate(&mut bad);
            assert!(bad.verify().is_err(), "a tampered aggregate must not verify");
        };
        tampered(&|s| s.xmss_signers.swap(0, 1));
        tampered(&|s| s.xmss_signers[1].0 = XMSS_EPOCH_B + 1);
        tampered(&|s| {
            let moved = s.xmss_signers[1].2.pop().expect("a key to move");
            s.xmss_signers[0].2.push(moved);
            s.xmss_signers[0].2.sort();
            s.xmss_signers[0].2.dedup();
        });
        tampered(&|s| {
            // Relabel group B's claims as group A's: B's keys are already among
            // A's, so this folds the two groups into one.
            let (_, _, keys) = s.xmss_signers.remove(1);
            s.xmss_signers[0].2.extend(keys);
            s.xmss_signers[0].2.sort();
            s.xmss_signers[0].2.dedup();
        });
    }

    #[test]
    fn aggregate_overlapping_signers() {
        lean_vm::init_prover_pool();
        let signers = get_signers(40);
        let left = prove_leaf(&signers[..25]);
        let right = prove_leaf(&signers[15..]);
        let node = aggregate(&[left, right], vec![], vec![], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!(xmss_claims(&node), 40);
        assert!(node.xmss_signers[0].2.windows(2).all(|w| w[0] < w[1]));
    }

    /// Three levels, both schemes. The SPHINCS claims are rebuilt twice over, once
    /// into each node and again into the root, and the two nodes share one claim,
    /// so the root needs a SPHINCS duplicate slot for a claim it never saw
    /// directly. The root also adds a raw signature of each scheme alongside its
    /// children.
    #[test]
    #[ignore]
    fn aggregate_three_levels() {
        lean_vm::init_prover_pool();
        let signers = get_signers(4 * SMALL_LEAF_SIZE);
        let claims = get_sphincs_signers(5);
        let leaf = |index: usize, sphincs: &[RawSphincs]| {
            aggregate(
                &[],
                at_epoch(
                    &signers[index * SMALL_LEAF_SIZE..(index + 1) * SMALL_LEAF_SIZE],
                    XMSS_EPOCH_A,
                ),
                sphincs.to_vec(),
                None,
                LOG_INV_RATE,
            )
            .expect("leaf aggregates")
        };
        let node = |children: &[AggregateSignature]| {
            aggregate(children, vec![], vec![], None, LOG_INV_RATE).expect("node aggregates")
        };
        // Claim 1 is under both nodes; claim 4 arrives raw at the root, and so
        // do two XMSS signatures at a second epoch, so the root holds a group
        // its children never carried.
        let left = node(&[leaf(0, &claims[..2]), leaf(1, &[])]);
        let right = node(&[leaf(2, &claims[1..3]), leaf(3, &[])]);
        let root = aggregate(
            &[left, right],
            at_epoch(&get_signers_at(2, XMSS_EPOCH_B), XMSS_EPOCH_B),
            claims[4..].to_vec(),
            None,
            LOG_INV_RATE,
        )
        .expect("root aggregates");
        root.verify().expect("root verifies");
        assert_eq!(xmss_claims(&root), 4 * SMALL_LEAF_SIZE + 2);
        assert_eq!(root.xmss_signers.len(), 2, "the raw epoch-B group joins the children's");
        assert_eq!(root.sphincs_signers.len(), 4, "claims 0, 1, 2 and 4, the repeat merged");
        assert!(
            root.xmss_signers
                .iter()
                .all(|(_, _, k)| k.windows(2).all(|w| w[0] < w[1]))
        );
        assert!(root.sphincs_signers.windows(2).all(|w| w[0] < w[1]));
    }

    #[test]
    #[ignore]
    fn aggregate_statement_binds() {
        lean_vm::init_prover_pool();
        let signers = get_signers(2 * SMALL_LEAF_SIZE);
        let left = prove_leaf(&signers[..SMALL_LEAF_SIZE]);
        let right = prove_leaf(&signers[SMALL_LEAF_SIZE..]);
        // Mixed, so both published lists are non-empty and every tampering
        // below has a SPHINCS counterpart.
        let node = aggregate(&[left, right], vec![], get_sphincs_signers(3), None, LOG_INV_RATE).expect("node");
        node.verify().expect("the honest node verifies");

        assert_eq!(
            AggregateSignature::from_bytes(&node.to_bytes())
                .expect("round trip")
                .to_bytes(),
            node.to_bytes(),
            "the wire format round-trips, recomputed claim values included"
        );
        let without = AggregateSignature::from_bytes_without_pubkeys(
            &node.to_bytes_without_pubkeys(),
            (node.xmss_signers.clone(), node.sphincs_signers.clone()),
        )
        .expect("round trip");
        without.verify().expect("a caller-supplied signer set verifies");

        let tampered = |mutate: &dyn Fn(&mut AggregateSignature)| {
            let mut bad = node.clone();
            mutate(&mut bad);
            assert!(bad.verify().is_err(), "a tampered aggregate must not verify");
        };
        tampered(&|s| s.xmss_signers[0].2[0] = s.xmss_signers[0].2[1].clone());
        tampered(&|s| {
            s.xmss_signers[0].2.swap(0, 1);
        });
        tampered(&|s| {
            s.xmss_signers[0].2.pop();
        });
        tampered(&|s| s.sphincs_signers[0] = s.sphincs_signers[1]);
        tampered(&|s| {
            s.sphincs_signers.swap(0, 1);
        });
        tampered(&|s| {
            s.sphincs_signers.pop();
        });
        // Relabelling a signer's scheme: the same 32 bytes moved to the other
        // list. Every count and the splits between them are in the statement, and
        // the guest holds each region's writers to that region, so this is
        // not a free relabelling of what the aggregate claims.
        tampered(&|s| {
            let moved = s.xmss_signers[0].2.remove(0);
            let claimed = (SphincsPublicKey::from_bytes(&moved.flatten()), s.xmss_signers[0].1);
            s.sphincs_signers.push(claimed);
            s.sphincs_signers.sort();
        });
        tampered(&|s| s.xmss_signers[0].0 += 1);
        tampered(&|s| s.xmss_signers[0].1[0] ^= 1);
        // A signer's own message is in the statement too, so editing it is not a
        // free re-attribution of that signature to another message.
        tampered(&|s| s.sphincs_signers[0].1[0] ^= 1);
        tampered(&|s| s.defer.bytecode_point[0] += F192::ONE);
        tampered(&|s| s.defer.matrix_point[0] += F192::ONE);
        tampered(&|s| s.xmss_signers[0].2[0] = get_signers(2 * SMALL_LEAF_SIZE + 1)[2 * SMALL_LEAF_SIZE].0.clone());
        // Splitting one group's keys across two epochs: the same claims cannot
        // be re-attributed to an epoch nothing signed at.
        tampered(&|s| {
            let moved = s.xmss_signers[0].2.pop().expect("a key to move");
            let epoch = s.xmss_signers[0].0;
            let message = s.xmss_signers[0].1;
            s.xmss_signers.push((epoch + 1, message, vec![moved]));
        });

        // A claim off the wire carries only its points. Tampering with either
        // half must be caught: a point by the recomputation, a value by the
        // statement the proof is checked against.
        let from_wire = |mutate: &dyn Fn(&mut AggregateSignature)| {
            let mut bad = AggregateSignature::from_bytes(&node.to_bytes()).expect("round trip");
            mutate(&mut bad);
            assert!(bad.verify().is_err(), "a tampered wire aggregate must not verify");
        };
        from_wire(&|s| s.defer.bytecode_point[0] += F192::ONE);
        from_wire(&|s| s.defer.matrix_point[0] += F192::ONE);
        from_wire(&|s| s.defer.bytecode_value += F192::ONE);
        from_wire(&|s| s.defer.matrix_a_value += F192::ONE);
        from_wire(&|s| s.defer.matrix_b_value += F192::ONE);
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

    type Tamper<'a> = (&'a str, &'a dyn Fn(&mut Hints));

    /// Corrupt each security-critical hint and require rejection.
    #[test]
    #[ignore]
    fn aggregate_hints_bind() {
        lean_vm::init_prover_pool();
        let signers = get_signers(2 * SMALL_LEAF_SIZE);

        let rejects = |children: &[AggregateSignature],
                       raw_signatures: Vec<(XmssPublicKey, xmss::Epoch, xmss::Message, XmssSignature)>,
                       raw_sphincs: Vec<RawSphincs>,
                       description: &str,
                       tamper: &dyn Fn(&mut Hints)| {
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                aggregate_tampered(children, raw_signatures, raw_sphincs, None, LOG_INV_RATE, |hints| {
                    tamper(hints)
                })
                .map(|(signature, _)| signature.verify().is_ok())
            }));
            assert!(
                !matches!(outcome, Ok(Ok(true))),
                "tampering {description} must be rejected"
            );
        };

        let raw_signatures = at_epoch(&signers[..SMALL_LEAF_SIZE], XMSS_EPOCH_A);
        prove_leaf(&signers[..SMALL_LEAF_SIZE]);
        let leaf_cases: &[Tamper] = &[
            ("raw_index (duplicate slot)", &|h: &mut Hints| {
                let entries = h.entries("raw_index");
                entries[1] = entries[0].clone();
            }),
            ("raw_index (out of range)", &|h: &mut Hints| {
                h.entries("raw_index")[0] = vec![count(SMALL_LEAF_SIZE)];
            }),
            ("group (n_xmss inflated)", &|h: &mut Hints| {
                h.entries("group")[0][3] = count(SMALL_LEAF_SIZE + 1);
            }),
            ("group (n_raw_xmss understated)", &|h: &mut Hints| {
                h.entries("group")[0][5] = count(SMALL_LEAF_SIZE - 1);
            }),
            ("group (a spurious duplicate slot)", &|h: &mut Hints| {
                h.entries("group")[0][4] = count(1);
            }),
            // One more group than the hint stream carries: witness generation
            // has nothing to pop for it.
            ("meta (n_epochs inflated)", &|h: &mut Hints| {
                h.entries("meta")[0][0] = count(2);
            }),
            ("pubkeys (a key nobody signed for)", &|h: &mut Hints| {
                h.entries("pubkeys")[0][0] += F192::ONE;
            }),
            // The window split of a list hash is advice, so both halves are pinned:
            // the product identity ties them to the block count, and the tail's own
            // range check keeps its `match` dispatch on a real arm.
            (
                "signers_split (a window count the list does not have)",
                &|h: &mut Hints| {
                    h.entries("signers_split")[0][0] = count(1);
                },
            ),
            ("signers_split (a tail past a whole window)", &|h: &mut Hints| {
                h.entries("signers_split")[0][1] = count(SIGNERS_WINDOW);
            }),
            ("fs_seed", &|h: &mut Hints| {
                h.entries("fs_seed")[0][0] += F192::ONE;
            }),
            ("leaf_defer", &|h: &mut Hints| {
                h.entries("leaf_defer")[0][0] += F192::ONE;
            }),
            // A leaf derives its group's tweak table from this, so a wrong
            // epoch is caught by the signatures long before the statement digest.
            ("group (another epoch's tweak table)", &|h: &mut Hints| {
                h.entries("group")[0][0] += F192::ONE;
            }),
            ("group (wider than the u32 the verifier holds)", &|h: &mut Hints| {
                h.entries("group")[0][0] += F192::new(0, 1, 0);
            }),
            // The group's signatures were made over another message, so the
            // encoding digests reject long before the statement digest.
            ("group (another message under the signatures)", &|h: &mut Hints| {
                h.entries("group")[0][1] += F192::ONE;
            }),
        ];
        for (description, tamper) in leaf_cases {
            rejects(&[], raw_signatures.clone(), vec![], description, *tamper);
        }

        // A leaf holding two epoch groups: the second group's region is one
        // slot, so its writer cannot reach the first group's keys, and the two
        // groups' tweak tables cannot be swapped.
        let mut two_epoch_raw = at_epoch(&signers[..2], XMSS_EPOCH_A);
        two_epoch_raw.extend(at_epoch(&get_signers_at(1, XMSS_EPOCH_B), XMSS_EPOCH_B));
        aggregate(&[], two_epoch_raw.clone(), vec![], None, LOG_INV_RATE)
            .expect("the honest two-epoch leaf aggregates");
        let two_epoch_cases: &[Tamper] = &[
            (
                "raw_index (an XMSS signature crossing into another epoch's region)",
                &|h: &mut Hints| {
                    h.entries("raw_index")[2] = vec![count(1)];
                },
            ),
            ("group (two epochs swapped)", &|h: &mut Hints| {
                let entries = h.entries("group");
                let other = entries[1][0];
                entries[1][0] = entries[0][0];
                entries[0][0] = other;
            }),
            ("group (a group's count moved to the other)", &|h: &mut Hints| {
                h.entries("group")[0][3] = count(1);
                h.entries("group")[1][3] = count(2);
            }),
            // The declared count is advice: keep both table groups but hash only the
            // first, while the statement still publishes both.
            ("meta (a published group left out of the digest)", &|h: &mut Hints| {
                h.entries("meta")[0][0] = count(1);
                h.entries("meta")[0][1] = count(1);
            }),
        ];
        for (description, tamper) in two_epoch_cases {
            rejects(&[], two_epoch_raw.clone(), vec![], description, *tamper);
        }

        // A mixed leaf: three XMSS signers then two SPHINCS ones, so the XMSS
        // region is slots 0..3 and the SPHINCS region 3..5. Each scheme's
        // witness has to bind, and neither scheme's signature may cover the
        // other's declared key, which is what the statement's split claims.
        let mixed_xmss = at_epoch(&signers[..3], XMSS_EPOCH_A);
        let mixed_sphincs = get_sphincs_signers(2);
        aggregate(&[], mixed_xmss.clone(), mixed_sphincs.clone(), None, LOG_INV_RATE)
            .expect("the honest mixed leaf aggregates");
        let mixed_cases: &[Tamper] = &[
            (
                "raw_index (an XMSS signature reaching the SPHINCS region)",
                &|h: &mut Hints| {
                    h.entries("raw_index")[0] = vec![count(3)];
                },
            ),
            ("sp_raw_index (out of range)", &|h: &mut Hints| {
                h.entries("sp_raw_index")[0] = vec![count(2)];
            }),
            ("sp_raw_index (duplicate slot)", &|h: &mut Hints| {
                let entries = h.entries("sp_raw_index");
                entries[1] = entries[0].clone();
            }),
            ("meta (n_sphincs inflated)", &|h: &mut Hints| {
                h.entries("meta")[0][1] = count(3);
            }),
            ("meta (n_raw_sphincs understated)", &|h: &mut Hints| {
                h.entries("meta")[0][3] = count(1);
            }),
            ("sphincs_signers (a message nobody signed)", &|h: &mut Hints| {
                h.entries("sphincs_signers")[0][2] += F192::ONE;
            }),
            ("sphincs_signers (a key nobody signed for)", &|h: &mut Hints| {
                h.entries("sphincs_signers")[0][0] += F192::ONE;
            }),
            ("sp_rand (another randomizer, so another index)", &|h: &mut Hints| {
                h.entries("sp_rand")[0][0] += F192::ONE;
            }),
            ("sp_counter", &|h: &mut Hints| {
                h.entries("sp_counter")[0][0] += F192::ONE;
            }),
            ("sp_digits", &|h: &mut Hints| {
                let entries = h.entries("sp_digits");
                entries[0][0] *= F192::from(primitives::field::G);
            }),
            ("sp_chain_starts", &|h: &mut Hints| {
                h.entries("sp_chain_starts")[0][0] += F192::ONE;
            }),
            ("sp_fts_secrets", &|h: &mut Hints| {
                h.entries("sp_fts_secrets")[0][0] += F192::ONE;
            }),
            ("sp_fts_paths", &|h: &mut Hints| {
                h.entries("sp_fts_paths")[0][0] += F192::ONE;
            }),
            ("sp_siblings", &|h: &mut Hints| {
                h.entries("sp_siblings")[0][0] += F192::ONE;
            }),
        ];
        for (description, tamper) in mixed_cases {
            rejects(&[], mixed_xmss.clone(), mixed_sphincs.clone(), description, *tamper);
        }

        let left = prove_leaf(&signers[..SMALL_LEAF_SIZE]);
        let right = prove_leaf(&signers[SMALL_LEAF_SIZE..]);
        let children = vec![left, right];
        aggregate(&children, vec![], vec![], None, LOG_INV_RATE).expect("the honest node aggregates");
        let node_cases: &[Tamper] = &[
            ("child_index (duplicate slot)", &|h: &mut Hints| {
                let entries = h.entries("child_index");
                entries[1] = entries[0].clone();
            }),
            ("child_index (out of range)", &|h: &mut Hints| {
                h.entries("child_index")[0] = vec![count(2 * SMALL_LEAF_SIZE)];
            }),
            ("child_group (count understated)", &|h: &mut Hints| {
                h.entries("child_group")[0][3] = count(SMALL_LEAF_SIZE - 1);
            }),
            // A child group claimed at an epoch or under a message the child
            // never carried: the map equality or the rebuilt digest rejects.
            ("child_group (epoch)", &|h: &mut Hints| {
                h.entries("child_group")[0][0] += F192::ONE;
            }),
            ("child_group (message)", &|h: &mut Hints| {
                h.entries("child_group")[0][1] += F192::ONE;
            }),
            ("child_defer (a forged carried claim)", &|h: &mut Hints| {
                h.entries("child_defer")[0][0] += F192::ONE;
            }),
            ("bc_star_hint", &|h: &mut Hints| {
                h.entries("bc_star_hint")[0][0] += F192::ONE;
            }),
            ("mat_stars_hint", &|h: &mut Hints| {
                h.entries("mat_stars_hint")[0][0] += F192::ONE;
            }),
            ("rs_nover", &|h: &mut Hints| {
                h.entries("rs_nover")[0][0] *= F192::from(primitives::field::G);
            }),
            // The one hint carrying flock's whole lincheck terminal. Pinned not
            // by the guest's own assert (which merely defines it) but by the
            // matrix batching, whose reduced claims the root discharges against
            // the real A_0/B_0.
            ("matpart", &|h: &mut Hints| {
                h.entries("matpart")[0][0] += F192::ONE;
            }),
            // A node holding no raw XMSS signature builds no tweak tables, so
            // the statement digest is all that pins its epochs. The children's
            // epochs must then land on slots of this altered list, and the map
            // equality has no target, so the node cannot be proven.
            (
                "group (a node that derives nothing from the epoch)",
                &|h: &mut Hints| {
                    h.entries("group")[0][0] += F192::ONE;
                },
            ),
        ];
        for (description, tamper) in node_cases {
            rejects(&children, vec![], vec![], description, *tamper);
        }

        // A node over children of two different epochs: the hinted group map is
        // what ties each child's group to the parent region of the same epoch.
        let epoch_children = vec![
            prove_leaf(&signers[..2]),
            aggregate(
                &[],
                at_epoch(&get_signers_at(2, XMSS_EPOCH_B), XMSS_EPOCH_B),
                vec![],
                None,
                LOG_INV_RATE,
            )
            .expect("the honest epoch-B leaf aggregates"),
        ];
        aggregate(&epoch_children, vec![], vec![], None, LOG_INV_RATE).expect("the honest two-epoch node aggregates");
        let epoch_node_cases: &[Tamper] = &[
            // Pointing the second child's group at the parent's epoch-A region:
            // the epochs disagree, so the map equality fails.
            ("child_group_map (a group mapped across epochs)", &|h: &mut Hints| {
                h.entries("child_group_map")[1][0] = count(0);
            }),
            ("child_group_map (out of range)", &|h: &mut Hints| {
                h.entries("child_group_map")[0][0] = count(2);
            }),
        ];
        for (description, tamper) in epoch_node_cases {
            rejects(&epoch_children, vec![], vec![], description, *tamper);
        }

        // The same discipline over a child's SPHINCS claims, which are rebuilt by
        // their own loop (`hash_child_sphincs`) rather than the XMSS helper, so
        // the cases above do not reach them: these children carry claims.
        let sphincs = get_sphincs_signers(4);
        let mixed_child = |x: &[(XmssPublicKey, XmssSignature)], s: &[RawSphincs]| {
            aggregate(&[], at_epoch(x, XMSS_EPOCH_A), s.to_vec(), None, LOG_INV_RATE)
                .expect("the honest mixed child aggregates")
        };
        let mixed_children = vec![
            mixed_child(&signers[..2], &sphincs[..2]),
            mixed_child(&signers[2..4], &sphincs[2..]),
        ];
        let mixed_node_cases: &[Tamper] = &[
            ("child_sphincs_index (duplicate slot)", &|h: &mut Hints| {
                let entries = h.entries("child_sphincs_index");
                entries[1] = entries[0].clone();
            }),
            ("child_sphincs_index (out of range)", &|h: &mut Hints| {
                h.entries("child_sphincs_index")[0] = vec![count(4)];
            }),
            ("child_meta (a child's SPHINCS count understated)", &|h: &mut Hints| {
                h.entries("child_meta")[0][1] = count(1);
            }),
        ];
        for (description, tamper) in mixed_node_cases {
            rejects(&mixed_children, vec![], vec![], description, *tamper);
        }
    }

    #[test]
    #[ignore]
    fn aggregate_rejects_a_bad_signature() {
        lean_vm::init_prover_pool();
        let mut raw_signatures = at_epoch(&get_signers(3), XMSS_EPOCH_A);
        raw_signatures[1].3.wots_signature.chain_tips[0][0] ^= 1;
        let built = std::panic::catch_unwind(|| {
            aggregate(&[], raw_signatures, vec![], None, LOG_INV_RATE).map(|signature| signature.verify().is_ok())
        });
        assert!(
            !matches!(built, Ok(Ok(true))),
            "a forged signature must not produce a verifying aggregate"
        );

        let mut raw_sphincs = get_sphincs_signers(2);
        raw_sphincs[1].2.ots[2][0][0] ^= 1;
        let built = std::panic::catch_unwind(|| {
            aggregate(&[], vec![], raw_sphincs, None, LOG_INV_RATE).map(|signature| signature.verify().is_ok())
        });
        assert!(
            !matches!(built, Ok(Ok(true))),
            "a forged SPHINCS signature must not produce a verifying aggregate"
        );
    }

    /// Randomness that does not decode to a target-sum encoding used to panic
    /// the hint builder; it is a typed error now, and the abandoned builder
    /// leaves nothing behind.
    #[test]
    fn malformed_raw_signature_is_an_error() {
        let message = message();
        let pk = XmssPublicKey {
            merkle_root: [0; xmss::DIGEST_LEN],
            public_param: [0; xmss::PUBLIC_PARAM_LEN],
        };
        let randomness = (0..=u8::MAX)
            .find_map(|byte| {
                let mut randomness = [0; xmss::RANDOMNESS_LEN];
                randomness[0] = byte;
                xmss::wots_encode(&message, XMSS_EPOCH_A, &pk.public_param, &randomness)
                    .is_none()
                    .then_some(randomness)
            })
            .expect("some randomness fails the target sum");
        let sig = XmssSignature {
            wots_signature: xmss::WotsSignature {
                chain_tips: [[0; xmss::DIGEST_LEN]; xmss::V],
                randomness,
            },
            merkle_proof: [[0; xmss::DIGEST_LEN]; xmss::LOG_LIFETIME],
        };

        let mut hints = Hints::default();
        assert_eq!(
            push_signature_hints(&mut hints, &pk, &sig, &message, XMSS_EPOCH_A),
            Err(AggregationError::MalformedRawSignature)
        );
        assert!(hints.0.is_empty());
        assert_eq!(
            aggregate(&[], vec![(pk, XMSS_EPOCH_A, message, sig)], vec![], None, LOG_INV_RATE).err(),
            Some(AggregationError::MalformedRawSignature)
        );
    }

    /// The same for a SPHINCS claim, whose witness walk is equally fallible: a
    /// counter that does not encode has no witness, and that is an error rather
    /// than a panic inside the prover.
    #[test]
    fn malformed_raw_sphincs_signature_is_an_error() {
        let (public_key, signed, mut signature) = get_sphincs_signers(1).pop().expect("one signer");
        signature.counters[sphincs::D - 1] ^= 1;
        assert!(sphincs::verify(&public_key, &signed, &signature).is_err());
        let raw = vec![(public_key, signed, signature)];
        assert_eq!(
            aggregate(&[], vec![], raw, None, LOG_INV_RATE).err(),
            Some(AggregationError::MalformedRawSignature)
        );
    }

    /// Every `BLAKE2s` the guest itself runs reads a metadata cell an earlier
    /// instruction of its own function wrote: a `SET` for a compile-time counter,
    /// an `XOR` for a window's base plus its offset. An unwritten cell is
    /// prover-chosen (write-once memory constrains only what something writes), so
    /// a compression whose metadata nothing writes would hand the prover that
    /// hash's byte counter and both flags, and every guest digest rests on those
    /// being the ones the scheme specifies. The fill blocks are the deliberate
    /// exception: their dummy reads a cell nothing writes, and nothing reads what
    /// they compress (`lean_vm::cpu::filler`).
    ///
    /// This is a scan by pc, not a dominance check: a writer sitting in a branch
    /// nobody took would satisfy it. What makes naming such a cell impossible is
    /// `FnLower::scoped` reverting the constant pool at every join, and the
    /// `blake2s_default_iv_*` tests are what guard that, by proving both paths.
    #[test]
    fn every_guest_blake2s_metadata_cell_is_written_first() {
        use lean_vm::cpu::{DerefMode, Op};

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
        let fill: Vec<std::ops::Range<usize>> = program
            .filler
            .iter()
            .map(|b| b.pc as usize..(b.pc + b.size) as usize)
            .collect();
        let mut unwritten = Vec::new();
        for (name, entry, len) in &program.fn_ranges {
            let range = *entry as usize..(*entry + *len) as usize;
            for pc in range.clone() {
                let Op::Blake2s { md, .. } = program.prog[pc] else {
                    continue;
                };
                if fill.iter().any(|f| f.contains(&pc)) {
                    continue;
                }
                if !program.prog[range.start..pc].iter().any(|op| written(op).contains(&md)) {
                    unwritten.push(format!("{name} pc {pc} md fp[{md}]"));
                }
            }
        }
        assert!(unwritten.is_empty(), "metadata cell never written: {unwritten:?}");
    }
}
