//! Hint streams and the raw signatures' witnesses.

use super::cells::{count, exponent_bytes, pack_16_bytes};
use super::error::AggregateError;
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_vm_core::cpu::to_scalar;
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use primitives::field::F128;

// Both schemes' one-time keys go through the guest's one WOTS+C walk: the same chain
// length and digits dispatched a group at a time. leanSPHINCS groups DIGIT_GROUP
// digits, the last chain alone; leanXMSS LX_DIGIT_GROUP, then the rest. A chain step's
// address leaves out the chain index in leanXMSS, where it follows the value.
pub(super) const DIGIT_GROUP: usize = 3;
/// The guest's `LX_DIGIT_GROUP`.
pub(super) const LX_DIGIT_GROUP: usize = 4;
/// The guest's `LX_WINDOW`: index bits a path dispatch covers.
pub(super) const LX_WINDOW: usize = 8;
const _: () = assert!(
    lean_sphincs::internals::W * lean_sphincs::internals::V == 128 && lean_sphincs::internals::V % DIGIT_GROUP == 1
);
const _: () = assert!(
    lean_xmss::internals::W == lean_sphincs::internals::W && !lean_xmss::internals::V.is_multiple_of(LX_DIGIT_GROUP)
);
// A leaf index is the two layers' indices, which the guest dispatches on a window at a time.
const _: () = assert!(lean_xmss::LOG_LIFETIME == 32 && lean_xmss::internals::LAYER_HEIGHT.is_multiple_of(LX_WINDOW));
// The guest reads the leanSPHINCS digest as this shape lays it out: the FORS leaves
// fill the first call's first 30 bytes, each byte in at most two of them, the tree
// index's three bytes follow, the last in the second call, then the bottom leaf.
// It reads the layers' leaves off those bytes, and places a FORS tree index in two
// bytes and a codeword's digits a whole number to a byte.
const _: () = assert!(lean_sphincs::internals::LAYER_HEIGHTS[0] == 8 && lean_sphincs::internals::LAYER_HEIGHTS[1] == 8);
const _: () = assert!(lean_sphincs::internals::LAYER_HEIGHTS[2] == 10 && lean_sphincs::internals::LAYERS == 3);
const _: () = assert!(
    lean_sphincs::internals::MD_BYTES == 30
        && lean_sphincs::internals::FORS_TREES * lean_sphincs::internals::FORS_HEIGHT == 240
);
const _: () = assert!(
    lean_sphincs::internals::FORS_HEIGHT == 10
        && lean_sphincs::internals::FORS_TREES << lean_sphincs::internals::FORS_HEIGHT <= 1 << 16
);
const _: () = assert!(lean_sphincs::internals::TREE_INDEX_BYTES == 3 && lean_sphincs::internals::LEAF_INDEX_BYTES == 1);
const _: () = assert!(lean_sphincs::internals::DIGEST_CALLS == 2 && 8 % lean_sphincs::internals::W == 0);

/// The end of `H_msg`'s second call's low lane: its bytes past the digest are the
/// guest's `SP_UNUSED_BYTES`, `8 - (DIGEST_BYTES - 32)`.
const SP_LANE_END: usize = 32 + 8;
const _: () =
    assert!(lean_sphincs::internals::DIGEST_BYTES > 32 && lean_sphincs::internals::DIGEST_BYTES <= SP_LANE_END);

/// Named hint entries for a single sub-proof, ordered within each stream.
pub(super) type SubHints = Vec<(&'static str, Vec<F128>)>;

/// An edit to a node's hints: how a test hands the guest a witness the honest host
/// would not.
#[cfg(test)]
pub(super) type Forgery = Box<dyn FnOnce(&mut Hints)>;

#[cfg(test)]
thread_local! {
    /// The forgery the next node this thread aggregates gets.
    pub(super) static FORGE: std::cell::RefCell<Option<Forgery>> = const { std::cell::RefCell::new(None) };
}

/// The `hint_witness` streams of a run: each a name and its entries, in the order the guest pops them.
#[derive(Default)]
pub(super) struct Hints(pub(super) Vec<(String, Vec<Vec<F128>>)>);

impl Hints {
    pub(super) fn push(&mut self, name: &str, entry: Vec<F128>) {
        match self.0.iter_mut().find(|(n, _)| n == name) {
            Some((_, entries)) => entries.push(entry),
            None => self.0.push((name.to_string(), vec![entry])),
        }
    }

    /// An entry of one count ([`count`]).
    pub(super) fn push_count(&mut self, name: &str, n: usize) {
        self.push(name, vec![count(n)]);
    }

    pub(super) fn extend(&mut self, entries: SubHints) {
        for (name, entry) in entries {
            self.push(name, entry);
        }
    }

    /// Entry `i` of stream `name`, for a test to forge.
    #[cfg(test)]
    pub(super) fn entry_mut(&mut self, name: &str, i: usize) -> &mut Vec<F128> {
        let (_, entries) = self.0.iter_mut().find(|(n, _)| n == name).expect("a hinted stream");
        &mut entries[i]
    }

    /// The streams as [`isa::Prover::prove`] takes them.
    pub(super) fn witness(self) -> Vec<(String, Vec<Vec<verifier::E>>)> {
        let scalars = |entry: Vec<F128>| entry.iter().map(to_scalar).collect();
        let streams = self.0.into_iter();
        streams
            .map(|(name, entries)| (name, entries.into_iter().map(scalars).collect()))
            .collect()
    }
}

/// A one-cell entry of stream `name`: a 16-byte native value ([`pack_16_bytes`]).
fn packed(name: &'static str, bytes: &[u8]) -> (&'static str, Vec<F128>) {
    (name, vec![pack_16_bytes(bytes)])
}

/// The digits of a WOTS+C codeword as the guest dispatches on them: `group` at a
/// time, then the rest, each group's index little endian in base `CHAIN_LEN`, in the
/// exponent.
fn digit_hints(codeword: &[u8], size: usize) -> Vec<F128> {
    let mut out = Vec::new();
    for group in codeword.chunks(size) {
        let mut index = 0;
        for &digit in group.iter().rev() {
            index = index * lean_xmss::internals::CHAIN_LEN + digit as usize;
        }
        out.push(count(index));
    }
    out
}

/// One leanXMSS signature's witness: its leaf index shifted by each multiple of
/// `LX_WINDOW` and those windows in the exponent, then per layer, bottom first, the
/// sibling of every node on the path, the randomizer, the codeword's digits and the
/// chain values they start from.
pub(super) fn lean_xmss_hints(
    pk: &LeanXmssPublicKey,
    sig: &LeanXmssSignature,
    message: &lean_xmss::Message,
) -> Result<SubHints, AggregateError> {
    use lean_xmss::internals::{codeword, layer_index, layer_root, message_digest, sig_bottom, sig_top};
    let pp = lean_xmss::internals::pk_public_param(pk);
    let index = u64::from(sig.leaf_index());
    let (mut shifted, mut windows) = (Vec::new(), Vec::new());
    for shift in (0..lean_xmss::LOG_LIFETIME).step_by(LX_WINDOW) {
        shifted.push(F128::new(index >> shift, 0));
        windows.push(count(((index >> shift) % (1 << LX_WINDOW)) as usize));
    }
    let mut hints: SubHints = vec![("lx_index", shifted), ("lx_windows", windows)];
    let (bottom, top) = (sig_bottom(sig), sig_top(sig));
    let e = |layer| layer_index(sig.leaf_index(), layer);
    let (bottom_codeword, root) =
        layer_root(pp, 0, e(0), message, bottom, |_| {}).ok_or(AggregateError::InvalidSignature)?;
    // The top layer's root is the key's, which the guest checks against the claim: only its codeword is needed.
    let top_codeword =
        codeword(&message_digest(pp, 1, e(1), top.randomizer(), &root)).ok_or(AggregateError::InvalidSignature)?;
    for (layer_sig, codeword) in [(bottom, bottom_codeword), (top, top_codeword)] {
        for sibling in layer_sig.path() {
            hints.push(packed("lx_path", sibling));
        }
        hints.push(packed("randomizer", layer_sig.randomizer()));
        hints.push(("lx_digits", digit_hints(&codeword, LX_DIGIT_GROUP)));
        for value in layer_sig.chain_values() {
            hints.push(packed("chain_starts", value));
        }
    }
    Ok(hints)
}

/// One leanSPHINCS signature's witness: the randomizer, the bytes of `H_msg`'s
/// second call's low lane past the digest, each FORS tree's secret
/// and the ordered children of every node on its climb, then per layer, bottom
/// first, the encoding counter's bytes, the codeword digits (three at a time, in the
/// exponent), the chain values they start from, and the ordered children of every
/// node on the key's path.
///
/// The guest derives the index and every FORS leaf from the digest itself, so
/// nothing here carries them. The signer's message is not hinted either: it rides
/// its slot in the coverage table.
pub(super) fn lean_sphincs_hints(
    pk: &LeanSphincsPublicKey,
    sig: &LeanSphincsSignature,
    message: &lean_sphincs::Message,
) -> Result<SubHints, AggregateError> {
    let pk_seed = lean_sphincs::internals::pk_seed(pk);
    let mut hints: SubHints = vec![packed("sp_rand", lean_sphincs::internals::sig_randomizer(sig))];
    let digest = lean_sphincs::internals::h_msg(
        lean_sphincs::internals::sig_randomizer(sig),
        pk_seed,
        lean_sphincs::internals::pk_root(pk),
        message,
    );
    let (idx, leaves) = lean_sphincs::internals::digest_fields(&digest);
    hints.push((
        "sp_unused",
        exponent_bytes(&digest[lean_sphincs::internals::DIGEST_BYTES..SP_LANE_END]),
    ));
    for tree in lean_sphincs::internals::sig_fors(sig) {
        hints.push(packed("sp_fors_secrets", tree.secret()));
    }
    // On every path the guest does not order a node and its sibling: it is handed the
    // two children in order and checks that the node it holds is the one its bit names.
    let ordered = |pair: &[lean_sphincs::internals::Digest; 2]| vec![pack_16_bytes(&pair[0]), pack_16_bytes(&pair[1])];
    let mut signed =
        lean_sphincs::internals::fors_recover(pk_seed, idx, &leaves, lean_sphincs::internals::sig_fors(sig), |pair| {
            hints.push(("sp_fors_nodes", ordered(pair)));
        });
    for (layer, layer_sig) in lean_sphincs::internals::sig_layers(sig).iter().enumerate() {
        let key = lean_sphincs::internals::OtsKey::of_index(layer, idx);
        let (codeword, leaf) =
            lean_sphincs::internals::wots_leaf(pk_seed, &key, &signed, layer_sig.counter(), layer_sig.wots())
                .ok_or(AggregateError::InvalidSignature)?;
        hints.push(("sp_counter", exponent_bytes(&layer_sig.counter().to_be_bytes())));
        for digits in digit_hints(&codeword, DIGIT_GROUP) {
            hints.push(("digits", vec![digits]));
        }
        for value in layer_sig.wots() {
            hints.push(packed("chain_starts", value));
        }
        signed = lean_sphincs::internals::tree_fold(
            pk_seed,
            &key,
            leaf,
            lean_sphincs::internals::sig_path(sig, layer),
            |pair| {
                hints.push(("siblings", ordered(pair)));
            },
        );
    }
    Ok(hints)
}
