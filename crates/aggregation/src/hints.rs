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

/// The guest's `SP_FORS_LOW` and `SP_FORS_MID`: the leaf bits a FORS tree's two lower
/// dispatches cover, the top one taking the rest.
pub(super) const SP_FORS_LOW: usize = 2;
pub(super) const SP_FORS_MID: usize = 4;
/// The leaf bit each FORS window starts at, low first, then the height.
const SP_FORS_BOUNDS: [usize; 4] = [
    0,
    SP_FORS_LOW,
    SP_FORS_LOW + SP_FORS_MID,
    lean_sphincs::internals::FORS_HEIGHT,
];
/// The guest's `SP_PATH_WINDOW`: leaf bits a layer's path dispatch covers, a byte in two.
pub(super) const SP_PATH_WINDOW: usize = 4;
const _: () = assert!(2 * SP_PATH_WINDOW == 8);
// Every window climbs a level or more, and the guest reads a window's bits off one cell
// of the digest: no window lies across its two cells. Two trees' low windows go in one
// dispatch, whose bits one cell holds likewise.
const _: () = assert!(SP_FORS_LOW >= 1 && SP_FORS_MID >= 1 && SP_FORS_BOUNDS[2] < SP_FORS_BOUNDS[3]);
const _: () = {
    let height = lean_sphincs::internals::FORS_HEIGHT;
    let mut tree = 0;
    while tree < lean_sphincs::internals::FORS_TREES {
        let end = height * (tree + 1);
        let mut window = 0;
        while window < 3 {
            assert!((end - 1 - SP_FORS_BOUNDS[window]) / 128 == (end - SP_FORS_BOUNDS[window + 1]) / 128);
            window += 1;
        }
        assert!(tree % 2 == 0 || (end - 1) / 128 == (end - height - SP_FORS_LOW) / 128);
        tree += 1;
    }
    assert!(lean_sphincs::internals::FORS_TREES.is_multiple_of(2));
};

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

/// The digits of a WOTS+C codeword as the guest dispatches on them: `group` at a
/// time, then the rest, each group's index little endian in base `CHAIN_LEN`, in the
/// exponent.
fn digit_hints(codeword: &[u8], size: usize) -> impl Iterator<Item = Vec<F128>> + '_ {
    codeword.chunks(size).map(|group| {
        let index = group.iter().rev().fold(0, |index, &digit| {
            index * lean_xmss::internals::CHAIN_LEN + digit as usize
        });
        vec![count(index)]
    })
}

/// One leanXMSS signature's witness: its leaf index shifted by each multiple of
/// `LX_WINDOW` and those windows in the exponent, then per layer, bottom first, the
/// randomizer, the codeword's digits, the chain values they start from, and the
/// sibling of every node on the path.
pub(super) fn lean_xmss_hints(
    pk: &LeanXmssPublicKey,
    sig: &LeanXmssSignature,
    message: &lean_xmss::Message,
) -> Result<SubHints, AggregateError> {
    let pp = lean_xmss::internals::pk_public_param(pk);
    let index = u64::from(sig.leaf_index());
    let windows = (0..lean_xmss::LOG_LIFETIME).step_by(LX_WINDOW).map(|s| index >> s);
    let mut hints: SubHints = vec![
        ("lx_index", windows.clone().map(|x| F128::new(x, 0)).collect()),
        (
            "lx_windows",
            windows.map(|x| count((x % (1 << LX_WINDOW)) as usize)).collect(),
        ),
    ];
    let mut root: Vec<u8> = message.to_vec();
    let mut level = 0;
    for (layer, layer_sig) in [
        lean_xmss::internals::sig_bottom(sig),
        lean_xmss::internals::sig_top(sig),
    ]
    .into_iter()
    .enumerate()
    {
        let e = lean_xmss::internals::layer_index(sig.leaf_index(), layer);
        let (codeword, reached) = lean_xmss::internals::layer_root(pp, layer, e, &root, layer_sig, |pair| {
            hints.push((
                "lx_path",
                vec![pack_16_bytes(&pair[usize::from(index >> level & 1 == 0)])],
            ));
            level += 1;
        })
        .ok_or(AggregateError::InvalidSignature)?;
        hints.push(("randomizer", vec![pack_16_bytes(layer_sig.randomizer())]));
        hints.push(("lx_digits", digit_hints(&codeword, LX_DIGIT_GROUP).flatten().collect()));
        for value in layer_sig.chain_values() {
            hints.push(("chain_starts", vec![pack_16_bytes(value)]));
        }
        root = reached.to_vec();
    }
    Ok(hints)
}

/// The hints of one climb the guest dispatches a window at a time (`sp_climb`), the top
/// window first: the node each window but the lowest starts from, and the sibling of
/// every node on the way up. `pairs` are the ordered children of the path's nodes from
/// the leaf up, `index` the leaf's, and `bounds` the bit each window starts at, low
/// first, then the height.
fn climb_hints(pairs: &[[lean_sphincs::internals::Digest; 2]], index: usize, bounds: &[usize], hints: &mut SubHints) {
    let side = |z: usize| index >> z & 1;
    for window in bounds.windows(2).rev() {
        if window[0] > 0 {
            hints.push(("sp_mids", vec![pack_16_bytes(&pairs[window[0]][side(window[0])])]));
        }
        for z in window[0]..window[1] {
            hints.push(("sp_siblings", vec![pack_16_bytes(&pairs[z][side(z) ^ 1])]));
        }
    }
}

/// The windows of `index` between `bounds`, each in the exponent, low first.
fn window_hints(index: usize, bounds: &[usize]) -> impl Iterator<Item = F128> + '_ {
    bounds
        .windows(2)
        .map(move |window| count(index >> window[0] & ((1 << (window[1] - window[0])) - 1)))
}

/// One leanSPHINCS signature's witness: the randomizer; the digest's fields, which are
/// the three layers' leaves a byte at a time as values, each with its high window, the
/// top leaf's bits past its low byte, the six bits the tree index leaves and the bytes
/// of `H_msg`'s second call's low lane past the digest, both in the exponent; every
/// FORS tree's windows in the exponent, top first, its secret and its climb; then per
/// layer, bottom first, the encoding counter's bytes, the codeword digits (three at a
/// time, in the exponent), the chain values they start from, and the path's windows,
/// low first, and its climb.
///
/// The signer's message is not hinted: it rides its slot in the coverage table.
pub(super) fn lean_sphincs_hints(
    pk: &LeanSphincsPublicKey,
    sig: &LeanSphincsSignature,
    message: &lean_sphincs::Message,
) -> Result<SubHints, AggregateError> {
    let pk_seed = lean_sphincs::internals::pk_seed(pk);
    let mut hints: SubHints = vec![(
        "sp_rand",
        vec![pack_16_bytes(lean_sphincs::internals::sig_randomizer(sig))],
    )];
    let digest = lean_sphincs::internals::h_msg(
        lean_sphincs::internals::sig_randomizer(sig),
        pk_seed,
        lean_sphincs::internals::pk_root(pk),
        message,
    );
    let (idx, leaves) = lean_sphincs::internals::digest_fields(&digest);
    let keys: [_; lean_sphincs::internals::LAYERS] =
        std::array::from_fn(|layer| lean_sphincs::internals::OtsKey::of_index(layer, idx));
    let bytes = [keys[0].leaf, keys[1].leaf, keys[2].leaf & 0xff];
    let mut index: Vec<F128> = bytes
        .iter()
        .flat_map(|&byte| [byte, byte >> SP_PATH_WINDOW])
        .map(|value| F128::new(u64::from(value), 0))
        .collect();
    index.push(F128::new(u64::from(keys[2].leaf >> 8), 0));
    hints.push(("sp_index", index));
    let unused_bits = digest[lean_sphincs::internals::MD_BYTES] >> (lean_sphincs::internals::LAYER_HEIGHTS[2] - 8);
    hints.push(("sp_pad", vec![count(unused_bits.into())]));
    hints.push((
        "sp_unused",
        exponent_bytes(&digest[lean_sphincs::internals::DIGEST_BYTES..SP_LANE_END]),
    ));
    // Two trees at a time, as the guest dispatches them: each one's top window then its
    // middle one, then both low windows as one.
    let upper = |leaf: usize| {
        [
            leaf >> SP_FORS_BOUNDS[2],
            leaf >> SP_FORS_LOW & ((1 << SP_FORS_MID) - 1),
        ]
    };
    let low = |leaf: usize| leaf & ((1 << SP_FORS_LOW) - 1);
    let windows = leaves.chunks(2).flat_map(|two| {
        let lows = low(two[0]) | low(two[1]) << SP_FORS_LOW;
        upper(two[0]).into_iter().chain(upper(two[1])).chain([lows])
    });
    hints.push(("sp_fors_windows", windows.map(count).collect()));
    for tree in lean_sphincs::internals::sig_fors(sig) {
        hints.push(("sp_fors_secrets", vec![pack_16_bytes(tree.secret())]));
    }
    let mut pairs = Vec::new();
    let mut signed =
        lean_sphincs::internals::fors_recover(pk_seed, idx, &leaves, lean_sphincs::internals::sig_fors(sig), |pair| {
            pairs.push(*pair)
        });
    let trees: Vec<_> = pairs
        .chunks(lean_sphincs::internals::FORS_HEIGHT)
        .zip(&leaves)
        .collect();
    for two in trees.chunks(2) {
        for &(tree, &leaf) in two {
            climb_hints(tree, leaf, &SP_FORS_BOUNDS[1..], &mut hints);
        }
        for &(tree, &leaf) in two {
            climb_hints(tree, leaf, &SP_FORS_BOUNDS[..2], &mut hints);
        }
    }
    for (layer, layer_sig) in lean_sphincs::internals::sig_layers(sig).iter().enumerate() {
        let key = &keys[layer];
        let (codeword, leaf) =
            lean_sphincs::internals::wots_leaf(pk_seed, key, &signed, layer_sig.counter(), layer_sig.wots())
                .ok_or(AggregateError::InvalidSignature)?;
        hints.push(("sp_counter", exponent_bytes(&layer_sig.counter().to_be_bytes())));
        hints.extend(digit_hints(&codeword, DIGIT_GROUP).map(|entry| ("digits", entry)));
        for value in layer_sig.wots() {
            hints.push(("chain_starts", vec![pack_16_bytes(value)]));
        }
        let height = lean_sphincs::internals::LAYER_HEIGHTS[layer];
        let bounds = &[0, SP_PATH_WINDOW, 2 * SP_PATH_WINDOW, height][..if height > 8 { 4 } else { 3 }];
        hints.push(("sp_path_windows", window_hints(key.leaf as usize, bounds).collect()));
        let mut pairs = Vec::new();
        signed = lean_sphincs::internals::tree_fold(
            pk_seed,
            key,
            leaf,
            lean_sphincs::internals::sig_path(sig, layer),
            |pair| pairs.push(*pair),
        );
        climb_hints(&pairs, key.leaf as usize, bounds, &mut hints);
    }
    Ok(hints)
}
