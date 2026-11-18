use super::cells::{count, exponent_bytes, pack_16_bytes};
use super::deferred::{DeferredBytecodeClaim, bytecode_sums, bytecode_value, bytecode_vars};
use super::error::AggregateError;
use super::guest::{GUEST_SOURCE, compile_guest, unified_guest};
use super::hints::{
    DIGIT_GROUP, FORGE, Forgery, Hints, SP_FORS_LOW, SP_FORS_MID, SP_PATH_WINDOW, digit_hints, lean_sphincs_hints,
};
use super::placeholders::placeholder_map;
use super::proof::{AggregateClaims, AggregateProof, decode, encode};
use super::statement::{CLAIM_GROUP, claim_list_digest, list_split, statement_digest};
use super::*;
use fiat_shamir_prover::merkle::hash_to_scalars;
use isa::Program;
use isa::Prover;
use keccak256::{hash, hash_pair};
use lean_da::{BLOB_SYMBOLS, CELL_SYMBOLS, CELLS_PER_ROW, Codeword, DA_MAX_ROWS, Hash};
use lean_sphincs::LeanSphincsSignature;
use lean_vm_core::StableProver;
use lean_vm_core::cpu::{Fault, execute, from_scalar, to_scalar};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use primitives::field::F128;
use rand::SeedableRng;
use rand::rngs::StdRng;
use zkdsl_compiler::{compile, parse_with_replacements};

use crate::signers_cache::{
    LeanSphincsSigner, LeanXmssSigner, get_lean_sphincs_signers, get_signers, get_signers_for, message, message_for,
};

/// A second cached message, sorting after [`message`]; signer `i` holds the same
/// pubkey under both, at another leaf index.
const MESSAGE_B: u32 = 2;
const SMALL_LEAF_SIZE: usize = 6;

/// An aggregate's claims and proof.
type Node = (AggregateClaims, AggregateProof);

/// [`aggregate`](super::aggregate) on the stable prover at the test rate, without the statistics.
fn aggregate(
    children: &[Node],
    raw_lean_xmss: Vec<LeanXmssSigner>,
    raw_lean_sphincs: Vec<LeanSphincsSigner>,
    blobs: Option<&lean_da::BlobMatrix>,
    output: OutputClaims,
) -> Result<Node, AggregateError> {
    StableProver::init();
    let rate = lean_vm_core::pcs::TEST_LOG_INV_RATE;
    super::aggregate::<StableProver>(children, raw_lean_xmss, raw_lean_sphincs, blobs, output, rate)
        .map(|(claims, proof, _)| (claims, proof))
}

/// A node publishing every claim it covers, which must aggregate and verify.
fn prove(children: &[Node], raw_lean_xmss: &[LeanXmssSigner], raw_lean_sphincs: &[LeanSphincsSigner]) -> Node {
    let node = aggregate(
        children,
        raw_lean_xmss.to_vec(),
        raw_lean_sphincs.to_vec(),
        None,
        OutputClaims::All,
    )
    .expect("aggregates");
    assert!(node.1.verify(&node.0), "verifies");
    node
}

/// The blobs' matrix, `None` for no blobs.
fn matrix(blobs: &[lean_da::Blob]) -> Option<lean_da::BlobMatrix> {
    (!blobs.is_empty()).then(|| lean_da::BlobMatrix::build(blobs).unwrap())
}

fn da_rows(n_rows: usize, seed: u64) -> Vec<lean_da::Blob> {
    let mut rng = StdRng::seed_from_u64(seed);
    let symbols: Vec<u128> = (0..n_rows * BLOB_SYMBOLS)
        .map(|_| rand::Rng::random(&mut rng))
        .collect();
    symbols.as_chunks().0.to_vec()
}

/// Aggregating this fails in the guest's run once `forgery` edits the node's hints.
fn assert_forgery_rejected(
    forgery: Forgery,
    children: &[Node],
    raw: Vec<LeanXmssSigner>,
    sphincs: Vec<LeanSphincsSigner>,
    blobs: &[lean_da::Blob],
) {
    FORGE.with(|forge| *forge.borrow_mut() = Some(forgery));
    let result = aggregate(children, raw, sphincs, matrix(blobs).as_ref(), OutputClaims::All);
    assert!(
        result.err() == Some(AggregateError::ProvingFailed),
        "a forged hint is rejected"
    );
}

/// The guest's helpers under a `main` of their own, compiled at the bytecode size `2^kbc`.
fn guest_snippet(main: &str, kbc: usize) -> Program {
    let (helpers, _) = GUEST_SOURCE.split_once("\ndef main():").unwrap();
    let source = format!("{helpers}\ndef main():\n{main}");
    Program::from(compile(
        &parse_with_replacements(&source, &placeholder_map(kbc)).unwrap(),
    ))
}

#[test]
fn the_wire_layout_is_pinned() {
    let le = u64::to_le_bytes;
    let (point, proof) = (vec![F128::new(1, 2), F128::new(4, 5)], vec![9, 8, 7]);
    let bytes = encode(&point, &proof);
    assert_eq!(bytes, [&le(2)[..], &le(1), &le(2), &le(4), &le(5), &proof].concat());
    assert_eq!(decode(&bytes), Some((point, &proof[..])));
    // A count beyond the input, or beyond any input, fails whatever it claims.
    assert_eq!(decode(&[&le(3)[..], &bytes[8..]].concat()), None);
    assert_eq!(decode(&le(u64::MAX)), None);
}

/// The guest compiles to one program, always.
///
/// `unified_guest` finds a fixed point by compiling repeatedly and comparing
/// the result's log size, so a compiler that read a hash seed would not just
/// produce two incompatible transcripts, it could fail to converge at all.
/// The small programs in `zkdsl_compiler`'s `determinism` suite pin the
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

/// The guest builds a leanXMSS address as its type's cell plus `lo`,
/// `hi · 2^32` and `step · 2^61` in the low lane, and the top layer's flag, which
/// must be the native address's bytes.
#[test]
fn guest_addresses_are_the_native_ones() {
    let cell = |tw| pack_16_bytes(&lean_xmss::internals::address(&tw));
    let top = cell(lean_xmss::internals::tweak(0, lean_xmss::internals::TOP, 0));
    for tag in [
        lean_xmss::internals::TWEAK_CHAIN,
        lean_xmss::internals::TWEAK_LEAF,
        lean_xmss::internals::TWEAK_NODE,
        lean_xmss::internals::TWEAK_MSG,
    ] {
        for layer in 0..2 {
            for (hi, lo, step) in [(0u32, 0u32, 0usize), (5, 0x1234_5678, 2), (16, u32::MAX, 0)] {
                let tw = lean_xmss::internals::tweak(tag, lean_xmss::internals::layer_hi(layer, hi), lo).step(step);
                let fields = F128::new(u64::from(lo) | u64::from(hi) << 32 | (step as u64) << 61, 0);
                let guest =
                    cell(lean_xmss::internals::tweak(tag, 0, 0)) + fields + if layer == 1 { top } else { F128::ZERO };
                assert_eq!(guest, cell(tw));
            }
        }
    }
}

/// A leaf of both schemes, each list in its own region, with no blobs and so no root. One leanSPHINCS pubkey signs
/// two messages, the repeat the statement allows: two claims, ordered by the pair, each needing its own signature.
/// Generated here rather than cached, the cache holding one message per pubkey.
#[test]
fn aggregate_mixed_leaf() {
    let secret_key = [77; lean_sphincs::SECRET_KEY_LEN];
    let public_key = lean_sphincs::key_gen(&secret_key);
    let mut sphincs = get_lean_sphincs_signers::<StableProver>(3);
    for tag in [3u8, 9] {
        let signed: lean_sphincs::Message = std::array::from_fn(|i| tag.wrapping_mul(i as u8 + 1));
        sphincs.push((public_key, signed, lean_sphincs::sign(&secret_key, &signed)));
    }
    let leaf = prove(&[], &get_signers::<StableProver>(3), &sphincs);
    assert_eq!((leaf.0.lean_xmss.len(), leaf.0.lean_sphincs.len()), (3, 5));
    assert_eq!(leaf.0.lean_xmss[0].1, message());
    assert_eq!(leaf.0.da_commitment, None);
    let twice: Vec<_> = leaf.0.lean_sphincs.iter().filter(|(pk, _)| *pk == public_key).collect();
    assert!(
        twice.len() == 2 && twice[0].1 < twice[1].1,
        "the same pubkey twice, ordered by the message"
    );
}

/// A leanSPHINCS signature's digest and openings are bound in-circuit. A node fails the
/// guest's run when its hints put the digest's unused bytes or bits off by one, change
/// a sibling on a FORS climb or on a layer's path (in a top window, and in a middle one,
/// which only the node the window above starts from binds), a FORS secret, a chain's
/// start or a node a window starts from (in a FORS tree or on a path), dispatch a FORS
/// or a path window other than the digest's, name a leaf or a high window other than the
/// path's windows spell (the leaf alone, or with its window moved to agree), or give a
/// layer another counter.
#[test]
fn forged_lean_sphincs_hints_are_rejected() {
    use lean_sphincs::internals::{FORS_HEIGHT, FORS_TREES, H};
    let signers = get_lean_sphincs_signers::<StableProver>(1);
    let flip = |name: &'static str, entry: usize, at: usize| -> Forgery {
        Box::new(move |hints: &mut Hints| hints.entry_mut(name, entry)[at] += F128::ONE)
    };
    let next = |name: &'static str, entry: usize, at: usize| -> Forgery {
        Box::new(move |hints: &mut Hints| hints.entry_mut(name, entry)[at] *= count(1))
    };
    // The FORS trees' siblings come first, a tree's top window then its middle one, then
    // the layers' paths, the top one's two lower windows last.
    let fors_siblings = FORS_TREES * FORS_HEIGHT;
    let forgeries: [Forgery; 21] = [
        next("sp_unused", 0, 0),
        next("sp_pad", 0, 0),
        flip("sp_siblings", 0, 0),
        flip("sp_siblings", FORS_HEIGHT - SP_FORS_LOW - SP_FORS_MID, 0),
        flip("sp_siblings", FORS_HEIGHT - 1, 0),
        flip("sp_siblings", fors_siblings, 0),
        flip("sp_siblings", fors_siblings + H - 2 * SP_PATH_WINDOW, 0),
        flip("sp_siblings", fors_siblings + H - 1, 0),
        flip("sp_fors_secrets", 0, 0),
        flip("chain_starts", 0, 0),
        flip("sp_mids", 1, 0),
        flip("sp_mids", 2 * FORS_TREES, 0),
        next("sp_fors_windows", 0, 1),
        next("sp_fors_windows", 0, 5 * (FORS_TREES / 2) - 1),
        next("sp_path_windows", 1, 0),
        next("sp_path_windows", 2, 2),
        flip("sp_index", 0, 0),
        flip("sp_index", 0, 1),
        flip("sp_index", 0, 6),
        Box::new(|hints: &mut Hints| {
            // The bottom leaf's low bit flipped where it is a value and where it is dispatched on.
            let leaf = &mut hints.entry_mut("sp_index", 0)[0];
            let step = if leaf.c0 & 1 == 0 { count(1) } else { count(1).inv() };
            *leaf += F128::ONE;
            hints.entry_mut("sp_path_windows", 0)[0] *= step;
        }),
        next("sp_counter", 1, 0),
    ];
    for forgery in forgeries {
        assert_forgery_rejected(forgery, &[], vec![], signers.clone(), &[]);
    }
}

/// Writes over the honest hints of FORS tree `tree` those of its leaf `leaf` as the key
/// `secret_key` opens it for instance `idx`: the tree's windows, the leaf's secret, the
/// siblings on its climb and the two nodes its upper windows start from. `leaves` are
/// the digest's.
fn open_fors_leaf(
    hints: &mut Hints,
    secret_key: &lean_sphincs::SecretKey,
    idx: u64,
    leaves: &[usize; lean_sphincs::internals::FORS_TREES],
    tree: usize,
    leaf: usize,
) {
    use lean_sphincs::internals::{FORS_HEIGHT, FORS_PRF, FORS_TREE, OtsKey, pk_seed, prf, th, th_digests};
    let public_key = lean_sphincs::key_gen(secret_key);
    let seed = pk_seed(&public_key);
    let at = |t: u32, z: usize, j: usize| {
        let adrs = OtsKey::of_index(0, idx).adrs(t).with_tree_height(z as u32);
        adrs.with_tree_index(((tree << (FORS_HEIGHT - z)) + j) as u32)
    };
    let secret = |s: usize| prf(seed, secret_key, &at(FORS_PRF, 0, s));
    let mut levels = vec![
        (0..1 << FORS_HEIGHT)
            .map(|s| th(seed, &at(FORS_TREE, 0, s), &secret(s)))
            .collect::<Vec<_>>(),
    ];
    for z in 0..FORS_HEIGHT {
        let pairs = levels[z].as_chunks::<2>().0.iter().enumerate();
        let above = pairs.map(|(j, pair)| th_digests(seed, &at(FORS_TREE, z + 1, j), pair));
        levels.push(above.collect());
    }
    let (pair, odd, below) = (tree / 2, tree % 2, SP_FORS_LOW + SP_FORS_MID);
    let low = |leaf: usize| leaf & ((1 << SP_FORS_LOW) - 1);
    let mut two = [leaves[2 * pair], leaves[2 * pair + 1]];
    two[odd] = leaf;
    let windows = hints.entry_mut("sp_fors_windows", 0);
    windows[5 * pair + 2 * odd] = count(leaf >> below);
    windows[5 * pair + 2 * odd + 1] = count(leaf >> SP_FORS_LOW & ((1 << SP_FORS_MID) - 1));
    windows[5 * pair + 4] = count(low(two[0]) | low(two[1]) << SP_FORS_LOW);
    hints.entry_mut("sp_fors_secrets", tree)[0] = pack_16_bytes(&secret(leaf));
    // A pair's siblings: each tree's top window then its middle one, then each one's low
    // window (`lean_sphincs_hints`).
    let upper = FORS_HEIGHT - SP_FORS_LOW;
    for z in 0..FORS_HEIGHT {
        let entry = if z >= below {
            upper * odd + z - below
        } else if z >= SP_FORS_LOW {
            upper * odd + FORS_HEIGHT - below + z - SP_FORS_LOW
        } else {
            2 * upper + SP_FORS_LOW * odd + z
        };
        hints.entry_mut("sp_siblings", 2 * FORS_HEIGHT * pair + entry)[0] = pack_16_bytes(&levels[z][leaf >> z ^ 1]);
    }
    hints.entry_mut("sp_mids", 2 * tree)[0] = pack_16_bytes(&levels[below][leaf >> below]);
    hints.entry_mut("sp_mids", 2 * tree + 1)[0] = pack_16_bytes(&levels[SP_FORS_LOW][leaf >> SP_FORS_LOW]);
}

/// The FORS leaves and the index a leanSPHINCS signature opens are the digest's. A node
/// fails the guest's run when its hints open another leaf of a FORS tree as the signer
/// would have opened it, every hash on its climb the tree's own, so that the digest
/// alone tells the two apart: in each of a tree's three windows and in either cell of
/// the digest, tree 12 lying across both. The same routine opening the digest's own
/// leaves verifies. So does a node fail whose hints are, whole, those of the same key's
/// signature of another message.
#[test]
fn lean_sphincs_openings_are_the_digests() {
    use lean_sphincs::internals::{FORS_HEIGHT, digest_fields, h_msg, pk_root, pk_seed, sig_randomizer};
    let secret_key = [0x5A; lean_sphincs::SECRET_KEY_LEN];
    let pk = lean_sphincs::key_gen(&secret_key);
    let message = [0xC5; lean_sphincs::MESSAGE_LEN];
    let signer = (pk, message, lean_sphincs::sign(&secret_key, &message));
    let digest = h_msg(sig_randomizer(&signer.2), pk_seed(&pk), pk_root(&pk), &message);
    let (idx, leaves) = digest_fields(&digest);
    let open = |openings: &'static [(usize, usize)]| -> Forgery {
        Box::new(move |hints: &mut Hints| {
            for &(tree, flip) in openings {
                open_fors_leaf(hints, &secret_key, idx, &leaves, tree, leaves[tree] ^ flip);
            }
        })
    };
    FORGE.with(|forge| *forge.borrow_mut() = Some(open(&[(0, 0), (12, 0), (23, 0)])));
    prove(&[], &[], std::slice::from_ref(&signer));

    let other = [0x3C; lean_sphincs::MESSAGE_LEN];
    let transplant = lean_sphincs_hints(&pk, &lean_sphincs::sign(&secret_key, &other), &other).expect("hints");
    let forgeries: [Forgery; 5] = [
        open(&[(0, 1)]),
        open(&[(12, 1 << 1)]),
        open(&[(12, 1 << SP_FORS_LOW)]),
        open(&[(23, 1 << (FORS_HEIGHT - 1))]),
        Box::new(move |hints: &mut Hints| {
            let mut popped = std::collections::HashMap::new();
            for (name, entry) in transplant {
                let at: &mut usize = popped.entry(name).or_default();
                *hints.entry_mut(name, *at) = entry;
                *at += 1;
            }
        }),
    ];
    for forgery in forgeries {
        assert_forgery_rejected(forgery, &[], vec![], vec![signer.clone()], &[]);
    }
}

/// Writes over the honest hints of `signer`, whose key is `secret_key`, those of its
/// bottom one-time key standing at the leaf `flip` away from its own in the bottom tree,
/// the path's siblings kept, and of the middle key's signature of the root that reaches,
/// as `secret_key` signs it: the path's windows, the node its high window starts from,
/// then the counter, the codeword and each chain walked from its secret to its digit.
fn move_bottom_leaf(hints: &mut Hints, secret_key: &lean_sphincs::SecretKey, signer: &LeanSphincsSigner, flip: u32) {
    use lean_sphincs::internals::{
        FORS_TREES, N, OtsKey, V, WOTS_HASH, WOTS_PRF, digest_fields, fors_recover, h_msg, pk_root, pk_seed, prf,
        sig_fors, sig_layers, sig_path, sig_randomizer, th, tree_fold, wots_leaf,
    };
    let (pk, message, sig) = signer;
    let seed = pk_seed(pk);
    let (idx, leaves) = digest_fields(&h_msg(sig_randomizer(sig), seed, pk_root(pk), message));
    let (bottom, middle) = (OtsKey::of_index(0, idx), OtsKey::of_index(1, idx));
    let fors_key = fors_recover(seed, idx, &leaves, sig_fors(sig), |_| ());
    let signed = &sig_layers(sig)[0];
    let (_, one_time) = wots_leaf(seed, &bottom, &fors_key, signed.counter(), signed.wots()).expect("a codeword");
    let moved = OtsKey {
        leaf: bottom.leaf ^ flip,
        ..bottom
    };
    let mut pairs = Vec::new();
    let root = tree_fold(seed, &moved, one_time, sig_path(sig, 0), |pair| pairs.push(*pair));
    let leaf = moved.leaf as usize;
    let low = leaf & ((1 << SP_PATH_WINDOW) - 1);
    *hints.entry_mut("sp_path_windows", 0) = vec![count(low), count(leaf >> SP_PATH_WINDOW)];
    // The paths' nodes follow the FORS trees', two a tree.
    let start = &pairs[SP_PATH_WINDOW][leaf >> SP_PATH_WINDOW & 1];
    hints.entry_mut("sp_mids", 2 * FORS_TREES)[0] = pack_16_bytes(start);
    // The least counter that gives a codeword, as the signer takes it.
    let encode = |counter| Some((counter, wots_leaf(seed, &middle, &root, counter, &[[0; N]; V])?.0));
    let (counter, codeword) = (0..).find_map(encode).expect("a codeword");
    *hints.entry_mut("sp_counter", 1) = exponent_bytes(&counter.to_be_bytes());
    for (group, entry) in digit_hints(&codeword, DIGIT_GROUP).enumerate() {
        *hints.entry_mut("digits", V.div_ceil(DIGIT_GROUP) + group) = entry;
    }
    for (chain, &digit) in codeword.iter().enumerate() {
        let at = |t: u32| middle.adrs(t).with_chain(chain as u32);
        let secret = prf(seed, secret_key, &at(WOTS_PRF));
        let value = (0..digit).fold(secret, |value, from| {
            th(seed, &at(WOTS_HASH).with_hash(from.into()), &value)
        });
        hints.entry_mut("chain_starts", V + chain)[0] = pack_16_bytes(&value);
    }
}

/// The leaf a leanSPHINCS path climbs from is the one its key's addresses take. A node
/// fails the guest's run when its hints climb from another leaf of the bottom tree, in
/// the path's low window or in its high one, the bottom key's one-time leaf standing
/// there and the middle key signing the root that reaches, as the signer would have
/// signed it: every hash is then the witness's own and the digest is the signature's, so
/// that only what a dispatch stores into the hinted leaf tells the two apart. The same
/// routine at the digest's leaf verifies.
#[test]
fn lean_sphincs_paths_climb_from_the_digests_leaf() {
    let secret_key = [0x5A; lean_sphincs::SECRET_KEY_LEN];
    let message = [0xC5; lean_sphincs::MESSAGE_LEN];
    let signature = lean_sphincs::sign(&secret_key, &message);
    let signer = (lean_sphincs::key_gen(&secret_key), message, signature);
    let moved = |flip: u32| -> Forgery {
        let signer = signer.clone();
        Box::new(move |hints: &mut Hints| move_bottom_leaf(hints, &secret_key, &signer, flip))
    };
    FORGE.with(|forge| *forge.borrow_mut() = Some(moved(0)));
    prove(&[], &[], std::slice::from_ref(&signer));
    for flip in [1, 1 << SP_PATH_WINDOW] {
        assert_forgery_rejected(moved(flip), &[], vec![], vec![signer.clone()], &[]);
    }
}

/// A window a leanSPHINCS dispatch reads is range checked before it. The guest's run
/// fails at a range check (a `DEREF` through no small g-power), not at a hash that an
/// arm past the table goes on to, when its hints name the first value past the range
/// for a FORS tree's top or middle window, a pair's low windows, a path's low, high or
/// third window, or the digest's unused bits. So does one whose window is the
/// generator's inverse or lies outside the subfield.
#[test]
fn lean_sphincs_windows_past_their_range_fail_a_range_check() {
    use lean_sphincs::internals::{FORS_HEIGHT, FORS_TREES, LAYER_HEIGHTS};
    // The honest leaf's hints and public input, the guest then run on forged copies.
    let seen = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let copy = seen.clone();
    FORGE.with(|forge| *forge.borrow_mut() = Some(Box::new(move |hints| *copy.borrow_mut() = hints.0.clone())));
    let (claims, proof) = prove(&[], &[], &get_lean_sphincs_signers::<StableProver>(1));
    let defer = DeferredBytecodeClaim::recompute(proof.bytecode_point);
    let public_input = statement_digest(&claims, &defer);

    let top_arms = 1 << (FORS_HEIGHT - SP_FORS_LOW - SP_FORS_MID);
    let pair_arms = 1 << (2 * SP_FORS_LOW);
    let high_arms = 1 << (LAYER_HEIGHTS[2] - 2 * SP_PATH_WINDOW);
    let last = 5 * (FORS_TREES / 2) - 1;
    let forgeries = [
        ("sp_fors_windows", 0, 0, count(top_arms)),
        ("sp_fors_windows", 0, 1, count(1 << SP_FORS_MID)),
        ("sp_fors_windows", 0, 4, count(pair_arms)),
        ("sp_fors_windows", 0, last - 2, count(top_arms)),
        ("sp_fors_windows", 0, last, count(pair_arms)),
        ("sp_path_windows", 0, 0, count(1 << SP_PATH_WINDOW)),
        ("sp_path_windows", 1, 1, count(1 << SP_PATH_WINDOW)),
        ("sp_path_windows", 2, 2, count(high_arms)),
        ("sp_pad", 0, 0, count(256 / high_arms)),
        ("sp_fors_windows", 0, 0, count(1).inv()),
        ("sp_fors_windows", 0, 1, F128::new(0, 1)),
    ];
    for (name, entry, at, value) in forgeries {
        let mut hints = Hints(seen.borrow().clone());
        hints.entry_mut(name, entry)[at] = value;
        let Err(error) = execute(unified_guest(), &hints.0, public_input) else {
            panic!("{name}[{at}] past its range was accepted");
        };
        assert!(
            matches!(error.fault, Fault::WildPointer { .. }),
            "{name}[{at}] past its range fails elsewhere: {error}"
        );
    }
}

/// A leanXMSS signature's leaf index and codeword are bound in-circuit: a node whose
/// hints change the index, dispatch a path window other than the index's, or
/// dispatch a digit group other than the digest's fails the guest's run.
#[test]
fn forged_lean_xmss_hints_are_rejected() {
    let signers = get_signers::<StableProver>(1);
    let forgeries: [Forgery; 3] = [
        Box::new(|hints: &mut Hints| hints.entry_mut("lx_index", 0)[0] += F128::ONE),
        Box::new(|hints: &mut Hints| hints.entry_mut("lx_windows", 0)[0] *= count(1)),
        Box::new(|hints: &mut Hints| hints.entry_mut("lx_digits", 0)[0] *= count(1)),
    ];
    for forgery in forgeries {
        assert_forgery_rejected(forgery, &[], signers.clone(), vec![], &[]);
    }
}

/// The guest reads each child's root off its statement and publishes the one the
/// node picks, which must be its own with blobs: a child's root other than the one
/// its proof carries, a pick past the children, a child's root picked over the
/// node's blobs, or a membership challenge other than the root's fails the guest's run.
#[test]
fn forged_da_hints_are_rejected() {
    let child = aggregate(
        &[],
        get_signers::<StableProver>(SMALL_LEAF_SIZE),
        vec![],
        matrix(&da_rows(1, 7)).as_ref(),
        OutputClaims::All,
    )
    .unwrap();
    let forgeries: [(Forgery, bool); 4] = [
        (
            Box::new(|hints: &mut Hints| hints.entry_mut("child_da", 0)[0] += F128::ONE),
            false,
        ),
        (
            Box::new(|hints: &mut Hints| hints.entry_mut("da_pick", 0)[0] *= count(2)),
            false,
        ),
        (
            Box::new(|hints: &mut Hints| hints.entry_mut("da_pick", 0)[0] = count(0)),
            true,
        ),
        (
            Box::new(|hints: &mut Hints| hints.entry_mut("da_challenge", 0)[0] += F128::ONE),
            true,
        ),
    ];
    for (forgery, with_blobs) in forgeries {
        let blobs = if with_blobs { da_rows(1, 8) } else { vec![] };
        assert_forgery_rejected(forgery, std::slice::from_ref(&child), vec![], vec![], &blobs);
    }
}

/// The child's opening rides in as hints: a forged opened row or cap node fails the guest's Merkle check.
#[test]
fn forged_opening_hints_are_rejected() {
    let child = prove(&[], &get_signers::<StableProver>(SMALL_LEAF_SIZE), &[]);
    let forgeries: [Forgery; 2] = [
        Box::new(|hints: &mut Hints| hints.entry_mut("merkle_leaf_rows", 0)[0] += F128::ONE),
        Box::new(|hints: &mut Hints| hints.entry_mut("merkle_caps", 0)[4] += F128::ONE),
    ];
    for forgery in forgeries {
        assert_forgery_rejected(forgery, std::slice::from_ref(&child), vec![], vec![], &[]);
    }
}

#[test]
fn guest_column_selectors_match_native_eq() {
    let kbc = 18;
    let guest = guest_snippet(
        r#"    # The selector tables read whole nibbles of coordinates, zero past the stack.
    point = HeapBuf(4 * SEL_NIBBLES)
    hint_witness(point[0:MAX_STACK_LOG], "point")
    for k in unroll(MAX_STACK_LOG, 4 * SEL_NIBBLES):
        point[GEN ** k] = 0
    point1 = HeapBuf(4 * SEL_NIBBLES)
    for k in unroll(0, 4 * SEL_NIBBLES):
        point1[GEN ** k] = 1 + point[GEN ** k]
    sel_eq = selector_tables(point, point1)
    g_squares = exponent_tables()
    sel_g = g_squares * GEN ** SIZE_BITS
    offset = hint_witness("offset")
    kappa_g = hint_witness("kappa")
    weight = match(log(kappa_g), range(0, N_COLUMN_LOGS), lambda kappa: column_selector(offset, sel_eq, sel_g, kappa))
    public = GEN ** 0
    assert public[1] == weight
    return
"#,
        kbc,
    );
    let mut rng = StdRng::seed_from_u64(813);
    for mu in verifier::min_execution_stacked_log(kbc)..=verifier::MAX_STACKED_LOG {
        let mut point: Vec<F128> = (0..mu)
            .map(|_| {
                let (c0, c1) = rand::Rng::random(&mut rng);
                F128::new(c0, c1)
            })
            .collect();
        point.resize(verifier::MAX_STACKED_LOG, F128::ZERO);
        for kappa in 0..=mu {
            let mask = ((1usize << mu) - 1) & !((1usize << kappa) - 1);
            for offset in [0, mask, 0x0555_5555 & mask] {
                let selector: Vec<_> = (kappa..mu).map(|k| F128::new(((offset >> k) & 1) as u64, 0)).collect();
                let expected = selector
                    .iter()
                    .zip(&point[kappa..mu])
                    .fold(F128::ONE, |acc, (&s, &r)| acc * (F128::ONE + s + r));
                let mut hints = Hints::default();
                hints.push("point", point.clone());
                hints.push("offset", vec![count(offset)]);
                hints.push("kappa", vec![count(kappa)]);
                let execution = execute(&guest, &hints.0, [expected, F128::ZERO]).unwrap();
                assert!(execution.unconstrained_reads.is_empty());
            }
        }
    }
}

/// The right leaf holds more claims than one loop frame of its list hashes
/// ([`CLAIM_GROUP`]), so both that leaf and the parent rebuilding it run the
/// list's group loop and then a partial last group, while the left leaf's list is
/// a partial group alone. The leaves share three signers, so the parent rebuilds the
/// right list on the walk that allows repeated slots (`child_claim_list_any`).
#[test]
fn aggregate_two_to_one() {
    let big = 2 * CLAIM_GROUP + 3;
    let signers = get_signers::<StableProver>(SMALL_LEAF_SIZE + big);
    let left = prove(&[], &signers[..SMALL_LEAF_SIZE], &[]);
    let right = prove(&[], &signers[SMALL_LEAF_SIZE - 3..], &[]);
    let cover = super::coverage::plan_coverage(&[], &[], &[left.clone(), right.clone()], None).unwrap();
    assert!(
        !cover.lean_xmss.children[1].is_sorted_by(|a, b| a < b),
        "the right list takes the repeated-slot walk"
    );
    // A child whose claims are out of order, or whose proof the replay cannot walk, is refused before proving.
    let node_of = |left: Node| aggregate(&[left, right.clone()], vec![], vec![], None, OutputClaims::All).err();
    let mut unsorted = left.clone();
    unsorted.0.lean_xmss.reverse();
    assert_eq!(node_of(unsorted), Some(AggregateError::InvalidChild));
    let mut cut = left.clone();
    cut.1.proof.stream.truncate(cut.1.proof.stream.len() / 2);
    assert_eq!(node_of(cut), Some(AggregateError::InvalidChild));
    let node = prove(&[left, right], &[], &[]);
    assert_eq!(node.0.lean_xmss.len(), SMALL_LEAF_SIZE + big);
}

/// A LeanDA payload of the most blobs a node takes, proven without signatures and published in the statement. The
/// node has to reach the native committer's root, and the aggregate verifies against the receiver's claims only.
#[test]
fn aggregate_with_a_da_payload() {
    let rows = da_rows(DA_MAX_ROWS, 97);
    let matrix = lean_da::BlobMatrix::build(&rows).unwrap();
    let node = aggregate(&[], vec![], vec![], Some(&matrix), OutputClaims::All).expect("node aggregates");
    let expected = AggregateClaims {
        da_commitment: Some(matrix.commitment()),
        ..AggregateClaims::default()
    };
    assert_eq!(node.0, expected, "the guest committed to something else");
    // The receiver's own claims verify, any others fail.
    let bytes = node.1.to_bytes();
    let received = AggregateProof::from_bytes(&bytes).unwrap();
    assert!(received.verify(&expected));
    let other = AggregateClaims {
        da_commitment: Some([0; 32]),
        ..AggregateClaims::default()
    };
    assert!(!received.verify(&other));
    let claim = (
        LeanXmssPublicKey::from_bytes(&[0; lean_xmss::PUB_KEY_SIZE]),
        [0; lean_xmss::MESSAGE_LEN],
    );
    let unsorted = AggregateClaims {
        lean_xmss: vec![claim, claim],
        ..expected.clone()
    };
    assert!(!received.verify(&unsorted));
    let trailing = AggregateProof::from_bytes(&[&bytes[..], &[0]].concat());
    assert!(trailing.is_none());
}

/// A node publishes a root it holds, and with blobs only their matrix's.
#[test]
fn invalid_da_selections_are_rejected_before_building_the_proof() {
    let select = AggregateClaims {
        da_commitment: Some([0xa5; 32]),
        ..AggregateClaims::default()
    };
    let blobs = matrix(&da_rows(1, 3));
    let with = |blobs: Option<&lean_da::BlobMatrix>, declare: &AggregateClaims| {
        aggregate(&[], vec![], vec![], blobs, OutputClaims::Only(declare)).unwrap_err()
    };
    assert_eq!(
        with(None, &select),
        AggregateError::InvalidInput("the requested DA root is not a child's")
    );
    let blobs_root = AggregateError::InvalidInput("a node with blobs publishes their root");
    assert_eq!(with(blobs.as_ref(), &select), blobs_root);
    assert_eq!(with(blobs.as_ref(), &AggregateClaims::default()), blobs_root);
}

/// A proof carries one blob matrix. A node without blobs passes on one child's
/// root, the first's by default or the one it selects, or none; a node with blobs
/// publishes their matrix's, whatever its children hold.
#[test]
fn a_node_passes_on_one_childs_da_root() {
    let signers = get_signers::<StableProver>(SMALL_LEAF_SIZE);
    let mut children = vec![prove(&[], &signers, &[])];
    for (n_rows, seed) in [(1, 509), (2, 510)] {
        let rows = da_rows(n_rows, seed);
        children.push(aggregate(&[], signers.clone(), vec![], matrix(&rows).as_ref(), OutputClaims::All).unwrap());
    }
    let (first, second) = (
        children[1].0.da_commitment.unwrap(),
        children[2].0.da_commitment.unwrap(),
    );
    assert_ne!(first, second);
    let pass_on = |selected: Option<Option<[u8; 32]>>, blobs: &[lean_da::Blob]| {
        let declare = selected.map(|da_commitment| AggregateClaims {
            lean_xmss: children[0].0.lean_xmss.clone(),
            lean_sphincs: vec![],
            da_commitment,
        });
        let node = aggregate(
            &children,
            vec![],
            vec![],
            matrix(blobs).as_ref(),
            declare.as_ref().map_or(OutputClaims::All, OutputClaims::Only),
        )
        .unwrap();
        assert!(node.1.verify(&node.0));
        node.0.da_commitment
    };
    assert_eq!(pass_on(None, &[]), Some(first));
    assert_eq!(pass_on(Some(Some(second)), &[]), Some(second));
    assert_eq!(pass_on(Some(None), &[]), None);
    let rows = da_rows(1, 511);
    assert_eq!(
        pass_on(None, &rows),
        Some(lean_da::BlobMatrix::build(&rows).unwrap().commitment())
    );

    // Passed on again, one level up.
    let middle = prove(&children[1..], &[], &[]);
    let top = prove(&[children[0].clone(), middle], &[], &[]);
    assert_eq!(top.0.da_commitment, Some(first));
}

/// A list hash's split is advice the guest then dispatches on, so the claim count
/// after the last group has to be bounded before the `match`: a negative
/// exponent that satisfies the product identity must fail the range check in
/// `list_split` itself, not reach the dispatch as a wild jump.
#[test]
fn list_split_rejects_a_negative_rest() {
    let guest = guest_snippet(
        r#"    n_g = hint_witness("n")
    bigs, body, rest = list_split(n_g)
    public = GEN ** 0
    assert public[1] == body
    assert public[GEN] == rest
    return
"#,
        20,
    );
    let split = |body: F128, rest: F128| {
        let mut hints = Hints::default();
        hints.push("n", vec![count(6)]);
        hints.push("signers_split", vec![count(0), body, rest]);
        execute(&guest, &hints.0, [body, rest])
    };
    // Six claims: no whole group, then six.
    assert!(split(count(0), count(6)).is_ok());
    // One group and -11 claims after it: the product identity holds, the range
    // check must not.
    let negative = count(11).inv();
    let Err(err) = split(count(1), negative) else {
        panic!("a negative last-block count was accepted");
    };
    assert!(err.to_string().contains("list_split"), "rejected elsewhere: {err}");
}

/// `grind_check` rebuilds a lane from bit windows: an honest run cannot show a proof of work
/// is checked, so this pins that a set bit below the window fails and one at or above it passes.
#[test]
fn grind_check_reads_the_low_bits() {
    let guest = guest_snippet(
        r#"    word = hint_witness("w")
    grind_check(word, exponent_tables() * GEN ** WIN_TAB_AT, 3)
    return
"#,
        20,
    );
    let check = |lane: u64| {
        let mut hints = Hints::default();
        hints.push("w", vec![F128::new(lane, 0x0123_4567_89AB_CDEF)]);
        execute(&guest, &hints.0, [F128::ZERO, F128::ZERO])
    };
    for lane in [0, 0b1000, 1 << 63, 0xFEDC_BA98_7654_3218] {
        assert!(check(lane).is_ok(), "{lane:#x} has its low 3 bits zero");
    }
    for lane in [1, 0b100, 0xFEDC_BA98_7654_321A] {
        assert!(check(lane).is_err(), "{lane:#x} has a low bit set");
    }
}

/// The guest accepts committed codewords, and rejects a matrix with one symbol of
/// one row flipped, in either limb, though its root and vector are that matrix's: the row is no codeword.
#[test]
fn da_guest_checks_codeword_membership() {
    let guest = guest_snippet(
        r#"    byte_bits = HeapBuf(SP_BYTE_VALUES)
    for v in unroll(0, SP_BYTE_VALUES):
        byte_bits[GEN ** v] = v
    r0, r1, z = da_verify(byte_bits)
    digest = StackBuf(2)
    keccak([r0, r1], [z, 0], digest)
    public = GEN ** 0
    assert public[1] == digest[0]
    assert public[GEN] == digest[1]
    return
"#,
        20,
    );
    let blobs = da_rows(3, 101);
    let witness = lean_da::BlobMatrix::build(&blobs).unwrap();
    let rows: Vec<Codeword> = (0..blobs.len()).map(|i| *witness.row(i).unwrap()).collect();
    assert_eq!(da_root(&rows), witness.commitment());
    let verify = |rows: &[Codeword]| {
        let commitment = da_root(rows);
        let mut hints = Hints::default();
        hints.push(
            "da_challenge",
            vec![from_scalar(verifier::da::membership_challenge(&commitment))],
        );
        hints.push("da_n_blobs", vec![count(rows.len())]);
        for j in 0..CELLS_PER_ROW {
            for row in rows {
                let cell = &row.as_chunks::<CELL_SYMBOLS>().0[j];
                hints.push("da_symbols", cell.iter().map(|&w| F128::from(w)).collect());
            }
        }
        execute(
            &guest,
            &hints.0,
            hash_to_scalars(&verifier::da::digest(Some(commitment))),
        )
    };
    assert!(verify(&rows).unwrap().unconstrained_reads.is_empty());
    for (position, flip) in [(0, 1), (BLOB_SYMBOLS + 5, 1 << 64)] {
        let mut corrupted = rows.clone();
        corrupted[1][position] ^= flip;
        assert!(verify(&corrupted).is_err(), "a flip of {flip:#x} at {position} passed");
    }
}

/// The commitment to rows that need not be codewords, rebuilt as `BlobMatrix::build` does it.
fn da_root(rows: &[Codeword]) -> Hash {
    fn root(mut level: Vec<Hash>) -> Hash {
        while level.len() > 1 {
            level = level.chunks(2).map(|pair| hash_pair(&pair[0], &pair[1])).collect();
        }
        level[0]
    }
    let cell_digest = |cell: &[u128]| hash(&cell.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>());
    let mut blob_roots: Vec<Hash> = rows
        .iter()
        .map(|row| root(row.chunks(CELL_SYMBOLS).map(cell_digest).collect()))
        .collect();
    blob_roots.resize(DA_MAX_ROWS, lean_da::root_of_padding_blob());
    let mut count = [0; 32];
    count[0] = rows.len() as u8;
    hash_pair(&root(blob_roots), &count)
}

/// Claims left undeclared take duplicate slots. The first narrowing drops every
/// claim on one message, the second all but one claim.
#[test]
fn a_node_may_publish_less_than_it_covers() {
    let at_a = get_signers::<StableProver>(3);
    let at_b = get_signers_for::<StableProver>(2, MESSAGE_B);
    let wide = prove(&[], &[at_a.clone(), at_b].concat(), &[]);
    assert_eq!(wide.0.lean_xmss.len(), 5);

    let narrowed = |declare: &AggregateClaims| {
        aggregate(
            std::slice::from_ref(&wide),
            vec![],
            vec![],
            None,
            OutputClaims::Only(declare),
        )
    };
    let only = |lean_xmss: Vec<LeanXmssClaim>| AggregateClaims {
        lean_xmss,
        ..AggregateClaims::default()
    };
    let on_b: Vec<LeanXmssClaim> = wide
        .0
        .lean_xmss
        .iter()
        .filter(|(_, message)| *message == message_for(MESSAGE_B))
        .cloned()
        .collect();
    assert_eq!(on_b.len(), 2);

    let narrow = narrowed(&only(on_b.clone())).expect("narrows to one message");
    assert!(narrow.1.verify(&narrow.0), "the one-message narrowing verifies");
    assert_eq!(narrow.0.lean_xmss, on_b);

    let one = vec![(at_a[0].0, message())];
    let part = narrowed(&only(one.clone())).expect("narrows to one claim");
    assert!(part.1.verify(&part.0), "the one-claim narrowing verifies");
    assert_eq!(part.0.lean_xmss, one);

    assert_eq!(
        narrowed(&AggregateClaims::default()).err(),
        Some(AggregateError::InvalidInput("nothing to publish")),
        "a declaration has to publish something"
    );
    let uncovered = Some(AggregateError::InvalidInput(
        "a requested claim is not covered by the inputs",
    ));
    // A pubkey that signed A only, declared on B: the cache reuses pubkeys.
    assert_eq!(
        narrowed(&only(vec![(at_a[2].0, message_for(MESSAGE_B))])).err(),
        uncovered
    );
    // A covered pubkey, against a message nobody signed.
    assert_eq!(
        narrowed(&only(vec![(at_a[0].0, message_for(MESSAGE_B + 1))])).err(),
        uncovered
    );
}

/// A raw signature whose claim goes undeclared covers a duplicate slot.
#[test]
fn raw_signatures_may_go_undeclared() {
    let b = get_signers_for::<StableProver>(1, MESSAGE_B);
    let claim_b = vec![(b[0].0, message_for(MESSAGE_B))];
    let declare = AggregateClaims {
        lean_xmss: claim_b.clone(),
        ..AggregateClaims::default()
    };
    let raw = [get_signers::<StableProver>(1), b].concat();
    let node = aggregate(&[], raw, vec![], None, OutputClaims::Only(&declare)).expect("the narrowing leaf aggregates");
    assert!(node.1.verify(&node.0), "it verifies");
    assert_eq!(node.0.lean_xmss, claim_b);
}

/// Two messages in one tree. Signer `i` holds the same pubkey under both, at
/// different leaf indices, so its claims on B are distinct from those on A; the
/// left leaf holds one message, the right both, and the node needs a duplicate
/// slot for the claim both leaves cover.
#[test]
fn aggregate_two_messages() {
    let at_a = get_signers::<StableProver>(4);
    let at_b = get_signers_for::<StableProver>(2, MESSAGE_B);
    assert_eq!(at_a[0].0, at_b[0].0, "the cache reuses pubkeys across messages");
    assert_ne!(at_a[0].2.leaf_index(), at_b[0].2.leaf_index());
    let left = prove(&[], &at_a[..3], &[]);
    let right = prove(&[], &[&at_a[2..], &at_b[..]].concat(), &[]);
    // A pubkey of `left` signing a second message is a second claim of that pubkey.
    let crossed = prove(std::slice::from_ref(&left), &at_b[..1], &[]);
    let of_first: Vec<lean_xmss::Message> = crossed
        .0
        .lean_xmss
        .iter()
        .filter(|(pubkey, _)| *pubkey == at_a[0].0)
        .map(|(_, message)| *message)
        .collect();
    assert_eq!(of_first, vec![message(), message_for(MESSAGE_B)]);
    assert_eq!(crossed.0.lean_xmss.len(), 4);
    let node = prove(&[left, right], &[], &[]);
    let mut expected: Vec<LeanXmssClaim> = [at_a, at_b]
        .concat()
        .into_iter()
        .map(|(pubkey, message, _)| (pubkey, message))
        .collect();
    expected.sort();
    assert_eq!(node.0.lean_xmss, expected);
}

/// A child list walked by gaps (`child_claim_list_mono`) moves strictly forward. A
/// child may declare a claim twice, and a gap of `g^-1` would walk the copy back onto
/// the slot it just covered, with the same coverage mark, so write-once memory alone
/// would not see it: only the gap's `assert_gpow` does.
#[test]
fn a_child_walk_cannot_step_back() {
    let guest = guest_snippet(
        r#"    n_c = hint_witness("n")
    table = HeapBuf(GEN ** 8)
    hint_witness(table[0:8], "claims")
    cover = HeapBuf(GEN ** 2)
    d0, d1 = child_claim_list_digest(table, cover, GEN ** 3, GEN ** 2, n_c)
    public = GEN ** 0
    assert public[1] == d0
    assert public[GEN] == d1
    return
"#,
        20,
    );
    let claim = |i: u64| [1, 2, 3, 4].map(|k| F128::new(i * 7919 + k, k));
    let table: Vec<F128> = [claim(0), claim(1)].concat();
    let walk = |child: &[[F128; 4]], gaps: &[F128]| {
        let mut hints = Hints::default();
        hints.push("n", vec![count(child.len())]);
        hints.push("claims", table.clone());
        hints.push("signers_split", list_split(child.len()));
        hints.push("child_mono", vec![count(1)]);
        for &gap in gaps {
            hints.push("child_claim_gap", vec![gap]);
        }
        execute(&guest, &hints.0, claim_list_digest(child.iter().copied()))
    };
    assert!(walk(&[claim(0), claim(1)], &[count(0), count(0)]).is_ok());
    let back = count(1).inv();
    assert!(
        walk(&[claim(0), claim(0)], &[count(0), back]).is_err(),
        "a walk revisited a slot"
    );
}

/// Three levels, both schemes. Each node has a child of one scheme only, so it rebuilds a list empty on one side,
/// which is the only way the guest's claim-absorbing loops run over an empty range and reach their bound `log(x) <
/// log(g^0)` (unsatisfiable, so nothing may be written there). Leaves overlap in claims of each scheme, within a node
/// and across the two nodes, so the left node needs a duplicate slot and the root one in each region, each child's two
/// lists landing in their own; the root adds a raw signature of each scheme, leanXMSS on a second message, alongside its
/// children. The root's proof goes over the wire.
#[test]
fn aggregate_three_levels() {
    let xmss = get_signers::<StableProver>(17);
    let sphincs = get_lean_sphincs_signers::<StableProver>(5);
    let left = prove(
        &[prove(&[], &xmss[..6], &sphincs[..2]), prove(&[], &xmss[5..11], &[])],
        &[],
        &[],
    );
    let right = prove(
        &[prove(&[], &xmss[10..], &sphincs[1..3]), prove(&[], &[], &sphincs[3..4])],
        &[],
        &[],
    );
    let root = prove(
        &[left, right],
        &get_signers_for::<StableProver>(2, MESSAGE_B),
        &sphincs[4..],
    );
    assert_eq!(root.0.lean_xmss.len(), 17 + 2);
    assert_eq!(root.0.lean_sphincs.len(), 5, "the repeats merged");
    let received = AggregateProof::from_bytes(&root.1.to_bytes()).expect("round trip");
    assert_eq!(received.to_bytes(), root.1.to_bytes());
    assert!(received.verify(&root.0), "the receiver's claims verify");
}

/// A claim's value, read off its sums or recomputed, is the bytecode's evaluation, at a random point and at a leaf's,
/// where both take a fast path.
#[test]
fn bytecode_values_are_the_bytecode_evaluation() {
    let mut rng = StdRng::seed_from_u64(11);
    let limbs = (0..bytecode_vars()).map(|_| rand::Rng::random::<(u64, u64)>(&mut rng));
    let points = [
        limbs.map(|(c0, c1)| F128::new(c0, c1)).collect(),
        DeferredBytecodeClaim::leaf().bytecode_point,
    ];
    StableProver::init();
    for (sums, point) in bytecode_sums::<StableProver>(&points).iter().zip(&points) {
        let scalars: Vec<_> = point.iter().map(to_scalar).collect();
        let value = from_scalar(unified_guest().bytecode().evaluate(&scalars).unwrap());
        assert_eq!(bytecode_value(sums, point), value);
        assert_eq!(DeferredBytecodeClaim::recompute(point.clone()).bytecode_value, value);
    }
}

/// A raw signature the hint builder cannot walk is a typed error, not a panic: a leanXMSS randomizer whose digest is
/// not a codeword, and a leanSPHINCS counter that does not encode.
#[test]
fn malformed_raw_signatures_are_errors() {
    let message = message();
    let pk = LeanXmssPublicKey::from_bytes(&[0; lean_xmss::PUB_KEY_SIZE]);
    let randomizer = (0..=u8::MAX)
        .map(|byte| [byte; lean_xmss::internals::RANDOMIZER_LEN])
        .find(|r| {
            let digest =
                lean_xmss::internals::message_digest(lean_xmss::internals::pk_public_param(&pk), 0, 0, r, &message);
            lean_xmss::internals::codeword(&digest).is_none()
        })
        .expect("some randomizer fails the codeword");
    // Leaf index 0, then both layers: the randomizer, zero chain values, a zero path.
    let mut bytes = [0; lean_xmss::SIG_SIZE];
    let layer_size = (lean_xmss::SIG_SIZE - 4) / 2;
    bytes[4..4 + lean_xmss::internals::RANDOMIZER_LEN].copy_from_slice(&randomizer);
    bytes[4 + layer_size..][..lean_xmss::internals::RANDOMIZER_LEN].copy_from_slice(&randomizer);
    let xmss = vec![(pk, message, LeanXmssSignature::from_bytes(&bytes))];

    let (public_key, signed, signature) = get_lean_sphincs_signers::<StableProver>(1).pop().expect("one signer");
    // The bottom layer's counter follows the randomizer and the FORS openings.
    let mut bytes = signature.to_bytes();
    bytes[lean_sphincs::internals::N
        + lean_sphincs::internals::FORS_TREES * lean_sphincs::internals::FORS_OPENING_SIZE] ^= 1;
    let signature = LeanSphincsSignature::from_bytes(&bytes);
    assert!(!lean_sphincs::verify(&public_key, &signed, &signature));
    let sphincs = vec![(public_key, signed, signature)];

    for (xmss, sphincs) in [(xmss, vec![]), (vec![], sphincs)] {
        assert_eq!(
            aggregate(&[], xmss, sphincs, None, OutputClaims::All).err(),
            Some(AggregateError::InvalidSignature)
        );
    }
}
