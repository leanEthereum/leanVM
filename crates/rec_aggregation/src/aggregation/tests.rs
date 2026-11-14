use super::cells::{count, pack_16_bytes};
use super::deferred::{DeferredClaim, bytecode_sums, bytecode_value, bytecode_vars, stacked_bytecode};
use super::error::{AggregateVerifyError, AggregationError};
use super::guest::{compile_guest, unified_guest};
use super::hints::{FORGE, Forgery, Hints, lean_xmss_hints};
use super::node::aggregate;
use super::placeholders::placeholder_map;
use super::proof::{EthereumClaims, EthereumProof, decode, encode};
use super::statement::{CLAIM_GROUP, claim_list_digest, list_split};
use super::*;
use fiat_shamir::merkle::{Hash, hash_pair, hash_to_scalars};
use lean_compiler::{compile, parse_with_replacements};
use lean_da::{BLOB_SYMBOLS, CELL_SYMBOLS, CELLS_PER_ROW, Codeword, DA_MAX_ROWS, LOG_BLOB_SYMBOLS};
use leanvm_core::cpu::{from_scalar, verify};
use primitives::field::{F64, F128, g_pow};
use primitives::hash::hash;
use primitives::multilinear::mle_eval_par;
use rand::SeedableRng;
use rand::rngs::StdRng;
use signatures::lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use signatures::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use signatures::{lean_sphincs, lean_xmss};

use crate::signers_cache::{
    LeanXmssSigner, get_lean_sphincs_signers, get_signers, get_signers_for, message, message_for,
};

/// A second cached message, sorting after [`message`]; signer `i` holds the same
/// pubkey under both, at another leaf index.
const MESSAGE_B: u32 = 2;
const SMALL_LEAF_SIZE: usize = 6;
const LOG_INV_RATE: usize = leanvm_core::pcs::TEST_LOG_INV_RATE;

// The native verifier derives the DA challenge's grind from its own copy of the blob size.
const _: () = assert!(verifier::da::LOG_BLOB_SYMBOLS == LOG_BLOB_SYMBOLS);

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
/// The small programs in `lean_compiler`'s `determinism` suite pin the
/// digests; this pins the one program large enough to hit every path that
/// walks a map. A fixed `kbc` is enough: reproducibility does not depend on
/// the size being the fixed point.
#[test]
fn guest_compiles_reproducibly() {
    let (one, two) = (compile_guest(20), compile_guest(20));
    assert_eq!(
        format!("{:?}", one.prog()),
        format!("{:?}", two.prog()),
        "two compilations of the guest produced different bytecode, \
             so the compiler is reading a hash seed"
    );
}

fn prove_leaf(signers: &[LeanXmssSigner]) -> EthereumProof {
    aggregate(&[], signers.to_vec(), vec![], &[], None, LOG_INV_RATE).expect("leaf aggregates")
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
                let fields = F128::new(u64::from(lo) | u64::from(hi) << 32 | (step as u64) << 61, 0);
                let guest = cell(lean_xmss::tweak(tag, 0, 0)) + fields + if layer == 1 { top } else { F128::ZERO };
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
    parallel::init();
    let aggregate = prove_lean_sphincs_leaf(&get_lean_sphincs_signers(1));
    aggregate.verify().expect("verifies");
    assert!(aggregate.claims.lean_xmss.is_empty());
    assert_eq!(aggregate.claims.lean_sphincs.len(), 1);
}

/// A leanSPHINCS signature's digest and openings are bound in-circuit: a node whose
/// hints put the digest's unused bytes off by one, order a FORS node and its sibling
/// the other way, or give a layer another counter fails the guest's run.
#[test]
fn forged_lean_sphincs_hints_are_rejected() {
    parallel::init();
    let signers = get_lean_sphincs_signers(1);
    let forgeries: [Forgery; 3] = [
        Box::new(|hints: &mut Hints| {
            hints.entry_mut("sp_unused", 0)[0] *= count(1);
        }),
        Box::new(|hints: &mut Hints| hints.entry_mut("sp_fors_nodes", 0).swap(0, 1)),
        Box::new(|hints: &mut Hints| {
            hints.entry_mut("sp_counter", 1)[0] *= count(1);
        }),
    ];
    for forgery in forgeries {
        FORGE.with(|forge| *forge.borrow_mut() = Some(forgery));
        let result = aggregate(&[], vec![], signers.clone(), &[], None, LOG_INV_RATE);
        assert!(
            matches!(result, Err(AggregationError::ProofError(_))),
            "a forged hint is rejected"
        );
    }
}

/// A leanXMSS signature's leaf index and codeword are bound in-circuit: a node whose
/// hints change the index, dispatch a path window other than the index's, or
/// dispatch a digit group other than the digest's fails the guest's run.
#[test]
fn forged_lean_xmss_hints_are_rejected() {
    parallel::init();
    let signers = get_signers(1);
    let forgeries: [Forgery; 3] = [
        Box::new(|hints: &mut Hints| hints.entry_mut("lx_index", 0)[0] += F128::ONE),
        Box::new(|hints: &mut Hints| hints.entry_mut("lx_windows", 0)[0] *= count(1)),
        Box::new(|hints: &mut Hints| {
            hints.entry_mut("lx_digits", 0)[0] *= count(1);
        }),
    ];
    for forgery in forgeries {
        FORGE.with(|forge| *forge.borrow_mut() = Some(forgery));
        let result = aggregate(&[], signers.clone(), vec![], &[], None, LOG_INV_RATE);
        assert!(
            matches!(result, Err(AggregationError::ProofError(_))),
            "a forged hint is rejected"
        );
    }
}

#[test]
fn aggregate_one_signer() {
    parallel::init();
    let aggregate = prove_leaf(&get_signers(1));
    aggregate.verify().expect("verifies");
    assert_eq!(aggregate.claims.lean_xmss[0].1, message());
}

/// A leaf holding claims of both schemes, each list in its own region.
#[test]
fn aggregate_mixed_leaf() {
    parallel::init();
    let aggregate = aggregate(
        &[],
        get_signers(3),
        get_lean_sphincs_signers(3),
        &[],
        None,
        LOG_INV_RATE,
    )
    .expect("leaf aggregates");
    aggregate.verify().expect("verifies");
    assert_eq!(
        (aggregate.claims.lean_xmss.len(), aggregate.claims.lean_sphincs.len()),
        (3, 3)
    );
}

/// A node over children of both schemes, overlapping in one signer of each:
/// the coverage table then needs a duplicate slot in both regions, and each
/// child's two claim lists have to land in their own.
#[test]
fn aggregate_mixed_two_to_one() {
    parallel::init();
    let xmss = get_signers(6);
    let lean_sphincs = get_lean_sphincs_signers(4);
    let leaf = |x: &[LeanXmssSigner], s: &[RawSphincs]| {
        aggregate(&[], x.to_vec(), s.to_vec(), &[], None, LOG_INV_RATE).expect("leaf aggregates")
    };
    let left = leaf(&xmss[..4], &lean_sphincs[..3]);
    let right = leaf(&xmss[3..], &lean_sphincs[2..]);
    let node = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates");
    node.verify().expect("node verifies");
    assert_eq!((node.claims.lean_xmss.len(), node.claims.lean_sphincs.len()), (6, 4));
    assert!(node.claims.lean_xmss.windows(2).all(|w| w[0] < w[1]));
    assert!(node.claims.lean_sphincs.windows(2).all(|w| w[0] < w[1]));
}

/// A node whose children are each of one scheme only: every claim list it
/// rebuilds is empty on one side, which is the only way the guest's
/// claim-absorbing loops run over an empty range and its bound `log(x) <
/// log(g^0)` (unsatisfiable, so nothing may be written there) is reached.
#[test]
fn aggregate_one_scheme_per_child() {
    parallel::init();
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
    assert_eq!((node.claims.lean_xmss.len(), node.claims.lean_sphincs.len()), (3, 2));
}

/// The repeat the statement allows: one pubkey signing two messages is two
/// claims, ordered by the pair, each needing its own signature. Generated
/// here rather than cached, the cache holding one message per pubkey.
#[test]
fn aggregate_one_key_two_messages() {
    parallel::init();
    let (secret_key, public_key) = lean_sphincs::key_gen_from_seed([77; lean_sphincs::SEED_LEN]);
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
    assert_eq!(aggregate.claims.lean_sphincs.len(), 2);
    let (first, second) = (aggregate.claims.lean_sphincs[0], aggregate.claims.lean_sphincs[1]);
    assert_eq!(first.0, second.0, "the same pubkey, twice");
    assert!(first.1 < second.1, "ordered by the message");
}

#[test]
fn guest_column_selectors_match_native_eq() {
    parallel::init();
    let (helpers, _) = include_str!("../../guests/lean_ethereum.py")
        .split_once("\ndef main():")
        .unwrap();
    let source = format!(
        r#"{helpers}
def main():
    # The selector tables read whole nibbles of coordinates, zero past the stack.
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
"#
    );
    let kbc = 18;
    let guest = compile(&parse_with_replacements(&source, &placeholder_map(kbc)).unwrap());
    let run = |point: &[F128], offset: usize, kappa: usize, expected: F128| {
        let mut hints = Hints::default();
        hints.push("point", point.to_vec());
        hints.push("offset", vec![count(offset)]);
        hints.push("kappa", vec![count(kappa)]);
        let mut program = guest.clone();
        hints.install(&mut program);
        program.execute([expected, F128::ZERO])
    };
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
                let selector: Vec<_> = (kappa..mu)
                    .map(|k| F128::from(F64(((offset >> k) & 1) as u64)))
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

/// The right leaf holds more claims than one loop frame of its list hashes
/// ([`CLAIM_GROUP`]), so both that leaf and the parent rebuilding it run the
/// list's group loop and then a partial last group, while the left leaf's list is
/// a partial group alone.
#[test]
fn aggregate_two_to_one() {
    parallel::init();
    let big = 2 * CLAIM_GROUP + 3;
    let signers = get_signers(SMALL_LEAF_SIZE + big);
    let left = prove_leaf(&signers[..SMALL_LEAF_SIZE]);
    let right = prove_leaf(&signers[SMALL_LEAF_SIZE..]);
    let children = [left, right];
    let node = aggregate(&children, vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates");
    node.verify().expect("node verifies");
    // `cpu::verify` accepts the same proof of the same statement.
    verify(unified_guest(), &node.vm_public_input(), &node.proof).expect("node verifies natively");
    assert_eq!(node.claims.lean_xmss.len(), SMALL_LEAF_SIZE + big);
}

fn da_rows(n_rows: usize, seed: u64) -> Vec<lean_da::Blob> {
    let mut rng = <rand::rngs::StdRng as rand::SeedableRng>::seed_from_u64(seed);
    let symbols: Vec<u128> = (0..n_rows * BLOB_SYMBOLS)
        .map(|_| rand::Rng::random(&mut rng))
        .collect();
    symbols.as_chunks().0.to_vec()
}

/// A LeanDA payload, proven without signatures and published in the
/// statement. The node has to reach the native committer's root, and the
/// aggregate has to verify against a statement that carries it.
#[test]
fn aggregate_with_a_da_payload() {
    parallel::init();
    let rows = da_rows(3, 97);

    let node = aggregate(&[], vec![], vec![], &rows, None, LOG_INV_RATE).expect("node aggregates");
    node.verify().expect("node verifies");
    assert_eq!(node.claims.num_signature_claims(), 0);

    let commitment = lean_da::commit(&rows).unwrap().root();
    assert_eq!(
        node.claims.da_commitment,
        Some(commitment),
        "the guest committed to something else"
    );
    // The receiver supplies the claims it expects: those verify, any others fail.
    let bytes = node.proof_bytes();
    let expected = EthereumClaims {
        da_commitment: Some(commitment),
        ..EthereumClaims::default()
    };
    EthereumProof::from_proof_bytes(&bytes, expected.clone())
        .unwrap()
        .verify()
        .unwrap();
    let other = EthereumClaims {
        da_commitment: Some([0; 32]),
        ..EthereumClaims::default()
    };
    let wrong = EthereumProof::from_proof_bytes(&bytes, other).unwrap();
    assert!(matches!(wrong.verify(), Err(AggregateVerifyError::Snark(_))));
    let claim = (
        LeanXmssPublicKey::from_bytes(&[0; lean_xmss::PUB_KEY_SIZE]),
        [0; lean_xmss::MESSAGE_LEN],
    );
    let unsorted = EthereumClaims {
        lean_xmss: vec![claim, claim],
        ..expected.clone()
    };
    let malformed = EthereumProof::from_proof_bytes(&bytes, unsorted);
    assert!(matches!(malformed, Err(AggregateVerifyError::MalformedSignerSet)));
    let trailing = EthereumProof::from_proof_bytes(&[&bytes[..], &[0]].concat(), expected);
    assert!(matches!(trailing, Err(AggregateVerifyError::MalformedEncoding)));
}

/// A node publishes a root it holds, and with blobs only their matrix's.
#[test]
fn invalid_da_selections_are_rejected_before_building_the_proof() {
    let select = EthereumClaims {
        da_commitment: Some([0xa5; 32]),
        ..EthereumClaims::default()
    };
    assert_eq!(
        aggregate(&[], vec![], vec![], &[], Some(&select), LOG_INV_RATE).unwrap_err(),
        AggregationError::BlobNotCovered
    );
    assert_eq!(
        aggregate(&[], vec![], vec![], &da_rows(1, 3), Some(&select), LOG_INV_RATE).unwrap_err(),
        AggregationError::BlobsUnpublished
    );
    let unpublished = EthereumClaims::default();
    assert_eq!(
        aggregate(&[], vec![], vec![], &da_rows(1, 3), Some(&unpublished), LOG_INV_RATE).unwrap_err(),
        AggregationError::BlobsUnpublished
    );
}

/// A proof carries one blob matrix. A node without blobs passes on one child's
/// root, the first's by default or the one it selects, or none; a node with blobs
/// publishes their matrix's, whatever its children hold.
#[test]
fn a_node_passes_on_one_childs_da_root() {
    parallel::init();
    let signers = get_signers(SMALL_LEAF_SIZE);
    let mut children = vec![prove_leaf(&signers)];
    for (n_rows, seed) in [(1, 509), (2, 510)] {
        let rows = da_rows(n_rows, seed);
        children.push(aggregate(&[], signers.clone(), vec![], &rows, None, LOG_INV_RATE).unwrap());
    }
    let (first, second) = (
        children[1].claims.da_commitment.unwrap(),
        children[2].claims.da_commitment.unwrap(),
    );
    assert_ne!(first, second);
    let pass_on = |selected: Option<Option<[u8; 32]>>, blobs: &[lean_da::Blob]| {
        let declare = selected.map(|da_commitment| EthereumClaims {
            lean_xmss: children[0].claims.lean_xmss.clone(),
            lean_sphincs: vec![],
            da_commitment,
        });
        let node = aggregate(&children, vec![], vec![], blobs, declare.as_ref(), LOG_INV_RATE).unwrap();
        node.verify().unwrap();
        node.claims.da_commitment
    };
    assert_eq!(pass_on(None, &[]), Some(first));
    assert_eq!(pass_on(Some(Some(second)), &[]), Some(second));
    assert_eq!(pass_on(Some(None), &[]), None);
    let rows = da_rows(1, 511);
    assert_eq!(pass_on(None, &rows), Some(lean_da::commit(&rows).unwrap().root()));

    // Passed on again, one level up.
    let middle = aggregate(&children[1..], vec![], vec![], &[], None, LOG_INV_RATE).unwrap();
    let top = aggregate(&[children[0].clone(), middle], vec![], vec![], &[], None, LOG_INV_RATE).unwrap();
    top.verify().unwrap();
    assert_eq!(top.claims.da_commitment, Some(first));
}

/// The guest reads each child's root off its statement and publishes the one the
/// node picks, which must be its own with blobs: a child's root other than the one
/// its proof carries, a pick past the children, a child's root picked over the
/// node's blobs, or a membership challenge other than the root's fails the guest's run.
#[test]
fn forged_da_hints_are_rejected() {
    parallel::init();
    let signers = get_signers(SMALL_LEAF_SIZE);
    let child = aggregate(&[], signers.clone(), vec![], &da_rows(1, 7), None, LOG_INV_RATE).unwrap();
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
        FORGE.with(|forge| *forge.borrow_mut() = Some(forgery));
        let blobs = if with_blobs { da_rows(1, 8) } else { vec![] };
        let result = aggregate(std::slice::from_ref(&child), vec![], vec![], &blobs, None, LOG_INV_RATE);
        assert!(
            matches!(result, Err(AggregationError::ProofError(_))),
            "a forged DA hint is rejected"
        );
    }
}

/// The child's opening rides in as hints: a forged opened row or cap node fails the guest's Merkle check.
#[test]
fn forged_opening_hints_are_rejected() {
    parallel::init();
    let signers = get_signers(SMALL_LEAF_SIZE);
    let child = aggregate(&[], signers.clone(), vec![], &[], None, LOG_INV_RATE).unwrap();
    let forgeries: [Forgery; 2] = [
        Box::new(|hints: &mut Hints| hints.entry_mut("merkle_leaf_rows", 0)[0] += F128::ONE),
        Box::new(|hints: &mut Hints| hints.entry_mut("merkle_caps", 0)[4] += F128::ONE),
    ];
    for forgery in forgeries {
        FORGE.with(|forge| *forge.borrow_mut() = Some(forgery));
        let result = aggregate(std::slice::from_ref(&child), vec![], vec![], &[], None, LOG_INV_RATE);
        assert!(
            matches!(result, Err(AggregationError::ProofError(_))),
            "a forged opening hint is rejected"
        );
    }
}

/// A list hash's split is advice the guest then dispatches on, so the claim count
/// after the last group has to be bounded before the `match`: a negative
/// exponent that satisfies the product identity must fail the range check in
/// `list_split` itself, not reach the dispatch as a wild jump.
#[test]
fn list_split_rejects_a_negative_rest() {
    let (helpers, _) = include_str!("../../guests/lean_ethereum.py")
        .split_once("\ndef main():")
        .unwrap();
    let source = format!(
        r#"{helpers}
def main():
    n_g = hint_witness("n")
    bigs, body, rest = list_split(n_g)
    public = GEN ** 0
    assert public[1] == body
    assert public[GEN] == rest
    return
"#
    );
    let guest = compile(&parse_with_replacements(&source, &placeholder_map(20)).unwrap());
    let run = |body: F128, rest: F128| {
        let mut hints = Hints::default();
        hints.push("n", vec![count(6)]);
        hints.push("signers_split", vec![count(0), body, rest]);
        let mut program = guest.clone();
        hints.install(&mut program);
        program.execute([body, rest])
    };
    // Six claims: no whole group, then six.
    assert!(run(count(0), count(6)).is_ok());
    // One group and -11 claims after it: the product identity holds, the range
    // check must not.
    let negative = F128::from(g_pow(11).inv());
    let Err(err) = run(count(1), negative) else {
        panic!("a negative last-block count was accepted");
    };
    assert!(err.to_string().contains("list_split"), "rejected elsewhere: {err}");
}

/// `grind_check` rebuilds a lane from bit windows: an honest run cannot show a proof of work
/// is checked, so this pins that a set bit below the window fails and one at or above it passes.
#[test]
fn grind_check_reads_the_low_bits() {
    let (helpers, _) = include_str!("../../guests/lean_ethereum.py")
        .split_once("\ndef main():")
        .unwrap();
    let source = format!(
        r#"{helpers}
def main():
    word = hint_witness("w")
    grind_check(word, exponent_tables() * GEN ** WIN_TAB_AT, 3)
    return
"#
    );
    let guest = compile(&parse_with_replacements(&source, &placeholder_map(20)).unwrap());
    let run = |lane: u64| {
        let mut hints = Hints::default();
        hints.push("w", vec![F128::new(lane, 0x0123_4567_89AB_CDEF)]);
        let mut program = guest.clone();
        hints.install(&mut program);
        program.execute([F128::ZERO, F128::ZERO])
    };
    for lane in [0, 0b1000, 1 << 63, 0xFEDC_BA98_7654_3218] {
        assert!(run(lane).is_ok(), "{lane:#x} has its low 3 bits zero");
    }
    for lane in [1, 0b100, 0xFEDC_BA98_7654_321A] {
        assert!(run(lane).is_err(), "{lane:#x} has a low bit set");
    }
}

/// The guest accepts committed codewords, and rejects a matrix with one symbol of
/// one row flipped, in either limb, though its root and vector are that matrix's: the row is no codeword.
#[test]
fn da_guest_checks_codeword_membership() {
    parallel::init();
    let (helpers, _) = include_str!("../../guests/lean_ethereum.py")
        .split_once("\ndef main():")
        .unwrap();
    let source = format!(
        r#"{helpers}
def main():
    r0, r1, z = da_verify(exponent_tables())
    digest = StackBuf(2)
    keccak([r0, r1], [z, 0], digest)
    public = GEN ** 0
    assert public[1] == digest[0]
    assert public[GEN] == digest[1]
    return
"#
    );
    let guest = compile(&parse_with_replacements(&source, &placeholder_map(20)).unwrap());
    let blobs = da_rows(3, 101);
    let witness = lean_da::commit(&blobs).unwrap();
    let rows: Vec<Codeword> = (0..blobs.len()).map(|i| *witness.row(i).unwrap()).collect();
    assert_eq!(da_root(&rows), witness.root());
    let run = |rows: &[Codeword]| {
        let commitment = da_root(rows);
        let mut hints = Hints::default();
        hints.push(
            "da_challenge",
            vec![from_scalar(verifier::da::membership_challenge(&commitment))],
        );
        hints.push(
            "da_shape",
            vec![
                count(rows.len()),
                count(rows.len().next_power_of_two().ilog2() as usize),
            ],
        );
        for j in 0..CELLS_PER_ROW {
            for row in rows {
                let cell = &row.as_chunks::<CELL_SYMBOLS>().0[j];
                hints.push(
                    "da_symbols",
                    cell.iter().map(|&w| F128::new(w as u64, (w >> 64) as u64)).collect(),
                );
            }
        }
        let mut program = guest.clone();
        hints.install(&mut program);
        program.execute(hash_to_scalars(&verifier::da::digest(Some(commitment))))
    };
    assert!(run(&rows).unwrap().unconstrained_reads.is_empty());
    for (position, flip) in [(0, 1), (BLOB_SYMBOLS + 5, 1 << 64)] {
        let mut corrupted = rows.clone();
        corrupted[1][position] ^= flip;
        assert!(run(&corrupted).is_err(), "a flip of {flip:#x} at {position} passed");
    }
}

/// The commitment to rows that need not be codewords, rebuilt pairwise as `lean_da::commit` builds it.
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
    blob_roots.resize(rows.len().next_power_of_two(), lean_da::padding_root());
    root(blob_roots)
}

#[test]
fn too_many_blobs_are_rejected() {
    let rows = da_rows(DA_MAX_ROWS + 1, 0);
    assert!(matches!(
        aggregate(&[], vec![], vec![], &rows, None, LOG_INV_RATE),
        Err(AggregationError::InvalidBlobCount { blobs }) if blobs == DA_MAX_ROWS + 1
    ));
}

/// The row count is a run-time parameter, so payloads of different heights
/// must prove against the *same* bytecode and each reach its own committer's
/// root. Powers of two and the counts between them alike: 3 pads to 4 and 5 to
/// 8, exercising two different arms of the tree dispatch and a non-empty gap.
#[test]
fn da_row_count_is_a_run_time_parameter() {
    parallel::init();
    let signers = get_signers(SMALL_LEAF_SIZE);
    for n_rows in [1usize, 3, 4, 5] {
        let rows = da_rows(n_rows, 200 + n_rows as u64);
        let node = aggregate(&[], signers.clone(), vec![], &rows, None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        let commitment = lean_da::commit(&rows).unwrap().root();
        assert_eq!(node.claims.da_commitment, Some(commitment), "{n_rows} rows");
    }
}

/// A leaf carrying no payload publishes zeros for its root.
#[test]
fn no_payload_publishes_no_root() {
    parallel::init();
    let signers = get_signers(SMALL_LEAF_SIZE);
    let node = prove_leaf(&signers);
    assert_eq!(node.claims.da_commitment, None);
}

/// Claims left undeclared take duplicate slots. The first narrowing drops every
/// claim on one message, the second all but one claim.
#[test]
fn a_node_may_publish_less_than_it_covers() {
    parallel::init();
    let at_a = get_signers(3);
    let at_b = get_signers_for(2, MESSAGE_B);
    let mut raw = at_a.clone();
    raw.extend_from_slice(&at_b);
    let wide = aggregate(&[], raw, vec![], &[], None, LOG_INV_RATE).expect("the wide leaf aggregates");
    wide.verify().expect("the wide leaf verifies");
    assert_eq!(wide.claims.lean_xmss.len(), 5);

    let narrowed = |wide: &EthereumProof, declare: &EthereumClaims| {
        aggregate(
            std::slice::from_ref(wide),
            vec![],
            vec![],
            &[],
            Some(declare),
            LOG_INV_RATE,
        )
    };
    let only = |lean_xmss: Vec<LeanXmssClaim>| EthereumClaims {
        lean_xmss,
        ..EthereumClaims::default()
    };
    let on_b: Vec<LeanXmssClaim> = wide
        .claims
        .lean_xmss
        .iter()
        .filter(|(_, message)| *message == message_for(MESSAGE_B))
        .cloned()
        .collect();
    assert_eq!(on_b.len(), 2);

    let narrow = narrowed(&wide, &only(on_b.clone())).expect("narrows to one message");
    narrow.verify().expect("the one-message narrowing verifies");
    assert_eq!(narrow.claims.lean_xmss, on_b);

    let one = vec![(at_a[0].0, message())];
    let part = narrowed(&wide, &only(one.clone())).expect("narrows to one claim");
    part.verify().expect("the one-claim narrowing verifies");
    assert_eq!(part.claims.lean_xmss, one);

    assert_eq!(
        narrowed(&wide, &EthereumClaims::default()).err(),
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
    parallel::init();
    let a = get_signers(1);
    let b = get_signers_for(1, MESSAGE_B);
    let mut raw = a.clone();
    raw.extend_from_slice(&b);
    let claim_b = vec![(b[0].0, message_for(MESSAGE_B))];
    let sig = aggregate(
        &[],
        raw,
        vec![],
        &[],
        Some(&EthereumClaims {
            lean_xmss: claim_b.clone(),
            ..EthereumClaims::default()
        }),
        LOG_INV_RATE,
    )
    .expect("the narrowing leaf aggregates");
    sig.verify().expect("it verifies");
    assert_eq!(sig.claims.lean_xmss, claim_b);
}

/// Two messages in one tree. Signer `i` holds the same pubkey under both, at
/// different leaf indices, so its claims on B are distinct from those on A; the
/// left leaf holds one message, the right both, and the node needs a duplicate
/// slot for the claim both leaves cover.
#[test]
fn aggregate_two_messages() {
    parallel::init();
    let at_a = get_signers(4);
    let at_b = get_signers_for(2, MESSAGE_B);
    assert_eq!(at_a[0].0, at_b[0].0, "the cache reuses pubkeys across messages");
    assert_ne!(at_a[0].2.leaf_index(), at_b[0].2.leaf_index());
    let left = aggregate(&[], at_a[..3].to_vec(), vec![], &[], None, LOG_INV_RATE).expect("left");
    let mut right_raw = at_a[2..].to_vec();
    right_raw.extend_from_slice(&at_b);
    let right = aggregate(&[], right_raw, vec![], &[], None, LOG_INV_RATE).expect("right");
    right.verify().expect("the two-message leaf verifies");
    // A pubkey of `left` signing a second message is a second claim of that pubkey.
    let crossed = aggregate(
        std::slice::from_ref(&left),
        at_b[..1].to_vec(),
        vec![],
        &[],
        None,
        LOG_INV_RATE,
    )
    .expect("one pubkey under two messages aggregates");
    crossed.verify().expect("the crossed node verifies");
    let of_first: Vec<lean_xmss::Message> = crossed
        .claims
        .lean_xmss
        .iter()
        .filter(|(pubkey, _)| *pubkey == at_a[0].0)
        .map(|(_, message)| *message)
        .collect();
    assert_eq!(of_first, vec![message(), message_for(MESSAGE_B)]);
    assert_eq!(crossed.claims.lean_xmss.len(), 4);
    let node = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).expect("node");
    node.verify().expect("the two-message node verifies");
    let mut expected = at_a.clone();
    expected.extend_from_slice(&at_b);
    let mut expected: Vec<LeanXmssClaim> = expected
        .into_iter()
        .map(|(pubkey, message, _)| (pubkey, message))
        .collect();
    expected.sort();
    assert_eq!(node.claims.lean_xmss, expected);
}

#[test]
fn aggregate_overlapping_signers() {
    parallel::init();
    let signers = get_signers(40);
    let left = prove_leaf(&signers[..25]);
    let right = prove_leaf(&signers[15..]);
    let node = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates");
    node.verify().expect("node verifies");
    assert_eq!(node.claims.lean_xmss.len(), 40);
    assert!(node.claims.lean_xmss.windows(2).all(|w| w[0] < w[1]));
}

/// A child list walked by gaps (`child_claim_list_mono`) moves strictly forward. A
/// child may declare a claim twice, and a gap of `g^-1` would walk the copy back onto
/// the slot it just covered, with the same coverage mark, so write-once memory alone
/// would not see it: only the gap's `assert_gpow` does.
#[test]
fn a_child_walk_cannot_step_back() {
    let (helpers, _) = include_str!("../../guests/lean_ethereum.py")
        .split_once("\ndef main():")
        .unwrap();
    let source = format!(
        r#"{helpers}
def main():
    n_c = hint_witness("n")
    table = HeapBuf(GEN ** 8)
    hint_witness(table[0:8], "claims")
    cover = HeapBuf(GEN ** 2)
    d0, d1 = child_claim_list_digest(table, cover, GEN ** 3, GEN ** 2, n_c)
    public = GEN ** 0
    assert public[1] == d0
    assert public[GEN] == d1
    return
"#
    );
    let guest = compile(&parse_with_replacements(&source, &placeholder_map(20)).unwrap());
    let claim = |i: u64| [1, 2, 3, 4].map(|k| F128::new(i * 7919 + k, k));
    let table: Vec<F128> = [claim(0), claim(1)].concat();
    let run = |child: &[[F128; 4]], gaps: &[F128]| {
        let mut hints = Hints::default();
        hints.push("n", vec![count(child.len())]);
        hints.push("claims", table.clone());
        hints.push("signers_split", list_split(child.len()));
        hints.push("child_mono", vec![count(1)]);
        for &gap in gaps {
            hints.push("child_claim_gap", vec![gap]);
        }
        let mut program = guest.clone();
        hints.install(&mut program);
        program.execute(claim_list_digest(child.iter().copied()))
    };
    assert!(run(&[claim(0), claim(1)], &[count(0), count(0)]).is_ok());
    let back = F128::from(g_pow(1).inv());
    assert!(
        run(&[claim(0), claim(0)], &[count(0), back]).is_err(),
        "a walk revisited a slot"
    );
}

/// Three levels, both schemes. The leanSPHINCS claims are rebuilt twice over, once
/// into each node and again into the root, and the two nodes share one claim,
/// so the root needs a leanSPHINCS duplicate slot for a claim it never saw
/// directly. The root also adds a raw signature of each scheme alongside its
/// children.
#[test]
fn aggregate_three_levels() {
    parallel::init();
    let signers = get_signers(4 * SMALL_LEAF_SIZE);
    let claims = get_lean_sphincs_signers(5);
    let leaf = |index: usize, lean_sphincs: &[RawSphincs]| {
        aggregate(
            &[],
            signers[index * SMALL_LEAF_SIZE..(index + 1) * SMALL_LEAF_SIZE].to_vec(),
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
        get_signers_for(2, MESSAGE_B),
        claims[4..].to_vec(),
        &[],
        None,
        LOG_INV_RATE,
    )
    .expect("root aggregates");
    root.verify().expect("root verifies");
    assert_eq!(root.claims.lean_xmss.len(), 4 * SMALL_LEAF_SIZE + 2);
    assert_eq!(
        root.claims.lean_sphincs.len(),
        4,
        "claims 0, 1, 2 and 4, the repeat merged"
    );
    assert!(root.claims.lean_xmss.windows(2).all(|w| w[0] < w[1]));
    assert!(root.claims.lean_sphincs.windows(2).all(|w| w[0] < w[1]));
}

#[test]
fn aggregate_round_trips_through_the_wire() {
    parallel::init();
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

    let received = EthereumProof::from_proof_bytes(&node.proof_bytes(), node.claims.clone()).expect("round trip");
    assert_eq!(
        received.proof_bytes(),
        node.proof_bytes(),
        "the wire format round-trips, recomputed claim value included"
    );
    received.verify().expect("the receiver's claims verify");
}

/// The all-zeros fast path in `DeferredClaim::recompute` must agree with the
/// full pass it replaces, or every leaf would verify against the wrong
/// statement.
#[test]
fn leaf_claim_matches_the_general_path() {
    let leaf = DeferredClaim::leaf();
    assert_eq!(
        leaf.bytecode_value,
        mle_eval_par(stacked_bytecode(), &leaf.bytecode_point)
    );
}

/// The scalar verifier's deferred values are the prover's, away from the leaf shortcut.
#[test]
fn scalar_deferred_claim_matches_the_prover() {
    let mut rng = StdRng::seed_from_u64(7);
    let mut point = |len: usize| -> Vec<F128> {
        let limbs = (0..len).map(|_| rand::Rng::random::<(u64, u64)>(&mut rng));
        limbs.map(|(c0, c1)| F128::new(c0, c1)).collect()
    };
    let bytecode_point = point(bytecode_vars());
    assert_eq!(
        DeferredClaim::recompute_scalar(bytecode_point.clone()),
        DeferredClaim::recompute(bytecode_point)
    );
}

/// Each claim's value read off its sums is the bytecode's evaluation, at a random point and a leaf's.
#[test]
fn bytecode_sums_give_the_bytecode_value() {
    let mut rng = StdRng::seed_from_u64(11);
    let limbs = (0..bytecode_vars()).map(|_| rand::Rng::random::<(u64, u64)>(&mut rng));
    let points = [
        limbs.map(|(c0, c1)| F128::new(c0, c1)).collect(),
        vec![F128::ZERO; bytecode_vars()],
    ];
    for (sums, point) in bytecode_sums(&points).iter().zip(&points) {
        assert_eq!(bytecode_value(sums, point), mle_eval_par(stacked_bytecode(), point));
    }
}

/// A randomizer whose digest is not a codeword used to panic the hint builder;
/// it is a typed error now, and the abandoned builder leaves nothing behind.
#[test]
fn malformed_raw_signature_is_an_error() {
    let message = message();
    let pk = LeanXmssPublicKey::from_bytes(&[0; lean_xmss::PUB_KEY_SIZE]);
    let randomizer = (0..=u8::MAX)
        .map(|byte| [byte; lean_xmss::RANDOMIZER_LEN])
        .find(|r| {
            let digest = lean_xmss::message_digest(pk.__public_param(), 0, 0, r, &message);
            lean_xmss::codeword(&digest).is_none()
        })
        .expect("some randomizer fails the codeword");
    // Leaf index 0, then both layers: the randomizer, zero chain values, a zero path.
    let mut bytes = [0; lean_xmss::SIG_SIZE];
    let layer_size = (lean_xmss::SIG_SIZE - 4) / 2;
    bytes[4..4 + lean_xmss::RANDOMIZER_LEN].copy_from_slice(&randomizer);
    bytes[4 + layer_size..][..lean_xmss::RANDOMIZER_LEN].copy_from_slice(&randomizer);
    let sig = LeanXmssSignature::from_bytes(&bytes);

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
    let (public_key, signed, signature) = get_lean_sphincs_signers(1).pop().expect("one signer");
    // The bottom layer's counter follows the randomizer and the FORS openings.
    let mut bytes = signature.to_bytes();
    bytes[lean_sphincs::N + lean_sphincs::FORS_TREES * lean_sphincs::FORS_OPENING_SIZE] ^= 1;
    let signature = LeanSphincsSignature::from_bytes(&bytes);
    assert!(lean_sphincs::verify(&public_key, &signed, &signature).is_err());
    let raw = vec![(public_key, signed, signature)];
    assert_eq!(
        aggregate(&[], vec![], raw, &[], None, LOG_INV_RATE).err(),
        Some(AggregationError::MalformedRawSignature)
    );
}
