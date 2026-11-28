use super::cells::{count, pack_16_bytes};
use super::deferred::{DeferredBytecodeClaim, bytecode_sums, bytecode_vars};
use super::error::AggregateError;
use super::guest::{GUEST_SOURCE, compile_guest};
use super::hints::{FORGE, Forgery, Hints};
use super::placeholders::placeholder_map;
use super::proof::{AggregateProof, decode, encode};
use super::statement::{CLAIM_GROUP, claim_list_digest, list_split};
use super::*;
use fiat_shamir_prover::merkle::hash_to_scalars;
use isa::Program;
use isa::Prover;
use keccak256::{hash, hash_pair};
use lean_da::{BLOB_SYMBOLS, CELL_SYMBOLS, CELLS_PER_ROW, Codeword, DA_MAX_ROWS, Hash};
use lean_sphincs::LeanSphincsSignature;
use lean_vm_core::StableProver;
use lean_vm_core::cpu::{execute, from_scalar, to_scalar};
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

/// Changing the guest must bump [`PROTOCOL_VERSION`].
#[test]
fn protocol_version_pins_the_guest() {
    let iv: String = unified_guest()
        .bytecode()
        .fiat_shamir_iv()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    assert_eq!(
        (PROTOCOL_VERSION, iv.as_str()),
        (2, "f7b7b7f243620589d38261d96465a04168cf5f44ccb05bcca7ee762883e60db9"),
        "the guest changed: bump PROTOCOL_VERSION"
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

/// A leanSPHINCS signature's digest and openings are bound in-circuit: a node whose
/// hints put the digest's unused bytes off by one, order a FORS node and its sibling
/// the other way, or give a layer another counter fails the guest's run.
#[test]
fn forged_lean_sphincs_hints_are_rejected() {
    let signers = get_lean_sphincs_signers::<StableProver>(1);
    let forgeries: [Forgery; 3] = [
        Box::new(|hints: &mut Hints| hints.entry_mut("sp_unused", 0)[0] *= count(1)),
        Box::new(|hints: &mut Hints| hints.entry_mut("sp_fors_nodes", 0).swap(0, 1)),
        Box::new(|hints: &mut Hints| hints.entry_mut("sp_counter", 1)[0] *= count(1)),
    ];
    for forgery in forgeries {
        assert_forgery_rejected(forgery, &[], vec![], signers.clone(), &[]);
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

/// The link's shape and the program's value ride in as hints: a forged table height, tallest height or pointer width
/// fails its certification, and a forged program value the link's terminal check.
#[test]
fn forged_link_hints_are_rejected() {
    let child = prove(&[], &get_signers::<StableProver>(SMALL_LEAF_SIZE), &[]);
    let up = |name: &'static str, at: usize| -> Forgery {
        Box::new(move |hints: &mut Hints| {
            let entry = hints.entry_mut(name, 0);
            entry[at] *= count(1);
        })
    };
    let forgeries: [Forgery; 4] = [
        up("table_logs", 1),
        up("link_shape", 0),
        up("link_shape", 1),
        Box::new(|hints: &mut Hints| hints.entry_mut("split_values", 0)[0] += F128::ONE),
    ];
    for forgery in forgeries {
        assert_forgery_rejected(forgery, std::slice::from_ref(&child), vec![], vec![], &[]);
    }
}

/// The right leaf holds more claims than one loop frame of its list hashes
/// ([`CLAIM_GROUP`]), so both that leaf and the parent rebuilding it run the
/// list's group loop and then a partial last group, while the left leaf's list is
/// a partial group alone. The leaves share three signers, so the parent rebuilds the
/// right list on the walk that allows repeated slots (`child_claim_list_any`). The executor faults on a `KECCAK` block
/// across its window ([`isa::KECCAK_WINDOW`]), so the three runs also check the compiler lays the blocks out in them.
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
        for row in rows {
            for j in 0..CELLS_PER_ROW {
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

/// A claim's value read off its sums, the split table's path, is the one recomputed by `Bytecode::split`, at a random
/// point and at a leaf's, where both take a fast path.
#[test]
fn deferred_values_agree_on_the_table_and_the_split() {
    let mut rng = StdRng::seed_from_u64(11);
    let limbs = (0..bytecode_vars()).map(|_| rand::Rng::random::<(u64, u64)>(&mut rng));
    let points = [
        limbs.map(|(c0, c1)| F128::new(c0, c1)).collect(),
        DeferredBytecodeClaim::leaf().bytecode_point,
    ];
    StableProver::init();
    for (sums, point) in bytecode_sums::<StableProver>(&points).iter().zip(&points) {
        let value = DeferredBytecodeClaim::recompute(point.clone()).bytecode_value;
        assert_eq!(
            DeferredBytecodeClaim::from_sums(point.clone(), sums).bytecode_value,
            value
        );
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

/// A random `E` element.
fn random_e(rng: &mut StdRng) -> F128 {
    let (c0, c1) = rand::Rng::random(rng);
    F128::new(c0, c1)
}

/// The guest's `packed_message` and `squeeze_packed` against the native sponge, at every message length mod 8 and every
/// remainder arm of `squeeze_packed`'s loop of four permutations a frame, then a plain squeeze after both.
#[test]
fn guest_packed_message_and_squeeze_match_the_native_sponge() {
    use fiat_shamir_prover::FiatShamirState;
    let cases = [
        (8usize, 1usize),
        (9, 8),
        (13, 9),
        (15, 17),
        (16, 24),
        (65, 31),
        (71, 33),
        (1, 40),
        (3, 57),
    ];
    let mut main = String::new();
    for (n, count) in cases {
        main += &format!(
            r#"    cap = HeapBuf(5)
    hint_witness(cap[0:5], "cap")
    msg = HeapBuf({n})
    hint_witness(msg[0:{n}], "msg")
    exp = HeapBuf({e})
    hint_witness(exp[0:{e}], "exp")
    rm, f0, f1, f2, f3, f4 = packed_message(cap[GEN ** 0], cap[GEN ** 1], cap[GEN ** 2], cap[GEN ** 3], cap[GEN ** 4], msg, {n})
    assert rm == exp[GEN ** 0]
    out = HeapBuf({o})
    g0, g1, g2, g3, g4 = squeeze_packed(f0, f1, f2, f3, f4, out, GEN ** {p})
    for i in unroll(0, {count}):
        assert out[GEN ** i] == exp[GEN ** (1 + i)]
    sp = fs_cap(g0, g1, g2, g3, g4)
    no_rate = StackBuf(8)
    sp, c = squeeze(sp, no_rate, 0)
    assert c == exp[GEN ** {last}]
"#,
            e = count + 2,
            o = 8 * count.div_ceil(8),
            p = count.div_ceil(8),
            last = count + 1,
        );
    }
    main += "    return\n";
    let guest = guest_snippet(&main, 18);
    let mut fs = FiatShamirState::<F128>::new([9, 8, 7, 6], [5, 4, 3, 2]);
    let mut streams = Vec::new();
    for (case, (n, count)) in cases.into_iter().enumerate() {
        fs.observe(F128::new(77, case as u64));
        let _ = fs.sample();
        let msg: Vec<F128> = (0..n as u64).map(|i| F128::new(i * 0x9E37 + 1, i ^ 0xABCD)).collect();
        let mut native = fs.clone();
        native.observe_packed(&msg);
        let mut expected = vec![native.sample()];
        expected.extend(native.sample_packed(count));
        expected.push(native.sample());
        streams.push((fs.capacity_cells().to_vec(), msg, expected));
    }
    let run = |streams: &[(Vec<F128>, Vec<F128>, Vec<F128>)]| {
        let mut hints = Hints::default();
        for (cap, msg, expected) in streams {
            hints.push("cap", cap.clone());
            hints.push("msg", msg.clone());
            hints.push("exp", expected.clone());
        }
        execute(&guest, &hints.0, [F128::ZERO; 2])
    };
    run(&streams).unwrap();
    // A wrong message challenge, packed challenge or last challenge fails.
    for (case, (_, count)) in cases.into_iter().enumerate() {
        let mut wrong = streams.clone();
        wrong[case].2[[0, count, count + 1][case % 3]] += F128::ONE;
        assert!(run(&wrong).is_err(), "case {case}: a wrong challenge passes");
    }
}

/// `column_selector` at the nibble count `stack_selectors` passes it, the stack's own `ceil(mu / 4)`, against
/// the native eq of the column's offset bits, at every stack size and column size.
#[test]
fn guest_column_selectors_match_native_eq() {
    let kbc = 18;
    let mut rng = StdRng::seed_from_u64(99);
    let lo = verifier::min_execution_stacked_log(kbc);
    for n_nib in lo.div_ceil(4)..=verifier::MAX_STACKED_LOG.div_ceil(4) {
        let guest = guest_snippet(
            &format!(
                r#"    point = HeapBuf(4 * SEL_NIBBLES)
    hint_witness(point[0:MAX_STACK_LOG], "point")
    for k in unroll(MAX_STACK_LOG, 4 * SEL_NIBBLES):
        point[GEN ** k] = 0
    point1 = HeapBuf(4 * SEL_NIBBLES)
    for k in unroll(0, 4 * SEL_NIBBLES):
        point1[GEN ** k] = 1 + point[GEN ** k]
    sel_eq = selector_tables(point, point1, {n_nib})
    g_squares = exponent_tables()
    sel_g = g_squares * GEN ** SIZE_BITS
    offset = hint_witness("offset")
    kappa_g = hint_witness("kappa")
    weight = match(log(kappa_g), range(0, N_COLUMN_LOGS), lambda kappa: column_selector(offset, sel_eq, sel_g, {n_nib}, kappa))
    public = GEN ** 0
    assert public[1] == weight
    return
"#
            ),
            kbc,
        );
        for mu in (lo..=verifier::MAX_STACKED_LOG).filter(|mu| mu.div_ceil(4) == n_nib) {
            let mut point: Vec<F128> = (0..mu).map(|_| random_e(&mut rng)).collect();
            point.resize(verifier::MAX_STACKED_LOG, F128::ZERO);
            for kappa in 0..=mu {
                let mask = ((1usize << mu) - 1) & !((1usize << kappa) - 1);
                for offset in [0, mask, 0x0555_5555 & mask, 0x0aaa_aaaa & mask] {
                    let expected = (kappa..mu)
                        .map(|k| F128::new(((offset >> k) & 1) as u64, 0))
                        .zip(&point[kappa..mu])
                        .fold(F128::ONE, |acc, (s, &r)| acc * (F128::ONE + s + r));
                    let mut hints = Hints::default();
                    hints.push("point", point.clone());
                    hints.push("offset", vec![count(offset)]);
                    hints.push("kappa", vec![count(kappa)]);
                    let execution = execute(&guest, &hints.0, [expected, F128::ZERO])
                        .unwrap_or_else(|e| panic!("mu {mu} kappa {kappa} offset {offset:#x}: {e:?}"));
                    assert!(execution.unconstrained_reads.is_empty());
                    assert!(
                        offset != mask || execute(&guest, &hints.0, [expected + F128::ONE, F128::ZERO]).is_err(),
                        "mu {mu} kappa {kappa} offset {offset:#x}: a wrong weight passes"
                    );
                }
            }
        }
    }
}

/// `certify_stack` and `stack_selectors`, dispatched on the stack's size as the guest does, reproduce the native
/// whole-column layout: on fixed and random stacks, each block's claim at a random row reads the eq of
/// `Placement::stack_point` against a random opening point. A wrong weight fails, and so does a group order that is
/// not the native one.
#[test]
fn guest_stack_weights_match_native_layout() {
    use verifier::layout::{N_TABLES as TABLES, SizeSource, TABLE_LOG_FLOORS as FLOORS, stack_blocks};
    const ROW_CAP: usize = 40;
    const STACKS: usize = 120;
    let guest = guest_snippet(
        &format!(
            r#"    g_squares = exponent_tables()
    kappa_base = HeapBuf(N_TABLES + 2)
    hint_witness(kappa_base[0:N_TABLES + 2], "kappa_base")
    gmv, offs, kaps = certify_stack(kappa_base, g_squares)
    stack_log = hint_witness("stack_log")
    assert gmv == stack_log
    point = HeapBuf(4 * SEL_NIBBLES)
    hint_witness(point[0:4 * SEL_NIBBLES], "point")
    point1 = HeapBuf(4 * SEL_NIBBLES)
    for k in unroll(0, 4 * SEL_NIBBLES):
        point1[GEN ** k] = 1 + point[GEN ** k]
    assert log(gmv * LIG_MIN_SHIFT_INV) < LIG_N_LOG_SIZES
    sel = match(log(gmv * INV_GEN ** LIG_MIN_LOG_SIZE), range(0, LIG_N_LOG_SIZES), lambda s: stack_selectors(offs, kaps, point, point1, g_squares, (LIG_MIN_LOG_SIZE + s + 3) // 4))
    rows = HeapBuf(N_STK_BLOCKS * {ROW_CAP})
    hint_witness(rows[0:N_STK_BLOCKS * {ROW_CAP}], "rows")
    expected = HeapBuf(N_STK_BLOCKS)
    hint_witness(expected[0:N_STK_BLOCKS], "expected")
    for b in unroll(0, N_STK_BLOCKS):
        p = rows * GEN ** ({ROW_CAP} * b)
        kappa_g = kaps[GEN ** b]
        chain = HeapBuf(EQ_CHAIN_ARMS)
        eq_prefix_chain(chain, 1, p, point1, kappa_g)
        assert chain[kappa_g] * sel[GEN ** b] == expected[GEN ** b]
    return
"#
        ),
        18,
    );
    let blocks = stack_blocks();
    let map = placeholder_map(18);
    let lig = |name: &str| map[&format!("{name}_PLACEHOLDER")].parse::<usize>().unwrap();
    let (log_min, log_sizes) = (lig("LIG_MIN_LOG_SIZE"), lig("LIG_N_LOG_SIZES"));
    let sel_bits = 4 * (log_min + log_sizes - 1).div_ceil(4);
    let mut rng = StdRng::seed_from_u64(7);
    // (log memory, table heights): a stack at the PCS floor, then mixes of small and large tables, then random ones.
    let fixed: [(usize, [usize; TABLES]); 5] = [
        (1, [0, 0, 0, 0, 0, 0]),
        (4, [2, 3, 1, 0, 4, 9]),
        (12, [10, 11, 9, 8, 7, 9]),
        (16, [14, 15, 13, 12, 11, 10]),
        (17, [16, 16, 16, 16, 14, 12]),
    ];
    let (mut stacks, mut reordered) = (0, 0);
    while stacks < STACKS {
        let (log_memory, heights): (usize, Vec<usize>) = match fixed.get(stacks) {
            Some((log_memory, heights)) => (*log_memory, heights.to_vec()),
            None => {
                let cap = rand::Rng::random_range(&mut rng, 0..=24);
                let heights = (0..TABLES)
                    .map(|_| rand::Rng::random_range(&mut rng, 0..=cap))
                    .collect();
                (rand::Rng::random_range(&mut rng, 1..=28), heights)
            }
        };
        let heights: Vec<usize> = heights.iter().zip(FLOORS).map(|(&h, floor)| h.max(floor)).collect();
        let kappas: Vec<usize> = blocks
            .iter()
            .map(|block| {
                block.adj
                    + match block.source {
                        SizeSource::Memory => log_memory,
                        SizeSource::Table(t) => heights[t],
                    }
            })
            .collect();
        let (offsets, total_log) = verifier::stack_offsets(&kappas);
        let log = total_log.max(verifier::MIN_STACKED_LOG);
        if !(log_min..log_min + log_sizes).contains(&log) {
            assert!(stacks >= fixed.len(), "a fixed stack in range");
            continue;
        }
        stacks += 1;
        let point: Vec<F128> = (0..sel_bits)
            .map(|k| if k < log { random_e(&mut rng) } else { F128::ZERO })
            .collect();
        let mut rows = vec![F128::ZERO; blocks.len() * ROW_CAP];
        let mut expected = Vec::new();
        for (b, (&kappa, &offset)) in kappas.iter().zip(&offsets).enumerate() {
            let row: Vec<F128> = (0..kappa).map(|_| random_e(&mut rng)).collect();
            rows[b * ROW_CAP..b * ROW_CAP + kappa].copy_from_slice(&row);
            let placement = verifier::Placement {
                variables: kappa,
                index: offset,
            };
            let at = placement.stack_point(&row.iter().map(to_scalar).collect::<Vec<_>>(), log);
            expected.push(
                at.iter()
                    .zip(&point)
                    .fold(F128::ONE, |acc, (&a, &x)| acc * (F128::ONE + from_scalar(a) + x)),
            );
        }
        let order = super::child::stk_group_order(&kappas);
        let run = |order: &[F128], expected: Vec<F128>| {
            let mut hints = Hints::default();
            let base = [0, log_memory].into_iter().chain(heights.iter().copied());
            hints.push("kappa_base", base.map(count).collect());
            hints.push("stk_group_order", order.to_vec());
            hints.push("stack_log", vec![count(log)]);
            hints.push("point", point.clone());
            hints.push("rows", rows.clone());
            hints.push("expected", expected);
            execute(&guest, &hints.0, [F128::ZERO; 2])
        };
        let case = format!("log memory {log_memory}, heights {heights:?}, stack log {log}");
        let execution = run(&order, expected.clone()).unwrap_or_else(|e| panic!("{case}: {e:?}"));
        assert!(execution.unconstrained_reads.is_empty(), "{case}");
        let mut wrong = expected.clone();
        wrong[stacks % blocks.len()] += F128::ONE;
        assert!(run(&order, wrong).is_err(), "{case}: a wrong weight passes");
        // Two adjacent groups swapped: rejected whether or not they share a size.
        let at = stacks % (order.len() - 1);
        let mut swapped = order.clone();
        swapped.swap(at, at + 1);
        assert!(run(&swapped, expected).is_err(), "{case}: a swapped group order passes");
        reordered += 1;
    }
    assert_eq!(reordered, STACKS);
}

/// `link_terminal` at every pointer width the guest dispatches, against the native summand (`link::Functionals`): the
/// chunks' eq values of the 64 bit-slices, chunk 0's shifted reads inside its window, and the mirror certificate.
#[test]
fn guest_link_terminal_matches_native_at_every_pointer_width() {
    let kbc = 16;
    let map = placeholder_map(kbc);
    let constant = |name: &str| map[&format!("{name}_PLACEHOLDER")].parse::<usize>().unwrap();
    let (n_sent, max_shift) = (constant("LINK_N_SENT"), constant("LINK_MAX_SHIFT"));
    let guest = guest_snippet(
        r#"    r = HeapBuf(MAX_PTR_WIDTH)
    hint_witness(r[0:MAX_PTR_WIDTH], "r")
    sent = HeapBuf(LINK_N_SENT + BASE_FIELD_BITS)
    hint_witness(sent[0:LINK_N_SENT + BASE_FIELD_BITS], "sent")
    shifts = HeapBuf(LINK_MAX_SHIFT)
    hint_witness(shifts[0:LINK_MAX_SHIFT], "shifts")
    nu = HeapBuf(CHUNK_CAP)
    hint_witness(nu[0:CHUNK_CAP], "nu")
    sc = HeapBuf(5)
    hint_witness(sc[0:5], "scalars")
    g_w = sc[GEN ** 0]
    assert log(g_w * INV_GEN ** BYTECODE_LOG) < LINK_W_ARMS
    done = match(log(g_w * INV_GEN ** BYTECODE_LOG), range(0, LINK_W_ARMS), lambda k: link_terminal(r, sent, sc[GEN ** 1], shifts, sc[GEN ** 2], nu, sc[GEN ** 3], sc[GEN ** 4], k + BYTECODE_LOG))
    return
"#,
        kbc,
    );
    let mut rng = StdRng::seed_from_u64(5);
    let eq_table = |p: &[F128]| -> Vec<F128> {
        (0..1usize << p.len())
            .map(|v| {
                (0..p.len()).fold(F128::ONE, |a, h| {
                    a * if v >> h & 1 == 1 { p[h] } else { F128::ONE + p[h] }
                })
            })
            .collect()
    };
    for w in kbc..=verifier::MAX_POINTER_WIDTH {
        let chunks = verifier::Chunks::new(w).unwrap();
        let d = chunks.d();
        let r: Vec<F128> = (0..verifier::MAX_POINTER_WIDTH).map(|_| random_e(&mut rng)).collect();
        let slices: Vec<F128> = (0..64).map(|_| random_e(&mut rng)).collect();
        let shifts: Vec<F128> = (0..max_shift).map(|_| random_e(&mut rng)).collect();
        let nu: Vec<F128> = (0..d).map(|_| random_e(&mut rng)).collect();
        let (coef, cert_w, rest) = (random_e(&mut rng), random_e(&mut rng), random_e(&mut rng));
        // Chunk i's first index bit and first word bit.
        let (mut index_at, mut word_at) = (vec![0usize], vec![0usize]);
        for &width in &chunks.widths {
            index_at.push(index_at.last().unwrap() + width);
            word_at.push(word_at.last().unwrap() + (1 << width));
        }
        let eqs: Vec<Vec<F128>> = (0..d).map(|i| eq_table(&r[index_at[i]..index_at[i + 1]])).collect();
        let at = |i: usize, v: usize| slices[word_at[i] + v];
        let value: Vec<F128> = (0..d)
            .map(|i| (0..eqs[i].len()).map(|v| eqs[i][v] * at(i, v)).sum())
            .collect();
        let mirrored: Vec<F128> = (0..d)
            .map(|i| (0..eqs[i].len()).map(|v| eqs[i][eqs[i].len() - 1 - v] * at(i, v)).sum())
            .collect();
        let window = eqs[0].len();
        let mut low = coef * value[0];
        for s in 1..=max_shift {
            let shifted: F128 = (0..window.saturating_sub(s)).map(|v| eqs[0][v + s] * at(0, v)).sum();
            low += shifts[s - 1] * shifted;
        }
        low = value[1..].iter().fold(low, |acc, &v| acc * v);
        let cert: F128 = (0..d)
            .map(|i| {
                let mirror = r[index_at[i]..index_at[i + 1]]
                    .iter()
                    .fold(F128::ONE, |a, &x| a * (x * x + x));
                cert_w * nu[i] * (value[i] * mirrored[i] + mirror)
            })
            .sum();
        let claim = low + cert + rest;
        let mut sent = vec![F128::ZERO; n_sent];
        sent.extend(&slices);
        let mut nu = nu;
        nu.resize(9, F128::ZERO);
        let run = |claim: F128| {
            let mut hints = Hints::default();
            hints.push("r", r.clone());
            hints.push("sent", sent.clone());
            hints.push("shifts", shifts.clone());
            hints.push("nu", nu.clone());
            hints.push("scalars", vec![count(w), coef, cert_w, rest, claim]);
            execute(&guest, &hints.0, [F128::ZERO; 2])
        };
        run(claim).unwrap_or_else(|e| panic!("width {w}: {e:?}"));
        assert!(run(claim + F128::ONE).is_err(), "width {w}: a wrong claim passes");
    }
}

/// The link's suffix products of `1 + x` (`below` at `r`, a table's corner at `chi`), at every pointer width and row
/// count, against the native ones with a challenge equal to one: a quotient of prefix products is `0/0` there.
#[test]
fn guest_suffix_products_match_native_at_a_challenge_of_one() {
    let kbc = 16;
    let width = verifier::MAX_POINTER_WIDTH;
    let guest = guest_snippet(
        r#"    r = HeapBuf(MAX_PTR_WIDTH)
    hint_witness(r[0:MAX_PTR_WIDTH], "r")
    want = HeapBuf(MAX_PTR_WIDTH + 1)
    hint_witness(want[0:MAX_PTR_WIDTH + 1], "want")
    sc = HeapBuf(2)
    hint_witness(sc[0:2], "scalars")
    out = HeapBuf(MAX_PTR_WIDTH + 1)
    g_w = sc[GEN ** 0]
    if sc[GEN ** 1] == 0:
        assert log(g_w * INV_GEN ** BYTECODE_LOG) < LINK_W_ARMS
        idx, eqzr, shz = match(log(g_w * INV_GEN ** BYTECODE_LOG), range(0, LINK_W_ARMS), lambda k: index_side(r, r, out, k + BYTECODE_LOG))
    else:
        assert log(g_w) < EQ_CHAIN_ARMS
        done = match(log(g_w), range(0, EQ_CHAIN_ARMS), lambda n: one_plus_suffixes(out, r, n))
    for k in unroll(0, MAX_PTR_WIDTH + 1):
        assert out[GEN ** k] == want[GEN ** k]
    return
"#,
        kbc,
    );
    let mut rng = StdRng::seed_from_u64(11);
    let r: Vec<F128> = (0..width).map(|_| random_e(&mut rng)).collect();
    let run = |r: &[F128], want: &[F128], n: usize, corners: bool| {
        let mut hints = Hints::default();
        hints.push("r", r.to_vec());
        hints.push("want", want.to_vec());
        hints.push("scalars", vec![count(n), if corners { F128::ONE } else { F128::ZERO }]);
        execute(&guest, &hints.0, [F128::ZERO; 2])
    };
    for (corners, sizes) in [(false, kbc..=width), (true, 1..=width)] {
        for n in sizes {
            for one in [0, n / 2, n - 1] {
                let mut r = r.clone();
                r[one] = F128::ONE;
                // The native verifier's `below(k)` and corner: the product over `r[k..n]`. Past `n` the guest writes
                // nothing, and the assert writes the cell.
                let mut want: Vec<F128> = (0..=n)
                    .map(|k| r[k..n].iter().fold(F128::ONE, |a, &x| a * (F128::ONE + x)))
                    .collect();
                want.resize(width + 1, F128::ZERO);
                run(&r, &want, n, corners).unwrap_or_else(|e| panic!("n {n}, one at {one}: {e:?}"));
                want[one + 1] += F128::ONE;
                assert!(
                    run(&r, &want, n, corners).is_err(),
                    "n {n}, one at {one}: a wrong product passes"
                );
            }
        }
    }
}

/// `link_rounds`, four rounds a loop frame then a `link_rounds_last` arm, against `link_round` run as many times in a
/// row: the same challenges, cursor, claim and sponge, at every remainder and over several frames.
#[test]
fn guest_link_rounds_match_a_plain_loop_of_link_round() {
    let cases: Vec<(usize, usize)> = (0..=13)
        .chain([26])
        .flat_map(|count| [1usize, 3, 7].map(|n_tail| (count, n_tail)))
        .collect();
    let mut main = String::from("    g_squares = exponent_tables()\n    tabs = g_squares * GEN ** WIN_TAB_AT\n");
    for (count, n_tail) in &cases {
        // After no round the sponge is the capacity alone, after one a whole state.
        let cap = if *count == 0 { 0 } else { 8 };
        main += &format!(
            r#"    fs = HeapBuf(6)
    hint_witness(fs[0:6], "fs")
    stream = HeapBuf(400)
    hint_witness(stream[0:400], "stream")
    point = HeapBuf(32)
    a0, a1, a2, a3, a4, cur_a, cl_a = link_rounds(fs[GEN ** 0], fs[GEN ** 1], fs[GEN ** 2], fs[GEN ** 3], fs[GEN ** 4], stream, fs[GEN ** 5], point, GEN ** {count}, tabs, {n_tail}, 0)
    sp = fs_cap(fs[GEN ** 0], fs[GEN ** 1], fs[GEN ** 2], fs[GEN ** 3], fs[GEN ** 4])
    cur = stream
    cl = fs[GEN ** 5]
    for i in unroll(0, {count}):
        o = StackBuf(3)
        sp = link_round(sp, cur, cl, o, tabs, {n_tail}, 0)
        assert o[0] == point[GEN ** i]
        cur = o[1]
        cl = o[2]
    assert cur == cur_a
    assert cl == cl_a
    assert sp[{cap}] == a0
    assert sp[{cap} + 1] == a1
    assert sp[{cap} + 2] == a2
    assert sp[{cap} + 3] == a3
    assert sp[{cap} + 4] == a4
"#
        );
    }
    main += "    return\n";
    let guest = guest_snippet(&main, 18);
    let mut rng = StdRng::seed_from_u64(11);
    let mut hints = Hints::default();
    for _ in &cases {
        hints.push("fs", (0..6).map(|_| random_e(&mut rng)).collect());
        hints.push("stream", (0..400).map(|_| random_e(&mut rng)).collect());
    }
    execute(&guest, &hints.0, [F128::ZERO; 2]).unwrap();
}

/// `ring_rows`, eight coordinates a loop frame then an `rs_eq_rows_all` arm, against `rs_eq_rows` one coordinate at a
/// time, at every remainder and over several frames.
#[test]
fn guest_ring_rows_match_one_coordinate_at_a_time() {
    let counts = 0..=24;
    let mut main = String::new();
    for count in counts.clone() {
        main += &format!(
            r#"    zs = HeapBuf(32)
    hint_witness(zs[0:32], "zs")
    ps = HeapBuf(32)
    hint_witness(ps[0:32], "ps")
    c = HeapBuf(64)
    hint_witness(c[0:64], "c")
    rows = HeapBuf(({count} + 1) * 64)
    ring_rows(rows, zs, ps, c, GEN ** {count})
    ref = HeapBuf(({count} + 1) * 64)
    for k in unroll(0, 64):
        ref[GEN ** k] = c[GEN ** k]
    for m in unroll(0, {count}):
        nxt = rs_eq_rows(ref * GEN ** (64 * m), zs * GEN ** m, ps * GEN ** m, 1)
    for k in unroll(0, ({count} + 1) * 64):
        assert ref[GEN ** k] == rows[GEN ** k]
"#
        );
    }
    main += "    return\n";
    let guest = guest_snippet(&main, 18);
    let mut rng = StdRng::seed_from_u64(12);
    let mut hints = Hints::default();
    for _ in counts {
        hints.push("zs", (0..32).map(|_| random_e(&mut rng)).collect());
        hints.push("ps", (0..32).map(|_| random_e(&mut rng)).collect());
        hints.push("c", (0..64).map(|_| random_e(&mut rng)).collect());
    }
    execute(&guest, &hints.0, [F128::ZERO; 2]).unwrap();
}

/// A non-final WHIR level's glued query batch, `lam^2 sum_q lam^q prod_k (1 + p_k (1 + What_k(x_q)))` (native
/// `induced_weight` under the glue's `lam^2`), as the guest computes it on both its paths: the factored chains of
/// `level_residual` scaled by `lam^(n + 2) prod_k b_k`, and `level_residual_sum`, the one a zero challenge takes. Only
/// a challenge of zero reaches the second in a proof, so nothing else runs it.
#[test]
fn guest_residual_paths_match_native_induced_weight() {
    // Seven message columns, four of them fold challenges, over eleven queries: one batch of eight and three more.
    let (n, prefix, tail) = (11usize, 4usize, 3usize);
    let mu = prefix + tail;
    let vanish = mu * (mu + 1) / 2;
    let header = format!(
        r#"    pos = HeapBuf({n})
    hint_witness(pos[0:{n}], "pos")
    fc = HeapBuf({prefix})
    hint_witness(fc[0:{prefix}], "fold")
    tc = HeapBuf({tail})
    hint_witness(tc[0:{tail}], "tail")
    lam = hint_witness("lam")
    slow = level_residual_sum(pos, fc, tc, lam, {n}, {prefix}, {tail}, {vanish})
    public = GEN ** 0
    assert public[1] == slow
"#
    );
    let slow_only = guest_snippet(&format!("{header}    return\n"), 18);
    // The factored path, its row and scale as `open_stacked` builds them.
    let both = guest_snippet(
        &format!(
            r#"{header}    hs = HeapBuf(4)
    hint_witness(hs[0:4], "hs")
    rowd = HeapBuf({mu})
    scale = lam * lam * lam ** {n}
    for t in unroll(0, {prefix}):
        c = fc[GEN ** t]
        cb = c * VANISH_INVS_BY_COLS[{vanish} + t]
        rowd[GEN ** t] = (1 + c) * (1 / cb)
        scale *= cb
    for j in unroll(0, {tail}):
        c = tc[GEN ** j]
        cb = c * VANISH_INVS_BY_COLS[{vanish} + {prefix} + j]
        rowd[GEN ** ({prefix} + j)] = (1 + c) * (1 / cb)
        scale *= cb
    h, h_high = level_residual(pos, rowd, hs, 1 / lam, GEN ** {b}, GEN ** {r}, {mu}, 4, 2)
    assert scale * h == slow
    return
"#,
            b = n / 8,
            r = n % 8,
        ),
        18,
    );
    let native = |positions: &[u64], point: &[F128], lam: F128| -> F128 {
        let subspace = verifier::Subspace::new(mu);
        let point: Vec<verifier::E> = point.iter().map(to_scalar).collect();
        let lam_e = to_scalar(&lam);
        let mut total = verifier::E::new(0, 0);
        let mut weight = lam_e * lam_e;
        for &x in positions {
            let what = subspace.at(verifier::K(x));
            let mut product = weight;
            for (&p, &value) in point.iter().zip(&what) {
                product *= verifier::E::new(1, 0) + p * (verifier::K(1) + value);
            }
            total += product;
            weight *= lam_e;
        }
        from_scalar(total)
    };
    let mut rng = StdRng::seed_from_u64(23);
    let run = |guest: &Program, positions: &[u64], point: &[F128], lam: F128, expected: F128| {
        let mut hints = Hints::default();
        hints.push("pos", positions.iter().map(|&x| F128::new(x, 0)).collect());
        hints.push("fold", point[..prefix].to_vec());
        hints.push("tail", point[prefix..].to_vec());
        hints.push("lam", vec![lam]);
        hints.push(
            "hs",
            vec![F128::new(3, 1), F128::new(5, 9), F128::new(7, 2), F128::new(11, 4)],
        );
        execute(guest, &hints.0, [expected, F128::ZERO])
    };
    for case in 0..8 {
        let positions: Vec<u64> = (0..n)
            .map(|i| {
                if i == 3 {
                    0
                } else {
                    rand::Rng::random_range(&mut rng, 0..1u64 << 20)
                }
            })
            .collect();
        let mut point: Vec<F128> = (0..mu).map(|_| random_e(&mut rng)).collect();
        let lam = random_e(&mut rng);
        let expected = native(&positions, &point, lam);
        run(&both, &positions, &point, lam, expected).unwrap_or_else(|e| panic!("case {case}: {e:?}"));
        assert!(run(&both, &positions, &point, lam, expected + F128::ONE).is_err());
        // A zero or a one challenge, as a fold or a tail coordinate: the slow path alone, the factored one dividing by it.
        let at = case % mu;
        point[at] = if case < 4 { F128::ZERO } else { F128::ONE };
        let expected = native(&positions, &point, lam);
        run(&slow_only, &positions, &point, lam, expected).unwrap_or_else(|e| panic!("case {case}: {e:?}"));
        assert!(run(&slow_only, &positions, &point, lam, expected + F128::ONE).is_err());
        assert_eq!(native(&positions, &point, F128::ZERO), F128::ZERO);
        run(&slow_only, &positions, &point, F128::ZERO, F128::ZERO).unwrap();
    }
}

/// A node at the test rate aggregates children proven at each of the four rates: the guest's opening checks every rate.
#[test]
fn children_proven_at_every_rate_aggregate() {
    StableProver::init();
    let signers = get_signers::<StableProver>(4);
    let children: Vec<Node> = (verifier::MIN_LOG_INV_RATE..=verifier::MAX_LOG_INV_RATE)
        .zip(&signers)
        .map(|(rate, signer)| {
            let (claims, proof, _) =
                super::aggregate::<StableProver>(&[], vec![signer.clone()], vec![], None, OutputClaims::All, rate)
                    .unwrap();
            assert!(proof.verify(&claims), "the leaf at rate {rate} verifies");
            (claims, proof)
        })
        .collect();
    prove(&children, &[], &[]);
}

/// The guest's `JUMP` identities, its own text from the row side's base terms, at random sent values and challenges
/// against the native ones (`verifier::layout`'s `JUMP` constraints): a guest that dropped or changed one would differ.
#[test]
fn guest_jump_identities_match_native() {
    use verifier::layout::{OP_JUMP, tables};
    let block = |from: &str, to: &str| {
        let start = GUEST_SOURCE.find(from).expect("the block's first line");
        assert_eq!(GUEST_SOURCE.matches(from).count(), 1, "{from}");
        let end = start + GUEST_SOURCE[start..].find(to).expect("the block's last line") + to.len();
        GUEST_SOURCE[start..end].to_string()
    };
    let state = block(
        "        pc_t = sent[GEN ** STATE_PC[t]]\n",
        "nx1 = link_form(sent, STATE_NEXT1[t])\n",
    );
    let jump = block(
        "        if const(t == LINK_JUMP_TABLE):\n",
        "            table_base = table_base + eq_tau * ids\n",
    );
    let main = format!(
        r#"    sent = HeapBuf(LINK_N_SENT)
    hint_witness(sent[0:LINK_N_SENT], "sent")
    sc = HeapBuf(5)
    hint_witness(sc[0:5], "scalars")
    jump_0 = sc[GEN ** 0]
    jump_1 = sc[GEN ** 1]
    jump_2 = sc[GEN ** 2]
    jump_3 = sc[GEN ** 3]
    eq_tau = 1
    for t in unroll(LINK_JUMP_TABLE, LINK_JUMP_TABLE + 1):
{state}        table_base = 0
{jump}        assert table_base == sc[GEN ** 4]
    return
"#
    );
    let kbc = 18;
    let map = placeholder_map(kbc);
    let guest = guest_snippet(&main, kbc);
    // The sent run is each table's non-pointer columns, in table then column order.
    let tables = tables();
    let mut at = 0;
    let mut sent_pos = Vec::new();
    for table in &tables {
        let pointers = table.links.pointers();
        let pos: Vec<Option<usize>> = (0..table.width())
            .map(|c| {
                (!pointers.contains(&c)).then(|| {
                    at += 1;
                    at - 1
                })
            })
            .collect();
        sent_pos.push(pos);
    }
    assert_eq!(at.to_string(), map["LINK_N_SENT_PLACEHOLDER"]);
    let jump = &tables[OP_JUMP];
    let named = |name: &str| jump.columns.iter().position(|c| c == name).unwrap();
    let ids = ["v_cond", "w", "b", "v_pc", "v_fp"].map(|c| sent_pos[OP_JUMP][named(c)].unwrap().to_string());
    assert_eq!(map["JUMP_IDS_PLACEHOLDER"], format!("[{}]", ids.join(", ")));
    let mut rng = StdRng::seed_from_u64(0x7a);
    for _ in 0..20 {
        let sent: Vec<F128> = (0..at).map(|_| random_e(&mut rng)).collect();
        let columns: Vec<verifier::E> = (sent_pos[OP_JUMP].iter())
            .map(|p| to_scalar(&p.map_or_else(|| random_e(&mut rng), |p| sent[p])))
            .collect();
        let alphas: Vec<F128> = (0..4).map(|_| random_e(&mut rng)).collect();
        let want = ((jump.constraints)(&columns).into_iter())
            .zip(&alphas)
            .fold(F128::ZERO, |acc, (id, &a)| acc + a * from_scalar(id));
        let run = |want: F128| {
            let mut hints = Hints::default();
            hints.push("sent", sent.clone());
            hints.push("scalars", [alphas.clone(), vec![want]].concat());
            execute(&guest, &hints.0, [F128::ZERO; 2])
        };
        run(want).unwrap_or_else(|e| panic!("{e:?}"));
        assert!(run(want + F128::ONE).is_err(), "a wrong sum passes");
    }
}

/// The guest's memory budget, `NodeWitness.memoryBudget` in `formal/Statement/LeanVmGuestCompleteness.lean`: the
/// words a node's run may use, by its children, the claims their lists hold, its raw signatures and its blob matrix's
/// rows (`None` without one). A node within `2^24` of it keeps its memory, its cycles and so its pointer width within
/// `MAX_WIDTH`.
fn memory_budget(children: usize, child_claims: usize, xmss: usize, sphincs: usize, blob_rows: Option<usize>) -> usize {
    let blobs = blob_rows.map_or(0, |rows| 131_072 + 122_000 * rows);
    66 * child_claims + 457_265 * children + 1_400 * xmss + 7_500 * sphincs + blobs + 41_297
}

/// The guest's memory against its budget ([`memory_budget`]): each shape's run within it, its cycles below its memory,
/// and each item's increment within its coefficient. Run after a change to the guest's memory per item, with
/// `-- --ignored --nocapture`; the coefficients are the formal statement's, proved there of the compiled guest.
#[test]
#[ignore]
fn guest_memory_within_its_budget() {
    StableProver::init();
    let rate = lean_vm_core::pcs::TEST_LOG_INV_RATE;
    let run = |children: &[Node], xmss: &[LeanXmssSigner], sphincs: &[LeanSphincsSigner], blobs: usize| {
        let matrix = matrix(&da_rows(blobs, 5));
        let (claims, proof, stats) = super::aggregate::<StableProver>(
            children,
            xmss.to_vec(),
            sphincs.to_vec(),
            matrix.as_ref(),
            OutputClaims::All,
            rate,
        )
        .expect("aggregates");
        let child_claims: usize = children
            .iter()
            .map(|(c, _)| c.lean_xmss.len() + c.lean_sphincs.len())
            .sum();
        let rows = (blobs > 0).then_some(blobs);
        let budget = memory_budget(children.len(), child_claims, xmss.len(), sphincs.len(), rows);
        let used = stats.memory_used;
        println!(
            "children={} child_claims={child_claims} xmss={} sphincs={} blobs={blobs}: memory={used} cycles={} budget={budget}",
            children.len(),
            xmss.len(),
            sphincs.len(),
            stats.cycles
        );
        assert!(used <= budget, "within the budget");
        assert!(stats.cycles < used, "cycles below the memory");
        ((claims, proof), used)
    };
    let increment = |what: &str, (low, high): (usize, usize), allowed: usize| {
        println!("{what}: {} words, {allowed} allowed", high.saturating_sub(low));
        assert!(high <= low + allowed, "{what} within its coefficients");
    };
    let xmss = get_signers::<StableProver>(1025);
    let sphincs = get_lean_sphincs_signers::<StableProver>(96);
    let (wide, x_low) = run(&[], &xmss[..512], &[], 0);
    let (wider, x_high) = run(&[], &xmss[..1024], &[], 0);
    increment("512 leanXMSS", (x_low, x_high), 512 * 1_400);
    let (_, s_low) = run(&[], &[], &sphincs[..32], 0);
    let (_, s_high) = run(&[], &[], &sphincs, 0);
    increment("64 leanSPHINCS", (s_low, s_high), 64 * 7_500);
    let (_, b_low) = run(&[], &xmss[..512], &[], 8);
    let (_, b_high) = run(&[], &xmss[..512], &[], 16);
    increment("a matrix of 8 blob rows", (x_low, b_low), 131_072 + 8 * 122_000);
    increment("8 blob rows", (b_low, b_high), 8 * 122_000);
    let small = run(&[], &xmss[..8], &[], 0).0;
    let (_, c_low) = run(&vec![small.clone(); 4], &xmss[..512], &[], 0);
    let (_, c_high) = run(&vec![small; 8], &xmss[..512], &[], 0);
    increment("4 children", (c_low, c_high), 4 * (457_265 + 8 * 66));
    // Children with longer lists and larger proofs, the claims' cost and the proofs' within the budget.
    run(&vec![wide; 4], &xmss[..512], &[], 0);
    run(&vec![wider.clone(); 2], &[], &[], 0);
    run(&vec![wider.clone(); 4], &[], &sphincs, 16);
    // The costliest claim: a child repeating its sibling's claims around one of its own, so that they take duplicate
    // slots out of order (`child_claim_list_any`).
    let around = run(std::slice::from_ref(&wider), &xmss[1024..], &[], 0).0;
    let own = around
        .0
        .lean_xmss
        .iter()
        .position(|claim| !wider.0.lean_xmss.contains(claim));
    assert!(
        own.is_some_and(|i| i + 1 < around.0.lean_xmss.len()),
        "a claim of its own before the last"
    );
    let (_, d_low) = run(std::slice::from_ref(&wider), &[], &[], 0);
    let (_, d_high) = run(&[wider, around], &[], &[], 0);
    increment(
        "a child of 1025 claims, 1024 out of order",
        (d_low, d_high),
        457_265 + 1_025 * 66,
    );
}
