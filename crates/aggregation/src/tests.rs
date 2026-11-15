use super::cells::{count, pack_16_bytes};
use super::deferred::{DeferredBytecodeClaim, bytecode_sums, bytecode_value, bytecode_vars};
use super::error::AggregateError;
use super::guest::{GUEST_SOURCE, compile_guest, scalar_bytecode};
use super::hints::{FORGE, Forgery, Hints};
use super::placeholders::placeholder_map;
use super::proof::{AggregateClaims, AggregateProof, decode, encode};
use super::statement::{CLAIM_GROUP, claim_list_digest, list_split};
use super::*;
use fiat_shamir_prover::merkle::hash_to_scalars;
use isa::Prover;
use keccak256::{hash, hash_pair};
use lean_da::{BLOB_SYMBOLS, CELL_SYMBOLS, CELLS_PER_ROW, Codeword, DA_MAX_ROWS, Hash};
use lean_sphincs::LeanSphincsSignature;
use lean_vm_core::StableProver;
use lean_vm_core::cpu::{ExecError, Execution, Program, from_scalar, to_scalar};
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

/// The guest's helpers under a `main` of their own, assembled at the bytecode size `2^kbc`.
fn guest_snippet(main: &str, kbc: usize) -> Program {
    let (helpers, _) = GUEST_SOURCE.split_once("\ndef main():").unwrap();
    let source = format!("{helpers}\ndef main():\n{main}");
    StableProver::init();
    StableProver::assemble(compile(
        &parse_with_replacements(&source, &placeholder_map(kbc)).unwrap(),
    ))
}

/// Run `program` on `public_input` with the witness `hints`.
fn run(program: &Program, hints: Hints, public_input: [F128; 2]) -> Result<Execution, ExecError> {
    let mut program = program.clone();
    for (name, entries) in hints.witness() {
        let entries = entries
            .into_iter()
            .map(|entry| entry.into_iter().map(from_scalar).collect());
        program.set_witness(name, entries.collect());
    }
    program.execute(public_input)
}

// The native verifier derives the DA challenge's grind from its own copy of the blob size.
const _: () = assert!(verifier::da::LOG_BLOB_SYMBOLS == lean_da::LOG_BLOB_SYMBOLS);

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
    let mut sphincs = get_lean_sphincs_signers(3);
    for tag in [3u8, 9] {
        let signed: lean_sphincs::Message = std::array::from_fn(|i| tag.wrapping_mul(i as u8 + 1));
        sphincs.push((public_key, signed, lean_sphincs::sign(&secret_key, &signed)));
    }
    let leaf = prove(&[], &get_signers(3), &sphincs);
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
    let signers = get_lean_sphincs_signers(1);
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
    let signers = get_signers(1);
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
        get_signers(SMALL_LEAF_SIZE),
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
    let child = prove(&[], &get_signers(SMALL_LEAF_SIZE), &[]);
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
                let execution = run(&guest, hints, [expected, F128::ZERO]).unwrap();
                assert!(execution.unconstrained_reads.is_empty());
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
    let big = 2 * CLAIM_GROUP + 3;
    let signers = get_signers(SMALL_LEAF_SIZE + big);
    let left = prove(&[], &signers[..SMALL_LEAF_SIZE], &[]);
    let right = prove(&[], &signers[SMALL_LEAF_SIZE..], &[]);
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
        da_commitment: Some(matrix.top_root()),
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
    let signers = get_signers(SMALL_LEAF_SIZE);
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
        Some(lean_da::BlobMatrix::build(&rows).unwrap().top_root())
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
        run(&guest, hints, [body, rest])
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
        run(&guest, hints, [F128::ZERO, F128::ZERO])
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
        r#"    r0, r1, z = da_verify()
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
    assert_eq!(da_root(&rows), witness.top_root());
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
        run(&guest, hints, hash_to_scalars(&verifier::da::digest(Some(commitment))))
    };
    assert!(verify(&rows).unwrap().unconstrained_reads.is_empty());
    for (position, flip) in [(0, 1), (BLOB_SYMBOLS + 5, 1 << 64)] {
        let mut corrupted = rows.clone();
        corrupted[1][position] ^= flip;
        assert!(verify(&corrupted).is_err(), "a flip of {flip:#x} at {position} passed");
    }
}

/// The commitment to rows that need not be codewords, rebuilt pairwise as `BlobMatrix::build` does it.
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
    root(blob_roots)
}

/// Claims left undeclared take duplicate slots. The first narrowing drops every
/// claim on one message, the second all but one claim.
#[test]
fn a_node_may_publish_less_than_it_covers() {
    let at_a = get_signers(3);
    let at_b = get_signers_for(2, MESSAGE_B);
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
    let b = get_signers_for(1, MESSAGE_B);
    let claim_b = vec![(b[0].0, message_for(MESSAGE_B))];
    let declare = AggregateClaims {
        lean_xmss: claim_b.clone(),
        ..AggregateClaims::default()
    };
    let raw = [get_signers(1), b].concat();
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
    let at_a = get_signers(4);
    let at_b = get_signers_for(2, MESSAGE_B);
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
        run(&guest, hints, claim_list_digest(child.iter().copied()))
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
    let xmss = get_signers(17);
    let sphincs = get_lean_sphincs_signers(5);
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
    let root = prove(&[left, right], &get_signers_for(2, MESSAGE_B), &sphincs[4..]);
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
        let value = from_scalar(scalar_bytecode().evaluate(&scalars).unwrap());
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

    let (public_key, signed, signature) = get_lean_sphincs_signers(1).pop().expect("one signer");
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
