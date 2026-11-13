//! Real aggregations for the Lean differential check of the guest (`lean_vm/cli/GuestDiff.lean`): per case,
//! the node's statement, its seed and witness (`LeanVM.Node.NodeWitness`: every child's statement, fresh claim and
//! raw proof, the raw signatures with their claims, the batching's hints), the streams `aggregate` installed, the public input and the
//! run's memory size, as whitespace-separated tokens. Ported from the BLAKE2s-era `guest_diff`: Flock's claims are
//! gone (a deferred and a fresh claim are a point and a value), and the installed streams are read through
//! `aggregation/hints.rs`'s test-only `FORGE` hook, which hands this module the node's `Hints` before they are installed.
//! `LEANVM_GUEST_DIFF=<dir> cargo test --release --manifest-path scripts/guest-export/Cargo.toml --lib guest_diff -- --ignored`
//! writes `<dir>/<case>.txt`.
//!
//! The tokens: a field element is its two limbs in hex, a `K` word one hex token, a byte string one hex token, a
//! list its length then its items; a section starts with its name, which the reader checks.

use super::*;
use crate::signers_cache::{get_lean_sphincs_signers, get_signers};
use lean_da::{BLOB_SYMBOLS, CODEWORD_SYMBOLS};
use leanvm_core::cpu::{public_input_bytes, scalar_proof};
use signatures::lean_sphincs::LeanSphincsSignature;
use signatures::lean_xmss::LeanXmssSignature;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::fmt::Write as _;

thread_local! {
    /// The streams of the last node this thread aggregated, as the `FORGE` hook saw them.
    static INSTALLED: std::cell::RefCell<Vec<(String, Vec<Vec<F128>>)>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Have the next node this thread aggregates record its streams in `INSTALLED`, unchanged.
fn capture_next() {
    FORGE.with(|forge| {
        *forge.borrow_mut() = Some(Box::new(|hints: &mut Hints| {
            INSTALLED.with(|i| *i.borrow_mut() = hints.0.clone());
        }));
    });
}

struct Out(String);

impl Out {
    fn tag(&mut self, tag: &str) {
        write!(self.0, "\n{tag} ").unwrap();
    }

    fn n(&mut self, n: usize) {
        write!(self.0, "{n} ").unwrap();
    }

    fn e(&mut self, x: F128) {
        write!(self.0, "{:x} {:x} ", x.c0, x.c1).unwrap();
    }

    fn es(&mut self, xs: &[F128]) {
        self.n(xs.len());
        for &x in xs {
            self.e(x);
        }
    }

    fn bytes(&mut self, bytes: &[u8]) {
        for b in bytes {
            write!(self.0, "{b:02x}").unwrap();
        }
        self.0.push(' ');
    }

    fn digests<const N: usize>(&mut self, digests: &[[u8; N]]) {
        self.n(digests.len());
        for d in digests {
            self.bytes(d);
        }
    }

    fn deferred(&mut self, c: &DeferredClaim) {
        self.tag("defer");
        self.es(&c.bytecode_point);
        self.e(c.bytecode_value);
    }

    /// `NodeStatement`: the claims, the DA digest (`verifier::da::digest`), and the deferred claim.
    fn statement(&mut self, p: &EthereumProof) {
        self.tag("xmss");
        self.n(p.claims.lean_xmss.len());
        for (pk, m) in &p.claims.lean_xmss {
            self.bytes(&pk.to_bytes());
            self.bytes(m);
        }
        self.tag("sphincs");
        self.n(p.claims.lean_sphincs.len());
        for (pk, m) in &p.claims.lean_sphincs {
            self.bytes(&pk.to_bytes());
            self.bytes(m);
        }
        self.tag("da");
        self.bytes(&verifier::da::digest(p.claims.da_commitment));
        self.deferred(&p.defer);
    }

    /// The leaf index, then each layer, bottom first, its randomizer, chain values and path: read off the
    /// signature's bytes (`to_bytes`, in that order), the crate keeping its fields private.
    fn xmss_signature(&mut self, sig: &LeanXmssSignature) {
        use lean_xmss::{LAYER_HEIGHT, LeafIndex, N, RANDOMIZER_LEN, V};
        const LEAF_INDEX_SIZE: usize = size_of::<LeafIndex>();
        let bytes = sig.to_bytes();
        let mut at = Cursor(&bytes[..]);
        self.n(sig.leaf_index() as usize);
        at.take(LEAF_INDEX_SIZE);
        for _ in 0..2 {
            self.bytes(at.take(RANDOMIZER_LEN));
            self.digests(at.take(V * N).as_chunks::<N>().0);
            self.digests(at.take(LAYER_HEIGHT * N).as_chunks::<N>().0);
        }
        assert!(at.0.is_empty(), "a leanXMSS signature is read whole");
    }

    /// The randomizer, each FORS tree's secret and path, then each layer, bottom first, its counter (big endian in
    /// the bytes), chain values and path: read off the signature's bytes (`to_bytes`, in that order).
    fn sphincs_signature(&mut self, sig: &LeanSphincsSignature) {
        use lean_sphincs::{COUNTER_LEN, FORS_HEIGHT, FORS_TREES, LAYER_HEIGHTS, N, V};
        let bytes = sig.to_bytes();
        let mut at = Cursor(&bytes[..]);
        self.bytes(at.take(N));
        for _ in 0..FORS_TREES {
            self.bytes(at.take(N));
            self.digests(at.take(FORS_HEIGHT * N).as_chunks::<N>().0);
        }
        for (layer, height) in LAYER_HEIGHTS.into_iter().enumerate() {
            let counter = u32::from_be_bytes(at.take(COUNTER_LEN).try_into().unwrap());
            assert_eq!(counter, sig.__layers()[layer].counter());
            self.n(counter as usize);
            self.digests(at.take(V * N).as_chunks::<N>().0);
            self.digests(at.take(height * N).as_chunks::<N>().0);
        }
        assert!(at.0.is_empty(), "a leanSPHINCS signature is read whole");
    }
}

/// A signature's bytes, read front to back.
struct Cursor<'a>(&'a [u8]);

impl<'a> Cursor<'a> {
    fn take(&mut self, len: usize) -> &'a [u8] {
        let (head, rest) = self.0.split_at(len);
        self.0 = rest;
        head
    }
}

/// Aggregate, and write the case: the statement, the witness, the installed streams.
fn export(
    name: &str,
    children: Vec<EthereumProof>,
    raw_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: &[u64],
) -> EthereumProof {
    capture_next();
    let node = aggregate(
        &children,
        raw_xmss.clone(),
        raw_sphincs.clone(),
        blobs,
        None,
        LOG_INV_RATE,
    )
    .expect("node aggregates");
    node.verify().expect("node verifies");
    let streams = INSTALLED.with(|i| i.take());
    let stream = |name: &str| streams.iter().find(|(n, _)| n == name).map(|(_, e)| e.as_slice());

    let mut out = Out(format!("leanvm-guest-diff 4\ncase {name}"));
    out.tag("seed");
    let seed = leanvm_core::cpu::fs_seed(unified_guest());
    out.bytes(&cell_bytes(seed));
    out.tag("log_memory");
    out.n(node.proof.stream[0].c0 as usize);
    out.tag("public_input");
    out.es(&node.vm_public_input());
    out.tag("statement");
    out.statement(&node);

    out.tag("children");
    out.n(children.len());
    let bytecode = scalar_bytecode();
    for child in &children {
        out.tag("child");
        out.statement(child);
        let pi = child.vm_public_input();
        let scalar = scalar_proof(&child.proof);
        let summary =
            verifier::replay_unchecked(bytecode, &public_input_bytes(&pi), &scalar).expect("the child replays");
        // The fresh claim's value, which the caller evaluates (`aggregate_with_stats` off its batch's sums).
        let fresh_point: Vec<F128> = summary.bytecode_point.iter().copied().map(from_scalar).collect();
        let fresh_value = mle_eval_par(stacked_bytecode(), &fresh_point);
        let (_, fresh) =
            gen_verify(unified_guest(), pi, &child.proof, &summary, fresh_value).expect("the child fits");
        out.tag("fresh");
        let point: Vec<F128> = fresh.bytecode_point.clone();
        out.es(&point);
        out.e(fresh.bytecode_value);
        out.tag("proof");
        out.es(&child.proof.stream);
        // Every phase's paths (`Proof::merkle_openings`), each its leaf index, leaf and siblings.
        out.n(scalar.merkle_openings.len());
        for phase in &scalar.merkle_openings {
            out.n(phase.len());
            for path in phase {
                out.n(path.leaf_index as usize);
                out.n(path.leaf.len());
                for w in &path.leaf {
                    write!(out.0, "{:x} ", w.0).unwrap();
                }
                out.digests(&path.siblings);
            }
        }
    }

    // The raw signatures with their claims, as `aggregate` uses them: sorted on the claim,
    // deduplicated (`aggregation/node.rs:109-113`).
    let mut raw_xmss = raw_xmss;
    raw_xmss.sort_by_key(|(pk, message, _)| (*pk, *message));
    raw_xmss.dedup_by(|(a, am, _), (b, bm, _)| (a, am) == (b, bm));
    out.tag("raw_xmss");
    out.n(raw_xmss.len());
    for (pk, m, sig) in &raw_xmss {
        out.bytes(&pk.to_bytes());
        out.bytes(m);
        out.xmss_signature(sig);
    }
    let mut raw_sphincs = raw_sphincs;
    raw_sphincs.sort_by_key(|(pk, message, _)| (*pk, *message));
    raw_sphincs.dedup_by(|(a, am, _), (b, bm, _)| (a, am) == (b, bm));
    out.tag("raw_sphincs");
    out.n(raw_sphincs.len());
    for (pk, m, sig) in &raw_sphincs {
        out.bytes(&pk.to_bytes());
        out.bytes(m);
        out.sphincs_signature(sig);
    }
    // The directly held matrix: its root, its membership challenge and its rows.
    let direct = (!blobs.is_empty()).then(|| lean_da::commit(blobs).expect("a whole number of blob rows"));
    out.tag("da_witness");
    match &direct {
        Some(witness) => {
            let root = &witness.root();
            out.0.push_str("direct ");
            out.bytes(root);
            out.e(from_scalar(verifier::da::membership_challenge(root)));
            let rows: Vec<&[u64]> = (0..).map_while(|i| witness.row(i)).collect();
            out.n(rows.len());
            for row in rows {
                out.n(row.len());
                for w in row {
                    write!(out.0, "{w:x} ").unwrap();
                }
            }
        }
        None => out.0.push_str("none "),
    }
    out.tag("batch");
    let rounds = |name: &str| stream(name).map_or(vec![], |e| e[0].clone());
    out.es(&rounds("bc_sumcheck_msgs"));
    out.es(&stream("bc_star_hint").map_or(vec![F128::ZERO], |e| e[0].clone()));

    out.tag("streams");
    out.n(streams.len());
    for (name, entries) in &streams {
        out.tag(&format!("stream {name}"));
        out.n(entries.len());
        for entry in entries {
            out.es(entry);
        }
    }
    out.tag("end\n");

    let dir = std::env::var_os("LEANVM_GUEST_DIFF").expect("LEANVM_GUEST_DIFF names the output directory");
    let dir = std::path::Path::new(&dir);
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join(format!("{name}.txt")), out.0).unwrap();
    node
}

const LOG_INV_RATE: usize = leanvm_core::pcs::TEST_LOG_INV_RATE;

fn blob(seed: u64) -> Vec<u64> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..BLOB_SYMBOLS).map(|_| rng.random()).collect()
}

/// Two leaves, one of both schemes with a blob, one whose leanXMSS list is longer than a group of its digest
/// (`CLAIM_GROUP` claims), and a node over them with a blob and raw signatures, one of a claim both leaves make: the
/// leaves overlap in a claim of each scheme, so every coverage region of the node has duplicate slots, and its claims
/// are held directly and through each child. Then a node over the same leaves the other way round, with no blob and no
/// raw signature: it publishes its second child's DA digest (`da_pick` a child's slot, not the first).
#[test]
#[ignore]
fn guest_diff() {
    parallel::init();
    let wide = CLAIM_GROUP + 3;
    let xmss = get_signers(wide + 2);
    let sphincs = get_lean_sphincs_signers(3);
    let left = export("left", vec![], xmss[..2].to_vec(), sphincs[..2].to_vec(), &blob(1));
    let right = export("right", vec![], xmss[1..wide + 1].to_vec(), sphincs[1..].to_vec(), &[]);
    let raw = vec![xmss[1].clone(), xmss[wide + 1].clone()];
    export("node", vec![left.clone(), right.clone()], raw, vec![], &blob(2));
    export("pass", vec![right, left], vec![], vec![], &[]);
}

/// The smallest case: a leaf of one leanXMSS signature.
#[test]
#[ignore]
fn guest_diff_leaf() {
    parallel::init();
    export("leaf", vec![], get_signers(1), vec![], &[]);
}
