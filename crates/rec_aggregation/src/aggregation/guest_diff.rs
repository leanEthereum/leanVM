//! Real aggregations for the Lean differential check of the guest (`formal/lean_vm/cli/GuestDiff.lean`): per case,
//! the node's statement, its seed and witness (`LeanVM.Node.NodeWitness`: every child's statement, fresh claims and
//! raw proof, a holder per claim, the batching's hints), the streams `aggregate` installed, the public input and the
//! run's memory size, as whitespace-separated tokens. `LEANVM_GUEST_DIFF=<dir> cargo test --release -p
//! rec_aggregation guest_diff -- --ignored` writes `<dir>/<case>.txt`; `lake exe guest-diff <dir>/*.txt` reads them.
//!
//! The tokens: a field element is its three limbs in hex, a `K` word one hex token, a byte string one hex token, a
//! list its length then its items; a section starts with its name, which the reader checks.

use super::*;
use crate::signers_cache::{get_lean_sphincs_signers, get_signers, message};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::fmt::Write as _;

struct Out(String);

impl Out {
    fn tag(&mut self, tag: &str) {
        write!(self.0, "\n{tag} ").unwrap();
    }

    fn n(&mut self, n: usize) {
        write!(self.0, "{n} ").unwrap();
    }

    fn e(&mut self, x: F192) {
        write!(self.0, "{:x} {:x} {:x} ", x.c0, x.c1, x.c2).unwrap();
    }

    fn es(&mut self, xs: &[F192]) {
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
        self.es(&c.matrix_point);
        self.e(c.matrix_a_value);
        self.e(c.matrix_b_value);
    }

    /// `NodeStatement`: the claims, each DA root with its vector digest, and the deferred claim.
    fn statement(&mut self, p: &EthereumProof) {
        self.tag("xmss");
        self.n(p.xmss_signers.len());
        for (pk, m) in &p.xmss_signers {
            self.bytes(&pk.flatten());
            self.bytes(m);
        }
        self.tag("sphincs");
        self.n(p.lean_sphincs_signers.len());
        for (pk, m) in &p.lean_sphincs_signers {
            self.bytes(&pk.flatten());
            self.bytes(m);
        }
        self.tag("da");
        self.n(p.da_roots.len());
        for root in &p.da_roots {
            self.bytes(root);
            self.bytes(&lean_da::vector_digest(&lean_da::membership_vector(root)));
        }
        self.deferred(&p.defer);
    }

    fn xmss_signature(&mut self, sig: &LeanXmssSignature) {
        self.n(sig.leaf_index as usize);
        for layer in [&sig.bottom, &sig.top] {
            self.bytes(&layer.randomizer);
            self.digests(&layer.chain_values);
            self.digests(&layer.path);
        }
    }

    fn sphincs_signature(&mut self, sig: &LeanSphincsSignature) {
        self.bytes(&sig.randomizer);
        for tree in &sig.forest {
            for subtree in &tree.subtrees {
                self.digests(&subtree.values);
                self.digests(&subtree.path);
            }
            self.digests(&tree.path);
        }
        self.n(sig.counter as usize);
        self.digests(&sig.wots);
        self.digests(&sig.path);
    }
}

/// Where a claim is held: its raw witness, else the first child that makes it.
fn holder<K: PartialEq>(claim: &K, raw: Option<impl FnOnce(&mut Out)>, children: &[&[K]], out: &mut Out) {
    match raw {
        Some(write) => {
            out.0.push_str("direct ");
            write(out);
        }
        None => {
            let i = children
                .iter()
                .position(|c| c.contains(claim))
                .expect("a claim is held");
            write!(out.0, "child {i} ").unwrap();
        }
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
    let streams = INSTALLED.take();
    let stream = |name: &str| streams.iter().find(|(n, _)| n == name).map(|(_, e)| e.as_slice());

    let mut out = Out(format!("leanvm-guest-diff 1\ncase {name}"));
    out.tag("seed");
    let seed = leanvm_core::cpu::fs_seed(unified_guest());
    out.bytes(&cell_bytes(seed));
    out.tag("log_memory");
    out.n(node.proof.stream[0].c0 as usize);
    out.tag("public_input");
    out.es(&node.public_input());
    out.tag("statement");
    out.statement(&node);

    out.tag("children");
    out.n(children.len());
    let bytecode = scalar_bytecode();
    for child in &children {
        out.tag("child");
        out.statement(child);
        let pi = child.public_input();
        let summary = verifier::replay_unchecked(bytecode, &public_input_bytes(&pi), &scalar_proof(&child.proof))
            .expect("the child replays");
        let openings: Vec<(Vec<u64>, Vec<[u8; 32]>)> = summary
            .merkle_paths
            .iter()
            .map(|path| (path.leaf.iter().map(|w| w.0).collect(), path.siblings.clone()))
            .collect();
        let (_, fresh) = gen_verify(unified_guest(), pi, &child.proof.stream, summary).expect("the child fits");
        out.tag("fresh");
        let point: Vec<F192> = fresh
            .bytecode_row_point
            .iter()
            .chain(&fresh.bytecode_selector_point)
            .copied()
            .collect();
        out.es(&point);
        out.e(fresh.bytecode_value);
        out.e(fresh.matrix_a_coefficient);
        out.e(fresh.skip_point);
        out.es(&fresh.zerocheck_row_point);
        let column_point: Vec<F192> = fresh.lincheck_round_point.iter().rev().copied().collect();
        out.es(&column_point);
        out.es(&fresh.lincheck_terminal_values);
        out.e(fresh.matrix_claim);
        out.tag("proof");
        out.es(&child.proof.stream);
        out.n(openings.len());
        for (leaf, siblings) in &openings {
            out.n(leaf.len());
            for w in leaf {
                write!(out.0, "{w:x} ").unwrap();
            }
            out.digests(siblings);
        }
    }

    let xmss_children: Vec<&[LeanXmssClaim]> = children.iter().map(|c| c.xmss_signers.as_slice()).collect();
    out.tag("holders_xmss");
    out.n(node.xmss_signers.len());
    for claim in &node.xmss_signers {
        let raw = raw_xmss.iter().find(|(pk, m, _)| (*pk, *m) == *claim);
        holder(
            claim,
            raw.map(|(_, _, sig)| |out: &mut Out| out.xmss_signature(sig)),
            &xmss_children,
            &mut out,
        );
    }
    let sphincs_children: Vec<&[LeanSphincsClaim]> =
        children.iter().map(|c| c.lean_sphincs_signers.as_slice()).collect();
    out.tag("holders_sphincs");
    out.n(node.lean_sphincs_signers.len());
    for claim in &node.lean_sphincs_signers {
        let raw = raw_sphincs.iter().find(|(pk, m, _)| (*pk, *m) == *claim);
        holder(
            claim,
            raw.map(|(_, _, sig)| |out: &mut Out| out.sphincs_signature(sig)),
            &sphincs_children,
            &mut out,
        );
    }
    let da_children: Vec<&[[u8; 32]]> = children.iter().map(|c| c.da_roots.as_slice()).collect();
    let direct = (!blobs.is_empty()).then(|| lean_da::commit(blobs));
    out.tag("holders_da");
    out.n(node.da_roots.len());
    for root in &node.da_roots {
        let raw = direct.as_ref().filter(|(commitment, _)| commitment.root == *root);
        let write = raw.map(|(_, witness)| {
            move |out: &mut Out| {
                let rows: Vec<&[u64]> = witness.codewords.chunks(CODEWORD_SYMBOLS).collect();
                out.n(rows.len());
                for row in rows {
                    out.n(row.len());
                    for w in row {
                        write!(out.0, "{w:x} ").unwrap();
                    }
                }
                out.es(&lean_da::membership_vector(root));
            }
        });
        holder(root, write, &da_children, &mut out);
    }
    out.tag("batch");
    let rounds = |name: &str| stream(name).map_or(vec![], |e| e[0].clone());
    out.es(&rounds("bc_sumcheck_msgs"));
    out.es(&rounds("mat_sumcheck_msgs"));
    let stars: Vec<F192> = [stream("bc_star_hint"), stream("mat_stars_hint")]
        .into_iter()
        .flat_map(|e| e.map_or(vec![F192::ZERO], |e| e[0].clone()))
        .collect();
    out.es(&stars);

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

/// Two leaves, one of both schemes with a blob, one whose leanXMSS list is longer than a window of its digest, and a
/// node over them with a blob and raw signatures, one of a claim both leaves make: the leaves overlap in a claim of
/// each scheme, so every coverage region of the node has duplicate slots, and its claims and roots are held directly
/// and through each child.
#[test]
#[ignore]
fn guest_diff() {
    leanvm_core::init_prover();
    let wide = SIGNERS_WINDOW + 3;
    let xmss: Vec<_> = get_signers(wide + 2)
        .into_iter()
        .map(|(pk, sig)| (pk, message(), sig))
        .collect();
    let sphincs = get_lean_sphincs_signers(3);
    let left = export("left", vec![], xmss[..2].to_vec(), sphincs[..2].to_vec(), &blob(1));
    let right = export("right", vec![], xmss[1..wide + 1].to_vec(), sphincs[1..].to_vec(), &[]);
    let raw = vec![xmss[1].clone(), xmss[wide + 1].clone()];
    export("node", vec![left, right], raw, vec![], &blob(2));
}
