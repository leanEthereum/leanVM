//! Test vectors for `formal/lean_vm/LeanVM/Spec/Node.lean`: the statement's encodings and the batching of
//! deferred claims, on small inputs, written as the Lean data `tests/LeanVMTests/Spec/NodeVectors.lean` checks
//! against the Lean definitions. The test regenerates the file and fails if it differs from the committed one;
//! `LEANVM_WRITE_NODE_VECTORS=1` rewrites it.

use super::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::fmt::Write as _;

const PATH: &str = "../../formal/lean_vm/tests/LeanVMTests/Spec/NodeVectors.lean";

/// The DA matrix's rows, which `NodeVectors.lean`'s checks rebuild from the same formula.
const DA_ROWS: usize = 3;
fn da_symbol(row: usize, column: usize) -> u64 {
    ((row * CODEWORD_SYMBOLS + column + 1) as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)
}

fn element(rng: &mut StdRng) -> F192 {
    F192::new(rng.random(), rng.random(), rng.random())
}

fn elements(rng: &mut StdRng, len: usize) -> Vec<F192> {
    (0..len).map(|_| element(rng)).collect()
}

fn sum(values: impl Iterator<Item = F192>) -> F192 {
    values.fold(F192::ZERO, |acc, x| acc + x)
}

/// A child's claims on the fixed polynomials, true: the bytecode at its point, and `A0 + α B0` between the lincheck's
/// row weights (the quirky eq table) and its column weights (`eq(columnPoint) ⊗ slices`, as Lean writes them).
fn true_subproof(rng: &mut StdRng) -> DeferredSubproof {
    let (klog, kskip) = (flock::hash::K_LOG, flock::hash::K_SKIP);
    let point = elements(rng, bytecode_vars());
    let bytecode_value = mle_eval_par(stacked_bytecode(), &point);
    let (skip_point, alpha) = (element(rng), element(rng));
    let zerocheck_row_point = elements(rng, klog - kskip);
    let lincheck_round_point = elements(rng, klog - kskip);
    let slices = elements(rng, 1 << kskip);
    let column_point: Vec<F192> = lincheck_round_point.iter().rev().copied().collect();
    let columns: Vec<F192> = pcs::whir::build_eq_table_ext(&column_point)
        .iter()
        .flat_map(|&weight| slices.iter().map(move |&s| s * weight))
        .collect();
    let rows = flock::lincheck::build_quirky_eq_table(skip_point, &zerocheck_row_point, kskip);
    let (a, b) = flock::hash::row_values_walk(&columns);
    let form = |m: &[F192]| sum(m.iter().zip(&rows).map(|(&m, &u)| m * u));
    let (row_point, selector_point) = point.split_at(point.len() - leanvm_core::leaf::N_BYTECODE_SELECTORS);
    DeferredSubproof {
        public_input: [0, 1].map(|_| F192::new(rng.random(), rng.random(), 0)),
        bytecode_row_point: row_point.to_vec(),
        bytecode_selector_point: selector_point.to_vec(),
        bytecode_value,
        matrix_a_coefficient: alpha,
        skip_point,
        zerocheck_row_point,
        lincheck_round_point,
        lincheck_terminal_values: slices,
        matrix_claim: form(&a) + alpha * form(&b),
    }
}

fn cells_bytes(cells: &[F192; 2]) -> [u8; 32] {
    assert!(
        cells.iter().all(|cell| cell.c2 == 0),
        "a digest half is a canonical cell"
    );
    cell_bytes(cells.iter().copied()).try_into().unwrap()
}

/// Lean source for the values, one definition each.
struct Lean(String);

impl Lean {
    fn def(&mut self, doc: &str, name: &str, ty: &str, value: String) {
        writeln!(self.0, "/-- {doc} -/\ndef {name} : {ty} :=\n  {value}\n").unwrap();
    }
}

fn e(x: F192) -> String {
    format!("e 0x{:x} 0x{:x} 0x{:x}", x.c0, x.c1, x.c2)
}

fn list(items: impl IntoIterator<Item = String>) -> String {
    let items: Vec<String> = items.into_iter().collect();
    if items.is_empty() {
        return "[]".into();
    }
    format!("[{}]", items.join(",\n    "))
}

fn es(xs: &[F192]) -> String {
    list(xs.iter().map(|&x| e(x)))
}

fn digest(bytes: &[u8; 32]) -> String {
    let words = bytes
        .chunks(4)
        .map(|w| format!("0x{:08x}", u32::from_le_bytes(w.try_into().unwrap())));
    format!("#v[{}]", words.collect::<Vec<_>>().join(", "))
}

fn bits(bytes: &[u8]) -> String {
    let hex: String = bytes.iter().rev().map(|b| format!("{b:02x}")).collect();
    format!("BitVec.ofNat {} 0x{hex}", 8 * bytes.len())
}

fn deferred(c: &DeferredClaim) -> String {
    format!(
        "⟨{},\n    {},\n    {},\n    {},\n    {}⟩",
        es(&c.bytecode_point),
        e(c.bytecode_value),
        es(&c.matrix_point),
        e(c.matrix_a_value),
        e(c.matrix_b_value)
    )
}

fn rounds(messages: &[F192]) -> String {
    list(messages.chunks(2).map(|m| format!("({}, {})", e(m[0]), e(m[1]))))
}

#[test]
fn node_spec_vectors() {
    let mut rng = StdRng::seed_from_u64(0x4e0d_e5ec);
    let mut out = Lean(String::new());

    // The seed is the IV the Lean verifier derives from the guest's stacked bytecode.
    let seed = leanvm_core::cpu::fs_seed(unified_guest());
    let bytecode_bytes: Vec<u8> = stacked_bytecode().iter().flat_map(|w| w.0.to_le_bytes()).collect();
    let preimage = [
        &b"leanvm"[..],
        &(flock::hash::R1CS_DIGEST.len() as u64).to_le_bytes(),
        &flock::hash::R1CS_DIGEST,
        &primitives::hash::hash(&bytecode_bytes),
    ]
    .concat();
    assert_eq!(
        cells_bytes(&seed),
        primitives::hash::hash(&preimage),
        "fs_seed is the Lean fiatShamirIv"
    );

    // One pubkey under two messages: a claim is the pair, so it is two claims.
    let xmss_key = LeanXmssPublicKey {
        merkle_root: rng.random(),
        public_param: rng.random(),
    };
    let other_key = LeanXmssPublicKey {
        merkle_root: rng.random(),
        public_param: rng.random(),
    };
    let xmss_signers: Vec<LeanXmssClaim> = [xmss_key, xmss_key, other_key]
        .into_iter()
        .map(|key| (key, rng.random()))
        .collect();
    let sphincs_signers: Vec<LeanSphincsClaim> = (0..2)
        .map(|_| {
            let key = LeanSphincsPublicKey {
                root: rng.random(),
                public_param: rng.random(),
            };
            (key, rng.random())
        })
        .collect();
    let codewords = (0..DA_ROWS)
        .flat_map(|row| (0..CODEWORD_SYMBOLS).map(move |column| da_symbol(row, column)))
        .collect();
    let matrix_root = lean_da::commit_codewords(codewords).0.root;
    let da_roots = [matrix_root, rng.random()];
    assert_eq!(verifier::da::list_digest(&da_roots), da_list_digest(&da_roots));

    let subproofs = [true_subproof(&mut rng), true_subproof(&mut rng)];
    let carried = [0, 1].map(|_| {
        DeferredClaim::recompute(
            elements(&mut rng, bytecode_vars()),
            elements(&mut rng, 2 * flock::hash::K_LOG),
        )
        .unwrap()
    });
    let (hints, batched) = aggregate_deferred_claims(&subproofs, &[&carried[0], &carried[1]]).unwrap();
    let hint = |name: &str| &hints.iter().find(|(n, _)| *n == name).unwrap().1;
    assert_eq!(
        DeferredClaim::recompute(batched.bytecode_point.clone(), batched.matrix_point.clone()).unwrap(),
        batched,
        "the batched claim is true"
    );

    let signers = signers_hash(&xmss_signers, &sphincs_signers);
    let statement = statement_digest(signers, da_list_digest(&da_roots), &batched);

    out.def(
        "`R1CS_DIGEST`.",
        "r1csDigest",
        "List UInt8",
        format!("{:?}", flock::hash::R1CS_DIGEST.to_vec()),
    );
    out.def(
        "`fs_seed(unified_guest())`.",
        "seed",
        "Digest",
        digest(&cells_bytes(&seed)),
    );
    let claims = xmss_signers
        .iter()
        .map(|(k, m)| format!("(⟨{}, {}⟩, {})", bits(&k.merkle_root), bits(&k.public_param), bits(m)));
    out.def("The leanXMSS claims.", "xmss", "List XmssClaim", list(claims));
    let xmss_digest = cells_bytes(&claim_list_digest(xmss_signers.iter().map(lean_xmss_claim_cells)));
    out.def(
        "`claim_list_digest` of the leanXMSS claims.",
        "xmssListDigest",
        "Digest",
        digest(&xmss_digest),
    );
    let claims = sphincs_signers
        .iter()
        .map(|(k, m)| format!("(⟨{}, {}⟩, {})", bits(&k.root), bits(&k.public_param), bits(m)));
    out.def("The leanSPHINCS claims.", "sphincs", "List SphincsClaim", list(claims));
    let sphincs_digest = cells_bytes(&claim_list_digest(sphincs_signers.iter().map(lean_sphincs_claim_cells)));
    out.def(
        "`claim_list_digest` of the leanSPHINCS claims.",
        "sphincsListDigest",
        "Digest",
        digest(&sphincs_digest),
    );
    out.def(
        "`signers_hash`.",
        "signersDigest",
        "Digest",
        digest(&cells_bytes(&signers)),
    );
    out.def(
        "The DA roots: the matrix's, then another.",
        "daRoots",
        "List Digest",
        list(da_roots.iter().map(digest)),
    );
    let vectors = da_roots.map(|r| lean_da::vector_digest(&lean_da::membership_vector(&r)));
    out.def(
        "`vector_digest(membership_vector(root))` of each root.",
        "daVectorDigests",
        "List Digest",
        list(vectors.iter().map(digest)),
    );
    out.def(
        "`da_list_digest`.",
        "daListDigest",
        "Digest",
        digest(&da_list_digest(&da_roots)),
    );
    let children = subproofs.iter().zip(&carried).map(|(s, c)| {
        let bytecode_point: Vec<F192> = s
            .bytecode_row_point
            .iter()
            .chain(&s.bytecode_selector_point)
            .copied()
            .collect();
        let column_point: Vec<F192> = s.lincheck_round_point.iter().rev().copied().collect();
        format!(
            "⟨{},\n    ⟨{},\n    {}, {}, {},\n    {},\n    {},\n    {},\n    {}⟩,\n    {}⟩",
            digest(&cells_bytes(&s.public_input)),
            es(&bytecode_point),
            e(s.bytecode_value),
            e(s.matrix_a_coefficient),
            e(s.skip_point),
            es(&s.zerocheck_row_point),
            es(&column_point),
            es(&s.lincheck_terminal_values),
            e(s.matrix_claim),
            deferred(c)
        )
    });
    out.def(
        "Two children whose claims are true.",
        "children",
        "List ChildClaims",
        list(children),
    );
    let hints = format!(
        "⟨{},\n    {},\n    {}, {}, {}⟩",
        rounds(hint("bc_sumcheck_msgs")),
        rounds(hint("mat_sumcheck_msgs")),
        e(hint("bc_star_hint")[0]),
        e(hint("mat_stars_hint")[0]),
        e(hint("mat_stars_hint")[1])
    );
    out.def("`aggregate_deferred_claims`'s hints.", "hints", "BatchHints", hints);
    out.def(
        "The claim the batching defers.",
        "batched",
        "DeferredClaim",
        deferred(&batched),
    );
    out.def(
        "`statement_digest` of the statement of these claims deferring `batched`.",
        "statementDigest",
        "Digest",
        digest(&cells_bytes(&statement)),
    );

    let text = format!(
        "/-\n  LeanVMTests.Spec.NodeVectors\n\n  Generated by `node_spec_vectors` (crates/rec_aggregation/src/aggregation/node_vectors.rs); do\n  not edit. `LeanVMTests.Spec.Node` checks them.\n-/\n\nimport LeanVM.Spec.Node\n\nnamespace LeanVMTests.Spec.NodeVectors\n\nopen LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Node\n\n/-- A field element from its limbs. -/\ndef e (c0 c1 c2 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1) (K.ofBits c2)\n\n{}end LeanVMTests.Spec.NodeVectors\n",
        out.0
    );
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(PATH);
    if std::env::var_os("LEANVM_WRITE_NODE_VECTORS").is_some() {
        std::fs::write(&path, &text).unwrap();
    }
    let committed = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(
        committed == text,
        "{} is stale; rerun with LEANVM_WRITE_NODE_VECTORS=1",
        path.display()
    );
}
