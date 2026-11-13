//! Known answers of the deployed Rust for `Statement/LeanVmGuest.lean`, at the guest's real shape: the
//! claim lists' digests, the DA list's, the statement's digest under the
//! deployed seed, and a batching of two children with true claims on the guest's stacked
//! bytecode (`aggregate_deferred_claims`, its sumcheck over all `bytecode_vars()` variables), as
//! `tests/LeanVMTests/Spec/NodeVectors.lean`. The successor of the BLAKE2s-era
//! `node_spec_vectors`; the Lean checks (`#guard`s against the Spec definitions, and the mutations)
//! are hand-written in `tests/LeanVMTests/Spec/Node.lean`.

use super::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::fmt::Write as _;

fn element(rng: &mut StdRng) -> F128 {
    F128::new(rng.random(), rng.random())
}

fn elements(rng: &mut StdRng, len: usize) -> Vec<F128> {
    (0..len).map(|_| element(rng)).collect()
}

fn e(x: F128) -> String {
    format!("e 0x{:x} 0x{:x}", x.c0, x.c1)
}

fn es(xs: &[F128]) -> String {
    format!("[{}]", xs.iter().map(|&x| e(x)).collect::<Vec<_>>().join(",\n    "))
}

/// A 32-byte digest as the Spec's four little-endian lanes.
fn digest(d: &[u8; 32]) -> String {
    let lanes: Vec<String> = (0..4)
        .map(|i| format!("0x{:016x}", u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().unwrap())))
        .collect();
    format!("#v[{}]", lanes.join(", "))
}

/// Two cells as a digest (`digestHalves`' inverse).
fn cells_digest(c: &[F128; 2]) -> String {
    format!("#v[0x{:016x}, 0x{:016x}, 0x{:016x}, 0x{:016x}]", c[0].c0, c[0].c1, c[1].c0, c[1].c1)
}

fn le_nat(bytes: &[u8]) -> String {
    let mut hex = String::from("0x");
    for b in bytes.iter().rev() {
        write!(hex, "{b:02x}").unwrap();
    }
    hex
}

fn claim(pk: &[u8; 32], message: &[u8; 32]) -> String {
    format!(
        "(⟨BitVec.ofNat 128 {}, BitVec.ofNat 128 {}⟩, BitVec.ofNat 256 {})",
        le_nat(&pk[..16]),
        le_nat(&pk[16..]),
        le_nat(message)
    )
}

fn bytes32(rng: &mut StdRng) -> [u8; 32] {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    b
}

pub fn file() -> File {
    let mut rng = StdRng::seed_from_u64(0x6c65_616e_766d);
    let kbcv = bytecode_vars();

    // Claims as raw keys: the root and parameter halves the lists hash.
    let xmss: Vec<([u8; 32], [u8; 32])> = (0..3).map(|_| (bytes32(&mut rng), bytes32(&mut rng))).collect();
    let sphincs: Vec<([u8; 32], [u8; 32])> = (0..2).map(|_| (bytes32(&mut rng), bytes32(&mut rng))).collect();
    let xmss_typed: Vec<LeanXmssClaim> = xmss
        .iter()
        .map(|(pk, m)| {
            let key = LeanXmssPublicKey::from_bytes(pk);
            assert_eq!(&key.to_bytes(), pk);
            (key, *m)
        })
        .collect();
    let sphincs_typed: Vec<LeanSphincsClaim> = sphincs
        .iter()
        .map(|(pk, m)| {
            let key = LeanSphincsPublicKey::from_bytes(pk);
            assert_eq!(&key.to_bytes(), pk);
            (key, *m)
        })
        .collect();
    let xmss_digest = claim_list_digest(xmss_typed.iter().map(lean_xmss_claim_cells));
    let sphincs_digest = claim_list_digest(sphincs_typed.iter().map(lean_sphincs_claim_cells));
    let root = bytes32(&mut rng);
    let challenge = verifier::da::membership_challenge(&root);
    let da = verifier::da::digest(Some(root));

    // A deferred claim of the guest's shape, its value arbitrary (the digest does not care).
    let defer = DeferredClaim {
        bytecode_point: elements(&mut rng, kbcv),
        bytecode_value: element(&mut rng),
    };
    let seed = leanvm_core::cpu::fs_seed(unified_guest());
    let statement = statement_digest(&xmss_typed, &sphincs_typed, da, &defer);

    // Two children with true claims on the stacked bytecode.
    let subproofs: Vec<DeferredSubproof> = (0..2)
        .map(|_| {
            let point = elements(&mut rng, kbcv);
            let value = mle_eval_par(stacked_bytecode(), &point);
            let canonical = |rng: &mut StdRng| F128::new(rng.random(), rng.random());
            DeferredSubproof {
                public_input: [canonical(&mut rng), canonical(&mut rng)],
                bytecode_point: point,
                bytecode_value: value,
            }
        })
        .collect();
    let carried: Vec<DeferredClaim> = (0..2)
        .map(|_| DeferredClaim::recompute(elements(&mut rng, kbcv)).unwrap())
        .collect();
    let carried_refs: Vec<&DeferredClaim> = carried.iter().collect();
    // Each child's fresh claim, then its carried one: the batch's order, which its sums follow.
    let points: Vec<Vec<F128>> = subproofs
        .iter()
        .zip(&carried)
        .flat_map(|(subproof, carried)| [subproof.bytecode_point.clone(), carried.bytecode_point.clone()])
        .collect();
    let (hints, batched) = aggregate_deferred_claims(&subproofs, &carried_refs, bytecode_sums(&points))
        .expect("the honest children's deferred values are the bytecode's evaluations");
    let hint = |name: &str| &hints.iter().find(|(n, _)| *n == name).unwrap().1;
    let msgs = hint("bc_sumcheck_msgs");
    let star = hint("bc_star_hint");
    assert_eq!(star.len(), 1);
    // The batching challenge's grind nonce, then each round's `(g1, g_inf)`: a degree-two round grinds nothing.
    assert!(BATCH_LAM_GRIND_BITS > 0 && fiat_shamir::grinding_bits(2) == 0);
    assert_eq!(msgs.len(), 1 + 2 * kbcv);
    let (nonce, msgs) = (msgs[0], &msgs[1..]);

    let mut out = format!(
        "/-\n  LeanVMTests.Spec.NodeVectors\n\n  Generated by `guest-export` (lean_vm/scripts/guest-export) from leanVM {rev}; do not\n  \
         edit. The deployed Rust's encodings and batching on random inputs at the guest's shape\n  \
         (`bytecode_vars = {kbcv}`), which `Node.lean` checks against the Spec.\n-/\n\n\
         import Statement.LeanVmGuest\nimport LeanXmss.Scheme\nimport Statement.LeanSphincs\nimport Statement.Fast.Schemes\nimport LeanDa.Scheme\nimport Statement.Fast.Keccak\nimport Statement.Fast.QuadExt\nimport Statement.Fast.FieldWords\nimport LeanVM.Facts.Verifier\n\nnamespace LeanVMTests.Spec.NodeVectors\n\n\
         open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node\n\n\
         /-- A field element from its limbs. -/\n\
         def e (c0 c1 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1)\n\n",
        rev = env!("LEANVM_REV")
    );
    let list = |items: Vec<String>| format!("[{}]", items.join(",\n  "));
    writeln!(out, "/-- The deployed seed (`fs_seed`). -/\ndef seed : Digest := {}\n", cells_digest(&seed)).unwrap();
    writeln!(
        out,
        "/-- leanXMSS claims. -/\ndef xmss : List LeanXmssClaim :=\n  {}\n",
        list(xmss.iter().map(|(pk, m)| claim(pk, m)).collect())
    )
    .unwrap();
    writeln!(out, "def xmssListDigest : Digest := {}\n", cells_digest(&xmss_digest)).unwrap();
    writeln!(
        out,
        "/-- leanSPHINCS claims. -/\ndef sphincs : List LeanSphincsClaim :=\n  {}\n",
        list(sphincs.iter().map(|(pk, m)| claim(pk, m)).collect())
    )
    .unwrap();
    writeln!(out, "def sphincsListDigest : Digest := {}\n", cells_digest(&sphincs_digest)).unwrap();
    writeln!(
        out,
        "/-- A DA claim: a root with the membership challenge the Rust derives from it. -/\ndef daClaim : DaClaim := ⟨{}, {}⟩\n",
        digest(&root),
        e(from_scalar(challenge))
    )
    .unwrap();
    writeln!(out, "/-- The statement's DA field for it (`verifier::da::digest`). -/\ndef daDigest : Digest := {}\n", digest(&da)).unwrap();
    writeln!(out, "/-- The statement's DA field without a root. -/\ndef daNone : Digest := {}\n", digest(&verifier::da::digest(None))).unwrap();
    writeln!(
        out,
        "/-- A deferred claim of the guest's shape. -/\ndef defer : DeferredClaim :=\n  ⟨{},\n   {}⟩\n",
        es(&defer.bytecode_point),
        e(defer.bytecode_value)
    )
    .unwrap();
    writeln!(
        out,
        "/-- `statement_digest` of the claims and `defer` under `seed`. -/\ndef statementDigest : Digest := {}\n",
        cells_digest(&statement)
    )
    .unwrap();
    let children: Vec<String> = subproofs
        .iter()
        .zip(&carried)
        .map(|(s, c)| {
            let fresh: Vec<F128> = s.bytecode_point.clone();
            format!(
                "⟨{},\n   ⟨{},\n    {}⟩,\n   ⟨{},\n    {}⟩⟩",
                cells_digest(&s.public_input),
                es(&fresh),
                e(s.bytecode_value),
                es(&c.bytecode_point),
                e(c.bytecode_value)
            )
        })
        .collect();
    writeln!(
        out,
        "/-- Two children, true claims on the guest's stacked bytecode. -/\ndef children : List ChildClaims :=\n  {}\n",
        list(children)
    )
    .unwrap();
    let rounds: Vec<String> = msgs.chunks(2).map(|p| format!("({}, {})", e(p[0]), e(p[1]))).collect();
    writeln!(
        out,
        "/-- The Rust's batching hints (`bc_sumcheck_msgs`, `bc_star_hint`). -/\ndef hints : BatchingHints where\n  lambdaGrindNonce := {}\n  sumcheckMessages :=\n  {}\n  finalBytecodeValue := {}\n",
        e(nonce),
        list(rounds),
        e(star[0])
    )
    .unwrap();
    writeln!(
        out,
        "/-- The claim the batching defers. -/\ndef batched : DeferredClaim :=\n  ⟨{},\n   {}⟩\n",
        es(&batched.bytecode_point),
        e(batched.bytecode_value)
    )
    .unwrap();
    out.push_str("end LeanVMTests.Spec.NodeVectors\n");
    File {
        path: "tests/LeanVMTests/Spec/NodeVectors.lean".into(),
        text: out,
    }
}
