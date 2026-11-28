//! Known answers of the deployed Rust for `Statement/LeanVmGuest.lean`, at the guest's real shape: the
//! claim lists' digests, the DA list's, the statement's digest under the deployed seed, the split table's first
//! entry (`DeferredBytecodeClaim::leaf`), the split columns at instructions (`FreshClaim::at` at vertices of the
//! instructions' cube: entries of `split_table`), and a batching of two children
//! with true claims on the split program (`aggregate_deferred_claims`, its column challenges and its sumcheck over
//! all `bytecode_vars()` variables), as `tests/LeanVMTests/Spec/NodeVectors.lean`. The Lean checks (`#guard`s
//! against the Spec definitions, and the mutations) are hand-written in `tests/LeanVMTests/Spec/Node.lean`, the
//! slow ones compiled in `cli/NodeVectors.lean`.

use super::*;
use lean_sphincs::LeanSphincsPublicKey;
use lean_xmss::LeanXmssPublicKey;
use lean_vm_core::StableProver;
use lean_vm_core::cpu::{from_scalar, to_scalar};
use primitives::field::F128;
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
    let challenge = from_scalar(verifier::da::membership_challenge(&root));
    let da = verifier::da::digest(Some(root));

    // A deferred claim of the guest's shape, its value arbitrary (the digest does not care).
    let defer = DeferredBytecodeClaim {
        bytecode_point: elements(&mut rng, kbcv),
        bytecode_value: element(&mut rng),
    };
    let seed = fs_seed();
    let claims = AggregateClaims { lean_xmss: xmss_typed, lean_sphincs: sphincs_typed, da_commitment: Some(root) };
    let statement = statement_digest(&claims, &defer);

    // Two children with true claims on the split program: each one's public input, the fresh claim its verification
    // raises at a point over the instructions, and the claim its statement carries.
    let kbc = unified_guest().prog.len().trailing_zeros() as usize;
    let public_inputs: Vec<[F128; 2]> = (0..2).map(|_| [element(&mut rng), element(&mut rng)]).collect();
    <StableProver as isa::Prover>::init();
    let fresh: Vec<FreshClaim> = (0..2).map(|_| FreshClaim::at(elements(&mut rng, kbc))).collect();
    let carried: Vec<DeferredBytecodeClaim> = (0..2)
        .map(|_| DeferredBytecodeClaim::recompute(elements(&mut rng, kbcv)))
        .collect();
    let carried_points: Vec<Vec<F128>> = carried.iter().map(|c| c.bytecode_point.clone()).collect();
    let carried_sums = bytecode_sums::<StableProver>(&carried_points);
    let (hints, batched) =
        aggregate_deferred_claims::<StableProver>(&public_inputs, &fresh, &carried, carried_sums);
    // The split columns at instructions: the first of each opcode, and the last. At a vertex of the instructions'
    // cube, `split_values` is the split table's entries there.
    let table = split_table();
    let n = table.len() >> SPLIT_LOG;
    let mut instructions: Vec<usize> = (0..verifier::layout::tables().len())
        .filter_map(|op| (0..n).find(|&k| table[op * n + k] == 1))
        .collect();
    instructions.push(n - 1);
    let vertices: Vec<(usize, Vec<F128>)> = instructions
        .iter()
        .map(|&k| {
            let point = (0..kbc).map(|i| F128::new(((k >> i) & 1) as u64, 0)).collect();
            (k, FreshClaim::at(point).values)
        })
        .collect();
    let leaf = DeferredBytecodeClaim::leaf();
    let hint = |name: &str| &hints.iter().find(|(n, _)| *n == name).unwrap().1;
    let msgs = hint("bc_sumcheck_msgs");
    let star = hint("bc_star_hint");
    assert_eq!(star.len(), 1);
    // The batching challenge's grind nonce, then each round's `(g1, g_inf)`: a degree-two round grinds nothing.
    assert!(BATCH_LAM_GRIND_BITS > 0 && fiat_shamir_prover::grinding_bits(2) == 0);
    assert_eq!(msgs.len(), 1 + 2 * kbcv);
    let (nonce, msgs) = (msgs[0], &msgs[1..]);

    let mut out = format!(
        "/-\n  LeanVMTests.Spec.NodeVectors\n\n  Generated by `guest-export` (lean_vm/scripts/guest-export) from leanVM; do not edit.\n  \
         The deployed Rust's encodings and batching on random inputs at the guest's shape\n  \
         (`bytecode_vars = {kbcv}`), which `Node.lean` checks against the Spec.\n-/\n\n\
         import Statement.LeanVmGuest\nimport LeanXmss.Scheme\nimport Statement.LeanSphincs\nimport LeanDa.Scheme\nimport Statement.Fast.Keccak\nimport FastFields.QuadExt\nimport FastFields.FieldWords\nimport LeanVM.Facts.Verifier\n\nnamespace LeanVMTests.Spec.NodeVectors\n\n\
         open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node\n\n\
         /-- A field element from its limbs. -/\n\
         def e (c0 c1 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1)\n\n"
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
        e(challenge)
    )
    .unwrap();
    writeln!(out, "/-- The statement's DA field for it (`verifier::da::digest`). -/\ndef daDigest : Digest := {}\n", digest(&da)).unwrap();
    writeln!(out, "/-- The statement's DA field without a root. -/\ndef daNone : Digest := {}\n", digest(&verifier::da::digest(None))).unwrap();
    writeln!(
        out,
        "/-- A deferred claim of the guest's shape. -/\ndef defer : DeferredBytecodeClaim :=\n  ⟨{},\n   {}⟩\n",
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
    let children: Vec<String> = public_inputs
        .iter()
        .zip(&fresh)
        .zip(&carried)
        .map(|((public_input, f), c)| {
            format!(
                "⟨{},\n   ⟨{},\n    {}⟩,\n   ⟨{},\n    {}⟩⟩",
                cells_digest(public_input),
                es(&f.point),
                es(&f.values),
                es(&c.bytecode_point),
                e(c.bytecode_value)
            )
        })
        .collect();
    writeln!(
        out,
        "/-- Two children, true claims on the split program: each one's public input, fresh claim (`FreshClaim::at`) \
         and carried claim (`DeferredBytecodeClaim::recompute`). -/\ndef children : List ChildClaims :=\n  {}\n",
        list(children)
    )
    .unwrap();
    writeln!(
        out,
        "/-- The leaf's deferred value, the split table's first entry (`DeferredBytecodeClaim::leaf`). -/\ndef leafValue : E := {}\n",
        e(leaf.bytecode_value)
    )
    .unwrap();
    writeln!(
        out,
        "/-- The split columns at instructions `k`, the first of each opcode and the last (`FreshClaim::at` at the \
         vertex `k`). -/\ndef vertices : List (ℕ × List E) :=\n  {}\n",
        list(vertices.iter().map(|(k, values)| format!("({k}, {})", es(values))).collect())
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
        "/-- The claim the batching defers. -/\ndef batched : DeferredBytecodeClaim :=\n  ⟨{},\n   {}⟩\n",
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
