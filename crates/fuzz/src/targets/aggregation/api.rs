//! `aggregate-api`: adversarial calls of the public aggregation API. Invalid raw signatures, duplicates within and
//! across raw signatures and children, too many children, claim counts at `MAX_KEYS`, declarations nothing covers,
//! blobs of bad sizes, empty nodes, rates out of range. The oracle: an error of the documented kind, never a panic,
//! never an accepted run that publishes something its inputs do not back; a sampled valid node is proven in full.

use super::common::{BAD_CHILD, Expect, Inputs, error_kind, expect_for, judge, prove_and_check};
use super::fixtures::{Fixtures, N_SPHINCS, N_XMSS, X3, fixtures, message_b, root_of};
use super::forge::random_inputs;
use crate::{Ctx, Finding, Outcome, Source};
use rec_aggregation::fuzzing::Parts;
use rec_aggregation::{EthereumClaims, EthereumProof, MAX_KEYS, MAX_RECURSIONS};
use signatures::lean_sphincs::{self, LeanSphincsPublicKey, LeanSphincsSignature};
use signatures::lean_xmss::{self, LeanXmssPublicKey, LeanXmssSignature};

type Case = fn(&Fixtures, &mut Source, &Ctx) -> Outcome;

const CASES: &[(&str, Case)] = &[
    ("valid", valid),
    ("bitflip-xmss", bitflip_xmss),
    ("bitflip-sphincs", bitflip_sphincs),
    ("wrong-message", wrong_message),
    ("wrong-key", wrong_key),
    ("other-scheme-key", other_scheme_key),
    ("garbage-signature", garbage_signature),
    ("duplicate-raw", duplicate_raw),
    ("raw-and-child-overlap", raw_and_child_overlap),
    ("too-many-children", too_many_children),
    ("max-children", max_children),
    ("child-at-max-keys", child_at_max_keys),
    ("declare-uncovered", declare_uncovered),
    ("declare-da", declare_da),
    ("bad-blob-size", bad_blob_size),
    ("empty", empty),
    ("invalid-rate", invalid_rate),
    ("declare-messy", declare_messy),
    ("child-bytes", child_bytes),
];

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let f = fixtures(ctx)?;
    let (name, case) = CASES[src.below(CASES.len())];
    ctx.note(format!("case {name}"));
    case(f, src, ctx)
}

fn context(case: &str) -> String {
    format!("aggregate-api {case}")
}

/// Run `inputs` against what they deserve, and prove a sampled valid one.
fn check(f: &Fixtures, src: &mut Source, ctx: &Ctx, case: &str, inputs: &Inputs) -> Outcome {
    let _ = f;
    let expect = expect_for(inputs);
    let ran = judge(ctx, &context(case), inputs, &expect)?;
    let heavy = ctx.depth >= 2 || (ctx.depth == 1 && src.chance(1, 6));
    if let (Some(_), Expect::Exactly(want), true) = (ran, &expect, heavy) {
        prove_and_check(ctx, src, &context(case), inputs, want)?;
    }
    Ok(())
}

/// Random valid inputs with no `declare`, at least one raw signature of the scheme asked for.
fn base(f: &Fixtures, src: &mut Source, xmss: bool, sphincs: bool) -> Inputs {
    let mut inputs = random_inputs(src, f);
    inputs.declare = None;
    if xmss && inputs.xmss.is_empty() {
        inputs.xmss.push(f.signers.xmss[src.below(N_XMSS)].clone());
    }
    if sphincs && inputs.sphincs.is_empty() {
        inputs.sphincs.push(f.signers.sphincs[src.below(N_SPHINCS)].clone());
    }
    inputs
}

fn valid(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let inputs = random_inputs(src, f);
    check(f, src, ctx, "valid", &inputs)
}

fn flip(bytes: &mut [u8], src: &mut Source) {
    let i = src.below(bytes.len());
    bytes[i] ^= 1 << src.below(8);
}

fn bitflip_xmss(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = base(f, src, true, false);
    let k = src.below(inputs.xmss.len());
    let mut bytes = inputs.xmss[k].2.to_bytes();
    flip(&mut bytes, src);
    inputs.xmss[k].2 = LeanXmssSignature::from_bytes(&bytes);
    check(f, src, ctx, "bitflip-xmss", &inputs)
}

fn bitflip_sphincs(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = base(f, src, false, true);
    let k = src.below(inputs.sphincs.len());
    let mut bytes = inputs.sphincs[k].2.to_bytes();
    flip(&mut bytes, src);
    inputs.sphincs[k].2 = LeanSphincsSignature::from_bytes(&bytes);
    check(f, src, ctx, "bitflip-sphincs", &inputs)
}

fn wrong_message(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = base(f, src, true, true);
    let message = match src.below(3) {
        0 => message_b(),
        1 => f.signers.sphincs[src.below(N_SPHINCS)].1,
        _ => src.array(),
    };
    if src.bool() {
        let k = src.below(inputs.xmss.len());
        inputs.xmss[k].1 = message;
    } else {
        let k = src.below(inputs.sphincs.len());
        inputs.sphincs[k].1 = message;
    }
    check(f, src, ctx, "wrong-message", &inputs)
}

fn wrong_key(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = base(f, src, true, true);
    if src.bool() {
        let k = src.below(inputs.xmss.len());
        inputs.xmss[k].0 = if src.bool() {
            f.signers.xmss[src.below(N_XMSS)].0
        } else {
            f.signers.xmss_two[0].0
        };
    } else {
        let k = src.below(inputs.sphincs.len());
        inputs.sphincs[k].0 = if src.bool() {
            f.signers.sphincs[src.below(N_SPHINCS)].0
        } else {
            f.signers.sphincs_two[0].0
        };
    }
    check(f, src, ctx, "wrong-key", &inputs)
}

/// The other scheme's pubkey bytes under a signature of this one: one byte string, two schemes.
fn other_scheme_key(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = base(f, src, true, true);
    if src.bool() {
        let k = src.below(inputs.xmss.len());
        let pk = f.signers.sphincs[src.below(N_SPHINCS)].0.to_bytes();
        inputs.xmss[k].0 = LeanXmssPublicKey::from_bytes(&pk);
    } else {
        let k = src.below(inputs.sphincs.len());
        let pk = f.signers.xmss[src.below(N_XMSS)].0.to_bytes();
        inputs.sphincs[k].0 = LeanSphincsPublicKey::from_bytes(&pk);
    }
    check(f, src, ctx, "other-scheme-key", &inputs)
}

fn garbage_signature(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = base(f, src, true, true);
    if src.bool() {
        let k = src.below(inputs.xmss.len());
        let bytes: [u8; lean_xmss::SIG_SIZE] = src.bulk(lean_xmss::SIG_SIZE).try_into().unwrap();
        inputs.xmss[k].2 = LeanXmssSignature::from_bytes(&bytes);
    } else {
        let k = src.below(inputs.sphincs.len());
        let bytes: [u8; lean_sphincs::SIG_SIZE] = src.bulk(lean_sphincs::SIG_SIZE).try_into().unwrap();
        inputs.sphincs[k].2 = LeanSphincsSignature::from_bytes(&bytes);
    }
    check(f, src, ctx, "garbage-signature", &inputs)
}

/// The same signature twice, or one claim under two leanXMSS signatures at different leaf indices.
fn duplicate_raw(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = base(f, src, true, false);
    match src.below(3) {
        0 => {
            let k = src.below(inputs.xmss.len());
            let copy = inputs.xmss[k].clone();
            inputs.xmss.insert(src.below(inputs.xmss.len() + 1), copy);
        }
        1 => {
            inputs.xmss.push(f.signers.xmss_two[0].clone());
            inputs.xmss.push(f.signers.xmss_two[2].clone());
        }
        _ => {
            let copy = f.signers.sphincs[src.below(N_SPHINCS)].clone();
            inputs.sphincs.push(copy.clone());
            inputs.sphincs.push(copy);
        }
    }
    check(f, src, ctx, "duplicate-raw", &inputs)
}

/// Raw signatures whose claims a child also carries: each claim declared once, the copies in duplicate slots.
fn raw_and_child_overlap(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs::default();
    let i = src.below(f.children.len());
    inputs.child(f, i);
    for (pk, m) in &f.claims(i).xmss {
        if let Some(raw) = f
            .signers
            .xmss
            .iter()
            .chain(&f.signers.xmss_two)
            .find(|r| r.0 == *pk && r.1 == *m)
            && src.bool()
        {
            inputs.xmss.push(raw.clone());
        }
    }
    for (pk, m) in &f.claims(i).lean_sphincs {
        if let Some(raw) = f.signers.sphincs.iter().find(|r| r.0 == *pk && r.1 == *m)
            && src.bool()
        {
            inputs.sphincs.push(raw.clone());
        }
    }
    if src.bool() {
        inputs.child(f, i);
    }
    check(f, src, ctx, "raw-and-child-overlap", &inputs)
}

fn too_many_children(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs::default();
    for _ in 0..MAX_RECURSIONS + 1 + src.below(3) {
        inputs.child(f, src.below(f.children.len()));
    }
    judge(
        ctx,
        &context("too-many-children"),
        &inputs,
        &Expect::Refused(&["TooLarge"]),
    )
    .map(|_| ())
}

fn max_children(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs::default();
    for _ in 0..MAX_RECURSIONS {
        inputs.child(f, src.below(f.children.len()));
    }
    if src.bool() {
        inputs.xmss.push(f.signers.xmss[src.below(N_XMSS)].clone());
    }
    check(f, src, ctx, "max-children", &inputs)
}

/// `n` distinct synthetic leanXMSS claims, sorted.
pub fn synthetic_claims(n: usize) -> Vec<(LeanXmssPublicKey, lean_xmss::Message)> {
    let mut claims: Vec<_> = (0..n)
        .map(|i| {
            let mut pk = [0x33u8; 32];
            pk[..8].copy_from_slice(&(i as u64).to_le_bytes());
            (LeanXmssPublicKey::from_bytes(&pk), [0x44; 32])
        })
        .collect();
    claims.sort();
    claims.dedup();
    claims
}

/// A child claiming `MAX_KEYS` claims or one fewer, with a real proof of other claims.
fn child_at_max_keys(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let n = MAX_KEYS - src.below(3);
    let Parts {
        defer_point,
        defer_value,
        proof,
        ..
    } = f.proof(X3).clone().into_parts();
    let claims = EthereumClaims {
        xmss: synthetic_claims(n),
        ..EthereumClaims::default()
    };
    let forged = EthereumProof::from_parts(Parts {
        claims,
        defer_point,
        defer_value,
        proof,
    });
    let kinds: &'static [&'static str] = if n >= MAX_KEYS {
        &["InvalidChild/MalformedSignerSet"]
    } else {
        BAD_CHILD
    };
    match forged.verify() {
        Ok(()) => {
            return Err(Finding::critical(
                format!(
                    "{}: verify accepts {n} claims of a proof of three",
                    context("child-at-max-keys")
                ),
                String::new(),
            ));
        }
        Err(e) => ctx.note(format!("child-at-max-keys verify {}", super::common::verify_kind(&e))),
    }
    let mut inputs = Inputs::default();
    inputs.forged_child(forged, &format!("{n} synthetic claims"));
    judge(ctx, &context("child-at-max-keys"), &inputs, &Expect::Refused(kinds)).map(|_| ())
}

/// A declaration with one claim nothing covers: another message, another key, the other scheme.
fn declare_uncovered(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = random_inputs(src, f);
    let all = {
        let mut everything = inputs.clone();
        everything.declare = None;
        everything.expected_claims()
    };
    let mut d = inputs.declare.clone().unwrap_or_else(|| all.clone());
    match src.below(4) {
        0 if !all.xmss.is_empty() => {
            let (pk, _) = all.xmss[src.below(all.xmss.len())];
            d.xmss.push((pk, [0xC3; 32]));
        }
        1 if !all.xmss.is_empty() => {
            let (pk, m) = all.xmss[src.below(all.xmss.len())];
            d.lean_sphincs
                .push((LeanSphincsPublicKey::from_bytes(&pk.to_bytes()), m));
        }
        2 if !all.lean_sphincs.is_empty() => {
            let (pk, m) = all.lean_sphincs[src.below(all.lean_sphincs.len())];
            d.xmss.push((LeanXmssPublicKey::from_bytes(&pk.to_bytes()), m));
        }
        _ => {
            let (pk, m, _) = &f.signers.sphincs_two[1];
            d.lean_sphincs.push((*pk, *m));
        }
    }
    let covered =
        d.xmss.iter().all(|c| all.xmss.contains(c)) && d.lean_sphincs.iter().all(|c| all.lean_sphincs.contains(c));
    if covered {
        return Ok(());
    }
    inputs.declare = Some(d);
    judge(
        ctx,
        &context("declare-uncovered"),
        &inputs,
        &Expect::Refused(&["NotCovered"]),
    )
    .map(|_| ())
}

/// A DA root nothing holds, or, with blobs, any root but theirs.
fn declare_da(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = random_inputs(src, f);
    let mut d = inputs.expected_claims();
    let roots: Vec<[u8; 32]> = inputs
        .children
        .iter()
        .filter_map(|c| c.claims().da_commitment)
        .collect();
    let kinds: &'static [&'static str] = if inputs.blobs.is_empty() {
        let root = [root_of(&f.blobs[2]), [0; 32], [0xFF; 32]][src.below(3)];
        if roots.contains(&root) {
            return Ok(());
        }
        d.da_commitment = Some(root);
        &["BlobNotCovered"]
    } else {
        let own = root_of(&inputs.blobs);
        d.da_commitment = if roots.is_empty() || src.bool() {
            None
        } else {
            Some(roots[src.below(roots.len())])
        };
        if d.da_commitment == Some(own) {
            return Ok(());
        }
        &["BlobsUnpublished"]
    };
    inputs.declare = Some(d);
    judge(ctx, &context("declare-da"), &inputs, &Expect::Refused(kinds)).map(|_| ())
}

fn bad_blob_size(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = random_inputs(src, f);
    let n = lean_da::BLOB_SYMBOLS;
    let symbols = match src.below(8) {
        0 => 1,
        1 => n - 1,
        2 => n + 1,
        3 => 2 * n - 1,
        4 => 3 * n + src.range(1, n - 1),
        5 => n / 2,
        6 => n + src.range(1, n - 1),
        _ => (lean_da::DA_MAX_ROWS + 1) * n,
    };
    inputs.blobs = (0..symbols as u64).collect();
    inputs.declare = None;
    judge(
        ctx,
        &context("bad-blob-size"),
        &inputs,
        &Expect::Refused(&["InvalidBlobSize"]),
    )
    .map(|_| ())
}

fn empty(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs::default();
    match src.below(3) {
        0 => {}
        1 => {
            inputs.child(f, src.below(f.children.len()));
            inputs.declare = Some(EthereumClaims::default());
        }
        _ => {
            inputs.xmss.push(f.signers.xmss[src.below(N_XMSS)].clone());
            inputs.declare = Some(EthereumClaims::default());
        }
    }
    judge(ctx, &context("empty"), &inputs, &Expect::Refused(&["Empty"])).map(|_| ())
}

fn invalid_rate(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let inputs = random_inputs(src, f);
    let rate = [0, 5, 6, 64, usize::MAX][src.below(5)];
    let result = crate::catch(|| {
        rec_aggregation::aggregate(
            &inputs.children,
            inputs.xmss.clone(),
            inputs.sphincs.clone(),
            &inputs.blobs,
            inputs.declare.as_ref(),
            rate,
        )
    })
    .map_err(|(m, l)| Finding::panic(&m, &l).in_context("aggregate panics"))?;
    match result {
        Err(rec_aggregation::AggregationError::InvalidRate { .. }) => {
            ctx.note("invalid-rate refused");
            Ok(())
        }
        other => Err(Finding::low(
            format!("{}: not refused as InvalidRate", context("invalid-rate")),
            format!(
                "rate {rate}: {:?}",
                other.map(|p| p.claims().clone()).map_err(|e| error_kind(&e))
            ),
        )),
    }
}

/// A declaration with repeats, out of order: it names a set, which the node publishes sorted.
fn declare_messy(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = random_inputs(src, f);
    let mut d = inputs.declare.clone().unwrap_or_else(|| inputs.expected_claims());
    d.xmss.reverse();
    d.lean_sphincs.reverse();
    if let Some(&c) = d.xmss.first() {
        d.xmss.push(c);
    }
    if let Some(&c) = d.lean_sphincs.last() {
        d.lean_sphincs.insert(0, c);
    }
    inputs.declare = Some(d);
    check(f, src, ctx, "declare-messy", &inputs)
}

/// A child decoded from bytes it was not proven as: another fixture's, truncated, with a byte flipped, or under
/// another fixture's claims.
fn child_bytes(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = src.below(f.children.len());
    let j = src.below(f.children.len());
    let mut bytes = f.proof(i).proof_bytes();
    let claims = f.claims(j).clone();
    match src.below(4) {
        0 => {}
        1 => bytes.truncate(src.below(bytes.len())),
        2 => flip(&mut bytes, src),
        _ => bytes.push(src.u8()),
    }
    let child = match EthereumProof::from_proof_bytes(&bytes, claims) {
        Err(e) => {
            ctx.note(format!("child-bytes decode {}", super::common::verify_kind(&e)));
            return Ok(());
        }
        Ok(child) => child,
    };
    if child.proof_bytes() == f.proof(j).proof_bytes() {
        // The very aggregate `j` is.
        return Ok(());
    }
    super::common::reject_child(ctx, &context("child-bytes"), Inputs::default(), child, 0)
}
