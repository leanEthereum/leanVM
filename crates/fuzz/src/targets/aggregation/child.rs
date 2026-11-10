//! `guest-child`: a malicious child. A fixture aggregate is forged (its VM proof mutated, its deferred claim's point or
//! value changed, its claims or DA root changed) and handed to a node as a child. A differential test of
//! `crates/verifier` against the recursive verifier in `lean_ethereum.py`: whatever [`EthereumProof::verify`] rejects,
//! the guest's run has to refuse, and the other way round.

use super::common::{Inputs, benign_twin, describe_claims, describe_outcome, outcome, reads_a_valid_twin, verify_kind};
use super::fixtures::{Fixtures, N_SPHINCS, N_XMSS, fixtures};
use crate::mutate_proof::{mutate, perturb};
use crate::{Ctx, Finding, Outcome, Source};
use primitives::field::F192;
use rec_aggregation::fuzzing::{Parts, leaf_deferred, true_deferred_value};
use rec_aggregation::{EthereumClaims, EthereumProof};
use signatures::lean_sphincs::LeanSphincsPublicKey;
use signatures::lean_xmss::LeanXmssPublicKey;

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let f = fixtures(ctx)?;
    let i = src.below(f.children.len());
    let honest = f.proof(i);
    let mut parts = honest.clone().into_parts();
    let mut attack = forge(&mut parts, src, f, i);
    if src.chance(1, 6) {
        attack = format!("{attack} + {}", forge(&mut parts, src, f, i));
    }
    let forged = EthereumProof::from_parts(parts);
    ctx.note(format!("attack {attack}"));
    let context = format!("guest-child {}", f.children[i].name);
    let same_claims = forged.claims() == honest.claims();
    let same_defer = forged.deferred() == honest.deferred();
    let same_proof = forged.vm_proof() == honest.vm_proof();
    if same_claims && same_defer && same_proof {
        ctx.note("forgery changed nothing");
        return Ok(());
    }

    let verdict = forged.verify();
    let forged_claims = describe_claims(forged.claims());
    let detail = |extra: &str| {
        format!(
            "attack: {attack} on fixture `{}`\nhonest claims {}\nforged claims {forged_claims}\nverify: {verdict:?}\n{extra}",
            f.children[i].name,
            describe_claims(honest.claims()),
        )
    };
    // A statement some fixture honestly proves is true, whatever proof bytes back it: another fixture's whole aggregate,
    // or `x3r2`'s proof of `x3`'s claims.
    let true_statement = (0..f.children.len())
        .any(|j| forged.claims() == f.proof(j).claims() && forged.deferred() == f.proof(j).deferred());
    if verdict.is_ok() && true_statement && !(same_claims && same_defer) {
        ctx.note("forgery is another fixture's true statement");
        return Ok(());
    }
    if verdict.is_ok() {
        if !(same_claims && same_defer) {
            return Err(Finding::critical(
                format!("{context}: the Rust verifier accepts an aggregate with another statement"),
                detail("EthereumProof::verify accepted claims or a deferred claim the proof was not made for"),
            ));
        }
        ctx.note("verify accepts a mutated proof");
    }

    let mut inputs = Inputs::default();
    inputs.forged_child(forged, &format!("forged {}", f.children[i].name));
    if src.chance(1, 3) {
        inputs.child(f, src.below(f.children.len()));
        if src.bool() {
            inputs.children.swap(0, 1);
            inputs.names.swap(0, 1);
        }
    }
    if src.chance(1, 4) {
        inputs.xmss.push(f.signers.xmss[src.below(N_XMSS)].clone());
    }
    if src.chance(1, 6) {
        inputs.sphincs.push(f.signers.sphincs[src.below(N_SPHINCS)].clone());
    }
    let result = crate::catch(|| inputs.execute()).map_err(|(message, location)| {
        let mut finding = Finding::panic(&message, &location).in_context("aggregate panics on an invalid child");
        finding.detail = format!(
            "{}\n{}",
            finding.detail,
            detail(&format!("inputs: {}", inputs.describe()))
        );
        finding
    })?;
    super::common::note_kill(ctx, &result);
    match outcome(&result) {
        Err(kind) => {
            ctx.note(format!("refused {kind}"));
            if verdict.is_ok() {
                return Err(Finding::high(
                    format!("{context}: the guest refuses a child the Rust verifier accepts ({kind})"),
                    detail(&format!("{}\ninputs: {}", describe_outcome(&result), inputs.describe())),
                ));
            }
            Ok(())
        }
        Ok(()) => {
            let run = result.expect("accepted");
            if verdict.is_ok() {
                ctx.note("accepted a malleated proof the verifier accepts");
                return Ok(());
            }
            let why = verify_kind(verdict.as_ref().expect_err("rejected"));
            let k = inputs
                .names
                .iter()
                .position(|n| n.starts_with("forged"))
                .expect("a forged child");
            if let Some(j) = reads_a_valid_twin(f, &inputs, k) {
                let mut finding = benign_twin(&context, f.children[j].name);
                finding.detail = detail(&finding.detail);
                return Err(finding);
            }
            let value_only = same_claims && same_proof && forged_point_is(&inputs, honest);
            if why == "MalformedClaim" && value_only {
                // The guest batches a child's carried value without checking it: a false one has to survive into
                // the node's own deferred claim, which the root's `verify` recomputes.
                if true_deferred_value(&run.defer_point) == Some(run.defer_value) {
                    return Err(Finding::critical(
                        format!("{context}: a false carried deferred value vanishes in the batch"),
                        detail("the node's own deferred claim is true although a child's carried one is false"),
                    ));
                }
                ctx.note("false carried value propagates");
                return Ok(());
            }
            Err(Finding::critical(
                format!("{context}: the guest accepts a child the Rust verifier rejects ({why})"),
                detail(&format!(
                    "inputs: {}\npublished {}",
                    inputs.describe(),
                    describe_claims(&run.claims)
                )),
            ))
        }
    }
}

/// Whether the forged child (the first of `inputs` that is not a fixture) kept the honest deferred point.
fn forged_point_is(inputs: &Inputs, honest: &EthereumProof) -> bool {
    inputs
        .children
        .iter()
        .zip(&inputs.names)
        .find(|(_, n)| n.starts_with("forged"))
        .is_some_and(|(c, _)| c.deferred().0 == honest.deferred().0)
}

/// One edit of a child as a malicious aggregator would send it, named.
pub fn forge(parts: &mut Parts, src: &mut Source, f: &Fixtures, i: usize) -> String {
    let j = (i + 1 + src.below(f.children.len() - 1)) % f.children.len();
    let other = f.proof(j);
    match src.weighted(&[6, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 6]) {
        0 => format!("proof {}", mutate(&mut parts.proof, src, Some(other.vm_proof()))),
        16 => opened_content(&mut parts.proof, src),
        1 => {
            let n = src.range(2, 4);
            for _ in 0..n {
                mutate(&mut parts.proof, src, Some(other.vm_proof()));
            }
            "proof many".into()
        }
        2 => {
            parts.proof = other.vm_proof().clone();
            format!("proof of `{}`", f.children[j].name)
        }
        3 => {
            parts.defer_value = perturb(parts.defer_value, src);
            "defer value".into()
        }
        4 => {
            let k = src.below(parts.defer_point.len().max(1));
            if let Some(x) = parts.defer_point.get_mut(k) {
                *x = perturb(*x, src);
            }
            if src.bool() {
                if let Some(v) = true_deferred_value(&parts.defer_point) {
                    parts.defer_value = v;
                }
                "defer point, true value".into()
            } else {
                "defer point".into()
            }
        }
        5 => {
            (parts.defer_point, parts.defer_value) = leaf_deferred();
            "defer leaf's".into()
        }
        6 => {
            let (p, v) = other.deferred();
            parts.defer_point = p.to_vec();
            parts.defer_value = v;
            format!("defer of `{}`", f.children[j].name)
        }
        7 => {
            if src.bool() {
                parts.defer_point.pop();
            } else {
                parts.defer_point.push(F192::ZERO);
            }
            "defer point length".into()
        }
        8 => {
            let c = &mut parts.claims;
            let n = c.num_signature_claims();
            if n == 0 {
                return "claims none to edit".into();
            }
            let k = src.below(n);
            let flip = |m: &mut [u8; 32], src: &mut Source| m[src.below(32)] ^= 1 << src.below(8);
            if k < c.xmss.len() {
                flip(&mut c.xmss[k].1, src);
            } else {
                flip(&mut c.lean_sphincs[k - c.xmss.len()].1, src);
            }
            sort(c);
            "claims message".into()
        }
        9 => {
            let c = &mut parts.claims;
            if !c.xmss.is_empty() && (c.lean_sphincs.is_empty() || src.bool()) {
                let k = src.below(c.xmss.len());
                c.xmss[k].0 = f.signers.xmss[src.below(N_XMSS)].0;
            } else if !c.lean_sphincs.is_empty() {
                let k = src.below(c.lean_sphincs.len());
                c.lean_sphincs[k].0 = f.signers.sphincs[src.below(N_SPHINCS)].0;
            }
            sort(c);
            "claims pubkey".into()
        }
        10 => {
            let c = &mut parts.claims;
            match src.below(4) {
                0 => {
                    let (pk, m, _) = &f.signers.xmss[src.below(N_XMSS)];
                    c.xmss.push((*pk, *m));
                }
                1 => {
                    let (pk, m, _) = &f.signers.sphincs[src.below(N_SPHINCS)];
                    c.lean_sphincs.push((*pk, *m));
                }
                2 => {
                    let (pk, m, _) = &f.signers.xmss_two[1];
                    c.xmss.push((*pk, *m));
                }
                _ => {
                    let mut pk = [0u8; 32];
                    src.rng().fill(&mut pk);
                    c.xmss.push((LeanXmssPublicKey::from_bytes(&pk), src.array()));
                }
            }
            sort(c);
            "claims add".into()
        }
        11 => {
            let c = &mut parts.claims;
            let n = c.num_signature_claims();
            if n == 0 {
                return "claims none to remove".into();
            }
            let k = src.below(n);
            if k < c.xmss.len() {
                c.xmss.remove(k);
            } else {
                c.lean_sphincs.remove(k - c.xmss.len());
            }
            "claims remove".into()
        }
        12 => {
            let c = &mut parts.claims;
            if !c.xmss.is_empty() && (c.lean_sphincs.is_empty() || src.bool()) {
                let (pk, m) = c.xmss.remove(src.below(c.xmss.len()));
                c.lean_sphincs
                    .push((LeanSphincsPublicKey::from_bytes(&pk.to_bytes()), m));
            } else if !c.lean_sphincs.is_empty() {
                let (pk, m) = c.lean_sphincs.remove(src.below(c.lean_sphincs.len()));
                c.xmss.push((LeanXmssPublicKey::from_bytes(&pk.to_bytes()), m));
            }
            sort(c);
            "claims other scheme".into()
        }
        13 => {
            let c = &mut parts.claims;
            if c.xmss.len() > 1 {
                let k = src.below(c.xmss.len() - 1);
                c.xmss.swap(k, k + 1);
            } else if c.lean_sphincs.len() > 1 {
                c.lean_sphincs.swap(0, 1);
            }
            "claims unsorted".into()
        }
        14 => {
            parts.claims = other.claims().clone();
            format!("claims of `{}`", f.children[j].name)
        }
        _ => {
            let c = &mut parts.claims;
            c.da_commitment = match src.below(4) {
                0 => None,
                1 => other.claims().da_commitment.or(Some([1; 32])),
                2 => Some(super::fixtures::root_of(&f.blobs[2])),
                _ => c.da_commitment.map(|mut r| {
                    r[src.below(32)] ^= 1 << src.below(8);
                    r
                }),
            };
            "da root".into()
        }
    }
}

/// An opened leaf's word or a sibling changed, the query positions kept: the Fiat-Shamir transcript does not see
/// it, so the replay walks the proof and only the guest's Merkle check can refuse it.
fn opened_content(proof: &mut leanvm_core::cpu::Proof, src: &mut Source) -> String {
    let phases: Vec<usize> = (0..proof.merkle.len())
        .filter(|&p| !proof.merkle[p].is_empty())
        .collect();
    let Some(&phase) = phases.get(src.below(phases.len().max(1))) else {
        return "opened none".into();
    };
    let paths = &mut proof.merkle[phase];
    let q = src.below(paths.len());
    let path = &mut paths[q];
    if src.bool() && !path.leaf.is_empty() {
        let k = src.below(path.leaf.len());
        path.leaf[k].0 ^= 1 << src.below(64);
        "opened leaf word".into()
    } else if !path.siblings.is_empty() {
        let k = src.below(path.siblings.len());
        path.siblings[k][src.below(32)] ^= 1 << src.below(8);
        "opened sibling".into()
    } else {
        "opened none".into()
    }
}

fn sort(c: &mut EthereumClaims) {
    super::fixtures::normalize(c);
}
