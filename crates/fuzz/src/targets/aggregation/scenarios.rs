//! `aggregation-scenarios`: hand-written attacks on a node, each a named function stating what it tries and what it
//! expects. The case's input picks the scenario, and the variant where a scenario has several. A forgery accepted is
//! Critical; an honest node refused or publishing other claims is High.

use super::api::synthetic_claims;
use super::common::{
    BAD_SIGNATURE, Expect, Inputs, cells_of, count, count_inv, describe_claims, expect_for, judge, outcome,
    refusal_kind, reject_child,
};
use super::fixtures::{
    DA, Fixtures, MIXED, N_XMSS, NARROW, NODE, S2, TWO_MSG, X3, X3R2, fixtures, message_b, root_of, union,
};
use super::forge::{Streams, index_of, resplit};
use crate::mutate_proof::perturb;
use crate::{Ctx, Finding, Outcome, Source};
use primitives::field::F192;
use rec_aggregation::fuzzing::{
    NodeRun, Parts, arm_forgery, disarm_forgery, leaf_deferred, prepare_node, run_guest, statement_of,
    true_deferred_value,
};
use rec_aggregation::{
    AggregateVerifyError, AggregationError, EthereumClaims, EthereumProof, MAX_KEYS, MAX_RECURSIONS,
};
use signatures::lean_sphincs::LeanSphincsPublicKey;
use signatures::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};

type Scenario = fn(&Fixtures, &mut Source, &Ctx) -> Outcome;

pub const SCENARIOS: &[(&str, Scenario)] = &[
    ("pubkey-in-both-schemes", pubkey_in_both_schemes),
    ("one-key-two-messages-declared-once", one_key_two_messages_declared_once),
    ("one-claim-two-signatures", one_claim_two_signatures),
    ("child-superset-of-sibling", child_superset_of_sibling),
    ("same-child-twice", same_child_twice),
    (
        "child-claim-redeclared-other-message",
        child_claim_redeclared_other_message,
    ),
    ("leaf-child-forged-deferred-value", leaf_child_forged_deferred_value),
    ("node-child-with-leaf-point", node_child_with_leaf_point),
    ("children-at-two-rates", children_at_two_rates),
    ("grandparent-readds-dropped-claim", grandparent_readds_dropped_claim),
    ("da-root-of-second-child", da_root_of_second_child),
    ("blobs-declaring-no-root", blobs_declaring_no_root),
    ("child-at-max-keys-minus-one", child_at_max_keys_minus_one),
    ("other-childs-proof-bytes", other_childs_proof_bytes),
    ("swapped-deferred-claims", swapped_deferred_claims),
    ("dataless-child-only", dataless_child_only),
    ("root-forged-deferred-value", root_forged_deferred_value),
    ("xmss-claim-declared-as-sphincs", xmss_claim_declared_as_sphincs),
    ("child-claim-moved-to-other-scheme", child_claim_moved_to_other_scheme),
    ("child-claim-dropped", child_claim_dropped),
    ("child-claim-added", child_claim_added),
    ("empty-declaration", empty_declaration),
    ("raw-repeats-child-claim", raw_repeats_child_claim),
    ("invalid-undeclared-raw-signature", invalid_undeclared_raw_signature),
    ("sixteen-children", sixteen_children),
    ("child-with-other-da-root", child_with_other_da_root),
    ("blob-node-over-blob-children", blob_node_over_blob_children),
    ("declared-list-with-repeats", declared_list_with_repeats),
    ("claim-of-another-signer-by-hint", claim_of_another_signer_by_hint),
    (
        "sphincs-signature-published-as-xmss",
        sphincs_signature_published_as_xmss,
    ),
    ("dup-slot-promoted-to-foreign-claim", dup_slot_promoted_to_foreign_claim),
    ("raw-index-into-other-region", raw_index_into_other_region),
    ("child-walk-into-other-region", child_walk_into_other_region),
    ("child-wire-tampering", child_wire_tampering),
    ("da-root-without-child", da_root_without_child),
    ("leaf-lies-about-deferred-value", leaf_lies_about_deferred_value),
    ("child-claims-collapsed-to-a-repeat", child_claims_collapsed_to_a_repeat),
];

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let f = fixtures(ctx)?;
    let (name, scenario) = SCENARIOS[src.below(SCENARIOS.len())];
    ctx.note(format!("scenario {name}"));
    scenario(f, src, ctx).map_err(|finding| finding.in_context(&format!("scenario {name}")))
}

const CX: &str = "aggregation-scenarios";

fn exactly(ctx: &Ctx, inputs: &Inputs, want: EthereumClaims) -> Outcome {
    judge(ctx, CX, inputs, &Expect::Exactly(want)).map(|_| ())
}

fn refused(ctx: &Ctx, inputs: &Inputs, kinds: &'static [&'static str]) -> Outcome {
    judge(ctx, CX, inputs, &Expect::Refused(kinds)).map(|_| ())
}

fn with_children(f: &Fixtures, children: &[usize]) -> Inputs {
    let mut inputs = Inputs::default();
    for &i in children {
        inputs.child(f, i);
    }
    inputs
}

/// `fixture`'s aggregate with its parts edited.
fn edited(f: &Fixtures, fixture: usize, edit: impl FnOnce(&mut Parts)) -> EthereumProof {
    let mut parts = f.proof(fixture).clone().into_parts();
    edit(&mut parts);
    EthereumProof::from_parts(parts)
}

/// Build `inputs` with `edit` applied to the honest hints, and run the guest against the honest statement.
fn forged_run(inputs: &Inputs, edit: impl FnOnce(&mut Streams) + 'static) -> Result<NodeRun, AggregationError> {
    arm_forgery(Box::new(move |hints| edit(hints.streams_mut())));
    let result = inputs.execute();
    disarm_forgery();
    result
}

/// A witness the honest host would not produce must be refused.
fn forgery_refused(ctx: &Ctx, inputs: &Inputs, what: &str, edit: impl FnOnce(&mut Streams) + 'static) -> Outcome {
    let result = forged_run(inputs, edit);
    super::common::note_kill(ctx, &result);
    match outcome(&result) {
        Err(kind) => {
            ctx.note(format!("{what}: {kind}"));
            Ok(())
        }
        Ok(()) => Err(Finding::critical(
            format!("a forged witness is accepted: {what}"),
            format!("inputs: {}", inputs.describe()),
        )),
    }
}

/// Build `inputs` with `edit` applied to the hints, then run the guest against the statement of `claims(honest)`:
/// a node made to claim something else. Accepted and unbacked is Critical.
fn statement_refused(
    ctx: &Ctx,
    inputs: &Inputs,
    what: &str,
    edit: impl FnOnce(&mut Streams) + 'static,
    claims: impl FnOnce(&EthereumClaims) -> EthereumClaims,
) -> Outcome {
    arm_forgery(Box::new(move |hints| edit(hints.streams_mut())));
    let node = prepare_node(
        &inputs.children,
        inputs.xmss.clone(),
        inputs.sphincs.clone(),
        &inputs.blobs,
        inputs.declare.as_ref(),
    );
    disarm_forgery();
    let node = node.map_err(|e| Finding::high(format!("{what}: the honest node is not built"), format!("{e:?}")))?;
    let forged = claims(&node.claims);
    let pi = statement_of(&forged, &node.defer_point, node.defer_value);
    match run_guest(&node.program, pi) {
        Err(e) => {
            ctx.note(format!("{what}: {}", refusal_kind(&e)));
            Ok(())
        }
        Ok(_) => match inputs.backing().unbacked(&forged) {
            Some(why) => Err(Finding::critical(
                format!("a node claiming what nothing backs is accepted: {what}"),
                format!(
                    "{why}\nclaimed {}\ninputs: {}",
                    describe_claims(&forged),
                    inputs.describe()
                ),
            )),
            None => Err(Finding::high(
                format!("{what}: the forged statement is backed, the scenario is wrong"),
                describe_claims(&forged),
            )),
        },
    }
}

fn claim_cells(pk: &[u8; 32], message: &[u8; 32]) -> Vec<F192> {
    [cells_of(pk), cells_of(message)].concat()
}

/// The same 32 bytes as a leanSPHINCS pubkey and a leanXMSS one. A leanSPHINCS signature covers no leanXMSS
/// claim, declared (expect `NotCovered`), nor does a leanXMSS signature of another key verify under those bytes
/// (expect a refused signature).
fn pubkey_in_both_schemes(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let (pk, m, sig) = f.signers.sphincs[src.below(2)].clone();
    let as_xmss = LeanXmssPublicKey::from_bytes(&pk.to_bytes());
    let mut inputs = Inputs::default();
    inputs.sphincs.push((pk, m, sig));
    if src.bool() {
        inputs.declare = Some(EthereumClaims {
            xmss: vec![(as_xmss, m)],
            ..EthereumClaims::default()
        });
        refused(ctx, &inputs, &["NotCovered"])
    } else {
        inputs
            .xmss
            .push((as_xmss, m, f.signers.xmss[src.below(N_XMSS)].2.clone()));
        refused(ctx, &inputs, BAD_SIGNATURE)
    }
}

/// One leanXMSS key signing two messages, only one of its claims declared: the other rides a duplicate slot, and the
/// node publishes exactly the declared claim.
fn one_key_two_messages_declared_once(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs {
        xmss: f.signers.xmss_two[..2].to_vec(),
        ..Inputs::default()
    };
    if src.bool() {
        inputs.xmss.reverse();
    }
    let (pk, m, _) = &f.signers.xmss_two[src.below(2)];
    let want = EthereumClaims {
        xmss: vec![(*pk, *m)],
        ..EthereumClaims::default()
    };
    inputs.declare = Some(want.clone());
    exactly(ctx, &inputs, want)
}

/// One claim under two signatures of one key at different leaf indices: one claim, published once.
fn one_claim_two_signatures(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs {
        xmss: vec![f.signers.xmss_two[0].clone(), f.signers.xmss_two[2].clone()],
        ..Inputs::default()
    };
    if src.bool() {
        inputs.xmss.reverse();
    }
    let (pk, m, _) = &f.signers.xmss_two[0];
    exactly(
        ctx,
        &inputs,
        EthereumClaims {
            xmss: vec![(*pk, *m)],
            ..EthereumClaims::default()
        },
    )
}

/// A child whose claims are a superset of its sibling's: every claim of the smaller lands in a duplicate slot, and
/// the node publishes the superset.
fn child_superset_of_sibling(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let (small, big) = if src.bool() { (X3, NODE) } else { (S2, NODE) };
    let order = if src.bool() { [small, big] } else { [big, small] };
    let inputs = with_children(f, &order);
    exactly(ctx, &inputs, f.claims(NODE).clone())
}

/// The same child twice: its claims once, the copies in duplicate slots.
fn same_child_twice(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = [X3, S2, MIXED, NODE, TWO_MSG][src.below(5)];
    let inputs = with_children(f, &[i, i]);
    exactly(ctx, &inputs, f.claims(i).clone())
}

/// A child's claim re-declared by its parent under another message: nobody signed that, so `NotCovered`.
fn child_claim_redeclared_other_message(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = with_children(f, &[X3]);
    let mut d = f.claims(X3).clone();
    let k = src.below(d.xmss.len());
    d.xmss[k].1 = if src.bool() { message_b() } else { src.array() };
    inputs.declare = Some(d);
    refused(ctx, &inputs, &["NotCovered"])
}

/// A leaf presented as a child with its deferred value forged at the all-zero point: `verify` rejects it as a
/// malformed claim, and the node must not be built over it.
fn leaf_child_forged_deferred_value(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let leaf = [X3, S2, DA, MIXED, X3R2, TWO_MSG][src.below(6)];
    let forged = edited(f, leaf, |p| {
        p.defer_value = if src.bool() {
            p.defer_value + F192::ONE
        } else {
            perturb(p.defer_value, src)
        };
    });
    if forged.deferred() == f.proof(leaf).deferred() {
        return Ok(());
    }
    if !matches!(forged.verify(), Err(AggregateVerifyError::MalformedClaim)) {
        return Err(Finding::critical(
            "verify does not reject a false deferred value",
            format!("{:?}", forged.verify()),
        ));
    }
    reject_child(ctx, CX, Inputs::default(), forged, 0)
}

/// A two-level node presented with a leaf's deferred claim (the all-zero point and its true value): another
/// statement than the one proven.
fn node_child_with_leaf_point(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = if src.bool() { NODE } else { NARROW };
    let forged = edited(f, i, |p| (p.defer_point, p.defer_value) = leaf_deferred());
    reject_child(ctx, CX, Inputs::default(), forged, 0)
}

/// Children proven at different rates, one with the same claims as another: one guest dispatches on each child's
/// rate, and the node publishes the union.
fn children_at_two_rates(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let inputs = if src.bool() {
        with_children(f, &[X3, X3R2])
    } else {
        with_children(f, &[S2, X3R2, X3])
    };
    let want = expect_for(&inputs);
    judge(ctx, CX, &inputs, &want).map(|_| ())
}

/// A node that dropped a claim by `declare`, then a grandparent that re-adds it with no signature: by `declare`
/// (`NotCovered`), or by a child claiming it (rejected).
fn grandparent_readds_dropped_claim(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let dropped_x = f.claims(MIXED).xmss[0];
    let dropped_s = f.claims(MIXED).lean_sphincs[0];
    let mut readded = f.claims(NARROW).clone();
    if src.bool() {
        readded.xmss.push(dropped_x);
    } else {
        readded.lean_sphincs.push(dropped_s);
    }
    super::fixtures::normalize(&mut readded);
    if src.bool() {
        let mut inputs = with_children(f, &[NARROW]);
        inputs.declare = Some(readded);
        refused(ctx, &inputs, &["NotCovered"])
    } else {
        let forged = edited(f, NARROW, |p| p.claims = readded);
        reject_child(ctx, CX, Inputs::default(), forged, 0)
    }
}

/// A DA root from the second child while the first holds another: the node publishes the one declared, and a
/// witness that picks the other child's root for the same statement is refused.
fn da_root_of_second_child(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = with_children(f, &[DA, MIXED]);
    let mut want = f.claims(MIXED).clone();
    want.da_commitment = f.claims(MIXED).da_commitment;
    inputs.declare = Some(want.clone());
    if src.bool() {
        exactly(ctx, &inputs, want)
    } else {
        forgery_refused(ctx, &inputs, "da_pick of the other child", |s| {
            if let Some(i) = index_of(s, "da_pick") {
                s[i].1[0][0] = count(0);
            }
        })
    }
}

/// A node with blobs declaring no DA root: their matrix's root is what it must publish, `BlobsUnpublished`.
fn blobs_declaring_no_root(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    // Not the `da` fixture's blobs, whose root a declaration naming that child's would be.
    let mut inputs = Inputs {
        blobs: f.blobs[1 + src.below(2)].clone(),
        ..Inputs::default()
    };
    inputs.xmss.push(f.signers.xmss[0].clone());
    let mut d = super::fixtures::claims_of(&inputs.xmss, &[], None);
    if src.bool() {
        inputs.child(f, DA);
        d.da_commitment = if src.bool() { None } else { f.claims(DA).da_commitment };
    }
    inputs.declare = Some(d);
    refused(ctx, &inputs, &["BlobsUnpublished"])
}

/// A child claiming `MAX_KEYS - 1` claims over a real proof of three: inside the signer-set bound, so only the proof
/// can refuse it. One more is `MalformedSignerSet` at decoding already.
fn child_at_max_keys_minus_one(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    if src.bool() {
        let claims = EthereumClaims {
            xmss: synthetic_claims(MAX_KEYS),
            ..EthereumClaims::default()
        };
        return match EthereumProof::from_proof_bytes(&f.proof(X3).proof_bytes(), claims) {
            Err(AggregateVerifyError::MalformedSignerSet) => {
                ctx.note("MAX_KEYS claims: MalformedSignerSet");
                Ok(())
            }
            other => Err(Finding::high(
                "MAX_KEYS claims decode",
                format!("{:?}", other.map(|_| ())),
            )),
        };
    }
    let forged = edited(f, X3, |p| {
        p.claims = EthereumClaims {
            xmss: synthetic_claims(MAX_KEYS - 1),
            ..EthereumClaims::default()
        }
    });
    reject_child(ctx, CX, Inputs::default(), forged, 0)
}

/// A child whose proof bytes are another child's, under these claims.
fn other_childs_proof_bytes(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let (from, claims) = [
        (S2, X3),
        (X3, X3R2),
        (X3R2, X3),
        (MIXED, NARROW),
        (NARROW, MIXED),
        (NODE, X3),
    ][src.below(6)];
    // `x3r2` proves `x3`'s claims at another rate: one's bytes under the other's claims are an honest statement.
    if f.claims(claims) == f.proof(from).claims() {
        ctx.note("other child's bytes: the same statement");
        return Ok(());
    }
    let child = EthereumProof::from_proof_bytes(&f.proof(from).proof_bytes(), f.claims(claims).clone())
        .map_err(|e| Finding::high("a fixture's bytes do not decode", format!("{e:?}")))?;
    let mut sibling = Inputs::default();
    if src.bool() {
        sibling.child(f, claims);
    }
    reject_child(ctx, CX, sibling, child, src.below(2))
}

/// Two children with their deferred claims swapped: each its own statement no longer.
fn swapped_deferred_claims(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let (a, b) = [(X3, NODE), (NODE, NARROW), (X3, S2), (MIXED, NODE)][src.below(4)];
    let da = f.proof(a).deferred();
    let db = f.proof(b).deferred();
    let (pa, va, pb, vb) = (da.0.to_vec(), da.1, db.0.to_vec(), db.1);
    let fa = edited(f, a, |p| (p.defer_point, p.defer_value) = (pb, vb));
    let fb = edited(f, b, |p| (p.defer_point, p.defer_value) = (pa, va));
    if fa.deferred() == f.proof(a).deferred() {
        ctx.note("two leaves defer the same claim");
        return Ok(());
    }
    if fb.verify().is_ok() {
        return Err(Finding::critical(
            "verify accepts a swapped deferred claim",
            String::new(),
        ));
    }
    let mut inputs = Inputs::default();
    inputs.forged_child(fb, "swapped");
    reject_child(ctx, CX, inputs, fa, src.below(2))
}

/// No raw signatures and one child without DA: its claims and no root.
fn dataless_child_only(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = [X3, S2, NODE, TWO_MSG][src.below(4)];
    let inputs = with_children(f, &[i]);
    exactly(ctx, &inputs, f.claims(i).clone())
}

/// The root's deferred claim discharged with a forged value, or at another point with the true value there:
/// `verify` must reject both, and accept the honest one off the wire.
fn root_forged_deferred_value(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = [NODE, NARROW, X3][src.below(3)];
    let honest = f.proof(i);
    let received = EthereumProof::from_proof_bytes(&honest.proof_bytes(), honest.claims().clone())
        .map_err(|e| Finding::high("a fixture does not decode", format!("{e:?}")))?;
    if let Err(e) = received.verify() {
        return Err(Finding::high(
            "an honest root does not verify off the wire",
            format!("{e:?}"),
        ));
    }
    let forged = edited(f, i, |p| {
        if src.bool() {
            p.defer_value = perturb(p.defer_value, src);
        } else {
            let k = src.below(p.defer_point.len());
            p.defer_point[k] = perturb(p.defer_point[k], src);
            if let Some(v) = true_deferred_value(&p.defer_point) {
                p.defer_value = v;
            }
        }
    });
    if forged.deferred() == honest.deferred() {
        return Ok(());
    }
    match forged.verify() {
        Ok(()) => Err(Finding::critical(
            "verify accepts a root whose deferred claim was forged",
            format!("fixture {}", f.children[i].name),
        )),
        Err(e) => {
            ctx.note(format!("root defer {}", super::common::verify_kind(&e)));
            Ok(())
        }
    }
}

/// A leanXMSS claim of a child declared in the leanSPHINCS list: `NotCovered`.
fn xmss_claim_declared_as_sphincs(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = with_children(f, &[X3]);
    let mut d = f.claims(X3).clone();
    let (pk, m) = d.xmss.remove(src.below(d.xmss.len()));
    d.lean_sphincs
        .push((LeanSphincsPublicKey::from_bytes(&pk.to_bytes()), m));
    inputs.declare = Some(d);
    refused(ctx, &inputs, &["NotCovered"])
}

/// A child presenting one of its leanXMSS claims as leanSPHINCS, or the other way.
fn child_claim_moved_to_other_scheme(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = [X3, MIXED, NODE][src.below(3)];
    let to_sphincs = src.bool();
    let k = src.u8() as usize;
    let forged = edited(f, i, |p| {
        let c = &mut p.claims;
        if to_sphincs || c.lean_sphincs.is_empty() {
            let (pk, m) = c.xmss.remove(k % c.xmss.len());
            c.lean_sphincs
                .push((LeanSphincsPublicKey::from_bytes(&pk.to_bytes()), m));
        } else {
            let (pk, m) = c.lean_sphincs.remove(k % c.lean_sphincs.len());
            c.xmss.push((LeanXmssPublicKey::from_bytes(&pk.to_bytes()), m));
        }
        super::fixtures::normalize(c);
    });
    reject_child(ctx, CX, Inputs::default(), forged, 0)
}

/// A child claiming one claim fewer than proven.
fn child_claim_dropped(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = [X3, S2, MIXED, NODE, TWO_MSG, NARROW][src.below(6)];
    let k = src.u8() as usize;
    let forged = edited(f, i, |p| {
        let c = &mut p.claims;
        let n = c.num_signature_claims();
        let k = k % n;
        if k < c.xmss.len() {
            c.xmss.remove(k);
        } else {
            c.lean_sphincs.remove(k - c.xmss.len());
        }
    });
    reject_child(ctx, CX, Inputs::default(), forged, 0)
}

/// A child claiming one more claim than proven, a real signer's.
fn child_claim_added(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = [X3, S2, DA, MIXED, NODE][src.below(5)];
    let (pk, m, _) = f.signers.xmss[5 + src.below(3)].clone();
    let forged = edited(f, i, |p| {
        p.claims.xmss.push((pk, m));
        super::fixtures::normalize(&mut p.claims);
    });
    let mut inputs = Inputs::default();
    if src.bool() {
        // The added claim is also signed raw: the forged child's other claims are what nothing backs.
        inputs.xmss.push(f.signers.xmss[5].clone());
    }
    reject_child(ctx, CX, inputs, forged, 0)
}

/// A declaration of nothing: `Empty`, even with children or a DA child whose root goes undeclared.
fn empty_declaration(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = with_children(f, &[[X3, DA, MIXED][src.below(3)]]);
    inputs.declare = Some(EthereumClaims::default());
    refused(ctx, &inputs, &["Empty"])
}

/// Raw signatures whose claims a child carries too: published once.
fn raw_repeats_child_claim(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = with_children(f, &[X3]);
    for k in 0..3 {
        if src.bool() {
            inputs.xmss.push(f.signers.xmss[k].clone());
        }
    }
    if inputs.xmss.is_empty() {
        inputs.xmss.push(f.signers.xmss[2].clone());
    }
    exactly(ctx, &inputs, f.claims(X3).clone())
}

/// An invalid raw signature whose claim is left undeclared: it still takes a slot, so its verification still runs,
/// and the node is refused (acceptance would publish nothing false, and is Low).
fn invalid_undeclared_raw_signature(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs::default();
    inputs.xmss.push(f.signers.xmss[0].clone());
    let (pk, m, sig) = f.signers.xmss[1].clone();
    let mut bytes = sig.to_bytes();
    let at = src.below(bytes.len());
    bytes[at] ^= 1 << src.below(8);
    let bad = LeanXmssSignature::from_bytes(&bytes);
    if signatures::lean_xmss::verify(&pk, &m, &bad).is_ok() {
        return Ok(());
    }
    inputs.xmss.push((pk, m, bad));
    inputs.declare = Some(super::fixtures::claims_of(&inputs.xmss[..1], &[], None));
    refused(ctx, &inputs, BAD_SIGNATURE)
}

/// `MAX_RECURSIONS` children, every fixture among them: the union. One more: `TooLarge`.
fn sixteen_children(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs::default();
    for k in 0..MAX_RECURSIONS {
        inputs.child(f, (k + src.below(2)) % f.children.len());
    }
    if src.chance(1, 3) {
        inputs.child(f, X3);
        return refused(ctx, &inputs, &["TooLarge"]);
    }
    let want = expect_for(&inputs);
    judge(ctx, CX, &inputs, &want).map(|_| ())
}

/// A child presenting a DA root it does not hold, with a parent publishing that root.
fn child_with_other_da_root(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = [DA, MIXED, X3][src.below(3)];
    let root = root_of(&f.blobs[2]);
    let forged = edited(f, i, |p| p.claims.da_commitment = Some(root));
    let mut inputs = Inputs::default();
    if src.bool() {
        let mut d = forged.claims().clone();
        d.da_commitment = Some(root);
        inputs.declare = Some(d);
    }
    reject_child(ctx, CX, inputs, forged, 0)
}

/// A node with blobs over children with roots of their own: it publishes its blobs' root, and asked for a child's
/// it refuses, `BlobsUnpublished`.
fn blob_node_over_blob_children(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = with_children(f, &[DA, MIXED]);
    inputs.blobs = f.blobs[2].clone();
    if src.bool() {
        let mut want = union(f.claims(DA), f.claims(MIXED));
        want.da_commitment = Some(root_of(&f.blobs[2]));
        exactly(ctx, &inputs, want)
    } else {
        let mut d = f.claims(MIXED).clone();
        d.da_commitment = f.claims([DA, MIXED][src.below(2)]).da_commitment;
        inputs.declare = Some(d);
        refused(ctx, &inputs, &["BlobsUnpublished"])
    }
}

/// A declaration naming claims twice and out of order: a set, published sorted.
fn declared_list_with_repeats(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = with_children(f, &[X3, S2]);
    let want = f.claims(NODE).clone();
    let mut d = want.clone();
    d.xmss.reverse();
    d.xmss.push(d.xmss[src.below(d.xmss.len())]);
    d.lean_sphincs
        .insert(0, d.lean_sphincs[src.below(d.lean_sphincs.len())]);
    inputs.declare = Some(d);
    exactly(ctx, &inputs, want)
}

/// The claims stream names another real signer than the one whose signature covers the slot: the node would claim
/// a pubkey (one that signed the same message elsewhere) that signed nothing here.
fn claim_of_another_signer_by_hint(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs {
        xmss: f.signers.xmss[..2].to_vec(),
        ..Inputs::default()
    };
    if src.bool() {
        inputs.child(f, S2);
    }
    let k = src.below(2);
    let other = f.signers.xmss[6].0;
    let declared: Vec<_> = super::fixtures::claims_of(&inputs.xmss, &[], None).xmss;
    let (pk, m) = declared[k];
    let replace = claim_cells(&other.to_bytes(), &m);
    let original = claim_cells(&pk.to_bytes(), &m);
    statement_refused(
        ctx,
        &inputs,
        "a declared claim swapped for another signer's",
        move |s| {
            if let Some(c) = index_of(s, "claims")
                && let Some(e) = s[c].1.iter_mut().find(|e| **e == original)
            {
                *e = replace;
            }
        },
        move |honest| {
            let mut c = honest.clone();
            c.xmss[k].0 = other;
            c
        },
    )
}

/// A leanSPHINCS signature's claim published as leanXMSS by moving the boundary between the regions: the counts
/// and splits say one leanXMSS claim, the slot stays where the signature covers it.
fn sphincs_signature_published_as_xmss(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs::default();
    inputs.sphincs.push(f.signers.sphincs[src.below(2)].clone());
    let with_xmss = src.bool();
    if with_xmss {
        inputs.xmss.push(f.signers.xmss[0].clone());
    }
    let n_lx = usize::from(with_xmss);
    statement_refused(
        ctx,
        &inputs,
        "the leanSPHINCS claim moved into the leanXMSS list",
        move |s| {
            if let Some(m) = index_of(s, "meta") {
                s[m].1[0][0] *= count(1);
                s[m].1[0][3] *= count_inv(1);
            }
            resplit(s, n_lx, 1, n_lx + 1, 0);
        },
        |honest| {
            let mut c = honest.clone();
            let (pk, m) = c.lean_sphincs.remove(0);
            c.xmss.push((LeanXmssPublicKey::from_bytes(&pk.to_bytes()), m));
            c
        },
    )
}

/// A duplicate slot made a declared claim nobody signed: its writer (a child's copy of a claim) now covers the new
/// claim, and the duplicate count drops by one to keep the table's size.
fn dup_slot_promoted_to_foreign_claim(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let inputs = with_children(f, &[X3, [X3R2, X3][src.below(2)]]);
    let n = f.claims(X3).xmss.len();
    let mut foreign_pk = f.claims(X3).xmss[0].0.to_bytes();
    foreign_pk[src.below(32)] ^= 1 << src.below(8);
    let m = f.claims(X3).xmss[0].1;
    let foreign = claim_cells(&foreign_pk, &m);
    statement_refused(
        ctx,
        &inputs,
        "a duplicate slot promoted to a foreign declared claim",
        move |s| {
            if let (Some(meta), Some(c), Some(d)) =
                (index_of(s, "meta"), index_of(s, "claims"), index_of(s, "dup_claims"))
            {
                s[d].1.remove(0);
                s[c].1.insert(n, foreign);
                s[meta].1[0][0] *= count(1);
                s[meta].1[0][1] *= count_inv(1);
            }
            resplit(s, n, 0, n + 1, 0);
        },
        move |honest| {
            let mut c = honest.clone();
            c.xmss.push((LeanXmssPublicKey::from_bytes(&foreign_pk), m));
            c
        },
    )
}

/// A raw leanXMSS signature's slot index pointing into the leanSPHINCS region, at the claim there: the range check
/// on the leanXMSS region must refuse it.
fn raw_index_into_other_region(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs::default();
    inputs.xmss.push(f.signers.xmss[0].clone());
    inputs.sphincs.push(f.signers.sphincs[0].clone());
    let shift = src.range(1, 2);
    if src.bool() {
        forgery_refused(ctx, &inputs, "raw_index into the leanSPHINCS region", move |s| {
            if let Some(i) = index_of(s, "raw_index") {
                s[i].1[0][0] *= count(shift);
            }
        })
    } else {
        forgery_refused(ctx, &inputs, "sp_raw_index below the leanSPHINCS region", move |s| {
            if let Some(i) = index_of(s, "sp_raw_index") {
                s[i].1[0][0] *= count_inv(1);
            }
        })
    }
}

/// A child's claim walk stepping past its scheme's region into the other's.
fn child_walk_into_other_region(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let inputs = with_children(f, &[[MIXED, NODE][src.below(2)]]);
    let n_x = inputs.children[0].claims().xmss.len();
    let at = src.below(n_x);
    forgery_refused(ctx, &inputs, "a child's gap walk past its region", move |s| {
        if let Some(i) = index_of(s, "child_claim_gap")
            && let Some(e) = s[i].1.get_mut(at)
        {
            e[0] *= count(n_x);
        }
    })
}

/// A child's wire bytes truncated or extended: `MalformedEncoding`, never a different aggregate.
fn child_wire_tampering(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = src.below(f.children.len());
    let mut bytes = f.proof(i).proof_bytes();
    if src.bool() {
        bytes.truncate(src.below(bytes.len()));
    } else {
        let n = src.range(1, 16);
        bytes.extend(src.bytes(n));
    }
    match EthereumProof::from_proof_bytes(&bytes, f.claims(i).clone()) {
        Err(AggregateVerifyError::MalformedEncoding) => {
            ctx.note("wire: MalformedEncoding");
            Ok(())
        }
        Err(e) => Err(Finding::low(
            "tampered wire bytes refused as another error",
            format!("{e:?}"),
        )),
        Ok(child) => {
            if child.verify().is_ok() {
                return Err(Finding::critical(
                    "tampered wire bytes verify",
                    format!("fixture {}", f.children[i].name),
                ));
            }
            reject_child(ctx, CX, Inputs::default(), child, 0)
        }
    }
}

/// A DA root declared that only a child not given carries: `BlobNotCovered`.
fn da_root_without_child(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = with_children(f, &[[X3, S2, NODE][src.below(3)]]);
    let mut d = inputs.children[0].claims().clone();
    d.da_commitment = f.claims([DA, MIXED][src.below(2)]).da_commitment;
    inputs.declare = Some(d);
    refused(ctx, &inputs, &["BlobNotCovered"])
}

/// A leaf that lies about its deferred value. The guest checks a leaf's value nowhere (`leaf_defer`: the outer
/// verifier recomputes it), so the run is accepted and proven; `verify` must then reject the aggregate as a
/// malformed claim, and a parent must not be built over it.
fn leaf_lies_about_deferred_value(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut inputs = Inputs::default();
    inputs.xmss.push(f.signers.xmss[src.below(N_XMSS)].clone());
    let (point, value) = leaf_deferred();
    let lie = value + F192::ONE;
    arm_forgery(Box::new(move |hints| {
        let s = hints.streams_mut();
        if let Some(i) = index_of(s, "leaf_defer") {
            s[i].1[0][0] = lie;
        }
    }));
    let node = prepare_node(
        &inputs.children,
        inputs.xmss.clone(),
        inputs.sphincs.clone(),
        &inputs.blobs,
        None,
    );
    disarm_forgery();
    let node = node.map_err(|e| Finding::high("a one-signature leaf is not built", format!("{e:?}")))?;
    let pi = statement_of(&node.claims, &point, lie);
    if let Err(e) = run_guest(&node.program, pi) {
        ctx.note(format!("lying leaf refused {}", refusal_kind(&e)));
        return Ok(());
    }
    let rate = src.range(1, 2);
    let (proof, _) = leanvm_core::cpu::prove(&node.program, pi, rate)
        .map_err(|e| Finding::high("an accepted run is not proven", format!("{e:?}")))?;
    let evil = EthereumProof::from_parts(Parts {
        claims: node.claims.clone(),
        defer_point: point,
        defer_value: lie,
        proof,
    });
    match evil.verify() {
        Err(AggregateVerifyError::MalformedClaim) => {}
        other => {
            return Err(Finding::critical(
                "a leaf proven with a false deferred value is not refused as a malformed claim",
                format!("verify: {other:?}"),
            ));
        }
    }
    reject_child(ctx, CX, Inputs::default(), evil, 0)
}

/// A child whose two claims of one key are made one claim twice: not a set, refused before anything is read
/// (`MalformedSignerSet`), by `verify` and by the node.
fn child_claims_collapsed_to_a_repeat(f: &Fixtures, src: &mut Source, ctx: &Ctx) -> Outcome {
    let i = [TWO_MSG, X3, NODE][src.below(3)];
    let forged = edited(f, i, |p| {
        let c = &mut p.claims;
        c.xmss[1] = c.xmss[0];
    });
    if !matches!(forged.verify(), Err(AggregateVerifyError::MalformedSignerSet)) {
        return Err(Finding::high(
            "a repeated claim is not a malformed signer set",
            format!("{:?}", forged.verify()),
        ));
    }
    let mut inputs = Inputs::default();
    inputs.forged_child(forged, "repeat");
    refused(ctx, &inputs, &["InvalidChild/MalformedSignerSet"])
}
