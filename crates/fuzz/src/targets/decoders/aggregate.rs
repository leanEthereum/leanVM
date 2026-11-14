//! `decode-aggregate`: `EthereumProof::from_proof_bytes` on bytes built by structure (the deferred point's count and
//! limbs, then a VM proof's encoding) and mutated, under adversarial claims (unsorted, duplicated, at and past
//! `MAX_KEYS`, both schemes, with and without a DA root).
//!
//! Oracles: no panic; the decision is the documented one (an encoding that does not parse, a signer set that is not
//! strictly sorted or too large, a point of the wrong length are refused, anything else decodes); a decoded aggregate
//! re-encodes to its input and carries the claims it was given; `verify` never panics and never accepts, since the VM
//! proof inside is never one of the guest. Rarely, the deferred claim's two evaluations (the prover's pooled kernel and
//! the verifier's bucketed scalar walk) are compared on the guest's 2^23-word stacked bytecode.

use super::honest;
use crate::source::{Rng, mutate};
use crate::{Ctx, Finding, Outcome, Source, catch};
use primitives::field::{F64, F128};
use rec_aggregation::aggregation::unified_guest;
use crate::MAX_KEYS;
use rec_aggregation::{AggregateVerifyError, EthereumClaims, EthereumProof, fuzzing};
use signatures::{lean_sphincs, lean_xmss};
use std::sync::OnceLock;

/// The deferred point's length, which compiling the guest fixes.
fn vars() -> usize {
    static VARS: OnceLock<usize> = OnceLock::new();
    *VARS.get_or_init(|| fuzzing::leaf_deferred().0.len())
}

/// The guest's stacked bytecode, as the prover's kernels read it.
fn stacked() -> &'static [F64] {
    static TABLE: OnceLock<Vec<F64>> = OnceLock::new();
    TABLE.get_or_init(|| leanvm_core::cpu::layout::bytecode_table(unified_guest().prog()))
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Expect {
    Encoding,
    SignerSet,
    Claim,
    Ok,
}

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let n = vars();
    if src.chance(1, 64) || (ctx.depth >= 2 && src.chance(1, 8)) {
        deferred_agree(src, ctx, n)?;
    }
    let claims = claims(src, ctx);
    let valid_set =
        claims.lean_xmss.windows(2).all(|w| w[0] < w[1]) && claims.lean_sphincs.windows(2).all(|w| w[0] < w[1]);

    // The point: its announced count, then its limbs.
    let (count, point) = match src.below(10) {
        0 => {
            ctx.note("count off by one");
            let c = if src.bool() { n + 1 } else { n.saturating_sub(1) };
            (c as u64, vec![F128::ZERO; c])
        }
        1 => {
            ctx.note("count edge");
            let c = *src.pick(&[0u64, u64::MAX, u64::MAX / 24 + 1, 1 << 61, u32::MAX as u64]);
            (c, Vec::new())
        }
        2 if src.chance(1, 4) => {
            ctx.note("random point");
            (n as u64, (0..n).map(|_| src.f128()).collect())
        }
        3 => {
            ctx.note("boolean point");
            (n as u64, (0..n).map(|_| F128::new(src.below(2) as u64, 0)).collect())
        }
        _ => {
            ctx.note("zero point");
            (n as u64, vec![F128::ZERO; n])
        }
    };
    let fixtures = honest();
    let vm: Vec<u8> = match src.below(5) {
        0 | 1 if !fixtures.is_empty() => fixtures[src.below(fixtures.len())].bytes.clone(),
        2 => {
            let len = src.below(200);
            src.bulk(len)
        }
        3 => Vec::new(),
        _ => leanvm_core::cpu::Proof {
            stream: (0..src.below(16)).map(|_| src.f128()).collect(),
            merkle: Vec::new(),
        }
        .to_bytes(),
    };
    let mut bytes = count.to_le_bytes().to_vec();
    bytes.extend(point.iter().flat_map(|x| x.to_limbs()).flat_map(u64::to_le_bytes));
    bytes.extend(&vm);
    if src.chance(1, 4) {
        ctx.note("havoc");
        let mut rng = Rng::new(src.u64());
        bytes = mutate(&bytes, &mut rng, None);
    }

    // What the documentation says the decoder decides.
    let expect = {
        let header = bytes.get(..8).map(|h| u64::from_le_bytes(h.try_into().unwrap()));
        let body = header
            .and_then(|c| usize::try_from(c).ok()?.checked_mul(24))
            .filter(|&l| l <= bytes.len() - 8);
        match body {
            None => Expect::Encoding,
            Some(_) if !valid_set => Expect::SignerSet,
            Some(l) if leanvm_core::cpu::Proof::from_bytes(&bytes[8 + l..]).is_none() => Expect::Encoding,
            Some(l) if l / 24 != n => Expect::Claim,
            Some(_) => Expect::Ok,
        }
    };
    let decoded = catch(|| EthereumProof::from_proof_bytes(&bytes, claims.clone()))
        .map_err(|(m, l)| Finding::panic(&m, &l).in_context("EthereumProof::from_proof_bytes"))?;
    let got = match &decoded {
        Ok(_) => Expect::Ok,
        Err(AggregateVerifyError::MalformedEncoding) => Expect::Encoding,
        Err(AggregateVerifyError::MalformedSignerSet) => Expect::SignerSet,
        Err(AggregateVerifyError::MalformedClaim) => Expect::Claim,
        Err(AggregateVerifyError::Snark(_)) => {
            return Err(Finding::medium(
                "EthereumProof::from_proof_bytes ran the SNARK verifier",
                "parsing is documented not to verify",
            ));
        }
    };
    ctx.note(format!("decode {got:?}"));
    if (got == Expect::Ok) != (expect == Expect::Ok) {
        return Err(Finding::high(
            format!("EthereumProof::from_proof_bytes decided {got:?}, the format says {expect:?}"),
            format!(
                "{} bytes, {} leanXMSS and {} leanSPHINCS claims, sorted set {valid_set}",
                bytes.len(),
                claims.lean_xmss.len(),
                claims.lean_sphincs.len()
            ),
        ));
    }
    if got != expect {
        // Both refusals: which check fired first is not part of the contract, only that one did.
        ctx.note(format!("refused as {got:?}, expected {expect:?}"));
    }
    let Ok(proof) = decoded else { return Ok(()) };
    let again = catch(|| proof.proof_bytes())
        .map_err(|(m, l)| Finding::panic(&m, &l).in_context("EthereumProof::proof_bytes"))?;
    if again != bytes {
        return Err(Finding::high(
            "EthereumProof::from_proof_bytes accepted a non-canonical encoding",
            format!("{} bytes in, {} bytes back", bytes.len(), again.len()),
        ));
    }
    if *proof.claims() != claims {
        return Err(Finding::high(
            "a decoded aggregate carries other claims than it was given",
            "",
        ));
    }
    let verdict =
        catch(|| proof.verify()).map_err(|(m, l)| Finding::panic(&m, &l).in_context("EthereumProof::verify"))?;
    match verdict {
        Ok(()) => Err(Finding::critical(
            "EthereumProof::verify accepted an aggregate whose VM proof is not the guest's",
            format!(
                "{} bytes, claims {} + {}",
                bytes.len(),
                claims.lean_xmss.len(),
                claims.lean_sphincs.len()
            ),
        )),
        Err(e) => {
            ctx.note(format!(
                "verify refused {}",
                format!("{e:?}").split('(').next().unwrap_or("")
            ));
            Ok(())
        }
    }
}

fn bytes32(rng: &mut Rng) -> [u8; 32] {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    b
}

fn claims(src: &mut Source, ctx: &Ctx) -> EthereumClaims {
    let size = |src: &mut Source| match src.below(16) {
        0 => MAX_KEYS - 1 - src.below(2),
        1 => MAX_KEYS + src.below(2),
        2..=5 => 0,
        _ => src.below(6),
    };
    let (nx, ns) = (size(src), size(src));
    let (nx, ns) = if nx + ns > MAX_KEYS + 1 { (nx, 0) } else { (nx, ns) };
    let shape = src.below(6);
    ctx.note(format!(
        "claims shape {shape} {}",
        if nx + ns >= MAX_KEYS - 2 { "huge" } else { "small" }
    ));
    let mut rng = Rng::new(src.u64());
    let mut lean_xmss: Vec<_> = (0..nx)
        .map(|_| {
            (
                lean_xmss::LeanXmssPublicKey::from_bytes(&bytes32(&mut rng)),
                bytes32(&mut rng),
            )
        })
        .collect();
    let mut sphincs: Vec<_> = (0..ns)
        .map(|_| {
            (
                lean_sphincs::LeanSphincsPublicKey::from_bytes(&bytes32(&mut rng)),
                bytes32(&mut rng),
            )
        })
        .collect();
    match shape {
        0 => {}
        1 if lean_xmss.len() > 1 => {
            lean_xmss.sort();
            let i = src.below(lean_xmss.len() - 1);
            lean_xmss[i + 1] = lean_xmss[i];
        }
        2 if sphincs.len() > 1 => {
            sphincs.sort();
            let i = src.below(sphincs.len() - 1);
            // One key under two messages is fine; the same pair twice is not.
            sphincs[i + 1].0 = sphincs[i].0;
            if src.bool() {
                sphincs[i + 1].1 = sphincs[i].1;
            }
            sphincs.sort();
        }
        3 if lean_xmss.len() > 1 => {
            lean_xmss.sort();
            lean_xmss.reverse();
        }
        _ => {
            lean_xmss.sort();
            lean_xmss.dedup();
            sphincs.sort();
            sphincs.dedup();
        }
    }
    let da_commitment = src.bool().then(|| bytes32(&mut rng));
    EthereumClaims {
        lean_xmss,
        lean_sphincs: sphincs,
        da_commitment,
    }
}

/// The deferred claim evaluated by the prover's pooled MLE kernel and by the verifier's scalar walk must agree, or
/// every honest aggregate at that point fails.
fn deferred_agree(src: &mut Source, ctx: &Ctx, n: usize) -> Outcome {
    ctx.note("deferred agree");
    let point: Vec<F128> = match src.below(3) {
        0 => (0..n).map(|_| src.f128()).collect(),
        1 => (0..n).map(|_| F128::new(src.below(2) as u64, 0)).collect(),
        _ => (0..n).map(|_| *src.pick(&[F128::ZERO, F128::ONE, F128::Y])).collect(),
    };
    let scalar = fuzzing::true_deferred_value(&point);
    let pooled = primitives::multilinear::mle_eval_par(stacked(), &point);
    if scalar != Some(pooled) {
        return Err(Finding::high(
            "the deferred bytecode claim differs between the prover's and the verifier's evaluation",
            format!("verifier {scalar:?}, prover {pooled:?}"),
        ));
    }
    Ok(())
}
