//! Coverage: which slot each raw signature takes, and the multiset commitments the guest draws its challenges from.

use super::cells::count;
use super::error::AggregateError;
use super::proof::AggregateProof;
use super::statement::{claim_list_digest, lean_sphincs_claim_cells, lean_xmss_claim_cells};
use super::{AggregateClaims, LeanSphincsClaim, LeanXmssClaim};
use fiat_shamir_prover::{FiatShamirState, Sequential, grinding_bits};
use primitives::field::F128;
use std::collections::BTreeSet;

/// The coverage transcript's label (the guest's `CLAIMS_SEED`).
pub(super) const CLAIMS_LABEL: &[u8] = b"leanvm/recursion-claims/v1";

/// Each scheme's slots: its declared claims, then its duplicate slots, which the guest proves are, with multiplicity,
/// the claims of the raw signatures and the children's lists (`main`'s multiset identity).
///
/// A claim the declared set holds takes its slot there, one it does not takes a fresh duplicate slot, so every slot
/// is one source's. A raw signature names its slot, the slot it is verified against; a child's list is its own.
pub(super) struct Coverage {
    pub(super) lean_xmss: Region<LeanXmssClaim>,
    pub(super) lean_sphincs: Region<LeanSphincsClaim>,
}

/// One scheme's slots.
pub(super) struct Region<K> {
    /// The declared claims, strictly sorted.
    pub(super) signers: Vec<K>,
    pub(super) dups: Vec<K>,
    /// The slot of each raw signature, in the order given.
    pub(super) raw: Vec<usize>,
}

impl<K: Ord + Clone> Region<K> {
    /// Declares the union of the raw claims and the children's, or exactly
    /// `declare`, which they must cover.
    fn plan<'a>(
        raw: &[K],
        children: impl Iterator<Item = &'a [K]> + Clone,
        declare: Option<&[K]>,
    ) -> Result<Self, AggregateError>
    where
        K: 'a,
    {
        let mut signers = raw.to_vec();
        for child in children.clone() {
            signers.extend_from_slice(child);
        }
        signers.sort();
        signers.dedup();
        if let Some(declare) = declare {
            let mut wanted: BTreeSet<&K> = declare.iter().collect();
            signers.retain(|claim| wanted.remove(claim));
            if !wanted.is_empty() {
                return Err(AggregateError::InvalidInput(
                    "a requested claim is not covered by the inputs",
                ));
            }
        }
        let mut claimed = vec![false; signers.len()];
        let mut dups = Vec::new();
        let raw = raw
            .iter()
            .map(|claim| take_slot(&signers, &mut claimed, &mut dups, claim))
            .collect();
        for claim in children.flatten() {
            take_slot(&signers, &mut claimed, &mut dups, claim);
        }
        Ok(Self { signers, dups, raw })
    }

    fn slots(&self) -> usize {
        self.signers.len() + self.dups.len()
    }
}

/// A claim takes its declared slot once; subsequent or omitted occurrences take
/// fresh slots outside the hashed prefix.
fn take_slot<K: Ord + Clone>(claims: &[K], claimed: &mut [bool], duplicates: &mut Vec<K>, claim: &K) -> usize {
    match claims.binary_search(claim) {
        Ok(pos) if !claimed[pos] => {
            claimed[pos] = true;
            pos
        }
        _ => {
            duplicates.push(claim.clone());
            claims.len() + duplicates.len() - 1
        }
    }
}

/// What the guest's coverage transcript observes, in groups of four cells: the two declared digests, the two
/// duplicate digests, each child's two list digests, then each scheme's raw slots, padded with zeros to whole groups.
/// Returns the groups, the raw slots' group counts, and the transcript's grinding nonce, if it grinds.
pub(super) fn claim_commitments(
    cover: &Coverage,
    children: &[(AggregateClaims, AggregateProof)],
) -> (Vec<[F128; 4]>, [usize; 2], Option<u64>) {
    let x = &cover.lean_xmss;
    let s = &cover.lean_sphincs;
    let pair = |a: [F128; 2], b: [F128; 2]| [a[0], a[1], b[0], b[1]];
    let mut groups = vec![
        pair(
            claim_list_digest(x.signers.iter().map(lean_xmss_claim_cells)),
            claim_list_digest(s.signers.iter().map(lean_sphincs_claim_cells)),
        ),
        pair(
            claim_list_digest(x.dups.iter().map(lean_xmss_claim_cells)),
            claim_list_digest(s.dups.iter().map(lean_sphincs_claim_cells)),
        ),
    ];
    for (claims, _) in children {
        groups.push(pair(
            claim_list_digest(claims.lean_xmss.iter().map(lean_xmss_claim_cells)),
            claim_list_digest(claims.lean_sphincs.iter().map(lean_sphincs_claim_cells)),
        ));
    }
    let raw_groups = [x.raw.len().div_ceil(4), s.raw.len().div_ceil(4)];
    for raw in [&x.raw, &s.raw] {
        for chunk in raw.chunks(4) {
            let mut group = [F128::ZERO; 4];
            for (cell, &slot) in group.iter_mut().zip(chunk) {
                *cell = count(slot);
            }
            groups.push(group);
        }
    }
    let mut transcript = FiatShamirState::<F128>::from_label(CLAIMS_LABEL);
    for &cell in groups.iter().flatten() {
        transcript.observe(cell);
    }
    // Both products have n_total factors, the slots of both schemes.
    let factors = 2 * (x.slots() + s.slots()) as u128;
    let nonce = transcript.grind::<Sequential>(grinding_bits(factors));
    (groups, raw_groups, nonce)
}

pub(super) fn plan_coverage(
    raw_lean_xmss: &[LeanXmssClaim],
    raw_lean_sphincs: &[LeanSphincsClaim],
    children: &[(AggregateClaims, AggregateProof)],
    declare: Option<&AggregateClaims>,
) -> Result<Coverage, AggregateError> {
    Ok(Coverage {
        lean_xmss: Region::plan(
            raw_lean_xmss,
            children.iter().map(|(claims, _)| claims.lean_xmss.as_slice()),
            declare.map(|claims| claims.lean_xmss.as_slice()),
        )?,
        lean_sphincs: Region::plan(
            raw_lean_sphincs,
            children.iter().map(|(claims, _)| claims.lean_sphincs.as_slice()),
            declare.map(|claims| claims.lean_sphincs.as_slice()),
        )?,
    })
}
