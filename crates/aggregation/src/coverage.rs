//! What a node declares and what it sets aside: each scheme's declared claims and its duplicates.

use super::error::AggregateError;
use super::proof::AggregateProof;
use super::{AggregateClaims, LeanSphincsClaim, LeanXmssClaim};
use std::collections::BTreeSet;

/// The claims a node puts out, scheme by scheme: as a multiset, exactly the claims it takes in, its raw signatures'
/// and its children's. The guest checks that equality with a product over each side (`claims_product`), which is
/// what makes every declared claim covered by a real signature or a verified child.
pub(super) struct Coverage {
    pub(super) lean_xmss: Covered<LeanXmssClaim>,
    pub(super) lean_sphincs: Covered<LeanSphincsClaim>,
}

/// One scheme's claims put out.
pub(super) struct Covered<K> {
    /// The declared claims, strictly sorted.
    pub(super) declared: Vec<K>,
    /// The claims taken in beyond one of each declared claim.
    pub(super) dups: Vec<K>,
}

impl<K: Ord + Clone> Covered<K> {
    /// Declares the union of the raw claims and the children's, or exactly `declare`, which they must cover.
    fn plan<'a>(
        raw: &'a [K],
        children: impl Iterator<Item = &'a [K]>,
        declare: Option<&[K]>,
    ) -> Result<Self, AggregateError>
    where
        K: 'a,
    {
        let taken_in: Vec<&K> = raw.iter().chain(children.flatten()).collect();
        let mut declared: Vec<K> = taken_in.iter().map(|&claim| claim.clone()).collect();
        declared.sort();
        declared.dedup();
        if let Some(declare) = declare {
            let mut wanted: BTreeSet<&K> = declare.iter().collect();
            declared.retain(|claim| wanted.remove(claim));
            if !wanted.is_empty() {
                return Err(AggregateError::InvalidInput(
                    "a requested claim is not covered by the inputs",
                ));
            }
        }
        // A claim is declared once: its other occurrences, and the claims not declared, are duplicates.
        let mut claimed = vec![false; declared.len()];
        let mut dups = Vec::new();
        for claim in taken_in {
            match declared.binary_search(claim) {
                Ok(pos) if !claimed[pos] => claimed[pos] = true,
                _ => dups.push(claim.clone()),
            }
        }
        Ok(Self { declared, dups })
    }
}

pub(super) fn plan_coverage(
    raw_lean_xmss: &[LeanXmssClaim],
    raw_lean_sphincs: &[LeanSphincsClaim],
    children: &[(AggregateClaims, AggregateProof)],
    declare: Option<&AggregateClaims>,
) -> Result<Coverage, AggregateError> {
    Ok(Coverage {
        lean_xmss: Covered::plan(
            raw_lean_xmss,
            children.iter().map(|(claims, _)| claims.lean_xmss.as_slice()),
            declare.map(|claims| claims.lean_xmss.as_slice()),
        )?,
        lean_sphincs: Covered::plan(
            raw_lean_sphincs,
            children.iter().map(|(claims, _)| claims.lean_sphincs.as_slice()),
            declare.map(|claims| claims.lean_sphincs.as_slice()),
        )?,
    })
}
