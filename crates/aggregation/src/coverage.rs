//! The coverage table: which slot each raw signature and child claim writes.

use super::AggregateClaims;
use super::error::AggregateError;
use super::statement::{Claim, claim_lists};
use std::collections::BTreeSet;

/// The coverage slot each write in the guest's coverage walk targets, in walk
/// order: the raw signatures first, then each child's claim lists. Its regions, leanXMSS then leanSPHINCS.
///
/// The table is one contiguous region per scheme, each its declared claims followed
/// by its own duplicate slots:
///
/// | slots | holds |
/// | --- | --- |
/// | `[0, n_lean_xmss)` | the declared leanXMSS claims |
/// | `[n_lean_xmss, X)` | leanXMSS duplicate slots |
/// | `[X, X + n_lean_sphincs)` | the declared leanSPHINCS claims |
/// | `[X + n_lean_sphincs, n_total)` | leanSPHINCS duplicate slots |
///
/// A claim the declared set holds takes its slot there, one it does not takes a
/// fresh duplicate slot in the same region, so the walk hits every one of the
/// `n_total` slots exactly once. That bijection, enforced in-circuit by write-once
/// memory plus the final count, is what makes every declared claim covered by a real
/// signature or a verified child.
///
/// Keeping each region contiguous is what binds the scheme: the guest addresses
/// every writer as an offset into one region, bounded by that region's size, one
/// range check per write, so no signature can reach a claim of the other scheme.
pub(super) type Coverage = [Region; 2];

/// One scheme's region of the coverage table.
pub(super) struct Region {
    /// The declared claims, strictly sorted.
    pub(super) signers: Vec<Claim>,
    pub(super) dups: Vec<Claim>,
    /// The slot of each raw signature, in the order given.
    pub(super) raw: Vec<usize>,
    /// Per child, the slot of each of its claims.
    pub(super) children: Vec<Vec<usize>>,
}

/// The order that sorts `claims`, stably, keeping the first of each repeat.
pub(super) fn sorted_firsts(claims: &[Claim]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..claims.len()).collect();
    isa::sort::sort_by_key(&mut order, |&i| claims[i]);
    order.dedup_by_key(|i| claims[*i]);
    order
}

impl Region {
    /// The region of scheme `scheme` (0 or 1): declares the union of the raw claims and the children's, or exactly
    /// `declare`, which they must cover.
    fn plan(
        scheme: usize,
        raw: &[Claim],
        children: &[[Vec<Claim>; 2]],
        declare: Option<&[Claim]>,
    ) -> Result<Self, AggregateError> {
        let mut all = raw.to_vec();
        for child in children {
            all.extend_from_slice(&child[scheme]);
        }
        let mut signers: Vec<Claim> = sorted_firsts(&all).into_iter().map(|i| all[i]).collect();
        if let Some(declare) = declare {
            // Inserted one by one: collecting would sort them first.
            let mut wanted: BTreeSet<&Claim> = BTreeSet::new();
            wanted.extend(declare);
            signers.retain(|claim| wanted.remove(claim));
            if !wanted.is_empty() {
                return Err(AggregateError::InvalidInput(
                    "a requested claim is not covered by the inputs",
                ));
            }
        }
        // A claim takes its declared slot once; later or undeclared occurrences take fresh slots outside the hashed
        // prefix.
        let mut claimed = vec![false; signers.len()];
        let mut dups = Vec::new();
        let mut take_slot = |claim: &Claim| match signers.binary_search(claim) {
            Ok(pos) if !claimed[pos] => {
                claimed[pos] = true;
                pos
            }
            _ => {
                dups.push(*claim);
                signers.len() + dups.len() - 1
            }
        };
        let raw = raw.iter().map(&mut take_slot).collect();
        let children = children
            .iter()
            .map(|child| child[scheme].iter().map(&mut take_slot).collect())
            .collect();
        Ok(Self {
            signers,
            dups,
            raw,
            children,
        })
    }
}

/// Both regions, from each scheme's raw claims (sorted, without repeats) and each child's claim lists.
pub(super) fn plan_coverage(
    raw: &[Vec<Claim>; 2],
    children: &[[Vec<Claim>; 2]],
    declare: Option<&AggregateClaims>,
) -> Result<Coverage, AggregateError> {
    let declare = declare.map(claim_lists);
    let plan = |s: usize| Region::plan(s, &raw[s], children, declare.as_ref().map(|lists| lists[s].as_slice()));
    Ok([plan(0)?, plan(1)?])
}
