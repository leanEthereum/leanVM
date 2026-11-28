//! The coverage table: which slot each raw signature and child claim writes.

use super::AggregateClaims;
use super::error::AggregateError;
use super::statement::{Claim, claim_lists};

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
    /// The raw signatures in walk order, by index: sorted on their claims, the first of each repeat kept.
    pub(super) raw_order: Vec<usize>,
    /// The slot of each write, in walk order: the raw signatures' of `raw_order`, then each child's claims'.
    pub(super) slots: Vec<usize>,
}

/// The order that sorts `claims`, stably, keeping the first of each repeat.
fn sorted_firsts(claims: &[Claim]) -> Vec<usize> {
    let mut order = super::sort::order_by_key(claims.len(), |i| &claims[i]);
    order.dedup_by_key(|i| &claims[*i]);
    order
}

/// `claims[i]` for each `i` of `order`.
#[inline(never)]
fn pick(claims: &[Claim], order: &[usize]) -> Vec<Claim> {
    order.iter().map(|&i| claims[i]).collect()
}

impl Region {
    /// The region of scheme `scheme` (0 or 1), from its raw claims in any order: declares the union of the raw claims
    /// and the children's, or exactly `declare`, which they must cover.
    #[inline(never)]
    fn plan(
        scheme: usize,
        raw: &[Claim],
        children: &[[Vec<Claim>; 2]],
        declare: Option<&[Claim]>,
    ) -> Result<Self, AggregateError> {
        let raw_order = sorted_firsts(raw);
        let mut all = pick(raw, &raw_order);
        for child in children {
            all.extend_from_slice(&child[scheme]);
        }
        let wanted = declare.map(|declare| pick(declare, &sorted_firsts(declare)));
        // Each write's slot, in walk order: a declared claim's first write takes its declared slot, every other write
        // a fresh slot outside the hashed prefix.
        let mut slots = vec![usize::MAX; all.len()];
        let mut signers = Vec::new();
        for &i in &sorted_firsts(&all) {
            if wanted
                .as_ref()
                .is_none_or(|wanted| wanted.binary_search(&all[i]).is_ok())
            {
                slots[i] = signers.len();
                signers.push(all[i]);
            }
        }
        // Both lists are sorted without repeats, so the ones kept are all the wanted ones exactly when as many.
        if wanted.is_some_and(|wanted| wanted.len() != signers.len()) {
            return Err(AggregateError::InvalidInput(
                "a requested claim is not covered by the inputs",
            ));
        }
        let mut dups = Vec::new();
        for (slot, claim) in slots.iter_mut().zip(&all) {
            if *slot == usize::MAX {
                *slot = signers.len() + dups.len();
                dups.push(*claim);
            }
        }
        Ok(Self {
            signers,
            dups,
            raw_order,
            slots,
        })
    }
}

/// Both regions, from each scheme's raw claims and each child's claim lists.
pub(super) fn plan_coverage(
    raw: [&[Claim]; 2],
    children: &[[Vec<Claim>; 2]],
    declare: Option<&AggregateClaims>,
) -> Result<Coverage, AggregateError> {
    let declare = declare.map(claim_lists);
    let plan = |s: usize| {
        let declare = declare.as_ref().map(|lists| lists[s].as_slice());
        Region::plan(s, raw[s], children, declare)
    };
    Ok([plan(0)?, plan(1)?])
}
