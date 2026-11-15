//! The guest's claim pool and its coordinate terms.

use super::cells::count;
use lean_vm_core::cpu::{block_kappa_sources, keccak_value};
use lean_vm_core::leaf::{Block, Coord};
use primitives::field::F128;
use std::collections::{BTreeMap, HashMap};
use verifier::layout::{GLOBAL_COLUMN_BASES, TABLE_WIDTHS};
use verifier::layout::{MEMORY_0, MEMORY_1};

/// One entry of the guest's claim pool.
pub(super) enum ClaimSite {
    /// A committed column read by a framework bus block of kappa source `source`.
    Framework { column: usize, source: (usize, usize) },
    /// A table column, a KECCAK value lane's ([`keccak_value`]) included.
    TableColumn { column: usize, table: usize },
    /// One of the two PI memory limbs (MEMORY_0, MEMORY_1).
    MemoryLimb { column: usize },
}

/// The guest's `COORD_KIND_*` code for a coordinate (`guests/lean_ethereum.py`),
/// shared by its `COORD_TYPE` and `TERM_TYPE` arrays.
pub(super) fn coord_kind(c: &Coord) -> usize {
    match c {
        Coord::Const(_) => 0,
        Coord::Col(_) => 1,
        Coord::GCol(..) => 2,
        Coord::Index => 3,
        Coord::Public(_) => 4,
        Coord::Prod(..) => 5,
        Coord::Sum(..) => 6,
    }
}

/// The `K` scalar a coordinate carries beside its columns: the constant itself,
/// or the `g^k` a `GCol`/`Prod` scales by. Zero for every other kind.
pub(super) fn coord_scale(c: &Coord) -> F128 {
    match c {
        Coord::Const(v) => F128::from(*v),
        Coord::GCol(_, k) | Coord::Prod(_, _, k) => count(*k as usize),
        _ => F128::ZERO,
    }
}

/// Flatten one table-block coordinate into the guest's term arrays, in local
/// column indices. A [`Coord::Sum`]'s children are its terms; every other kind is
/// one term. `Index`/`Public` never reach a table block.
pub(super) fn push_coord_terms(c: &Coord, base: usize, terms: &mut Vec<Term>) {
    let (column_a, column_b) = match c {
        Coord::Const(_) => (0, 0),
        Coord::Col(i) | Coord::GCol(i, _) => (*i - base, 0),
        Coord::Prod(i, j, _) => (*i - base, *j - base),
        Coord::Sum(cs) => {
            for c in cs {
                push_coord_terms(c, base, terms);
            }
            return;
        }
        Coord::Index | Coord::Public(_) => unreachable!("a table's bus block carries no virtual coordinate"),
    };
    terms.push(Term {
        kind: coord_kind(c),
        constant: u128::from(coord_scale(c)),
        column_a,
        column_b,
    });
}

/// The terms of `a + b` (characteristic 2), merged: constants summed, the scales of
/// one column or one column product summed, and whatever sums to zero dropped.
pub(super) fn coord_difference(a: &[Term], b: &[Term]) -> Vec<Term> {
    let (konst, col, gcol) = (0, 1, 2); // coord_kind of Const, Col, GCol
    let one = u128::from(F128::ONE);
    let mut constant = 0u128;
    let mut scaled: BTreeMap<(usize, usize, usize), u128> = BTreeMap::new();
    for t in a.iter().chain(b) {
        match t.kind {
            k if k == konst => constant ^= t.constant,
            k if k == col => *scaled.entry((gcol, t.column_a, 0)).or_default() ^= one,
            k if k == gcol => *scaled.entry((gcol, t.column_a, 0)).or_default() ^= t.constant,
            k => {
                let (x, y) = (t.column_a.min(t.column_b), t.column_a.max(t.column_b));
                *scaled.entry((k, x, y)).or_default() ^= t.constant;
            }
        }
    }
    let mut out = Vec::new();
    if constant != 0 {
        out.push(Term {
            kind: konst,
            constant,
            column_a: 0,
            column_b: 0,
        });
    }
    for ((kind, column_a, column_b), constant) in scaled {
        if constant != 0 {
            let kind = if kind == gcol && constant == one { col } else { kind };
            out.push(Term {
                kind,
                constant,
                column_a,
                column_b,
            });
        }
    }
    out
}

/// The claim pool in the exact order the guest indexes it: the framework bus
/// claims (deduped by `(column, kappa)`, as `leaf.rs` pools them), then every
/// table's committed columns, then the PI memory limbs. With it, for every
/// coordinate of every block in order, `(fresh, slot)`: whether it raises its
/// framework claim first, and that claim's slot; zero for one that raises none.
pub(super) fn claim_pool(sides: &[Vec<Block>; 3], kbc: usize) -> (Vec<ClaimSite>, Vec<(usize, usize)>) {
    let (mut pool, mut coords) = (Vec::new(), Vec::new());
    let mut slot_of: HashMap<(usize, usize), usize> = HashMap::new();
    for (blk, &source) in sides.iter().flatten().zip(&block_kappa_sources(kbc)) {
        for c in &blk.coords {
            // Only the framework blocks raise claims: a table's coords are settled inside
            // the table sumcheck.
            let column = match c {
                Coord::Col(i) | Coord::GCol(i, _) if source.0 < 2 => *i,
                _ => {
                    coords.push((0, 0));
                    continue;
                }
            };
            let key = (column, blk.kappa);
            let fresh = !slot_of.contains_key(&key);
            if fresh {
                // Why the guest reads every `q_keccak` slot claim's instance point off `chi`: a virtual value column
                // is referenced only by its own table's bus blocks, which the table sumcheck settles.
                assert!(
                    keccak_value(column).is_none(),
                    "a framework block must not reference a virtual value column"
                );
                slot_of.insert(key, pool.len());
                pool.push(ClaimSite::Framework { column, source });
            }
            coords.push((usize::from(fresh), slot_of[&key]));
        }
    }
    for (t, (&base, &width)) in GLOBAL_COLUMN_BASES.iter().zip(&TABLE_WIDTHS).enumerate() {
        pool.extend((base..base + width).map(|column| ClaimSite::TableColumn { column, table: t }));
    }
    pool.extend([MEMORY_0, MEMORY_1].map(|column| ClaimSite::MemoryLimb { column }));
    (pool, coords)
}

pub(super) struct Term {
    pub(super) kind: usize,
    pub(super) constant: u128,
    pub(super) column_a: usize,
    pub(super) column_b: usize,
}
