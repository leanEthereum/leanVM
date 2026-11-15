//! The bus (§sec:gp to §sec:leafstack): its three trees' leaves, their grand products by GKR, and the leaf claims
//! that GKR ends on, split into what the verifier can check.
//!
//! A tree's leaves are a stack of blocks, one per flush of each table and one per boundary set: block `b` holds the
//! fingerprints `β + Σ_x α_x·σ_x(z)` of its rows' tuples (characteristic two), the identity on its padding rows.
//! The push and pull trees have one product (the bus balances), the count tree the product of every access count
//! (each nonzero). The batched GKR ([`gkr`]) leaves one claim per tree at one point `ζ`, which splits by block
//! (eq:gkr_leaves): a boundary block's share is a combination of public columns and of committed columns at `ζ`,
//! whose values are sent; a table's blocks become one degree-two [`Form`] over its columns, `B^s_j`, which the table
//! sumcheck proves ([`crate::constraints`]).

use std::sync::Arc;

use crate::constraints::Form;
use crate::gkr::{self, Ones};
use primitives::cast_slice;
use primitives::field::{Acc8, F64, F64x8, F128, F128x8, g_pow, g_pow32_by_lookup, index_mle, mul_by_g};
use primitives::multilinear::{eq_eval, interp};
use primitives::transcript::ProverState;
pub use verifier::bus_grinding_bits;
use verifier::layout::{GLOBAL_COLUMN_BASES, TABLE_WIDTHS};

/// One tuple coordinate as a function of the block's row `z`.
#[derive(Clone, Debug)]
pub enum Coord {
    /// A public constant (domain separator, opcode, the seed count `1`).
    Const(F64),
    /// A committed column, value `col[z]`.
    Col(usize),
    /// The free increment `g^k · col[z]` (a virtual column, §sec:vm): `k = 1` for the count and state steps, `k ≤ 12`
    /// for a KECCAK state's consecutive cells.
    GCol(usize, u32),
    /// The product `g^k · col_a[z] · col_b[z]` of two committed columns: an address `fp·g^o` rides the bus as one,
    /// committed nowhere (§sec:m3).
    Prod(usize, usize, u32),
    /// The index column `g^z` (§sec:idxcol), free via the factored MLE.
    Index,
    /// A public column (the bytecode program, §sec:e2e-bc): not committed, both parties form its MLE. Shared: push and
    /// pull carry the same thirteen columns ([`isa::Program::columns`]), one `K` word a row.
    Public(Arc<Vec<u64>>),
    /// A sum of `Const`/`Col`/`GCol`/`Prod` terms: a value a row derives from its columns (an `XOR`/`MUL` result, a
    /// `DEREF` store, a `JUMP` successor) without committing it. Only a table's blocks carry one, or a `Prod`: the
    /// table sumcheck settles them, while a boundary block's coordinates must be single columns.
    Sum(Vec<Coord>),
}

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates. The first `rows` flush; the rest are a table's
/// padding rows (§sec:e2e-pad), whose leaves are `1`, and `padding` is the tuple at the table's padding row.
#[derive(Clone, Debug)]
pub struct Block {
    pub kappa: usize,
    pub rows: usize,
    pub coords: Vec<Coord>,
    pub padding: Vec<F64>,
    /// The table whose flush this is, by index; `None` for a boundary block.
    pub owner: Option<usize>,
}

impl Block {
    /// A boundary block, every row of which flushes.
    pub fn full(kappa: usize, coords: Vec<Coord>) -> Self {
        Self {
            kappa,
            rows: 1 << kappa,
            coords,
            padding: Vec::new(),
            owner: None,
        }
    }
}

/// A table coordinate's value on a row whose local columns are `row`.
pub(crate) fn coord_at(c: &Coord, row: &[F64]) -> F64 {
    match c {
        Coord::Const(v) => *v,
        Coord::Col(i) => row[*i],
        Coord::GCol(i, k) => g_pow(*k as usize) * row[*i],
        Coord::Prod(i, j, k) => g_pow(*k as usize) * row[*i] * row[*j],
        Coord::Sum(cs) => cs.iter().map(|c| coord_at(c, row)).sum(),
        Coord::Index | Coord::Public(_) => unreachable!("a table's bus block carries no virtual coordinate"),
    }
}

/// Bits indexing a bus tuple's coordinates: its `2^4` slots are those of the bytecode encoding (§sec:m3,
/// §sec:e2e-bc). A tuple is fingerprinted as `Σ_x α_x·σ_x`, one independent weight per slot (§sec:gp).
pub const N_TUPLE_BITS: usize = verifier::layout::BUS_BITS;

/// The trees the bus GKR batches, in its order: push, pull, then the count tree.
pub const N_BUS_TREES: usize = verifier::N_BUS_TREES;

/// Placement of each block in the stacked leaf vector (input order).
#[derive(Clone, Debug)]
pub struct Layout {
    pub mu: usize,
    pub offsets: Vec<usize>,
}

/// Stack blocks largest-first at aligned offsets; `μ = ⌈log2 Σ 2^{κ_b}⌉`.
pub fn layout(blocks: &[Block]) -> Layout {
    let kappas: Vec<usize> = blocks.iter().map(|b| b.kappa).collect();
    let (offsets, mu) = verifier::stack_offsets(&kappas);
    Layout {
        mu,
        offsets: offsets.into_iter().map(|offset| offset as usize).collect(),
    }
}

/// An evaluation claim on a committed column, settled by the PCS opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ColumnClaim {
    pub col: usize,
    pub point: Vec<F128>,
    pub value: F128,
}

/// What the bus hands on: the boundary blocks' column claims, the GKR's point `ζ` (the table sumcheck's eq point),
/// and per tree each table's form `B^s_j` and what it sums to against `eq(ζ_{<τ_j}, ·)`, which nothing sends: the
/// verifier derives each tree's total.
pub(crate) struct BusProof {
    pub claims: Vec<ColumnClaim>,
    pub point: Vec<F128>,
    /// `forms[tree][table]`.
    pub forms: [Vec<Form>; N_BUS_TREES],
    /// `sigmas[tree][table]`.
    pub sigmas: [Vec<F128>; N_BUS_TREES],
}

/// One bus tree: its blocks, where they sit, and its fingerprint weights `α⃗` and `β`.
struct Tree<'a> {
    blocks: &'a [Block],
    layout: Layout,
    alpha: &'a [F128],
    beta: F128,
}

/// Prove the bus balances (§sec:gp to §sec:leafstack).
///
/// The stream: the [`bus_grinding_bits`] grind and the fingerprint `(α⃗, β)`; the batched GKR
/// ([`gkr::prove_products`]); the boundary blocks' fresh column values; the bytecode's share
/// ([`prove_bytecode_share`]).
pub(crate) fn prove_balance(blocks: [&[Block]; N_BUS_TREES], cols: &[&[F64]], ps: &mut ProverState) -> BusProof {
    let mut layouts = blocks.map(layout);
    let mu = layouts[0].mu;
    assert_eq!(
        layouts[1].mu, mu,
        "push and pull blocks are paired, so their layouts match"
    );
    assert!(layouts[2].mu <= mu, "the count tree is the shortest");
    let widest = blocks.iter().flat_map(|b| b.iter()).map(|b| b.coords.len()).max();
    assert!(
        widest.unwrap_or(0) <= 1 << N_TUPLE_BITS,
        "a tuple's coordinates index its slots"
    );

    let bits = bus_grinding_bits(mu);
    tracing::info_span!("Bus grind", mu, bits).in_scope(|| ps.grind(bits));
    let alpha = ps.sample_vec(1 << N_TUPLE_BITS);
    let beta = ps.sample();
    // The count tree's leaf is the count itself: weight one in slot 0, `β = 0`. Its leaves are a prefix of the push
    // tree's depth, at which `ζ` splits.
    let mut count_alpha = vec![F128::ZERO; 1 << N_TUPLE_BITS];
    count_alpha[0] = F128::ONE;
    let fingerprints = [(&alpha, beta), (&alpha, beta), (&count_alpha, F128::ZERO)];
    layouts[2].mu = mu;
    let trees: [Tree; N_BUS_TREES] = std::array::from_fn(|s| Tree {
        blocks: blocks[s],
        layout: layouts[s].clone(),
        alpha: fingerprints[s].0,
        beta: fingerprints[s].1,
    });

    let leaves = crate::stage!("Bus leaves", || trees.each_ref().map(|tree| build_leaves(tree, cols)));
    let ones = trees.each_ref().map(padding_runs);
    let (zeta, leaf_values) = crate::stage!("Bus GKR", || gkr::prove_products(leaves, ones, ps));

    let mut claims = Vec::new();
    let mut forms = std::array::from_fn(|_| TABLE_WIDTHS.map(Form::new).to_vec());
    let boundary = crate::stage!("Bus decompose", || {
        let boundary: [F128; N_BUS_TREES] =
            std::array::from_fn(|s| decompose(&trees[s], cols, &zeta, &mut forms[s], &mut claims, ps));
        prove_bytecode_share(blocks[0], &zeta, &alpha, ps);
        boundary
    });
    let sigmas = crate::stage!("Bus tables", || table_sums(cols, &forms, &zeta));
    for s in 0..N_BUS_TREES {
        // Completeness only: the verifier derives the tables' share rather than checking it.
        debug_assert_eq!(
            sigmas[s].iter().fold(boundary[s], |acc, &b| acc + b),
            leaf_values[s],
            "tree {s} must decompose into its leaf value"
        );
    }
    BusProof {
        claims,
        point: zeta,
        forms,
        sigmas,
    }
}

/// A non-constant coordinate's term of a leaf, which is its coefficient times this. `GCol` folds its `g^k` into the
/// coefficient.
enum Term<'a> {
    Col(usize),
    Prod(usize, usize),
    Index,
    Public(&'a [F64]),
}

/// One block's leaves, `constant + Σ_terms w·term(z)` on its first `rows` rows and the identity past them.
struct Formula<'a> {
    offset: usize,
    size: usize,
    rows: usize,
    constant: F128,
    terms: Vec<(Term<'a>, F128x8)>,
}

impl<'a> Formula<'a> {
    fn new(block: &'a Block, offset: usize, alpha: &[F128], beta: F128) -> Self {
        let mut constant = beta;
        let mut terms = Vec::with_capacity(block.coords.len());
        for (c, &w) in block.coords.iter().zip(alpha) {
            Self::add(c, w, &mut terms, &mut constant);
        }
        Self {
            offset,
            size: 1 << block.kappa,
            rows: block.rows,
            constant,
            terms: terms.into_iter().map(|(t, w)| (t, F128x8::splat(w))).collect(),
        }
    }

    /// Add coordinate `c` at weight `w`. A [`Coord::Sum`]'s terms share its weight, and the products of one pair in
    /// a sum (a gated count's) one term.
    fn add(c: &'a Coord, w: F128, terms: &mut Vec<(Term<'a>, F128)>, constant: &mut F128) {
        match c {
            Coord::Const(v) => *constant += w.mul_base(*v),
            Coord::Col(i) => terms.push((Term::Col(*i), w)),
            Coord::GCol(i, k) => terms.push((Term::Col(*i), w.mul_base(g_pow(*k as usize)))),
            Coord::Prod(i, j, k) => {
                let v = w.mul_base(g_pow(*k as usize));
                match terms.last_mut() {
                    Some((Term::Prod(a, b), u)) if (*a, *b) == (*i, *j) => *u += v,
                    _ => terms.push((Term::Prod(*i, *j), v)),
                }
            }
            Coord::Index => terms.push((Term::Index, w)),
            Coord::Public(vals) => terms.push((Term::Public(cast_slice(vals)), w)),
            Coord::Sum(cs) => {
                for c in cs {
                    Self::add(c, w, terms, constant);
                }
            }
        }
    }

    /// The leaves of rows `z..z + 8`, each a sum of products reduced once.
    #[inline(always)]
    fn leaves(&self, cols: &[&[F64]], z: usize) -> [F128; 8] {
        if z >= self.rows {
            return [F128::ONE; 8];
        }
        let n = self.rows - z;
        let load = |values: &[F64]| crate::load_k(values, z, n);
        let sum = self.terms.iter().fold(Acc8::ZERO, |acc, (term, w)| {
            acc + w.mul_base_unreduced(match *term {
                Term::Col(i) => load(cols[i]),
                Term::Prod(i, j) => load(cols[i]) * load(cols[j]),
                Term::Index => F64x8::splat(g_pow32_by_lookup(z as u32)) * F64x8::from_array(&G_POWERS),
                Term::Public(vals) => load(vals),
            })
        });
        let mut leaves = (sum.reduce() + F128x8::splat(self.constant)).to_array();
        leaves[n.min(8)..].fill(F128::ONE);
        leaves
    }
}

/// `g^0` to `g^7`, which step a row's index to the next seven's.
const G_POWERS: [F64; 8] = {
    let mut powers = [F64::ONE; 8];
    let mut i = 1;
    while i < 8 {
        powers[i] = mul_by_g(powers[i - 1]);
        i += 1;
    }
    powers
};

/// A tree's leaves, every block's rows at its offset, up to the last block: the identity past them is left out.
/// Each leaf is written once, eight at a time.
fn build_leaves(tree: &Tree, cols: &[&[F64]]) -> Vec<F128> {
    let mut formulas: Vec<Formula> = (tree.blocks.iter().zip(&tree.layout.offsets))
        .map(|(block, &offset)| Formula::new(block, offset, tree.alpha, tree.beta))
        .collect();
    formulas.sort_unstable_by_key(|f| f.offset);
    if formulas.is_empty() {
        return vec![F128::ONE];
    }
    // The blocks tile the leaves from zero, largest first ([`verifier::stack_offsets`]).
    let len = formulas.iter().map(|f| f.size).sum::<usize>();
    let at = |i: usize| &formulas[formulas.partition_point(|f| f.offset <= i) - 1];
    let mut leaves = parallel::map_collect(len.div_ceil(8), |k| {
        let f = at(8 * k);
        if f.size >= 8 {
            // Aligned at its size, the block holds all eight.
            return f.leaves(cols, 8 * k - f.offset);
        }
        // The blocks of fewer than eight rows, which come last: a leaf at a time.
        std::array::from_fn(|i| match 8 * k + i {
            z if z < len => at(z).leaves(cols, z - at(z).offset)[0],
            _ => F128::ONE,
        })
    })
    .into_flattened();
    leaves.truncate(len);
    leaves
}

/// The leaves of a tree's padding rows, which hold the identity, as sorted runs.
fn padding_runs(tree: &Tree) -> Ones {
    let mut runs: Ones = (tree.blocks.iter().zip(&tree.layout.offsets))
        .filter(|(block, _)| block.rows < 1 << block.kappa)
        .map(|(block, &offset)| offset + block.rows..offset + (1 << block.kappa))
        .collect();
    runs.sort_unstable_by_key(|run| run.start);
    runs
}

/// Split a tree's leaf claim by block (eq:gkr_leaves). A table's blocks accumulate into its form, `forms[t]`; a
/// boundary block's committed columns are claimed at `ζ_{<κ}`, each value not already in `claims` sent and recorded,
/// in coordinate order. Returns the boundary blocks' share of the leaf claim, the unused leaves', and the tables'
/// public padding term (eq:pad_leaf): all of it but the forms' sums.
fn decompose(
    tree: &Tree,
    cols: &[&[F64]],
    zeta: &[F128],
    forms: &mut [Form],
    claims: &mut Vec<ColumnClaim>,
    ps: &mut ProverState,
) -> F128 {
    let (alpha, beta) = (tree.alpha, tree.beta);
    assert_eq!(zeta.len(), tree.layout.mu);
    let mut share = F128::ZERO;
    let mut used = F128::ZERO;
    for (block, &offset) in tree.blocks.iter().zip(&tree.layout.offsets) {
        let (zeta_lo, zeta_hi) = zeta.split_at(block.kappa);
        let sel = offset >> block.kappa;
        let sel_bits: Vec<F128> = (0..zeta_hi.len())
            .map(|k| F128::new(((sel >> k) & 1) as u64, 0))
            .collect();
        let eq_sel = eq_eval(&sel_bits, zeta_hi);
        used += eq_sel;

        if let Some(t) = block.owner {
            let (form, base) = (&mut forms[t], GLOBAL_COLUMN_BASES[t]);
            form.constant += eq_sel * beta;
            for (c, &w) in block.coords.iter().zip(alpha) {
                add_to_form(c, eq_sel * w, base, form);
            }
            // The form sums over the padding rows too, where the leaf is `1` rather than `φ(padding)`.
            let phi_padding = (block.padding.iter().zip(alpha)).fold(beta, |acc, (&v, &w)| acc + w.mul_base(v));
            share += eq_sel * padding_weight(zeta_lo, block.rows) * (F128::ONE + phi_padding);
            continue;
        }

        // The block's columns not yet claimed at `ζ_lo`, and its public columns, at `ζ_lo` in one pass.
        let mut fresh: Vec<usize> = (block.coords.iter())
            .filter_map(|c| match c {
                Coord::Col(i) | Coord::GCol(i, _) if known_claim(claims, *i, zeta_lo).is_none() => Some(*i),
                _ => None,
            })
            .collect();
        fresh.sort_unstable();
        fresh.dedup();
        let terms: Vec<(&[F64], Option<&[F64]>)> = (fresh.iter().map(|&i| (cols[i], None)))
            .chain(public_columns(block).map(|c| (c, None)))
            .collect();
        let evals = crate::eq::eq_sums(zeta_lo, &terms);
        let mut public = evals[fresh.len()..].iter().copied();
        let mut col_value = |i: usize| -> F128 {
            if let Some(v) = known_claim(claims, i, zeta_lo) {
                return v;
            }
            let value = evals[fresh.binary_search(&i).unwrap()];
            ps.add_scalar(value);
            let point = zeta_lo.to_vec();
            claims.push(ColumnClaim { col: i, point, value });
            value
        };
        let mut fingerprint = beta;
        for (c, &w) in block.coords.iter().zip(alpha) {
            fingerprint += w * match c {
                Coord::Const(v) => F128::from(*v),
                Coord::Index => index_mle(zeta_lo),
                Coord::Col(i) => col_value(*i),
                Coord::GCol(i, k) => col_value(*i).mul_base(g_pow(*k as usize)),
                Coord::Public(_) => public.next().unwrap(),
                Coord::Prod(..) | Coord::Sum(..) => unreachable!("only a table's block carries a degree-2 coordinate"),
            };
        }
        share += eq_sel * fingerprint;
    }
    // The unused leaves past the blocks are `1`.
    share + F128::ONE + used
}

/// `pad_n(point)`, the multilinear extension of `[z ≥ n]`, `n ≤ 2^|point|` (lemma lem:suffix).
fn padding_weight(point: &[F128], n: usize) -> F128 {
    let bit = |k: usize| F128::new(((n >> k) & 1) as u64, 0);
    let low = point.iter().enumerate().fold(F128::ONE, |pad, (k, &r)| {
        (F128::ONE + bit(k)) * r + (F128::ONE + bit(k) + r) * pad
    });
    (F128::ONE + bit(point.len())) * low
}

/// Add coordinate `c` of a table's block to that table's form at weight `w`, global column `i` its local `i - base`.
/// A [`Coord::Sum`]'s terms share its weight.
fn add_to_form(c: &Coord, w: F128, base: usize, form: &mut Form) {
    match c {
        Coord::Const(v) => form.constant += w.mul_base(*v),
        Coord::Col(i) => form.coeffs[*i - base] += w,
        Coord::GCol(i, k) => form.coeffs[*i - base] += w.mul_base(g_pow(*k as usize)),
        Coord::Prod(i, j, k) => form.prods.push((*i - base, *j - base, w.mul_base(g_pow(*k as usize)))),
        Coord::Sum(cs) => {
            for c in cs {
                add_to_form(c, w, base, form);
            }
        }
        Coord::Index | Coord::Public(_) => unreachable!("a table's bus block carries no virtual coordinate"),
    }
}

/// The value already claimed for `(col, point)`: push and pull share their point, so a column read by both, or by
/// two blocks of one height, is sent and opened once.
fn known_claim(claims: &[ColumnClaim], col: usize, point: &[F128]) -> Option<F128> {
    claims
        .iter()
        .find(|c| c.col == col && c.point == point)
        .map(|c| c.value)
}

/// A block's public columns, in coordinate order.
fn public_columns(block: &Block) -> impl Iterator<Item = &[F64]> {
    block.coords.iter().filter_map(|c| match c {
        Coord::Public(vals) => Some(cast_slice(vals)),
        _ => None,
    })
}

/// The program's share of a bytecode leaf, `S = Σ_x α_x·P(ζ_lo, x)` over the slots `x` of the stacked bytecode `P`
/// (§sec:e2e-bc), reduced to one evaluation of `P`. The stream: `S`, a sumcheck of [`N_TUPLE_BITS`] degree-two rounds
/// over `x`, the low bit bound first, ending at `r⃗`, then `P(ζ_lo, r⃗)`, whose product with `α̃(r⃗)` the verifier
/// checks against the last round.
fn prove_bytecode_share(push: &[Block], zeta: &[F128], alpha: &[F128], ps: &mut ProverState) {
    let block = (push.iter())
        .find(|block| public_columns(block).next().is_some())
        .expect("the push side seeds the bytecode");
    let zeta_lo = &zeta[..block.kappa];
    let public: Vec<(&[F64], Option<&[F64]>)> = public_columns(block).map(|c| (c, None)).collect();
    let mut evals = crate::eq::eq_sums(zeta_lo, &public).into_iter();
    let mut slots: Vec<F128> = (0..1 << N_TUPLE_BITS)
        .map(|x| match block.coords.get(x) {
            Some(Coord::Public(_)) => evals.next().unwrap(),
            _ => F128::ZERO,
        })
        .collect();
    let mut weights = alpha.to_vec();
    ps.add_scalar(weights.iter().zip(&slots).map(|(&a, &p)| a * p).sum());
    for _ in 0..N_TUPLE_BITS {
        let pairs = || weights.as_chunks::<2>().0.iter().zip(slots.as_chunks::<2>().0);
        let c0: F128 = pairs().map(|(a, p)| a[0] * p[0]).sum();
        let c2: F128 = pairs().map(|(a, p)| (a[0] + a[1]) * (p[0] + p[1])).sum();
        let c1: F128 = pairs().map(|(a, p)| a[0] * (p[0] + p[1]) + (a[0] + a[1]) * p[0]).sum();
        ps.add_round_poly(&[c0, c1, c2], false);
        let r = ps.sample();
        let fold = |v: &[F128]| -> Vec<F128> { v.as_chunks::<2>().0.iter().map(|h| interp(h[0], h[1], r)).collect() };
        (weights, slots) = (fold(&weights), fold(&slots));
    }
    ps.add_scalar(slots[0]);
}

/// What each tree's form of each table sums to against `eq(ζ_{<τ}, ·)`. A form's linear part needs the table's
/// columns at `ζ_{<τ}`, its products `Σ_z eq·col_a·col_b` for each pair, all of a table's in one pass, a pair named
/// by several forms (an address flushed by both sides) once.
fn table_sums(cols: &[&[F64]], forms: &[Vec<Form>; N_BUS_TREES], zeta: &[F128]) -> [Vec<F128>; N_BUS_TREES] {
    let per_table: Vec<[F128; N_BUS_TREES]> = (0..verifier::layout::N_TABLES)
        .map(|t| {
            let n_cols = TABLE_WIDTHS[t];
            let columns = &cols[GLOBAL_COLUMN_BASES[t]..][..n_cols];
            let mut pairs: Vec<(usize, usize)> = (forms.iter())
                .flat_map(|tree| tree[t].prods.iter().map(|&(a, b, _)| (a, b)))
                .collect();
            pairs.sort_unstable();
            pairs.dedup();
            let terms: Vec<(&[F64], Option<&[F64]>)> = (columns.iter().map(|&c| (c, None)))
                .chain(pairs.iter().map(|&(a, b)| (columns[a], Some(columns[b]))))
                .collect();
            let sums = crate::eq::eq_sums(&zeta[..crate::log2_strict_usize(columns[0].len())], &terms);
            let (evals, pair_sums) = sums.split_at(n_cols);
            forms.each_ref().map(|tree| {
                let form = &tree[t];
                form.prods.iter().fold(form.linear(evals), |acc, &(a, b, q)| {
                    acc + q * pair_sums[pairs.binary_search(&(a, b)).unwrap()]
                })
            })
        })
        .collect();
    std::array::from_fn(|s| per_table.iter().map(|sums| sums[s]).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// A coordinate's value at row `z`, from its definition.
    fn coord_value(c: &Coord, cols: &[&[F64]], z: usize) -> F64 {
        match c {
            Coord::Const(v) => *v,
            Coord::Col(i) => cols[*i][z],
            Coord::GCol(i, k) => g_pow(*k as usize) * cols[*i][z],
            Coord::Prod(i, j, k) => g_pow(*k as usize) * cols[*i][z] * cols[*j][z],
            Coord::Index => g_pow(z),
            Coord::Public(vals) => F64(vals[z]),
            Coord::Sum(cs) => cs.iter().map(|c| coord_value(c, cols, z)).sum(),
        }
    }

    /// The leaves by their definition, every block at its offset.
    fn naive_leaves(tree: &Tree, cols: &[&[F64]]) -> Vec<F128> {
        let len = tree.blocks.iter().map(|blk| 1 << blk.kappa).sum::<usize>().max(1);
        let mut leaves = vec![F128::ONE; len];
        for (b, blk) in tree.blocks.iter().enumerate() {
            for z in 0..blk.rows {
                leaves[tree.layout.offsets[b] + z] = (blk.coords.iter().zip(tree.alpha))
                    .fold(tree.beta, |acc, (c, &wi)| acc + wi.mul_base(coord_value(c, cols, z)));
            }
        }
        leaves
    }

    /// The builder's leaves are their definitions.
    #[test]
    fn built_leaves_match_the_definition() {
        let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15);
        let columns: Vec<Vec<F64>> = (0..6)
            .map(|_| (0..1 << 12).map(|_| F64(rng.next_u64())).collect())
            .collect();
        let cols: Vec<&[F64]> = columns.iter().map(Vec::as_slice).collect();
        let public = Arc::new((0..1 << 11).map(|_| rng.next_u64()).collect::<Vec<_>>());
        let block = |kappa: usize, rows: usize, coords: Vec<Coord>| Block {
            kappa,
            rows,
            coords,
            padding: Vec::new(),
            owner: None,
        };
        use Coord::*;
        let wide = |count: Coord| {
            vec![
                Const(F64(5)),
                Index,
                count,
                Prod(0, 2, 1),
                Sum(vec![Col(4), GCol(5, 3)]),
            ]
        };
        let narrow = |count: Coord| vec![Const(F64(7)), Col(3), count, Public(public.clone())];
        let push = vec![
            block(12, 3001, wide(GCol(1, 1))),
            block(11, 1 << 11, narrow(Col(2))),
            block(2, 3, vec![Const(F64(1)), Col(4)]),
            block(0, 1, vec![Const(F64(2))]),
        ];
        let pull = vec![
            block(12, 3001, wide(Col(1))),
            block(11, 1 << 11, narrow(GCol(2, 1))),
            block(1, 2, vec![Const(F64(3)), Col(0)]),
        ];
        let count = vec![block(12, 3001, vec![Col(1)]), block(11, 1 << 11, vec![Col(2)])];
        let alpha = rng.ext_vec(1 << N_TUPLE_BITS);
        let beta = F128::new(27, 18);
        for (blocks, beta) in [(&push, beta), (&pull, beta), (&count, F128::ZERO)] {
            let tree = Tree {
                blocks,
                layout: layout(blocks),
                alpha: &alpha,
                beta,
            };
            assert_eq!(build_leaves(&tree, &cols), naive_leaves(&tree, &cols));
        }
    }
}
