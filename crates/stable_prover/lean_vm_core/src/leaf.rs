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

use crate::constraints::Form;
use crate::gkr::{self, Ones};
use pcs::sumcheck::product_sumcheck;
use primitives::cast_slice;
use primitives::field::{Acc8, F64, F64x8, F128, F128x8, mul_by_g};
use primitives::transcript::ProverState;
use verifier::N_BUS_TREES;
use verifier::layout::{BUS_BITS, GLOBAL_COLUMN_BASES, TABLE_WIDTHS};

/// One tuple coordinate as a function of the block's row `z`.
#[derive(Clone, Debug)]
pub enum Coord {
    /// A public constant (domain separator, opcode, the seed count `1`).
    Const(F64),
    /// A committed column, value `col[z]`.
    Col(usize),
    /// `g^k · col[z]`, a virtual column (§sec:vm): a count's increment or the fall-through pc, `k = 1`.
    GCol(usize, u32),
    /// The product `g^k · col_a[z] · col_b[z]` of two committed columns: an address `fp·g^o` rides the bus as one,
    /// committed nowhere (§sec:m3).
    Prod(usize, usize, u32),
    /// The index column `g^z` (§sec:idxcol), free via the factored MLE.
    Index,
    /// Column `s` of the stacked bytecode (§sec:e2e-bc, [`isa::Program::stacked_bytecode`]): public, not committed,
    /// both parties form its MLE.
    Public(usize),
    /// A sum of `Const`/`Col`/`GCol`/`Prod` terms: a value a row derives from its columns (an `XOR`/`MUL` result, a
    /// `DEREF` store, a `JUMP` successor) without committing it. Only a table's blocks carry one, or a `Prod`: the
    /// table sumcheck settles them, while a boundary block's coordinates must be single columns.
    Sum(Vec<Coord>),
}

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates. The first `rows` flush; the rest are a table's
/// padding rows (§sec:e2e-pad), whose leaves are `1`, and `padding` is the tuple at the table's padding row, which the
/// guest's padding term reads.
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
    // A public column would be read past the row.
    let (mut terms, mut constant) = (Vec::new(), F128::ZERO);
    Formula::add(c, F128::ONE, row.len(), &mut terms, &mut constant);
    let value = terms.into_iter().fold(constant, |acc, (term, w)| {
        acc + w.mul_base(match term {
            Term::Col(i) => row[i],
            Term::Prod(i, j) => row[i] * row[j],
            Term::Index => unreachable!("a table's bus block carries no virtual coordinate"),
        })
    });
    value.as_base().expect("a table coordinate lies in K")
}

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
/// and per tree each table's form `B^s_j`. What the forms sum to is never sent: the verifier derives each tree's total.
pub(crate) struct BusProof {
    pub claims: Vec<ColumnClaim>,
    pub point: Vec<F128>,
    /// `forms[tree][table]`.
    pub forms: [Vec<Form>; N_BUS_TREES],
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
/// The stream: the [`verifier::bus_grinding_bits`] grind and the fingerprint `(α⃗, β)`; the batched GKR
/// ([`gkr::prove_products`]); the boundary blocks' fresh column values; the bytecode's share
/// ([`prove_bytecode_share`]).
pub(crate) fn prove_balance(
    blocks: [&[Block]; N_BUS_TREES],
    cols: &[&[F64]],
    stacked_bytecode: &[u64],
    ps: &mut ProverState,
) -> BusProof {
    // The columns [`Coord::Public`] names.
    let public: Vec<&[F64]> = cast_slice(stacked_bytecode)
        .chunks_exact(stacked_bytecode.len() >> BUS_BITS)
        .collect();
    let mut layouts = blocks.map(layout);
    let mu = layouts[0].mu;
    assert_eq!(
        layouts[1].mu, mu,
        "push and pull blocks are paired, so their layouts match"
    );
    assert!(layouts[2].mu <= mu, "the count tree is the shortest");
    let widest = blocks.iter().flat_map(|b| b.iter()).map(|b| b.coords.len()).max();
    assert!(
        widest.unwrap_or(0) <= 1 << BUS_BITS,
        "a tuple's coordinates index its slots"
    );

    let bits = verifier::bus_grinding_bits(mu);
    ps.grind(bits);
    let alpha = ps.sample_vec(1 << BUS_BITS);
    let beta = ps.sample();
    // The count tree's leaf is the count itself: weight one in slot 0, `β = 0`. Its leaves are a prefix of the push
    // tree's depth, at which `ζ` splits.
    let mut count_alpha = vec![F128::ZERO; 1 << BUS_BITS];
    count_alpha[0] = F128::ONE;
    let fingerprints = [(&alpha, beta), (&alpha, beta), (&count_alpha, F128::ZERO)];
    layouts[2].mu = mu;
    let mut layouts = layouts.into_iter();
    let trees: [Tree; N_BUS_TREES] = std::array::from_fn(|s| Tree {
        blocks: blocks[s],
        layout: layouts.next().unwrap(),
        alpha: fingerprints[s].0,
        beta: fingerprints[s].1,
    });

    // The committed columns, then the public ones.
    let columns: Vec<&[F64]> = cols.iter().chain(&public).copied().collect();
    let leaves = trees.each_ref().map(|tree| build_leaves(tree, &columns, cols.len()));
    let (zeta, _) = gkr::prove_products(leaves, ps);

    let mut claims = Vec::new();
    let mut forms: [Vec<Form>; N_BUS_TREES] =
        std::array::from_fn(|_| TABLE_WIDTHS.iter().map(|&width| Form::new(width)).collect());
    {
        for (tree, forms) in trees.iter().zip(&mut forms) {
            decompose(tree, cols, &zeta, forms, &mut claims, ps);
        }
        prove_bytecode_share(blocks[0], &public, &zeta, &alpha, ps);
    };
    BusProof {
        claims,
        point: zeta,
        forms,
    }
}

/// A non-constant coordinate's term of a leaf, which is its coefficient times this. `GCol` folds its `g^k` into the
/// coefficient; a [`Coord::Public`] column is a `Col` past the committed ones.
enum Term {
    Col(usize),
    Prod(usize, usize),
    Index,
}

/// One block's leaves, `constant + Σ_terms w·term(z)` on its first `rows` rows and the identity past them.
struct Formula {
    offset: usize,
    size: usize,
    rows: usize,
    constant: F128,
    terms: Vec<(Term, F128)>,
}

impl Formula {
    /// The block's formula, its public columns from column `public`.
    fn new(block: &Block, offset: usize, alpha: &[F128], beta: F128, public: usize) -> Self {
        let mut constant = beta;
        let mut terms = Vec::with_capacity(block.coords.len());
        for (c, &w) in block.coords.iter().zip(alpha) {
            Self::add(c, w, public, &mut terms, &mut constant);
        }
        Self {
            offset,
            size: 1 << block.kappa,
            rows: block.rows,
            constant,
            terms,
        }
    }

    /// Add coordinate `c` at weight `w`. A [`Coord::Sum`]'s terms share its weight, and the products of one pair in
    /// a sum (a gated count's) one term.
    fn add(c: &Coord, w: F128, public: usize, terms: &mut Vec<(Term, F128)>, constant: &mut F128) {
        let (term, k) = match *c {
            Coord::Const(v) => return *constant += w.mul_base(v),
            Coord::Col(i) => (Term::Col(i), 0),
            Coord::GCol(i, k) => (Term::Col(i), k),
            Coord::Prod(i, j, k) => (Term::Prod(i, j), k),
            Coord::Index => (Term::Index, 0),
            Coord::Public(s) => (Term::Col(public + s), 0),
            Coord::Sum(ref cs) => {
                for c in cs {
                    Self::add(c, w, public, terms, constant);
                }
                return;
            }
        };
        let v = w.mul_base(crate::tables::g_pow(k as usize));
        match (terms.last_mut(), &term) {
            (Some((Term::Prod(a, b), u)), Term::Prod(i, j)) if (*a, *b) == (*i, *j) => *u += v,
            _ => terms.push((term, v)),
        }
    }

    /// The leaves of rows `z..z + 8`, each a sum of products reduced once.
    #[inline]
    fn leaves(&self, cols: &[&[F64]], z: usize) -> [F128; 8] {
        if z >= self.rows {
            return ONES;
        }
        let n = self.rows - z;
        let load = |values: &[F64]| crate::load_k(values, z, n);
        let sum = self.terms.iter().fold(Acc8::ZERO, |acc, &(ref term, w)| {
            let (w, k) = match *term {
                Term::Col(i) => (w, load(cols[i])),
                Term::Prod(i, j) => (w, load(cols[i]) * load(cols[j])),
                // `g^z` rides the weight.
                Term::Index => (w.mul_base(F64(isa::g_pow(z as u32))), F64x8::from_array(&G_POWERS)),
            };
            acc + F128x8::splat(w).mul_base_unreduced(k)
        });
        let mut leaves = (sum.reduce() + F128x8::splat(self.constant)).to_array();
        let n = n.min(8);
        leaves[n..].copy_from_slice(&ONES[n..]);
        leaves
    }
}

/// Eight identities.
const ONES: [F128; 8] = [F128::ONE; 8];

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

/// A tree's leaves, every block's rows at its offset, up to the last block, padded with the identity to a multiple of
/// [`gkr::BLOCK`]: the identity past them is left out. Each leaf is written once, eight at a time. With them, the runs of padding rows, whose leaves are the identity.
/// `cols` are the committed columns, then the public ones from `public`.
fn build_leaves(tree: &Tree, cols: &[&[F64]], public: usize) -> (Vec<F128>, Ones) {
    // [`verifier::stack_offsets`] places each size from the largest down, its blocks in index order.
    let largest = tree.blocks.iter().map(|b| b.kappa).max().unwrap_or(0);
    let mut formulas = Vec::with_capacity(tree.blocks.len());
    for kappa in (0..=largest).rev() {
        for (block, &offset) in tree.blocks.iter().zip(&tree.layout.offsets) {
            if block.kappa == kappa {
                formulas.push(Formula::new(block, offset, tree.alpha, tree.beta, public));
            }
        }
    }
    let ones = (formulas.iter())
        .filter(|f| f.rows < f.size)
        .map(|f| f.offset + f.rows..f.offset + f.size)
        .collect();
    if formulas.is_empty() {
        return (vec![F128::ONE], ones);
    }
    // The blocks tile the leaves from zero, largest first.
    let len = formulas.iter().map(|f| f.size).sum::<usize>();
    let at = |i: usize| &formulas[formulas.partition_point(|f| f.offset <= i) - 1];
    let leaves = parallel::map_collect(len.next_multiple_of(gkr::BLOCK) / 8, |k| {
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
    (leaves, ones)
}

/// Split a tree's leaf claim by block (eq:gkr_leaves). A table's blocks accumulate into its form, `forms[t]`; a
/// boundary block's committed columns are claimed at `ζ_{<κ}`, each value not already in `claims` sent and recorded,
/// in coordinate order. The rest of the claim is public, and the verifier derives the forms' share from it.
fn decompose(
    tree: &Tree,
    cols: &[&[F64]],
    zeta: &[F128],
    forms: &mut [Form],
    claims: &mut Vec<ColumnClaim>,
    ps: &mut ProverState,
) {
    let (alpha, beta) = (tree.alpha, tree.beta);
    assert_eq!(zeta.len(), tree.layout.mu);
    for (block, &offset) in tree.blocks.iter().zip(&tree.layout.offsets) {
        let (zeta_lo, zeta_hi) = zeta.split_at(block.kappa);
        if let Some(t) = block.owner {
            // `eq(ζ_hi, ·)` at the block's index among the blocks of its height.
            let sel = offset >> block.kappa;
            let eq_sel: F128 = (zeta_hi.iter().enumerate())
                .map(|(k, &z)| if (sel >> k) & 1 == 1 { z } else { F128::ONE + z })
                .product();
            let (form, base) = (&mut forms[t], GLOBAL_COLUMN_BASES[t]);
            form.constant += eq_sel * beta;
            let mut terms = Vec::new();
            for (c, &w) in block.coords.iter().zip(alpha) {
                Formula::add(c, eq_sel * w, 0, &mut terms, &mut form.constant);
            }
            for (term, w) in terms {
                match term {
                    Term::Col(i) => form.coeffs[i - base] += w,
                    Term::Prod(i, j) => form.prods.push((i - base, j - base, w)),
                    Term::Index => unreachable!("a table's bus block carries no virtual coordinate"),
                }
            }
            continue;
        }

        // The block's columns not yet claimed at `ζ_lo`, in coordinate order, at `ζ_lo` in one pass.
        let mut fresh: Vec<usize> = Vec::new();
        for c in &block.coords {
            if let Coord::Col(i) | Coord::GCol(i, _) = c
                && !known_claim(claims, *i, zeta_lo)
                && !fresh.contains(i)
            {
                fresh.push(*i);
            }
        }
        let columns: Vec<&[F64]> = fresh.iter().map(|&i| cols[i]).collect();
        for (&col, value) in fresh.iter().zip(crate::eq::eq_sums(zeta_lo, &columns)) {
            ps.add_scalar(value);
            let point = zeta_lo.to_vec();
            claims.push(ColumnClaim { col, point, value });
        }
    }
}

/// Whether `(col, point)` is already claimed: push and pull share their point, so a column read by both, or by two
/// blocks of one height, is sent and opened once.
fn known_claim(claims: &[ColumnClaim], col: usize, point: &[F128]) -> bool {
    claims.iter().any(|c| c.col == col && c.point == point)
}

/// A block's public columns, in coordinate order.
fn public_columns<'a>(block: &Block, public: &[&'a [F64]]) -> impl Iterator<Item = &'a [F64]> {
    block.coords.iter().filter_map(|c| match c {
        Coord::Public(s) => Some(public[*s]),
        _ => None,
    })
}

/// The program's share of a bytecode leaf, `S = Σ_x α_x·P(ζ_lo, x)` over the slots `x` of the stacked bytecode `P`
/// (§sec:e2e-bc), reduced to one evaluation of `P`. The stream: `S`, a sumcheck of [`BUS_BITS`] degree-two rounds
/// over `x`, the low bit bound first, ending at `r⃗`, then `P(ζ_lo, r⃗)`, whose product with `α̃(r⃗)` the verifier
/// checks against the last round.
fn prove_bytecode_share(push: &[Block], public: &[&[F64]], zeta: &[F128], alpha: &[F128], ps: &mut ProverState) {
    let block = (push.iter())
        .find(|block| public_columns(block, public).next().is_some())
        .expect("the push side seeds the bytecode");
    let zeta_lo = &zeta[..block.kappa];
    let columns: Vec<&[F64]> = public_columns(block, public).collect();
    let mut evals = crate::eq::eq_sums(zeta_lo, &columns).into_iter();
    let slots: Vec<F128> = (0..1 << BUS_BITS)
        .map(|x| match block.coords.get(x) {
            Some(Coord::Public(_)) => evals.next().unwrap(),
            _ => F128::ZERO,
        })
        .collect();
    ps.add_scalar(primitives::field::dot(alpha, &slots));
    let (_, slots, _) = product_sumcheck(ps, alpha.to_vec(), slots, 1, F128::ONE);
    ps.add_scalar(slots[0]);
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::g_pow;
    use primitives::test_rng::Rng;

    /// A coordinate's value at row `z`, from its definition.
    fn coord_value(c: &Coord, cols: &[&[F64]], public: &[&[F64]], z: usize) -> F64 {
        match c {
            Coord::Const(v) => *v,
            Coord::Col(i) => cols[*i][z],
            Coord::GCol(i, k) => g_pow(*k as usize) * cols[*i][z],
            Coord::Prod(i, j, k) => g_pow(*k as usize) * cols[*i][z] * cols[*j][z],
            Coord::Index => g_pow(z),
            Coord::Public(s) => public[*s][z],
            Coord::Sum(cs) => cs.iter().map(|c| coord_value(c, cols, public, z)).sum(),
        }
    }

    /// The leaves by their definition, every block at its offset.
    fn naive_leaves(tree: &Tree, cols: &[&[F64]], public: &[&[F64]]) -> Vec<F128> {
        let len = tree.blocks.iter().map(|blk| 1 << blk.kappa).sum::<usize>().max(1);
        let mut leaves = vec![F128::ONE; len];
        for (b, blk) in tree.blocks.iter().enumerate() {
            for z in 0..blk.rows {
                leaves[tree.layout.offsets[b] + z] = (blk.coords.iter().zip(tree.alpha))
                    .fold(tree.beta, |acc, (c, &wi)| {
                        acc + wi.mul_base(coord_value(c, cols, public, z))
                    });
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
        let bytecode: Vec<F64> = (0..1 << 11).map(|_| F64(rng.next_u64())).collect();
        let public = [bytecode.as_slice()];
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
        let narrow = |count: Coord| vec![Const(F64(7)), Col(3), count, Public(0)];
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
        let alpha = rng.ext_vec(1 << BUS_BITS);
        let beta = F128::new(27, 18);
        for (blocks, beta) in [(&push, beta), (&pull, beta), (&count, F128::ZERO)] {
            let tree = Tree {
                blocks,
                layout: layout(blocks),
                alpha: &alpha,
                beta,
            };
            let columns: Vec<&[F64]> = cols.iter().chain(&public).copied().collect();
            let (leaves, naive) = (
                build_leaves(&tree, &columns, cols.len()).0,
                naive_leaves(&tree, &cols, &public),
            );
            assert_eq!(leaves[..naive.len()], naive);
            assert!(leaves[naive.len()..].iter().all(|&l| l == F128::ONE));
        }
    }
}
