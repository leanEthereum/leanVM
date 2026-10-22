//! The bus: a single shared channel balanced by a grand product (§sec:gp through §sec:leafstack). Each
//! interaction wires a table's columns into width-`m` tuples and flushes them in a
//! direction; the bus balances when pushed and pulled tuples form the same
//! multiset, proven by two GKR passes over the leaf vectors `β − π_α(σ)`. Each pass
//! reduces to a leaf claim `Ṽ₀(ζ)`, decomposed into evaluation claims on the
//! committed columns. Tuple coordinates `σ_i` are `K`-valued (column entries,
//! g-powers, separators); the fingerprint challenges `α, β` are `E`-valued, so a
//! leaf accumulates via the mixed `mul_base` product (2 PMULL per coordinate).

use crate::colval::ColVal;
use crate::gkr;
use crate::transcript::ProverState;
use primitives::field::{F64, F192, F192Unreduced, Weights8, dot_base, g_pow, index_mle, mul_by_g};
use primitives::multilinear::{eq_eval, eq_table, mle_eval, mle_eval_par};
use std::collections::HashMap;
use std::ops::Range;
use std::sync::Arc;

/// One tuple coordinate as a function of the block's row `z`.
#[derive(Clone, Debug)]
pub enum Coord {
    /// A public constant (domain separator, opcode, the seed count `1`).
    Const(F64),
    /// A committed column, value `col[z]`.
    Col(usize),
    /// The free increment `g^k · col[z]` (a virtual column, §sec:vm): `k = 1` for the
    /// count/state steps, `k ≤ 12` for a KECCAK state's consecutive cells.
    GCol(usize, u32),
    /// The product `g^k · col_a[z] · col_b[z]` of two committed columns. An address
    /// is `fp·g^o`, so this carries one on the bus without committing it: the
    /// coordinate IS the product, so no column can disagree with it and the binding
    /// constraint that used to say so is unnecessary (§sec:m3).
    Prod(usize, usize, u32),
    /// The index column `g^z` (§sec:idxcol), free via the factored MLE.
    Index,
    /// A public column (the bytecode program, §sec:e2e-bc): not committed; both parties form
    /// its MLE directly, so it raises no claim. Shared rather than owned: push and
    /// pull carry the same eleven columns, tens of megabytes at production sizes.
    Public(Arc<Vec<F64>>),
    /// A sum of `Const`/`Col`/`GCol`/`Prod` terms: any degree-2 form over the
    /// table's columns, which is all §sec:m3 asks of a coordinate. This is what
    /// carries a value a row DERIVES from its columns (an `XOR`/`MUL` result, a
    /// `DEREF` store, a `JUMP` successor) without committing a column for it, and
    /// with it the identity that would have tied the two. Like [`Coord::Prod`],
    /// only a table's blocks may carry one: the table sumcheck settles them,
    /// while a framework block has to split into per-column openings.
    Sum(Vec<Coord>),
}

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates. The first `rows` flush;
/// the rest are a table's padding rows (§sec:e2e-pad), whose leaves are `1`, and
/// `padding` is the tuple at the table's padding row.
#[derive(Clone, Debug)]
pub struct Block {
    pub kappa: usize,
    pub rows: usize,
    pub coords: Vec<Coord>,
    pub padding: Vec<F64>,
}

impl Block {
    /// A block every row of which flushes.
    pub fn full(kappa: usize, coords: Vec<Coord>) -> Self {
        Self {
            kappa,
            rows: 1 << kappa,
            coords,
            padding: Vec::new(),
        }
    }
}

/// `pad_n(point)`, the multilinear extension of `[z ≥ n]`, `n ≤ 2^|point|` (lemma lem:suffix).
fn padding_weight(point: &[F192], n: usize) -> F192 {
    let bit = |k: usize| F192::new(((n >> k) & 1) as u64, 0, 0);
    let low = point.iter().enumerate().fold(F192::ONE, |pad, (k, &r)| {
        (F192::ONE + bit(k)) * r + (F192::ONE + bit(k) + r) * pad
    });
    (F192::ONE + bit(point.len())) * low
}

/// A table coordinate's value on a row whose local columns are `row`.
pub(crate) fn coord_at(c: &Coord, row: &[F64]) -> F64 {
    match c {
        Coord::Const(v) => *v,
        Coord::Col(i) => row[*i],
        Coord::GCol(i, k) => g_pow(*k as usize) * row[*i],
        Coord::Prod(i, j, k) => g_pow(*k as usize) * row[*i] * row[*j],
        Coord::Sum(cs) => cs.iter().fold(F64::ZERO, |acc, c| acc + coord_at(c, row)),
        Coord::Index | Coord::Public(_) => unreachable!("a table's bus block carries no virtual coordinate"),
    }
}

/// Placement of each block in the stacked leaf vector (input order).
#[derive(Clone, Debug)]
pub struct Layout {
    pub mu: usize,
    pub offsets: Vec<usize>,
}

/// An evaluation claim on a committed column, settled against the witness.
/// Reconstructed identically by both sides (its value rides the stream).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnClaim {
    pub col: usize,
    pub point: Vec<F192>,
    pub value: F192,
}

/// The fingerprint weights `eq(α⃗, x)` over the `2^N_TUPLE_BITS` slots (§sec:gp).
/// A tuple is fingerprinted as `Σ_x eq(α⃗, x)·σ_x`, a MULTILINEAR combination
/// rather than a power chain: each leaf factor is then of total degree
/// `N_TUPLE_BITS` in the challenges instead of the tuple width, and slot `x`'s
/// weight is an `eq` weight, which is what lets the aligned bytecode polynomial
/// be read off at `α⃗` itself (§sec:e2e-bc).
pub fn fingerprint_weights(alphas: &[F192]) -> Vec<F192> {
    debug_assert_eq!(alphas.len(), N_TUPLE_BITS);
    let mut w = vec![F192::ONE; 1 << N_TUPLE_BITS];
    for (bit, &a) in alphas.iter().enumerate() {
        for (x, wx) in w.iter_mut().enumerate() {
            *wx *= if (x >> bit) & 1 == 1 { a } else { a + F192::ONE };
        }
    }
    w
}

/// Bits indexing a bus tuple's coordinates: `m = 14` coordinates live in the
/// `2^4` slots of the bytecode encoding (§sec:m3, §sec:e2e-bc).
pub const N_TUPLE_BITS: usize = 4;

/// Conservative sum of the degree bounds for every random-challenge failure in
/// the bus argument. A side contains at most `2^mu` leaf factors, each of total
/// degree `N_TUPLE_BITS` in `α⃗` and one in `β`. The second term covers all
/// radix-four GKR batching and sumcheck challenges.
fn soundness_degree_bound(mu: usize) -> u128 {
    assert!(mu < u128::BITS as usize, "bus layout is too large to bound");
    let fingerprint = (N_TUPLE_BITS as u128 + 1) * (1u128 << mu);
    let gkr = 8u128 * (mu as u128 + 1).pow(2);
    fingerprint + gkr
}

fn soundness_bits(mu: usize) -> u32 {
    let degree = soundness_degree_bound(mu);
    192u32.saturating_sub(u128::BITS - degree.leading_zeros())
}

/// Check that the 192-bit challenge field supplies the target bus soundness.
/// Push and pull have the same logical height, and the count product is checked
/// by the same GKR rather than by a separate root-at-random test.
fn assert_grinding_unnecessary(
    push_blocks: &[Block],
    pull_blocks: &[Block],
    push: &Layout,
    pull: &Layout,
    count: &Layout,
) {
    assert_eq!(
        push.mu, pull.mu,
        "push/pull bus blocks are paired, so their layouts match"
    );
    assert!(count.mu <= push.mu, "count sums fewer bus messages than push");
    let widest = push_blocks
        .iter()
        .chain(pull_blocks)
        .map(|block| block.coords.len())
        .max()
        .unwrap_or(0);
    assert!(widest <= 1 << N_TUPLE_BITS, "a tuple's coordinates index its slots");
    assert!(
        soundness_bits(push.mu) >= crate::SECURITY_BITS,
        "bus layout exceeds the unground F192 soundness budget"
    );
}

/// Stack blocks largest-first at aligned offsets; `μ = ⌈log2 Σ 2^{κ_b}⌉`.
pub fn layout(blocks: &[Block]) -> Layout {
    let kappas: Vec<Option<usize>> = blocks.iter().map(|b| Some(b.kappa)).collect();
    let (offsets, placed) = crate::witness::stack_offsets(&kappas);
    Layout {
        mu: crate::log2_ceil_usize(placed.max(1)),
        offsets,
    }
}

/// A non-constant coordinate as `(source, coefficient)`: its leaf contribution is
/// the mixed product `coeff · source(z)` with `source(z) ∈ K`, `coeff ∈ E`.
/// `GCol` folds the `g^k` factor into the coefficient.
enum Term<'a> {
    Col(usize, F192),
    Prod(usize, usize, F192),
    Index(F192),
    Public(&'a [F64], F192),
}

/// Flatten one coordinate into leaf terms at coefficient `w`. A [`Coord::Sum`]
/// spreads its children over the SAME `w`: they are one coordinate, so they share
/// its `α`-power.
fn push_terms<'a>(c: &'a Coord, w: F192, terms: &mut Vec<Term<'a>>, constant: &mut F192) {
    match c {
        Coord::Const(v) => *constant += w.mul_base(*v),
        Coord::Col(i) => terms.push(Term::Col(*i, w)),
        Coord::GCol(i, k) => terms.push(Term::Col(*i, w.mul_base(g_pow(*k as usize)))),
        Coord::Prod(i, j, k) => terms.push(Term::Prod(*i, *j, w.mul_base(g_pow(*k as usize)))),
        Coord::Index => terms.push(Term::Index(w)),
        Coord::Public(vals) => terms.push(Term::Public(vals.as_slice(), w)),
        Coord::Sum(cs) => {
            for c in cs {
                push_terms(c, w, terms, constant);
            }
        }
    }
}

/// One block's leaf formula: `const_part + Σ terms(z)` on its real rows, the identity
/// on its padding rows.
struct LeafBlock<'a> {
    side: usize,
    offset: usize,
    kappa: usize,
    rows: usize,
    const_part: F192,
    terms: Vec<Term<'a>>,
}

impl LeafBlock<'_> {
    /// The leaf of real row `z`, whose index column value `g^z` is `index`.
    #[inline]
    fn leaf(&self, z: usize, cols: &[&[F64]], index: F64) -> F192 {
        // The α-weighted coordinate sum defers its reductions: each mixed
        // product contributes its three raw limb products (3 PMULL, no
        // reduction tail), one combined reduction per row at the end,
        // bit-identical to summing reduced `mul_base` terms.
        let mut acc = F192Unreduced::ZERO;
        for t in &self.terms {
            acc ^= match t {
                Term::Col(i, c) => c.mul_base_unreduced(cols[*i][z]),
                Term::Prod(i, j, c) => c.mul_base_unreduced(cols[*i][z] * cols[*j][z]),
                Term::Index(c) => c.mul_base_unreduced(index),
                Term::Public(vals, c) => c.mul_base_unreduced(vals[z]),
            };
        }
        self.const_part + acc.reduce()
    }

    /// The leaves of rows `z0..z0 + out.len()`.
    fn fill(&self, z0: usize, out: &mut [F192], cols: &[&[F64]]) {
        let real = self.rows.saturating_sub(z0).min(out.len());
        let (real_out, padding) = out.split_at_mut(real);
        // A padding row's leaf is the identity, so it leaves the product alone.
        padding.fill(F192::ONE);
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
        let done = self.fill8(z0, real_out, cols);
        #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq")))]
        let done = 0;
        let mut index = g_pow(z0 + done);
        for (i, slot) in real_out.iter_mut().enumerate().skip(done) {
            *slot = self.leaf(z0 + i, cols, index);
            index = mul_by_g(index);
        }
    }

    /// [`fill`](Self::fill) eight rows at a time, every term one lane-wise mixed
    /// product ([`primitives::field::x8`]); returns how many rows it wrote.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    fn fill8(&self, z0: usize, out: &mut [F192], cols: &[&[F64]]) -> usize {
        use primitives::field::x8::{F64x8, F192x8, Mixed8};
        let eight = |source: &[F64], z: usize| F64x8::load(source[z..z + 8].try_into().unwrap());
        // `g^z` for the eight rows, stepped by `g^8`.
        let mut index = F64x8::new(std::array::from_fn(|i| g_pow(z0 + i)));
        let step = F64x8::splat(g_pow(8));
        let coeffs: Vec<F192x8> = self
            .terms
            .iter()
            .map(|t| match t {
                Term::Col(_, c) | Term::Prod(_, _, c) | Term::Index(c) | Term::Public(_, c) => F192x8::splat(*c),
            })
            .collect();
        let constant = F192x8::splat(self.const_part);
        let (chunks, _) = out.as_chunks_mut::<8>();
        for (k, slot) in chunks.iter_mut().enumerate() {
            let z = z0 + 8 * k;
            let mut acc = Mixed8::ZERO;
            for (t, &c) in self.terms.iter().zip(&coeffs) {
                match t {
                    Term::Col(i, _) => acc.add(c, eight(cols[*i], z)),
                    Term::Prod(i, j, _) => acc.add(c, eight(cols[*i], z) * eight(cols[*j], z)),
                    Term::Index(_) => acc.add(c, index),
                    Term::Public(vals, _) => acc.add(c, eight(vals, z)),
                }
            }
            index = index * step;
            (acc.reduce() + constant).store(slot);
        }
        8 * chunks.len()
    }
}

/// `dst[i] = ∏ src[4i..4i+4]`, an incomplete last four-tuple padded with the identity.
fn padded_products(src: &[F192], dst: &mut [F192]) {
    let full = src.len() / 4;
    gkr::products_into(&src[..4 * full], &mut dst[..full]);
    if full < dst.len() {
        dst[full] = src[4 * full..].iter().fold(F192::ONE, |acc, &x| acc * x);
    }
}

/// Build the three sides' leaves: block `b` row `z` holds `β − Σ_i w_i c_i(z)` for the
/// side's fingerprint weights `w = eq(α⃗, ·)`, followed implicitly by the identity `1`
/// up to `2^μ`. The row-invariant weights and constant coordinates are folded once
/// per block into its `const_part`.
///
/// The blocks of one height and row count (a table's push, pull and count blocks,
/// which read the same columns) are built together, a chunk of rows at a time, so a
/// column is read from memory once however many blocks flush it. Each chunk's
/// four- and sixteen-tuple products, the GKR's levels two and four, are formed while
/// it is in cache.
pub fn build_leaves(sides: [(&[Block], &Layout, &[F192], F192); 3], cols: &[&[F64]]) -> [gkr::Leaves; 3] {
    /// Rows staged at a time: one block's chunk stays in L1 while its products are formed.
    const CHUNK: usize = 1 << 11;
    /// Leaves per task, whatever the group's block count, so that tasks balance.
    const TASK_LEAVES: usize = 1 << 15;
    /// Blocks below this height are left to a serial pass, being too small to own
    /// whole sixteen-tuples.
    const CHUNKED: usize = 4;

    let mut blocks: Vec<LeafBlock> = Vec::new();
    let mut lens = [1usize; 3];
    for (side, &(side_blocks, lay, w, beta)) in sides.iter().enumerate() {
        // `stack_offsets` packs the power-of-two blocks contiguously from zero,
        // largest first, so they tile `0..len`, and the blocks of height `CHUNKED` or
        // more precede the smaller ones.
        if !side_blocks.is_empty() {
            lens[side] = side_blocks.iter().map(|blk| 1usize << blk.kappa).sum();
        }
        for (b, blk) in side_blocks.iter().enumerate() {
            assert!(
                lay.offsets[b] + (1 << blk.kappa) <= lens[side],
                "the blocks tile the leaves"
            );
            let mut const_part = beta;
            let mut terms: Vec<Term> = Vec::with_capacity(blk.coords.len());
            for (i, c) in blk.coords.iter().enumerate() {
                push_terms(c, w[i], &mut terms, &mut const_part);
            }
            blocks.push(LeafBlock {
                side,
                offset: lay.offsets[b],
                kappa: blk.kappa,
                rows: blk.rows,
                const_part,
                terms,
            });
        }
        debug_assert!(lens[side] <= 1usize << lay.mu);
    }

    // Capacity is rounded to whole four-tuples because `gkr::QuaternaryLayerState`
    // pads this level to that before reading it, and growing it here would copy it.
    let mut values: [Vec<F192>; 3] = lens.map(|n| {
        // SAFETY: the blocks write every leaf of `0..n` (one identity leaf for a side
        // without blocks, below) before anything reads it.
        let mut v = unsafe { primitives::uninit_vec(n.next_multiple_of(4)) };
        v.truncate(n);
        v
    });
    // SAFETY: the chunks write the products of the tuples inside blocks of height
    // `CHUNKED` or more, and the serial pass below the rest.
    let mut fours: [Vec<F192>; 3] = lens.map(|n| unsafe { primitives::uninit_vec(n.div_ceil(4)) });
    let mut sixteens: [Vec<F192>; 3] = lens.map(|n| unsafe { primitives::uninit_vec(n.div_ceil(16)) });

    let mut shapes: Vec<(usize, usize)> = blocks
        .iter()
        .filter(|b| b.kappa >= CHUNKED)
        .map(|b| (b.kappa, b.rows))
        .collect();
    shapes.sort_unstable();
    shapes.dedup();
    let groups: Vec<Vec<&LeafBlock>> = shapes
        .iter()
        .map(|&shape| blocks.iter().filter(|b| (b.kappa, b.rows) == shape).collect())
        .collect();
    let tasks: Vec<(usize, Range<usize>)> = shapes
        .iter()
        .zip(&groups)
        .enumerate()
        .flat_map(|(g, (&(kappa, _), group))| {
            let height = 1usize << kappa;
            let rows = (TASK_LEAVES / group.len()).next_power_of_two().min(height);
            (0..height).step_by(rows).map(move |z| (g, z..z + rows))
        })
        .collect();
    let ptrs = [&mut values, &mut fours, &mut sixteens]
        .map(|level| level.each_mut().map(|v| parallel::SendPtr(v.as_mut_ptr())));
    parallel::for_each(tasks.len(), |task| {
        let (group, ref rows) = tasks[task];
        let mut stage = [F192::ZERO; CHUNK];
        let mut stage4 = [F192::ZERO; CHUNK / 4];
        let mut stage16 = [F192::ZERO; CHUNK / 16];
        // The GKR reads all three long after this pass has evicted them.
        let stream = primitives::stream::Stream::new();
        for z0 in rows.clone().step_by(CHUNK) {
            let len = CHUNK.min(rows.len());
            let (leaves, fours, sixteens) = (&mut stage[..len], &mut stage4[..len / 4], &mut stage16[..len / 16]);
            for blk in &groups[group] {
                blk.fill(z0, leaves, cols);
                gkr::products_into(leaves, fours);
                gkr::products_into(fours, sixteens);
                let at = blk.offset + z0;
                // SAFETY: a block's chunks are disjoint ranges of its side's leaves, blocks
                // are disjoint, and a chunk owns the tuples it starts, `at` being a multiple
                // of sixteen.
                unsafe {
                    stream.copy(ptrs[0][blk.side].slice(at, len), leaves);
                    stream.copy(ptrs[1][blk.side].slice(at / 4, len / 4), fours);
                    stream.copy(ptrs[2][blk.side].slice(at / 16, len / 16), sixteens);
                }
            }
        }
    });

    for (side, v) in values.iter_mut().enumerate() {
        let mut tail = lens[side];
        for blk in blocks.iter().filter(|b| b.side == side && b.kappa < CHUNKED) {
            blk.fill(0, &mut v[blk.offset..blk.offset + (1 << blk.kappa)], cols);
            tail = tail.min(blk.offset);
        }
        if sides[side].0.is_empty() {
            v[0] = F192::ONE;
        }
        // The tuples among the smallest blocks, the last ones padded with the identity.
        padded_products(&v[tail..], &mut fours[side][tail / 4..]);
        padded_products(&fours[side][tail / 4..], &mut sixteens[side][tail / 16..]);
    }
    let [v0, v1, v2] = values;
    let [f0, f1, f2] = fours;
    let [s0, s1, s2] = sixteens;
    [(0, v0, f0, s0), (1, v1, f1, s1), (2, v2, f2, s2)].map(|(side, values, fours, sixteens)| gkr::Leaves {
        values,
        fours,
        sixteens,
        // The padding rows of the chunked blocks.
        ones: blocks
            .iter()
            .filter(|blk| blk.side == side && blk.kappa >= CHUNKED && blk.rows < 1 << blk.kappa)
            .map(|blk| blk.offset + blk.rows..blk.offset + (1 << blk.kappa))
            .collect(),
    })
}

/// One table's bus contribution on one side, as a form over that table's committed
/// columns: `Σ_c coeffs[c]·col_c(z) + Σ (a,b,c) c·col_a(z)·col_b(z) + constant`.
/// Every coefficient is a public function of `α`, `β` and the block selectors at
/// `ζ`, because a table's bus blocks carry only `Const`/`Col`/`GCol`/`Prod`
/// coordinates. The table sumcheck sums this against `eq(ζ[..τ], ·)` instead of
/// opening each column at `ζ`, which is why those per-column claims no longer reach
/// the PCS.
///
/// The quadratic part comes from [`Coord::Prod`] and is free: the AIR identities are
/// already degree 2, so a degree-2 form does not raise the round-polynomial degree
/// the batch pays for.
#[derive(Clone, Debug)]
pub struct BusForm {
    pub coeffs: Vec<F192>,
    /// `(col_a, col_b, coeff)` in LOCAL column indices.
    pub prods: Vec<(usize, usize, F192)>,
    pub constant: F192,
}

impl BusForm {
    fn new(n_cols: usize) -> Self {
        Self {
            coeffs: vec![F192::ZERO; n_cols],
            prods: Vec::new(),
            constant: F192::ZERO,
        }
    }

    /// The same form scaled by `w`. Every coefficient is `E`-valued already, so
    /// folding the side's `η`-power in here costs three multiplies once per table
    /// instead of one per [`eval_unreduced`](Self::eval_unreduced), which the
    /// zerocheck calls per row per round.
    pub fn scaled(&self, w: F192) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(|&c| c * w).collect(),
            prods: self.prods.iter().map(|&(a, b, c)| (a, b, c * w)).collect(),
            constant: self.constant * w,
        }
    }

    /// The pointwise sum of several forms over the same columns.
    ///
    /// Evaluating the sum is evaluating each and adding, and the constraint batch
    /// only ever wants a table's total, so its three bus sides collapse to one
    /// dot product and one product list: the row loop then reads the column
    /// values once for all three rather than once each.
    pub fn sum(forms: impl IntoIterator<Item = Self>) -> Self {
        let mut forms = forms.into_iter();
        let mut out = forms.next().expect("a table has at least one bus form");
        for form in forms {
            assert_eq!(out.coeffs.len(), form.coeffs.len(), "forms over the same columns");
            for (slot, c) in out.coeffs.iter_mut().zip(form.coeffs) {
                *slot += c;
            }
            out.constant += form.constant;
            for (a, b, c) in form.prods {
                match out.prods.iter_mut().find(|p| (p.0, p.1) == (a, b)) {
                    Some(p) => p.2 += c,
                    None => out.prods.push((a, b, c)),
                }
            }
        }
        out.prods.retain(|p| p.2 != F192::ZERO);
        out
    }

    /// The form at one point, unreduced: `evals` are the columns' values there.
    /// This is what the zerocheck evaluates, per row while a table is unfolded and
    /// at the sumcheck point after, so a table's several forms share one reduction
    /// rather than paying one per term.
    /// `quadratic` selects only degree-two terms, for a sumcheck round coefficient.
    pub fn eval_unreduced<T: ColVal>(&self, evals: &[T], quadratic: bool) -> T::Unreduced {
        self.prods.iter().fold(
            if quadratic {
                T::lift(F192::ZERO)
            } else {
                T::dot_unreduced(&self.coeffs, evals) ^ T::lift(self.constant)
            },
            |acc, &(a, b, c)| acc ^ (evals[a] * evals[b]).mul_e_unreduced(c),
        )
    }

    /// What the form sums to over the table's rows against `eq(ζ, ·)`, the target the
    /// zerocheck settles. The linear part factors through the columns' evaluations at
    /// `ζ`, which is the whole point of a form; a product coordinate does NOT, so
    /// `prod_sums` supplies `Σ_z eq(ζ,z)·col_a(z)·col_b(z)` for each pair it uses.
    fn sum_at(&self, evals: &[F192], prod_sums: &[(usize, usize, F192)]) -> F192 {
        self.prods
            .iter()
            .fold(F192::dot(&self.coeffs, evals, self.constant), |acc, &(a, b, c)| {
                let s = prod_sums
                    .iter()
                    .find(|p| (p.0, p.1) == (a, b))
                    .expect("every pair was summed");
                acc + c * s.2
            })
    }
}

/// Accumulate one coordinate of a table's block into that table's form, at
/// coefficient `w`. A [`Coord::Sum`]'s children share `w`, so a derived value
/// lands as the several coefficients and products it is made of.
fn accumulate_form(c: &Coord, w: F192, base: usize, form: &mut BusForm) {
    match c {
        Coord::Const(v) => form.constant += w.mul_base(*v),
        Coord::Col(i) => form.coeffs[*i - base] += w,
        Coord::GCol(i, k) => form.coeffs[*i - base] += w.mul_base(g_pow(*k as usize)),
        Coord::Prod(i, j, k) => form.prods.push((*i - base, *j - base, w.mul_base(g_pow(*k as usize)))),
        Coord::Sum(cs) => {
            for c in cs {
                accumulate_form(c, w, base, form);
            }
        }
        Coord::Index | Coord::Public(_) => {
            unreachable!("a table's bus block carries no virtual coordinate")
        }
    }
}

/// Walk one side's blocks. A block owned by table `t` (with column base `base`)
/// accumulates into `forms[t]`; the framework blocks are decomposed into per-column
/// claims as before, `fresh` supplying values not already in `claims`. Returns the
/// framework blocks' contribution to `Ṽ₀(ζ)` plus the padding mass, so the caller
/// can settle the side once the zerocheck has proven the tables' forms.
///
/// A table's form is summed over all its rows, padding rows included, where the leaf
/// holds `1` instead: the difference, `padding_weight · (β + fingerprint(pad) + 1)`, is
/// public, so it joins the padding mass.
fn decompose_formula<F: FnMut(usize, &[F192]) -> F192>(
    blocks: &[Block],
    lay: &Layout,
    zeta: &[F192],
    w: &[F192],
    beta: F192,
    owners: &[Option<(usize, usize)>],
    forms: &mut [BusForm],
    claims: &mut Vec<ColumnClaim>,
    public: &mut PublicEvals,
    mut fresh: F,
) -> F192 {
    assert_eq!(zeta.len(), lay.mu);
    let mut acc = F192::ZERO;
    let mut sel_sum = F192::ZERO;
    for (b, blk) in blocks.iter().enumerate() {
        let kappa = blk.kappa;
        let zeta_lo = &zeta[..kappa];
        let zeta_hi = &zeta[kappa..];
        let sel = lay.offsets[b] >> kappa;
        let sel_bits: Vec<F192> = (0..(lay.mu - kappa))
            .map(|k| F192::new(((sel >> k) & 1) as u64, 0, 0))
            .collect();
        let eq_hi = eq_eval(&sel_bits, zeta_hi);
        sel_sum += eq_hi;

        // A table's block becomes a linear form the zerocheck will sum; only the
        // framework blocks (boundary, memory, bytecode) still open columns at ζ.
        if let Some((t, base)) = owners[b] {
            let form = &mut forms[t];
            form.constant += eq_hi * beta;
            for (i, c) in blk.coords.iter().enumerate() {
                accumulate_form(c, eq_hi * w[i], base, form);
            }
            let phi_padding = blk
                .padding
                .iter()
                .zip(w)
                .fold(beta, |acc, (&v, &wi)| acc + wi.mul_base(v));
            acc += eq_hi * padding_weight(zeta_lo, blk.rows) * (F192::ONE + phi_padding);
            continue;
        }

        // Column `i` at ζ_lo: reuse the recorded claim, else take a fresh value and
        // record it. The push ORDER is the stream order, so every coordinate that
        // needs a column value must go through here.
        let mut col_val = |i: usize| -> F192 {
            if let Some(v) = known_claim(claims, i, zeta_lo) {
                return v;
            }
            let v = fresh(i, zeta_lo);
            claims.push(ColumnClaim {
                col: i,
                point: zeta_lo.to_vec(),
                value: v,
            });
            v
        };
        let mut inner = F192::ZERO;
        for (i, c) in blk.coords.iter().enumerate() {
            let coord_val = match c {
                Coord::Const(v) => F192::from(*v),
                Coord::Index => index_mle(zeta_lo),
                Coord::Col(i) => col_val(*i),
                Coord::GCol(i, k) => col_val(*i).mul_base(g_pow(*k as usize)),
                Coord::Prod(..) | Coord::Sum(..) => {
                    unreachable!("only a table's bus block carries a degree-2 coordinate")
                }
                Coord::Public(vals) => public_eval(vals, zeta_lo, public),
            };
            inner += w[i] * coord_val;
        }
        acc += eq_hi * (beta + inner);
    }
    // The padding rows (identity `1`) contribute the leftover mass `1 - Σ_b sel_b`.
    acc + (F192::ONE + sel_sum)
}

/// Look up an already-recorded claim on `(col, point)`. Push and pull share
/// their GKR point, so a column read by both sides (or by two same-κ blocks of
/// one side) is streamed and opened ONCE; later occurrences reuse the value.
fn known_claim(claims: &[ColumnClaim], col: usize, point: &[F192]) -> Option<F192> {
    claims
        .iter()
        .find(|c| c.col == col && c.point == point)
        .map(|c| c.value)
}

// One bus GKR point per cache; its prefixes are keyed by length and shared column identity.
type PublicEvals = HashMap<(usize, usize), F192>;

fn public_eval(vals: &Arc<Vec<F64>>, point: &[F192], cache: &mut PublicEvals) -> F192 {
    *cache
        .entry((Arc::as_ptr(vals) as usize, point.len()))
        .or_insert_with(|| primitives::multilinear::mle_eval_par(vals, point))
}

/// Prover-side decomposition: reads the real columns, writing each FRESH
/// committed value onto the stream and recording the matching claim
/// (block/coord order); duplicates reuse the recorded value.
///
/// The fresh column MLE evaluations run in a parallel first pass: within one
/// `decompose_formula` call no challenge is sampled between claims (`zeta`,
/// `alpha`, `beta` are fixed arguments and each claim's point is
/// `zeta[..kappa]` of its block), so the values are independent of the
/// transcript and only their `add_scalar` ORDER matters. The second pass
/// replays them through the transcript in the original block/coord order,
/// keeping the stream byte-identical to the serial form.
fn decompose_prove(
    blocks: &[Block],
    lay: &Layout,
    cols: &[&[F64]],
    zeta: &[F192],
    w: &[F192],
    beta: F192,
    owners: &[Option<(usize, usize)>],
    forms: &mut [BusForm],
    claims: &mut Vec<ColumnClaim>,
    public: &mut PublicEvals,
    ps: &mut ProverState,
) -> F192 {
    // Pass 1: enumerate the FRESH committed coords exactly as `decompose_formula`
    // visits them (blocks in order, coords in order, Col/GCol only, first
    // occurrence per `(col, point)`, the same dedup as `known_claim`), then
    // evaluate the column MLEs in parallel.
    let mut jobs: Vec<(usize, usize)> = Vec::new();
    for (b, blk) in blocks.iter().enumerate() {
        if owners[b].is_some() {
            continue;
        }
        for c in &blk.coords {
            if let Coord::Col(i) | Coord::GCol(i, _) = c {
                let fresh = known_claim(claims, *i, &zeta[..blk.kappa]).is_none() && !jobs.contains(&(*i, blk.kappa));
                if fresh {
                    jobs.push((*i, blk.kappa));
                }
            }
        }
    }
    // One evaluation at a time, each across the whole pool: a few long columns, one
    // per worker, would leave the rest of it idle.
    let vals: Vec<F192> = jobs
        .iter()
        .map(|&(col, kappa)| mle_eval_par(cols[col], &zeta[..kappa]))
        .collect();

    // Pass 2: replay in the original order; duplicates reuse the recorded claim.
    let mut fresh_iter = jobs.iter().zip(vals.iter());
    decompose_formula(
        blocks,
        lay,
        zeta,
        w,
        beta,
        owners,
        forms,
        claims,
        public,
        |col, zeta_lo| {
            let (&(jc, jk), &v) = fresh_iter
                .next()
                .expect("job enumeration matches decompose_formula's col_val order");
            debug_assert_eq!((jc, jk), (col, zeta_lo.len()), "job/coord order drift");
            debug_assert_eq!(v, mle_eval(cols[col], zeta_lo), "job/coord order drift");
            ps.add_scalar(v);
            v
        },
    )
}

/// Selector bits of the stacked bytecode polynomial: the public encoding
/// columns (opcode + ten operand/immediate slots = eleven) stack along
/// `2^N_BYTECODE_SELECTORS` slots. A column's slot is its bus tuple coordinate,
/// which is what fixes the width at sixteen rather than at the column count.
pub const N_BYTECODE_SELECTORS: usize = 4;

/// Slot of the first public column: the bytecode block leads with three
/// non-public coordinates (tag, index, read count), and a column's slot IS its
/// bus tuple coordinate.
pub const BYTECODE_PUBLIC_SLOT: usize = 3;

/// The stacked bytecode polynomial as a dense table: eleven public encoding
/// columns at their tuple coordinates, padded to sixteen selector slots. One
/// multilinear polynomial B̃ in `κ_bc + 4` variables, which is what a bus leaf
/// reads at `(ζ_lo, α⃗)` (§sec:e2e-bc); the outermost verifier evaluates it.
pub fn stacked_bytecode_table(blocks: &[Block]) -> Vec<F64> {
    let mut kbc = 0;
    let mut cols: Vec<&[F64]> = Vec::new();
    for blk in blocks {
        for c in &blk.coords {
            if let Coord::Public(vals) = c {
                kbc = blk.kappa;
                cols.push(vals.as_slice());
            }
        }
    }
    let mut table = vec![F64::ZERO; 1 << (N_BYTECODE_SELECTORS + kbc)];
    for (i, vals) in cols.into_iter().enumerate() {
        let slot = BYTECODE_PUBLIC_SLOT + i;
        assert!(slot < 1 << N_BYTECODE_SELECTORS, "a public slot is a tuple coordinate");
        assert_eq!(vals.len(), 1 << kbc);
        table[(slot << kbc)..((slot + 1) << kbc)].copy_from_slice(vals);
    }
    table
}

/// The three bus sides in `[push, pull, count]` order with their fingerprint
/// weights. The count channel's leaf is the count itself (a single `Col`), so it
/// runs at `α⃗ = 0` (weight `1` on slot `0`, zero elsewhere), `β = 0`, and its GKR
/// root is the product of all counts.
fn sides<'a>(
    blocks: [&'a [Block]; 3],
    lays: [&'a Layout; 3],
    w: &'a [F192],
    count_w: &'a [F192],
    beta: F192,
) -> [(&'a [Block], &'a Layout, &'a [F192], F192); 3] {
    [
        (blocks[0], lays[0], w, beta),
        (blocks[1], lays[1], w, beta),
        (blocks[2], lays[2], count_w, F192::ZERO),
    ]
}

/// Prove the bus balances; returns the per-column claims to open (§sec:leafstack). `alpha`/
/// `beta` follow the witness commitment (the only ordering the grand product
/// needs), and the block structure is public, so no shape is observed.
/// Everything the bus hands on: the framework blocks' column claims,
/// the shared GKR point (the table sumcheck's eq point), and
/// per side the tables' linear forms plus what each is claimed to sum to.
pub struct BusProof {
    pub claims: Vec<ColumnClaim>,
    /// The GKR point ζ: the zerocheck reuses it, so no fresh point is sampled.
    pub point: Vec<F192>,
    /// `forms[side][table]`, in `[push, pull, count]` order.
    pub forms: [Vec<BusForm>; 3],
    /// `sigmas[side][table]`: each form's eq-weighted sum over its table's rows.
    /// Prover-side only. NOTHING here travels: the batch's target is the caller's
    /// derived `Σ_s η^·totals[s]`, and the shares serve only to build each round's
    /// waiting line, which rides inside the round polynomial.
    pub sigmas: [Vec<F192>; 3],
}

pub fn prove_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    cols: &[&[F64]],
    owners: &[Vec<Option<(usize, usize)>>; 3],
    tables: &[(usize, usize)],
    ps: &mut ProverState,
) -> BusProof {
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let mut count_lay = layout(count);
    assert_grinding_unnecessary(push, pull, &push_lay, &pull_lay, &count_lay);
    let alphas: Vec<F192> = (0..N_TUPLE_BITS).map(|_| ps.sample()).collect();
    let w = fingerprint_weights(&alphas);
    let count_w = fingerprint_weights(&[F192::ZERO; N_TUPLE_BITS]);
    let beta = ps.sample();
    // The leaves keep the all-one padding implicit; decomposition uses the full logical depth.
    count_lay.mu = push_lay.mu;
    let leaves = crate::stage!("Bus leaves", || {
        build_leaves(
            sides(
                [push, pull, count],
                [&push_lay, &pull_lay, &count_lay],
                &w,
                &count_w,
                beta,
            ),
            cols,
        )
    });
    // All three trees run as ONE RLC-batched GKR (equal μ: push/pull match
    // block-for-block, count is padded), so every claim lands on ONE point ζ.
    let bus_gkr = crate::stage!("Bus GKR", || {
        gkr::prove_product_triple(leaves, ps, gkr::RootShape::FirstTwoShared)
    });

    // Framework blocks keep their per-column claims (deduped: push/pull share ζ);
    // every table block becomes a form for the zerocheck instead.
    let mut claims: Vec<ColumnClaim> = Vec::new();
    let sides = sides(
        [push, pull, count],
        [&push_lay, &pull_lay, &count_lay],
        &w,
        &count_w,
        beta,
    );
    // Each table's columns at ζ[..τ], computed once and shared by the three sides
    // (a form's linear part factors through them). Nothing here travels, neither the
    // evaluations nor any total: the verifier derives each side's table share as `Ṽ₀(ζ)` less the
    // framework decomposition and the batch settles it. A
    // transmitted total would appear in exactly one check, which it could always be
    // solved to satisfy, and would settle nothing.
    let mut forms = std::array::from_fn(|_| tables.iter().map(|&(_, n)| BusForm::new(n)).collect::<Vec<_>>());
    let mut frameworks = [F192::ZERO; 3];
    let mut public = PublicEvals::new();
    crate::stage!("Bus decompose", || {
        for (s, &(blocks, lay, a, g)) in sides.iter().enumerate() {
            frameworks[s] = decompose_prove(
                blocks,
                lay,
                cols,
                &bus_gkr.point,
                a,
                g,
                &owners[s],
                &mut forms[s],
                &mut claims,
                &mut public,
                ps,
            );
        }
    });
    let (table_evals, prod_sums) = crate::stage!("Bus tables", || tables_and_prods_at(
        cols,
        tables,
        &forms,
        &bus_gkr.point
    ));
    let sigmas: [Vec<F192>; 3] = std::array::from_fn(|s| {
        let sigmas: Vec<F192> = forms[s]
            .iter()
            .zip(&table_evals)
            .zip(&prod_sums)
            .map(|((f, e), p)| f.sum_at(e, p))
            .collect();
        // Completeness only: the verifier derives this identity rather than checking
        // it, so a mismatch here is a prover bug, not a rejection path.
        debug_assert_eq!(
            sigmas.iter().fold(frameworks[s], |acc, &b| acc + b),
            bus_gkr.values[s],
            "side {s} must decompose into its leaf value"
        );
        sigmas
    });

    BusProof {
        claims,
        point: bus_gkr.point,
        forms,
        sigmas,
    }
}

/// `Σ_z eq(point, z)·c(z)` for every column `c`, then `Σ_z eq(point, z)·a(z)·b(z)` for
/// every pair `(a, b)`, all in one parallel pass over the rows.
///
/// `eq` factors into a table over the low variables, packed for [`dot_base`] and
/// held in L1, and one over the rest that weights each block's reduced inner sums,
/// so every column moves only its own eight bytes a row and no `E` table of its
/// length is ever written.
fn eq_sums(point: &[F192], columns: &[&[F64]], pairs: &[(&[F64], &[F64])]) -> Vec<F192> {
    const LOW: usize = 10;
    if point.len() < 3 {
        let eq = eq_table(point);
        let dot = |f: &dyn Fn(usize) -> F64| {
            eq.iter()
                .enumerate()
                .fold(F192::ZERO, |acc, (z, &w)| acc + w.mul_base(f(z)))
        };
        return columns
            .iter()
            .map(|c| dot(&|z| c[z]))
            .chain(pairs.iter().map(|(a, b)| dot(&|z| a[z] * b[z])))
            .collect();
    }
    let low_vars = point.len().min(LOW);
    let low: Vec<Weights8> = eq_table(&point[..low_vars])
        .as_chunks::<8>()
        .0
        .iter()
        .map(Weights8::new)
        .collect();
    let high = eq_table(&point[low_vars..]);
    let width = 1usize << low_vars;
    parallel::fold_reduce(
        high.len(),
        || vec![F192::ZERO; columns.len() + pairs.len()],
        |acc, row| {
            let span = row * width..(row + 1) * width;
            let (singles, products) = acc.split_at_mut(columns.len());
            for (slot, c) in singles.iter_mut().zip(columns) {
                *slot += high[row] * dot_base(&low, &c[span.clone()]).reduce();
            }
            let mut product = [F64::ZERO; 1 << LOW];
            for (slot, (a, b)) in products.iter_mut().zip(pairs) {
                for ((p, &x), &y) in product.iter_mut().zip(&a[span.clone()]).zip(&b[span.clone()]) {
                    *p = x * y;
                }
                *slot += high[row] * dot_base(&low, &product[..width]).reduce();
            }
        },
        |mut left, right| {
            for (slot, part) in left.iter_mut().zip(right) {
                *slot += part;
            }
            left
        },
    )
}

/// Every table's committed columns at `ζ[..τ_t]`, and, for every column pair its
/// forms multiply, `Σ_z eq(ζ[..τ], z)·col_a(z)·col_b(z)`, in one pass per table
/// ([`eq_sums`]). Pairs are deduped across the three sides and the several blocks
/// that carry the same address, so an address costs one product however often it is
/// flushed. `tables[t] = (base, n_cols)` in the global schema; a pair names LOCAL
/// column indices.
#[allow(clippy::type_complexity)]
fn tables_and_prods_at(
    cols: &[&[F64]],
    tables: &[(usize, usize)],
    forms: &[Vec<BusForm>; 3],
    zeta: &[F192],
) -> (Vec<Vec<F192>>, Vec<Vec<(usize, usize, F192)>>) {
    tables
        .iter()
        .enumerate()
        .map(|(t, &(base, n_cols))| {
            let tau = crate::log2_strict_usize(cols[base].len());
            let mut pairs: Vec<(usize, usize)> = forms
                .iter()
                .flat_map(|side| side[t].prods.iter().map(|&(a, b, _)| (a, b)))
                .collect();
            pairs.sort_unstable();
            pairs.dedup();
            let columns = &cols[base..base + n_cols];
            let products: Vec<(&[F64], &[F64])> = pairs.iter().map(|&(a, b)| (columns[a], columns[b])).collect();
            let mut sums = eq_sums(&zeta[..tau], columns, &products);
            let prods = pairs
                .iter()
                .zip(&sums[n_cols..])
                .map(|(&(a, b), &s)| (a, b, s))
                .collect();
            sums.truncate(n_cols);
            (sums, prods)
        })
        .unzip()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr::{Leaves, RootShape, prove_product_triple};

    /// A coordinate's value at row `z`, from its definition.
    fn coord_value(c: &Coord, cols: &[&[F64]], z: usize) -> F64 {
        match c {
            Coord::Const(v) => *v,
            Coord::Col(i) => cols[*i][z],
            Coord::GCol(i, k) => g_pow(*k as usize) * cols[*i][z],
            Coord::Prod(i, j, k) => g_pow(*k as usize) * cols[*i][z] * cols[*j][z],
            Coord::Index => g_pow(z),
            Coord::Public(vals) => vals[z],
            Coord::Sum(cs) => cs.iter().fold(F64::ZERO, |acc, c| acc + coord_value(c, cols, z)),
        }
    }

    /// The leaves by their definition, every block at its offset.
    fn naive_leaves(blocks: &[Block], lay: &Layout, cols: &[&[F64]], w: &[F192], beta: F192) -> Vec<F192> {
        let len = blocks.iter().map(|b| 1 << b.kappa).sum::<usize>().max(1);
        let mut leaves = vec![F192::ONE; len];
        for (b, blk) in blocks.iter().enumerate() {
            for z in 0..blk.rows {
                leaves[lay.offsets[b] + z] = blk
                    .coords
                    .iter()
                    .zip(w)
                    .fold(beta, |acc, (c, &wi)| acc + wi.mul_base(coord_value(c, cols, z)));
            }
        }
        leaves
    }

    /// The builder's leaves and products are their definitions, and its identity runs
    /// leave the proof as it is.
    #[test]
    fn built_leaves_match_the_definition() {
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let columns: Vec<Vec<F64>> = (0..6).map(|_| (0..1 << 12).map(|_| F64(next())).collect()).collect();
        let cols: Vec<&[F64]> = columns.iter().map(Vec::as_slice).collect();
        let public = Arc::new((0..1 << 11).map(|_| F64(next())).collect::<Vec<_>>());
        let block = |kappa: usize, rows: usize, coords: Vec<Coord>| Block {
            kappa,
            rows,
            coords,
            padding: Vec::new(),
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
        let lays = [&push, &pull, &count].map(|b| layout(b));
        let w = fingerprint_weights(&[F192::new(3, 1, 4), F192::new(1, 5, 9), F192::new(2, 6, 5), F192::Y]);
        let count_w = fingerprint_weights(&[F192::ZERO; N_TUPLE_BITS]);
        let beta = F192::new(27, 18, 28);
        let sides = sides(
            [&push, &pull, &count],
            [&lays[0], &lays[1], &lays[2]],
            &w,
            &count_w,
            beta,
        );
        let want: [Vec<F192>; 3] = sides.map(|(blocks, lay, w, beta)| naive_leaves(blocks, lay, &cols, w, beta));

        let built = build_leaves(sides, &cols);
        for (got, want) in built.iter().zip(&want) {
            let reference = Leaves::new(want.clone());
            assert_eq!(
                (&got.values, &got.fours, &got.sixteens),
                (&reference.values, &reference.fours, &reference.sixteens)
            );
            assert!(
                got.ones
                    .iter()
                    .flat_map(Clone::clone)
                    .all(|i| got.values[i] == F192::ONE)
            );
        }
        assert!(built.iter().all(|leaves| !leaves.ones.is_empty()));
        let mut proofs = [ProverState::from_label(b"leaves"), ProverState::from_label(b"leaves")];
        let [ps0, ps1] = &mut proofs;
        let planned = prove_product_triple(built, ps0, RootShape::Distinct);
        let reference = prove_product_triple(want.map(Leaves::new), ps1, RootShape::Distinct);
        assert_eq!((planned.point, planned.values), (reference.point, reference.values));
        let [a, b] = proofs.map(|ps| ps.into_proof().stream);
        assert_eq!(a, b);
    }

    /// The bound is `(N_TUPLE_BITS + 1)·2^mu` plus the GKR terms: only the bus
    /// DEPTH costs bits now, the multilinear fingerprint having fixed each factor's
    /// degree at four in `α⃗` and one in `β`, whatever the tuple's width.
    #[test]
    fn bus_soundness_tracks_depth_only() {
        assert!(soundness_bits(38) >= crate::SECURITY_BITS);
        assert!(soundness_bits(61) >= crate::SECURITY_BITS);
        assert!(soundness_bits(62) < crate::SECURITY_BITS);
    }
}
