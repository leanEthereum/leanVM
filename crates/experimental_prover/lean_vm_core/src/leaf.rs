//! The bus: a single shared channel balanced by a grand product (§sec:gp through §sec:leafstack). Each
//! interaction wires a table's columns into width-`m` tuples and flushes them in a
//! direction; the bus balances when pushed and pulled tuples form the same
//! multiset, proven by grand products over the leaf vectors `β − π_α(σ)` under one
//! fingerprint `(α⃗, β)`, `α⃗` a weight per tuple slot, plus the count tree. One
//! batched GKR reduces the three trees to leaf claims `Ṽ₀(ζ)` at one point,
//! decomposed into evaluation claims on the committed columns. Tuple coordinates
//! `σ_i` are `K`-valued (column entries, g-powers, separators); the fingerprint
//! challenges `α, β` are `E`-valued, so a leaf accumulates via the mixed `mul_base`
//! product (2 PMULL per coordinate).

use crate::gkr;
use crate::transcript::ProverState;
use primitives::cast_slice;
use primitives::field::{F64, F128, F128Unreduced, g_pow, mul_by_g};
use primitives::multilinear::{eq_eval, interp, mle_eval_par};
use std::ops::Range;
use verifier::N_BUS_TREES;
use verifier::layout::BUS_BITS;

/// One tuple coordinate as a function of the block's row `z`.
#[derive(Clone, Debug)]
pub enum Coord {
    /// A public constant (domain separator, opcode, the seed count `1`).
    Const(F64),
    /// A committed column, value `col[z]`.
    Col(usize),
    /// `g^k · col[z]`, a virtual column (§sec:vm): a count's increment or the fall-through pc, `k = 1`.
    GCol(usize, u32),
    /// The product `g^k · col_a[z] · col_b[z]` of two committed columns. An address
    /// is `fp·g^o`, so this carries one on the bus without committing it: the
    /// coordinate IS the product, so no column can disagree with it and the binding
    /// constraint that used to say so is unnecessary (§sec:m3).
    Prod(usize, usize, u32),
    /// The index column `g^z` (§sec:idxcol), free via the factored MLE.
    Index,
    /// Column `s` of the stacked bytecode (§sec:e2e-bc, [`isa::Program::stacked_bytecode`]): public, not committed,
    /// both parties form its MLE.
    Public(usize),
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
/// the rest are a table's padding rows (§sec:e2e-pad), whose leaves are `1`.
#[derive(Clone, Debug)]
pub struct Block {
    pub kappa: usize,
    pub rows: usize,
    pub coords: Vec<Coord>,
}

impl Block {
    /// A block every row of which flushes.
    pub fn full(kappa: usize, coords: Vec<Coord>) -> Self {
        Self {
            kappa,
            rows: 1 << kappa,
            coords,
        }
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
    pub point: Vec<F128>,
    pub value: F128,
}

/// The count tree's weights: the count alone, in slot `0` (`α⃗ = (1, 0, …, 0)`, `β = 0`).
fn count_weights() -> Vec<F128> {
    let mut w = vec![F128::ZERO; 1 << BUS_BITS];
    w[0] = F128::ONE;
    w
}

/// Check the bus layout's shape. Push and pull have the same logical height, and the count
/// product is checked by the same GKR rather than by a separate root-at-random test.
fn check_bus_shape(push_blocks: &[Block], pull_blocks: &[Block], push: &Layout, pull: &Layout, count: &Layout) {
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
    assert!(widest <= 1 << BUS_BITS, "a tuple's coordinates index its slots");
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

/// A non-constant coordinate as `(source, coefficient)`: its leaf contribution is
/// the mixed product `coeff · source(z)` with `source(z) ∈ K`, `coeff ∈ E`.
/// `GCol` folds the `g^k` factor into the coefficient.
enum Term<'a> {
    Col(usize, F128),
    Prod(usize, usize, F128),
    Index(F128),
    Public(&'a [F64], F128),
}

/// Flatten one coordinate into leaf terms at coefficient `w`. A [`Coord::Sum`]
/// spreads its children over the SAME `w`: they are one coordinate, so they share
/// its `α`-power.
fn push_terms<'a>(c: &Coord, w: F128, public: &[&'a [F64]], terms: &mut Vec<Term<'a>>, constant: &mut F128) {
    match c {
        Coord::Const(v) => *constant += w.mul_base(*v),
        Coord::Col(i) => terms.push(Term::Col(*i, w)),
        Coord::GCol(i, k) => terms.push(Term::Col(*i, w.mul_base(g_pow(*k as usize)))),
        Coord::Prod(i, j, k) => {
            // A sum's products of one pair (a gated count's) share one term.
            let v = w.mul_base(g_pow(*k as usize));
            match terms.last_mut() {
                Some(Term::Prod(a, b, u)) if (*a, *b) == (*i, *j) => *u += v,
                _ => terms.push(Term::Prod(*i, *j, v)),
            }
        }
        Coord::Index => terms.push(Term::Index(w)),
        Coord::Public(s) => terms.push(Term::Public(public[*s], w)),
        Coord::Sum(cs) => {
            for c in cs {
                push_terms(c, w, public, terms, constant);
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
    const_part: F128,
    terms: Vec<Term<'a>>,
}

impl LeafBlock<'_> {
    /// The leaf of real row `z`, whose index column value `g^z` is `index`.
    #[inline]
    fn leaf(&self, z: usize, cols: &[&[F64]], index: F64) -> F128 {
        // The α-weighted coordinate sum defers its reductions: each mixed
        // product contributes its two raw limb products (2 PMULL, no
        // reduction tail), one combined reduction per row at the end,
        // bit-identical to summing reduced `mul_base` terms.
        let mut acc = F128Unreduced::ZERO;
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
    fn fill(&self, z0: usize, out: &mut [F128], cols: &[&[F64]]) {
        let real = self.rows.saturating_sub(z0).min(out.len());
        let (real_out, padding) = out.split_at_mut(real);
        // A padding row's leaf is the identity, so it leaves the product alone.
        padding.fill(F128::ONE);
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "vpclmulqdq"))]
        let done = self.fill_lanes(z0, real_out, cols);
        #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "vpclmulqdq")))]
        let done = 0;
        let mut index = g_pow(z0 + done);
        for (i, slot) in real_out.iter_mut().enumerate().skip(done) {
            *slot = self.leaf(z0 + i, cols, index);
            index = mul_by_g(index);
        }
    }

    /// [`fill`](Self::fill) [`lanes::N`] rows at a time, every term one lane-wise mixed
    /// product; returns how many rows it wrote.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "vpclmulqdq"))]
    fn fill_lanes(&self, z0: usize, out: &mut [F128], cols: &[&[F64]]) -> usize {
        use lanes::{E, K, Mixed, N};
        let load = |source: &[F64], z: usize| K::load(source[z..z + N].try_into().unwrap());
        // `g^z` for the `N` rows, stepped by `g^N`.
        let mut index = K::new(std::array::from_fn(|i| g_pow(z0 + i)));
        let step = K::splat(g_pow(N));
        let coeffs: Vec<E> = self
            .terms
            .iter()
            .map(|t| match t {
                Term::Col(_, c) | Term::Prod(_, _, c) | Term::Index(c) | Term::Public(_, c) => E::splat(*c),
            })
            .collect();
        let constant = E::splat(self.const_part);
        let (chunks, _) = out.as_chunks_mut::<N>();
        for (k, slot) in chunks.iter_mut().enumerate() {
            let z = z0 + N * k;
            let mut acc = Mixed::ZERO;
            for (t, &c) in self.terms.iter().zip(&coeffs) {
                match t {
                    Term::Col(i, _) => acc.add(c, load(cols[*i], z)),
                    Term::Prod(i, j, _) => acc.add(c, load(cols[*i], z) * load(cols[*j], z)),
                    Term::Index(_) => acc.add(c, index),
                    Term::Public(vals, _) => acc.add(c, load(vals, z)),
                }
            }
            index = index * step;
            (acc.reduce() + constant).store(slot);
        }
        N * chunks.len()
    }
}

/// The lane-wise kernels [`LeafBlock::fill_lanes`] runs on: eight lanes with AVX-512
/// ([`primitives::field::x8`]), four without ([`primitives::field::x4`]).
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
mod lanes {
    pub(super) use primitives::field::x8::{F64x8 as K, F128x8 as E, Mixed8 as Mixed};
    pub(super) const N: usize = 8;
}
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    target_feature = "vpclmulqdq",
    not(target_feature = "avx512f")
))]
mod lanes {
    pub(super) use primitives::field::x4::{F64x4 as K, F128x4 as E, Mixed4 as Mixed};
    pub(super) const N: usize = 4;
}

/// `dst[i] = ∏ src[4i..4i+4]`, an incomplete last four-tuple padded with the identity.
fn padded_products(src: &[F128], dst: &mut [F128]) {
    let full = src.len() / 4;
    gkr::products_into(&src[..4 * full], &mut dst[..full]);
    if full < dst.len() {
        dst[full] = src[4 * full..].iter().product();
    }
}

/// Build every tree's leaves: block `b` row `z` holds `β − Σ_i w_i c_i(z)` for the
/// tree's fingerprint weights `w`, followed implicitly by the identity `1`
/// up to `2^μ`. The row-invariant weights and constant coordinates are folded once
/// per block into its `const_part`.
///
/// The blocks of one height and row count (a table's push, pull and count blocks,
/// which read the same columns) are built together, a chunk of rows at a time, so a
/// column is read from memory once however many blocks flush it. Each chunk's four- and sixteen-tuple products, the GKR's levels two and four,
/// are formed while it is in cache.
pub(crate) fn build_leaves(
    sides: [(&[Block], &Layout, &[F128], F128); N_BUS_TREES],
    cols: &[&[F64]],
    public: &[&[F64]],
) -> [gkr::Leaves; N_BUS_TREES] {
    /// Rows staged at a time: one block's chunk stays in L1 while its products are formed.
    const CHUNK: usize = 1 << 11;
    /// Leaves per task, whatever the group's block count, so that tasks balance.
    const TASK_LEAVES: usize = 1 << 15;
    /// Blocks below this height are left to a serial pass, being too small to own
    /// whole sixteen-tuples.
    const CHUNKED: usize = 4;

    let mut blocks: Vec<LeafBlock> = Vec::new();
    let mut lens = [1usize; N_BUS_TREES];
    for (side, &(side_blocks, lay, w, beta)) in sides.iter().enumerate() {
        // `verifier::stack_offsets` packs the power-of-two blocks contiguously from zero,
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
                push_terms(c, w[i], public, &mut terms, &mut const_part);
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

    // SAFETY: the blocks write every leaf of `0..n` (one identity leaf for a side
    // without blocks, below) before anything reads it.
    let mut values: [Vec<F128>; N_BUS_TREES] = lens.map(|n| unsafe { gkr::level(n) });
    // SAFETY: the chunks write the products of the tuples inside blocks of height
    // `CHUNKED` or more, and the serial pass below the rest.
    let mut fours: [Vec<F128>; N_BUS_TREES] = lens.map(|n| unsafe { gkr::level(n.div_ceil(4)) });
    let mut sixteens: [Vec<F128>; N_BUS_TREES] = lens.map(|n| unsafe { gkr::level(n.div_ceil(16)) });

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
            // At least one sixteen per task, or its `sixteens` would go unwritten.
            let rows = (TASK_LEAVES / group.len()).next_power_of_two().clamp(16, height);
            (0..height).step_by(rows).map(move |z| (g, z..z + rows))
        })
        .collect();
    let ptrs = [&mut values, &mut fours, &mut sixteens]
        .map(|level| level.each_mut().map(|v| parallel::SendPtr(v.as_mut_ptr())));
    parallel::for_each(tasks.len(), |task| {
        let (group, ref rows) = tasks[task];
        let mut stage = [F128::ZERO; CHUNK];
        let mut stage4 = [F128::ZERO; CHUNK / 4];
        let mut stage16 = [F128::ZERO; CHUNK / 16];
        // The GKR reads all three levels long after this pass has evicted them.
        let stream = primitives::stream::Stream::new();
        for z0 in rows.clone().step_by(CHUNK) {
            let len = CHUNK.min(rows.len());
            let (leaves, fours, sixteens) = (&mut stage[..len], &mut stage4[..len / 4], &mut stage16[..len / 16]);
            for blk in &groups[group] {
                blk.fill(z0, leaves, cols);
                // Past the block's real rows every leaf, and so every tuple's product, is the identity.
                let live = if gkr::SKIP_IDENTITY {
                    blk.rows.saturating_sub(z0).next_multiple_of(16).min(len)
                } else {
                    len
                };
                gkr::products_into(&leaves[..live], &mut fours[..live / 4]);
                gkr::products_into(&fours[..live / 4], &mut sixteens[..live / 16]);
                fours[live / 4..].fill(F128::ONE);
                sixteens[live / 16..].fill(F128::ONE);
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
            v[0] = F128::ONE;
        }
        // The tuples among the smallest blocks, the last ones padded with the identity.
        padded_products(&v[tail..], &mut fours[side][tail / 4..]);
        padded_products(&fours[side][tail / 4..], &mut sixteens[side][tail / 16..]);
    }
    let mut levels = values.into_iter().zip(fours).zip(sixteens).enumerate();
    std::array::from_fn(|_| {
        let (side, ((values, fours), sixteens)) = levels.next().expect("one level triple per tree");
        // The padding rows of the chunked blocks, by offset.
        let mut ones: Vec<_> = blocks
            .iter()
            .filter(|blk| blk.side == side && blk.kappa >= CHUNKED && blk.rows < 1 << blk.kappa)
            .map(|blk| blk.offset + blk.rows..blk.offset + (1 << blk.kappa))
            .collect();
        ones.sort_unstable_by_key(|r| r.start);
        gkr::Leaves {
            values,
            fours,
            sixteens,
            ones,
        }
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
    pub coeffs: Vec<F128>,
    /// `(col_a, col_b, coeff)` in LOCAL column indices.
    pub(crate) prods: Vec<(usize, usize, F128)>,
    pub constant: F128,
}

impl BusForm {
    /// The zero form over `n_cols` columns.
    pub(crate) fn new(n_cols: usize) -> Self {
        Self {
            coeffs: vec![F128::ZERO; n_cols],
            prods: Vec::new(),
            constant: F128::ZERO,
        }
    }

    /// The same form scaled by `w`. Every coefficient is `E`-valued already, so
    /// folding the side's `ξ`-power in here costs three multiplies once per table
    /// instead of one per row and round of the zerocheck.
    pub fn scaled(&self, w: F128) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(|&c| c * w).collect(),
            prods: self.prods.iter().map(|&(a, b, c)| (a, b, c * w)).collect(),
            constant: self.constant * w,
        }
    }

    /// The pointwise sum of several forms over the same columns. Their products are
    /// listed together, a pair named in two forms twice.
    pub fn sum(forms: impl IntoIterator<Item = Self>) -> Self {
        let mut forms = forms.into_iter();
        let mut out = forms.next().expect("a table has at least one bus form");
        for form in forms {
            assert_eq!(out.coeffs.len(), form.coeffs.len(), "forms over the same columns");
            for (slot, c) in out.coeffs.iter_mut().zip(form.coeffs) {
                *slot += c;
            }
            out.constant += form.constant;
            out.prods.extend(form.prods);
        }
        out
    }

    /// The form at one point, `evals` the columns' values there; only its degree-two terms when `quadratic`.
    #[cfg(test)]
    pub(crate) fn eval(&self, evals: &[F128], quadratic: bool) -> F128 {
        let linear = if quadratic { F128::ZERO } else { self.linear(evals) };
        self.prods
            .iter()
            .fold(linear, |acc, &(a, b, c)| acc + evals[a] * evals[b] * c)
    }

    /// `constant + Σ coeffs[i]·evals[i]`.
    #[cfg(test)]
    fn linear(&self, evals: &[F128]) -> F128 {
        self.coeffs
            .iter()
            .zip(evals)
            .fold(self.constant, |acc, (&w, &v)| acc + w * v)
    }
}

/// Accumulate one coordinate of a table's block into that table's form, at
/// coefficient `w`. A [`Coord::Sum`]'s children share `w`, so a derived value
/// lands as the several coefficients and products it is made of.
fn accumulate_form(c: &Coord, w: F128, base: usize, form: &mut BusForm) {
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

/// Look up an already-recorded claim on `(col, point)`. Push and pull share
/// their GKR point, so a column read by both sides (or by two same-κ blocks of
/// one side) is streamed and opened ONCE.
fn known_claim(claims: &[ColumnClaim], col: usize, point: &[F128]) -> bool {
    claims.iter().any(|c| c.col == col && c.point == point)
}

/// Walk one side's blocks. A block owned by table `t` (with column base `base`)
/// accumulates into `forms[t]`, for the table sumcheck to settle; a framework block's
/// committed columns are evaluated at `ζ[..κ]` and each FRESH value is written onto the
/// stream and recorded as a claim, in block/coord order.
fn decompose_prove(
    blocks: &[Block],
    lay: &Layout,
    cols: &[&[F64]],
    zeta: &[F128],
    w: &[F128],
    beta: F128,
    owners: &[Option<(usize, usize)>],
    forms: &mut [BusForm],
    claims: &mut Vec<ColumnClaim>,
    ps: &mut ProverState,
) {
    assert_eq!(zeta.len(), lay.mu);
    let mut jobs: Vec<(usize, usize)> = Vec::new();
    for (b, blk) in blocks.iter().enumerate() {
        let kappa = blk.kappa;
        if let Some((t, base)) = owners[b] {
            let sel = lay.offsets[b] >> kappa;
            let sel_bits: Vec<F128> = (0..(lay.mu - kappa))
                .map(|k| F128::new(((sel >> k) & 1) as u64, 0))
                .collect();
            let eq_hi = eq_eval(&sel_bits, &zeta[kappa..]);
            let form = &mut forms[t];
            form.constant += eq_hi * beta;
            for (i, c) in blk.coords.iter().enumerate() {
                accumulate_form(c, eq_hi * w[i], base, form);
            }
            continue;
        }
        for c in &blk.coords {
            if let Coord::Col(i) | Coord::GCol(i, _) = c
                && !known_claim(claims, *i, &zeta[..kappa])
                && !jobs.contains(&(*i, kappa))
            {
                jobs.push((*i, kappa));
            }
        }
    }
    // One evaluation at a time, each across the whole pool: a few long columns, one
    // per worker, would leave the rest of it idle.
    for (col, kappa) in jobs {
        let point = &zeta[..kappa];
        let value = mle_eval_par(cols[col], point);
        ps.add_scalar(value);
        claims.push(ColumnClaim {
            col,
            point: point.to_vec(),
            value,
        });
    }
}

/// The bus trees in GKR order (push, pull, count), each its blocks, layout, fingerprint
/// weights and `β`. The count channel's leaf is the count itself (a single `Col`), so it
/// runs at [`count_weights`], `β = 0`, and its GKR root is the product of all counts.
fn sides<'a>(
    blocks: [&'a [Block]; N_BUS_TREES],
    lays: [&'a Layout; N_BUS_TREES],
    w: &'a [F128],
    count_w: &'a [F128],
    beta: F128,
) -> [(&'a [Block], &'a Layout, &'a [F128], F128); N_BUS_TREES] {
    [
        (blocks[0], lays[0], w, beta),
        (blocks[1], lays[1], w, beta),
        (blocks[2], lays[2], count_w, F128::ZERO),
    ]
}

/// The program's share of a bytecode leaf, `S = Σ_x α_x·P(ζ_lo, x)` over the slots `x` of the
/// stacked bytecode `P` (§sec:e2e-bc), reduced to one evaluation of `P`. The stream: `S`, a
/// sumcheck of [`BUS_BITS`] degree-two rounds over `x`, the low bit bound first, ending at
/// `r⃗`, then `P(ζ_lo, r⃗)`, whose product with `α̃(r⃗)` the verifier checks against the last round.
fn prove_bytecode_share(push: &[Block], zeta: &[F128], w: &[F128], public: &[&[F64]], ps: &mut ProverState) {
    let block = push
        .iter()
        .find(|blk| blk.coords.iter().any(|c| matches!(c, Coord::Public(_))))
        .expect("the push side seeds the bytecode");
    let zeta_lo = &zeta[..block.kappa];
    let mut slots: Vec<F128> = (0..1 << BUS_BITS)
        .map(|x| match block.coords.get(x) {
            Some(Coord::Public(s)) => mle_eval_par(public[*s], zeta_lo),
            _ => F128::ZERO,
        })
        .collect();
    let mut weights = w.to_vec();
    ps.add_scalar(weights.iter().zip(&slots).map(|(&a, &p)| a * p).sum());
    for _ in 0..BUS_BITS {
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

/// Everything the bus hands on: the framework blocks' column claims,
/// the shared GKR point (the table sumcheck's eq point), and
/// per tree the tables' forms.
pub(crate) struct BusProof {
    pub claims: Vec<ColumnClaim>,
    /// The GKR point ζ: the zerocheck reuses it, so no fresh point is sampled.
    pub point: Vec<F128>,
    /// `forms[tree][table]`, in GKR order ([`N_BUS_TREES`]).
    pub forms: [Vec<BusForm>; N_BUS_TREES],
}

/// Prove the bus balances; returns the per-column claims to open (§sec:leafstack). The
/// fingerprint follows the witness commitment (the only ordering the grand product
/// needs), and the block structure is public, so no shape is observed.
///
/// The stream, in order: the [`verifier::bus_grinding_bits`] grind and the fingerprint `(α⃗, β)`; the
/// batched GKR ([`gkr::prove_products`]); the framework blocks' fresh column values; the
/// bytecode's share ([`prove_bytecode_share`]).
pub(crate) fn prove_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    cols: &[&[F64]],
    stacked_bytecode: &[u64],
    owners: &[Vec<Option<(usize, usize)>>; 3],
    tables: &[(usize, usize)],
    ps: &mut ProverState,
) -> BusProof {
    // The columns [`Coord::Public`] names.
    let public: Vec<&[F64]> = cast_slice(stacked_bytecode)
        .chunks_exact(stacked_bytecode.len() >> BUS_BITS)
        .collect();
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let mut count_lay = layout(count);
    check_bus_shape(push, pull, &push_lay, &pull_lay, &count_lay);
    let bits = verifier::bus_grinding_bits(push_lay.mu);
    tracing::info_span!("Bus grind", mu = push_lay.mu, bits).in_scope(|| ps.grind(bits));
    let w = ps.sample_vec(1 << BUS_BITS);
    let beta = ps.sample();
    let count_w = count_weights();
    // The leaves keep the all-one padding implicit; decomposition uses the full logical depth.
    count_lay.mu = push_lay.mu;
    let blocks = [push, pull, count];
    let lays = [&push_lay, &pull_lay, &count_lay];
    let sides = sides(blocks, lays, &w, &count_w, beta);
    let leaves = crate::stage!("Bus leaves", || build_leaves(sides, cols, &public));
    // All three trees run as ONE RLC-batched GKR (equal μ: push/pull match
    // block-for-block, count is padded), so every claim lands on ONE point ζ.
    let bus_gkr = crate::stage!("Bus GKR", || gkr::prove_products(leaves, ps));

    // Framework blocks keep their per-column claims (deduped: push/pull share ζ);
    // every table block becomes a form for the zerocheck instead.
    let mut claims: Vec<ColumnClaim> = Vec::new();
    // No table total travels: the verifier derives each tree's table share as `Ṽ₀(ζ)` less the
    // framework decomposition and the batch settles it. A transmitted total would appear in
    // exactly one check, which it could always be solved to satisfy, and would settle nothing.
    let mut forms = std::array::from_fn(|_| tables.iter().map(|&(_, n)| BusForm::new(n)).collect::<Vec<_>>());
    crate::stage!("Bus decompose", || {
        for (s, &(blocks, lay, a, g)) in sides.iter().enumerate() {
            decompose_prove(
                blocks,
                lay,
                cols,
                &bus_gkr.point,
                a,
                g,
                &owners[s],
                &mut forms[s],
                &mut claims,
                ps,
            );
        }
        prove_bytecode_share(push, &bus_gkr.point, &w, &public, ps);
    });

    BusProof {
        claims,
        point: bus_gkr.point,
        forms,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr::{Leaves, prove_products};

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
    fn naive_leaves(
        blocks: &[Block],
        lay: &Layout,
        cols: &[&[F64]],
        public: &[&[F64]],
        w: &[F128],
        beta: F128,
    ) -> Vec<F128> {
        let len = blocks.iter().map(|b| 1 << b.kappa).sum::<usize>().max(1);
        let mut leaves = vec![F128::ONE; len];
        for (b, blk) in blocks.iter().enumerate() {
            for z in 0..blk.rows {
                leaves[lay.offsets[b] + z] = blk
                    .coords
                    .iter()
                    .zip(w)
                    .fold(beta, |acc, (c, &wi)| acc + wi.mul_base(coord_value(c, cols, public, z)));
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
        let bytecode: Vec<F64> = (0..1 << 11).map(|_| F64(next())).collect();
        let public = [bytecode.as_slice()];
        let block = |kappa: usize, rows: usize, coords: Vec<Coord>| Block { kappa, rows, coords };
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
        let lays = [&push, &pull, &count].map(|b| layout(b));
        let w: Vec<F128> = (0..1 << BUS_BITS).map(|_| F128::new(next(), next())).collect();
        let count_w = count_weights();
        let beta = F128::new(27, 18);
        let sides = sides(
            [&push, &pull, &count],
            [&lays[0], &lays[1], &lays[2]],
            &w,
            &count_w,
            beta,
        );
        let want = sides.map(|(blocks, lay, w, beta)| naive_leaves(blocks, lay, &cols, &public, w, beta));

        let built = build_leaves(sides, &cols, &public);
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
                    .all(|i| got.values[i] == F128::ONE)
            );
        }
        assert!(built.iter().all(|leaves| !leaves.ones.is_empty()));
        // The GKR wants its first two products equal, so each side is paired with itself.
        let reference = want.map(Leaves::new);
        for side in [0, 1] {
            let pick = |l: &[Leaves; N_BUS_TREES]| [l[side].clone(), l[side].clone(), l[2].clone()];
            let mut proofs = [ProverState::from_label(b"leaves"), ProverState::from_label(b"leaves")];
            let [ps0, ps1] = &mut proofs;
            let planned = prove_products(pick(&built), ps0);
            let reference = prove_products(pick(&reference), ps1);
            assert_eq!((planned.point, planned.values), (reference.point, reference.values));
            let [a, b] = proofs.map(|ps| ps.into_proof().stream);
            assert_eq!(a, b);
        }
    }
}
