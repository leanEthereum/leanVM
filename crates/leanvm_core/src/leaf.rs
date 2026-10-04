//! The bus: a single shared channel balanced by a grand product (§sec:gp through §sec:leafstack). Each
//! interaction wires a table's columns into width-`m` tuples and flushes them in a
//! direction; the bus balances when pushed and pulled tuples form the same
//! multiset, proven by one batched GKR over the two sides' leaf vectors `β − π_α(σ)`,
//! the push side ending on the lookup arrays' producers, whose leaves are those raised
//! to the powers their multiplicities' bits select. Each side reduces to a leaf claim
//! `Ṽ₀(ζ)`, decomposed into evaluation claims on the committed columns. Tuple
//! coordinates `σ_i` are `K`-valued (column entries, separators, tags); the
//! fingerprint challenges `α, β` are `E`-valued, so a leaf accumulates via the mixed
//! `mul_base` product (2 PMULL per coordinate).

use crate::PAR_THRESHOLD;
use crate::colval::ColVal;
use crate::gkr;
use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192, F192Unreduced, int_index_mle};
use primitives::multilinear::{eq_eval, eq_table_arena, mle_eval};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use zk_alloc::ArenaVec;

/// One tuple coordinate as a function of the block's row `z`.
#[derive(Clone, Debug)]
pub enum Coord {
    /// A public constant (domain separator, opcode, a seed's timestamp).
    Const(F64),
    /// A committed column, value `col[z]`.
    Col(usize),
    /// The product `col_a[z] · col_b[z]` of two columns, carried on the bus without
    /// committing it: the coordinate IS the product, so no column can disagree with
    /// it and no constraint has to say so (§sec:m3).
    Prod(usize, usize),
    /// The integer index column `base ^ (z << shift)` (§sec:idxcol), the element
    /// whose bits are that integer's: what addresses a region whose cell `z` sits at
    /// `base + (z << shift)`. Free, its MLE being linear.
    IntIndex { base: F64, shift: u32 },
    /// A public column (the bytecode program, §sec:e2e-bc): not committed; both parties form
    /// its MLE directly, so it raises no claim. Shared rather than owned: a column is
    /// tens of megabytes at production sizes.
    Public(Arc<Vec<F64>>),
    /// A public column that is zero outside a few blocks (RAM as the run finds it,
    /// §sec:memchan): the verifier evaluates it in time proportional to the blocks,
    /// not to the column.
    Sparse(Arc<SparseColumn>),
    /// A sum of `Const`/`Col`/`Prod` terms: any degree-2 form over the
    /// table's columns, which is all §sec:m3 asks of a coordinate. This is what
    /// carries a value a row DERIVES from its columns (a branch's successor, what a
    /// jump writes to `rd`, a hash row's block addresses) without committing a column for it, and
    /// with it the identity that would have tied the two. Like [`Coord::Prod`],
    /// only a table's blocks may carry one: the table sumcheck settles them,
    /// while a framework block has to split into per-column openings.
    Sum(Vec<Self>),
}

impl Coord {
    /// The coordinate with every column index shifted by `base`: a table's local coordinate, made global.
    pub fn offset(self, base: usize) -> Self {
        match self {
            Self::Col(i) => Self::Col(base + i),
            Self::Prod(i, j) => Self::Prod(base + i, base + j),
            Self::Sum(cs) => Self::Sum(cs.into_iter().map(|c| c.offset(base)).collect()),
            other => other,
        }
    }
}

/// A public column of `2^log_len` words given by its nonzero stretches, each cut into
/// ALIGNED blocks: a power of two of words, at an offset that is a multiple of it. Such
/// a block's share of the column's multilinear extension is its own extension in the
/// low variables times the indicator of its offset's bits in the high ones.
#[derive(Debug)]
pub struct SparseColumn {
    log_len: usize,
    blocks: Vec<(usize, Vec<F64>)>,
    /// The column written out, which only the prover needs.
    dense: std::sync::OnceLock<Vec<F64>>,
}

impl SparseColumn {
    /// From `(offset, words)` stretches, which must not overlap.
    pub fn new(log_len: usize, stretches: &[(usize, &[u64])]) -> Self {
        let mut blocks = Vec::new();
        for &(mut at, mut words) in stretches {
            assert!(at + words.len() <= 1 << log_len, "a stretch runs past the column");
            while !words.is_empty() {
                // The largest aligned block starting here that the stretch still fills.
                let aligned = if at == 0 { usize::MAX } else { 1 << at.trailing_zeros() };
                let size = aligned.min(1 << words.len().ilog2());
                blocks.push((at, words[..size].iter().map(|&w| F64(w)).collect()));
                (at, words) = (at + size, &words[size..]);
            }
        }
        Self {
            log_len,
            blocks,
            dense: std::sync::OnceLock::new(),
        }
    }

    fn dense(&self) -> &[F64] {
        self.dense.get_or_init(|| {
            let mut column = vec![F64::ZERO; 1 << self.log_len];
            for (at, words) in &self.blocks {
                column[*at..at + words.len()].copy_from_slice(words);
            }
            column
        })
    }

    /// The column's multilinear extension at `point`.
    pub(crate) fn eval(&self, point: &[F192]) -> F192 {
        assert_eq!(point.len(), self.log_len);
        self.blocks.iter().fold(F192::ZERO, |acc, (at, words)| {
            let k = words.len().ilog2() as usize;
            let selector = point[k..].iter().enumerate().fold(F192::ONE, |s, (j, &z)| {
                s * if (at >> (k + j)) & 1 == 1 { z } else { z + F192::ONE }
            });
            acc + selector * primitives::multilinear::mle_eval(words, &point[..k])
        })
    }
}

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates. Every one of them is a
/// row the program executed, since a table's height is its row count (§sec:e2e-pad), so a
/// block has no padding rows to divide back out of the product.
#[derive(Clone, Debug)]
pub struct Block {
    pub kappa: usize,
    pub coords: Vec<Coord>,
    /// The table whose block it is, if any. A table's block becomes a form its table
    /// sumcheck settles; a framework block opens its columns at the bus point.
    pub owner: Option<usize>,
}

impl Block {
    /// A block no table owns.
    pub const fn framework(kappa: usize, coords: Vec<Coord>) -> Self {
        Self {
            kappa,
            coords,
            owner: None,
        }
    }

    /// A block of table `owner`.
    pub const fn table(owner: usize, kappa: usize, coords: Vec<Coord>) -> Self {
        Self {
            kappa,
            coords,
            owner: Some(owner),
        }
    }
}

/// A lookup array as its table side pushes it (§sec:lookup): `2^kappa` entries, entry `x`
/// the tuple `coords` at row `x`, pushed `m_x` times, `m_x` being the committed word
/// `col[x]` read as an integer. Bit `i` of it is a push block of its own, whose row `x`
/// is the entry's leaf raised to `2^i` where that bit is set and `1` where it is not, so
/// the bits' blocks together push entry `x` exactly `m_x` times. The bus reads the low
/// `bits` bits; the rest are zero.
#[derive(Clone, Debug)]
pub struct Producer {
    pub kappa: usize,
    pub coords: Vec<Coord>,
    pub col: usize,
    pub bits: usize,
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

/// Why the bus does not balance.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] fiat_shamir::transcript::Error),
    /// The grand products' GKR rejects.
    #[error(transparent)]
    Gkr(#[from] gkr::GkrError),
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

/// Bits indexing a bus tuple's coordinates: every tuple, the bytecode's widest at
/// fourteen, lives in the `2^4` slots of the bytecode encoding (§sec:m3, §sec:e2e-bc).
pub const N_TUPLE_BITS: usize = 4;

/// Conservative sum of the degree bounds for every random-challenge failure in
/// the bus argument. A side's product has at most `factors` linear factors, counted
/// with multiplicity, each `β - π_α(t)` of total degree `N_TUPLE_BITS` in `(α⃗, β)`:
/// `N_TUPLE_BITS` in `α⃗`, one in `β`, and the total degree of a sum is the larger.
/// The second term covers all radix-four GKR batching and sumcheck challenges.
fn soundness_degree_bound(factors: u128, mu: usize) -> u128 {
    assert!(mu < u128::BITS as usize, "bus layout is too large to bound");
    let fingerprint = N_TUPLE_BITS as u128 * factors;
    let gkr = 8u128 * (mu as u128 + 1).pow(2);
    fingerprint + gkr
}

fn soundness_bits(factors: u128, mu: usize) -> u32 {
    let degree = soundness_degree_bound(factors, mu);
    192u32.saturating_sub(u128::BITS - degree.leading_zeros())
}

/// The linear factors a side's product has, counted with multiplicity: one per row
/// of a block, and up to `2^bits - 1` per entry of a producer.
fn factors(blocks: &[Block], producers: &[Producer]) -> u128 {
    let rows: u128 = blocks.iter().map(|b| 1u128 << b.kappa).sum();
    rows + producers
        .iter()
        .map(|p| (1u128 << p.kappa) * ((1u128 << p.bits) - 1))
        .sum::<u128>()
}

/// Check that the 192-bit challenge field supplies the target bus soundness.
fn assert_grinding_unnecessary(push_blocks: &[Block], pull_blocks: &[Block], producers: &[Producer], mu: usize) {
    let widest = push_blocks
        .iter()
        .chain(pull_blocks)
        .map(|block| block.coords.len())
        .chain(producers.iter().map(|p| p.coords.len()))
        .max()
        .unwrap_or(0);
    assert!(widest <= 1 << N_TUPLE_BITS, "a tuple's coordinates index its slots");
    let factors = factors(push_blocks, producers).max(factors(pull_blocks, &[]));
    assert!(
        soundness_bits(factors, mu) >= crate::SECURITY_BITS,
        "bus layout exceeds the unground F192 soundness budget"
    );
}

/// Stack blocks largest-first at aligned offsets; `μ = ⌈log2 Σ 2^{κ_b}⌉`. A producer's
/// bits are blocks too, after `blocks`, in order.
pub fn layout(blocks: &[Block], producers: &[Producer]) -> Layout {
    let kappas: Vec<Option<usize>> = blocks
        .iter()
        .map(|b| b.kappa)
        .chain(producers.iter().flat_map(|p| std::iter::repeat_n(p.kappa, p.bits)))
        .map(Some)
        .collect();
    let (offsets, placed) = crate::witness::stack_offsets(&kappas);
    Layout {
        mu: crate::log2_ceil_usize(placed.max(1)),
        offsets,
    }
}

/// The leaves one side leaves unmatched on the other, as `(side, block, row)`, under
/// one fixed fingerprint: what to look at when a bus does not balance. A producer's
/// entry counts as its multiplicity's worth of leaves, reported as block
/// `push.len() + p` for producer `p`.
#[cfg(test)]
pub(crate) fn unmatched_leaves(
    push: &[Block],
    pull: &[Block],
    producers: &[Producer],
    cols: &[&[F64]],
) -> Vec<(&'static str, usize, usize)> {
    let alphas: Vec<F192> = (0..N_TUPLE_BITS as u64)
        .map(|i| F192::new(3 + i, 5 + 7 * i, 11))
        .collect();
    let (w, beta) = (fingerprint_weights(&alphas), F192::new(13, 17, 19));
    let side = |blocks: &[Block]| {
        let mut at = Vec::new();
        for (b, block) in blocks.iter().enumerate() {
            let mut leaves = vec![F192::ZERO; 1 << block.kappa];
            fill_tuple(&block.coords, cols, &w, beta, &mut leaves);
            at.extend(leaves.into_iter().enumerate().map(|(z, leaf)| (leaf, b, z)));
        }
        at
    };
    let (mut pushed, pulled) = (side(push), side(pull));
    for (p, producer) in producers.iter().enumerate() {
        let mut leaves = vec![F192::ZERO; 1 << producer.kappa];
        fill_tuple(&producer.coords, cols, &w, beta, &mut leaves);
        for (x, leaf) in leaves.into_iter().enumerate() {
            let m = cols[producer.col][x].0 & ((1u64 << producer.bits) - 1);
            pushed.extend(std::iter::repeat_n((leaf, push.len() + p, x), m as usize));
        }
    }
    let key = |leaf: &F192| (leaf.c0, leaf.c1, leaf.c2);
    let mut counts: HashMap<_, i64> = HashMap::new();
    for (leaf, ..) in &pushed {
        *counts.entry(key(leaf)).or_default() += 1;
    }
    for (leaf, ..) in &pulled {
        *counts.entry(key(leaf)).or_default() -= 1;
    }
    let unmatched = |name: &'static str, leaves: &[(F192, usize, usize)]| {
        leaves
            .iter()
            .filter(|(leaf, ..)| counts[&key(leaf)] != 0)
            .map(|&(_, b, z)| (name, b, z))
            .collect::<Vec<_>>()
    };
    [unmatched("push", &pushed), unmatched("pull", &pulled)].concat()
}

/// A non-constant coordinate as `(source, coefficient)`: its leaf contribution is
/// the mixed product `coeff · source(z)` with `source(z) ∈ K`, `coeff ∈ E`.
enum Term<'a> {
    Col(usize, F192),
    Prod(usize, usize, F192),
    IntIndex(F192, u32),
    Public(&'a [F64], F192),
}

/// Flatten one coordinate into leaf terms at coefficient `w`. A [`Coord::Sum`]
/// spreads its children over the SAME `w`: they are one coordinate, so they share
/// its `α`-power.
fn push_terms<'a>(c: &'a Coord, w: F192, terms: &mut Vec<Term<'a>>, constant: &mut F192) {
    match c {
        Coord::Const(v) => *constant += w.mul_base(*v),
        Coord::Col(i) => terms.push(Term::Col(*i, w)),
        Coord::Prod(i, j) => terms.push(Term::Prod(*i, *j, w)),
        Coord::IntIndex { base, shift } => {
            *constant += w.mul_base(*base);
            terms.push(Term::IntIndex(w, *shift));
        }
        Coord::Public(vals) => terms.push(Term::Public(vals.as_slice(), w)),
        Coord::Sparse(column) => terms.push(Term::Public(column.dense(), w)),
        Coord::Sum(cs) => {
            for c in cs {
                push_terms(c, w, terms, constant);
            }
        }
    }
}

/// One tuple's leaves, `β − Σ_i w_i c_i(z)` for every row `z`, into `dst`. The
/// row-invariant weights and constant coordinates are folded once into `const_part`.
fn fill_tuple(coords: &[Coord], cols: &[&[F64]], w: &[F192], beta: F192, dst: &mut [F192]) {
    let mut const_part = beta;
    let mut terms: Vec<Term> = Vec::with_capacity(coords.len());
    for (i, c) in coords.iter().enumerate() {
        push_terms(c, w[i], &mut terms, &mut const_part);
    }
    let row = |z: usize| -> F192 {
        // The α-weighted coordinate sum defers its reductions: each mixed
        // product contributes its three raw limb products (3 PMULL, no
        // reduction tail), one combined reduction per row at the end,
        // bit-identical to summing reduced `mul_base` terms.
        let mut acc = F192Unreduced::ZERO;
        for t in &terms {
            acc ^= match t {
                Term::Col(i, c) => c.mul_base_unreduced(cols[*i][z]),
                Term::Prod(i, j, c) => c.mul_base_unreduced(cols[*i][z] * cols[*j][z]),
                Term::IntIndex(c, shift) => c.mul_base_unreduced(F64((z as u64) << shift)),
                Term::Public(vals, c) => c.mul_base_unreduced(vals[z]),
            };
        }
        const_part + acc.reduce()
    };
    if dst.len() >= PAR_THRESHOLD {
        parallel::fill(dst, row);
    } else {
        for (z, slot) in dst.iter_mut().enumerate() {
            *slot = row(z);
        }
    }
}

/// Rows per task of the producers' per-bit passes.
const PRODUCER_CHUNK: usize = 1 << 12;

/// A producer's entries' leaves, `β − π_α(e_x)`, which its bits raise to their powers.
fn producer_leaves(p: &Producer, cols: &[&[F64]], w: &[F192], beta: F192) -> ArenaVec<F192> {
    let mut q = ArenaVec::with_capacity(1 << p.kappa);
    // SAFETY: `fill_tuple` writes every slot before anything reads one.
    unsafe { q.set_len(1 << p.kappa) };
    fill_tuple(&p.coords, cols, w, beta, &mut q);
    q
}

/// Build one side's leaf vector: block `b` row `z` holds `β − Σ_i w_i c_i(z)` for
/// the fingerprint weights `w = eq(α⃗, ·)`, then each producer's bit blocks, bit `i`'s
/// row `x` holding `(β − π_α(e_x))^{2^i}` where that bit of `m_x` is set and `1` where
/// it is not, followed implicitly by the identity `1` up to `2^μ`.
pub fn build_leaves(
    blocks: &[Block],
    producers: &[Producer],
    lay: &Layout,
    cols: &[&[F64]],
    w: &[F192],
    beta: F192,
) -> ArenaVec<F192> {
    let kappas: Vec<usize> = blocks
        .iter()
        .map(|b| b.kappa)
        .chain(producers.iter().flat_map(|p| std::iter::repeat_n(p.kappa, p.bits)))
        .collect();
    let explicit = kappas
        .iter()
        .zip(&lay.offsets)
        .map(|(&kappa, &offset)| offset + (1usize << kappa))
        .max()
        .unwrap_or(1);
    debug_assert!(explicit <= 1usize << lay.mu);
    // `stack_offsets` packs the power-of-two blocks contiguously from zero, so the
    // blocks tile `0..explicit` and every slot below is written by one of them: the
    // identity fill would be overwritten in full, and this is the largest buffer in
    // the proof. The `covered` test is what licenses skipping it, so a layout that
    // ever left a hole falls back to filling rather than reading uninitialized rows.
    // Capacity is rounded to whole four-tuples because `gkr::QuaternaryLayerState`
    // pads this level to that before reading it, and growing it here would copy it.
    let covered: usize = kappas.iter().map(|&kappa| 1usize << kappa).sum();
    let mut leaves = if covered == explicit {
        let mut values = ArenaVec::with_capacity(explicit.next_multiple_of(4));
        // SAFETY: the per-block fills below cover `0..explicit` exactly, and each
        // joins before this function returns.
        unsafe { values.set_len(explicit) };
        values
    } else {
        let mut values = ArenaVec::with_capacity(explicit.next_multiple_of(4));
        values.resize(explicit, F192::ONE);
        values
    };
    // Every row of every block is a real row: a table's height is exactly the
    // number of rows it executed (`cpu::filler`), so no block has padding rows
    // whose tuples would have to be divided back out of the product.
    for (b, blk) in blocks.iter().enumerate() {
        let off = lay.offsets[b];
        let dst = &mut leaves[off..off + (1usize << blk.kappa)];
        fill_tuple(&blk.coords, cols, w, beta, dst);
    }
    let mut b = blocks.len();
    for p in producers {
        let mut q = producer_leaves(p, cols, w, beta);
        let mult = cols[p.col];
        for bit in 0..p.bits {
            let off = lay.offsets[b];
            let dst = &mut leaves[off..off + (1usize << p.kappa)];
            // Bit `bit`'s leaves, then `q` squared in place for the next bit.
            parallel::chunks_mut2(dst, &mut q, PRODUCER_CHUNK, |ci, dst, q| {
                let mult = &mult[ci * PRODUCER_CHUNK..];
                for ((slot, q), m) in dst.iter_mut().zip(q.iter_mut()).zip(mult) {
                    *slot = if (m.0 >> bit) & 1 == 1 { *q } else { F192::ONE };
                    *q = q.square();
                }
            });
            b += 1;
        }
    }
    leaves
}

/// What the producer's air sums against `eq(ζ, ·)` (§sec:lookup): its bits as `E`
/// columns, then for each bit `i` the public column `(β − π_α(e_x))^{2^i} − 1`, so that
/// bit `i`'s leaf is `1 + b_i·P'_i`. Prover-side; the verifier evaluates the public
/// half itself, its program columns' share in a deferred claim.
pub fn producer_columns(p: &Producer, cols: &[&[F64]], w: &[F192], beta: F192) -> Vec<ArenaVec<F192>> {
    let mut q = producer_leaves(p, cols, w, beta);
    let mult = cols[p.col];
    let bits = (0..p.bits).map(|bit| {
        let mut column = ArenaVec::with_capacity(1 << p.kappa);
        column.extend(mult.iter().map(|m| F192::from(F64((m.0 >> bit) & 1))));
        column
    });
    let mut public = Vec::with_capacity(p.bits);
    for _ in 0..p.bits {
        let mut column = ArenaVec::with_capacity(1 << p.kappa);
        column.extend(q.iter().map(|&v| v + F192::ONE));
        public.push(column);
        parallel::for_each_mut(&mut q, |_, v| *v = v.square());
    }
    bits.chain(public).collect()
}

/// The producer's public half at `chi`, short of its program columns' share.
///
/// ```text
/// MLE(P_i)(chi) - 1 - D_i   for each bit i,   P_i(x) = beta^(2^i) + sum_s w_s^(2^i) c_s(x)^(2^i)
/// ```
///
/// - `D_i` is the program columns' share, left to a deferred claim.
/// - The Frobenius `a -> a^(2^i)` is additive, so a coordinate's power is as cheap as the coordinate.
/// - A constant stays one, and an integer index column stays affine in the bits.
pub fn producer_affine_evals(p: &Producer, w: &[F192], beta: F192, chi: &[F192]) -> Vec<F192> {
    assert_eq!(chi.len(), p.kappa);
    // Running `2^i`-th powers: the constant, each index coordinate's weight and monomials.
    let mut constant = beta;
    let mut affine: Vec<(F192, Vec<F64>)> = Vec::new();
    for (c, &weight) in p.coords.iter().zip(w) {
        match c {
            Coord::Const(v) => constant += weight.mul_base(*v),
            Coord::IntIndex { base, shift } => {
                constant += weight.mul_base(*base);
                affine.push((weight, (0..p.kappa).map(|k| F64(1 << (k as u32 + shift))).collect()));
            }
            Coord::Public(_) => {}
            _ => unreachable!("a producer's tuple is public"),
        }
    }
    let mut evals = Vec::with_capacity(p.bits);
    for _ in 0..p.bits {
        let mut eval = constant;
        for (weight, monomials) in &affine {
            eval += *weight
                * chi
                    .iter()
                    .zip(monomials)
                    .fold(F192::ZERO, |s, (z, &m)| s + z.mul_base(m));
        }
        evals.push(eval + F192::ONE);
        constant = constant.square();
        for (weight, monomials) in &mut affine {
            *weight = weight.square();
            monomials.iter_mut().for_each(|m| *m = *m * *m);
        }
    }
    evals
}

/// The program columns' share of a producer's public half at `chi`, under the twist `mu`.
///
/// ```text
/// sum_i mu_i D_i,   D_i = sum_x eq(chi, x) c(x)^(2^i),   c(x) = sum_s w_s c_s(x)
/// ```
///
/// The sum over `s` runs over the tuple's public coordinates.
/// Raising to `2^i` is additive, so it splits over the set bits `k` of each `c_s(x)`:
///
/// ```text
/// sum_i mu_i D_i = sum_{s,k} B_{s,k} sum_i mu_i (w_s 2^k)^(2^i),   B_{s,k} = sum_x eq(chi, x) bit_k(c_s(x))
/// ```
///
/// That is one pass over the columns, then a fixed cost per coordinate, bit and power.
pub(crate) fn producer_public_twist(coords: &[Coord], w: &[F192], chi: &[F192], twist: &[F192]) -> F192 {
    let eq = primitives::multilinear::eq_table(chi);
    let mut total = F192::ZERO;
    for (c, &weight) in coords.iter().zip(w) {
        let Coord::Public(vals) = c else { continue };
        assert_eq!(vals.len(), eq.len());
        let mut slices = [F192::ZERO; 64];
        for (&e, v) in eq.iter().zip(vals.iter()) {
            let mut bits = v.0;
            while bits != 0 {
                slices[bits.trailing_zeros() as usize] += e;
                bits &= bits - 1;
            }
        }
        // Running `2^i`-th powers of the weight and of each bit's element.
        let mut weight = weight;
        let mut basis: [F64; 64] = std::array::from_fn(|k| F64(1 << k));
        for &mu in twist {
            let sum = (slices.iter().zip(&basis)).fold(F192::ZERO, |s, (b, &g)| s + b.mul_base(g));
            total += mu * weight * sum;
            weight = weight.square();
            basis.iter_mut().for_each(|g| *g = *g * *g);
        }
    }
    total
}

/// One table's bus contribution on one side, as a form over that table's committed
/// columns: `Σ_c coeffs[c]·col_c(z) + Σ (a,b,c) c·col_a(z)·col_b(z) + constant`.
/// Every coefficient is a public function of `α`, `β` and the block selectors at
/// `ζ`, because a table's bus blocks carry only `Const`/`Col`/`Prod`
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
    /// instead of one per [`eval`](Self::eval), which the zerocheck calls per row
    /// per round.
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
    /// only ever wants a table's total, so its two bus sides collapse to one
    /// dot product and one product list: the row loop then reads the column
    /// values once for both rather than once each.
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

    /// [`eval_unreduced`](Self::eval_unreduced) on its own.
    pub fn eval<T: ColVal>(&self, evals: &[T]) -> F192 {
        T::reduce(self.eval_unreduced(evals, false))
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
        Coord::Prod(i, j) => form.prods.push((*i - base, *j - base, w)),
        Coord::Sum(cs) => {
            for c in cs {
                accumulate_form(c, w, base, form);
            }
        }
        Coord::IntIndex { .. } | Coord::Public(_) | Coord::Sparse(_) => {
            unreachable!("a table's bus block carries no virtual coordinate")
        }
    }
}

/// The weight `eq(sel_b, ζ_hi)` block `b`, of `2^kappa` rows, carries in `Ṽ₀(ζ)`.
fn selector(lay: &Layout, b: usize, kappa: usize, zeta: &[F192]) -> F192 {
    let sel = lay.offsets[b] >> kappa;
    let sel_bits: Vec<F192> = (0..(lay.mu - kappa))
        .map(|k| F192::new(((sel >> k) & 1) as u64, 0, 0))
        .collect();
    eq_eval(&sel_bits, &zeta[kappa..])
}

/// The framework blocks' column claims, deduplicated: push and pull share their GKR
/// point, so a column read by both sides (or by two same-κ blocks of one side) is
/// streamed and opened ONCE; later occurrences reuse the value. Alongside them, each
/// producer's weight on each of its bits' blocks, which its air owes the push side, and
/// the sparse public columns' shares, which the decomposition leaves out.
#[derive(Default)]
struct Openings {
    claims: Vec<ColumnClaim>,
    /// `(column, κ)` to the column's value at `ζ[..κ]`: every claim is at a prefix of
    /// the one bus point, so its length names it.
    known: HashMap<(usize, usize), F192>,
    public: PublicEvals,
    /// Per producer, its bits' blocks' selectors, in order.
    producers: Vec<Vec<F192>>,
    sparse: Vec<SparseShare>,
}

/// A sparse column's share `weight col(point)` of a side's leaf claim.
///
/// The decomposition leaves it to whoever holds the column: RAM's image is the program's.
#[derive(Clone, Debug)]
pub struct SparseShare {
    /// The column's weight in the leaf claim.
    pub weight: F192,
    /// The point at which the column is evaluated.
    pub point: Vec<F192>,
    /// The column.
    pub column: Arc<SparseColumn>,
}

/// Walk one side's blocks. A block owned by table `t` accumulates into `forms[t]`,
/// over the table's local columns (`tables[t]` is its `(base, width)`); a producer's
/// bit block leaves its selector in `open.producers`, its air's weight on that bit; the
/// framework blocks are decomposed into per-column claims, `fresh` supplying values not
/// already opened, and a sparse public column's share is left in `open.sparse`. Returns
/// the framework blocks' contribution to `Ṽ₀(ζ)` short of those shares, plus the
/// padding mass, so the caller can settle the side once the zerocheck has proven the
/// tables' forms and the producers' airs.
fn decompose_formula<F: FnMut(usize, &[F192]) -> Result<F192, Error>>(
    side: &Side,
    zeta: &[F192],
    tables: &[(usize, usize)],
    forms: &mut [BusForm],
    open: &mut Openings,
    mut fresh: F,
) -> Result<F192, Error> {
    let (lay, w, beta) = (&side.lay, &side.w, side.beta);
    assert_eq!(zeta.len(), lay.mu);
    let mut acc = F192::ZERO;
    let mut sel_sum = F192::ZERO;
    let mut b = side.blocks.len();
    for producer in side.producers {
        let selectors: Vec<F192> = (b..b + producer.bits)
            .map(|b| selector(lay, b, producer.kappa, zeta))
            .collect();
        sel_sum += selectors.iter().fold(F192::ZERO, |a, &s| a + s);
        open.producers.push(selectors);
        b += producer.bits;
    }
    for (b, blk) in side.blocks.iter().enumerate() {
        let kappa = blk.kappa;
        let zeta_lo = &zeta[..kappa];
        let eq_hi = selector(lay, b, kappa, zeta);
        sel_sum += eq_hi;

        // A table's block becomes a linear form the zerocheck will sum; only the
        // framework blocks (boundary, registers, memory) still open columns at ζ.
        if let Some(t) = blk.owner {
            let form = &mut forms[t];
            form.constant += eq_hi * beta;
            for (i, c) in blk.coords.iter().enumerate() {
                accumulate_form(c, eq_hi * w[i], tables[t].0, form);
            }
            continue;
        }

        // Column `i` at ζ_lo: reuse the recorded claim, else take a fresh value and
        // record it. The push ORDER is the stream order, so every coordinate that
        // needs a column value must go through here.
        let mut col_val = |i: usize| -> Result<F192, Error> {
            if let Some(&v) = open.known.get(&(i, kappa)) {
                return Ok(v);
            }
            let v = fresh(i, zeta_lo)?;
            open.known.insert((i, kappa), v);
            open.claims.push(ColumnClaim {
                col: i,
                point: zeta_lo.to_vec(),
                value: v,
            });
            Ok(v)
        };
        let mut inner = F192::ZERO;
        for (i, c) in blk.coords.iter().enumerate() {
            let coord_val = match c {
                Coord::Const(v) => F192::from(*v),
                Coord::IntIndex { base, shift } => int_index_mle(*base, *shift, zeta_lo),
                Coord::Col(i) => col_val(*i)?,
                Coord::Prod(..) | Coord::Sum(..) => {
                    unreachable!("only a table's bus block carries a degree-2 coordinate")
                }
                Coord::Public(vals) => public_eval(vals, zeta_lo, &mut open.public),
                Coord::Sparse(column) => {
                    open.sparse.push(SparseShare {
                        weight: eq_hi * w[i],
                        point: zeta_lo.to_vec(),
                        column: Arc::clone(column),
                    });
                    F192::ZERO
                }
            };
            inner += w[i] * coord_val;
        }
        acc += eq_hi * (beta + inner);
    }
    // The padding rows (identity `1`) contribute the leftover mass `1 - Σ_b sel_b`.
    Ok(acc + (F192::ONE + sel_sum))
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
    side: &Side,
    cols: &[&[F64]],
    zeta: &[F192],
    tables: &[(usize, usize)],
    forms: &mut [BusForm],
    open: &mut Openings,
    ps: &mut ProverState,
) -> F192 {
    // Pass 1: enumerate the FRESH committed coords exactly as `decompose_formula`
    // visits them (framework blocks in order, coords in order, Col only, first
    // occurrence per `(col, κ)`), then evaluate the column MLEs in parallel.
    let mut jobs: Vec<(usize, usize)> = Vec::new();
    let mut seen = HashSet::new();
    for blk in side.blocks.iter().filter(|b| b.owner.is_none()) {
        for c in &blk.coords {
            if let Coord::Col(i) = c {
                let key = (*i, blk.kappa);
                if !open.known.contains_key(&key) && seen.insert(key) {
                    jobs.push(key);
                }
            }
        }
    }
    let vals: Vec<F192> = parallel::map_collect(jobs.len(), |i| {
        let (col, kappa) = jobs[i];
        mle_eval(cols[col], &zeta[..kappa])
    });

    // Pass 2: replay in the original order; duplicates reuse the recorded claim.
    let mut fresh_iter = jobs.iter().zip(vals.iter());
    let framework = decompose_formula(side, zeta, tables, forms, open, |col, zeta_lo| {
        let (&(jc, jk), &v) = fresh_iter
            .next()
            .expect("job enumeration matches decompose_formula's col_val order");
        debug_assert_eq!((jc, jk), (col, zeta_lo.len()), "job/coord order drift");
        debug_assert_eq!(v, mle_eval(cols[col], zeta_lo), "job/coord order drift");
        ps.add_scalar(v);
        Ok(v)
    })
    .expect("prover decomposition is infallible");
    (open.sparse.drain(..)).fold(framework, |acc, s| acc + s.weight * s.column.eval(&s.point))
}

/// Selector bits of the stacked bytecode polynomial: the public encoding
/// columns stack along `2^N_BYTECODE_SELECTORS` slots. A column's slot is its bus
/// tuple coordinate, which is what fixes the width at sixteen rather than at the
/// column count.
pub const N_BYTECODE_SELECTORS: usize = 4;

/// Slot of the first public column: the bytecode tuple leads with two coordinates
/// that are not the program's (the separator and the address), and a column's slot IS
/// its bus tuple coordinate.
pub const BYTECODE_PUBLIC_SLOT: usize = 2;

/// The stacked bytecode polynomial as a dense table: the public encoding columns of a
/// `2^kbc`-entry tuple at their tuple coordinates, padded to sixteen selector slots.
/// The program's digest is taken over it ([`crate::cpu::Program`]).
pub fn stacked_bytecode_table(kbc: usize, coords: &[Coord]) -> Vec<F64> {
    let mut table = vec![F64::ZERO; 1 << (N_BYTECODE_SELECTORS + kbc)];
    for (slot, c) in coords.iter().enumerate() {
        if let Coord::Public(vals) = c {
            assert!(slot >= BYTECODE_PUBLIC_SLOT, "the program's columns follow the address");
            assert!(slot < 1 << N_BYTECODE_SELECTORS, "a public slot is a tuple coordinate");
            assert_eq!(vals.len(), 1 << kbc);
            table[(slot << kbc)..((slot + 1) << kbc)].copy_from_slice(vals);
        }
    }
    table
}

/// One bus side: its blocks and producers, where they stack, and its fingerprint
/// `(eq(α⃗, ·), β)`.
struct Side<'a> {
    blocks: &'a [Block],
    producers: &'a [Producer],
    lay: Layout,
    w: Vec<F192>,
    beta: F192,
}

/// The two bus sides in `[push, pull]` order, which both parties lay out and
/// fingerprint the same way before the GKR, and the fingerprint's challenges.
struct BusSetup<'a> {
    sides: [Side<'a>; 2],
    alphas: Vec<F192>,
}

impl<'a> BusSetup<'a> {
    /// Lay the sides out and sample the fingerprint. The push side ends on the
    /// producers' bits, which no pull pairs with, so the two sides no longer match block
    /// for block: the shorter tree is padded to the taller's depth (identity leaves),
    /// and both run as ONE RLC-batched GKR at ONE shared point.
    fn new(push: &'a [Block], pull: &'a [Block], producers: &'a [Producer], challenger: &mut impl Challenger) -> Self {
        let mut push_lay = layout(push, producers);
        let mut pull_lay = layout(pull, &[]);
        let mu = push_lay.mu.max(pull_lay.mu);
        assert_grinding_unnecessary(push, pull, producers, mu);
        (push_lay.mu, pull_lay.mu) = (mu, mu);
        let alphas: Vec<F192> = (0..N_TUPLE_BITS).map(|_| challenger.sample()).collect();
        let w = fingerprint_weights(&alphas);
        let beta = challenger.sample();
        Self {
            sides: [
                Side {
                    blocks: push,
                    producers,
                    lay: push_lay,
                    w: w.clone(),
                    beta,
                },
                Side {
                    blocks: pull,
                    producers: &[],
                    lay: pull_lay,
                    w,
                    beta,
                },
            ],
            alphas,
        }
    }

    /// The depth of the batched GKR.
    const fn mu(&self) -> usize {
        self.sides[0].lay.mu
    }

    /// Each table's form on every side, empty.
    fn empty_forms(tables: &[(usize, usize)]) -> [Vec<BusForm>; 2] {
        std::array::from_fn(|_| tables.iter().map(|&(_, n)| BusForm::new(n)).collect())
    }
}

/// What a producer's air is owed and summed over, prover-side: its weight on each
/// bit's block, its columns ([`producer_columns`]), and what its summand sums to
/// against `eq(ζ[..κ], ·)`.
pub struct ProducerProof {
    pub coefficients: Vec<F192>,
    pub columns: Vec<ArenaVec<F192>>,
    pub sigma: F192,
}

/// Prove the bus balances; returns the per-column claims to open (§sec:leafstack). `alpha`/
/// `beta` follow the witness commitment (the only ordering the grand product
/// needs), and the block structure is public, so no shape is observed.
/// Everything the bus hands on: the framework blocks' column claims,
/// the shared GKR point (the table sumcheck's eq point),
/// per side the tables' linear forms plus what each is claimed to sum to, and the
/// producers' share of the push side.
pub struct BusProof {
    pub claims: Vec<ColumnClaim>,
    /// The GKR point ζ: the zerocheck reuses it, so no fresh point is sampled.
    pub point: Vec<F192>,
    /// `forms[side][table]`, in `[push, pull]` order.
    pub forms: [Vec<BusForm>; 2],
    /// `sigmas[side][table]`: each form's eq-weighted sum over its table's rows.
    /// Prover-side only. NOTHING here travels: the batch's target is the caller's
    /// derived `Σ_s η^·totals[s]`, and the shares serve only to build each round's
    /// waiting line, which rides inside the round polynomial.
    pub sigmas: [Vec<F192>; 2],
    /// The producers' share of the push side, in their order.
    pub producers: Vec<ProducerProof>,
    /// The fingerprint weights `eq(α⃗, ·)` and `β`, which the producers' public
    /// columns are made of.
    pub weights: Vec<F192>,
    pub beta: F192,
}

pub fn prove_balance(
    push: &[Block],
    pull: &[Block],
    producers: &[Producer],
    cols: &[&[F64]],
    tables: &[(usize, usize)],
    ps: &mut ProverState,
) -> BusProof {
    let setup = BusSetup::new(push, pull, producers, ps);
    // Two independent leaf vectors, built one after another: each `build_leaves`
    // already fans its own blocks out across the whole pool, so nesting an outer
    // split on top would only add a barrier. The all-one padding stays implicit.
    let leaves = crate::stage!("Bus leaves", || {
        setup
            .sides
            .each_ref()
            .map(|side| build_leaves(side.blocks, side.producers, &side.lay, cols, &side.w, side.beta))
    });
    // Both trees run as ONE RLC-batched GKR, the shorter padded, so every claim lands
    // on ONE point ζ.
    let bus_gkr = crate::stage!("Bus GKR", || { gkr::prove_products(leaves, ps) });

    // Framework blocks keep their per-column claims (deduped: push/pull share ζ);
    // every table block becomes a form for the zerocheck instead, and every producer
    // bit a weight for its producer's air.
    // Each table's columns at ζ[..τ], computed once and shared by the two sides
    // (a form's linear part factors through them). Nothing here travels, neither the
    // evaluations nor any total: the verifier derives each side's table share as `Ṽ₀(ζ)` less the
    // framework decomposition ([`verify_balance`]) and the batch settles it. A
    // transmitted total would appear in exactly one check, which it could always be
    // solved to satisfy, and would settle nothing.
    let mut forms = BusSetup::empty_forms(tables);
    let mut frameworks = [F192::ZERO; 2];
    let mut open = Openings::default();
    crate::stage!("Bus decompose", || {
        for (s, side) in setup.sides.iter().enumerate() {
            frameworks[s] = decompose_prove(side, cols, &bus_gkr.point, tables, &mut forms[s], &mut open, ps);
        }
    });
    let (table_evals, prod_sums) = tables_and_prods_at(cols, tables, &forms, &bus_gkr.point);
    let [push_side, _] = &setup.sides;
    let (w, beta) = (push_side.w.clone(), push_side.beta);
    let producers: Vec<ProducerProof> = producers
        .iter()
        .zip(std::mem::take(&mut open.producers))
        .map(|(p, coefficients)| {
            let columns = producer_columns(p, cols, &w, beta);
            let eq = eq_table_arena(&bus_gkr.point[..p.kappa]);
            let (bits, public) = columns.split_at(p.bits);
            // Bit `i`'s block at ζ: `Σ_x eq(ζ, x)·(1 + b_i(x)·P'_i(x))`, the eq weights summing to one.
            let sigma = parallel::map_reduce(
                p.bits,
                || F192::ZERO,
                |i| {
                    let rows = eq.iter().zip(bits[i].iter().zip(public[i].iter()));
                    let sum = rows.fold(F192::ZERO, |s, (&e, (&b, &q))| s + e * b * q);
                    coefficients[i] * (F192::ONE + sum)
                },
                |a, b| a + b,
            );
            ProducerProof {
                coefficients,
                columns,
                sigma,
            }
        })
        .collect();
    let sigmas: [Vec<F192>; 2] = std::array::from_fn(|s| {
        let sigmas: Vec<F192> = forms[s]
            .iter()
            .zip(&table_evals)
            .zip(&prod_sums)
            .map(|((f, e), p)| f.sum_at(e, p))
            .collect();
        // Completeness only: the verifier derives this identity rather than checking
        // it, so a mismatch here is a prover bug, not a rejection path.
        let producers = if s == 0 {
            producers.iter().map(|p| p.sigma).collect()
        } else {
            Vec::new()
        };
        debug_assert_eq!(
            sigmas.iter().chain(&producers).fold(frameworks[s], |acc, &b| acc + b),
            bus_gkr.values[s],
            "side {s} must decompose into its leaf value"
        );
        sigmas
    });

    BusProof {
        claims: open.claims,
        point: bus_gkr.point,
        forms,
        sigmas,
        producers,
        weights: w,
        beta,
    }
}

/// Every table's committed columns at `ζ[..τ_t]`, and, for every column pair its
/// forms multiply, `Σ_z eq(ζ[..τ], z)·col_a(z)·col_b(z)`.
///
/// One eq table per table, streamed once past every column and every pair at
/// the same time. Evaluated apart these are `n_cols + n_pairs` fold ladders
/// over the same table at the same point, and a ladder lifts every `K` word it
/// reads into an `E` it writes and reads again, where a dot against the weights
/// moves the column's own eight bytes. Pairs are deduped across the two sides
/// and the several blocks that carry the same address, so an address costs one
/// pass however often it is flushed. `tables[t] = (base, n_cols)` in the global
/// schema; a pair names LOCAL column indices.
#[allow(clippy::type_complexity)]
fn tables_and_prods_at(
    cols: &[&[F64]],
    tables: &[(usize, usize)],
    forms: &[Vec<BusForm>; 2],
    zeta: &[F192],
) -> (Vec<Vec<F192>>, Vec<Vec<(usize, usize, F192)>>) {
    /// Rows per task: the eq slice a task reads stays in L2 while every column
    /// and pair accumulator sweeps past it.
    const ROWS: usize = 1 << 12;

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

            let eq = eq_table_arena(&zeta[..tau]);
            let n_acc = n_cols + pairs.len();
            let sums = parallel::fold_reduce(
                (1usize << tau).div_ceil(ROWS),
                || vec![F192Unreduced::ZERO; n_acc],
                |acc, chunk| {
                    let lo = chunk * ROWS;
                    let weights = &eq[lo..(lo + ROWS).min(1 << tau)];
                    let span = |c: usize| &cols[base + c][lo..lo + weights.len()];
                    for (c, slot) in acc[..n_cols].iter_mut().enumerate() {
                        for (&w, &v) in weights.iter().zip(span(c)) {
                            *slot ^= w.mul_base_unreduced(v);
                        }
                    }
                    for (&(a, b), slot) in pairs.iter().zip(&mut acc[n_cols..]) {
                        for ((&w, &x), &y) in weights.iter().zip(span(a)).zip(span(b)) {
                            *slot ^= w.mul_base_unreduced(x * y);
                        }
                    }
                },
                |mut left, right| {
                    for (slot, part) in left.iter_mut().zip(right) {
                        *slot ^= part;
                    }
                    left
                },
            );
            let evals = sums[..n_cols].iter().map(|s| s.reduce()).collect();
            let prods = pairs
                .iter()
                .zip(&sums[n_cols..])
                .map(|(&(a, b), s)| (a, b, s.reduce()))
                .collect();
            (evals, prods)
        })
        .unzip()
}

/// What [`verify_balance`] establishes: the per-column claims to open and the
/// table forms with their claimed sums.
pub struct BusVerify {
    pub claims: Vec<ColumnClaim>,
    /// The GKR point ζ, reused as the table sumcheck's eq point.
    pub point: Vec<F192>,
    /// `forms[side][table]`, for the zerocheck to settle.
    pub forms: [Vec<BusForm>; 2],
    /// Per producer, its weight on each bit's block.
    pub producers: Vec<Vec<F192>>,
    /// Per side, what the tables' and the producers' blocks owe its leaf claim:
    /// `Ṽ₀(ζ)` less the framework blocks' decomposition. Derived here, pinned by the
    /// batch's target. The sparse columns' shares are not in it.
    pub totals: [F192; 2],
    /// Per side, the sparse columns' shares: the tables owe `totals[s] + sum weight col(point)`.
    pub sparse: [Vec<SparseShare>; 2],
    /// The fingerprint's challenges `alpha`.
    pub alphas: Vec<F192>,
    /// The fingerprint weights `eq(alpha, .)` and `beta`, which the producers' public columns are made of.
    pub weights: Vec<F192>,
    pub beta: F192,
}

/// Verify the bus balances, oracle-free (the prover's committed values arrive on
/// the stream and are certified by `pcs`). Returns the per-column claims to open.
pub fn verify_balance(
    push: &[Block],
    pull: &[Block],
    producers: &[Producer],
    tables: &[(usize, usize)],
    vs: &mut VerifierState,
) -> Result<BusVerify, Error> {
    let setup = BusSetup::new(push, pull, producers, vs);
    let bus_gkr = gkr::verify_products::<2>(setup.mu(), vs)?;
    // Every row of every table is a real row (`cpu::filler`), so the two sides balance
    // outright: no padding tuples to divide back out, and no announced row counts whose
    // truthfulness the soundness argument would have to establish. The GKR sends ONE root
    // for both sides, so a prover cannot even state an unbalanced bus, and there is nothing
    // to check here.

    // Framework blocks decompose as before; the tables' blocks become linear forms and the
    // producers' bits weights on their airs. Each side's share of those is DERIVED from
    // `framework + Ṽ₀(ζ)` rather than checked here, the batch's target being what pins
    // it, so no table column is opened at ζ.
    let mut forms = BusSetup::empty_forms(tables);
    let mut totals = [F192::ZERO; 2];
    let mut sparse: [Vec<SparseShare>; 2] = Default::default();
    let mut open = Openings::default();
    for (s, side) in setup.sides.iter().enumerate() {
        let framework = decompose_formula(side, &bus_gkr.point, tables, &mut forms[s], &mut open, |_, _| {
            Ok(vs.next_scalar()?)
        })?;
        // What the tables owe this side: DERIVED, never read. A transmitted total
        // would be a free variable in its own check and would settle nothing; the
        // caller instead pins these against the batch's target.
        totals[s] = framework + bus_gkr.values[s];
        sparse[s] = std::mem::take(&mut open.sparse);
    }
    let [push_side, _] = setup.sides;

    Ok(BusVerify {
        claims: open.claims,
        point: bus_gkr.point,
        forms,
        producers: open.producers,
        totals,
        sparse,
        alphas: setup.alphas,
        weights: push_side.w,
        beta: push_side.beta,
    })
}

#[cfg(test)]
mod tests {
    use super::{F64, F192, SparseColumn, soundness_bits};

    /// A sparse column's block-wise evaluation is its dense multilinear extension,
    /// whatever the stretches' offsets and lengths.
    #[test]
    fn sparse_column_evaluates_as_its_dense_form() {
        let words: Vec<u64> = (1..=37).map(|i| i * 0x9e37_79b9_7f4a_7c15).collect();
        let column = SparseColumn::new(9, &[(0, &words[..4]), (5, &words[4..17]), (300, &words[17..])]);
        assert_eq!(
            column.dense()[5..18],
            words[4..17].iter().map(|&w| F64(w)).collect::<Vec<_>>()
        );
        assert_eq!(column.dense().iter().filter(|w| !w.is_zero()).count(), words.len());
        let point: Vec<F192> = (0..9).map(|i| F192::new(3 + i, 5 * i + 1, 7)).collect();
        assert_eq!(
            column.eval(&point),
            primitives::multilinear::mle_eval(column.dense(), &point)
        );
    }

    /// The bound is `N_TUPLE_BITS` per linear factor plus the GKR terms: the
    /// multilinear fingerprint fixes each factor's total degree at four, whatever
    /// the tuple's width.
    #[test]
    fn bus_soundness_tracks_factors() {
        assert!(soundness_bits(1 << 38, 38) >= crate::SECURITY_BITS);
        assert!(soundness_bits(1 << 61, 61) >= crate::SECURITY_BITS);
        assert!(soundness_bits(1 << 62, 62) < crate::SECURITY_BITS);
    }
}
