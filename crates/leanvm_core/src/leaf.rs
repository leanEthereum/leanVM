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

use crate::arith::{Arith, Native, Verifier};
use crate::colval::ColVal;
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
use crate::colval::PackedCoeffs;
use crate::gkr::GkrError;
use crate::rec::FixedColumn;
use crate::{PAR_THRESHOLD, gkr};
use fiat_shamir::transcript::{Challenger, ProverState, TranscriptError, Transmitter};
use parallel::Chunks;
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
use primitives::field::MixedSums8;
use primitives::field::{F64, F192, F192Unreduced, Weights8, dot_base};
#[cfg(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "pclmulqdq",
        not(target_feature = "vpclmulqdq")
    )
))]
use primitives::field::{F192x1, F192x1Unreduced};
#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "pclmulqdq",
        not(target_feature = "vpclmulqdq")
    )
)))]
use primitives::field::{mul2, mul4};
use primitives::multilinear::{eq_table, mle_eval};
use std::collections::{HashMap, HashSet};
use std::convert::Infallible;
use std::mem::MaybeUninit;
use std::ops::Range;
use std::sync::{Arc, OnceLock};
use thiserror::Error;

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
    /// A committed column times a public constant, `c · col[z]`: what makes a coordinate depend on a 0 or 1 column
    /// (an extension-field row's `base` bit choosing between two separators).
    Scaled(F64, usize),
    /// The integer index column `base ^ (z << shift)` (§sec:idxcol), the element
    /// whose bits are that integer's: what addresses a region whose cell `z` sits at
    /// `base + (z << shift)`. Free, its MLE being linear.
    IntIndex { base: F64, shift: u32 },
    /// A public column (the bytecode program, §sec:e2e-bc): not committed; both parties form
    /// its MLE directly, so it raises no claim. Shared rather than owned: a column is
    /// tens of megabytes at production sizes.
    Public(PublicColumn),
    /// A public column that is zero outside a few blocks (RAM as the run finds it,
    /// §sec:memchan): the verifier evaluates it in time proportional to the blocks,
    /// not to the column.
    Sparse(Arc<SparseColumn>),
    /// A sum of `Const`/`Col`/`Prod`/`Scaled` terms: any degree-2 form over the
    /// table's columns, which is all §sec:m3 asks of a coordinate. This is what
    /// carries a value a row DERIVES from its columns (a branch's successor, what a
    /// jump writes to `rd`, a hash row's block addresses) without committing a column for it, and
    /// with it the identity that would have tied the two. Like [`Coord::Prod`],
    /// only a table's blocks may carry one: the table sumcheck settles them,
    /// while a framework block has to split into per-column openings.
    Sum(Vec<Self>),
}

/// A public column's words, and which fixed column of a recursion circuit they are, if any.
#[derive(Clone, Debug)]
pub struct PublicColumn {
    /// The words.
    pub values: Arc<Vec<F64>>,
    /// The recursion circuit's fixed column the words are, whose evaluation a recursive verifier takes as a hint.
    pub(crate) fixed: Option<FixedColumn>,
}

impl PublicColumn {
    /// A column that is no recursion circuit's fixed column.
    pub const fn new(values: Arc<Vec<F64>>) -> Self {
        Self { values, fixed: None }
    }

    /// A recursion circuit's fixed column.
    pub(crate) const fn fixed(values: Arc<Vec<F64>>, column: FixedColumn) -> Self {
        Self {
            values,
            fixed: Some(column),
        }
    }
}

impl Coord {
    /// Whether the coordinate is linear in the columns: it multiplies no column by another.
    pub fn is_linear(&self) -> bool {
        match self {
            Self::Prod(..) => false,
            Self::Sum(terms) => terms.iter().all(Self::is_linear),
            _ => true,
        }
    }

    /// The coordinate with every column index shifted by `base`: a table's local coordinate, made global.
    pub fn offset(self, base: usize) -> Self {
        match self {
            Self::Col(i) => Self::Col(base + i),
            Self::Prod(i, j) => Self::Prod(base + i, base + j),
            Self::Scaled(c, i) => Self::Scaled(c, base + i),
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
    dense: OnceLock<Vec<F64>>,
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
            dense: OnceLock::new(),
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
pub struct ColumnClaim<E = F192> {
    pub col: usize,
    pub point: Vec<E>,
    pub value: E,
}

/// Why the bus does not balance.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum BusError {
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// The grand products' GKR rejects.
    #[error(transparent)]
    Gkr(#[from] GkrError),
    /// The layout has too many factors for the challenge field and its grinding to give the bus its margin.
    #[error("the bus layout gives {bits} bits of soundness and {grinding} of grinding, below {required}")]
    Soundness { bits: u32, grinding: u32, required: u32 },
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

/// Bits the bus must clear: the target, plus what the commitment's list costs.
///
/// The fingerprint and the GKR challenges are drawn after the root, which binds the prover only to a list of polynomials.
/// Each challenge must hold against every member, so its error is multiplied by the list size (§sec:e2e-ledger).
const BUS_SOUNDNESS_BITS: u32 = crate::SECURITY_BITS + ::pcs::whir::L0_LIST_BITS as u32;

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

/// Check that the 192-bit challenge field and the grinding give the bus its margin.
///
/// # Why grinding counts
///
/// - A proof of work of `g` bits before the fingerprint challenges makes each draw of them cost `2^g` hashes.
/// - So the fingerprint's error counts `g` bits fewer against the margin (§sec:e2e-ledger).
/// - The GKR's own terms are far below the margin, so the grinding before the fingerprint covers the sum.
///
/// # Errors
///
/// A layout whose products have too many factors for the margin.
fn check_soundness(
    push_blocks: &[Block],
    pull_blocks: &[Block],
    producers: &[Producer],
    mu: usize,
    grinding: u32,
) -> Result<(), BusError> {
    let widest = push_blocks
        .iter()
        .chain(pull_blocks)
        .map(|block| block.coords.len())
        .chain(producers.iter().map(|p| p.coords.len()))
        .max()
        .unwrap_or(0);
    assert!(widest <= 1 << N_TUPLE_BITS, "a tuple's coordinates index its slots");
    let factors = factors(push_blocks, producers).max(factors(pull_blocks, &[]));
    let bits = soundness_bits(factors, mu);
    if bits + grinding < BUS_SOUNDNESS_BITS {
        return Err(BusError::Soundness {
            bits,
            grinding,
            required: BUS_SOUNDNESS_BITS,
        });
    }
    Ok(())
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
        Coord::Scaled(c, i) => terms.push(Term::Col(*i, w.mul_base(*c))),
        Coord::IntIndex { base, shift } => {
            *constant += w.mul_base(*base);
            terms.push(Term::IntIndex(w, *shift));
        }
        Coord::Public(column) => terms.push(Term::Public(column.values.as_slice(), w)),
        Coord::Sparse(column) => terms.push(Term::Public(column.dense(), w)),
        Coord::Sum(cs) => {
            for c in cs {
                push_terms(c, w, terms, constant);
            }
        }
    }
}

/// Rows per task of a block's leaf fill, a multiple of eight.
const LEAF_CHUNK: usize = 1 << 10;

/// One tuple's leaves, `β − Σ_i w_i c_i(z)` for every row `z`, into `dst`. The
/// row-invariant weights and constant coordinates are folded once into `const_part`.
///
/// With `products`, also the leaves' [`gkr::next_level`] while they are in registers:
/// `dst` then holds whole groups of eight rows, and `products` a quarter of its length.
fn fill_tuple(
    coords: &[Coord],
    cols: &[&[F64]],
    w: &[F192],
    beta: F192,
    dst: &mut [MaybeUninit<F192>],
    products: Option<&mut [MaybeUninit<F192>]>,
) {
    let mut const_part = beta;
    let mut terms: Vec<Term> = Vec::with_capacity(coords.len());
    for (i, c) in coords.iter().enumerate() {
        push_terms(c, w[i], &mut terms, &mut const_part);
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    )))]
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
    // Eight rows at once: each term's coefficient meets eight words in one batched
    // product, and the eight sums reduce together. Elsewhere one row at a time.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    let rows8 = |z: usize| -> [F192; 8] {
        let mut sums = MixedSums8::new();
        for t in &terms {
            let (c, k) = match t {
                Term::Col(i, c) => (c, *cols[*i][z..z + 8].as_array().unwrap()),
                Term::Prod(i, j, c) => (c, std::array::from_fn(|r| cols[*i][z + r] * cols[*j][z + r])),
                Term::IntIndex(c, shift) => (c, std::array::from_fn(|r| F64(((z + r) as u64) << shift))),
                Term::Public(vals, c) => (c, *vals[z..z + 8].as_array().unwrap()),
            };
            sums.add(*c, k);
        }
        sums.reduce().map(|s| const_part + s)
    };
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"),
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    )))]
    let rows8 = |z: usize| -> [F192; 8] { std::array::from_fn(|r| row(z + r)) };
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    )))]
    let fill = |base: usize, dst: &mut [MaybeUninit<F192>], products: Option<&mut [MaybeUninit<F192>]>| {
        let (groups, tail) = dst.as_chunks_mut::<8>();
        let tail_start = base + 8 * groups.len();
        if let Some(products) = products {
            debug_assert!(tail.is_empty() && products.len() == 2 * groups.len());
            for ((g, out), pair) in groups.iter_mut().enumerate().zip(products.as_chunks_mut::<2>().0) {
                let l = rows8(base + 8 * g);
                let [a, b, c, d] = mul4([l[0], l[2], l[4], l[6]], [l[1], l[3], l[5], l[7]]);
                pair.write_copy_of_slice(&mul2([a, c], [b, d]));
                out.write_copy_of_slice(&l);
            }
        } else {
            for (g, out) in groups.iter_mut().enumerate() {
                out.write_copy_of_slice(&rows8(base + 8 * g));
            }
        }
        for (r, slot) in tail.iter_mut().enumerate() {
            slot.write(row(tail_start + r));
        }
    };
    // One row at a time with every value in vector registers from its load to its store: the
    // terms' products summed unreduced and reduced once, and four rows' product formed from them.
    #[cfg(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    ))]
    let constant = F192x1::new(const_part);
    #[cfg(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    ))]
    let row = |z: usize| -> F192x1 {
        let mut acc = F192x1Unreduced::zero();
        for t in &terms {
            let (c, k) = match t {
                Term::Col(i, c) => (c, cols[*i][z]),
                Term::Prod(i, j, c) => (c, cols[*i][z] * cols[*j][z]),
                Term::IntIndex(c, shift) => (c, F64((z as u64) << shift)),
                Term::Public(vals, c) => (c, vals[z]),
            };
            acc ^= F192x1::load(c).mul_base_unreduced(k);
        }
        constant + acc.reduce()
    };
    #[cfg(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    ))]
    let fill = |base: usize, dst: &mut [MaybeUninit<F192>], products: Option<&mut [MaybeUninit<F192>]>| {
        if let Some(products) = products {
            let (quads, tail) = dst.as_chunks_mut::<4>();
            debug_assert!(tail.is_empty() && products.len() == quads.len());
            for ((q, [o0, o1, o2, o3]), product) in quads.iter_mut().enumerate().zip(products) {
                let z = base + 4 * q;
                let (a, b, c, d) = (row(z), row(z + 1), row(z + 2), row(z + 3));
                a.store(o0);
                b.store(o1);
                c.store(o2);
                d.store(o3);
                ((a * b) * (c * d)).store(product);
            }
        } else {
            for (r, slot) in dst.iter_mut().enumerate() {
                row(base + r).store(slot);
            }
        }
    };
    if dst.len() >= PAR_THRESHOLD {
        if let Some(products) = products {
            let products = Chunks::new(products, LEAF_CHUNK / 4);
            parallel::chunks_mut(dst, LEAF_CHUNK, |ci, chunk| {
                // SAFETY: task `ci` alone takes chunk `ci` of the products, the quarter of its rows.
                fill(ci * LEAF_CHUNK, chunk, Some(unsafe { products.get(ci) }));
            });
        } else {
            parallel::chunks_mut(dst, LEAF_CHUNK, |ci, chunk| fill(ci * LEAF_CHUNK, chunk, None));
        }
    } else {
        fill(0, dst, products);
    }
}

/// One tuple's leaves over `2^kappa` rows, in a vector of their own.
fn tuple_leaves(coords: &[Coord], kappa: usize, cols: &[&[F64]], w: &[F192], beta: F192) -> Vec<F192> {
    let mut leaves = Box::new_uninit_slice(1 << kappa);
    fill_tuple(coords, cols, w, beta, &mut leaves, None);
    // SAFETY: the fill wrote every slot.
    unsafe { leaves.assume_init() }.into_vec()
}

/// Rows per task of the producers' per-bit passes.
const PRODUCER_CHUNK: usize = 1 << 12;

/// A producer's entries' leaves, `β − π_α(e_x)`, which its bits raise to their powers.
fn producer_leaves(p: &Producer, cols: &[&[F64]], w: &[F192], beta: F192) -> Vec<F192> {
    tuple_leaves(&p.coords, p.kappa, cols, w, beta)
}

/// Build one side's leaf vector: block `b` row `z` holds `β − Σ_i w_i c_i(z)` for
/// the fingerprint weights `w = eq(α⃗, ·)`, then each producer's bit blocks, bit `i`'s
/// row `x` holding `(β − π_α(e_x))^{2^i}` where that bit of `m_x` is set and `1` where
/// it is not, followed implicitly by the identity `1` up to `2^μ`. Returns the leaves
/// and their first product level, `gkr::next_level`, formed for most blocks in the same pass.
pub fn build_leaves(
    blocks: &[Block],
    producers: &[Producer],
    lay: &Layout,
    cols: &[&[F64]],
    w: &[F192],
    beta: F192,
) -> (Vec<F192>, Vec<F192>) {
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
    // ever left a hole falls back to filling rather than leaving rows unwritten.
    // Capacity is rounded to whole four-tuples because `gkr::QuaternaryLayerState`
    // pads this level to that before reading it, and growing it here would copy it.
    let covered: usize = kappas.iter().map(|&kappa| 1usize << kappa).sum();
    let mut leaves = Vec::with_capacity(explicit.next_multiple_of(4));
    let slots = &mut leaves.spare_capacity_mut()[..explicit];
    if covered != explicit {
        slots.fill(MaybeUninit::new(F192::ONE));
    }
    let n_products = explicit.div_ceil(4);
    let mut products = Vec::with_capacity(n_products.next_multiple_of(4));
    let product_slots = &mut products.spare_capacity_mut()[..n_products];
    let mut fused: Vec<Range<usize>> = Vec::with_capacity(blocks.len());
    // Every row of every block is a real row: a table's height is exactly the
    // number of rows it executed (`cpu::filler`), so no block has padding rows
    // whose tuples would have to be divided back out of the product.
    for (b, blk) in blocks.iter().enumerate() {
        let (off, len) = (lay.offsets[b], 1usize << blk.kappa);
        let dst = &mut slots[off..off + len];
        // A block of eight rows or more starts at a multiple of its size, so its
        // four-tuples are its own.
        if blk.kappa >= 3 {
            debug_assert!(off.is_multiple_of(len), "a block starts at a multiple of its size");
            let products = &mut product_slots[off / 4..(off + len) / 4];
            fill_tuple(&blk.coords, cols, w, beta, dst, Some(products));
            fused.push(off / 4..(off + len) / 4);
        } else {
            fill_tuple(&blk.coords, cols, w, beta, dst, None);
        }
    }
    let mut b = blocks.len();
    for p in producers {
        let mut q = producer_leaves(p, cols, w, beta);
        let mult = cols[p.col];
        for bit in 0..p.bits {
            let off = lay.offsets[b];
            let dst = &mut slots[off..off + (1usize << p.kappa)];
            // Bit `bit`'s leaves, then `q` squared in place for the next bit.
            parallel::chunks_mut2(dst, &mut q, PRODUCER_CHUNK, |ci, dst, q| {
                let mult = &mult[ci * PRODUCER_CHUNK..];
                for ((slot, q), m) in dst.iter_mut().zip(q.iter_mut()).zip(mult) {
                    slot.write(if (m.0 >> bit) & 1 == 1 { *q } else { F192::ONE });
                    *q = q.square();
                }
            });
            b += 1;
        }
    }
    // SAFETY: the blocks tile `0..explicit` when they cover it, and the identity fill wrote it otherwise.
    unsafe { leaves.set_len(explicit) };
    // The products no block fill formed: the small blocks', the producers' and any hole's.
    fused.sort_unstable_by_key(|r| r.start);
    let mut start = 0;
    for r in fused.into_iter().chain(std::iter::once(n_products..n_products)) {
        if start < r.start {
            let dst = &mut product_slots[start..r.start];
            let product = |i: usize| gkr::padded_product(&leaves, start + i);
            if dst.len() >= PAR_THRESHOLD {
                parallel::fill(dst, |i| MaybeUninit::new(product(i)));
            } else {
                for (i, slot) in dst.iter_mut().enumerate() {
                    slot.write(product(i));
                }
            }
        }
        start = start.max(r.end);
    }
    // SAFETY: the block fills wrote the ranges in `fused`, and the pass above every slot between them.
    unsafe { products.set_len(n_products) };
    (leaves, products)
}

/// What the producer's air sums against `eq(ζ, ·)` (§sec:lookup): its bits as `E`
/// columns, then for each bit `i` the public column `(β − π_α(e_x))^{2^i} − 1`, so that
/// bit `i`'s leaf is `1 + b_i·P'_i`. Prover-side; the verifier evaluates the public
/// half itself, its program columns' share in a deferred claim.
pub fn producer_columns(p: &Producer, cols: &[&[F64]], w: &[F192], beta: F192) -> Vec<Vec<F192>> {
    let mut q = producer_leaves(p, cols, w, beta);
    let mult = cols[p.col];
    let bits = (0..p.bits).map(|bit| {
        let mut column = Vec::with_capacity(1 << p.kappa);
        column.extend(mult.iter().map(|m| F192::from(F64((m.0 >> bit) & 1))));
        column
    });
    let mut public = Vec::with_capacity(p.bits);
    for _ in 0..p.bits {
        let mut column = Vec::with_capacity(1 << p.kappa);
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
pub fn producer_affine_evals<A: Arith>(a: &mut A, p: &Producer, w: &[A::E], beta: A::E, chi: &[A::E]) -> Vec<A::E> {
    assert_eq!(chi.len(), p.kappa);
    // Running `2^i`-th powers: the constant, each index coordinate's weight and monomials.
    let mut constant = beta;
    let mut affine: Vec<(A::E, Vec<F64>)> = Vec::new();
    for (c, &weight) in p.coords.iter().zip(w) {
        match c {
            Coord::Const(v) => constant = a.mul_const_add(weight, F192::from(*v), constant),
            Coord::IntIndex { base, shift } => {
                constant = a.mul_const_add(weight, F192::from(*base), constant);
                affine.push((weight, (0..p.kappa).map(|k| F64(1 << (k as u32 + shift))).collect()));
            }
            Coord::Public(_) => {}
            _ => unreachable!("a producer's tuple is public"),
        }
    }
    let mut evals = Vec::with_capacity(p.bits);
    for bit in 0..p.bits {
        let mut eval = constant;
        for (weight, monomials) in &affine {
            let zero = a.zero();
            let x = (chi.iter().zip(monomials)).fold(zero, |s, (&z, &m)| a.mul_const_add(z, F192::from(m), s));
            eval = a.mul_add(*weight, x, eval);
        }
        evals.push(a.add_const(eval, F192::ONE));
        // The last bit's powers are never used.
        if bit + 1 < p.bits {
            constant = a.square(constant);
            for (weight, monomials) in &mut affine {
                *weight = a.square(*weight);
                monomials.iter_mut().for_each(|m| *m = *m * *m);
            }
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
        let Coord::Public(PublicColumn { values: vals, .. }) = c else {
            continue;
        };
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
/// `ζ`, because what a table's bus blocks carry besides `Const`/`Col`/`Prod`
/// coordinates is a top-level `IntIndex` or `Public` one, which the verifier
/// evaluates itself and which stays out of the form. The table sumcheck sums this against `eq(ζ[..τ], ·)` instead of
/// opening each column at `ζ`, which is why those per-column claims no longer reach
/// the PCS.
///
/// The quadratic part comes from [`Coord::Prod`] and is free: the AIR identities are
/// already degree 2, so a degree-2 form does not raise the round-polynomial degree
/// the batch pays for.
#[derive(Clone, Debug)]
pub struct BusForm<E = F192> {
    pub coeffs: Vec<E>,
    /// `(col_a, col_b, coeff)` in LOCAL column indices.
    pub prods: Vec<(usize, usize, E)>,
    pub constant: E,
}

impl<E: Copy> BusForm<E> {
    /// The zero form over `n_cols` columns.
    pub(crate) fn new(n_cols: usize, zero: E) -> Self {
        Self {
            coeffs: vec![zero; n_cols],
            prods: Vec::new(),
            constant: zero,
        }
    }

    /// The form's part linear in the columns `cols`, as a form over them alone, in their order.
    ///
    /// # Panics
    ///
    /// Panics if the form multiplies two columns.
    pub(crate) fn on(&self, cols: &[usize], zero: E) -> Self {
        assert!(self.prods.is_empty(), "a linear form");
        Self {
            coeffs: cols.iter().map(|&c| self.coeffs[c]).collect(),
            prods: Vec::new(),
            constant: zero,
        }
    }

    /// The form at the columns' values `evals`.
    pub fn at<A: Arith<E = E>>(&self, a: &mut A, evals: &[E]) -> E {
        let linear = (self.coeffs.iter().zip(evals)).fold(self.constant, |acc, (&c, &v)| a.mul_add(c, v, acc));
        self.prods.iter().fold(linear, |acc, &(i, j, c)| {
            let p = a.mul(evals[i], evals[j]);
            a.mul_add(c, p, acc)
        })
    }
}

impl BusForm {
    /// The form at the columns' values `evals`, in a verifier's arithmetic: its coefficients are constants.
    pub fn at_constants<A: Arith>(&self, a: &mut A, evals: &[A::E]) -> A::E {
        let constant = a.constant(self.constant);
        let linear = (self.coeffs.iter().zip(evals))
            .filter(|(c, _)| !c.is_zero())
            .fold(constant, |acc, (&c, &v)| a.mul_const_add(v, c, acc));
        self.prods.iter().fold(linear, |acc, &(i, j, c)| {
            let p = a.mul(evals[i], evals[j]);
            a.mul_const_add(p, c, acc)
        })
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
        let linear = if quadratic {
            T::lift(F192::ZERO)
        } else {
            T::dot_unreduced(&self.coeffs, evals) ^ T::lift(self.constant)
        };
        self.add_products(evals, linear)
    }

    /// `acc` plus the form's products at `evals`.
    #[inline(always)]
    fn add_products<T: ColVal>(&self, evals: &[T], acc: T::Unreduced) -> T::Unreduced {
        (self.prods.iter()).fold(acc, |acc, &(a, b, c)| acc ^ (evals[a] * evals[b]).mul_e_unreduced(c))
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

/// A form as the prover's table sumcheck evaluates it per row, on AVX-512 its linear
/// coefficients packed for [`dot_base`].
#[derive(Clone, Debug)]
pub struct PackedForm {
    form: BusForm,
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    packed: PackedCoeffs,
}

impl PackedForm {
    #[cfg_attr(
        not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")),
        expect(clippy::missing_const_for_fn, reason = "const only where nothing is packed")
    )]
    pub fn new(form: BusForm) -> Self {
        Self {
            #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
            packed: PackedCoeffs::new(&form.coeffs),
            form,
        }
    }

    /// [`BusForm::eval_unreduced`], on AVX-512 its linear part one batched dot product
    /// where `evals` is a row padded to the packed width.
    #[inline(always)]
    pub fn eval_unreduced<T: ColVal>(&self, evals: &[T], quadratic: bool) -> T::Unreduced {
        #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
        if !quadratic && evals.len() == self.packed.width() {
            let linear = T::dot_packed(&self.packed, evals) ^ T::lift(self.form.constant);
            return self.form.add_products(evals, linear);
        }
        self.form.eval_unreduced(evals, quadratic)
    }
}

/// Accumulate one coordinate of a table's block, at weight `w`, into that table's form at the block's selector `eq_hi`.
///
/// A constant joins the block's `constant`, which the selector multiplies once.
/// A sum's children share `w`, so a derived value lands as the coefficients and products it is made of.
impl<E: Copy> BusForm<E> {
    fn accumulate<A: Arith<E = E>>(
        &mut self,
        a: &mut A,
        c: &Coord,
        weight: BlockWeight<E>,
        base: usize,
        constant: &mut E,
    ) {
        let BlockWeight { selector, w } = weight;
        match c {
            Coord::Const(v) => *constant = a.mul_const_add(w, F192::from(*v), *constant),
            Coord::Col(i) => self.coeffs[*i - base] = a.mul_add(selector, w, self.coeffs[*i - base]),
            Coord::Prod(i, j) => {
                let product = a.mul(selector, w);
                self.prods.push((*i - base, *j - base, product));
            }
            Coord::Scaled(c, i) => {
                let product = a.mul(selector, w);
                self.coeffs[*i - base] = a.mul_const_add(product, F192::from(*c), self.coeffs[*i - base]);
            }
            Coord::Sum(cs) => {
                for c in cs {
                    self.accumulate(a, c, weight, base, constant);
                }
            }
            Coord::IntIndex { .. } | Coord::Public(_) | Coord::Sparse(_) => {
                unreachable!(
                    "a table's bus block carries a virtual coordinate only at the top level, and no sparse one"
                )
            }
        }
    }
}

/// A coordinate's weight in its side's leaf claim: its block's selector `eq(sel_b, zeta_hi)` times its fingerprint weight `w_i`.
#[derive(Clone, Copy)]
struct BlockWeight<E> {
    selector: E,
    w: E,
}

/// The framework blocks' column claims, deduplicated: push and pull share their GKR
/// point, so a column read by both sides (or by two same-κ blocks of one side) is
/// streamed and opened ONCE; later occurrences reuse the value. Alongside them, each
/// producer's weight on each of its bits' blocks, which its air owes the push side, and
/// the sparse public columns' shares, which the decomposition leaves out.
struct Openings<E> {
    claims: Vec<ColumnClaim<E>>,
    /// `(column, κ)` to the column's value at `ζ[..κ]`: every claim is at a prefix of
    /// the one bus point, so its length names it.
    known: HashMap<(usize, usize), E>,
    /// A public column's value at a prefix of the point, by the column's address and the prefix's length.
    public: HashMap<(usize, usize), E>,
    /// Per producer, its bits' blocks' selectors, in order.
    producers: Vec<Vec<E>>,
    /// The side's blocks' selectors, in order.
    selectors: Vec<E>,
    sparse: Vec<SparseShare<E>>,
}

impl<E: Copy> Openings<E> {
    /// A public column at a prefix of the bus point, evaluated once per column and prefix length.
    fn public<A: Arith<E = E>>(&mut self, a: &mut A, column: &PublicColumn, point: &[E]) -> E {
        let key = (Arc::as_ptr(&column.values) as usize, point.len());
        if let Some(&x) = self.public.get(&key) {
            return x;
        }
        let x = a.public_mle(column, point);
        self.public.insert(key, x);
        x
    }
}

impl<E> Default for Openings<E> {
    fn default() -> Self {
        Self {
            claims: Vec::new(),
            known: HashMap::new(),
            public: HashMap::new(),
            producers: Vec::new(),
            selectors: Vec::new(),
            sparse: Vec::new(),
        }
    }
}

/// A sparse column's share `weight col(point)` of a side's leaf claim.
///
/// The decomposition leaves it to whoever holds the column: RAM's image is the program's.
#[derive(Clone, Debug)]
pub struct SparseShare<E = F192> {
    /// The column's weight in the leaf claim.
    pub weight: E,
    /// The point at which the column is evaluated.
    pub point: Vec<E>,
    /// The column.
    pub column: Arc<SparseColumn>,
}

/// The bus fingerprint `(eq(alpha, .), beta)` and its challenges `alpha`.
struct Fingerprint<E> {
    alphas: Vec<E>,
    w: Vec<E>,
    beta: E,
}

impl Side<'_> {
    /// Walk one side's blocks at the GKR point `zeta`, and return the side's known part of its leaf claim.
    ///
    /// - A block owned by table `t` accumulates into `forms[t]`, over the table's local columns (`tables[t]` is its `(base, width)`).
    /// - Its `IntIndex` and `Public` coordinates are no columns: the verifier evaluates them, and they join the known part.
    /// - A producer's bit block leaves its selector in `open.producers`, its air's weight on that bit.
    /// - A framework block decomposes into per-column claims, `fresh` supplying the values not already opened.
    /// - A sparse public column's share is left in `open.sparse`.
    ///
    /// The known part is the framework blocks' contribution to `V_0(zeta)` short of the sparse shares, the tables' virtual coordinates, and the padding mass.
    #[expect(
        clippy::too_many_arguments,
        reason = "the side's fingerprint, point and the claims it extends"
    )]
    fn decompose<A: Arith, Er>(
        &self,
        a: &mut A,
        fp: &Fingerprint<A::E>,
        zeta: &[A::E],
        tables: &[(usize, usize)],
        forms: &mut [BusForm<A::E>],
        open: &mut Openings<A::E>,
        mut fresh: impl FnMut(&mut A, usize, &[A::E]) -> Result<A::E, Er>,
    ) -> Result<A::E, Er> {
        let (lay, w, beta) = (&self.lay, &fp.w, fp.beta);
        assert_eq!(zeta.len(), lay.mu);
        // The weight `eq(sel_b, zeta_hi)` block `b`, of `2^kappa` rows, carries in `V_0(zeta)`.
        let selector = |a: &mut A, b: usize, kappa: usize| a.eq_bits(lay.offsets[b] >> kappa, &zeta[kappa..]);
        let mut acc = a.zero();
        let mut sel_sum = a.one();
        let mut b = self.blocks.len();
        for producer in self.producers {
            let selectors: Vec<A::E> = (b..b + producer.bits).map(|b| selector(a, b, producer.kappa)).collect();
            sel_sum = selectors.iter().fold(sel_sum, |s, &e| a.add(s, e));
            open.producers.push(selectors);
            b += producer.bits;
        }
        for (b, blk) in self.blocks.iter().enumerate() {
            let kappa = blk.kappa;
            let zeta_lo = &zeta[..kappa];
            let eq_hi = selector(a, b, kappa);
            sel_sum = a.add(sel_sum, eq_hi);
            open.selectors.push(eq_hi);

            // A table's block becomes a linear form the zerocheck will sum; only the
            // framework blocks (boundary, registers, memory) still open columns at ζ.
            if let Some(t) = blk.owner {
                let form = &mut forms[t];
                let mut constant = beta;
                let mut known = a.zero();
                for (i, c) in blk.coords.iter().enumerate() {
                    match c {
                        Coord::IntIndex { base, shift } => {
                            let x = a.int_index(*base, *shift, zeta_lo);
                            known = a.mul_add(w[i], x, known);
                        }
                        Coord::Public(column) => {
                            let x = open.public(a, column, zeta_lo);
                            known = a.mul_add(w[i], x, known);
                        }
                        _ => form.accumulate(
                            a,
                            c,
                            BlockWeight {
                                selector: eq_hi,
                                w: w[i],
                            },
                            tables[t].0,
                            &mut constant,
                        ),
                    }
                }
                form.constant = a.mul_add(eq_hi, constant, form.constant);
                acc = a.mul_add(eq_hi, known, acc);
                continue;
            }

            // The block's leaf `beta + sum_i w_i c_i` at `zeta_lo`.
            //
            // A column's value is the recorded claim's, else a fresh one, recorded.
            // The push ORDER is the stream order, so every coordinate that needs a column value goes through here.
            let mut leaf = beta;
            for (i, c) in blk.coords.iter().enumerate() {
                leaf = match c {
                    Coord::Const(v) => a.mul_const_add(w[i], F192::from(*v), leaf),
                    Coord::IntIndex { base, shift } => {
                        let x = a.int_index(*base, *shift, zeta_lo);
                        a.mul_add(w[i], x, leaf)
                    }
                    Coord::Col(col) => {
                        let x = match open.known.get(&(*col, kappa)) {
                            Some(&x) => x,
                            None => {
                                let x = fresh(a, *col, zeta_lo)?;
                                open.known.insert((*col, kappa), x);
                                open.claims.push(ColumnClaim {
                                    col: *col,
                                    point: zeta_lo.to_vec(),
                                    value: x,
                                });
                                x
                            }
                        };
                        a.mul_add(w[i], x, leaf)
                    }
                    Coord::Prod(..) | Coord::Scaled(..) | Coord::Sum(..) => {
                        unreachable!("only a table's bus block carries a degree-2 coordinate")
                    }
                    Coord::Public(column) => {
                        let x = open.public(a, column, zeta_lo);
                        a.mul_add(w[i], x, leaf)
                    }
                    Coord::Sparse(column) => {
                        let weight = a.mul(eq_hi, w[i]);
                        open.sparse.push(SparseShare {
                            weight,
                            point: zeta_lo.to_vec(),
                            column: Arc::clone(column),
                        });
                        leaf
                    }
                };
            }
            acc = a.mul_add(eq_hi, leaf, acc);
        }
        // The padding rows (identity `1`) contribute the leftover mass `1 - sum_b sel_b`.
        Ok(a.add(acc, sel_sum))
    }

    /// Prover-side decomposition: reads the real columns, writing each FRESH
    /// committed value onto the stream and recording the matching claim
    /// (block/coord order); duplicates reuse the recorded value.
    ///
    /// The fresh column MLE evaluations run in a parallel first pass: within one
    /// decomposition no challenge is sampled between claims (`zeta`,
    /// `alpha`, `beta` are fixed arguments and each claim's point is
    /// `zeta[..kappa]` of its block), so the values are independent of the
    /// transcript and only their `add_scalar` ORDER matters. The second pass
    /// replays them through the transcript in the original block/coord order,
    /// keeping the stream byte-identical to the serial form.
    #[expect(
        clippy::too_many_arguments,
        reason = "the side's fingerprint, columns, point and the claims it extends"
    )]
    fn decompose_prove(
        &self,
        fp: &Fingerprint<F192>,
        cols: &[&[F64]],
        zeta: &[F192],
        tables: &[(usize, usize)],
        forms: &mut [BusForm],
        open: &mut Openings<F192>,
        ps: &mut ProverState,
    ) -> F192 {
        // Pass 1: enumerate the FRESH committed coords exactly as the decomposition
        // visits them (framework blocks in order, coords in order, Col only, first
        // occurrence per `(col, κ)`), then evaluate the column MLEs in parallel.
        let mut jobs: Vec<(usize, usize)> = Vec::new();
        let mut seen = HashSet::new();
        for blk in self.blocks.iter().filter(|b| b.owner.is_none()) {
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
        let framework = self.decompose(&mut Native, fp, zeta, tables, forms, open, |_, col, zeta_lo| {
            let (&(jc, jk), &v) = fresh_iter
                .next()
                .expect("job enumeration matches the decomposition's column order");
            debug_assert_eq!((jc, jk), (col, zeta_lo.len()), "job/coord order drift");
            debug_assert_eq!(v, mle_eval(cols[col], zeta_lo), "job/coord order drift");
            ps.add_scalar(v);
            Ok::<_, Infallible>(v)
        });
        let Ok(framework) = framework;
        (open.sparse.drain(..)).fold(framework, |acc, s| acc + s.weight * s.column.eval(&s.point))
    }
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
        if let Coord::Public(PublicColumn { values: vals, .. }) = c {
            assert!(slot >= BYTECODE_PUBLIC_SLOT, "the program's columns follow the address");
            assert!(slot < 1 << N_BYTECODE_SELECTORS, "a public slot is a tuple coordinate");
            assert_eq!(vals.len(), 1 << kbc);
            table[(slot << kbc)..((slot + 1) << kbc)].copy_from_slice(vals);
        }
    }
    table
}

/// One bus side: its blocks and producers, and where they stack.
struct Side<'a> {
    blocks: &'a [Block],
    producers: &'a [Producer],
    lay: Layout,
}

/// The two bus sides in `[push, pull]` order, which both parties lay out the same way before the GKR.
struct BusSetup<'a> {
    sides: [Side<'a>; 2],
    /// The proof-of-work bits before the fingerprint challenges.
    grinding: u32,
}

impl<'a> BusSetup<'a> {
    /// Lay the sides out. The push side ends on the
    /// producers' bits, which no pull pairs with, so the two sides no longer match block
    /// for block: the shorter tree is padded to the taller's depth (identity leaves),
    /// and both run as ONE RLC-batched GKR at ONE shared point.
    ///
    /// # Errors
    ///
    /// A layout too large for the bus's soundness margin at this grinding.
    fn new(push: &'a [Block], pull: &'a [Block], producers: &'a [Producer], grinding: u32) -> Result<Self, BusError> {
        let mut push_lay = layout(push, producers);
        let mut pull_lay = layout(pull, &[]);
        let mu = push_lay.mu.max(pull_lay.mu);
        check_soundness(push, pull, producers, mu, grinding)?;
        (push_lay.mu, pull_lay.mu) = (mu, mu);
        Ok(Self {
            grinding,
            sides: [
                Side {
                    blocks: push,
                    producers,
                    lay: push_lay,
                },
                Side {
                    blocks: pull,
                    producers: &[],
                    lay: pull_lay,
                },
            ],
        })
    }

    /// The depth of the batched GKR.
    const fn mu(&self) -> usize {
        self.sides[0].lay.mu
    }

    /// Each table's form on every side, empty.
    fn empty_forms<E: Copy>(tables: &[(usize, usize)], zero: E) -> [Vec<BusForm<E>>; 2] {
        std::array::from_fn(|_| tables.iter().map(|&(_, n)| BusForm::new(n, zero)).collect())
    }
}

/// What a producer's air is owed and summed over, prover-side: its weight on each
/// bit's block, its columns ([`producer_columns`]), and what its summand sums to
/// against `eq(ζ[..κ], ·)`.
pub struct ProducerProof {
    pub coefficients: Vec<F192>,
    pub columns: Vec<Vec<F192>>,
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
    /// Each table's columns at `ζ[..τ]`: what a table with linear forms sends in place of a sumcheck.
    pub evals: Vec<Vec<F192>>,
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

/// Prove the bus balances, after a proof of work of the given bits when there are any.
pub fn prove_balance(
    push: &[Block],
    pull: &[Block],
    producers: &[Producer],
    grinding: u32,
    cols: &[&[F64]],
    tables: &[(usize, usize)],
    ps: &mut ProverState,
) -> BusProof {
    let setup = BusSetup::new(push, pull, producers, grinding).expect("the size caps keep every bus layout sound");
    // No grinding sends no nonce.
    if setup.grinding > 0 {
        ps.grind(setup.grinding);
    }
    let alphas = ps.sample_vec(N_TUPLE_BITS);
    let fp = Fingerprint {
        w: fingerprint_weights(&alphas),
        alphas,
        beta: ps.sample(),
    };
    // Two independent leaf vectors, built one after another: each `build_leaves`
    // already fans its own blocks out across the whole pool, so nesting an outer
    // split on top would only add a barrier. The all-one padding stays implicit.
    let leaves = crate::stage!("Bus leaves", || {
        setup
            .sides
            .each_ref()
            .map(|side| build_leaves(side.blocks, side.producers, &side.lay, cols, &fp.w, fp.beta))
    });
    // Both trees run as ONE RLC-batched GKR, the shorter padded, so every claim lands
    // on ONE point ζ.
    let bus_gkr = crate::stage!("Bus GKR", || { gkr::prove_products(leaves, ps) });

    // Framework blocks keep their per-column claims (deduped: push/pull share ζ);
    // every table block becomes a form for the zerocheck instead, and every producer
    // bit a weight for its producer's air.
    // Each table's columns at ζ[..τ], computed once and shared by the two sides
    // (a form's linear part factors through them). No total travels: the verifier derives
    // each side's table share as `Ṽ₀(ζ)` less the framework decomposition (`verify_balance`).
    // The caller sends a linear table's evaluations, which the opening binds, and the batch
    // settles the rest. A transmitted total would appear in exactly one check, which it could
    // always be solved to satisfy, and would settle nothing.
    let mut forms = BusSetup::empty_forms(tables, F192::ZERO);
    let mut frameworks = [F192::ZERO; 2];
    let mut open = Openings::default();
    crate::stage!("Bus decompose", || {
        for (s, side) in setup.sides.iter().enumerate() {
            frameworks[s] = side.decompose_prove(&fp, cols, &bus_gkr.point, tables, &mut forms[s], &mut open, ps);
        }
    });
    let (table_evals, prod_sums) = tables_and_prods_at(cols, tables, &forms, &bus_gkr.point);
    let Fingerprint { w, beta, .. } = fp;
    let producers: Vec<ProducerProof> = producers
        .iter()
        .zip(std::mem::take(&mut open.producers))
        .map(|(p, coefficients)| {
            let columns = producer_columns(p, cols, &w, beta);
            let eq = eq_table(&bus_gkr.point[..p.kappa]);
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
        evals: table_evals,
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

            let eq = eq_table(&zeta[..tau]);
            let n_acc = n_cols + pairs.len();
            // A task packs its eq slice once, then every column and pair dots against it
            // eight rows at a time; a slice short of eight rows takes the scalar path.
            let sums = parallel::map_reduce_with_state(
                (1usize << tau).div_ceil(ROWS),
                || (Vec::with_capacity(ROWS / 8), Vec::with_capacity(ROWS)),
                || vec![F192Unreduced::ZERO; n_acc],
                |(packed, products): &mut (Vec<Weights8>, Vec<F64>), acc, chunk| {
                    let lo = chunk * ROWS;
                    let weights = &eq[lo..(lo + ROWS).min(1 << tau)];
                    let span = |c: usize| &cols[base + c][lo..lo + weights.len()];
                    let (blocks, tail) = weights.as_chunks::<8>();
                    let split = 8 * blocks.len();
                    packed.clear();
                    packed.extend(blocks.iter().map(Weights8::new));
                    let dot = |k: &[F64]| {
                        tail.iter()
                            .zip(&k[split..])
                            .fold(dot_base(packed, &k[..split]), |acc, (&w, &v)| {
                                acc ^ w.mul_base_unreduced(v)
                            })
                    };
                    for (c, slot) in acc[..n_cols].iter_mut().enumerate() {
                        *slot ^= dot(span(c));
                    }
                    for (&(a, b), slot) in pairs.iter().zip(&mut acc[n_cols..]) {
                        products.clear();
                        products.extend(span(a).iter().zip(span(b)).map(|(&x, &y)| x * y));
                        *slot ^= dot(products);
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
pub struct BusVerify<E = F192> {
    pub claims: Vec<ColumnClaim<E>>,
    /// The GKR point ζ, reused as the table sumcheck's eq point.
    pub point: Vec<E>,
    /// `forms[side][table]`, for the zerocheck to settle.
    pub forms: [Vec<BusForm<E>>; 2],
    /// Per producer, its weight on each bit's block.
    pub producers: Vec<Vec<E>>,
    /// Per side, what the tables' and the producers' blocks owe its leaf claim:
    /// `Ṽ₀(ζ)` less the framework blocks' decomposition and the tables' virtual
    /// coordinates. Derived here, pinned by the batch's target. The sparse columns' shares are not in it.
    pub totals: [E; 2],
    /// Per side, the sparse columns' shares: the tables owe `totals[s] + sum weight col(point)`.
    pub sparse: [Vec<SparseShare<E>>; 2],
    /// Per side, each block's selector `eq(sel_b, zeta_hi)`, in block order.
    pub selectors: [Vec<E>; 2],
    /// The fingerprint's challenges `alpha`.
    pub alphas: Vec<E>,
    /// The fingerprint weights `eq(alpha, .)` and `beta`, which the producers' public columns are made of.
    pub weights: Vec<E>,
    pub beta: E,
}

/// Verify the bus balances, oracle-free (the prover's committed values arrive on
/// the stream and are certified by `pcs`). Returns the per-column claims to open.
///
/// # Errors
///
/// Returns the GKR's refusal, a malformed stream, a nonce short of the proof of work, or a layout too large for the bus's margin at this grinding.
pub fn verify_balance<V: Verifier>(
    v: &mut V,
    push: &[Block],
    pull: &[Block],
    producers: &[Producer],
    grinding: u32,
    tables: &[(usize, usize)],
) -> Result<BusVerify<V::E>, BusError> {
    let setup = BusSetup::new(push, pull, producers, grinding)?;
    if setup.grinding > 0 {
        v.grind_check(setup.grinding)?;
    }
    let alphas = v.sample_vec(N_TUPLE_BITS);
    let fp = Fingerprint {
        w: v.eq_table(&alphas),
        alphas,
        beta: v.sample(),
    };
    let bus_gkr = gkr::verify_products(v, setup.mu())?;
    // Every row of every table is a real row (`cpu::filler`), so the two sides balance
    // outright: no padding tuples to divide back out, and no announced row counts whose
    // truthfulness the soundness argument would have to establish. The GKR sends ONE root
    // for both sides, so a prover cannot even state an unbalanced bus, and there is nothing
    // to check here.

    // Framework blocks decompose as before; the tables' blocks become linear forms and the
    // producers' bits weights on their airs. Each side's share of those is DERIVED from
    // `framework + Ṽ₀(ζ)` rather than checked here, the batch's target being what pins
    // it, so no table column is opened at ζ.
    let zero = v.zero();
    let mut forms = BusSetup::empty_forms(tables, zero);
    let mut totals = [zero; 2];
    let mut sparse: [Vec<SparseShare<V::E>>; 2] = Default::default();
    let mut selectors: [Vec<V::E>; 2] = Default::default();
    let mut open = Openings::default();
    for (s, side) in setup.sides.iter().enumerate() {
        let framework = side.decompose(v, &fp, &bus_gkr.point, tables, &mut forms[s], &mut open, |v, _, _| {
            v.next_scalar()
        })?;
        // What the tables owe this side: DERIVED, never read. A transmitted total
        // would be a free variable in its own check and would settle nothing; the
        // caller instead pins these against the batch's target.
        totals[s] = v.add(framework, bus_gkr.values[s]);
        sparse[s] = std::mem::take(&mut open.sparse);
        selectors[s] = std::mem::take(&mut open.selectors);
    }

    Ok(BusVerify {
        claims: open.claims,
        point: bus_gkr.point,
        forms,
        producers: open.producers,
        totals,
        sparse,
        selectors,
        alphas: fp.alphas,
        weights: fp.w,
        beta: fp.beta,
    })
}

#[cfg(test)]
pub(crate) mod tests {
    use super::{
        BUS_SOUNDNESS_BITS, Block, BusError, BusSetup, Coord, F64, F192, N_TUPLE_BITS, Producer, PublicColumn,
        SparseColumn, build_leaves, fingerprint_weights, gkr, layout, prove_balance, soundness_bits, tuple_leaves,
        verify_balance,
    };
    use crate::cpu::layout::Sizes;
    use crate::cpu::{Layout, Lookup, Program, UNGROUND_LOG_BYTECODE};
    use crate::pcs::MAX_MU;
    use crate::rv::Region;
    use crate::tables::N_TABLES;
    use fiat_shamir::transcript::{ProverState, VerifierState};
    use std::collections::HashMap;
    use std::sync::Arc;

    /// The leaves one side leaves unmatched on the other, as `(side, block, row)`, under
    /// one fixed fingerprint: what to look at when a bus does not balance. A producer's
    /// entry counts as its multiplicity's worth of leaves, reported as block
    /// `push.len() + p` for producer `p`.
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
                let leaves = tuple_leaves(&block.coords, block.kappa, cols, &w, beta);
                at.extend(leaves.into_iter().enumerate().map(|(z, leaf)| (leaf, b, z)));
            }
            at
        };
        let (mut pushed, pulled) = (side(push), side(pull));
        for (p, producer) in producers.iter().enumerate() {
            let leaves = tuple_leaves(&producer.coords, producer.kappa, cols, &w, beta);
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

    #[test]
    fn a_tables_virtual_coordinates_join_the_known_part() {
        // Table 0 pushes `(sep, base ^ (z << 3), public[z], col[z])`; a framework block pulls the same tuples.
        let kappa = 3;
        let column: Vec<F64> = (0..1u64 << kappa).map(|z| F64(z * 0x9e37_79b9 + 5)).collect();
        let public = Arc::new((0..1u64 << kappa).map(|z| F64(z ^ 0xabcd)).collect::<Vec<_>>());
        let coords = vec![
            Coord::Const(F64(7)),
            Coord::IntIndex {
                base: F64(0x4000),
                shift: 3,
            },
            Coord::Public(PublicColumn::new(public)),
            Coord::Col(0),
        ];
        let push = [Block::table(0, kappa, coords.clone())];
        let pull = [Block::framework(kappa, coords)];
        let tables = [(0, 1)];

        let mut ps = ProverState::from_label(b"leaf-virtual-coordinates");
        let bus = prove_balance(&push, &pull, &[], 0, &[&column], &tables, &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::from_label(b"leaf-virtual-coordinates", &proof);
        let verified = verify_balance(&mut vs, &push, &pull, &[], 0, &tables).expect("an honest bus balances");

        // What the verifier derives the tables owe is what their forms sum to, the virtual coordinates aside.
        for side in 0..2 {
            assert_eq!(verified.totals[side], bus.sigmas[side][0], "side {side}");
            assert_eq!(verified.forms[side][0].coeffs, bus.forms[side][0].coeffs, "side {side}");
            assert_eq!(
                verified.forms[side][0].constant, bus.forms[side][0].constant,
                "side {side}"
            );
        }
        assert_ne!(verified.totals[0], F192::ZERO);
    }

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

    /// The first product level `build_leaves` returns is `gkr::next_level` of its leaves,
    /// whichever way each four-tuple's product was formed: in a block's fill (eight rows
    /// or more, a parallel one at `PAR_THRESHOLD`), or after it (smaller blocks, a
    /// producer's bits, and the ragged last four-tuple).
    #[test]
    fn build_leaves_forms_the_first_product_level() {
        let rows = 1u64 << 11;
        let cols: Vec<Vec<F64>> = (0..3u64)
            .map(|c| {
                (0..rows)
                    .map(|z| F64((z + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (c << 40)))
                    .collect()
            })
            .collect();
        let cols: Vec<&[F64]> = cols.iter().map(Vec::as_slice).collect();
        let coords = || {
            vec![
                Coord::Const(F64(7)),
                Coord::IntIndex {
                    base: F64(0x4000),
                    shift: 3,
                },
                Coord::Col(0),
                Coord::Prod(1, 2),
            ]
        };
        // Out of size order, so the layout moves every block.
        let blocks: Vec<Block> = [2, 0, 11, 3, 1]
            .into_iter()
            .map(|kappa| Block::framework(kappa, coords()))
            .collect();
        let producers = [Producer {
            kappa: 4,
            coords: vec![Coord::Col(1)],
            col: 2,
            bits: 2,
        }];
        let lay = layout(&blocks, &producers);
        let alphas: Vec<F192> = (0..N_TUPLE_BITS as u64)
            .map(|i| F192::new(3 + i, 5 + 7 * i, 11))
            .collect();
        let w = fingerprint_weights(&alphas);
        let (leaves, products) = build_leaves(&blocks, &producers, &lay, &cols, &w, F192::new(13, 17, 19));
        assert_eq!(leaves.len(), (1 << 11) + 8 + 2 * 16 + 4 + 2 + 1);
        assert_eq!(products, gkr::next_level(&leaves));
    }

    /// The bound is `N_TUPLE_BITS` per linear factor plus the GKR terms: the
    /// multilinear fingerprint fixes each factor's total degree at four, whatever
    /// the tuple's width.
    #[test]
    fn bus_soundness_tracks_factors() {
        // 2^f factors of degree four cost f + 2 bits, and the GKR's terms one more.
        let largest = (192 - BUS_SOUNDNESS_BITS - 3) as usize;
        assert!(soundness_bits(1 << largest, largest) >= BUS_SOUNDNESS_BITS);
        assert!(soundness_bits(1 << (largest + 1), largest + 1) < BUS_SOUNDNESS_BITS);
    }

    #[test]
    fn every_layout_one_commitment_holds_keeps_the_margin_with_its_grinding() {
        // Every block of a RISC-V layout at 2^MAX_MU rows, more than any block of a committed layout has.
        let program = Program::new(&[0x0000_0073], Region::TEXT.base(), vec![], 0, 0).unwrap();
        let layout = Layout::new(program.rv(), [0; N_TABLES], 0);
        let widest = |blocks: &[Block]| -> Vec<Block> {
            blocks
                .iter()
                .map(|b| Block {
                    kappa: MAX_MU,
                    ..b.clone()
                })
                .collect()
        };
        let (push, pull) = (widest(&layout.push), widest(&layout.pull));

        // The multiplicity column and every table's packed witness share the commitment, so the rows, every one a
        // bytecode read, number below 2^MAX_MU, and a multiplicity has at most MAX_MU bits.
        let bytecode = |log_entries: usize| {
            layout
                .producers
                .iter()
                .map(|p| Producer {
                    kappa: log_entries,
                    bits: MAX_MU,
                    ..p.clone()
                })
                .collect::<Vec<_>>()
        };

        // Every text the region holds keeps the margin with its grinding, and one bit less grinding loses it.
        let keeps =
            |log_bytecode: usize, grinding: u32| BusSetup::new(&push, &pull, &bytecode(log_bytecode), grinding).is_ok();
        for log_bytecode in 0..=Region::TEXT.max_log_words() {
            let sizes = Sizes {
                log_bytecode,
                log_ram: 0,
                log_advice: 0,
            };
            let grinding = Lookup::Bytecode.grinding_bits(sizes);
            assert!(keeps(log_bytecode, grinding), "2^{log_bytecode} entries");
            assert_eq!(grinding == 0, log_bytecode <= UNGROUND_LOG_BYTECODE);
            if grinding > 0 {
                assert!(!keeps(log_bytecode, grinding - 1), "2^{log_bytecode} entries");
            }
        }
    }

    #[test]
    fn a_layout_past_the_margin_is_refused() {
        // A producer of 2^30 entries whose multiplicities have 30 bits: about 2^60 factors.
        let tuple = vec![Coord::Const(F64::ONE)];
        let producers = [Producer {
            kappa: 30,
            coords: tuple.clone(),
            col: 0,
            bits: 30,
        }];
        let pull = [Block::framework(0, tuple)];

        // Without grinding, the verifier's setup refuses it with an error, before drawing any challenge.
        assert!(matches!(
            BusSetup::new(&[], &pull, &producers, 0),
            Err(BusError::Soundness {
                required: BUS_SOUNDNESS_BITS,
                ..
            })
        ));
    }
}
