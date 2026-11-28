//! Hotwire's row side: one sum-check over every table's rows, then over the pointer columns.
//!
//! The rows are bound lowest variable first, so a round pairs consecutive rows of a table, which are consecutive
//! executions of its opcode. A table of `2^m` rows takes part from round 1 and is finished after `m` rounds; from
//! then on its value is multiplied by the all-zeros corner factor `1 + x_h` of each further row variable, once.
//! The pointer-column variables `q` come last.
//!
//! A pointer column `q` of table `F` contributes, at row `u`,
//!
//! `c_q(u)·Φ_0(u; r) + Σ_g c_g(u)·Φ_g(u; r) + ω_F(u)·Σ_i ε_{q,i}·(D_i(u; r_i)·D_i(u; 1 + r_i) + π_{w_i}(r_i))`,
//!
//! the column's coefficient `c_q = ω_F·(constant + aux) + act_F·(constant + aux)` times the pointer at the index
//! point `r`, each shift group's `c_g` times the pointer read further inside its window (`Φ_g`, chunk 0's table
//! `Σ_s μ_s·T_s` in place of `D_0`), plus the mirror certificate (the mirror test of Emile Wambsgans), which vanishes on every executed row whose chunks
//! are one-hot. The certificate reads chunk `i` at the same coordinates `r_i` as the pointer, so the two share
//! `D_i(r_i)`. Two rows whose chunk agrees make that chunk's factor constant in the round that pairs them, and
//! leave its certificate term zero: the prover skips both (equal-value skipping), and a chunk that agrees across a
//! whole folded group keeps a tag saying so.
//!
//! Rows from `explicit` on hold the padrow, whose pointer words are zero, so every folded group of them holds the
//! padrow's values: the prover keeps them as one tail rather than folding them. The coefficients vanish past the
//! executed rows, so only the pairs up to there are summed, unless a table's base terms reach its padding rows.
//!
//! A table's base terms (see [`super::base`]) belong to the pointer-column index `q = 0`: the row rounds add them
//! like any summand, and the column rounds carry their total `B` as `eq(0, q)·B`.

use super::base::Base;
use super::pointer::{ChunkEq, Chunks, NO_INDEX, Shifts, SplitEq, eval_chunk, mirror};
use super::{at, fold};
use primitives::bit_fold::fold_sparse_bits;
use primitives::field::{F128, F128Unreduced};
use std::mem::MaybeUninit;

/// Room for the coefficients of one round: degree `max(d + 2, 4) ≤ 11`.
const MAX_COEFFS: usize = 12;

/// A row's tags: per chunk `i`, in field `i` of [`TAG_BITS`], its one-hot value across the row's group or [`MIXED`].
type Tags = u64;

/// The bits of a tag field: nine fit a [`Tags`].
const TAG_BITS: usize = 7;

/// No one-hot value: a tag for a chunk that is not one value across its group.
const MIXED: u8 = (1 << TAG_BITS) - 1;

/// A row past the explicit ones: every chunk [`MIXED`].
const ALL_MIXED: Tags = Tags::MAX;

/// One in the lowest bit of every tag field.
const ONES: Tags = ((1 << (TAG_BITS * MAX_CHUNKS)) - 1) / MIXED as Tags;

/// The low six bits, and the high bit, of every tag field.
const LOW: Tags = ONES * (MIXED >> 1) as Tags;
const HIGH: Tags = ONES << (TAG_BITS - 1);

/// Chunk `i`'s tag in `t`.
#[inline(always)]
fn tag(t: Tags, i: usize) -> u8 {
    (t >> (TAG_BITS * i)) as u8 & MIXED
}

/// Every field whose low six bits or high bit are not all zero, set to [`MIXED`].
#[inline(always)]
fn mixed_fields(x: Tags) -> Tags {
    let nonzero = (((x & LOW) + LOW) | x) & HIGH;
    (nonzero >> (TAG_BITS - 1)) * Tags::from(MIXED)
}

/// An index's digits, each in its chunk's tag field: one lookup per byte of the index.
struct Spread {
    bytes: [[Tags; 256]; 4],
    /// The fields past the last chunk, and the bit past every field, all set.
    unused: Tags,
}

impl Spread {
    fn new(chunks: &Chunks) -> Self {
        assert!(chunks.width <= 32 && chunks.d() <= MAX_CHUNKS);
        let mut bytes = [[0; 256]; 4];
        for (b, table) in bytes.iter_mut().enumerate() {
            for (v, o) in table.iter_mut().enumerate() {
                for i in 0..chunks.d() {
                    *o |= (chunks.digit(v << (8 * b), i) as Tags) << (TAG_BITS * i);
                }
            }
        }
        Self {
            bytes,
            unused: !((1 << (TAG_BITS * chunks.d())) - 1),
        }
    }

    #[inline(always)]
    fn at(&self, sigma: u32) -> Tags {
        let [a, b, c, d] = sigma.to_le_bytes();
        self.bytes[0][usize::from(a)]
            | self.bytes[1][usize::from(b)]
            | self.bytes[2][usize::from(c)]
            | self.bytes[3][usize::from(d)]
    }

    /// The tags of a group of indices whose first is `sigma` and that differ from it in the bits `diff`: each chunk's
    /// digit where the group agrees, [`MIXED`] where it does not.
    #[inline(always)]
    fn tags(&self, sigma: u32, diff: u32) -> Tags {
        self.at(sigma) | mixed_fields(self.at(diff)) | self.unused
    }
}

/// Pairs per task of a round.
const TASK_PAIRS: usize = 256;

/// Rows per task of a pass that does little per row: folding a vector, summing bit-slices.
const ROW_BLOCK: usize = 1 << 12;

/// Rounds a table's pointer columns stay words, each folded row read as an `eq`-weighted sum over its group of
/// words, before the prover writes out their values.
const WORD_ROUNDS: usize = 3;

/// Words in a folded row's group before the values are written out.
const MAX_GROUP: usize = 1 << (WORD_ROUNDS - 1);

/// A column's slot tables, and each slot's table times each word's fold weight, while the rounds read words.
type WordTables<'a, 'b> = (&'a [(usize, &'b [F128])], &'a [Vec<F128>]);

/// A table's round sum, set up: [`State::round_setup`].
struct RoundSetup<'b> {
    pairs: usize,
    per_task: usize,
    tables: Vec<Vec<(usize, &'b [F128])>>,
    weighted: Vec<Vec<Vec<F128>>>,
}

/// Chunks of a word, at most.
const MAX_CHUNKS: usize = 9;

/// Aux columns of a table, at most: a pair reads them into a fixed array.
const MAX_AUX: usize = 4;

/// A column's coefficient on one of its table's two row weights: `constant`, plus a scale times a linear form of the
/// table's columns when `aux` names one.
#[derive(Clone, Copy, Debug)]
pub struct Coef {
    pub constant: F128,
    pub aux: Option<(usize, F128)>,
}

impl Coef {
    pub const ZERO: Self = Self {
        constant: F128::ZERO,
        aux: None,
    };

    pub fn constant(constant: F128) -> Self {
        Self { constant, aux: None }
    }

    fn is_zero(&self) -> bool {
        self.constant.is_zero() && self.aux.is_none()
    }
}

/// Shifted reads of a pointer column that share a coefficient on `ω_F`: `coef·Σ_s μ_s·Φ_s`, the pointer read each
/// `s ≥ 1` of `weights = [(s, μ_s)]` further inside its window.
#[derive(Clone, Debug)]
pub struct ShiftGroup {
    pub coef: Coef,
    pub weights: Vec<(usize, F128)>,
}

/// One pointer column, as the row side reads it.
pub struct RowColumn<'a> {
    /// The words, one per row of the table.
    pub words: &'a [u64],
    /// Each word's index, or [`NO_INDEX`] ([`Chunks::decode_all`]).
    pub index: Vec<u32>,
    /// Coefficient on `ω_F` of the pointer itself, `Φ_0`.
    pub omega: Coef,
    /// Coefficient on `act_F` of `Φ_0`.
    pub act: Coef,
    /// The shifted reads.
    pub shifts: Vec<ShiftGroup>,
    /// The certificate's coefficient per chunk.
    pub cert: Vec<F128>,
    /// The column's index in the pointer-column rounds.
    pub q: usize,
}

/// One table, as the row side reads it.
pub struct RowTable<'a> {
    pub log_rows: usize,
    /// Executed rows, the support of `ω_F` and `act_F`.
    pub rows: usize,
    /// Rows from here on hold the padrow.
    pub explicit: usize,
    /// `ω_F` on the executed rows.
    pub omega: Vec<F128>,
    /// `τ`, where `ω_F = θ·eq(τ, ·)` on the executed rows, which lets each round factor `eq(τ_h, X)` out.
    pub tau: Vec<F128>,
    /// The linear forms the coefficients name, each on the explicit rows, and their values on the padrow.
    pub aux: Vec<Vec<F128>>,
    pub aux_tail: Vec<F128>,
    pub columns: Vec<RowColumn<'a>>,
    /// The table's base terms, at `q = 0`.
    pub base: Base<'a>,
    /// The first round's polynomial of `base`'s `ω` blocks ([`Base::omega_round`]), which that round then adds in
    /// place of summing them.
    pub base_first: [F128; 5],
}

/// The functionals the row side evaluates pointers with: `D_i` at the index point `r`, chunk 0's window shifts there,
/// and `D_i` at `1 + r` for the certificate.
pub struct RowPoints {
    eq: ChunkEq,
    bar: ChunkEq,
    shifts: Shifts,
    /// `π_{w_i}(r_i)` per chunk.
    mirrors: Vec<F128>,
    /// Per chunk, `D_i(r_i)·D_i(1 + r_i)` over a pair of one-hot values `v ≠ v'` in `X + X²`: entry
    /// `v·2^{w_i} + v'` is `e_v·ē_{v'} + e_{v'}·ē_v` for the tables `e` at `r_i` and `ē` at `1 + r_i`.
    cert_pairs: Vec<Vec<F128>>,
    /// `eq(r, ·)` over whole pointers.
    split: SplitEq,
    /// `Π_i D_i(r_i)` over sets of chunks at one-hot values.
    clean: CleanEq,
    spread: Spread,
}

/// Entries of one block of [`CleanEq`], at most.
const CLEAN_BLOCK: usize = 1 << 13;

/// Blocks of [`CleanEq`], at most.
const CLEAN_BLOCKS: usize = 4;

/// The products of the chunk tables at one-hot values over any set of chunks: per block of consecutive chunks, a
/// table over the block's codes, a chunk's code its digit plus one when it is in the set and zero when not, so a
/// product over chunks whose digits are known is one lookup per block.
struct CleanEq {
    /// Per chunk, its block and the place value of its code there.
    place: [(usize, u32); MAX_CHUNKS],
    blocks: Vec<Vec<F128>>,
    /// Per block, the shift and mask of the index bits its chunks cover, and the block's code with each of those
    /// chunks at its digit, by those bits.
    full: Vec<(u32, u32, Vec<u32>)>,
}

impl CleanEq {
    fn new(chunks: &Chunks, tables: &[Vec<F128>]) -> Self {
        let mut place = [(0, 0); MAX_CHUNKS];
        let mut blocks: Vec<Vec<F128>> = vec![vec![F128::ONE]];
        for (i, table) in tables.iter().enumerate() {
            let radix = table.len() + 1;
            if blocks.last().unwrap().len() * radix > CLEAN_BLOCK {
                blocks.push(vec![F128::ONE]);
            }
            let block = blocks.last_mut().unwrap();
            let stride = block.len();
            place[i] = (blocks.len() - 1, stride as u32);
            let block = blocks.last_mut().unwrap();
            let low = block.clone();
            block.extend(table.iter().flat_map(|&t| low.iter().map(move |&v| v * t)));
        }
        assert!(blocks.len() <= CLEAN_BLOCKS);
        let full = (0..blocks.len())
            .map(|b| {
                let members: Vec<usize> = (0..tables.len()).filter(|&i| place[i].0 == b).collect();
                let shift = chunks.digit_shift(members[0]);
                let bits: usize = members.iter().map(|&i| chunks.widths[i]).sum();
                let codes = (0..1usize << bits)
                    .map(|s| {
                        let sigma = s << shift;
                        (members.iter())
                            .map(|&i| (chunks.digit(sigma, i) as u32 + 1) * place[i].1)
                            .sum()
                    })
                    .collect();
                (shift as u32, (1u32 << bits) - 1, codes)
            })
            .collect();
        Self { place, blocks, full }
    }

    /// The set of every chunk at its digit in `sigma` but those in `varying`.
    #[inline(always)]
    fn codes_except(&self, chunks: &Chunks, sigma: u32, varying: u32) -> [u32; CLEAN_BLOCKS] {
        let mut codes = [0u32; CLEAN_BLOCKS];
        for (c, (shift, mask, table)) in codes.iter_mut().zip(&self.full) {
            *c = table[(sigma >> shift & mask) as usize];
        }
        let mut rest = varying;
        while rest != 0 {
            let i = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            let (block, stride) = self.place[i];
            codes[block] -= (chunks.digit(sigma as usize, i) as u32 + 1) * stride;
        }
        codes
    }

    /// Put chunk `i` at digit `v` into the set `codes`.
    #[inline(always)]
    fn add(&self, codes: &mut [u32; CLEAN_BLOCKS], i: usize, v: u8) {
        let (block, stride) = self.place[i];
        codes[block] += (u32::from(v) + 1) * stride;
    }

    /// The product over the set `codes`.
    #[inline(always)]
    fn at(&self, codes: &[u32; CLEAN_BLOCKS]) -> F128 {
        match self.blocks.as_slice() {
            [a] => a[codes[0] as usize],
            [a, b] => a[codes[0] as usize] * b[codes[1] as usize],
            blocks => (blocks.iter().zip(codes)).map(|(b, &c)| b[c as usize]).product(),
        }
    }
}

impl RowPoints {
    pub fn new(chunks: &Chunks, r: &[F128], max_shift: usize) -> Self {
        let eq = ChunkEq::at(chunks, r);
        let bar = ChunkEq::mirrored(chunks, r);
        let cert_pairs = eq
            .tables
            .iter()
            .zip(&bar.tables)
            .map(|(e, f)| {
                let n = e.len();
                (0..n * n)
                    .map(|k| {
                        let (v, w) = (k / n, k % n);
                        e[v] * f[w] + e[w] * f[v]
                    })
                    .collect()
            })
            .collect();
        Self {
            clean: CleanEq::new(chunks, &eq.tables),
            spread: Spread::new(chunks),
            shifts: Shifts::new(&eq, max_shift),
            mirrors: (0..chunks.d()).map(|i| mirror(chunks.part(r, i))).collect(),
            eq,
            bar,
            cert_pairs,
            split: SplitEq::new(r, chunks.widths[0]),
        }
    }

    /// The layout of a column's values over every shift up to the largest, as the column rounds and the verifier
    /// read them.
    fn all_shifts(&self, d: usize) -> Slots {
        Slots::new(d, self.shifts.max_shift)
    }
}

/// Where a column's chunk functionals sit among its values: `D_i` at `r` and at `1 + r` (`d` each), then chunk 0's
/// table per shift group.
#[derive(Clone, Copy, Debug)]
struct Slots {
    d: usize,
    groups: usize,
}

impl Slots {
    fn new(d: usize, groups: usize) -> Self {
        Self { d, groups }
    }

    fn n_values(&self) -> usize {
        2 * self.d + self.groups
    }

    #[inline(always)]
    fn eq(&self, i: usize) -> usize {
        i
    }

    #[inline(always)]
    fn bar(&self, i: usize) -> usize {
        self.d + i
    }

    #[inline(always)]
    fn group(&self, g: usize) -> usize {
        2 * self.d + g
    }

    /// Slot `k`'s chunk.
    fn chunk(&self, k: usize) -> usize {
        if k < 2 * self.d { k % self.d } else { 0 }
    }

    /// Slot `k`'s chunk and table, the groups' tables read from `groups`.
    #[inline(always)]
    fn table<'b>(&self, k: usize, points: &'b RowPoints, groups: &'b [Vec<F128>]) -> (usize, &'b [F128]) {
        let d = self.d;
        if k < 2 * d {
            let t = [&points.eq, &points.bar][k / d];
            return (k % d, &t.tables[k % d]);
        }
        (0, &groups[k - 2 * d])
    }
}

/// A column at the end of the row rounds: its 64 bit-slices at `χ_F`, and the values they give, laid out by
/// `RowPoints::all_shifts`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnEnd {
    pub slices: Vec<F128>,
    pub values: Vec<F128>,
}

/// `Σ_u eq[u]·bit_b(word_u)` for each bit `b`, for each column's words under its `eq`, in one dispatch.
fn bit_slices_eq(columns: &[(&[u64], &[F128])]) -> Vec<Vec<F128>> {
    let mut first = Vec::with_capacity(columns.len() + 1);
    first.push(0);
    for (words, eq) in columns {
        first.push(first.last().unwrap() + words.len().min(eq.len()).div_ceil(ROW_BLOCK));
    }
    let slices = parallel::fold_reduce(
        *first.last().unwrap(),
        || vec![[F128::ZERO; 64]; columns.len()],
        |acc, task| {
            let c = first.partition_point(|&f| f <= task) - 1;
            let (words, eq) = columns[c];
            let start = (task - first[c]) * ROW_BLOCK;
            let end = words.len().min(eq.len()).min(start + ROW_BLOCK);
            let mut slices = [F128::ZERO; 64];
            fold_sparse_bits(&eq[start..end], &words[start..end], &mut slices);
            add_into(&mut acc[c], &slices);
        },
        |mut a, b| {
            for (a, b) in a.iter_mut().zip(&b) {
                add_into(a, b);
            }
            a
        },
    );
    slices.into_iter().map(|s| s.to_vec()).collect()
}

/// A chunk table at a word's 64 bit-slices: the functional is linear in the bits.
fn from_slices(chunks: &Chunks, slices: &[F128], i: usize, table: &[F128]) -> F128 {
    let start = chunks.word_shift(i);
    table.iter().zip(&slices[start..]).map(|(&e, &s)| e * s).sum()
}

impl ColumnEnd {
    fn from_slices(chunks: &Chunks, points: &RowPoints, slices: Vec<F128>) -> Self {
        let slots = points.all_shifts(chunks.d());
        let groups = &points.shifts.tables[1..];
        let values = (0..slots.n_values())
            .map(|k| {
                let (i, table) = slots.table(k, points, groups);
                from_slices(chunks, &slices, i, table)
            })
            .collect();
        Self { slices, values }
    }
}

/// A table's values at the end of the row rounds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableEnd {
    pub omega: F128,
    pub act: F128,
    pub aux: Vec<F128>,
    /// `Π (1 + χ_h)` over the row variables past the table's.
    pub corner: F128,
    pub columns: Vec<ColumnEnd>,
    /// The base terms at `χ_F`, without the corner factor.
    pub base: F128,
}

/// What the row side ends at.
pub struct RowEnd {
    /// `χ`, one coordinate per row round.
    pub point: Vec<F128>,
    /// `q*`, one coordinate per pointer-column round.
    pub column_point: Vec<F128>,
    pub tables: Vec<TableEnd>,
    /// The claim the last round leaves.
    pub claim: F128,
}

// ---- small polynomials in coefficient form -------------------------------------

type Poly = [F128; MAX_COEFFS];

/// A round's terms under one weight at a pair, unreduced.
type Acc = [F128Unreduced; MAX_COEFFS];

/// The most coefficients the base terms under `ω` have at a pair: a gate times a quadratic form.
const BASE_COEFFS: usize = 4;

/// A certificate's terms at a pair, unreduced: three coefficients.
type CertAcc = [F128Unreduced; 3];

/// Where a column's terms at a pair go: those under `ω` to `omega`, those under `act` to `act`, and the certificate's,
/// which are under `ω` too, to `cert`. Without `x1`, the terms in `omega` and `cert` may
/// leave out any part of their `X` coefficient: the round recovers it from its claim (see [`prove`]).
struct Sums<'s> {
    omega: &'s mut Acc,
    act: &'s mut Acc,
    cert: &'s mut CertAcc,
    x1: bool,
}

impl Sums<'_> {
    fn reborrow(&mut self) -> Sums<'_> {
        Sums {
            omega: &mut *self.omega,
            act: &mut *self.act,
            cert: &mut *self.cert,
            x1: self.x1,
        }
    }
}

/// `p ← p·(a + b·X)` for `p` of `len` coefficients; the new length.
#[inline(always)]
fn mul_linear(p: &mut Poly, len: usize, a: F128, b: F128) -> usize {
    p[len] = p[len - 1] * b;
    for j in (1..len).rev() {
        p[j] = (p[j].mul_unreduced(a) ^ p[j - 1].mul_unreduced(b)).reduce();
    }
    p[0] *= a;
    len + 1
}

/// `p ← p·f` for the linear `f` with `f(0) = pair.0`, `f(1) = pair.1`.
#[inline(always)]
fn mul_pair(p: &mut Poly, len: usize, pair: (F128, F128)) -> usize {
    mul_linear(p, len, pair.0, pair.0 + pair.1)
}

/// `acc ← acc + p·f` for the linear `f` through `pair`; the length of the sum.
#[inline(always)]
fn add_mul_pair(acc: &mut Poly, acc_len: usize, p: &Poly, len: usize, pair: (F128, F128)) -> usize {
    let (a, b) = (pair.0, pair.0 + pair.1);
    acc[0] += p[0] * a;
    for j in 1..len {
        acc[j] += (p[j].mul_unreduced(a) ^ p[j - 1].mul_unreduced(b)).reduce();
    }
    acc[len] += p[len - 1] * b;
    acc_len.max(len + 1)
}

/// The product of the linear functions through two pairs.
#[inline(always)]
fn pair_product(a: (F128, F128), b: (F128, F128)) -> [F128; 3] {
    let (c0, c2) = (a.0 * b.0, (a.0 + a.1) * (b.0 + b.1));
    [c0, a.1 * b.1 + c0 + c2, c2]
}

#[inline(always)]
fn add_into(acc: &mut [F128], p: &[F128]) {
    for (o, v) in acc.iter_mut().zip(p) {
        *o += *v;
    }
}

#[inline(always)]
fn is_zero_pair(p: (F128, F128)) -> bool {
    p.0.is_zero() && p.1.is_zero()
}

/// `c(X)·Φ_0(X) + Σ_g c_g(X)·Φ_g(X)` for one column at one pair, added to `acc`: the pointer under its coefficient
/// and each shift group under its own, each coefficient linear and given by its coefficients. `pair(k)` is value slot
/// `k` at the two rows; a chunk whose `same(i)` holds is a constant factor `first(i)`.
///
/// The pointer and every group share the factors `Π_{i ≥ 1} D_i`, so with a live group chunk 0 is the factor
/// `c·D_0 + Σ_g c_g·Φ_g`, and equal-value skipping then shortens the rest. The pointer's term under the act weight has no shift
/// groups: it is its coefficient times all the factors.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn pointer_pair(
    acc: &mut Acc,
    slots: &Slots,
    coef: &[F128],
    groups: &[[F128; 2]],
    act: Option<(&mut Acc, &[F128])>,
    (clean, digit): (&CleanEq, impl Fn(usize) -> Option<u8>),
    same: impl Fn(usize) -> bool,
    first: impl Fn(usize) -> F128,
    pair: impl Fn(usize) -> (F128, F128),
    x1: bool,
) {
    let d = slots.d;
    let mut p = [F128::ZERO; MAX_COEFFS];
    // A zero coefficient starts the chunk-0 factor empty.
    let mut len = if coef.iter().all(|c| c.is_zero()) {
        0
    } else {
        coef.len()
    };
    p[..len].copy_from_slice(&coef[..len]);
    // The factors `D_i` as `a + b·X`: chunk 0 first when the groups take it (for the act term), then the rest.
    let mut factors = [(F128::ZERO, F128::ZERO); MAX_CHUNKS];
    let mut start = 0;
    if groups.iter().any(|g| g.iter().any(|c| !c.is_zero())) {
        let e = pair(slots.eq(0));
        factors[0] = (e.0, e.0 + e.1);
        if len > 0 {
            len = mul_pair(&mut p, len, e);
        }
        for (g, gc) in groups.iter().enumerate() {
            let e = pair(slots.group(g));
            if !gc.iter().all(|c| c.is_zero()) && !is_zero_pair(e) {
                let mut gp = [F128::ZERO; MAX_COEFFS];
                gp[..2].copy_from_slice(gc);
                len = add_mul_pair(&mut p, len, &gp, 2, e);
            }
        }
        start = 1;
    }
    let p_live = !p[..len].iter().all(|c| c.is_zero());
    let act = act.filter(|(_, c)| !c.iter().all(|c| c.is_zero()));
    if !p_live && act.is_none() {
        return;
    }
    // The remaining factors: one lookup for the chunks constant at one-hot values, one product for the rest.
    let mut codes = [0u32; CLEAN_BLOCKS];
    let mut n = start;
    for i in start..d {
        if let Some(v) = digit(i) {
            clean.add(&mut codes, i, v);
        } else {
            factors[n] = if same(i) {
                (first(i), F128::ZERO)
            } else {
                let (a, b) = pair(slots.eq(i));
                (a, a + b)
            };
            n += 1;
        }
    }
    let s = clean.at(&codes);
    if p_live {
        let t = product(&factors[start..n]);
        add_tail(acc, &p[..len], s, &t[..n - start + 1], x1);
    }
    if let Some((act_acc, c)) = act {
        let t = product(&factors[..n]);
        add_scaled(act_acc, s, c, &t[..n + 1], true);
    }
}

/// `acc ← acc + s·p·t`, without the `X` coefficient unless `x1`.
#[inline(always)]
fn add_tail(acc: &mut Acc, p: &[F128], s: F128, t: &[F128], x1: bool) {
    for (i, &c) in p.iter().enumerate() {
        let c = s * c;
        for (j, (o, &v)) in acc[i..].iter_mut().zip(t).enumerate() {
            if x1 || i + j != 1 {
                *o ^= c.mul_unreduced(v);
            }
        }
    }
}

/// `acc ← acc + c·f` for `c` of one or two coefficients and the linear `f` through `pair`, without the `X`
/// coefficient unless `x1`.
#[inline(always)]
fn add_times_pair(acc: &mut Acc, c: &[F128], pair: (F128, F128), x1: bool) {
    let (a, b) = (pair.0, pair.0 + pair.1);
    acc[0] ^= c[0].mul_unreduced(a);
    if x1 {
        acc[1] ^= c[0].mul_unreduced(b);
    }
    if c.len() == 2 && !c[1].is_zero() {
        if x1 {
            acc[1] ^= c[1].mul_unreduced(a);
        }
        acc[2] ^= c[1].mul_unreduced(b);
    }
}

/// [`pointer_pair`] when at most one chunk differs across the pair's words: the pointer and every shifted pointer are
/// then linear in `X`, through their values `phi(row)` and `shifted(g, row)` at the two rows. A term reads the second
/// row only when it reaches past the constant coefficient, or its `X` coefficient is wanted.
#[inline(always)]
fn linear_pointer(
    acc: &mut Acc,
    coef: &[F128],
    groups: &[[F128; 2]],
    act: Option<(&mut Acc, &[F128])>,
    phi: impl Fn(usize) -> F128,
    shifted: impl Fn(usize, usize) -> F128,
    x1: bool,
) {
    let linear = |c: &[F128]| c.len() == 2 && !c[1].is_zero();
    let live = !coef[0].is_zero() || linear(coef);
    if live || act.is_some() {
        let lo = phi(0);
        let hi = if x1 || linear(coef) || act.is_some() {
            phi(1)
        } else {
            F128::ZERO
        };
        if live {
            add_times_pair(acc, coef, (lo, hi), x1);
        }
        if let Some((act_acc, c)) = act {
            add_times_pair(act_acc, c, (lo, hi), true);
        }
    }
    for (g, gc) in groups.iter().enumerate() {
        if !(gc[0].is_zero() && gc[1].is_zero()) {
            let lo = shifted(g, 0);
            let hi = if x1 || linear(gc) { shifted(g, 1) } else { F128::ZERO };
            add_times_pair(acc, gc, (lo, hi), x1);
        }
    }
}

/// `at` of each word of a group by its index, folded by the bound challenges `r`, the first for adjacent words.
#[inline(always)]
fn fold_words(index: &[u32], r: &[F128], at: impl Fn(usize) -> F128) -> F128 {
    let mut values = [F128::ZERO; MAX_GROUP];
    for (v, &x) in values.iter_mut().zip(index) {
        *v = at(x as usize);
    }
    let mut len = index.len();
    for &x in r {
        len /= 2;
        for t in 0..len {
            let (a, b) = (values[2 * t], values[2 * t + 1]);
            values[t] = fold(a, b, x);
        }
    }
    values[0]
}

/// `Σ_i ε_i·(D_i(r_i)·D_i(1 + r_i) + π_i)(X)` for one column at one pair, added to `acc`, from the bar slots, which
/// hold `ε_i·D_i(1 + r_i)` (see [`Column::bars`]), and `ε_i·π_i` in `cert_mirrors`. A chunk at the same one-hot value
/// at both rows (`clean`) adds zero, one at a one-hot value at each row (`one_hot`) adds `b·b̄·(X + X²)`, and one
/// whose values agree (`same`) a constant.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn cert_pair(
    acc: &mut CertAcc,
    slots: &Slots,
    cert: &[F128],
    cert_mirrors: &[F128],
    clean: impl Fn(usize) -> bool,
    one_hot: impl Fn(usize) -> bool,
    same: impl Fn(usize) -> bool,
    pair: impl Fn(usize) -> (F128, F128),
    x1: bool,
) {
    let mut m = [F128Unreduced::ZERO; 3];
    let mut constant = F128::ZERO;
    for i in 0..slots.d {
        if clean(i) || cert[i].is_zero() {
            continue;
        }
        let (x, y) = (pair(slots.eq(i)), pair(slots.bar(i)));
        if one_hot(i) {
            let t = (x.0 + x.1).mul_unreduced(y.0 + y.1);
            if x1 {
                m[1] ^= t;
            }
            m[2] ^= t;
        } else if same(i) {
            m[0] ^= x.0.mul_unreduced(y.0);
            constant += cert_mirrors[i];
        } else {
            add_pair_product(&mut m, x, y, x1);
            constant += cert_mirrors[i];
        }
    }
    add_cert(acc, m, constant);
}

/// `acc ← acc + m + constant`, `m` of three coefficients.
#[inline(always)]
fn add_cert(acc: &mut CertAcc, m: [F128Unreduced; 3], constant: F128) {
    acc[0] ^= m[0] ^ F128Unreduced::from(constant);
    acc[1] ^= m[1];
    acc[2] ^= m[2];
}

/// How a chunk that varies across a pair of rows stands there, for [`plain_terms`].
#[derive(Clone, Copy)]
enum ChunkPair {
    /// One-hot values `a` at the first row and `b ≠ a` at the second.
    OneHot(u8, u8),
    /// `D_i` and the scaled `D̄_i` at the two rows.
    Values((F128, F128), (F128, F128)),
}

/// The product of two linear factors `a + b·X`, by Karatsuba; without `x1`, its `X` coefficient is left zero.
#[inline(always)]
fn quad_x(f: (F128, F128), g: (F128, F128), x1: bool) -> [F128; 3] {
    let c0 = f.0.mul_unreduced(g.0);
    let c2 = f.1.mul_unreduced(g.1);
    let mid = if x1 {
        ((f.0 + f.1).mul_unreduced(g.0 + g.1) ^ c0 ^ c2).reduce()
    } else {
        F128::ZERO
    };
    [c0.reduce(), mid, c2.reduce()]
}

/// The product of two linear factors `a + b·X`.
#[inline(always)]
fn quad(f: (F128, F128), g: (F128, F128)) -> [F128; 3] {
    quad_x(f, g, true)
}

/// `out ← p·q` for `p` of `P` and `q` of `Q` coefficients; without `x1`, the `X` coefficient is left zero.
#[inline(always)]
fn conv<const P: usize, const Q: usize>(p: &[F128], q: &[F128], out: &mut [F128], x1: bool) {
    let mut u = [F128Unreduced::ZERO; MAX_CHUNKS + 1];
    for i in 0..P {
        for j in 0..Q {
            if x1 || i + j != 1 {
                u[i + j] ^= p[i].mul_unreduced(q[j]);
            }
        }
    }
    for (o, v) in out[..P + Q - 1].iter_mut().zip(u) {
        *o = v.reduce();
    }
}

/// The product of three linear factors; without `x1`, its `X` coefficient is left zero.
#[inline(always)]
fn cubic_x(f: &[(F128, F128)], x1: bool) -> [F128; 4] {
    let mut out = [F128::ZERO; 4];
    conv::<3, 2>(&quad(f[0], f[1]), &[f[2].0, f[2].1], &mut out, x1);
    out
}

/// The product of three linear factors.
#[inline(always)]
fn cubic(f: &[(F128, F128)]) -> [F128; 4] {
    cubic_x(f, true)
}

/// The product of the linear factors `a + b·X` in `f`, as a balanced tree; its length is `f.len() + 1`.
#[inline(always)]
fn product(f: &[(F128, F128)]) -> [F128; MAX_CHUNKS + 1] {
    product_x(f, true)
}

/// [`product`], without `x1` its `X` coefficient left zero where that saves a product: only the last multiplication
/// changes, and a single factor stays whole.
#[inline(always)]
fn product_x(f: &[(F128, F128)], x1: bool) -> [F128; MAX_CHUNKS + 1] {
    let mut out = [F128::ZERO; MAX_CHUNKS + 1];
    match f.len() {
        0 => out[0] = F128::ONE,
        1 => (out[0], out[1]) = f[0],
        2 => out[..3].copy_from_slice(&quad_x(f[0], f[1], x1)),
        3 => out[..4].copy_from_slice(&cubic_x(f, x1)),
        4 => conv::<3, 3>(&quad(f[0], f[1]), &quad(f[2], f[3]), &mut out, x1),
        5 => conv::<3, 4>(&quad(f[0], f[1]), &cubic(&f[2..]), &mut out, x1),
        6 => conv::<4, 4>(&cubic(f), &cubic(&f[3..]), &mut out, x1),
        7 => {
            let mut four = [F128::ZERO; 5];
            conv::<3, 3>(&quad(f[0], f[1]), &quad(f[2], f[3]), &mut four, true);
            conv::<5, 4>(&four, &cubic(&f[4..]), &mut out, x1)
        }
        8 => {
            let mut four = [[F128::ZERO; 5]; 2];
            for (o, f) in four.iter_mut().zip(f.chunks(4)) {
                conv::<3, 3>(&quad(f[0], f[1]), &quad(f[2], f[3]), o, true);
            }
            conv::<5, 5>(&four[0], &four[1], &mut out, x1)
        }
        9 => {
            let (mut four, mut five) = ([F128::ZERO; 5], [F128::ZERO; 6]);
            conv::<3, 3>(&quad(f[0], f[1]), &quad(f[2], f[3]), &mut four, true);
            conv::<3, 4>(&quad(f[4], f[5]), &cubic(&f[6..]), &mut five, true);
            conv::<5, 6>(&four, &five, &mut out, x1)
        }
        _ => unreachable!("at most {MAX_CHUNKS} chunks"),
    }
    out
}

/// `acc ← acc + s·c·p` for `c` of one or two coefficients, without the `X` coefficient unless `x1`.
#[inline(always)]
fn add_scaled(acc: &mut Acc, s: F128, c: &[F128], p: &[F128], x1: bool) {
    let t0 = s * c[0];
    for (j, (o, &v)) in acc.iter_mut().zip(p).enumerate() {
        if x1 || j != 1 {
            *o ^= t0.mul_unreduced(v);
        }
    }
    if c.len() == 2 && !c[1].is_zero() {
        let t1 = s * c[1];
        for (j, (o, &v)) in acc[1..].iter_mut().zip(p).enumerate() {
            if x1 || j != 0 {
                *o ^= t1.mul_unreduced(v);
            }
        }
    }
}

/// [`Column::add_terms`] for a column without shift groups, from how each of its chunks stands at the pair:
/// `c(X)·Φ_0(X)` under each weight and the certificate under `ω`. The chunks that stand constant at one-hot values
/// give one lookup in [`CleanEq`], already in `codes`, and the chunks in `varying` one product of linear factors,
/// which both weights share.
#[inline(always)]
fn plain_terms(
    column: &Column,
    aux: &[(F128, F128)],
    points: &RowPoints,
    widths: &[usize],
    sums: Sums<'_>,
    (codes, varying): ([u32; CLEAN_BLOCKS], u32),
    chunk: impl Fn(usize) -> ChunkPair,
) {
    let mut factors = [(F128::ZERO, F128::ZERO); MAX_CHUNKS];
    let mut n = 0;
    let mut m = [F128Unreduced::ZERO; 3];
    let mut constant = F128::ZERO;
    let mut rest = varying;
    while rest != 0 {
        let i = rest.trailing_zeros() as usize;
        rest &= rest - 1;
        let eps = column.cert[i];
        match chunk(i) {
            ChunkPair::OneHot(a, b) => {
                let t = &points.eq.tables[i];
                let (x0, x1) = (t[usize::from(a)], t[usize::from(b)]);
                factors[n] = (x0, x0 + x1);
                n += 1;
                if !eps.is_zero() {
                    let c = eps.mul_unreduced(points.cert_pairs[i][(usize::from(a) << widths[i]) + usize::from(b)]);
                    m[1] ^= c;
                    m[2] ^= c;
                }
            }
            ChunkPair::Values(x, y) => {
                factors[n] = (x.0, x.0 + x.1);
                n += 1;
                if !eps.is_zero() {
                    add_pair_product(&mut m, x, y, sums.x1);
                    constant += column.cert_mirrors[i];
                }
            }
        }
    }
    add_cert(sums.cert, m, constant);
    let (coef, len) = coef_linear(column.omega, aux);
    let live = !(coef[0].is_zero() && coef[1].is_zero());
    if !live && column.act.is_zero() {
        return;
    }
    let s = points.clean.at(&codes);
    // Without `x1` the sum leaves out its `X` coefficient, so a constant coefficient alone never reads the product's,
    // and the product skips it.
    let p = product_x(&factors[..n], sums.x1 || len == 2 || !column.act.is_zero());
    let p = &p[..n + 1];
    if live {
        add_scaled(sums.omega, s, &coef[..len], p, sums.x1);
    }
    if !column.act.is_zero() {
        let (c, len) = coef_linear(column.act, aux);
        add_scaled(sums.act, s, &c[..len], p, true);
    }
}

/// `m ← m + x(X)·y(X)` for the linear `x`, `y` through their pairs, by Karatsuba, without the `X` coefficient
/// unless `x1`.
#[inline(always)]
fn add_pair_product(m: &mut [F128Unreduced; 3], x: (F128, F128), y: (F128, F128), x1: bool) {
    let c0 = x.0.mul_unreduced(y.0);
    let c2 = (x.0 + x.1).mul_unreduced(y.0 + y.1);
    m[0] ^= c0;
    if x1 {
        m[1] ^= x.1.mul_unreduced(y.1) ^ c0 ^ c2;
    }
    m[2] ^= c2;
}

/// `ω(X)·m(X)` added to `acc`, `m` of three coefficients.
#[inline(always)]
fn add_weighted(acc: &mut Poly, omega: (F128, F128), m: [F128; 3]) {
    let (w0, w1) = (omega.0, omega.0 + omega.1);
    acc[0] += w0 * m[0];
    acc[1] += w0 * m[1] + w1 * m[0];
    acc[2] += w0 * m[2] + w1 * m[1];
    acc[3] += w1 * m[2];
}

/// A coefficient at a pair of rows, `constant + aux(X)`, by its coefficients in `X`: one when it is constant.
#[inline(always)]
fn coef_linear(c: Coef, aux: &[(F128, F128)]) -> ([F128; 2], usize) {
    match c.aux {
        None => ([c.constant, F128::ZERO], 1),
        Some((a, s)) => {
            let (a0, a1) = aux[a];
            let lo = c.constant + s * a0;
            ([lo, s * (a0 + a1)], 2)
        }
    }
}

/// The summand at one bound point from a column's values laid out by `slots`: `(c·D_0 + Σ_g c_g·Φ_g)·Π_{i ≥ 1} D_i +
/// Σ_i e_i·(D_i(r_i)·D_i(1 + r_i) + π_i)`.
fn summand(slots: &Slots, mirrors: &[F128], coef: F128, groups: &[F128], values: &[F128], certs: &[F128]) -> F128 {
    let d = slots.d;
    let rest: F128 = (1..d).map(|i| values[slots.eq(i)]).product();
    let low: F128 = coef * values[slots.eq(0)]
        + (groups.iter().enumerate())
            .map(|(g, &c)| c * values[slots.group(g)])
            .sum::<F128>();
    let cert: F128 = (0..d)
        .map(|i| certs[i] * (values[slots.eq(i)] * values[slots.bar(i)] + mirrors[i]))
        .sum();
    low * rest + cert
}

// ---- per-table state ----------------------------------------------------------------

/// Where a column's slots sit in a stored row: chunk by chunk, so that a row whose chunks from some `p` on all hold
/// one-hot values stores only the slots of chunks `0..p` and reads the rest from the tables at its digits.
struct Layout {
    /// The tag fields of the chunks.
    chunk_fields: Tags,
    /// Per slot, its chunk.
    chunk: Vec<u8>,
    /// Per slot, its place in a stored row.
    place: Vec<u16>,
    /// Per place in a stored row, its slot.
    order: Vec<u16>,
    /// At `p ≤ d`, how many values a row stores when it stores chunks `0..p`.
    stored: [usize; MAX_CHUNKS + 1],
}

impl Layout {
    fn new(slots: &Slots) -> Self {
        let n = slots.n_values();
        let d = slots.d;
        let chunk: Vec<u8> = (0..n).map(|k| slots.chunk(k) as u8).collect();
        let mut order: Vec<u16> = (0..n as u16).collect();
        order.sort_by_key(|&k| chunk[usize::from(k)]);
        let mut place = vec![0u16; n];
        for (j, &k) in order.iter().enumerate() {
            place[usize::from(k)] = j as u16;
        }
        let mut stored = [0; MAX_CHUNKS + 1];
        for p in 0..=d {
            stored[p] = chunk.iter().filter(|&&c| usize::from(c) < p).count();
        }
        Self {
            chunk_fields: (1 << (TAG_BITS * d)) - 1,
            chunk,
            place,
            order,
            stored,
        }
    }

    /// How many values a row with tags `t` stores: the slots of every chunk up to its last [`MIXED`] one.
    #[inline(always)]
    fn stored_len(&self, t: Tags) -> usize {
        let x = !t;
        // The high bit of each chunk's field of `t` that is MIXED.
        let mixed = !(((x & LOW) + LOW) | x) & HIGH & self.chunk_fields;
        self.stored[(Tags::BITS - mixed.leading_zeros()) as usize / TAG_BITS]
    }

    /// A row's value at `slot`: stored, or the slot's table at the chunk's one-hot digit.
    #[inline(always)]
    fn read(&self, row: RowView, tables: &[(usize, &[F128])], slot: usize) -> F128 {
        debug_assert!(slot < self.place.len() && tables.len() == self.place.len());
        // SAFETY: `slot` is one of the layout's slots, as `tables` has one entry per slot. A row stores
        // `stored_len(tags)` values ([`fill_sparse`]), or every slot for the tail row, whose tags are all
        // [`MIXED`]: a place past them is a chunk after the row's last [`MIXED`] one, whose tag is its one-hot digit,
        // below its table's length.
        unsafe {
            let j = usize::from(*self.place.get_unchecked(slot));
            if j < row.values.len() {
                *row.values.get_unchecked(j)
            } else {
                let c = usize::from(*self.chunk.get_unchecked(slot));
                let table = tables.get_unchecked(slot).1;
                let v = usize::from(tag(row.tags, c));
                debug_assert!(v < table.len());
                *table.get_unchecked(v)
            }
        }
    }
}

/// A row of a column's folded values: what it stores, laid out by its [`Layout`], and its tags.
#[derive(Clone, Copy)]
struct RowView<'b> {
    values: &'b [F128],
    tags: Tags,
}

/// A column's folded values: each explicit row stores its first [`Layout::stored_len`] values, one row after another,
/// and the tail row past them stores every slot.
struct Sparse {
    data: Vec<F128>,
    /// Where each explicit row starts in `data`, and the end.
    offsets: Vec<u32>,
    tail: Vec<F128>,
}

impl Sparse {
    #[inline(always)]
    fn row(&self, k: usize) -> &[F128] {
        match (self.offsets.get(k), self.offsets.get(k + 1)) {
            (Some(&a), Some(&b)) => &self.data[a as usize..b as usize],
            _ => &self.tail,
        }
    }
}

/// Every column's `len` new rows as [`Sparse`] values and tags: `tag(c, k)` is row `k`'s tags in column `c`, and
/// `fill(c, rows, tags, values)` writes the stored values of column `c`'s `rows`, with tags `tags`, one row after
/// another. Two dispatches cover every column.
///
/// # Safety
///
/// `fill` writes every element of `values`, which holds `Layout::stored_len` of each row's tags for its column.
unsafe fn fill_sparse(
    layouts: &[&Layout],
    len: usize,
    tag: impl Fn(usize, usize) -> Tags + Sync,
    fill: impl Fn(usize, std::ops::Range<usize>, &[Tags], &mut [MaybeUninit<F128>]) + Sync,
) -> Vec<(Sparse, Vec<Tags>)> {
    let per_column = len.div_ceil(TASK_PAIRS);
    let tasks = layouts.len() * per_column;
    let rows = |task: usize| {
        let start = task % per_column * TASK_PAIRS;
        start..len.min(start + TASK_PAIRS)
    };
    let mut tags: Vec<Vec<MaybeUninit<Tags>>> = layouts.iter().map(|_| primitives::uninit_vec(len)).collect();
    let mut offsets: Vec<Vec<MaybeUninit<u32>>> = layouts.iter().map(|_| primitives::uninit_vec(len + 1)).collect();
    // Each task's stored values.
    let sizes = {
        let tag_ptrs: Vec<_> = tags.iter_mut().map(|t| parallel::SendPtr(t.as_mut_ptr())).collect();
        let offset_ptrs: Vec<_> = offsets.iter_mut().map(|o| parallel::SendPtr(o.as_mut_ptr())).collect();
        parallel::map_collect(tasks, |task| {
            let (c, rows) = (task / per_column, rows(task));
            let (t, o) = (tag_ptrs[c].0, offset_ptrs[c].0);
            let mut size = 0usize;
            for k in rows {
                let v = tag(c, k);
                size += layouts[c].stored_len(v);
                // SAFETY: row `k` is this task's, inside column `c`'s `len` rows; its offset is relative to the
                // task's first row until the second dispatch adds the task's start.
                unsafe {
                    (*t.add(k)).write(v);
                    (*o.add(k + 1)).write(size as u32);
                }
            }
            size
        })
    };
    // Each task's first value in its column, and each column's length.
    let mut starts = vec![0usize; tasks];
    let mut totals = vec![0usize; layouts.len()];
    for c in 0..layouts.len() {
        let mut at = 0;
        for task in c * per_column..(c + 1) * per_column {
            starts[task] = at;
            at += sizes[task];
        }
        assert!(at < u32::MAX as usize, "a column's stored values fit their offsets");
        totals[c] = at;
        offsets[c][0].write(0);
    }
    // SAFETY: the first dispatch wrote every tag and every offset past the first, and the loop above the first.
    let (tags, mut offsets): (Vec<Vec<Tags>>, Vec<Vec<u32>>) = unsafe {
        (
            tags.into_iter().map(|v| primitives::assume_init_vec(v)).collect(),
            offsets.into_iter().map(|v| primitives::assume_init_vec(v)).collect(),
        )
    };
    let mut data: Vec<Vec<MaybeUninit<F128>>> = totals.iter().map(|&n| primitives::uninit_vec(n)).collect();
    {
        let data_ptrs: Vec<_> = data.iter_mut().map(|v| parallel::SendPtr(v.as_mut_ptr())).collect();
        let offset_ptrs: Vec<_> = offsets.iter_mut().map(|o| parallel::SendPtr(o.as_mut_ptr())).collect();
        let tags = &tags;
        parallel::for_each(tasks, |task| {
            let (c, rows) = (task / per_column, rows(task));
            let start = starts[task];
            // SAFETY: this task's rows and their values are its own, inside column `c`'s.
            unsafe {
                let o = offset_ptrs[c].0;
                for k in rows.clone() {
                    *o.add(k + 1) += start as u32;
                }
                let values = std::slice::from_raw_parts_mut(data_ptrs[c].0.add(start), sizes[task]);
                fill(c, rows.clone(), &tags[c][rows], values);
            }
        });
    }
    // SAFETY: the second dispatch handed `fill` each task's values, which tile every column's, and `fill` wrote them.
    let data = data.into_iter().map(|v| unsafe { primitives::assume_init_vec(v) });
    (data.zip(offsets).zip(tags).zip(layouts))
        .map(|(((data, offsets), tags), layout)| {
            let tail = vec![F128::ZERO; layout.order.len()];
            (Sparse { data, offsets, tail }, tags)
        })
        .collect()
}

/// Values in rows of `stride`, explicit on a prefix and one tail row after it. Before the first fold they are the
/// columns as given, so the first round reads them where they are.
struct Strided {
    data: Vec<F128>,
    /// Until the first fold, the columns in place of `data`, each over the explicit rows.
    columns: Vec<Vec<F128>>,
    tail: Vec<F128>,
    stride: usize,
}

impl Strided {
    /// Row `k` after the first fold.
    #[inline(always)]
    fn row(&self, k: usize) -> &[F128] {
        let s = self.stride;
        self.data.get(k * s..(k + 1) * s).unwrap_or(&self.tail)
    }

    /// Row `u`'s value in column `i`.
    #[inline(always)]
    fn at(&self, u: usize, i: usize) -> F128 {
        let s = self.stride;
        let stored = match self.columns.get(i) {
            Some(column) => column.get(u),
            None => self.data.get(u * s + i),
        };
        stored.copied().unwrap_or(self.tail[i])
    }

    /// Bind the lowest variable at `x`: `len` explicit rows after.
    fn fold(&mut self, len: usize, x: F128) {
        let s = self.stride;
        if s == 0 {
            return;
        }
        // SAFETY: every row writes each of its `s` values.
        self.data = unsafe {
            primitives::filled_vec(len * s, |out| {
                parallel::chunks_mut(out, s * TASK_PAIRS, |task, chunk| {
                    for (j, row) in chunk.chunks_mut(s).enumerate() {
                        let k = task * TASK_PAIRS + j;
                        for (i, o) in row.iter_mut().enumerate() {
                            o.write(fold(self.at(2 * k, i), self.at(2 * k + 1, i), x));
                        }
                    }
                });
            })
        };
        self.columns = Vec::new();
    }
}

/// Per chunk, its bits when every word of `group` holds the same ones.
#[inline(always)]
fn uniform_chunks(chunks: &Chunks, group: &[u64]) -> [Option<u64>; MAX_CHUNKS] {
    let mut out = [None; MAX_CHUNKS];
    for (i, o) in out.iter_mut().enumerate().take(chunks.d()) {
        let b = chunks.bits(group[0], i);
        if group[1..].iter().all(|&u| chunks.bits(u, i) == b) {
            *o = Some(b);
        }
    }
    out
}

/// The weights the bound challenges `r` fold a group of words by, the first for adjacent words: word `t`'s is
/// `Π_j r_j` over the bits `j` set in `t` times `Π_j (1 + r_j)` over the others.
fn fold_weights(r: &[F128]) -> Vec<F128> {
    let mut weights = vec![F128::ONE];
    for &x in r {
        let low: Vec<F128> = weights.iter().map(|&w| w * (F128::ONE + x)).collect();
        weights = low.into_iter().chain(weights.iter().map(|&w| w * x)).collect();
    }
    weights
}

/// Each slot's table times each word's fold weight in turn, `weights.len()` copies of the table.
fn weighted_tables(tables: &[(usize, &[F128])], weights: &[F128]) -> Vec<Vec<F128>> {
    tables
        .iter()
        .map(|&(_, table)| {
            weights
                .iter()
                .flat_map(|&w| table.iter().map(move |&v| w * v))
                .collect()
        })
        .collect()
}

/// Chunk `i`'s `table` at a folded row: its values on the words of `group` folded by the bound challenges, as a sum of
/// lookups in `weighted`, the table times each word's fold weight ([`weighted_tables`]), so a group costs no product.
/// One lookup when the chunk is `uniform` across the group.
#[inline(always)]
fn weighted_value(
    chunks: &Chunks,
    table: &[F128],
    weighted: &[F128],
    i: usize,
    group: &[u64],
    uniform: Option<u64>,
) -> F128 {
    if uniform.is_some() {
        return eval_chunk(chunks, table, group[0], i);
    }
    let len = table.len();
    group
        .iter()
        .zip(weighted.chunks_exact(len))
        .fold(F128::ZERO, |sum, (&u, w)| sum + eval_chunk(chunks, w, u, i))
}

/// Row `k`'s tags, chunk `i`'s in the `TAG_BITS`-bit field `i`.
#[inline(always)]
fn row_tags(tags: &[Tags], k: usize) -> Tags {
    tags.get(k).copied().unwrap_or(ALL_MIXED)
}

/// The tags of a folded pair: each chunk's tag where the two rows agree, [`MIXED`] where they differ.
#[inline(always)]
fn fold_tags(a: Tags, b: Tags) -> Tags {
    a | mixed_fields(a ^ b)
}

/// A pointer column: its words, and after round 1 per row its chunk functionals laid out by `slots`, and per chunk a
/// tag, the one-hot value the whole folded group holds or [`MIXED`], packed [`TAG_BITS`] a chunk.
struct Column<'a> {
    words: &'a [u64],
    slots: Slots,
    /// Chunk 0's table per group.
    group_tables: Vec<Vec<F128>>,
    /// Per group, its low table in [`SplitEq`].
    split_group_tables: Vec<Vec<F128>>,
    /// Each word's index, or [`NO_INDEX`], while the rounds read words.
    index: Vec<u32>,
    /// Where its slots sit in a stored row.
    layout: Layout,
    values: Option<Sparse>,
    tags: Vec<Tags>,
    omega: Coef,
    act: Coef,
    shifts: Vec<ShiftGroup>,
    cert: Vec<F128>,
    /// Per chunk, `D_i` at `1 + r` times the chunk's certificate weight `ε_i` (one when `ε_i` is zero), so a pair's
    /// certificate term is one product of its two slots; [`State::end`] divides the weight back out.
    bars: Vec<Vec<F128>>,
    /// `ε_i·π_i` per chunk.
    cert_mirrors: Vec<F128>,
    q: usize,
}

/// A chunk's certificate weight as [`Column::bars`] scales its table by.
fn bar_scale(eps: F128) -> F128 {
    if eps.is_zero() { F128::ONE } else { eps }
}

impl<'a> Column<'a> {
    fn new(column: RowColumn<'a>, chunks: &Chunks, points: &RowPoints) -> Self {
        let slots = Slots::new(chunks.d(), column.shifts.len());
        let group_tables = column
            .shifts
            .iter()
            .map(|g| {
                assert!(
                    g.weights
                        .iter()
                        .all(|&(s, _)| (1..=points.shifts.max_shift).contains(&s))
                );
                points.shifts.combined(&g.weights)
            })
            .collect();
        let split_group_tables = column
            .shifts
            .iter()
            .map(|g| points.split.shifted_table(&g.weights))
            .collect();
        let words = column.words;
        assert_eq!(column.index.len(), words.len(), "an index per word");
        Self {
            words,
            slots,
            group_tables,
            split_group_tables,
            index: column.index,
            layout: Layout::new(&slots),
            values: None,
            tags: Vec::new(),
            omega: column.omega,
            act: column.act,
            shifts: column.shifts,
            bars: (points.bar.tables.iter().zip(&column.cert))
                .map(|(t, &e)| t.iter().map(|&v| bar_scale(e) * v).collect())
                .collect(),
            cert_mirrors: column.cert.iter().zip(&points.mirrors).map(|(&e, &m)| e * m).collect(),
            cert: column.cert,
            q: column.q,
        }
    }

    /// Every slot's table and chunk, in slot order.
    fn tables<'b>(&'b self, points: &'b RowPoints) -> Vec<(usize, &'b [F128])> {
        let d = self.slots.d;
        (0..self.slots.n_values())
            .map(|k| match k.checked_sub(d) {
                Some(i) if i < d => (i, self.bars[i].as_slice()),
                _ => self.slots.table(k, points, &self.group_tables),
            })
            .collect()
    }

    /// Row `k`'s tags after the word rounds, its group of `n` words `k·n..(k + 1)·n`: per chunk its digit where the
    /// whole group holds one one-hot value there, [`MIXED`] elsewhere.
    #[inline(always)]
    fn materialize_tag(&self, n: usize, k: usize, chunks: &Chunks, spread: &Spread) -> Tags {
        let mut t = ALL_MIXED;
        match self.group_sigmas(n, k) {
            Some((sigmas, diff)) => t = spread.tags(sigmas[0], diff as u32),
            None => {
                let group = self.group_words(n, k);
                let uniform = uniform_chunks(chunks, &group[..n]);
                for (i, u) in uniform.iter().enumerate().take(chunks.d()) {
                    if let Some(b) = u.filter(|b| b.is_power_of_two()) {
                        t ^= Tags::from(MIXED ^ b.trailing_zeros() as u8) << (TAG_BITS * i);
                    }
                }
            }
        }
        t
    }

    /// Row `k`'s group of `n` indices and the bits where they differ, when every word of the group is one-hot.
    #[inline(always)]
    fn group_sigmas(&self, n: usize, k: usize) -> Option<([u32; 2 * MAX_GROUP], usize)> {
        let group = self.index.get(k * n..(k + 1) * n)?;
        let mut sigmas = [0u32; 2 * MAX_GROUP];
        let mut diff = 0;
        for (o, &s) in sigmas.iter_mut().zip(group) {
            if s == NO_INDEX {
                return None;
            }
            *o = s;
            diff |= s ^ group[0];
        }
        Some((sigmas, diff as usize))
    }

    /// Row `k`'s group of `n` words.
    #[inline(always)]
    fn group_words(&self, n: usize, k: usize) -> [u64; 2 * MAX_GROUP] {
        let mut group = [0u64; 2 * MAX_GROUP];
        for (o, u) in group[..n].iter_mut().enumerate() {
            *u = self.words.get(k * n + o).copied().unwrap_or(0);
        }
        group
    }

    /// The stored values of rows `rows` after the word rounds, one row after another, each its group of `n` words
    /// folded by the bound challenges, with `tables` from [`Self::tables`] and `weighted` from [`weighted_tables`].
    #[allow(clippy::too_many_arguments)]
    fn materialize_rows(
        &self,
        tables: &[(usize, &[F128])],
        weighted: &[Vec<F128>],
        n: usize,
        rows: std::ops::Range<usize>,
        tags: &[Tags],
        mut values: &mut [MaybeUninit<F128>],
        chunks: &Chunks,
    ) {
        let layout = &self.layout;
        for (&t, k) in tags.iter().zip(rows) {
            let len = layout.stored_len(t);
            let (row, rest) = values.split_at_mut(len);
            values = rest;
            let order = &layout.order[..len];
            // Every word one-hot: a chunk is uniform where its digit agrees across the group's indices.
            // The tags hold each uniform chunk's digit, so only the varying chunks read the indices' digits.
            if let Some((sigmas, _)) = self.group_sigmas(n, k) {
                let sigmas = &sigmas[..n];
                for (o, &slot) in row.iter_mut().zip(order) {
                    let (i, table) = tables[usize::from(slot)];
                    let tag = tag(t, i);
                    o.write(if tag != MIXED {
                        table[usize::from(tag)]
                    } else {
                        let (len, weighted) = (table.len(), &weighted[usize::from(slot)]);
                        (sigmas.iter().enumerate()).fold(F128::ZERO, |sum, (t, &s)| {
                            sum + weighted[t * len + chunks.digit(s as usize, i)]
                        })
                    });
                }
                continue;
            }
            let group = self.group_words(n, k);
            let group = &group[..n];
            let uniform = uniform_chunks(chunks, group);
            for (o, &slot) in row.iter_mut().zip(order) {
                let (i, table) = tables[usize::from(slot)];
                o.write(weighted_value(
                    chunks,
                    table,
                    &weighted[usize::from(slot)],
                    i,
                    group,
                    uniform[i],
                ));
            }
        }
    }

    /// The stored values of rows `rows`, with tags `tags`, one row after another, with the lowest variable bound at
    /// `x`, and `tables` from [`Self::tables`] for the chunks a row reads from its digits.
    fn fold_rows(
        &self,
        tables: &[(usize, &[F128])],
        rows: std::ops::Range<usize>,
        tags: &[Tags],
        mut values: &mut [MaybeUninit<F128>],
        x: F128,
    ) {
        let layout = &self.layout;
        for (&t, k) in tags.iter().zip(rows) {
            let len = layout.stored_len(t);
            let (row, rest) = values.split_at_mut(len);
            values = rest;
            let (lo, hi) = (self.view(2 * k), self.view(2 * k + 1));
            let (lo_len, hi_len) = (lo.values.len(), hi.values.len());
            for (j, o) in row.iter_mut().enumerate() {
                let a = if j < lo_len {
                    lo.values[j]
                } else {
                    layout.read(lo, tables, usize::from(layout.order[j]))
                };
                let b = if j < hi_len {
                    hi.values[j]
                } else {
                    layout.read(hi, tables, usize::from(layout.order[j]))
                };
                o.write(fold(a, b, x));
            }
        }
    }

    /// Row `k` of the folded values: what it stores and its tags.
    #[inline(always)]
    fn view(&self, k: usize) -> RowView<'_> {
        let values = self.values.as_ref().expect("the values are written out");
        RowView {
            values: values.row(k),
            tags: row_tags(&self.tags, k),
        }
    }

    /// Row `k`'s value at every slot, in slot order.
    fn dense_row(&self, k: usize, points: &RowPoints) -> Vec<F128> {
        let tables = self.tables(points);
        let row = self.view(k);
        (0..self.slots.n_values())
            .map(|slot| self.layout.read(row, &tables, slot))
            .collect()
    }

    fn set_values(&mut self, values: Sparse, tags: Vec<Tags>) {
        self.values = Some(values);
        self.tags = tags;
    }

    /// Add the column's terms at a pair to `sums`, each without its weight: the pointer's under `ω` to `omega`, and
    /// under `act` to `act`. `pointer(acc, coef, groups)` adds a pointer term, `cert(acc)` the certificate's.
    #[inline(always)]
    fn add_terms(
        &self,
        aux: &[(F128, F128)],
        sums: Sums<'_>,
        pointer: impl FnOnce(&mut Acc, &[F128], &[[F128; 2]], Option<(&mut Acc, &[F128])>, bool),
        cert: impl FnOnce(&mut CertAcc, bool),
    ) {
        let scaled = |c: Coef| coef_linear(c, aux);
        let mut groups = [[F128::ZERO; 2]; 4];
        for (o, g) in groups.iter_mut().zip(&self.shifts) {
            *o = scaled(g.coef).0;
        }
        let (coef, len) = scaled(self.omega);
        let (act_coef, act_len) = coef_linear(self.act, aux);
        let act = (!self.act.is_zero()).then_some((sums.act, &act_coef[..act_len]));
        pointer(sums.omega, &coef[..len], &groups[..self.shifts.len()], act, sums.x1);
        cert(sums.cert, sums.x1);
    }

    /// The coefficient of `Φ_0`, of each shift `s` (at `s - 1`), and the certificate weights at a table's end, times
    /// its corner factor.
    fn end_coefs(&self, end: &TableEnd, max_shift: usize) -> (F128, Vec<F128>, Vec<F128>) {
        let weight = |c: Coef| c.constant + c.aux.map_or(F128::ZERO, |(a, s)| s * end.aux[a]);
        let coef = end.corner * (end.omega * weight(self.omega) + end.act * weight(self.act));
        let mut shifts = vec![F128::ZERO; max_shift];
        for g in &self.shifts {
            let c = end.corner * end.omega * weight(g.coef);
            for &(s, mu) in &g.weights {
                shifts[s - 1] += c * mu;
            }
        }
        let certs = self.cert.iter().map(|&e| end.corner * end.omega * e).collect();
        (coef, shifts, certs)
    }
}

struct State<'a> {
    log_rows: usize,
    /// Support of `ω` and `act`.
    support: usize,
    /// Explicit rows.
    explicit: usize,
    omega: Vec<F128>,
    /// `act` at row `full` when it is below `support`: one on every row before, zero from `support` on.
    act_edge: F128,
    /// `ω`'s point: it is `θ·eq(τ, ·)` on the executed rows.
    tau: Vec<F128>,
    /// Rows whose whole group of rows is executed: there `act` is one and `ω` is `eq`'s.
    full: usize,
    aux: Strided,
    columns: Vec<Column<'a>>,
    /// The table's row variables.
    m: usize,
    /// The row challenges bound while the pointer columns are still words.
    bound: Vec<F128>,
    /// The table's value once its rows are bound, and the corner factor since.
    done: Option<(F128, F128)>,
    base: Base<'a>,
    /// [`RowTable::base_first`], until the first round.
    base_first: Option<[F128; 5]>,
    /// Whether a column has a term under `act_F`.
    any_act: bool,
}

impl<'a> State<'a> {
    fn new(table: RowTable<'a>, chunks: &Chunks, points: &RowPoints) -> Self {
        assert!(table.rows <= table.explicit && table.explicit <= 1 << table.log_rows);
        assert_eq!(table.omega.len(), table.rows);
        assert_eq!(table.aux_tail.len(), table.aux.len(), "a tail value per aux column");
        assert!(table.aux.len() <= MAX_AUX, "at most {MAX_AUX} aux columns");
        assert!(
            table.columns.iter().all(|c| c.shifts.len() <= 4),
            "at most four shift groups a column"
        );
        let aux = Strided {
            data: Vec::new(),
            stride: table.aux.len(),
            columns: table.aux,
            tail: table.aux_tail,
        };
        let mut state = Self {
            log_rows: table.log_rows,
            m: table.log_rows,
            support: table.rows,
            explicit: table.explicit,
            omega: table.omega,
            act_edge: F128::ZERO,
            tau: table.tau,
            full: table.rows,
            aux,
            columns: table
                .columns
                .into_iter()
                .map(|c| Column::new(c, chunks, points))
                .collect(),
            bound: Vec::new(),
            done: None,
            base: table.base,
            base_first: (table.log_rows > 0).then_some(table.base_first),
            any_act: false,
        };
        state.any_act = state.columns.iter().any(|c| !c.act.is_zero());
        if state.log_rows == 0 {
            // One row: its values are the table's end from the start.
            state.materialize(1, chunks, points);
            state.base.fold(1, F128::ZERO);
            state.finish(points);
        }
        state
    }

    /// Write out every column's values and tags at `len` folded rows, from its words and the bound challenges.
    fn materialize(&mut self, len: usize, chunks: &Chunks, points: &RowPoints) {
        let tables: Vec<_> = self.columns.iter().map(|c| c.tables(points)).collect();
        let weights = fold_weights(&self.bound);
        let weighted: Vec<_> = tables.iter().map(|t| weighted_tables(t, &weights)).collect();
        let (columns, n) = (&self.columns, weights.len());
        let layouts: Vec<&Layout> = columns.iter().map(|c| &c.layout).collect();
        // SAFETY: `materialize_rows` writes each row's `stored_len` values.
        let out = unsafe {
            fill_sparse(
                &layouts,
                len,
                |c, k| columns[c].materialize_tag(n, k, chunks, &points.spread),
                |c, rows, tags, values| {
                    columns[c].materialize_rows(&tables[c], &weighted[c], n, rows, tags, values, chunks);
                },
            )
        };
        drop(tables);
        for (column, (values, tags)) in self.columns.iter_mut().zip(out) {
            column.set_values(values, tags);
            column.index = Vec::new();
        }
    }

    /// Rows bound: the table's value at its end.
    fn finish(&mut self, points: &RowPoints) {
        let end = self.end(F128::ONE, points);
        let weight = |c: Coef| c.constant + c.aux.map_or(F128::ZERO, |(a, s)| s * end.aux[a]);
        let value: F128 = self
            .columns
            .iter()
            .zip(&end.columns)
            .map(|(column, values)| {
                let coef = end.omega * weight(column.omega) + end.act * weight(column.act);
                let groups: Vec<F128> = column.shifts.iter().map(|g| end.omega * weight(g.coef)).collect();
                let certs: Vec<F128> = column.cert.iter().map(|&e| end.omega * e).collect();
                summand(&column.slots, &points.mirrors, coef, &groups, &values.values, &certs)
            })
            .sum();
        self.done = Some((value + end.base, F128::ONE));
    }

    /// Pairs whose rows are all executed, when `ω` is `θ·eq(τ, ·)` there: below them `act` is one and `ω` factors
    /// `eq(τ_h, X)` out.
    fn whole(&self) -> usize {
        self.full / 2
    }

    #[inline(always)]
    fn aux_pair(&self, k: usize) -> [(F128, F128); MAX_AUX] {
        let mut out = [(F128::ZERO, F128::ZERO); MAX_AUX];
        if self.aux.columns.is_empty() {
            let (lo, hi) = (self.aux.row(2 * k), self.aux.row(2 * k + 1));
            for (o, (&a, &b)) in out.iter_mut().zip(lo.iter().zip(hi)) {
                *o = (a, b);
            }
        } else {
            for (i, o) in out.iter_mut().enumerate().take(self.aux.stride) {
                *o = (self.aux.at(2 * k, i), self.aux.at(2 * k + 1, i));
            }
        }
        out
    }

    /// What every task of this round's sum shares: the columns' tables and the pairs each task takes.
    fn round_setup<'b>(&'b self, points: &'b RowPoints) -> RoundSetup<'b> {
        let pairs = if self.base.on_padding() {
            self.explicit.div_ceil(2)
        } else {
            self.support.div_ceil(2)
        };
        let tables: Vec<Vec<(usize, &[F128])>> = self.columns.iter().map(|c| c.tables(points)).collect();
        // While the columns are words, each slot's table times each word's fold weight.
        let weights = fold_weights(&self.bound);
        let weighted = (self.columns.iter().zip(&tables))
            .map(|(c, t)| {
                if c.values.is_none() && weights.len() > 1 {
                    weighted_tables(t, &weights)
                } else {
                    Vec::new()
                }
            })
            .collect();
        // A small round still spreads over the workers.
        let per_task = (pairs / 64).clamp(8, TASK_PAIRS);
        RoundSetup {
            pairs,
            per_task,
            tables,
            weighted,
        }
    }

    /// One task's share of the round polynomial over this table's pairs, added to `acc`. With `derive`, the share
    /// leaves out part of the `X` coefficient of `factored`, which [`prove`] recovers from the round's claim.
    #[allow(clippy::too_many_arguments)]
    fn round_task(
        &self,
        setup: &RoundSetup,
        task: usize,
        chunks: &Chunks,
        points: &RowPoints,
        derive: bool,
        acc: &mut Poly,
    ) {
        let RoundSetup {
            pairs,
            per_task,
            ref tables,
            ref weighted,
        } = *setup;
        let n = 1 << self.bound.len();
        // Below `whole` pairs, both rows' groups are executed, so `act` is one at both and `ω` is
        // `(ω_0 + ω_1)·eq(τ_h, X)`: the pair's terms under `ω` add to `factored` scaled by `ω_0 + ω_1`, and
        // `eq(τ_h, X)` multiplies their sum once per task. The pair's terms are summed unscaled first, so the scale
        // costs one product per coefficient the pair reaches, not one per column coefficient.
        let (whole, tau) = (self.whole(), self.tau[self.m - self.log_rows]);
        let len = (chunks.d() + 2).max(4);
        let mut factored = [F128Unreduced::ZERO; MAX_COEFFS];
        let mut under_one = [F128Unreduced::ZERO; MAX_COEFFS];
        let range = task * per_task..pairs.min((task + 1) * per_task);
        let window = self.base.window(2 * range.start, 2 * range.end);
        // Each word column's words on the task's pairs, as one run.
        let first_word = (2 * range.start) << self.bound.len();
        let word_runs: Vec<&[u64]> = (self.columns.iter())
            .map(|c| match c.values {
                None => {
                    let len = c.words.len();
                    &c.words[first_word.min(len)..((2 * range.end) << self.bound.len()).min(len)]
                }
                Some(_) => &[],
            })
            .collect();
        for k in range.clone() {
            let omega = (at(&self.omega, 2 * k), at(&self.omega, 2 * k + 1));
            // The base terms under `ω`, reduced: at most `BASE_COEFFS` coefficients.
            let mut under_omega = [F128::ZERO; MAX_COEFFS];
            let with_omega = !is_zero_pair(omega) && self.base_first.is_none();
            if with_omega || self.base.on_padding() {
                // Below `whole` with `derive`, the round leaves out the `X` coefficient of the terms under `ω`.
                (self.base).pair(&window, k, with_omega, !(derive && k < whole), &mut under_omega, acc);
            }
            if is_zero_pair(omega) && 2 * k >= self.support {
                continue;
            }
            let act = (self.act(2 * k), self.act(2 * k + 1));
            let aux = self.aux_pair(k);
            let mut cert = [F128Unreduced::ZERO; 3];
            let add_columns = |sums: &mut Sums| {
                for (((column, tables), weighted), run) in self.columns.iter().zip(tables).zip(weighted).zip(&word_runs)
                {
                    let words = (tables.as_slice(), weighted.as_slice());
                    let mut sums = sums.reborrow();
                    match &column.values {
                        None if n == 1
                            && column.shifts.is_empty()
                            && Self::pair_single(column, k, &aux, chunks, points, sums.reborrow()) => {}
                        None if n == 2
                            && column.shifts.is_empty()
                            && Self::pair_group::<2>(column, weighted, k, &aux, chunks, points, sums.reborrow()) => {}
                        None if n == 4
                            && column.shifts.is_empty()
                            && Self::pair_group::<4>(column, weighted, k, &aux, chunks, points, sums.reborrow()) => {}
                        None => {
                            let run = (first_word, &**run);
                            Self::pair_words(column, words, run, &self.bound, k, &aux, chunks, points, sums);
                        }
                        Some(_) => Self::pair_folded(column, words.0, k, &aux, points, chunks, sums),
                    }
                }
            };
            if k < whole {
                // The columns add their terms under `ω` to `cols_omega` and those under `act` to `under_one`; the
                // pair's terms under `ω` then take the scale `ω_0 + ω_1` together.
                let mut cols_omega = [F128Unreduced::ZERO; MAX_COEFFS];
                add_columns(&mut Sums {
                    omega: &mut cols_omega,
                    act: &mut under_one,
                    cert: &mut cert,
                    x1: !derive,
                });
                for (o, c) in under_omega.iter_mut().zip(&cert) {
                    *o += c.reduce();
                }
                debug_assert!(under_omega[len.max(BASE_COEFFS)..].iter().all(|c| c.is_zero()));
                let scale = omega.0 + omega.1;
                for (j, (f, (c, &v))) in factored[..len]
                    .iter_mut()
                    .zip(cols_omega.iter().zip(&under_omega))
                    .enumerate()
                {
                    if (derive && j == 1) || (*c == F128Unreduced::ZERO && v.is_zero()) {
                        continue;
                    }
                    *f ^= scale.mul_unreduced(c.reduce() + v);
                }
            } else {
                let (mut cols_omega, mut cols_act) =
                    ([F128Unreduced::ZERO; MAX_COEFFS], [F128Unreduced::ZERO; MAX_COEFFS]);
                add_columns(&mut Sums {
                    omega: &mut cols_omega,
                    act: &mut cols_act,
                    cert: &mut cert,
                    x1: true,
                });
                for (o, c) in under_omega[..len].iter_mut().zip(&cols_omega) {
                    *o += c.reduce();
                }
                for (o, c) in under_omega.iter_mut().zip(&cert) {
                    *o += c.reduce();
                }
                add_mul_pair(acc, 0, &under_omega, len, omega);
                if self.any_act {
                    let under_act = cols_act.map(F128Unreduced::reduce);
                    add_mul_pair(acc, 0, &under_act, len, act);
                }
            }
        }
        if range.start < whole {
            let factored = factored.map(F128Unreduced::reduce);
            add_mul_pair(acc, 0, &factored, len, (F128::ONE + tau, tau));
            add_into(acc, &under_one.map(F128Unreduced::reduce)[..len]);
        }
    }

    /// [`Self::pair_words`] in the first round, for a column without shift groups, when both words are one-hot; whether
    /// they were. With at most one chunk differing the pointer is linear in `X`, through `eq(r, ·)` at the two indices.
    #[inline(always)]
    fn pair_single(
        column: &Column,
        k: usize,
        aux: &[(F128, F128)],
        chunks: &Chunks,
        points: &RowPoints,
        sums: Sums<'_>,
    ) -> bool {
        let (lo, hi) = match column.index.get(2 * k..2 * k + 2) {
            Some(&[lo, hi]) if lo != NO_INDEX && hi != NO_INDEX => (lo, hi),
            _ => return false,
        };
        let varying = chunks.varying(lo ^ hi);
        let digit = |sigma: u32, i: usize| chunks.digit(sigma as usize, i);
        if varying.count_ones() > 1 {
            let chunk = |i: usize| ChunkPair::OneHot(digit(lo, i) as u8, digit(hi, i) as u8);
            let codes = points.clean.codes_except(chunks, lo, varying);
            plain_terms(column, aux, points, &chunks.widths, sums, (codes, varying), chunk);
            return true;
        }
        let (coef, len) = coef_linear(column.omega, aux);
        let linear = len == 2 && !coef[1].is_zero();
        let live = !coef[0].is_zero() || linear;
        let act = !column.act.is_zero();
        if live || act {
            let split = &points.split;
            let phi_hi = if sums.x1 || linear || act {
                split.at(hi as usize)
            } else {
                F128::ZERO
            };
            let phi = (split.at(lo as usize), phi_hi);
            if live {
                add_times_pair(sums.omega, &coef[..len], phi, sums.x1);
            }
            if act {
                let (c, len) = coef_linear(column.act, aux);
                add_times_pair(sums.act, &c[..len], phi, true);
            }
        }
        if varying != 0 {
            let i = varying.trailing_zeros() as usize;
            let eps = column.cert[i];
            if !eps.is_zero() {
                let t = eps.mul_unreduced(points.cert_pairs[i][(digit(lo, i) << chunks.widths[i]) + digit(hi, i)]);
                if sums.x1 {
                    sums.cert[1] ^= t;
                }
                sums.cert[2] ^= t;
            }
        }
        true
    }

    /// [`Self::pair_words`] after the first round, each folded row a group of `N` words, for a column without shift
    /// groups, when all its words are one-hot; whether they were. A chunk is one-hot at a folded row where its words
    /// agree, else their values' sum in `weighted`, the slot tables times each word's fold weight.
    #[inline(always)]
    fn pair_group<const N: usize>(
        column: &Column,
        weighted: &[Vec<F128>],
        k: usize,
        aux: &[(F128, F128)],
        chunks: &Chunks,
        points: &RowPoints,
        sums: Sums<'_>,
    ) -> bool {
        let Some(words) = column.index.get(2 * N * k..2 * N * (k + 1)) else {
            return false;
        };
        if words.contains(&NO_INDEX) {
            return false;
        }
        let (lo, hi) = words.split_at(N);
        let spread = |side: &[u32]| side.iter().fold(0, |d, &s| d | (s ^ side[0]));
        let (lo_diff, hi_diff) = (spread(lo), spread(hi));
        let varying = chunks.varying(lo_diff | hi_diff | (lo[0] ^ hi[0]));
        let digit = |sigma: u32, i: usize| chunks.digit(sigma as usize, i);
        // A slot's value at a folded row: one lookup where its words agree on the chunk, else their values in the
        // weighted copies of the table, one copy per word.
        let value = |table: &[F128], weighted: &[F128], side: &[u32], diff: u32, i: usize| {
            if digit(diff, i) == 0 {
                return table[digit(side[0], i)];
            }
            (side.iter().enumerate()).fold(F128::ZERO, |sum, (t, &s)| sum + weighted[t * table.len() + digit(s, i)])
        };
        let slots = &column.slots;
        let chunk = |i: usize| {
            if digit(lo_diff, i) == 0 && digit(hi_diff, i) == 0 {
                return ChunkPair::OneHot(digit(lo[0], i) as u8, digit(hi[0], i) as u8);
            }
            let pair = |table: &[F128], weighted: &[F128]| {
                (
                    value(table, weighted, lo, lo_diff, i),
                    value(table, weighted, hi, hi_diff, i),
                )
            };
            ChunkPair::Values(
                pair(&points.eq.tables[i], &weighted[slots.eq(i)]),
                pair(&column.bars[i], &weighted[slots.bar(i)]),
            )
        };
        let codes = points.clean.codes_except(chunks, lo[0], varying);
        plain_terms(column, aux, points, &chunks.widths, sums, (codes, varying), chunk);
        true
    }

    /// The first rounds: the pair `(2k, 2k + 1)` straight from the words, each folded row its group of words folded
    /// by the bound challenges `r`.
    #[allow(clippy::too_many_arguments)]
    fn pair_words(
        column: &Column,
        (tables, weighted): WordTables<'_, '_>,
        (first_word, run): (usize, &[u64]),
        r: &[F128],
        k: usize,
        aux: &[(F128, F128)],
        chunks: &Chunks,
        points: &RowPoints,
        mut sums: Sums<'_>,
    ) {
        let n = 1 << r.len();
        let done = match n {
            1 => Self::try_indices::<1>(column, (tables, weighted), r, k, aux, chunks, points, sums.reborrow()),
            2 => Self::try_indices::<2>(column, (tables, weighted), r, k, aux, chunks, points, sums.reborrow()),
            _ => false,
        };
        if done {
            return;
        }
        // `run` holds the column's words from `first_word` on, as far as the task's pairs and the column reach.
        let word = |u: usize| run.get(u - first_word).copied().unwrap_or(0);
        let (mut lo, mut hi) = ([0u64; MAX_GROUP], [0u64; MAX_GROUP]);
        for t in 0..n {
            lo[t] = word(2 * k * n + t);
            hi[t] = word((2 * k + 1) * n + t);
        }
        let (lo, hi) = (&lo[..n], &hi[..n]);
        let (lo_bits, hi_bits) = (uniform_chunks(chunks, lo), uniform_chunks(chunks, hi));
        let same = |i: usize| lo_bits[i].is_some() && lo_bits[i] == hi_bits[i];
        let one_hot =
            |i: usize| lo_bits[i].is_some_and(u64::is_power_of_two) && hi_bits[i].is_some_and(u64::is_power_of_two);
        let pair = |slot: usize| {
            let (i, table) = tables[slot];
            // A single word is uniform in every chunk, and its slot has no weighted table.
            let weighted = weighted.get(slot).map_or(&[][..], Vec::as_slice);
            (
                weighted_value(chunks, table, weighted, i, lo, lo_bits[i]),
                weighted_value(chunks, table, weighted, i, hi, hi_bits[i]),
            )
        };
        let slots = &column.slots;
        column.add_terms(
            aux,
            sums,
            |acc, coef, groups, act, x1| {
                pointer_pair(
                    acc,
                    slots,
                    coef,
                    groups,
                    act,
                    (&points.clean, |i| {
                        let b = lo_bits[i].filter(|b| same(i) && b.is_power_of_two());
                        b.map(|b| b.trailing_zeros() as u8)
                    }),
                    same,
                    |i| points.eq.eval(chunks, lo[0], i),
                    pair,
                    x1,
                )
            },
            |acc, x1| {
                cert_pair(
                    acc,
                    slots,
                    &column.cert,
                    &column.cert_mirrors,
                    |i| same(i) && lo_bits[i].is_some_and(u64::is_power_of_two),
                    one_hot,
                    same,
                    pair,
                    x1,
                )
            },
        );
    }

    /// [`Self::pair_indices`] on the pair `k` of groups of `N` words when every word's chunks are one-hot; whether it
    /// was.
    #[allow(clippy::too_many_arguments)]
    #[inline(always)]
    fn try_indices<const N: usize>(
        column: &Column,
        tables: WordTables<'_, '_>,
        r: &[F128],
        k: usize,
        aux: &[(F128, F128)],
        chunks: &Chunks,
        points: &RowPoints,
        sums: Sums<'_>,
    ) -> bool {
        let index = |u: usize| column.index.get(u).copied().unwrap_or(NO_INDEX);
        let sigmas: [[u32; N]; 2] = [0, 1].map(|side| std::array::from_fn(|t| index((2 * k + side) * N + t)));
        if sigmas.iter().any(|s| s.contains(&NO_INDEX)) {
            return false;
        }
        Self::pair_indices::<N>(column, tables, r, sigmas, aux, chunks, points, sums);
        true
    }

    /// [`Self::pair_words`] when every word's chunks are one-hot, from the words' indices, `sigmas[0]` for the
    /// first row's group and `sigmas[1]` for the second's: a chunk
    /// whose digit agrees across them is constant and its certificate term zero, and a pointer with at most one
    /// varying chunk is linear in `X`.
    #[allow(clippy::too_many_arguments)]
    fn pair_indices<const N: usize>(
        column: &Column,
        (tables, weighted): WordTables<'_, '_>,
        r: &[F128],
        sigmas: [[u32; N]; 2],
        aux: &[(F128, F128)],
        chunks: &Chunks,
        points: &RowPoints,
        sums: Sums<'_>,
    ) {
        let (lo, hi) = (&sigmas[0], &sigmas[1]);
        let (mut lo_diff, mut hi_diff) = (0, 0);
        for (&a, &b) in lo.iter().zip(hi) {
            lo_diff |= a ^ lo[0];
            hi_diff |= b ^ hi[0];
        }
        let diff = lo_diff | hi_diff | (lo[0] ^ hi[0]);
        let digit = |sigma: u32, i: usize| chunks.digit(sigma as usize, i);
        let varying = chunks.varying(diff);
        // Slot `slot`'s value at a folded row of `side`: one lookup when its chunk's digit agrees across the side,
        // else each word's lookup in the weighted tables.
        let value = |slot: usize, side: &[u32], side_diff: u32| {
            let (i, table) = tables[slot];
            if digit(side_diff, i) == 0 {
                return table[digit(side[0], i)];
            }
            let len = table.len();
            (side.iter().enumerate()).fold(F128::ZERO, |sum, (t, &sigma)| {
                sum + weighted[slot][t * len + digit(sigma, i)]
            })
        };
        let pair = |slot: usize| (value(slot, lo, lo_diff), value(slot, hi, hi_diff));
        let slots = &column.slots;
        if column.shifts.is_empty() && (N > 1 || varying.count_ones() > 1) {
            let chunk = |i: usize| {
                let v = |sigma: u32| digit(sigma, i) as u8;
                if digit(lo_diff, i) == 0 && digit(hi_diff, i) == 0 {
                    ChunkPair::OneHot(v(lo[0]), v(hi[0]))
                } else {
                    ChunkPair::Values(pair(slots.eq(i)), pair(slots.bar(i)))
                }
            };
            let codes = points.clean.codes_except(chunks, lo[0], varying);
            return plain_terms(column, aux, points, &chunks.widths, sums, (codes, varying), chunk);
        }
        column.add_terms(
            aux,
            sums,
            |acc, coef, groups, act, x1| {
                if varying.count_ones() <= 1 {
                    let rows = [lo, hi];
                    linear_pointer(
                        acc,
                        coef,
                        groups,
                        act,
                        |row| fold_words(rows[row], r, |sigma| points.split.at(sigma)),
                        |g, row| {
                            let at = |sigma| points.split.at_shifted(&column.split_group_tables[g], sigma);
                            fold_words(rows[row], r, at)
                        },
                        x1,
                    )
                } else {
                    pointer_pair(
                        acc,
                        slots,
                        coef,
                        groups,
                        act,
                        (&points.clean, |i| {
                            (varying >> i & 1 == 0).then(|| digit(lo[0], i) as u8)
                        }),
                        |_| false,
                        |_| F128::ZERO,
                        pair,
                        x1,
                    )
                }
            },
            |acc, x1| {
                let mut m = [F128Unreduced::ZERO; 3];
                let mut constant = F128::ZERO;
                let mut rest = varying;
                while rest != 0 {
                    let i = rest.trailing_zeros() as usize;
                    rest &= rest - 1;
                    let eps = column.cert[i];
                    if eps.is_zero() {
                        continue;
                    }
                    if digit(lo_diff, i) == 0 && digit(hi_diff, i) == 0 {
                        let t = eps.mul_unreduced(
                            points.cert_pairs[i][(digit(lo[0], i) << chunks.widths[i]) + digit(hi[0], i)],
                        );
                        if x1 {
                            m[1] ^= t;
                        }
                        m[2] ^= t;
                    } else {
                        add_pair_product(&mut m, pair(slots.eq(i)), pair(slots.bar(i)), x1);
                        constant += column.cert_mirrors[i];
                    }
                }
                add_cert(acc, m, constant);
            },
        );
    }

    /// Later rounds: the pair `(2k, 2k + 1)` of the folded columns.
    #[allow(clippy::too_many_arguments)]
    fn pair_folded(
        column: &Column,
        tables: &[(usize, &[F128])],
        k: usize,
        aux: &[(F128, F128)],
        points: &RowPoints,
        chunks: &Chunks,
        sums: Sums<'_>,
    ) {
        let slots = &column.slots;
        let (lo_row, hi_row) = (column.view(2 * k), column.view(2 * k + 1));
        let read = |row: RowView, slot: usize| column.layout.read(row, tables, slot);
        let pair = |slot: usize| (read(lo_row, slot), read(hi_row, slot));
        let (lo_tags, hi_tags) = (lo_row.tags, hi_row.tags);
        if column.shifts.is_empty() {
            let chunk = |i: usize| {
                let (a, b) = (tag(lo_tags, i), tag(hi_tags, i));
                match (a, b) {
                    (MIXED, _) | (_, MIXED) => ChunkPair::Values(pair(slots.eq(i)), pair(slots.bar(i))),
                    _ => ChunkPair::OneHot(a, b),
                }
            };
            let (mut codes, mut varying) = ([0u32; CLEAN_BLOCKS], 0u32);
            for i in 0..chunks.d() {
                let (a, b) = (tag(lo_tags, i), tag(hi_tags, i));
                if a == b && a != MIXED {
                    points.clean.add(&mut codes, i, a);
                } else {
                    varying |= 1 << i;
                }
            }
            return plain_terms(column, aux, points, &chunks.widths, sums, (codes, varying), chunk);
        }
        let clean = |i: usize| {
            let t = tag(lo_tags, i);
            t != MIXED && t == tag(hi_tags, i)
        };
        // Chunk `i`'s `D_i` and scaled `D̄_i` agree at the two rows.
        let both_agree = |i: usize| {
            let (e, b) = (pair(slots.eq(i)), pair(slots.bar(i)));
            e.0 == e.1 && b.0 == b.1
        };
        column.add_terms(
            aux,
            sums,
            |acc, coef, groups, act, x1| {
                let digit = |i: usize| {
                    let t = tag(lo_tags, i);
                    (t != MIXED && t == tag(hi_tags, i)).then_some(t)
                };
                // Chunk `i`'s `D_i`, its slot `i`, agrees at the two rows.
                let eq_agrees = |i: usize| {
                    let e = pair(slots.eq(i));
                    e.0 == e.1
                };
                let first = |i: usize| read(lo_row, slots.eq(i));
                pointer_pair(
                    acc,
                    slots,
                    coef,
                    groups,
                    act,
                    (&points.clean, digit),
                    eq_agrees,
                    first,
                    pair,
                    x1,
                )
            },
            |acc, x1| {
                cert_pair(
                    acc,
                    slots,
                    &column.cert,
                    &column.cert_mirrors,
                    clean,
                    |_| false,
                    both_agree,
                    pair,
                    x1,
                )
            },
        );
    }

    /// `act` at row `u`.
    #[inline(always)]
    fn act(&self, u: usize) -> F128 {
        if u < self.full {
            F128::ONE
        } else if u < self.support {
            self.act_edge
        } else {
            F128::ZERO
        }
    }

    /// Bind the lowest row variable at `x`.
    fn fold(&mut self, x: F128, chunks: &Chunks, points: &RowPoints) {
        let support = self.support.div_ceil(2);
        let explicit = self.explicit.div_ceil(2);
        let omega = &self.omega;
        // SAFETY: every entry is written.
        self.omega = unsafe {
            primitives::filled_vec(support, |out| {
                parallel::chunks_mut(out, ROW_BLOCK, |task, chunk| {
                    for (j, o) in chunk.iter_mut().enumerate() {
                        let k = task * ROW_BLOCK + j;
                        o.write(fold(at(omega, 2 * k), at(omega, 2 * k + 1), x));
                    }
                });
            })
        };
        let full = self.full / 2;
        self.act_edge = fold(self.act(2 * full), self.act(2 * full + 1), x);
        self.aux.fold(explicit, x);
        self.base.fold(explicit, x);
        self.base_first = None;
        let words = self.columns.first().is_some_and(|c| c.values.is_none());
        if words {
            self.bound.push(x);
        }
        if !words {
            let columns = &self.columns;
            let tables: Vec<_> = columns.iter().map(|c| c.tables(points)).collect();
            let layouts: Vec<&Layout> = columns.iter().map(|c| &c.layout).collect();
            // SAFETY: `fold_rows` writes each row's `stored_len` values.
            let out = unsafe {
                fill_sparse(
                    &layouts,
                    explicit,
                    |c, k| fold_tags(row_tags(&columns[c].tags, 2 * k), row_tags(&columns[c].tags, 2 * k + 1)),
                    |c, rows, tags, values| columns[c].fold_rows(&tables[c], rows, tags, values, x),
                )
            };
            drop(tables);
            for (column, (values, tags)) in self.columns.iter_mut().zip(out) {
                column.set_values(values, tags);
            }
        } else if self.bound.len() == WORD_ROUNDS || self.log_rows == 1 {
            self.materialize(explicit, chunks, points);
        }
        self.support = support;
        self.explicit = explicit;
        self.full /= 2;
        self.log_rows -= 1;
        if self.log_rows == 0 {
            self.finish(points);
        }
    }

    fn end(&self, corner: F128, points: &RowPoints) -> TableEnd {
        TableEnd {
            omega: at(&self.omega, 0),
            act: self.act(0),
            aux: (0..self.aux.stride).map(|i| self.aux.at(0, i)).collect(),
            corner,
            columns: self
                .columns
                .iter()
                .map(|c| {
                    let mut values = if c.values.is_some() {
                        c.dense_row(0, points)
                    } else {
                        Vec::new()
                    };
                    let d = c.slots.d;
                    for (v, &e) in values.iter_mut().skip(d).take(d).zip(&c.cert) {
                        *v *= bar_scale(e).inv();
                    }
                    ColumnEnd {
                        slices: Vec::new(),
                        values,
                    }
                })
                .collect(),
            base: self.base.end(at(&self.omega, 0)),
        }
    }
}

/// One column in the pointer-column rounds: its coefficient, its coefficient per shift, its values laid out by
/// [`RowPoints::all_shifts`] and its certificate weights.
type ColumnAt = (F128, Vec<F128>, Vec<F128>, Vec<F128>);

/// The row side over `tables`. `round` takes each round polynomial's coefficients and returns the challenge;
/// `claim` is what the rows sum to, and every round derives part of its polynomial from its claim. The
/// pointer-column rounds run over `q_vars` variables, each column at its own `q`.
pub fn prove(
    chunks: &Chunks,
    points: &RowPoints,
    tables: Vec<RowTable>,
    q_vars: usize,
    mut claim: F128,
    round: &mut dyn FnMut(&[F128]) -> F128,
) -> RowEnd {
    let d = chunks.d();
    let n_coeffs = row_coeffs(d);
    let n_rounds = tables.iter().map(|t| t.log_rows).max().unwrap_or(0);
    let mut states: Vec<State> =
        tracing::info_span!("Setup").in_scope(|| tables.into_iter().map(|t| State::new(t, chunks, points)).collect());
    let mut point = Vec::with_capacity(n_rounds);
    let rounds = tracing::info_span!("Row rounds").entered();
    for h in 0..n_rounds {
        let _round = tracing::info_span!("Row round", round = h).entered();
        let mut poly = [F128::ZERO; MAX_COEFFS];
        tracing::info_span!("Sum").in_scope(|| {
            // Every live table's tasks in one dispatch.
            let setups: Vec<Option<RoundSetup>> = states
                .iter()
                .map(|s| s.done.is_none().then(|| s.round_setup(points)))
                .collect();
            // Every table that factors out `eq(τ_h, X)` uses the same `τ_h`, the round's coordinate of the shared
            // `τ`. Then the tables leave out the `X` coefficient `f_1` of their
            // summed `factored`, and the round recovers it from the claim: `f_1·X·eq(τ_h, X) = f_1·((1 + τ_h)·X + X²)`,
            // and the claim is the sum of the coefficients from `X` up, so `f_1·τ_h` is the claim plus that sum.
            let taus: Vec<F128> = states
                .iter()
                .filter(|s| s.done.is_none())
                .map(|s| s.tau[s.m - s.log_rows])
                .collect();
            let tau = taus.first().copied().unwrap_or(F128::ZERO);
            let derive = !tau.is_zero() && taus.iter().all(|&t| t == tau);
            let mut first = vec![0];
            for setup in &setups {
                let tasks = setup.as_ref().map_or(0, |r| r.pairs.div_ceil(r.per_task));
                first.push(first.last().unwrap() + tasks);
            }
            poly = parallel::fold_reduce(
                *first.last().unwrap(),
                || [F128::ZERO; MAX_COEFFS],
                |acc, task| {
                    let t = first.partition_point(|&f| f <= task) - 1;
                    let setup = setups[t].as_ref().unwrap();
                    states[t].round_task(setup, task - first[t], chunks, points, derive, acc);
                },
                |mut a, b| {
                    add_into(&mut a, &b);
                    a
                },
            );
            for state in &states {
                match state.done {
                    None => {
                        if let Some(first) = &state.base_first {
                            add_into(&mut poly, first);
                        }
                    }
                    Some((value, corner)) => {
                        poly[0] += value * corner;
                        poly[1] += value * corner;
                    }
                }
            }
            if derive {
                let f1 = (claim + poly[1..].iter().copied().sum::<F128>()) * tau.inv();
                poly[1] += f1 * (F128::ONE + tau);
                poly[2] += f1;
            }
        });
        debug_assert_eq!(claim, poly[1..].iter().copied().sum::<F128>());
        let x = round(&poly[..n_coeffs]);
        claim = primitives::multilinear::poly_eval(&poly[..n_coeffs], x);
        tracing::info_span!("Fold").in_scope(|| {
            for state in &mut states {
                match &mut state.done {
                    None => state.fold(x, chunks, points),
                    Some((_, corner)) => *corner *= F128::ONE + x,
                }
            }
        });
        point.push(x);
    }

    drop(rounds);

    // Each column's values at its table's end come from its bit-slices there, as the verifier's do, so the
    // column rounds see every shift's tables of every column.
    let _ends = tracing::info_span!("Ends").entered();
    // One eq table per table size, and every column's bit-slices in one dispatch.
    let mut eqs: Vec<(usize, Vec<F128>)> = Vec::new();
    for s in &states {
        if !eqs.iter().any(|(m, _)| *m == s.m) {
            eqs.push((s.m, primitives::multilinear::eq_table(&point[..s.m])));
        }
    }
    let eq = |m: usize| eqs.iter().find(|(e, _)| *e == m).map(|(_, t)| t.as_slice()).unwrap();
    let words: Vec<(&[u64], &[F128])> = states
        .iter()
        .flat_map(|s| s.columns.iter().map(move |c| (s.m, c)))
        .map(|(m, c)| {
            assert_eq!(c.words.len(), 1 << m, "a column has its table's rows");
            (c.words, eq(m))
        })
        .collect();
    let mut slices = bit_slices_eq(&words).into_iter();
    let ends: Vec<TableEnd> = states
        .iter()
        .map(|s| {
            let mut end = s.end(s.done.map_or(F128::ONE, |(_, corner)| corner), points);
            for column_end in &mut end.columns {
                let full = ColumnEnd::from_slices(chunks, points, slices.next().unwrap());
                debug_assert_eq!(column_end.values[..2 * d], full.values[..2 * d]);
                *column_end = full;
            }
            end
        })
        .collect();
    let mut columns: Vec<Option<ColumnAt>> = Vec::new();
    columns.resize_with(1 << q_vars, || None);
    for (state, end) in states.iter().zip(&ends) {
        for (column, values) in state.columns.iter().zip(&end.columns) {
            let (coef, shifts, certs) = column.end_coefs(end, points.shifts.max_shift);
            assert!(columns[column.q].is_none(), "two columns at q = {}", column.q);
            columns[column.q] = Some((coef, shifts, values.values.clone(), certs));
        }
    }
    let base = ends.iter().map(|e| e.corner * e.base).sum();
    drop(_ends);
    tracing::info_span!("Free").in_scope(|| drop(states));
    let (column_point, claim) = tracing::info_span!("Pointer-column rounds")
        .in_scope(|| prove_columns(chunks, points, columns, base, claim, round));
    RowEnd {
        point,
        column_point,
        tables: ends,
        claim,
    }
}

/// Coefficients of a row round: degree `d + 2` from a gated coefficient times a pointer, 4 from the base terms.
fn row_coeffs(d: usize) -> usize {
    (d + 2).max(4) + 1
}

/// Coefficients of a column round: degree `d + 1` from a pointer, 3 from a certificate.
fn column_coeffs(d: usize) -> usize {
    (d + 1).max(3) + 1
}

/// The rounds over the pointer-column index `q`, lowest bit first, an empty `q` a zero column; `base` is the tables'
/// base terms, at `q = 0`.
fn prove_columns(
    chunks: &Chunks,
    points: &RowPoints,
    columns: Vec<Option<ColumnAt>>,
    mut base: F128,
    mut claim: F128,
    round: &mut dyn FnMut(&[F128]) -> F128,
) -> (Vec<F128>, F128) {
    let d = chunks.d();
    let slots = points.all_shifts(d);
    let n_shifts = points.shifts.max_shift;
    let n_coeffs = column_coeffs(d);
    let n_vars = columns.len().trailing_zeros() as usize;
    let zero = || {
        (
            F128::ZERO,
            vec![F128::ZERO; n_shifts],
            vec![F128::ZERO; slots.n_values()],
            vec![F128::ZERO; d],
        )
    };
    let mut columns: Vec<ColumnAt> = columns.into_iter().map(|c| c.unwrap_or_else(zero)).collect();
    let mut point = Vec::with_capacity(n_vars);
    for _ in 0..n_vars {
        let mut poly = [F128::ZERO; MAX_COEFFS];
        poly[0] += base;
        poly[1] += base;
        for k in 0..columns.len() / 2 {
            let (lo, hi) = (&columns[2 * k], &columns[2 * k + 1]);
            let pair = |slot: usize| (lo.2[slot], hi.2[slot]);
            let groups: Vec<[F128; 2]> = (0..n_shifts).map(|s| [lo.1[s], lo.1[s] + hi.1[s]]).collect();
            let mut terms = [F128Unreduced::ZERO; MAX_COEFFS];
            pointer_pair(
                &mut terms,
                &slots,
                &[lo.0, lo.0 + hi.0],
                &groups,
                None,
                (&points.clean, |_| None),
                |_| false,
                |_| F128::ZERO,
                pair,
                true,
            );
            add_into(&mut poly, &terms.map(F128Unreduced::reduce));
            for i in 0..d {
                let m = pair_product(pair(slots.eq(i)), pair(slots.bar(i)));
                add_weighted(&mut poly, (lo.3[i], hi.3[i]), [m[0] + points.mirrors[i], m[1], m[2]]);
            }
        }
        debug_assert_eq!(claim, poly[1..].iter().copied().sum::<F128>());
        let x = round(&poly[..n_coeffs]);
        claim = primitives::multilinear::poly_eval(&poly[..n_coeffs], x);
        base *= F128::ONE + x;
        let fold = |a: F128, b: F128| a + x * (a + b);
        let fold_vec = |a: &[F128], b: &[F128]| a.iter().zip(b).map(|(&a, &b)| fold(a, b)).collect::<Vec<_>>();
        columns = (0..columns.len() / 2)
            .map(|k| {
                let (lo, hi) = (&columns[2 * k], &columns[2 * k + 1]);
                (
                    fold(lo.0, hi.0),
                    fold_vec(&lo.1, &hi.1),
                    fold_vec(&lo.2, &hi.2),
                    fold_vec(&lo.3, &hi.3),
                )
            })
            .collect();
        point.push(x);
    }
    let (coef, shifts, values, certs) = &columns[0];
    let last = summand(&slots, &points.mirrors, *coef, shifts, values, certs) + base;
    debug_assert_eq!(claim, last);
    (point, last)
}

#[cfg(test)]
mod tests {
    use super::super::base::{Block, Weight};
    use super::super::pointer::eval_chunk;
    use super::*;
    use crate::form::Form;
    use primitives::field::F64;
    use primitives::multilinear::{eq_eval, eq_table, poly_eval};
    use primitives::test_rng::Rng;

    struct Raw {
        log_rows: usize,
        rows: usize,
        explicit: usize,
        omega: Vec<F128>,
        aux: Vec<Vec<F128>>,
        aux_tail: Vec<F128>,
        words: Vec<Vec<u64>>,
        coefs: Vec<(Coef, Coef, Vec<ShiftGroup>, Vec<F128>)>,
        /// Committed columns for the base terms, the padrow past `explicit`.
        k_columns: Vec<Vec<F64>>,
        padrow: Vec<F64>,
        blocks: Vec<Block>,
        tau: Vec<F128>,
    }

    /// Base blocks over three committed columns: one `ω` block, one gated by column 2, one on every row that
    /// vanishes where column 0 does (on the padrow).
    fn random_blocks(rng: &mut Rng) -> Vec<Block> {
        let form = |rng: &mut Rng, constant: bool| {
            let mut f = Form::new(3);
            f.constant = if constant { rng.ext() } else { F128::ZERO };
            f.coeffs[0] = rng.ext();
            if constant {
                f.coeffs[1] = rng.ext();
            }
            f.prods.push((0, 1, rng.ext()));
            f
        };
        vec![
            Block {
                weight: Weight::Omega,
                gate: None,
                form: form(rng, true),
            },
            Block {
                weight: Weight::Omega,
                gate: Some(2),
                form: form(rng, true),
            },
            Block {
                weight: Weight::Eq,
                gate: None,
                form: form(rng, false),
            },
        ]
    }

    /// A random table: three columns whose neighbouring rows share most chunks, some words not one-hot, padding rows
    /// zero past `explicit`. The first column is read shifted by one, the second by several shifts in two groups.
    fn random_table(
        rng: &mut Rng,
        chunks: &Chunks,
        max_shift: usize,
        (log_rows, rows, explicit): (usize, usize, usize),
    ) -> Raw {
        let mask = (1usize << chunks.width) - 1;
        let mut words = Vec::new();
        let mut coefs = Vec::new();
        for c in 0..3 {
            let mut sigma = rng.next_u64() as usize & mask;
            let column = (0..1 << log_rows)
                .map(|u| {
                    if u >= explicit {
                        return 0;
                    }
                    if rng.next_u32().is_multiple_of(3) {
                        sigma = (sigma + rng.next_u32() as usize % 5) & mask;
                    }
                    if rng.next_u32().is_multiple_of(7) {
                        // Near the top of its window, so a shift leaves it.
                        sigma |= (1 << chunks.widths[0]) - 2;
                        sigma &= mask;
                    }
                    let word = chunks.encode(sigma);
                    if rng.next_u32().is_multiple_of(11) {
                        word ^ 1 << (rng.next_u32() % 64)
                    } else {
                        word
                    }
                })
                .collect();
            words.push(column);
            let coef = |rng: &mut Rng, a: usize| Coef {
                constant: rng.ext(),
                aux: if a < 2 { Some((a, rng.ext())) } else { None },
            };
            let shifts = match c {
                0 => vec![ShiftGroup {
                    coef: coef(rng, 2),
                    weights: vec![(1, rng.ext())],
                }],
                1 => (0..2)
                    .map(|g| ShiftGroup {
                        coef: coef(rng, 2 * g),
                        weights: (0..3)
                            .map(|_| (1 + rng.next_u32() as usize % max_shift, rng.ext()))
                            .collect(),
                    })
                    .collect(),
                _ => Vec::new(),
            };
            coefs.push((coef(rng, c), coef(rng, c + 1), shifts, rng.ext_vec(chunks.d())));
        }
        let padrow = vec![F64::ZERO, F64(rng.next_u64()), F64(rng.next_u64())];
        let k_columns = (0..3)
            .map(|c| {
                (0..1 << log_rows)
                    .map(|u| if u < explicit { F64(rng.next_u64()) } else { padrow[c] })
                    .collect()
            })
            .collect();
        let tau = rng.ext_vec(log_rows);
        let theta = rng.ext();
        let mut omega = eq_table(&tau);
        omega.truncate(rows);
        omega.iter_mut().for_each(|x| *x *= theta);
        Raw {
            log_rows,
            rows,
            explicit,
            omega,
            aux: (0..2).map(|_| rng.ext_vec(explicit)).collect(),
            aux_tail: rng.ext_vec(2),
            words,
            coefs,
            k_columns,
            padrow,
            blocks: random_blocks(rng),
            tau,
        }
    }

    /// The base terms of a table at one row, from its columns' values there.
    fn base_at(t: &Raw, omega: F128, eq: F128, col: &dyn Fn(usize) -> F128) -> F128 {
        t.blocks
            .iter()
            .map(|b| {
                let w = if b.weight == Weight::Omega { omega } else { eq };
                let mut f = b.form.constant;
                for (i, &c) in b.form.coeffs.iter().enumerate() {
                    f += c * col(i);
                }
                for &(x, y, c) in &b.form.prods {
                    f += c * col(x) * col(y);
                }
                w * b.gate.map_or(F128::ONE, col) * f
            })
            .sum()
    }

    /// A folded pair keeps each chunk's tag where the rows agree and is [`MIXED`] where they differ, field by field.
    #[test]
    fn folded_tags_agree_with_the_fieldwise_rule() {
        let mut rng = Rng::new(0x7a6);
        for _ in 0..10_000 {
            let pick = |rng: &mut Rng| -> Tags {
                (0..MAX_CHUNKS).fold(0, |t, i| {
                    t | Tags::from([0u8, 1, 3, 31, MIXED][rng.next_u64() as usize % 5]) << (TAG_BITS * i)
                })
            };
            let (a, b) = (pick(&mut rng), pick(&mut rng));
            let want = (0..MAX_CHUNKS).fold(0, |t, i| {
                let (x, y) = (tag(a, i), tag(b, i));
                t | Tags::from(if x == y { x } else { MIXED }) << (TAG_BITS * i)
            });
            assert_eq!(fold_tags(a, b), want);
        }
    }

    #[test]
    fn row_side_matches_the_naive_sum_and_end() {
        let mut rng = Rng::new(0x407);
        for (width, max_shift, shapes) in [
            (7usize, 12usize, vec![(3usize, 5usize, 6usize), (2, 4, 4)]),
            (13, 12, vec![(5, 19, 25), (6, 64, 64), (2, 1, 3), (0, 1, 1)]),
            (13, 3, vec![(5, 19, 25), (6, 64, 64), (2, 1, 3), (0, 0, 0)]),
            (22, 12, vec![(4, 16, 16), (7, 100, 100), (3, 7, 8)]),
            (23, 12, vec![(4, 16, 16), (3, 7, 8)]),
            (24, 12, vec![(5, 30, 32), (3, 7, 8)]),
            (9, 12, vec![(5, 19, 25), (2, 4, 4)]),
            (1, 1, vec![(3, 6, 6), (1, 2, 2)]),
        ] {
            let chunks = Chunks::new(width);
            let d = chunks.d();
            let points = RowPoints::new(&chunks, &rng.ext_vec(width), max_shift);
            let raw: Vec<Raw> = shapes
                .iter()
                .map(|&s| random_table(&mut rng, &chunks, max_shift, s))
                .collect();
            let n_columns = 3 * raw.len();
            let q_vars = n_columns.next_power_of_two().trailing_zeros() as usize;
            let mut q = 0;
            fn base(t: &Raw) -> Base<'_> {
                Base::new(
                    t.blocks.clone(),
                    t.k_columns.iter().map(Vec::as_slice).collect(),
                    &t.padrow,
                    Some(eq_table(&t.tau)),
                )
            }
            let tables: Vec<RowTable> = raw
                .iter()
                .map(|t| RowTable {
                    log_rows: t.log_rows,
                    rows: t.rows,
                    explicit: t.explicit,
                    omega: t.omega.clone(),
                    tau: t.tau.clone(),
                    aux: t.aux.clone(),
                    aux_tail: t.aux_tail.clone(),
                    columns: t
                        .words
                        .iter()
                        .zip(&t.coefs)
                        .map(|(w, (o, a, g, e))| {
                            q += 1;
                            RowColumn {
                                words: w,
                                index: chunks.decode_all(w),
                                omega: *o,
                                act: *a,
                                shifts: g.clone(),
                                cert: e.clone(),
                                q: q - 1,
                            }
                        })
                        .collect(),
                    base: base(t),
                    base_first: base(t).omega_round(&t.omega, t.tau.first().copied()),
                })
                .collect();

            // Per row of a column: its coefficient, its coefficient per shift, `ω`, and the chunk functionals.
            let slots = points.all_shifts(d);
            let starts = &points.shifts.tables[1..];
            let chunks_ref = &chunks;
            let shift_coefs = |groups: &[ShiftGroup], weight: &dyn Fn(&Coef) -> F128| {
                let mut out = vec![F128::ZERO; max_shift];
                for g in groups {
                    for &(s, mu) in &g.weights {
                        out[s - 1] += weight(&g.coef) * mu;
                    }
                }
                out
            };
            let row_value = |t: &Raw, u: usize, column: usize| -> (F128, Vec<F128>, F128, Vec<F128>) {
                let (om, act) = if u < t.rows {
                    (t.omega[u], F128::ONE)
                } else {
                    (F128::ZERO, F128::ZERO)
                };
                let aux = |a: usize| if u < t.explicit { t.aux[a][u] } else { t.aux_tail[a] };
                let w = t.words[column][u];
                let (co, ca, groups, _) = &t.coefs[column];
                let weight = |c: &Coef| c.constant + c.aux.map_or(F128::ZERO, |(a, s)| s * aux(a));
                let vals = (0..slots.n_values())
                    .map(|k| {
                        let (i, table) = slots.table(k, &points, starts);
                        eval_chunk(chunks_ref, table, w, i)
                    })
                    .collect();
                let shifts = shift_coefs(groups, &|c| om * weight(c));
                (om * weight(co) + act * weight(ca), shifts, om, vals)
            };
            let row_summand = |t: &Raw, column: usize, coef: F128, shifts: &[F128], om: F128, vals: &[F128]| {
                let certs: Vec<F128> = t.coefs[column].3.iter().map(|&e| om * e).collect();
                summand(&slots, &points.mirrors, coef, shifts, vals, &certs)
            };
            let mut total = F128::ZERO;
            for t in &raw {
                let eq = eq_table(&t.tau);
                for u in 0..1 << t.log_rows {
                    for column in 0..3 {
                        let (coef, shifts, om, vals) = row_value(t, u, column);
                        total += row_summand(t, column, coef, &shifts, om, &vals);
                    }
                    let om = if u < t.rows { t.omega[u] } else { F128::ZERO };
                    total += base_at(t, om, eq[u], &|c| F128::from(t.k_columns[c][u]));
                }
            }

            let mut claim = total;
            let mut n_coeffs = Vec::new();
            let mut claims = Vec::new();
            let end = prove(&chunks, &points, tables, q_vars, total, &mut |poly| {
                assert_eq!(claim, poly[1..].iter().copied().sum::<F128>(), "a round's sum");
                claims.push(claim);
                n_coeffs.push(poly.len());
                let x = rng.ext();
                claim = poly_eval(poly, x);
                x
            });
            claims.push(claim);
            assert_eq!(claim, end.claim);
            let max_log = shapes.iter().map(|s| s.0).max().unwrap();
            assert!(n_coeffs[..max_log].iter().all(|&n| n == row_coeffs(d)));
            assert!(n_coeffs[max_log..].iter().all(|&n| n == column_coeffs(d)));

            // The end, from the rows' multilinear extensions at χ and then the columns' at q*.
            let chi = &end.point;
            let mut columns = Vec::new();
            let mut base = F128::ZERO;
            for (t, table_end) in raw.iter().zip(&end.tables) {
                let eqs = eq_table(&chi[..t.log_rows]);
                let corner: F128 = chi[t.log_rows..].iter().map(|&x| F128::ONE + x).product();
                assert_eq!(table_end.corner, corner);
                // `ω`, `act` and each aux column are separate factors of the summand, so each is its own extension.
                let mle = |f: &dyn Fn(usize) -> F128| eqs.iter().enumerate().map(|(u, &e)| e * f(u)).sum::<F128>();
                let om = mle(&|u| if u < t.rows { t.omega[u] } else { F128::ZERO });
                let act = mle(&|u| if u < t.rows { F128::ONE } else { F128::ZERO });
                let aux: Vec<F128> = (0..2)
                    .map(|a| mle(&|u| if u < t.explicit { t.aux[a][u] } else { t.aux_tail[a] }))
                    .collect();
                assert_eq!(table_end.omega, om);
                let k_values: Vec<F128> = (0..3).map(|c| mle(&|u| F128::from(t.k_columns[c][u]))).collect();
                let table_base = base_at(t, om, eq_eval(&t.tau, &chi[..t.log_rows]), &|c| k_values[c]);
                assert_eq!(table_end.base, table_base);
                base += corner * table_base;
                for column in 0..3 {
                    let mut vals = vec![F128::ZERO; slots.n_values()];
                    for (u, &e) in eqs.iter().enumerate() {
                        let (_, _, _, g) = row_value(t, u, column);
                        for (v, g) in vals.iter_mut().zip(g) {
                            *v += e * g;
                        }
                    }
                    let (co, ca, groups, cert) = &t.coefs[column];
                    let weight = |c: &Coef| c.constant + c.aux.map_or(F128::ZERO, |(a, s)| s * aux[a]);
                    let coef = om * weight(co) + act * weight(ca);
                    assert_eq!(table_end.columns[column].values, vals);
                    let shifts = shift_coefs(groups, &|c| corner * om * weight(c));
                    let certs: Vec<F128> = cert.iter().map(|&e| corner * om * e).collect();
                    columns.push((corner * coef, shifts, vals, certs));
                }
            }
            let at_chi: F128 = columns
                .iter()
                .map(|(c, s, v, e)| summand(&slots, &points.mirrors, *c, s, v, e))
                .sum();
            assert_eq!(claims[max_log], at_chi + base, "the row rounds end on the columns' sum");
            let eqq = eq_table(&end.column_point);
            let mle = |f: &dyn Fn(usize) -> F128| (0..columns.len()).map(|q| eqq[q] * f(q)).sum::<F128>();
            let coef = mle(&|q| columns[q].0);
            let shifts: Vec<F128> = (0..max_shift).map(|s| mle(&|q| columns[q].1[s])).collect();
            let vals: Vec<F128> = (0..slots.n_values()).map(|j| mle(&|q| columns[q].2[j])).collect();
            let certs: Vec<F128> = (0..d).map(|i| mle(&|q| columns[q].3[i])).collect();
            let base_q: F128 = end.column_point.iter().map(|&x| F128::ONE + x).product();
            let last = summand(&slots, &points.mirrors, coef, &shifts, &vals, &certs);
            assert_eq!(end.claim, last + base_q * base);
        }
    }
}
