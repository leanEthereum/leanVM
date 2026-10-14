//! The dense reduction: claims on the dense polynomials to one evaluation of each, at prefixes of one point.
//!
//! The claims' terms are batched by the powers of one challenge `theta`, then one degree-two sumcheck runs over
//!
//! ```text
//! sum_j sum_x Xi_j(x) P_j(x),    Xi_j = sum_{t on P_j} theta^t scale_t eq(p_t, .)
//! ```
//!
//! lowest variable first.
//! A polynomial of fewer variables is bound early, and its share then waits on the rest: each later round multiplies it by its challenge.

use super::DensePoly;
use super::{DenseTables, Entry, Msg, ReduceError, TILE};
use fiat_shamir::ProverState;
use fiat_shamir::arith::{Arith, Verifier};
use parallel::ChunkView;
use primitives::field::{F64, F192, F192Unreduced};
use primitives::multilinear::{eq_table, eq_table_seeded, mle_eval_par};
use primitives::write_only;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::ops::Range;

/// Public coordinates of a point: `len` bits, lowest first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Bits {
    /// The bits, as an integer.
    pub(crate) value: usize,
    /// How many there are.
    pub(crate) len: usize,
}

/// One claim on a dense polynomial `P`, at the shared prefix, then public bits, then the kind's bits: `s P(low, bits, top) = s v`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DenseTerm<E> {
    /// How many of the shared prefix's coordinates the point starts with.
    pub(crate) n_low: usize,
    /// The public coordinates after them.
    pub(crate) bits: Bits,
    /// The last coordinates, a child's kind's bits, lowest first, if any.
    pub(crate) top: Vec<E>,
    /// A factor both sides carry, one when absent: a zero scale makes the claim vacuous.
    pub(crate) scale: Option<E>,
    /// The claimed value.
    pub(crate) value: E,
}

/// Claims on one dense polynomial at points sharing a prefix, each batched as a claim of its own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DenseClaim<E> {
    /// The polynomial.
    pub(crate) poly: DensePoly,
    /// The prefix every claim's point starts with a part of.
    pub(crate) low: Vec<E>,
    /// The claims.
    pub(crate) terms: Vec<DenseTerm<E>>,
}

/// Each dense polynomial's variables: the bytecode table's, the image's, the fixed polynomial's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DenseVars(pub(crate) [usize; DensePoly::COUNT]);

/// What the dense reduction leaves: one point, and each reduced polynomial's value at its prefix.
///
/// A polynomial no claim weighs is not reduced and has no value.
pub(crate) struct DenseReduced<E> {
    /// The point, one coordinate per round.
    pub(crate) point: Vec<E>,
    /// Each polynomial's value at its prefix of the point, if reduced.
    pub(crate) values: [Option<E>; DensePoly::COUNT],
}

/// The dense reduction's prover: each reduced polynomial and its weight table, both folded as the challenges come.
pub(crate) struct DenseProver<'a> {
    /// The reduced polynomials, in order.
    parts: Vec<Part<'a>>,
    /// The challenges so far.
    point: Vec<F192>,
    /// The next round's message.
    message: [F192; 2],
}

/// One reduced polynomial in the prover: its variables, its table, and its weight table `Xi_j`.
///
/// The weight table is zero past the prefix its terms touch, so each round folds and sums that prefix alone. Where the
/// prefix's last entry pairs with one past it, that entry is the polynomial's value on its block at the challenges so
/// far, evaluated from the table as given.
///
/// When each of its blocks is a sum of few low tables times high ones, the weight table stays factored while the low
/// tables have variables left: a round sums each low table against the table, then scales by the high one. Past that,
/// or from the start otherwise, it is a table.
struct Part<'a> {
    /// The polynomial's variables.
    n_vars: usize,
    /// Its values as given.
    base: &'a [F64],
    /// The length of the prefix its terms touch, at least one.
    live: usize,
    /// The rounds before its weight table is written out.
    factored: usize,
    /// Its weight table's blocks, folded, until it is written out.
    blocks: Vec<Block>,
    /// Its weight table once written out, folded.
    weights: Vec<F192>,
    /// Its values, folded from the first round on.
    table: Vec<F192>,
    /// The buffers the next fold writes.
    spare: [Vec<F192>; 2],
}

/// One term of a weight table: `c eq(p, .)` on one aligned block of the table.
struct Placed {
    /// The term's coefficient.
    coef: F192,
    /// The point's coordinates before its trailing Boolean ones.
    point: Vec<F192>,
    /// The block's offset in the table, which the trailing Boolean coordinates name.
    offset: usize,
}

impl Bits {
    /// No coordinates.
    pub(crate) const NONE: Self = Self { value: 0, len: 0 };
}

impl<E: Copy> DenseTerm<E> {
    /// The same claim, each element mapped by `f`.
    pub(super) fn map<T>(&self, f: &mut impl FnMut(E) -> T) -> DenseTerm<T> {
        DenseTerm {
            n_low: self.n_low,
            bits: self.bits,
            top: self.top.iter().map(|&x| f(x)).collect(),
            scale: self.scale.map(&mut *f),
            value: f(self.value),
        }
    }
}

impl<E> DenseClaim<E> {
    /// The polynomials some claim of these weighs, which the reduction reduces.
    fn weighed(claims: &[Self]) -> [bool; DensePoly::COUNT] {
        DensePoly::ALL.map(|p| claims.iter().any(|c| c.poly == p))
    }
}

impl<E: Copy + PartialEq> DenseReduced<E> {
    /// Verify the reduction of the claims.
    ///
    /// # Errors
    ///
    /// Returns a malformed stream, or the final identity's failure.
    pub(crate) fn verify<V: Verifier<E = E>>(
        v: &mut V,
        vars: &DenseVars,
        claims: &[DenseClaim<E>],
    ) -> Result<Self, ReduceError> {
        let reduced = DenseClaim::weighed(claims);
        let theta = v.verifier_message();
        let n_terms = claims.iter().map(|c| c.terms.len()).sum();
        let powers = v.powers(theta, n_terms);
        let zero = v.zero();
        let terms = claims.iter().flat_map(|c| &c.terms);
        let mut claim = (terms.zip(&powers)).fold(zero, |acc, (t, &power)| {
            let value = t.scale.map_or(t.value, |s| v.mul(s, t.value));
            v.mul_add(power, value, acc)
        });

        let rounds = vars.rounds(reduced);
        let mut point = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let h = v.read_round(3, claim, None)?;
            let r = v.verifier_message();
            claim = v.poly_eval(&h, r);
            point.push(r);
        }
        let mut values = [None; DensePoly::COUNT];
        for (value, reduced) in values.iter_mut().zip(reduced) {
            if reduced {
                *value = Some(v.prover_message()?);
            }
        }
        let weights = vars.final_weights(v, claims, &powers, &point);
        let total = (values.iter().zip(weights)).fold(zero, |acc, (value, weight)| match (value, weight) {
            (Some(value), Some(weight)) => v.mul_add(*value, weight, acc),
            _ => acc,
        });
        v.ensure_eq(claim, total, || ReduceError::Dense)?;
        Ok(Self { point, values })
    }
}

impl<E: Copy> DenseClaim<E> {
    /// `s P(point) = s v`, the scale `s` one when absent.
    pub(crate) fn at(poly: DensePoly, point: Vec<E>, scale: Option<E>, value: E) -> Self {
        let n_low = point.len();
        Self {
            poly,
            low: point,
            terms: vec![DenseTerm {
                n_low,
                bits: Bits::NONE,
                top: Vec::new(),
                scale,
                value,
            }],
        }
    }

    /// `P(point, bits) = v`: a point, then public coordinates.
    pub(crate) fn at_bits(poly: DensePoly, point: Vec<E>, bits: Bits, value: E) -> Self {
        let mut claim = Self::at(poly, point, None, value);
        claim.terms[0].bits = bits;
        claim
    }

    /// The same claims, each element mapped by `f`.
    pub(super) fn map<T>(&self, f: &mut impl FnMut(E) -> T) -> DenseClaim<T> {
        DenseClaim {
            poly: self.poly,
            low: self.low.iter().map(|&x| f(x)).collect(),
            terms: self.terms.iter().map(|t| t.map(f)).collect(),
        }
    }
}

impl DenseVars {
    /// The rounds: the most variables a reduced polynomial has.
    fn rounds(&self, reduced: [bool; DensePoly::COUNT]) -> usize {
        (self.0.iter().zip(reduced))
            .filter_map(|(&n, r)| r.then_some(n))
            .max()
            .unwrap_or(0)
    }

    /// Each reduced polynomial's weight in the final identity: `Xi_j` at its prefix of `point`, times the later challenges.
    pub(super) fn final_weights<A: Arith>(
        &self,
        a: &mut A,
        claims: &[DenseClaim<A::E>],
        powers: &[A::E],
        point: &[A::E],
    ) -> [Option<A::E>; DensePoly::COUNT] {
        let mut weights = [None; DensePoly::COUNT];
        let mut powers = powers.iter().copied();
        for claim in claims {
            let n = self.0[claim.poly as usize];
            let xi = claim.weight_at(a, &mut powers, &point[..n]);
            let slot = &mut weights[claim.poly as usize];
            *slot = Some(slot.map_or(xi, |w| a.add(w, xi)));
        }
        for (weight, &n) in weights.iter_mut().zip(&self.0) {
            if let Some(w) = weight {
                *w = point[n.min(point.len())..].iter().fold(*w, |acc, &x| a.mul(acc, x));
            }
        }
        weights
    }
}

impl<E: Copy> DenseClaim<E> {
    /// `sum_t power_t scale_t eq(p_t, r)`, the powers taken in order, the terms sharing their low point's prefix.
    fn weight_at<A: Arith<E = E>>(&self, a: &mut A, powers: &mut impl Iterator<Item = E>, r: &[E]) -> E {
        let longest = self.terms.iter().map(|t| t.n_low).max().unwrap_or(0);
        let one = a.one();
        let mut prefix = Vec::with_capacity(longest + 1);
        prefix.push(one);
        for (j, (&p, &x)) in self.low.iter().zip(r).take(longest).enumerate() {
            let s = a.add(p, x);
            let next = a.times_one_plus(prefix[j], s);
            prefix.push(next);
        }
        let zero = a.zero();
        self.terms.iter().fold(zero, |acc, t| {
            let DenseTerm {
                n_low,
                bits,
                ref top,
                scale,
                ..
            } = *t;
            let at_bits = n_low + bits.len;
            assert_eq!(
                at_bits + top.len(),
                r.len(),
                "a term's point has its polynomial's variables"
            );
            let bits_eq = a.eq_bits(bits.value, &r[n_low..at_bits]);
            let mut eq = a.mul(prefix[n_low], bits_eq);
            for (&top, &x) in top.iter().zip(&r[at_bits..]) {
                let s = a.add(top, x);
                eq = a.times_one_plus(eq, s);
            }
            let power = powers.next().expect("a power per term");
            let weight = scale.map_or(power, |s| a.mul(power, s));
            a.mul_add(weight, eq, acc)
        })
    }
}

impl DenseTerm<F192> {
    /// The term at its coefficient, placed in its polynomial's table: its point's trailing Boolean coordinates name a block.
    fn placed(&self, low: &[F192], coef: F192) -> Placed {
        let mut point = low[..self.n_low].to_vec();
        point.extend((0..self.bits.len).map(|i| F192::new((self.bits.value >> i & 1) as u64, 0, 0)));
        point.extend(&self.top);
        let boolean = |x: &F192| *x == F192::ZERO || *x == F192::ONE;
        let k = point.len() - point.iter().rev().take_while(|x| boolean(x)).count();
        let offset = (point[k..].iter().enumerate())
            .map(|(i, &x)| usize::from(x == F192::ONE) << (k + i))
            .sum();
        point.truncate(k);
        Placed { coef, point, offset }
    }
}

impl<'a> DenseProver<'a> {
    /// Prove the reduction of the claims, which must be true of the tables.
    pub(super) fn prove(ps: &mut ProverState, vars: &DenseVars, tables: &'a DenseTables, claims: &[DenseClaim<F192>]) {
        let theta = ps.verifier_message();
        let mut prover = Self::new(vars, tables, claims, theta);
        for i in 0..prover.rounds() {
            ps.prover_messages(&prover.message());
            let r = ps.verifier_message();
            prover.bind(i, r);
        }
        ps.prover_messages(&prover.finals());
    }

    /// The prover of the claims under the batching challenge `theta`.
    pub(super) fn new(vars: &DenseVars, tables: &'a DenseTables, claims: &[DenseClaim<F192>], theta: F192) -> Self {
        let reduced = DenseClaim::weighed(claims);
        let mut placed: Vec<Vec<Placed>> = DensePoly::ALL.map(|_| Vec::new()).into();
        let mut power = F192::ONE;
        for claim in claims {
            for term in &claim.terms {
                let coef = term.scale.map_or(power, |s| power * s);
                if !coef.is_zero() {
                    placed[claim.poly as usize].push(term.placed(&claim.low, coef));
                }
                power *= theta;
            }
        }
        let mut message = Msg::default();
        let parts: Vec<Part> = (DensePoly::ALL.into_iter().zip(placed))
            .filter(|&(p, _)| reduced[p as usize])
            .map(|(p, terms)| {
                let n_vars = vars.0[p as usize];
                let base = &tables.0[p as usize];
                assert_eq!(base.len(), 1 << n_vars, "a dense table has its variables");
                let (part, first) = Part::new(n_vars, base, &terms);
                message ^= first;
                part
            })
            .collect();
        Self {
            point: Vec::with_capacity(parts.iter().map(|p| p.n_vars).max().unwrap_or(0)),
            parts,
            message: message.reduce(),
        }
    }

    /// The number of rounds.
    pub(super) fn rounds(&self) -> usize {
        self.parts.iter().map(|p| p.n_vars).max().unwrap_or(0)
    }

    /// The next round's message: `h(0)` and the leading coefficient, the claim fixing the linear one.
    ///
    /// A polynomial bound already contributes a linear term only, which the claim accounts for.
    pub(super) const fn message(&self) -> [F192; 2] {
        self.message
    }

    /// Bind round `i`'s variable to `r`, and build the next round's message from the folded pairs.
    pub(super) fn bind(&mut self, i: usize, r: F192) {
        assert_eq!(i, self.point.len(), "rounds come in order");
        self.point.push(r);
        let point = &self.point;
        let message: Msg = (self.parts.iter_mut().filter(|p| p.n_vars > i))
            .map(|p| p.bind(point))
            .sum();
        self.message = message.reduce();
    }

    /// Each reduced polynomial's value at its prefix of the point.
    pub(super) fn finals(&self) -> Vec<F192> {
        (self.parts.iter())
            .map(|p| p.table.first().copied().unwrap_or_else(|| F192::from(p.base[0])))
            .collect()
    }
}

impl<'a> Part<'a> {
    /// The part of the polynomial `base` of `n_vars` variables, weighed by `terms`, and its first round's message.
    fn new(n_vars: usize, base: &'a [F64], terms: &[Placed]) -> (Self, Msg) {
        let blocks = Block::all(terms);
        let factored = if blocks.iter().all(|b| b.groups.len() <= FACTORED_GROUPS) {
            blocks
                .iter()
                .map(|b| b.row.trailing_zeros() as usize)
                .min()
                .unwrap_or(0)
        } else {
            0
        };
        let live = terms
            .iter()
            .map(|t| t.offset + (1 << t.point.len()))
            .max()
            .unwrap_or(0)
            .max(1);
        let mut part = Self {
            n_vars,
            base,
            live,
            factored,
            blocks: Vec::new(),
            weights: Vec::new(),
            table: Vec::new(),
            spare: [Vec::new(), Vec::new()],
        };
        let len = part.len_at(0);
        let (source, w_len) = if factored > 0 {
            (Source::Blocks(&blocks), 0)
        } else {
            (Source::Write(&blocks), len)
        };
        let mut weights = Vec::with_capacity(w_len);
        // SAFETY: the pass writes every entry before any is read.
        let w_slots = unsafe { write_only(&mut weights.spare_capacity_mut()[..w_len]) };
        let wc = ChunkView::new(w_slots, PAR_LEN);
        let message = Msg::sum_tasks(len.div_ceil(PAR_LEN), |c| {
            let (from, to) = (c * PAR_LEN, len.min((c + 1) * PAR_LEN));
            let touching = source.touching(from, to);
            // SAFETY: each chunk index is taken once, and the table outlives the dispatch.
            let wo: &mut [F192] = if wc.is_empty() { &mut [] } else { unsafe { wc.get(c) } };
            (from..to)
                .step_by(TILE)
                .map(|a| {
                    let b = to.min(a + TILE);
                    let wo = wo.get_mut(a - from..b - from).unwrap_or_default();
                    source.message(&touching, a, &base[a..b], wo, F192::ZERO)
                })
                .sum()
        });
        // SAFETY: the pass wrote all `w_len` entries.
        unsafe { weights.set_len(w_len) };
        part.blocks = blocks;
        part.weights = weights;
        (part, message)
    }

    /// The entries kept after `i` rounds: the pairs covering the live prefix, or the value once bound.
    const fn len_at(&self, i: usize) -> usize {
        if i < self.n_vars {
            2 * self.live.div_ceil(2 << i)
        } else {
            1
        }
    }

    /// Bind the next variable to the last challenge of `point`; the next round's message, zero after the last.
    fn bind(&mut self, point: &[F192]) -> Msg {
        let i = point.len() - 1;
        let r = point[i];
        if i < self.factored {
            self.blocks.iter_mut().for_each(|b| b.fold(r));
        }
        let half = self.live.div_ceil(2 << i);
        let len = self.len_at(i + 1);
        let extra = (len > half).then(|| {
            let size = 2 << i;
            mle_eval_par(&self.base[half * size..(half + 1) * size], point)
        });
        let source = match (i + 1).cmp(&self.factored) {
            Ordering::Less => Source::Blocks(&self.blocks),
            Ordering::Equal => Source::Write(&self.blocks),
            Ordering::Greater => Source::Fold(&self.weights),
        };
        let w_len = if matches!(source, Source::Blocks(_)) || len == 1 {
            0
        } else {
            len
        };
        let [w_spare, t_spare] = &mut self.spare;
        let mut w = buffer(w_spare, w_len);
        let mut t = buffer(t_spare, len);
        // SAFETY: the fold writes every entry of both before any is read.
        let (w_out, t_out) = unsafe {
            (
                write_only(&mut w.spare_capacity_mut()[..w_len]),
                write_only(&mut t.spare_capacity_mut()[..len]),
            )
        };
        let message = if i == 0 {
            source.fold_round(self.base, r, half, extra, w_out, t_out)
        } else {
            source.fold_round(&self.table, r, half, extra, w_out, t_out)
        };
        // SAFETY: the fold wrote the first `w_len` and `len` entries.
        unsafe {
            w.set_len(w_len);
            t.set_len(len);
        }
        if i + 1 == self.factored {
            self.blocks = Vec::new();
        }
        self.spare = [
            std::mem::replace(&mut self.weights, w),
            std::mem::replace(&mut self.table, t),
        ];
        message
    }
}

/// An empty buffer with room for `len` entries, reusing `spare`'s allocation.
fn buffer(spare: &mut Vec<F192>, len: usize) -> Vec<F192> {
    let mut v = std::mem::take(spare);
    if v.capacity() < len {
        return Vec::with_capacity(len);
    }
    v.clear();
    v
}

/// Below this many entries a pass runs on the calling thread; a task of the pool takes this many.
const PAR_LEN: usize = 1 << 12;

/// Where a pass finds the weights of the entries it reaches.
#[derive(Clone, Copy)]
enum Source<'w> {
    /// The blocks, at the pass's level: the weights stay factored.
    Blocks(&'w [Block]),
    /// The blocks, at the pass's level: the pass writes the weights out.
    Write(&'w [Block]),
    /// The table one level up: the pass folds it.
    Fold(&'w [F192]),
}

impl Source<'_> {
    /// The blocks reaching entries `from..to`.
    fn touching(&self, from: usize, to: usize) -> Vec<&Block> {
        match *self {
            Self::Blocks(blocks) | Self::Write(blocks) => (blocks.iter())
                .filter(|b| b.start < to && from < b.start + b.len)
                .collect(),
            Self::Fold(_) => Vec::new(),
        }
    }

    /// The message of the table's entries `a..a + t.len()`, `touching` the blocks reaching them. Unless the weights stay
    /// factored, the pass writes them to `w`: from the blocks, or folding the table one level up by `r`.
    fn message<T: Entry>(&self, touching: &[&Block], a: usize, t: &[T], w: &mut [F192], r: F192) -> Msg {
        match *self {
            Self::Blocks(_) => touching.iter().map(|b| b.message(a, t)).sum(),
            Self::Write(_) => {
                let mut acc = [F192Unreduced::ZERO; TILE];
                let acc = &mut acc[..w.len()];
                for b in touching {
                    b.add_to(a, acc);
                }
                for (w, x) in w.iter_mut().zip(acc) {
                    *w = x.reduce();
                }
                T::dot(w, t)
            }
            Self::Fold(table) => {
                F192::fold_into(&table[2 * a..2 * (a + w.len())], r, w);
                T::dot(w, t)
            }
        }
    }

    /// One round's fold of a part's table `t` into `t_out`, its weights as `source` says into `w_out`, and the next
    /// round's message.
    ///
    /// The first `half` entries fold from pairs. Past them, when `t_out` is one longer, are the weight's zero and the
    /// table's `extra`. The message is over the folded pairs, none when one entry is left.
    fn fold_round<T: Entry>(
        self,
        t: &[T],
        r: F192,
        half: usize,
        extra: Option<F192>,
        w_out: &mut [F192],
        t_out: &mut [F192],
    ) -> Msg {
        if t_out.len() == 1 {
            t_out[0] = T::fold(t[0], t[1], r);
            return Msg::default();
        }
        let pairs = half & !1;
        let tc = ChunkView::new(&mut t_out[..pairs], PAR_LEN);
        let w_pairs = pairs.min(w_out.len());
        let wc = ChunkView::new(&mut w_out[..w_pairs], PAR_LEN);
        let mut message = Msg::sum_tasks(pairs.div_ceil(PAR_LEN), |c| {
            let (from, to) = (c * PAR_LEN, pairs.min((c + 1) * PAR_LEN));
            let touching = self.touching(from, to);
            // SAFETY: each chunk index is taken once, and both tables outlive the dispatch.
            let (tables, wo): (&mut [F192], &mut [F192]) =
                unsafe { (tc.get(c), if wc.is_empty() { &mut [] } else { wc.get(c) }) };
            (from..to)
                .step_by(TILE)
                .map(|a| {
                    let b = to.min(a + TILE);
                    let tile = &mut tables[a - from..b - from];
                    T::fold_into(&t[2 * a..2 * b], r, tile);
                    let wo = wo.get_mut(a - from..b - from).unwrap_or_default();
                    self.message(&touching, a, tile, wo, r)
                })
                .sum()
        });
        if let Some(extra) = extra {
            let k = half - 1;
            t_out[k..].copy_from_slice(&[T::fold(t[2 * k], t[2 * k + 1], r), extra]);
            let w = &mut w_out[k..];
            w[0] = match self {
                Source::Blocks(_) => unreachable!("a factored level's prefix is whole pairs"),
                Source::Write(blocks) => {
                    let mut acc = [F192Unreduced::ZERO];
                    blocks.iter().for_each(|b| b.add_to(k, &mut acc));
                    acc[0].reduce()
                }
                Source::Fold(table) => F192::fold(table[2 * k], table[2 * k + 1], r),
            };
            w[1] = F192::ZERO;
            message ^= F192::dot(w, &t_out[k..]);
        }
        message
    }
}

/// The variables of a block's low tables, which a pass keeps in L1.
const LOW_VARS: usize = 10;

/// The most groups a block may have for its part's weights to stay factored.
const FACTORED_GROUPS: usize = 2;

/// One aligned block of a weight table at the current level, `sum_g low_g ⊗ high_g`: terms sharing their low
/// coordinates share the low table, against the sum of their high ones scaled by their coefficients.
struct Block {
    /// The block's first entry.
    start: usize,
    /// Its entries.
    len: usize,
    /// The entries of its low tables, one row of the block.
    row: usize,
    /// Each group's low and high tables.
    groups: Vec<(Vec<F192>, Vec<F192>)>,
}

impl Block {
    /// The blocks of a weight table's terms, at the first level.
    fn all(terms: &[Placed]) -> Vec<Self> {
        let mut by_block: BTreeMap<(usize, usize), Vec<&Placed>> = BTreeMap::new();
        for t in terms {
            by_block.entry((t.offset, t.point.len())).or_default().push(t);
        }
        by_block.values().map(|terms| Self::new(terms)).collect()
    }

    /// The block of these terms, which share their offset and length.
    fn new(terms: &[&Placed]) -> Self {
        let k = terms[0].point.len();
        let l = k.min(LOW_VARS);
        let mut groups: Vec<(&[F192], Vec<F192>)> = Vec::new();
        for t in terms {
            let (low, high) = t.point.split_at(l);
            let high = eq_table_seeded(high, t.coef);
            match groups.iter_mut().find(|(p, _)| *p == low) {
                Some((_, sum)) => sum.iter_mut().zip(high).for_each(|(s, e)| *s += e),
                None => groups.push((low, high)),
            }
        }
        Self {
            start: terms[0].offset,
            len: 1 << k,
            row: 1 << l,
            groups: groups.into_iter().map(|(p, high)| (eq_table(p), high)).collect(),
        }
    }

    /// Bind the lowest variable, one of the low tables', to `r`.
    fn fold(&mut self, r: F192) {
        for (low, _) in &mut self.groups {
            let mut folded = vec![F192::ZERO; low.len() / 2];
            F192::fold_into(low, r, &mut folded);
            *low = folded;
        }
        (self.start, self.len, self.row) = (self.start / 2, self.len / 2, self.row / 2);
    }

    /// `f(h, x, run)` for each run of entries `a..a + n` in the block, `run` in row `h` from column `x`.
    fn runs(&self, a: usize, n: usize, mut f: impl FnMut(usize, usize, Range<usize>)) {
        let (mut lo, hi) = (a.max(self.start), (a + n).min(self.start + self.len));
        while lo < hi {
            let (h, x) = ((lo - self.start) / self.row, (lo - self.start) % self.row);
            let end = hi.min(lo - x + self.row);
            f(h, x, lo..end);
            lo = end;
        }
    }

    /// `acc[y] += Xi(a + y)` over the block.
    fn add_to(&self, a: usize, acc: &mut [F192Unreduced]) {
        self.runs(a, acc.len(), |h, x, run| {
            let acc = &mut acc[run.start - a..run.end - a];
            for (low, high) in &self.groups {
                let (e, low) = (high[h], &low[x..x + acc.len()]);
                let (quads, rest) = low.as_chunks::<4>();
                let (acc_quads, acc_rest) = acc.as_chunks_mut::<4>();
                for (s, &q) in acc_quads.iter_mut().zip(quads) {
                    for (s, p) in s.iter_mut().zip(F192::mul_unreduced4([e; 4], q)) {
                        *s ^= p;
                    }
                }
                for (s, &l) in acc_rest.iter_mut().zip(rest) {
                    *s ^= e.mul_unreduced(l);
                }
            }
        });
    }

    /// The message of the table's entries `a..a + t.len()` against the block's weights: each row's run is summed
    /// against the low tables, then scaled by the high ones. A run is whole pairs while a row has two entries.
    fn message<T: Entry>(&self, a: usize, t: &[T]) -> Msg {
        let mut m = Msg::default();
        self.runs(a, t.len(), |h, x, run| {
            let t = &t[run.start - a..run.end - a];
            for (low, high) in &self.groups {
                let [c0, c2] = T::dot(&low[x..x + t.len()], t).reduce();
                m ^= Msg::new(high[h].mul_unreduced(c0), high[h].mul_unreduced(c2));
            }
        });
        m
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::tree::reduce;

    use fiat_shamir::arith::{Arith, Native};
    use fiat_shamir::{ProverState, SessionId, VerifierState};
    use primitives::multilinear::mle_eval;
    use primitives::test_util::Rng;

    // Claims on every table at random points, one of several terms with public bits, a kind bit and a scale, the last.
    fn dense_claims(rng: &mut Rng, tables: &DenseTables, vars: &DenseVars) -> Vec<DenseClaim<F192>> {
        let mut claims = Vec::new();
        for poly in DensePoly::ALL {
            let table = &tables.0[poly as usize];
            for _ in 0..2 {
                let point = rng.ext_vec(vars.0[poly as usize]);
                let value = mle_eval(table, &point);
                claims.push(DenseClaim::at(poly, point, None, value));
            }
        }
        let n = vars.0[DensePoly::Fixed as usize];
        let low = rng.ext_vec(n - 3);
        let term = |n_low: usize, bits: usize, top: u64, scale: F192| {
            let mut point = low[..n_low].to_vec();
            point.extend((0..n - 1 - n_low).map(|i| F192::new((bits >> i & 1) as u64, 0, 0)));
            point.push(F192::new(top, 0, 0));
            DenseTerm {
                n_low,
                bits: Bits {
                    value: bits,
                    len: n - 1 - n_low,
                },
                top: vec![F192::new(top, 0, 0)],
                scale: Some(scale),
                value: mle_eval(&tables.0[DensePoly::Fixed as usize], &point),
            }
        };
        claims.push(DenseClaim {
            poly: DensePoly::Fixed,
            low: low.clone(),
            terms: vec![
                term(n - 3, 1, 0, rng.ext()),
                term(n - 4, 2, 1, rng.ext()),
                term(n - 3, 0, 1, F192::ZERO),
            ],
        });
        claims
    }

    #[test]
    fn the_dense_reduction_reduces_to_the_polynomials() {
        let mut rng = Rng::new(17);
        let vars = DenseVars([3, 6, 7, 5]);
        let tables = DenseTables(vars.0.map(|n| (0..1 << n).map(|_| F64(rng.next_u64())).collect()));
        let claims = dense_claims(&mut rng, &tables, &vars);
        let prove = |claims: &[DenseClaim<F192>], forge: bool| {
            let mut ps = ProverState::new(
                &SessionId::tagged(reduce::SESSION_TAG, &SessionId::new(b"tree-test").0),
                &0u64,
            );
            if forge {
                // A cheating prover: honest rounds, then values that meet the final identity of the claims as stated.
                let theta = ps.verifier_message();
                let mut p = DenseProver::new(&vars, &tables, claims, theta);
                let n_terms = claims.iter().map(|c| c.terms.len()).sum();
                let powers = Native.powers(theta, n_terms);
                let terms = claims.iter().flat_map(|c| &c.terms);
                let mut claim = (terms.zip(&powers)).fold(F192::ZERO, |acc, (t, &w)| {
                    acc + w * t.scale.unwrap_or(F192::ONE) * t.value
                });
                let point: Vec<F192> = (0..p.rounds())
                    .map(|i| {
                        let [c0, c2] = p.message();
                        ps.prover_messages(&[c0, c2]);
                        let r = ps.verifier_message();
                        claim = c0 + (claim + c2) * r + c2 * r * r;
                        p.bind(i, r);
                        r
                    })
                    .collect();
                let weights: Vec<F192> = vars
                    .final_weights(&mut Native, claims, &powers, &point)
                    .into_iter()
                    .flatten()
                    .collect();
                let mut values = p.finals();
                let rest = (values.iter().zip(&weights).skip(1)).fold(F192::ZERO, |acc, (&v, &w)| acc + v * w);
                values[0] = (claim + rest) * weights[0].inv();
                ps.prover_messages(&values);
            } else {
                DenseProver::prove(&mut ps, &vars, &tables, claims);
            }
            ps.into_proof()
        };
        let verify = |claims: &[DenseClaim<F192>], proof| {
            let mut vs = VerifierState::new(
                &SessionId::tagged(reduce::SESSION_TAG, &SessionId::new(b"tree-test").0),
                &0u64,
                proof,
            );
            DenseReduced::verify(&mut vs, &vars, claims)
        };

        let proof = prove(&claims, false);
        let reduced = verify(&claims, &proof).expect("an honest reduction");
        for poly in DensePoly::ALL {
            let point = &reduced.point[..vars.0[poly as usize]];
            assert_eq!(
                reduced.values[poly as usize],
                Some(mle_eval(&tables.0[poly as usize], point)),
                "{poly:?}"
            );
        }

        // A false claim: the honest prover's reduction is refused, and a cheating prover's reduces it to a false value.
        let mut false_claims = claims;
        let last = false_claims.len() - 1;
        false_claims[last].terms[1].value += F192::ONE;
        assert_eq!(verify(&false_claims, &proof).err(), Some(ReduceError::Dense));
        let forged = prove(&false_claims, true);
        let reduced = verify(&false_claims, &forged).expect("the forgery meets the final identity");
        let falsified = DensePoly::ALL.into_iter().filter(|&poly| {
            let point = &reduced.point[..vars.0[poly as usize]];
            reduced.values[poly as usize] != Some(mle_eval(&tables.0[poly as usize], point))
        });
        assert!(falsified.count() > 0, "a false claim reduced to true values");
    }

    // A claim on `poly` whose terms each weigh one block: `(n_low, bits)` names the `2^n_low` entries at `bits << n_low`.
    fn block_claim(
        rng: &mut Rng,
        tables: &DenseTables,
        vars: &DenseVars,
        poly: DensePoly,
        blocks: &[(usize, usize)],
    ) -> DenseClaim<F192> {
        let n = vars.0[poly as usize];
        let low = rng.ext_vec(n);
        let mut terms = Vec::new();
        for &(n_low, bits) in blocks {
            let mut point = low[..n_low].to_vec();
            point.extend((0..n - n_low).map(|i| F192::new((bits >> i & 1) as u64, 0, 0)));
            terms.push(DenseTerm {
                n_low,
                bits: Bits {
                    value: bits,
                    len: n - n_low,
                },
                top: Vec::new(),
                scale: Some(rng.ext()),
                value: mle_eval(&tables.0[poly as usize], &point),
            });
        }
        DenseClaim { poly, low, terms }
    }

    #[test]
    fn the_dense_reduction_reduces_claims_on_a_prefix() {
        // Weights zero past a prefix whose length is odd at several rounds, so the prover evaluates the table past it. The
        // blocks of the image and the fixed polynomial have one or two low points, so their weights stay factored for a few
        // rounds; the bytecode's has three, written out at once.
        let mut rng = Rng::new(23);
        let vars = DenseVars([3, 5, 14, 4]);
        let tables = DenseTables(vars.0.map(|n| (0..1 << n).map(|_| F64(rng.next_u64())).collect()));
        let mut claims: Vec<DenseClaim<F192>> = (0..3)
            .map(|_| {
                let point = rng.ext_vec(3);
                let value = mle_eval(&tables.0[DensePoly::Bytecode as usize], &point);
                DenseClaim::at(DensePoly::Bytecode, point, None, value)
            })
            .collect();
        claims.push(block_claim(&mut rng, &tables, &vars, DensePoly::Image, &[(1, 2)]));
        claims.push(block_claim(
            &mut rng,
            &tables,
            &vars,
            DensePoly::Fixed,
            &[(2, 0xAAA), (5, 7), (2, 0xAAA)],
        ));
        claims.push(block_claim(&mut rng, &tables, &vars, DensePoly::Fixed, &[(5, 7)]));
        claims.push(block_claim(&mut rng, &tables, &vars, DensePoly::Wide, &[(1, 3)]));
        let mut ps = ProverState::new(
            &SessionId::tagged(reduce::SESSION_TAG, &SessionId::new(b"tree-test").0),
            &0u64,
        );
        DenseProver::prove(&mut ps, &vars, &tables, &claims);
        let proof = ps.into_proof();
        let mut vs = VerifierState::new(
            &SessionId::tagged(reduce::SESSION_TAG, &SessionId::new(b"tree-test").0),
            &0u64,
            &proof,
        );
        let reduced = DenseReduced::verify(&mut vs, &vars, &claims).expect("an honest reduction");
        for poly in DensePoly::ALL {
            let point = &reduced.point[..vars.0[poly as usize]];
            assert_eq!(
                reduced.values[poly as usize],
                Some(mle_eval(&tables.0[poly as usize], point)),
                "{poly:?}"
            );
        }
    }
}
