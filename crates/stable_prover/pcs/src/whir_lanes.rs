//! Level 0's fold rounds, on the weight's terms ([`crate::stack_open::Terms`]) and the lanes' projections onto them.
//!
//! The weight stays `W(l, x) = sum_t A(l, t) K_t(x)`, so a round's inner products are rows of `A` against rows of
//! projections `P(lane)(t) = sum_x lane(x) K_t(x)`: over the pairs `(F, G)`, lanes `2m` and `2m + 1`,
//!
//! ```text
//!     v_G = sum_m <A(2m), P(G)>,   v_F = sum_m <A(2m) + A(2m+1), P(F)>,   t_i = sum_m <A(2m+i), P(X F)>.
//! ```
//!
//! Round 1 projects the stack's lanes. The folded lanes `G + alpha F + beta X F` have the projections
//! `P(G) + alpha P(F) + beta P(X F)`, so every round projects only `X F` beyond that. A fold writes the folded lanes
//! out, for the next round's `X F`, and takes `A`'s rows at `alpha`. After the last fold one lane is left, and the
//! weight is lifted over it.
//!
//! The stack's absent lanes are zero, so they take no projection, but `A` keeps a row for every lane: a claim's
//! weight may reach past the committed lanes. A lane without a partner folds against zero.

use primitives::field::{F64, F64x8, F128, F128x8, dot};
use primitives::multilinear::fold;

use crate::stack_open::{LOW_VARS, Terms};
use crate::whir::{FoldChallenges, FoldRounds, FoldTable};
use crate::xmul::x_at;

const BLOCK: usize = 1 << LOW_VARS;

/// Row `l` of a table of rows of `n` values, empty past the table: a lane without data.
#[inline(never)]
fn row<T>(v: &[T], n: usize, l: usize) -> &[T] {
    v.get(l * n..(l + 1) * n).unwrap_or_default()
}

/// Eight coefficients of a lane from `c`, zero past it.
fn coefs<T: Copy + Default>(lane: &[T], c: usize) -> [T; 8] {
    core::array::from_fn(|j| lane.get(c + j).copied().unwrap_or_default())
}

/// Lanes of `len` coefficients, `stride` apart, a multiple of eight, zeros between.
#[derive(Default)]
pub(crate) struct Folded {
    pub(crate) coefs: Vec<F128>,
    pub(crate) len: usize,
    pub(crate) stride: usize,
}

impl Folded {
    /// The `n_lanes` lanes of `v`, coefficient `c` of lane `l` at `c * n_lanes + l`.
    pub(crate) fn transpose(v: &[F128], n_lanes: usize) -> Self {
        let len = v.len() / n_lanes;
        let stride = len.next_multiple_of(8);
        let coefs = crate::collect_chunks(n_lanes * stride, |k| {
            let (l, c) = (8 * k / stride, 8 * k % stride);
            core::array::from_fn::<_, 8, _>(|j| {
                if c + j < len {
                    v[(c + j) * n_lanes + l]
                } else {
                    F128::ZERO
                }
            })
        });
        Self { coefs, len, stride }
    }

    #[inline(never)]
    pub(crate) fn count(&self) -> usize {
        self.coefs.len() / self.stride
    }

    /// Lane `l`.
    pub(crate) fn lane(&self, l: usize) -> &[F128] {
        row(&self.coefs, self.stride, l)
    }

    /// The one lane left.
    pub(crate) fn into_lane(mut self) -> Vec<F128> {
        assert_eq!(self.count(), 1, "every lane variable is folded");
        self.coefs.truncate(self.len);
        self.coefs
    }
}

/// The lanes that carry data.
pub(crate) enum Lanes {
    /// Round 1's: the committed stack, lanes of `len` words end to end.
    Stack { words: Vec<F64>, len: usize },
    /// A later round's.
    Folded(Folded),
}

impl Lanes {
    #[inline(never)]
    fn count(&self) -> usize {
        match self {
            Lanes::Stack { words, len } => words.len() / len,
            Lanes::Folded(lanes) => lanes.count(),
        }
    }

    fn len(&self) -> usize {
        match self {
            Lanes::Stack { len, .. } | Lanes::Folded(Folded { len, .. }) => *len,
        }
    }

    /// The lanes `G + alpha F + beta X F`, one coefficient longer, written by the pool eight coefficients at a time.
    pub(crate) fn fold(&self, ch: &FoldChallenges) -> Folded {
        let (alpha, beta) = (F128x8::splat(ch.alpha), F128x8::splat(ch.beta));
        let (n_pairs, len) = (self.count().div_ceil(2), 1 + self.len());
        let stride = len.next_multiple_of(8);
        let coefs = crate::collect_chunks(n_pairs * stride, |k| {
            let (m, c) = (8 * k / stride, 8 * k % stride);
            let p = match self {
                Lanes::Stack { words, len } => {
                    let (f, g) = (row(words, *len, 2 * m), row(words, *len, 2 * m + 1));
                    let xf = F64x8::from_array(&core::array::from_fn(|j| x_at(f, c + j)));
                    let f = F64x8::from_array(&coefs(f, c));
                    (alpha.mul_base_unreduced(f) + beta.mul_base_unreduced(xf)).reduce()
                        + F128x8::from_array(&coefs(g, c).map(F128::from))
                }
                Lanes::Folded(lanes) => {
                    let (f, g) = (lanes.lane(2 * m), lanes.lane(2 * m + 1));
                    let xf = F128x8::from_array(&core::array::from_fn(|j| x_at(f, c + j)));
                    let f = F128x8::from_array(&coefs(f, c));
                    (alpha.mul_unreduced(f) + beta.mul_unreduced(xf)).reduce() + F128x8::from_array(&coefs(g, c))
                }
            };
            p.to_array()
        });
        Folded { coefs, len, stride }
    }
}

/// The `K` sequences a round projects ([`Terms::project`]), two or one per pair `m` of lanes `F`, `G`: the stack's
/// `F` and `G`, the stack's `X F`, or a folded `X F` as its two limbs.
pub(crate) enum Sequences<'a> {
    Lanes(&'a [F64], usize),
    StackXf(&'a [F64], usize),
    FoldedXf(&'a Folded),
}

impl Sequences<'_> {
    /// Block `h` of pair `m`'s sequence `j`.
    pub(crate) fn block(&self, m: usize, j: usize, h: usize, out: &mut [F64; BLOCK]) {
        let at = h * BLOCK;
        match *self {
            Sequences::Lanes(words, len) => match row(words, len, 2 * m + j).get(at..at + BLOCK) {
                Some(lane) => out.copy_from_slice(lane),
                None => out.fill(F64::ZERO),
            },
            Sequences::StackXf(words, len) => {
                let f = row(words, len, 2 * m);
                for (i, o) in out.iter_mut().enumerate() {
                    *o = x_at(f, at + i);
                }
            }
            Sequences::FoldedXf(lanes) => {
                let f = lanes.lane(2 * m);
                for (i, o) in out.iter_mut().enumerate() {
                    o.0 = x_at(f, at + i).to_limbs()[j];
                }
            }
        }
    }
}

pub(crate) struct LaneRounds {
    terms: Terms,
    /// `A`: a row of `n_terms` for every lane of the round, absent ones included.
    a: Vec<F128>,
    lanes: Lanes,
    /// The projections of the lanes that carry data, a row per lane.
    p: Vec<F128>,
    /// The projections of `X F`, a row per pair, from a round's table to its fold.
    pxf: Vec<F128>,
}

impl LaneRounds {
    /// The rounds on `stack`, its lanes of `2^terms.lane_vars` words end to end, against the weight with terms
    /// `terms` and table `a`.
    pub(crate) fn new(stack: Vec<F64>, terms: Terms, a: Vec<F128>) -> Self {
        let len = 1 << terms.lane_vars;
        assert!(stack.len().is_multiple_of(len));
        assert!(a.len() >= stack.len() / len * terms.n_terms(), "a row of A per lane");
        Self {
            terms,
            a,
            lanes: Lanes::Stack { words: stack, len },
            p: Vec::new(),
            pxf: Vec::new(),
        }
    }

    /// The one lane left, low coefficients then high, and the weight lifted over its low coefficients.
    pub(crate) fn finish(self) -> (Vec<F128>, Vec<F128>) {
        assert_eq!(
            (self.lanes.count(), self.a.len()),
            (1, self.terms.n_terms()),
            "every lane variable is folded"
        );
        let Lanes::Folded(lanes) = self.lanes else {
            panic!("a fold before the end")
        };
        (lanes.into_lane(), self.terms.lift(&self.a))
    }
}

impl FoldRounds for LaneRounds {
    fn table(&mut self) -> FoldTable {
        let (nt, n_pairs) = (self.terms.n_terms(), self.lanes.count().div_ceil(2));
        match &self.lanes {
            Lanes::Stack { words, len } => {
                self.p = self.terms.project(n_pairs, 2, &Sequences::Lanes(words, *len));
                self.pxf = self.terms.project(n_pairs, 1, &Sequences::StackXf(words, *len));
            }
            Lanes::Folded(lanes) => {
                let rows = self.terms.project(n_pairs, 2, &Sequences::FoldedXf(lanes));
                self.pxf = (0..nt * n_pairs)
                    .map(|i| rows[i / nt * 2 * nt + i % nt] + F128::Y * rows[i / nt * 2 * nt + nt + i % nt])
                    .collect();
            }
        }

        let mut table = [F128::ZERO; 4];
        for m in 0..n_pairs {
            let (f, g, xf) = (
                row(&self.p, nt, 2 * m),
                row(&self.p, nt, 2 * m + 1),
                row(&self.pxf, nt, m),
            );
            let (a0, a1) = (row(&self.a, nt, 2 * m), row(&self.a, nt, 2 * m + 1));
            for (s, v) in table
                .iter_mut()
                .zip([dot(a0, g), dot(a0, f) + dot(a1, f), dot(a0, xf), dot(a1, xf)])
            {
                *s += v;
            }
        }
        table
    }

    fn fold(&mut self, ch: &FoldChallenges) {
        let (nt, n_pairs) = (self.terms.n_terms(), self.lanes.count().div_ceil(2));
        let FoldChallenges { alpha, beta } = *ch;
        let p = &self.p;
        self.a = fold(&self.a, nt, alpha);
        self.p = (0..n_pairs * nt)
            .map(|i| {
                let (m, t) = (i / nt, i % nt);
                let at = |l: usize| p.get(l * nt + t).copied().unwrap_or(F128::ZERO);
                at(2 * m + 1) + alpha * at(2 * m) + beta * self.pxf[i]
            })
            .collect();
        self.lanes = Lanes::Folded(self.lanes.fold(ch));
    }
}
