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
//! A round reads pair `m`'s projections only on the terms where `A(2m)` or `A(2m+1)` is nonzero, its `need`, and the
//! fold keeps the others zero in the folded row. So a pair projects `X F` on its need only, and a lane is known on its
//! last pair's need: it is projected afresh on the rest of its new pair's.
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
fn row<T>(v: &[T], n: usize, l: usize) -> &[T] {
    v.get(l * n..(l + 1) * n).unwrap_or_default()
}

/// Eight coefficients of a lane from `c`, zero past it.
fn coefs<T: Copy + Default>(lane: &[T], c: usize) -> [T; 8] {
    core::array::from_fn(|j| lane.get(c + j).copied().unwrap_or_default())
}

/// The lanes that carry data.
enum Lanes {
    /// Round 1's: the committed stack, lanes of `len` words end to end.
    Stack { words: Vec<F64>, len: usize },
    /// A later round's: lanes of `len` coefficients, `stride` apart, zeros between.
    Folded {
        coefs: Vec<F128>,
        len: usize,
        stride: usize,
    },
}

impl Lanes {
    fn count(&self) -> usize {
        match self {
            Lanes::Stack { words, len } => words.len() / len,
            Lanes::Folded { coefs, stride, .. } => coefs.len() / stride,
        }
    }

    fn len(&self) -> usize {
        match self {
            Lanes::Stack { len, .. } | Lanes::Folded { len, .. } => *len,
        }
    }

    /// The lanes `G + alpha F + beta X F`, one coefficient longer, written by the pool eight coefficients at a time.
    fn fold(&self, ch: &FoldChallenges) -> Lanes {
        let (alpha, beta) = (F128x8::splat(ch.alpha), F128x8::splat(ch.beta));
        let (n_pairs, len) = (self.count().div_ceil(2), 1 + self.len());
        let stride = len.next_multiple_of(8);
        let coefs = parallel::map_collect(n_pairs * stride / 8, |k| {
            let (m, c) = (8 * k / stride, 8 * k % stride);
            let p = match self {
                Lanes::Stack { words, len } => {
                    let (f, g) = (row(words, *len, 2 * m), row(words, *len, 2 * m + 1));
                    let xf = F64x8::from_array(&core::array::from_fn(|j| x_at(f, c + j)));
                    let f = F64x8::from_array(&coefs(f, c));
                    (alpha.mul_base_unreduced(f) + beta.mul_base_unreduced(xf)).reduce()
                        + F128x8::from_array(&coefs(g, c).map(F128::from))
                }
                Lanes::Folded { coefs: v, stride, .. } => {
                    let (f, g) = (row(v, *stride, 2 * m), row(v, *stride, 2 * m + 1));
                    let xf = F128x8::from_array(&core::array::from_fn(|j| x_at(f, c + j)));
                    let f = F128x8::from_array(&coefs(f, c));
                    (alpha.mul_unreduced(f) + beta.mul_unreduced(xf)).reduce() + F128x8::from_array(&coefs(g, c))
                }
            };
            p.to_array()
        })
        .into_flattened();
        Lanes::Folded { coefs, len, stride }
    }
}

pub(crate) struct LaneRounds {
    terms: Terms,
    /// `A`: a row of `n_terms` for every lane of the round, absent ones included.
    a: Vec<F128>,
    lanes: Lanes,
    /// The projections of the lanes that carry data, a row per lane, where `known` marks.
    p: Vec<F128>,
    known: Vec<bool>,
    /// From a round's table to its fold: each pair's need, and the projections of its `X F` on it.
    need: Vec<bool>,
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
            known: Vec::new(),
            need: Vec::new(),
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
        let Lanes::Folded { mut coefs, len, .. } = self.lanes else {
            panic!("a fold before the end")
        };
        coefs.truncate(len);
        let w = tracing::info_span!("Lift").in_scope(|| self.terms.lift(&self.a));
        (coefs, w)
    }
}

impl FoldRounds for LaneRounds {
    fn table(&mut self) -> FoldTable {
        let (nt, n_lanes) = (self.terms.n_terms(), self.lanes.count());
        let n_pairs = n_lanes.div_ceil(2);
        let nonzero = |l: usize, t: usize| row(&self.a, nt, l).get(t).is_some_and(|&v| v != F128::ZERO);
        self.need = (0..n_pairs * nt)
            .map(|i| {
                let (m, t) = (i / nt, i % nt);
                nonzero(2 * m, t) || nonzero(2 * m + 1, t)
            })
            .collect();
        // Per lane that carries data, the terms of its pair's need it is not known on.
        let fresh: Vec<bool> = (0..2 * n_pairs * nt)
            .map(|i| {
                let (l, t) = (i / nt, i % nt);
                l < n_lanes && self.need[l / 2 * nt + t] && !self.known.get(i).is_some_and(|&k| k)
            })
            .collect();
        // Per pair, `F`, `G` and `X F`, each its own `K` sequence or, in a folded round, two: its limbs.
        let limbs = match self.lanes {
            Lanes::Stack { .. } => 1,
            Lanes::Folded { .. } => 2,
        };
        let live: Vec<bool> = (0..n_pairs)
            .flat_map(|m| {
                let (f, g) = fresh[2 * m * nt..][..2 * nt].split_at(nt);
                [f, g, &self.need[m * nt..][..nt]]
                    .map(|mask| mask.repeat(limbs))
                    .concat()
            })
            .collect();
        let span = tracing::info_span!("Project", pairs = n_pairs).entered();
        let rows = match &self.lanes {
            Lanes::Stack { words, len } => self.terms.project(n_pairs, &live, |m, h, [f_out, g_out, xf_out]| {
                let (f, g) = (row(words, *len, 2 * m), row(words, *len, 2 * m + 1));
                f_out.copy_from_slice(&f[h * BLOCK..][..BLOCK]);
                match g.get(h * BLOCK..(h + 1) * BLOCK) {
                    Some(g) => g_out.copy_from_slice(g),
                    None => g_out.fill(F64::ZERO),
                }
                for (i, o) in xf_out.iter_mut().enumerate() {
                    *o = x_at(f, h * BLOCK + i);
                }
            }),
            Lanes::Folded { coefs, stride, .. } => {
                let rows = self.terms.project(n_pairs, &live, |m, h, out: &mut [[F64; BLOCK]; 6]| {
                    let (f, g) = (row(coefs, *stride, 2 * m), row(coefs, *stride, 2 * m + 1));
                    let [f_lo, f_hi, g_lo, g_hi, xf_lo, xf_hi] = out;
                    for i in 0..BLOCK {
                        let c = h * BLOCK + i;
                        [f_lo[i].0, f_hi[i].0] = f.get(c).copied().unwrap_or_default().to_limbs();
                        [g_lo[i].0, g_hi[i].0] = g.get(c).copied().unwrap_or_default().to_limbs();
                        [xf_lo[i].0, xf_hi[i].0] = x_at(f, c).to_limbs();
                    }
                });
                // Each sequence from its limbs.
                rows.chunks_exact(2 * nt)
                    .flat_map(|r| {
                        let (lo, hi) = r.split_at(nt);
                        lo.iter().zip(hi).map(|(&lo, &hi)| lo + F128::Y * hi)
                    })
                    .collect()
            }
        };
        drop(span);
        // Pair `m`'s row of projections holds `F`, `G`, then `X F`.
        self.p.resize(n_lanes * nt, F128::ZERO);
        for i in (0..fresh.len()).filter(|&i| fresh[i]) {
            self.p[i] = rows[i / (2 * nt) * 3 * nt + i % (2 * nt)];
        }
        self.pxf = rows.chunks_exact(3 * nt).flat_map(|r| &r[2 * nt..]).copied().collect();

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
        self.known = std::mem::take(&mut self.need);
        self.lanes = tracing::info_span!("Lanes").in_scope(|| self.lanes.fold(ch));
    }
}
