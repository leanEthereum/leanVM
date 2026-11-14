//! Level 0's fold rounds, on the weight's terms and the lanes' projections onto them.
//!
//! The weight is never written out over the stack: it stays `b(l, x) = sum_t A(l, t) K_t(x)`, and a round's table
//! is the rows of `A` against the projections `P(l, t) = sum_x lane(l, x) K_t(x)` of the lanes it needs (see the
//! `basis` module of `stack_open`). Round 1 projects the stack and `X` times its even lanes. A later round projects
//! only `X F`: the projections of `F`, `G` and the folded lanes are linear in the ones before.
//!
//! A fold folds `A` and the projections only. Its lanes are written out by the next round's table, as that round's
//! pairs `(F, G)`, each `P = G + alpha F + beta X F` of the pairs before; round 1's pairs are the stack's lanes, read
//! in place. The last fold's one lane is written out at the end, and the weight is lifted for it.
//!
//! The stack's absent lanes are zero, so they take no projection, but `A` keeps a row for every lane: a claim's weight
//! may reach past the committed lanes. A lane without a partner folds against zero, its row of `A` against its
//! partner's.

use primitives::field::{F64, F64x8, F128, F128x8};
use primitives::multilinear::interp;

use crate::stack_open::{LOW_VARS, Terms};
use crate::whir::{FoldChallenges, FoldTable, InitialBasis};
use crate::xmul::x_at;

const BLOCK: usize = 1 << LOW_VARS;

/// `sum_t a[t] * p[t]`.
fn dot(a: &[F128], p: &[F128]) -> F128 {
    a.iter()
        .zip(p)
        .filter(|(a, _)| !a.is_zero())
        .map(|(&a, &p)| a * p)
        .sum()
}

/// A lane's coefficient `c`, zero past it.
fn coef<T: Copy + Default>(lane: &[T], c: usize) -> T {
    lane.get(c).copied().unwrap_or_default()
}

/// Eight coefficients of a lane from `c`, zero past it.
fn coefs<T: Copy + Default>(lane: &[T], c: usize) -> [T; 8] {
    core::array::from_fn(|j| coef(lane, c + j))
}

/// `n_lanes` lanes of `stride` coefficients end to end, `at8(lane, c)` giving the eight from `c`.
fn build_lanes(n_lanes: usize, stride: usize, at8: impl Fn(usize, usize) -> [F128; 8] + Sync) -> Vec<F128> {
    assert!(stride.is_multiple_of(8));
    parallel::map_collect(n_lanes * stride / 8, |k| at8(8 * k / stride, 8 * k % stride)).into_flattened()
}

/// A round's pairs `(F, G)`.
enum Pairs {
    /// Round 1's: the committed lanes two by two.
    Stack,
    /// A later round's, `len` coefficients each, `stride` apart with zeros between, a missing `G` zero.
    Stored {
        f: Vec<F128>,
        g: Vec<F128>,
        len: usize,
        stride: usize,
    },
}

/// A round's folded lanes `P = G + alpha F + beta X F`, one coefficient longer than its pairs.
struct Folded<'a> {
    pairs: &'a Pairs,
    stack: &'a [F64],
    lane_block: usize,
    n_stack: usize,
    ch: FoldChallenges,
}

impl Folded<'_> {
    fn count(&self) -> usize {
        match self.pairs {
            Pairs::Stack => self.n_stack.div_ceil(2),
            Pairs::Stored { f, stride, .. } => f.len() / stride,
        }
    }

    fn len(&self) -> usize {
        1 + match self.pairs {
            Pairs::Stack => self.lane_block,
            Pairs::Stored { len, .. } => *len,
        }
    }

    fn stack_lane(&self, l: usize) -> Option<&[F64]> {
        (l < self.n_stack).then(|| &self.stack[l * self.lane_block..(l + 1) * self.lane_block])
    }

    /// `P_i[c..c + 8]`, zero past the lanes.
    fn at8(&self, i: usize, c: usize) -> [F128; 8] {
        let FoldChallenges { alpha, beta } = self.ch;
        let (alpha, beta) = (F128x8::splat(alpha), F128x8::splat(beta));
        let p = match self.pairs {
            Pairs::Stack => {
                let Some(f) = self.stack_lane(2 * i) else {
                    return [F128::ZERO; 8];
                };
                let g = self.stack_lane(2 * i + 1).unwrap_or_default();
                let xf = F64x8::from_array(&core::array::from_fn(|j| x_at(f, c + j)));
                let g = F128x8::from_array(&coefs(g, c).map(F128::from));
                (alpha.mul_base_unreduced(F64x8::from_array(&coefs(f, c))) + beta.mul_base_unreduced(xf)).reduce() + g
            }
            Pairs::Stored { f, g, len, stride } => {
                let lane = i * stride..i * stride + len;
                let (Some(f), Some(g)) = (f.get(lane.clone()), g.get(lane)) else {
                    return [F128::ZERO; 8];
                };
                let xf = F128x8::from_array(&core::array::from_fn(|j| x_at(f, c + j)));
                let g = F128x8::from_array(&coefs(g, c));
                (alpha.mul_unreduced(F128x8::from_array(&coefs(f, c))) + beta.mul_unreduced(xf)).reduce() + g
            }
        };
        p.to_array()
    }
}

/// What a round's table leaves for its fold: the projections of `X F` per pair, and the pairs.
struct Pending {
    pxf: Vec<F128>,
    pairs: Pairs,
}

pub(crate) struct LaneRounds {
    /// The committed lanes, read until round 2's table (or `finish` after one round), then freed.
    stack: Vec<F64>,
    lane_block: usize,
    n_stack: usize,
    terms: Terms,
    n_terms: usize,
    /// The current lanes that carry data: their count and their projections; `A` has a row for every lane.
    n_lanes: usize,
    a: Vec<F128>,
    p: Vec<F128>,
    /// The pairs the last fold folded and its challenges; before round 1, the lanes are the stack's.
    folded: Option<(Pairs, FoldChallenges)>,
    pending: Option<Pending>,
}

impl LaneRounds {
    pub(crate) fn new(stack: Vec<F64>, basis: InitialBasis, lane_block: usize) -> Self {
        let InitialBasis { a, n_terms, terms } = basis;
        assert!(lane_block > 0 && stack.len().is_multiple_of(lane_block));
        assert_eq!(lane_block, 1 << terms.lane_vars());
        let n_lanes = stack.len() / lane_block;
        assert!(a.len().is_multiple_of(n_terms) && a.len() >= n_lanes * n_terms);
        Self {
            stack,
            lane_block,
            n_stack: n_lanes,
            terms,
            n_terms,
            n_lanes,
            a,
            p: Vec::new(),
            folded: None,
            pending: None,
        }
    }

    fn row<'a>(&self, t: &'a [F128], l: usize) -> Option<&'a [F128]> {
        t.get(l * self.n_terms..(l + 1) * self.n_terms)
    }

    fn view<'a>(&'a self, pairs: &'a Pairs, ch: FoldChallenges) -> Folded<'a> {
        Folded {
            pairs,
            stack: &self.stack,
            lane_block: self.lane_block,
            n_stack: self.n_stack,
            ch,
        }
    }

    /// Round 1's projections: every lane's into `p`, and `X F`'s per pair.
    fn project_stack(&mut self, live: &[bool]) -> Vec<F128> {
        let (nt, n, lb) = (self.n_terms, self.n_lanes, self.lane_block);
        let stack = &self.stack;
        let rows = tracing::info_span!("Project", lanes = n + n.div_ceil(2)).in_scope(|| {
            self.terms.project_rows(n, 2, live, |l, blocks, feed| {
                let lane = &stack[l * lb..(l + 1) * lb];
                for h in blocks {
                    feed(0, h, &lane[h * BLOCK..][..BLOCK]);
                    // Only an even lane, a pair's `F`, takes `X` times it.
                    if l % 2 == 0 {
                        let xf: [F64; BLOCK] = std::array::from_fn(|i| x_at(lane, h * BLOCK + i));
                        feed(1, h, &xf);
                    }
                }
            })
        });
        self.p = rows.chunks_exact(nt).step_by(2).flatten().copied().collect();
        // Lane `2m`'s second slot.
        rows.chunks_exact(nt).skip(1).step_by(4).flatten().copied().collect()
    }

    /// A later round's pairs, the last fold's lanes, written out, and `X F`'s projection per pair.
    fn write_pairs(&self, folded: &Folded, live: &[bool]) -> (Pairs, Vec<F128>) {
        let nt = self.n_terms;
        let (count, len) = (folded.count(), folded.len());
        let n_pairs = count.div_ceil(2);
        let stride = len.next_multiple_of(8);
        let f = build_lanes(n_pairs, stride, |m, c| folded.at8(2 * m, c));
        let g = build_lanes(n_pairs, stride, |m, c| folded.at8(2 * m + 1, c));
        // `X F` goes in as its two limbs, each a `K` lane.
        let rows = tracing::info_span!("Project", lanes = n_pairs).in_scope(|| {
            self.terms.project_rows(n_pairs, 2, live, |m, blocks, feed| {
                let lane = &f[m * stride..][..len];
                for h in blocks {
                    let xf: [[u64; 2]; BLOCK] = std::array::from_fn(|i| x_at(lane, h * BLOCK + i).to_limbs());
                    feed(0, h, &xf.map(|[lo, _]| F64(lo)));
                    feed(1, h, &xf.map(|[_, hi]| F64(hi)));
                }
            })
        });
        let pxf = (0..n_pairs * nt)
            .map(|i| {
                let (m, t) = (i / nt, i % nt);
                rows[2 * m * nt + t] + F128::Y * rows[(2 * m + 1) * nt + t]
            })
            .collect();
        (Pairs::Stored { f, g, len, stride }, pxf)
    }

    /// The round's table.
    pub(crate) fn table(&mut self) -> FoldTable {
        let (nt, n_pairs) = (self.n_terms, self.n_lanes.div_ceil(2));
        // The terms some row of `A` weighs: a lane's projection meets every other lane's row in the later rounds'
        // cross terms, `<W_0, G>` with `W_0` from the lanes before `G`'s.
        let live: Vec<bool> = (0..nt)
            .map(|t| self.a.iter().skip(t).step_by(nt).any(|a| !a.is_zero()))
            .collect();
        let (pairs, pxf) = match self.folded.take() {
            None => (Pairs::Stack, self.project_stack(&live)),
            Some((pairs, ch)) => {
                let written = self.write_pairs(&self.view(&pairs, ch), &live);
                // Round 2 read the stack's pairs last.
                if matches!(pairs, Pairs::Stack) {
                    self.stack = Vec::new();
                }
                written
            }
        };

        let zero = vec![F128::ZERO; nt];
        let mut table = [F128::ZERO; 4];
        for m in 0..n_pairs {
            let f = self.row(&self.p, 2 * m).expect("a pair's first lane is present");
            let g = self.row(&self.p, 2 * m + 1).unwrap_or(&zero);
            let a0 = self.row(&self.a, 2 * m).expect("a pair's first lane is present");
            let a1 = self.row(&self.a, 2 * m + 1).unwrap_or(&zero);
            let xf = &pxf[m * nt..][..nt];
            for (s, v) in table
                .iter_mut()
                .zip([dot(a0, g), dot(a0, f) + dot(a1, f), dot(a0, xf), dot(a1, xf)])
            {
                *s += v;
            }
        }
        self.pending = Some(Pending { pxf, pairs });
        table
    }

    /// The round's fold: `A`'s rows at `alpha`, and the projections of the lanes `P = G + alpha F + beta X F`, which
    /// the next table writes out.
    pub(crate) fn fold(&mut self, ch: &FoldChallenges) {
        let Pending { pxf, pairs } = self.pending.take().expect("a table before its fold");
        let (nt, n_pairs) = (self.n_terms, self.n_lanes.div_ceil(2));
        let FoldChallenges { alpha, beta } = *ch;
        self.a = (0..(self.a.len() / nt).div_ceil(2) * nt)
            .map(|i| {
                let (m, t) = (i / nt, i % nt);
                let a1 = self.a.get((2 * m + 1) * nt + t).copied().unwrap_or(F128::ZERO);
                interp(self.a[2 * m * nt + t], a1, alpha)
            })
            .collect();
        let zero = vec![F128::ZERO; nt];
        let mut p = Vec::with_capacity(n_pairs * nt);
        for (m, xf) in pxf.chunks_exact(nt).enumerate() {
            let f = self.row(&self.p, 2 * m).expect("a pair's first lane is present");
            let g = self.row(&self.p, 2 * m + 1).unwrap_or(&zero);
            p.extend(f.iter().zip(g).zip(xf).map(|((&f, &g), &xf)| g + alpha * f + beta * xf));
        }
        self.p = p;
        self.folded = Some((pairs, *ch));
        self.n_lanes = n_pairs;
    }

    /// The one lane left, low coefficients then high, and the weight lifted over its low coefficients.
    pub(crate) fn finish(self) -> (Vec<F128>, Vec<F128>) {
        assert_eq!(
            (self.n_lanes, self.a.len()),
            (1, self.n_terms),
            "every lane variable is folded"
        );
        let (pairs, ch) = self.folded.as_ref().expect("a fold before the end");
        let folded = self.view(pairs, *ch);
        let lane = tracing::info_span!("Lanes").in_scope(|| {
            let mut lane = build_lanes(1, folded.len().next_multiple_of(8), |_, c| folded.at8(0, c));
            lane.truncate(folded.len());
            lane
        });
        let w = tracing::info_span!("Lift").in_scope(|| self.terms.lift(&self.a));
        (lane, w)
    }
}
