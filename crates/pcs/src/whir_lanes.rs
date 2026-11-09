//! Level 0's fold rounds, on the weight's terms and the lanes' projections onto them.
//!
//! The weight is never written out over the stack: it stays `b(l, x) = sum_t A(l, t) K_t(x)`, and a round's table
//! is the rows of `A` against the projections `P(l, t) = sum_x lane(l, x) K_t(x)` of the lanes it needs (see the
//! `basis` module of `stack_open`). Round 1 projects the stack and `X` times it, and its fold writes the folded
//! lanes out. A later round projects only `X H`: the projections of `G`, `H` and the folded lanes are linear in
//! the ones before. The last round leaves one lane in the clear, and the weight is lifted for it.
//!
//! The stack's absent lanes are zero, and so are their rows of `A`: a lane without a partner folds against zero.

use primitives::field::{F64, F128};

use crate::stack_open::Terms;
use crate::whir::{FoldChallenges, FoldTable, InitialBasis};
use crate::xmul::mul_x_lane;

/// Columns per task where lanes are written out.
const COLS: usize = 1 << 13;

/// `n` lanes of `len` values, back to back, a range of columns per task: `fill(lane, first, out)`.
fn fill_lanes(n: usize, len: usize, fill: impl Fn(usize, usize, &mut [F128]) + Sync) -> Vec<F128> {
    let per = len.div_ceil(COLS);
    let fill_all = |out: &mut [F128]| {
        let ptr = parallel::SendPtr(out.as_mut_ptr());
        parallel::for_each(n * per, |t| {
            let (m, first) = (t / per, t % per * COLS);
            // SAFETY: each task owns its range of columns of its lane.
            fill(m, first, unsafe { ptr.slice(m * len + first, COLS.min(len - first)) });
        });
    };
    // SAFETY: `fill_all` writes every element, and reads none.
    unsafe { primitives::filled_vec(n * len, fill_all) }
}

/// `sum_t a[t] * p[t]`.
fn dot(a: &[F128], p: &[F128]) -> F128 {
    a.iter()
        .zip(p)
        .filter(|(a, _)| !a.is_zero())
        .map(|(&a, &p)| a * p)
        .sum()
}

/// What a round's table leaves for its fold, per pair of lanes: the projections of `G`, `H` and `X H`, and the
/// lanes `H` after round 1.
struct Pending {
    theta: F128,
    pg: Vec<F128>,
    ph: Vec<F128>,
    pxh: Vec<F128>,
    h: Vec<F128>,
}

pub(crate) struct LaneRounds {
    /// The committed lanes, read by round 1.
    stack: Vec<F64>,
    lane_block: usize,
    terms: Terms,
    n_terms: usize,
    /// The current lanes: their count, one row of `A` each and their projections, and after round 1 the lanes
    /// themselves, `len` coefficients each.
    n_lanes: usize,
    a: Vec<F128>,
    p: Vec<F128>,
    lanes: Vec<F128>,
    len: usize,
    pending: Option<Pending>,
}

impl LaneRounds {
    pub(crate) fn new(stack: Vec<F64>, basis: InitialBasis, lane_block: usize) -> Self {
        let InitialBasis { a, n_terms, terms } = basis;
        assert!(lane_block > 0 && stack.len().is_multiple_of(lane_block));
        assert_eq!(lane_block, 1 << terms.lane_vars());
        let n_lanes = stack.len() / lane_block;
        assert_eq!(a.len(), n_lanes * n_terms);
        Self {
            stack,
            lane_block,
            terms,
            n_terms,
            n_lanes,
            a,
            p: Vec::new(),
            lanes: Vec::new(),
            len: lane_block,
            pending: None,
        }
    }

    fn row<'a>(&self, t: &'a [F128], l: usize) -> Option<&'a [F128]> {
        t.get(l * self.n_terms..(l + 1) * self.n_terms)
    }

    /// The round's table after `theta`.
    pub(crate) fn table(&mut self, theta: F128) -> FoldTable {
        let (nt, n_pairs, lb) = (self.n_terms, self.n_lanes.div_ceil(2), self.lane_block);
        // The terms some row of `A` weighs: a lane's projection meets every other lane's row in the later rounds'
        // cross terms, `<W_0, G>` with `W_0` from the lanes before `G`'s.
        let live: Vec<bool> = (0..nt)
            .map(|t| self.a.iter().skip(t).step_by(nt).any(|a| !a.is_zero()))
            .collect();
        let terms = &self.terms;
        let low = terms.low_vars();
        let (pxh, h) = if self.lanes.is_empty() {
            // Each lane and `X` times it, from one read of the lane.
            let (stack, n) = (&self.stack, self.n_lanes);
            let rows = tracing::info_span!("Project", lanes = 2 * n).in_scope(|| {
                terms.project_rows(n, 2, &live, |l, blocks, emit| {
                    let words = blocks.start << low..blocks.end << low;
                    let lane = &stack[l * lb..(l + 1) * lb];
                    emit(0, &lane[words.clone()], terms.lane_repeats(l, blocks), F128::ONE);
                    let mut x = vec![F64::ZERO; words.len()];
                    mul_x_lane(lane, words.start, &mut x);
                    emit(1, &x, &[], F128::ONE);
                })
            });
            let row = |l: usize, slot: usize| rows.get((2 * l + slot) * nt..(2 * l + slot + 1) * nt);
            self.p = (0..n)
                .flat_map(|l| row(l, 0).expect("a present lane"))
                .copied()
                .collect();
            let pxh = (0..n_pairs * nt)
                .map(|i| {
                    let (m, t) = (i / nt, i % nt);
                    let g = row(2 * m + 1, 1).map_or(F128::ZERO, |g| theta * g[t]);
                    row(2 * m, 1).expect("a present lane")[t] + g
                })
                .collect();
            (pxh, Vec::new())
        } else {
            let (lanes, len, n) = (&self.lanes, self.len, self.n_lanes);
            let h = fill_lanes(n_pairs, len, |m, first, out| {
                let f = &lanes[2 * m * len + first..][..out.len()];
                match lanes.get((2 * m + 1) * len + first..(2 * m + 1) * len + first + out.len()) {
                    Some(g) if 2 * m + 1 < n => {
                        for ((o, &f), &g) in out.iter_mut().zip(f).zip(g) {
                            *o = f + theta * g;
                        }
                    }
                    _ => out.copy_from_slice(f),
                }
            });
            let pxh = tracing::info_span!("Project", lanes = n_pairs).in_scope(|| {
                terms.project_rows(n_pairs, 1, &live, |m, blocks, emit| {
                    let words = blocks.start << low..blocks.end << low;
                    let mut xh = vec![F128::ZERO; words.len()];
                    mul_x_lane(&h[m * len..(m + 1) * len], words.start, &mut xh);
                    let [lo, hi]: [Vec<F64>; 2] = [0, 1].map(|k| xh.iter().map(|v| F64(v.to_limbs()[k])).collect());
                    emit(0, &lo, &[], F128::ONE);
                    emit(0, &hi, &[], F128::Y);
                })
            });
            (pxh, h)
        };

        let zero = vec![F128::ZERO; nt];
        let (mut pg, mut ph) = (Vec::with_capacity(n_pairs * nt), Vec::with_capacity(n_pairs * nt));
        let mut table = [F128::ZERO; 5];
        for m in 0..n_pairs {
            let pf = self.row(&self.p, 2 * m).expect("a pair's first lane is present");
            let g = self.row(&self.p, 2 * m + 1).unwrap_or(&zero);
            let a0 = self.row(&self.a, 2 * m).expect("a pair's first lane is present");
            let a1 = self.row(&self.a, 2 * m + 1).unwrap_or(&zero);
            let start = ph.len();
            ph.extend(pf.iter().zip(g).map(|(&f, &g)| f + theta * g));
            pg.extend_from_slice(g);
            let (h, xh) = (&ph[start..], &pxh[m * nt..][..nt]);
            for (s, v) in table
                .iter_mut()
                .zip([dot(a0, g), dot(a0, h), dot(a0, xh), dot(a1, h), dot(a1, xh)])
            {
                *s += v;
            }
        }
        self.pending = Some(Pending { theta, pg, ph, pxh, h });
        table
    }

    /// The round's fold: lanes `P = G + alpha H + beta X H`, one coefficient longer, and `A`'s rows by `gamma`.
    pub(crate) fn fold(&mut self, ch: &FoldChallenges) {
        let Pending { theta, pg, ph, pxh, h } = self.pending.take().expect("a table before its fold");
        assert_eq!(theta, ch.theta);
        let (nt, n, n_pairs) = (self.n_terms, self.n_lanes, self.n_lanes.div_ceil(2));
        let FoldChallenges { gamma, alpha, beta, .. } = *ch;
        self.a = (0..n_pairs * nt)
            .map(|i| {
                let (m, t) = (i / nt, i % nt);
                let a0 = self.a[2 * m * nt + t];
                let a1 = self.a.get((2 * m + 1) * nt + t).copied().unwrap_or(F128::ZERO);
                a0 + gamma * (a0 + a1)
            })
            .collect();
        self.p = (0..n_pairs * nt)
            .map(|i| pg[i] + alpha * ph[i] + beta * pxh[i])
            .collect();
        let len = self.len + 1;
        self.lanes = tracing::info_span!("Lanes", lanes = n_pairs, len).in_scope(|| {
            if self.lanes.is_empty() {
                // `P = alpha F + (1 + alpha theta) G + beta X F + beta theta X G`, from K lanes.
                let (stack, lb) = (&self.stack, self.lane_block);
                let (cg, cxg) = (F128::ONE + alpha * theta, beta * theta);
                fill_lanes(n_pairs, len, |m, first, out| {
                    let f = &stack[2 * m * lb..(2 * m + 1) * lb];
                    let g = (2 * m + 1 < n).then(|| &stack[(2 * m + 1) * lb..(2 * m + 2) * lb]);
                    let mut x = vec![F64::ZERO; out.len()];
                    mul_x_lane(f, first, &mut x);
                    for (i, (o, &xf)) in out.iter_mut().zip(&x).enumerate() {
                        let f = f.get(first + i).copied().unwrap_or(F64::ZERO);
                        *o = alpha.mul_base(f) + beta.mul_base(xf);
                    }
                    if let Some(g) = g {
                        mul_x_lane(g, first, &mut x);
                        for (i, (o, &xg)) in out.iter_mut().zip(&x).enumerate() {
                            let g = g.get(first + i).copied().unwrap_or(F64::ZERO);
                            *o += cg.mul_base(g) + cxg.mul_base(xg);
                        }
                    }
                })
            } else {
                let (lanes, prev) = (&self.lanes, self.len);
                fill_lanes(n_pairs, len, |m, first, out| {
                    let h = &h[m * prev..(m + 1) * prev];
                    mul_x_lane(h, first, out);
                    let g = (2 * m + 1 < n).then(|| &lanes[(2 * m + 1) * prev..(2 * m + 2) * prev]);
                    for (i, o) in out.iter_mut().enumerate() {
                        let c = first + i;
                        let (h, g) = (
                            h.get(c).copied().unwrap_or(F128::ZERO),
                            g.and_then(|g| g.get(c)).copied().unwrap_or(F128::ZERO),
                        );
                        *o = g + alpha * h + beta * *o;
                    }
                })
            }
        });
        self.len = len;
        self.n_lanes = n_pairs;
    }

    /// The committed lanes if `keep`, once round 1 has read them. Otherwise they go now.
    pub(crate) fn take_stack(&mut self, keep: bool) -> Vec<F64> {
        assert!(!self.lanes.is_empty(), "round 1 is over");
        let stack = std::mem::take(&mut self.stack);
        if keep { stack } else { Vec::new() }
    }

    /// The one lane left, low coefficients then high, and the weight lifted over its low coefficients.
    pub(crate) fn finish(self) -> (Vec<F128>, Vec<F128>) {
        assert_eq!(self.n_lanes, 1, "every lane variable is folded");
        let w = tracing::info_span!("Lift").in_scope(|| self.terms.lift(&self.a));
        (self.lanes, w)
    }
}
