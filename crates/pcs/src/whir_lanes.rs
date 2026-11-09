//! Level 0's fold rounds, on the weight's terms and the lanes' projections onto them.
//!
//! The weight is never written out over the stack: it stays `b(l, x) = sum_t A(l, t) K_t(x)`, and a round's table
//! is the rows of `A` against the projections `P(l, t) = sum_x lane(l, x) K_t(x)` of the lanes it needs (see the
//! `basis` module of `stack_open`). Round 1 projects the stack and `X` times it. A later round projects only `X H`:
//! the projections of `G`, `H` and the folded lanes are linear in the ones before.
//!
//! A fold folds `A` and the projections only. Its lanes are written by the next round's table, which knows that
//! round's `theta`: one pass folds the round's pairs `(H, G)` into `P = G + alpha H + beta X H` and writes the next
//! round's pairs `(P_0 + theta P_1, P_1)`, projecting `X` times the first as it goes. Round 1's pairs are the stack's
//! lanes, read in place. The last fold's one lane is written out at the end, and the weight is lifted for it.
//!
//! The stack's absent lanes are zero, and so are their rows of `A`: a lane without a partner folds against zero.
//!
//! Where the stack's blocks under a lane `X H` repeat, its blocks repeat past their first few words (one more per
//! round, from multiplying by `X`), so a block of `X H` is a repeat when those words are too.

use primitives::field::{F64, F64x8, F128, F128x8, mul_base_splat8};
use primitives::stream::Stream;

use crate::stack_open::{SWEEP, Terms};
use crate::whir::{FoldChallenges, FoldTable, InitialBasis};
use crate::xmul::{exponents8, mul_x_block, multiples, sums8, x_at};

/// The words of a block of a round-`r` lane `X H` that can differ from the block before when the stack's blocks under
/// it repeat: its first `r`. Later rounds skip no blocks.
const HEAD: usize = 8;

/// Coefficients per task where the last lane is written out.
const COLS: usize = 1 << 13;

/// `sum_t a[t] * p[t]`.
fn dot(a: &[F128], p: &[F128]) -> F128 {
    a.iter()
        .zip(p)
        .filter(|(a, _)| !a.is_zero())
        .map(|(&a, &p)| a * p)
        .sum()
}

/// A lane's coefficient `c`, zero past it.
fn outside<T: Copy + Default>(lane: &[T]) -> impl Fn(usize) -> T + '_ {
    |c| lane.get(c).copied().unwrap_or_default()
}

/// A round's pairs: `H = F + theta G` and `G` of each.
enum Pairs {
    /// Round 1's: the committed lanes two by two, `H` implicit.
    Stack,
    /// A later round's, `len` coefficients each, a missing `G` zero.
    Stored { h: Vec<F128>, g: Vec<F128>, len: usize },
}

/// A round's folded lanes `P = G + alpha H + beta X H`, one coefficient longer than its pairs, read anywhere.
struct Folded<'a> {
    pairs: &'a Pairs,
    stack: &'a [F64],
    lane_block: usize,
    n_stack: usize,
    ch: FoldChallenges,
    /// `beta A_t` and `beta theta A_t` for every `t`: the challenges of `X F` and `X G`, or of `X H`.
    cx: [[F128; 64]; 2],
}

impl Folded<'_> {
    fn count(&self) -> usize {
        match self.pairs {
            Pairs::Stack => self.n_stack.div_ceil(2),
            Pairs::Stored { h, len, .. } => h.len() / len,
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

    /// `P_i[c]`, zero past the lanes.
    fn at(&self, i: usize, c: usize) -> F128 {
        let FoldChallenges { theta, alpha, beta, .. } = self.ch;
        match self.pairs {
            Pairs::Stack => {
                // `alpha F + (1 + alpha theta) G + beta X F + beta theta X G`.
                let term = |l: usize, a: F128, b: F128| {
                    self.stack_lane(l).map_or(F128::ZERO, |lane| {
                        a.mul_base(outside(lane)(c)) + b.mul_base(x_at(lane, c))
                    })
                };
                term(2 * i, alpha, beta) + term(2 * i + 1, F128::ONE + alpha * theta, beta * theta)
            }
            Pairs::Stored { h, g, len } => match (h.get(i * len..(i + 1) * len), g.get(i * len..(i + 1) * len)) {
                (Some(h), Some(g)) => outside(g)(c) + alpha * outside(h)(c) + beta * x_at(h, c),
                _ => F128::ZERO,
            },
        }
    }

    /// `P_i` over the `out.len()` coefficients from `first`, a power of two that divides `first`, inside the low part.
    ///
    /// `X` multiplies column `c` by `A_t` after summing two coefficients, so a multiple of `X` enters as the sums, the
    /// `A_t` folded into its challenge.
    fn block(&self, i: usize, first: usize, out: &mut [F128]) {
        let n = out.len();
        let FoldChallenges { theta, alpha, .. } = self.ch;
        let out = out.as_chunks_mut::<8>().0;
        let lanes = |t: [usize; 8], c: &[F128; 64]| F128x8::from_array(&t.map(|t| c[t]));
        match self.pairs {
            Pairs::Stack => {
                let f = self.stack_lane(2 * i).expect("a folded lane has its first");
                let g = self.stack_lane(2 * i + 1);
                let (cg, [cxf, cxg]) = (F128::ONE + alpha * theta, &self.cx);
                let (fb, f8) = (&f[first..first + n], f[first..first + n].as_chunks::<8>().0);
                for (q, o) in out.iter_mut().enumerate() {
                    let (sf, t0) = sums8(fb, q, first, outside(f));
                    let t = exponents8(t0);
                    let mut sum =
                        mul_base_splat8(alpha, &f8[q]) ^ lanes(t, cxf).mul_base_unreduced(F64x8::from_array(&sf));
                    if let Some(g) = g {
                        let gb = &g[first..first + n];
                        let (sg, _) = sums8(gb, q, first, outside(g));
                        sum ^= mul_base_splat8(cg, &gb.as_chunks::<8>().0[q])
                            ^ lanes(t, cxg).mul_base_unreduced(F64x8::from_array(&sg));
                    }
                    *o = sum.reduce_lanes().to_array();
                }
            }
            Pairs::Stored { h, g, len } => {
                let (h, g) = (&h[i * len..(i + 1) * len], &g[i * len..(i + 1) * len]);
                let (hb, cxh, alpha) = (&h[first..first + n], &self.cx[0], F128x8::splat(alpha));
                let (h8, g8) = (hb.as_chunks::<8>().0, g[first..first + n].as_chunks::<8>().0);
                for (q, o) in out.iter_mut().enumerate() {
                    let (sh, t0) = sums8(hb, q, first, outside(h));
                    let sum = alpha.mul_unreduced(F128x8::from_array(&h8[q]))
                        ^ lanes(exponents8(t0), cxh).mul_unreduced(F128x8::from_array(&sh));
                    *o = (F128x8::from_array(&g8[q]) + sum.reduce_lanes()).to_array();
                }
            }
        }
    }
}

/// What a round's table leaves for its fold: the projections of `G`, `H` and `X H` per pair, and the pairs.
struct Pending {
    theta: F128,
    pg: Vec<F128>,
    ph: Vec<F128>,
    pxh: Vec<F128>,
    pairs: Pairs,
}

pub(crate) struct LaneRounds {
    /// The committed lanes, read until round 2's table.
    stack: Vec<F64>,
    lane_block: usize,
    n_stack: usize,
    terms: Terms,
    n_terms: usize,
    /// The current lanes: their count, one row of `A` each and their projections.
    n_lanes: usize,
    a: Vec<F128>,
    p: Vec<F128>,
    /// The pairs the last fold folded and its challenges; before round 1, the lanes are the stack's.
    folded: Option<(Pairs, FoldChallenges)>,
    pending: Option<Pending>,
    /// Rounds whose tables are taken.
    round: usize,
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
            n_stack: n_lanes,
            terms,
            n_terms,
            n_lanes,
            a,
            p: Vec::new(),
            folded: None,
            pending: None,
            round: 0,
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
            cx: [multiples(ch.beta), multiples(ch.beta * ch.theta)],
        }
    }

    /// Round 1's projections: every lane's into `p`, and `X H`'s per pair, `X F + theta X G`.
    fn project_stack(&mut self, theta: F128, live: &[bool]) -> Vec<F128> {
        let (nt, n, lb) = (self.n_terms, self.n_lanes, self.lane_block);
        let (stack, terms) = (&self.stack, &self.terms);
        let low = terms.low_vars();
        let rows = tracing::info_span!("Project", lanes = 2 * n).in_scope(|| {
            terms.project_rows(n, 2, live, |l, blocks, feed| {
                let lane = &stack[l * lb..(l + 1) * lb];
                let tags = terms.lane_repeats(l, blocks.clone());
                let (mut x, mut x_tags) = (vec![F64::ZERO; SWEEP << low], [false; SWEEP]);
                // The block before's first word of `X F`.
                let mut last = None;
                for start in blocks.clone().step_by(SWEEP) {
                    let sweep = start..(start + SWEEP).min(blocks.end);
                    let words = sweep.start << low..sweep.end << low;
                    feed(0, start, &lane[words.clone()], terms.lane_repeats(l, sweep.clone()));
                    for (k, b) in sweep.clone().enumerate() {
                        let (first, out) = (b << low, &mut x[k << low..(k + 1) << low]);
                        mul_x_block(&lane[first..first + out.len()], first, outside(lane), out);
                        x_tags[k] = last == Some(out[0]) && tags.get(b - blocks.start) == Some(&true);
                        last = Some(out[0]);
                    }
                    feed(1, start, &x[..words.len()], &x_tags[..sweep.len()]);
                }
            })
        });
        let row = |l: usize, slot: usize| rows.get((2 * l + slot) * nt..(2 * l + slot + 1) * nt);
        self.p = rows.chunks_exact(nt).step_by(2).flatten().copied().collect();
        (0..n.div_ceil(2) * nt)
            .map(|i| {
                let (m, t) = (i / nt, i % nt);
                let g = row(2 * m + 1, 1).map_or(F128::ZERO, |g| theta * g[t]);
                row(2 * m, 1).expect("a present lane")[t] + g
            })
            .collect()
    }

    /// A later round's pairs `(P_0 + theta P_1, P_1)` of the last fold's lanes, written out, and `X H`'s projection
    /// per pair.
    fn write_pairs(&self, folded: &Folded, theta: F128, live: &[bool]) -> (Pairs, Vec<F128>) {
        let (nt, lb, terms) = (self.n_terms, self.lane_block, &self.terms);
        let (count, len) = (folded.count(), folded.len());
        let n_pairs = count.div_ceil(2);
        let (low, block) = (terms.low_vars(), 1usize << terms.low_vars());
        // The stack lanes under a pair, and the words of `X H` a repeat of theirs leaves free.
        let (group, head) = (1usize << self.round, self.round);
        let next = |m: usize, c: usize| folded.at(2 * m, c) + theta * folded.at(2 * m + 1, c);
        // SAFETY: the pass writes every low coefficient and the loop after it every high one, before any is read.
        let (mut h, mut g) = unsafe {
            (
                primitives::uninit_vec(n_pairs * len),
                primitives::uninit_vec(n_pairs * len),
            )
        };
        let (hp, gp) = (parallel::SendPtr(h.as_mut_ptr()), parallel::SendPtr(g.as_mut_ptr()));
        let rows = tracing::info_span!("Project", lanes = n_pairs).in_scope(|| {
            terms.project_rows(n_pairs, 2, live, |m, blocks, feed| {
                let stream = Stream::new();
                let [mut pa, mut pb, mut hn, mut xh] = [0; 4].map(|_| vec![F128::ZERO; block]);
                let mut limbs = [vec![F64::ZERO; SWEEP << low], vec![F64::ZERO; SWEEP << low]];
                let mut tags = [false; SWEEP];
                let stacked = m * group..((m + 1) * group).min(self.n_stack);
                let repeats = |b: usize| {
                    head <= HEAD
                        && stacked
                            .clone()
                            .all(|l| terms.lane_repeats(l, b..b + 1).first() == Some(&true))
                };
                let theta8 = F128x8::splat(theta);
                // The block before's last `H` coefficient and first words of `X H`.
                let mut last: Option<(F128, [F128; HEAD])> = None;
                for start in blocks.clone().step_by(SWEEP) {
                    let sweep = start..(start + SWEEP).min(blocks.end);
                    for (k, b) in sweep.clone().enumerate() {
                        let first = b << low;
                        folded.block(2 * m, first, &mut pa);
                        if 2 * m + 1 < count {
                            folded.block(2 * m + 1, first, &mut pb);
                        } else {
                            pb.fill(F128::ZERO);
                        }
                        let (a8, b8) = (pa.as_chunks::<8>().0, pb.as_chunks::<8>().0);
                        for ((o, a), b) in hn.as_chunks_mut::<8>().0.iter_mut().zip(a8).zip(b8) {
                            *o = (F128x8::from_array(a) + theta8 * F128x8::from_array(b)).to_array();
                        }
                        // SAFETY: each task owns its blocks of its pair.
                        unsafe {
                            stream.copy(hp.slice(m * len + first, block), &hn);
                            stream.copy(gp.slice(m * len + first, block), &pb);
                        }
                        let outside = |c: usize| match last {
                            Some((before, _)) if c + 1 == first => before,
                            _ => next(m, c),
                        };
                        mul_x_block(&hn, first, outside, &mut xh);
                        let words: [F128; HEAD] = xh[..HEAD].try_into().expect("a block holds its head");
                        tags[k] = last.is_some_and(|(_, w)| w == words) && repeats(b);
                        last = Some((hn[block - 1], words));
                        let [lo, hi] = &mut limbs;
                        for ((lo, hi), v) in lo[k << low..].iter_mut().zip(&mut hi[k << low..]).zip(&xh) {
                            let [l, h] = v.to_limbs();
                            (*lo, *hi) = (F64(l), F64(h));
                        }
                    }
                    let words = sweep.len() << low;
                    feed(0, start, &limbs[0][..words], &tags[..sweep.len()]);
                    feed(1, start, &limbs[1][..words], &tags[..sweep.len()]);
                }
            })
        });
        for m in 0..n_pairs {
            for c in lb..len {
                h[m * len + c] = next(m, c);
                g[m * len + c] = folded.at(2 * m + 1, c);
            }
        }
        let pxh = (0..n_pairs * nt)
            .map(|i| {
                let (m, t) = (i / nt, i % nt);
                rows[2 * m * nt + t] + F128::Y * rows[(2 * m + 1) * nt + t]
            })
            .collect();
        (Pairs::Stored { h, g, len }, pxh)
    }

    /// The round's table after `theta`.
    pub(crate) fn table(&mut self, theta: F128) -> FoldTable {
        let (nt, n_pairs) = (self.n_terms, self.n_lanes.div_ceil(2));
        self.round += 1;
        // The terms some row of `A` weighs: a lane's projection meets every other lane's row in the later rounds'
        // cross terms, `<W_0, G>` with `W_0` from the lanes before `G`'s.
        let live: Vec<bool> = (0..nt)
            .map(|t| self.a.iter().skip(t).step_by(nt).any(|a| !a.is_zero()))
            .collect();
        let (pairs, pxh) = match self.folded.take() {
            None => (Pairs::Stack, self.project_stack(theta, &live)),
            Some((pairs, ch)) => self.write_pairs(&self.view(&pairs, ch), theta, &live),
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
        self.pending = Some(Pending {
            theta,
            pg,
            ph,
            pxh,
            pairs,
        });
        table
    }

    /// The round's fold: `A`'s rows by `gamma`, and the projections of the lanes `P = G + alpha H + beta X H`, which
    /// the next table writes out.
    pub(crate) fn fold(&mut self, ch: &FoldChallenges) {
        let Pending {
            theta,
            pg,
            ph,
            pxh,
            pairs,
        } = self.pending.take().expect("a table before its fold");
        assert_eq!(theta, ch.theta);
        let (nt, n_pairs) = (self.n_terms, self.n_lanes.div_ceil(2));
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
        self.folded = Some((pairs, *ch));
        self.n_lanes = n_pairs;
    }

    /// The one lane left, low coefficients then high, the weight lifted over its low coefficients, and the committed
    /// lanes if `keep_stack`.
    pub(crate) fn finish(self, keep_stack: bool) -> (Vec<F128>, Vec<F128>, Vec<F64>) {
        assert_eq!(self.n_lanes, 1, "every lane variable is folded");
        let (pairs, ch) = self.folded.as_ref().expect("a fold before the end");
        let folded = self.view(pairs, *ch);
        let (len, lb) = (folded.len(), self.lane_block);
        let lane = tracing::info_span!("Lanes", len).in_scope(|| {
            let cols = COLS.min(lb);
            // SAFETY: the fill writes every element, and reads none.
            unsafe {
                primitives::filled_vec(len, |out: &mut [F128]| {
                    let (low, high) = out.split_at_mut(lb);
                    parallel::chunks_mut(low, cols, |t, out| {
                        folded.block(0, t * cols, out);
                    });
                    for (c, o) in (lb..).zip(high) {
                        *o = folded.at(0, c);
                    }
                })
            }
        });
        let w = tracing::info_span!("Lift").in_scope(|| self.terms.lift(&self.a));
        (lane, w, if keep_stack { self.stack } else { Vec::new() })
    }
}
