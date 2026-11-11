//! Level 0's fold rounds, on the weight's terms and the lanes' projections onto them.
//!
//! The weight is never written out over the stack: it stays `b(l, x) = sum_t A(l, t) K_t(x)`, and a round's table
//! is the rows of `A` against the projections `P(l, t) = sum_x lane(l, x) K_t(x)` of the lanes it needs (see the
//! `basis` module of `stack_open`). Round 1 projects the stack and `X` times its even lanes. A later round projects
//! only `X F`: the projections of `F`, `G` and the folded lanes are linear in the ones before.
//!
//! A fold folds `A` and the projections only. Its lanes are written by the next round's table: one pass folds the
//! round's pairs `(F, G)` into `P = G + alpha F + beta X F`, writes them out as the next round's pairs, and projects
//! `X` times each pair's first. Round 1's pairs are the stack's lanes, read in place. The last fold's one lane is
//! written out at the end, and the weight is lifted for it.
//!
//! The stack's absent lanes are zero, so they take no projection, but `A` keeps a row for every lane: a claim's weight
//! may reach past the committed lanes. A lane without a partner folds against zero, its row of `A` against its
//! partner's.
//!
//! Where the stack's blocks under a lane `X F` repeat, its blocks repeat past their first few words (one more per
//! round, from multiplying by `X`), so a block of `X F` is a repeat when those words are too.

use primitives::field::{F64, F64x8, F128, F128x8, mul_base_splat8};
use primitives::stream::Stream;

use crate::stack_open::{SWEEP, Terms};
use crate::whir::{FoldChallenges, FoldTable, InitialBasis};
use crate::xmul::{exponents8, mul_x_block, multiples, sums8, x_at};

/// The words of a block of a round-`r` lane `X F` that can differ from the block before when the stack's blocks under
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

/// A round's pairs `(F, G)`.
enum Pairs {
    /// Round 1's: the committed lanes two by two.
    Stack,
    /// A later round's, `len` coefficients each, a missing `G` zero.
    Stored { f: Vec<F128>, g: Vec<F128>, len: usize },
}

/// A round's folded lanes `P = G + alpha F + beta X F`, one coefficient longer than its pairs, read anywhere.
struct Folded<'a> {
    pairs: &'a Pairs,
    stack: &'a [F64],
    lane_block: usize,
    n_stack: usize,
    ch: FoldChallenges,
    /// `beta A_t` for every `t`: the challenges of `X F`.
    cx: [F128; 64],
}

impl Folded<'_> {
    fn count(&self) -> usize {
        match self.pairs {
            Pairs::Stack => self.n_stack.div_ceil(2),
            Pairs::Stored { f, len, .. } => f.len() / len,
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
        let FoldChallenges { alpha, beta, .. } = self.ch;
        match self.pairs {
            Pairs::Stack => self.stack_lane(2 * i).map_or(F128::ZERO, |f| {
                let g = self.stack_lane(2 * i + 1).map_or(F64::ZERO, |g| outside(g)(c));
                F128::from(g) + alpha.mul_base(outside(f)(c)) + beta.mul_base(x_at(f, c))
            }),
            Pairs::Stored { f, g, len } => match (f.get(i * len..(i + 1) * len), g.get(i * len..(i + 1) * len)) {
                (Some(f), Some(g)) => outside(g)(c) + alpha * outside(f)(c) + beta * x_at(f, c),
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
        let FoldChallenges { alpha, .. } = self.ch;
        let out = out.as_chunks_mut::<8>().0;
        let cx = |t0: usize| F128x8::from_array(&exponents8(t0).map(|t| self.cx[t]));
        match self.pairs {
            Pairs::Stack => {
                let f = self.stack_lane(2 * i).expect("a folded lane has its first");
                let g = self
                    .stack_lane(2 * i + 1)
                    .map(|g| g[first..first + n].as_chunks::<8>().0);
                let (fb, f8) = (&f[first..first + n], f[first..first + n].as_chunks::<8>().0);
                for (q, o) in out.iter_mut().enumerate() {
                    let (sf, t0) = sums8(fb, q, first, outside(f));
                    let sum = mul_base_splat8(alpha, &f8[q]) ^ cx(t0).mul_base_unreduced(F64x8::from_array(&sf));
                    *o = sum.reduce_lanes().to_array();
                    if let Some(g) = g {
                        o.iter_mut().zip(g[q]).for_each(|(o, g)| *o += F128::from(g));
                    }
                }
            }
            Pairs::Stored { f, g, len } => {
                let (f, g) = (&f[i * len..(i + 1) * len], &g[i * len..(i + 1) * len]);
                let (fb, alpha) = (&f[first..first + n], F128x8::splat(alpha));
                let (f8, g8) = (fb.as_chunks::<8>().0, g[first..first + n].as_chunks::<8>().0);
                for (q, o) in out.iter_mut().enumerate() {
                    let (sf, t0) = sums8(fb, q, first, outside(f));
                    let sum =
                        alpha.mul_unreduced(F128x8::from_array(&f8[q])) ^ cx(t0).mul_unreduced(F128x8::from_array(&sf));
                    *o = (F128x8::from_array(&g8[q]) + sum.reduce_lanes()).to_array();
                }
            }
        }
    }
}

/// What a round's table leaves for its fold: the projections of `X F` per pair, and the pairs.
struct Pending {
    pxf: Vec<F128>,
    pairs: Pairs,
}

pub(crate) struct LaneRounds {
    /// The committed lanes, read until round 2's table (or `finish` after one round), then freed unless `keep_stack`.
    stack: Vec<F64>,
    keep_stack: bool,
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
    /// Rounds whose tables are taken.
    round: usize,
}

impl LaneRounds {
    pub(crate) fn new(stack: Vec<F64>, basis: InitialBasis, lane_block: usize, keep_stack: bool) -> Self {
        let InitialBasis { a, n_terms, terms } = basis;
        assert!(lane_block > 0 && stack.len().is_multiple_of(lane_block));
        assert_eq!(lane_block, 1 << terms.lane_vars());
        let n_lanes = stack.len() / lane_block;
        assert!(a.len().is_multiple_of(n_terms) && a.len() >= n_lanes * n_terms);
        Self {
            stack,
            keep_stack,
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
            cx: multiples(ch.beta),
        }
    }

    /// Round 1's projections: every lane's into `p`, and `X F`'s per pair.
    fn project_stack(&mut self, live: &[bool]) -> Vec<F128> {
        let (nt, n, lb) = (self.n_terms, self.n_lanes, self.lane_block);
        let (stack, terms) = (&self.stack, &self.terms);
        let low = terms.low_vars();
        let rows = tracing::info_span!("Project", lanes = n + n.div_ceil(2)).in_scope(|| {
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
                    if l % 2 == 1 {
                        continue;
                    }
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
        self.p = rows.chunks_exact(nt).step_by(2).flatten().copied().collect();
        // Lane `2m`'s second slot.
        rows.chunks_exact(nt).skip(1).step_by(4).flatten().copied().collect()
    }

    /// A later round's pairs, the last fold's lanes, written out, and `X F`'s projection per pair.
    fn write_pairs(&self, folded: &Folded, live: &[bool]) -> (Pairs, Vec<F128>) {
        let (nt, lb, terms) = (self.n_terms, self.lane_block, &self.terms);
        let (count, len) = (folded.count(), folded.len());
        let n_pairs = count.div_ceil(2);
        let (low, block) = (terms.low_vars(), 1usize << terms.low_vars());
        // The stack lanes under a pair's `F`, and the words of `X F` a repeat of theirs leaves free.
        let (group, head) = (1usize << (self.round - 1), self.round);
        // SAFETY: the pass writes every low coefficient and the loop after it every high one, before any is read.
        let (mut f, mut g) = unsafe {
            (
                primitives::uninit_vec(n_pairs * len),
                primitives::uninit_vec(n_pairs * len),
            )
        };
        let (fp, gp) = (parallel::SendPtr(f.as_mut_ptr()), parallel::SendPtr(g.as_mut_ptr()));
        let rows = tracing::info_span!("Project", lanes = n_pairs).in_scope(|| {
            terms.project_rows(n_pairs, 2, live, |m, blocks, feed| {
                let stream = Stream::new();
                let [mut pa, mut pb, mut xf] = [0; 3].map(|_| vec![F128::ZERO; block]);
                let mut limbs = [vec![F64::ZERO; SWEEP << low], vec![F64::ZERO; SWEEP << low]];
                let mut tags = [false; SWEEP];
                let stacked = 2 * m * group..((2 * m + 1) * group).min(self.n_stack);
                let repeats = |b: usize| {
                    head <= HEAD
                        && stacked
                            .clone()
                            .all(|l| terms.lane_repeats(l, b..b + 1).first() == Some(&true))
                };
                // The block before's last `F` coefficient and first words of `X F`.
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
                        // SAFETY: each task owns its blocks of its pair.
                        unsafe {
                            stream.copy(fp.slice(m * len + first, block), &pa);
                            stream.copy(gp.slice(m * len + first, block), &pb);
                        }
                        let outside = |c: usize| match last {
                            Some((before, _)) if c + 1 == first => before,
                            _ => folded.at(2 * m, c),
                        };
                        mul_x_block(&pa, first, outside, &mut xf);
                        let words: [F128; HEAD] = xf[..HEAD].try_into().expect("a block holds its head");
                        tags[k] = last.is_some_and(|(_, w)| w == words) && repeats(b);
                        last = Some((pa[block - 1], words));
                        let [lo, hi] = &mut limbs;
                        for ((lo, hi), v) in lo[k << low..].iter_mut().zip(&mut hi[k << low..]).zip(&xf) {
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
                f[m * len + c] = folded.at(2 * m, c);
                g[m * len + c] = folded.at(2 * m + 1, c);
            }
        }
        let pxf = (0..n_pairs * nt)
            .map(|i| {
                let (m, t) = (i / nt, i % nt);
                rows[2 * m * nt + t] + F128::Y * rows[(2 * m + 1) * nt + t]
            })
            .collect();
        (Pairs::Stored { f, g, len }, pxf)
    }

    /// The round's table.
    pub(crate) fn table(&mut self) -> FoldTable {
        let (nt, n_pairs) = (self.n_terms, self.n_lanes.div_ceil(2));
        self.round += 1;
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
                if matches!(pairs, Pairs::Stack) && !self.keep_stack {
                    self.stack = Vec::new();
                }
                written
            }
        };

        let zero = vec![F128::ZERO; nt];
        let mut table = [F128::ZERO; 5];
        for m in 0..n_pairs {
            let f = self.row(&self.p, 2 * m).expect("a pair's first lane is present");
            let g = self.row(&self.p, 2 * m + 1).unwrap_or(&zero);
            let a0 = self.row(&self.a, 2 * m).expect("a pair's first lane is present");
            let a1 = self.row(&self.a, 2 * m + 1).unwrap_or(&zero);
            let xf = &pxf[m * nt..][..nt];
            for (s, v) in table
                .iter_mut()
                .zip([dot(a0, g), dot(a0, f), dot(a0, xf), dot(a1, f), dot(a1, xf)])
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
                let a0 = self.a[2 * m * nt + t];
                let a1 = self.a.get((2 * m + 1) * nt + t).copied().unwrap_or(F128::ZERO);
                a0 + alpha * (a0 + a1)
            })
            .collect();
        let p = &self.p;
        self.p = (0..n_pairs * nt)
            .map(|i| {
                let (m, t) = (i / nt, i % nt);
                let g = p.get((2 * m + 1) * nt + t).copied().unwrap_or(F128::ZERO);
                g + alpha * p[2 * m * nt + t] + beta * pxf[i]
            })
            .collect();
        self.folded = Some((pairs, *ch));
        self.n_lanes = n_pairs;
    }

    /// The one lane left, low coefficients then high, the weight lifted over its low coefficients, and the committed
    /// lanes if `keep_stack`.
    pub(crate) fn finish(self) -> (Vec<F128>, Vec<F128>, Vec<F64>) {
        assert_eq!(
            (self.n_lanes, self.a.len()),
            (1, self.n_terms),
            "every lane variable is folded"
        );
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
        (lane, w, if self.keep_stack { self.stack } else { Vec::new() })
    }
}
