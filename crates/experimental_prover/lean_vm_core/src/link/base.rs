//! The row side's base terms: what a table's rows add at the pointer-column index `q = 0`, as forms of degree at most
//! two in the table's columns.
//!
//! A table carries one block per weight and gate: `ω_F(u)·form(u)` for the ungated part of its links, then
//! `ω_F(u)·gate(u)·form(u)` for each gate, and for `JUMP` `eq(τ_F, u)·form(u)` with its four identities. A block
//! is degree 4 in a row variable at most: its weight, its gate and the form's products.
//!
//! A form's products mostly share a column (`fp` times an operand, a layout flag times a lane), so each form is kept
//! as `L(u) + Σ_a col_a(u)·L_a(u)` for linear forms `L`, `L_a`. The prover tabulates every `L` once on the explicit
//! rows from the committed `K` columns, then folds those and the factor columns instead of every column a form reads.

use super::{at, fold};
use crate::form::Form;
use primitives::field::{F64, F128, F128Unreduced};
use std::mem::MaybeUninit;

/// What a block's form is multiplied by.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Weight {
    /// The table's `ω_F`, which vanishes on its padding rows.
    Omega,
    /// `eq(τ_F, u)` on every row, padding rows included.
    Eq,
}

/// One block: `weight(u)·gate(u)·form(u)`.
#[derive(Clone, Debug)]
pub struct Block {
    pub weight: Weight,
    pub gate: Option<usize>,
    pub form: Form,
}

/// A linear form over a table's columns, by local index.
#[derive(Clone, Debug)]
struct Linear {
    constant: F128,
    terms: Vec<(usize, F128)>,
}

impl Linear {
    #[inline(always)]
    fn at(&self, column: impl Fn(usize) -> F64) -> F128 {
        let sum = self.terms.iter().fold(F128Unreduced::ZERO, |acc, &(c, w)| {
            acc ^ w.mul_base_unreduced(column(c))
        });
        self.constant + sum.reduce()
    }

    /// The form at two rows, `column(c)` giving column `c` at both, in one pass over the terms.
    #[inline(always)]
    fn at_pair(&self, column: impl Fn(usize) -> (F64, F64)) -> (F128, F128) {
        let (lo, hi) = self
            .terms
            .iter()
            .fold((F128Unreduced::ZERO, F128Unreduced::ZERO), |(lo, hi), &(c, w)| {
                let (a, b) = column(c);
                (lo ^ w.mul_base_unreduced(a), hi ^ w.mul_base_unreduced(b))
            });
        (self.constant + lo.reduce(), self.constant + hi.reduce())
    }
}

/// A linear form's constant and each term's column with its coefficient times `1 + x` and times `x`: the form at a
/// row folded at `x` from the two rows' columns.
type SplitLinear = (F128, Vec<(usize, F128, F128)>);

/// A block over the tabulated values: its weight, its gate's slot, the slot of its linear part and a
/// `(factor, linear form)` pair of slots per product.
#[derive(Clone, Debug)]
struct Factored {
    weight: Weight,
    gate: Option<usize>,
    linear: usize,
    products: Vec<(usize, usize)>,
}

/// The products of a form, grouped by a shared column: `(column, Σ w·other)` per group, greedily by the column the
/// most remaining products read.
fn factor(prods: &[(usize, usize, F128)]) -> Vec<(usize, Linear)> {
    let mut left: Vec<(usize, usize, F128)> = prods.iter().copied().filter(|p| !p.2.is_zero()).collect();
    let mut out = Vec::new();
    while !left.is_empty() {
        let mut counts = std::collections::BTreeMap::<usize, usize>::new();
        for &(a, b, _) in &left {
            *counts.entry(a).or_default() += 1;
            if b != a {
                *counts.entry(b).or_default() += 1;
            }
        }
        let column = counts
            .iter()
            .max_by_key(|&(c, n)| (*n, std::cmp::Reverse(*c)))
            .map(|(&c, _)| c)
            .unwrap();
        let mut terms: Vec<(usize, F128)> = Vec::new();
        left.retain(|&(a, b, w)| {
            if a != column && b != column {
                return true;
            }
            let other = if a == column { b } else { a };
            match terms.iter_mut().find(|(c, _)| *c == other) {
                Some((_, v)) => *v += w,
                None => terms.push((other, w)),
            }
            false
        });
        out.push((
            column,
            Linear {
                constant: F128::ZERO,
                terms,
            },
        ));
    }
    out
}

/// The base terms of one table.
pub struct Base<'a> {
    blocks: Vec<Factored>,
    /// The factor and gate columns, by local index, in slot order.
    factors: Vec<usize>,
    linears: Vec<Linear>,
    /// Round 1's columns, every row of each, by local index.
    columns: Vec<&'a [F64]>,
    /// After round 1: the slots' values on the explicit rows, `stride` a row.
    folded: Option<Vec<F128>>,
    /// The slots' values on the padrow.
    tail: Vec<F128>,
    stride: usize,
    /// `eq(τ_F, u)` on every row, when a block is weighted by it.
    eq: Option<Vec<F128>>,
}

/// Round 1's columns on one task's rows ([`Base::window`]), one run of words each: column `c` at row `u` is
/// `cols[c][u - start]`.
pub struct Window<'a> {
    start: usize,
    cols: Vec<&'a [F64]>,
}

/// Rows per task of a fold.
const FOLD_ROWS: usize = 512;

/// The most slots a table's base terms use.
const MAX_SLOTS: usize = 128;

/// `p ← p·a(X)` for `p` of `len` coefficients and the linear `a` given at 0 and 1; the new length.
#[inline(always)]
fn times_linear(p: &mut [F128; 5], len: usize, (a0, a1): (F128, F128)) -> usize {
    let b = a0 + a1;
    p[len] = p[len - 1] * b;
    for j in (1..len).rev() {
        p[j] = (p[j].mul_unreduced(a0) ^ p[j - 1].mul_unreduced(b)).reduce();
    }
    p[0] *= a0;
    len + 1
}

/// `p ← p + w(X)·g(X)·f(X)` for linear `w`, `g` given at 0 and 1, `w` one when absent, and the quadratic `f` in
/// coefficients.
#[inline(always)]
fn add_block(acc: &mut [F128], w: Option<(F128, F128)>, gate: Option<(F128, F128)>, f: [F128; 3]) {
    let mut p = [f[0], f[1], f[2], F128::ZERO, F128::ZERO];
    let mut len = 3;
    for a in gate.into_iter().chain(w) {
        len = times_linear(&mut p, len, a);
    }
    for (o, v) in acc.iter_mut().zip(&p[..len]) {
        *o += *v;
    }
}

/// [`add_block`] for a gate that is still a `K` column, by mixed products.
#[inline(always)]
fn add_block_base(acc: &mut [F128], w: Option<(F128, F128)>, gate: Option<(F64, F64)>, f: [F128; 3]) {
    let mut p = [f[0], f[1], f[2], F128::ZERO, F128::ZERO];
    let mut len = 3;
    if let Some((a0, a1)) = gate {
        let b = a0 + a1;
        p[3] = p[2].mul_base(b);
        for j in (1..3).rev() {
            p[j] = (p[j].mul_base_unreduced(a0) ^ p[j - 1].mul_base_unreduced(b)).reduce();
        }
        p[0] = p[0].mul_base(a0);
        len = 4;
    }
    if let Some(w) = w {
        len = times_linear(&mut p, len, w);
    }
    for (o, v) in acc.iter_mut().zip(&p[..len]) {
        *o += *v;
    }
}

/// A block's gate times its form at a row of slot values, unweighted.
#[inline(always)]
fn form_at(b: &Factored, row: &[F128]) -> F128 {
    let products = b
        .products
        .iter()
        .fold(F128Unreduced::ZERO, |acc, &(f, l)| acc ^ row[f].mul_unreduced(row[l]));
    let form = row[b.linear] + products.reduce();
    b.gate.map_or(form, |g| row[g] * form)
}

impl<'a> Base<'a> {
    /// `columns` holds every local column of the table, every row; `padrow` the table's padding row; `eq` the table
    /// of `eq(τ_F, ·)` when a block is weighted by it.
    pub fn new(blocks: Vec<Block>, columns: Vec<&'a [F64]>, padrow: &[F64], eq: Option<Vec<F128>>) -> Self {
        let mut factors: Vec<usize> = Vec::new();
        let mut linears: Vec<Linear> = Vec::new();
        let slot = |c: usize, factors: &mut Vec<usize>| {
            factors.iter().position(|&f| f == c).unwrap_or_else(|| {
                factors.push(c);
                factors.len() - 1
            })
        };
        let mut shaped = Vec::with_capacity(blocks.len());
        for b in &blocks {
            let gate = b.gate.map(|g| slot(g, &mut factors));
            linears.push(Linear {
                constant: b.form.constant,
                terms: b
                    .form
                    .coeffs
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| !c.is_zero())
                    .map(|(i, &c)| (i, c))
                    .collect(),
            });
            let linear = linears.len() - 1;
            let products: Vec<(usize, usize)> = factor(&b.form.prods)
                .into_iter()
                .map(|(column, form)| {
                    linears.push(form);
                    (slot(column, &mut factors), linears.len() - 1)
                })
                .collect();
            shaped.push((b.weight, gate, linear, products));
        }
        let n = factors.len();
        let blocks: Vec<Factored> = shaped
            .into_iter()
            .map(|(weight, gate, linear, products)| Factored {
                weight,
                gate,
                linear: n + linear,
                products: products.into_iter().map(|(f, l)| (f, n + l)).collect(),
            })
            .collect();
        let stride = n + linears.len();
        assert!(
            stride <= MAX_SLOTS,
            "a table's base terms use at most {MAX_SLOTS} slots"
        );
        let mut base = Self {
            blocks,
            factors,
            linears,
            columns,
            folded: None,
            tail: Vec::new(),
            stride,
            eq,
        };
        // SAFETY: `slots` writes each of the `stride` values.
        base.tail = unsafe { primitives::filled_vec(stride, |tail| base.slots(|c| padrow[c], tail)) };
        assert!(
            base.blocks
                .iter()
                .filter(|b| b.weight == Weight::Eq)
                .all(|b| form_at(b, &base.tail).is_zero()),
            "a block weighted on every row vanishes on the padrow"
        );
        assert_eq!(base.eq.is_some(), base.blocks.iter().any(|b| b.weight == Weight::Eq));
        base
    }

    /// The slots' values at a row of `K` values, `column` reading a local column there: the first `stride` of `out`.
    #[inline(always)]
    fn slots(&self, column: impl Fn(usize) -> F64 + Copy, out: &mut [MaybeUninit<F128>]) {
        let n = self.factors.len();
        for (o, &c) in out.iter_mut().zip(&self.factors) {
            o.write(F128::from(column(c)));
        }
        for (o, l) in out[n..].iter_mut().zip(&self.linears) {
            o.write(l.at(column));
        }
    }

    /// Round 1's columns on rows `start..end`, or nothing once they are folded.
    pub fn window(&self, start: usize, end: usize) -> Window<'a> {
        let cols = match self.folded {
            Some(_) => Vec::new(),
            None => (self.columns.iter())
                .map(|c| &c[start.min(c.len())..end.min(c.len())])
                .collect(),
        };
        Window { start, cols }
    }

    /// Call `f` on the slots' values at row `u`, which `rows` covers before the first fold.
    #[inline(always)]
    fn with_row<R>(&self, rows: &Window, u: usize, f: impl FnOnce(&[F128]) -> R) -> R {
        let s = self.stride;
        match &self.folded {
            Some(folded) => f(folded.get(u * s..(u + 1) * s).unwrap_or(&self.tail)),
            None if rows.cols.first().is_some_and(|c| u - rows.start < c.len()) => {
                let mut row = [MaybeUninit::<F128>::uninit(); MAX_SLOTS];
                let u = u - rows.start;
                self.slots(|c| rows.cols[c][u], &mut row[..s]);
                // SAFETY: `slots` wrote each of the first `s` values.
                f(unsafe { row[..s].assume_init_ref() })
            }
            None => f(&self.tail),
        }
    }

    /// The first round's polynomial of the `ω` blocks, `Σ_k ω(X)·gate(X)·form(X)` over the pairs `(2k, 2k + 1)`,
    /// with `omega` on the executed rows. Its values at 0 and 1 sum to what the blocks sum to before any row is
    /// bound. With `tau0`, `ω` is `θ·eq(τ, ·)` there and `tau0` is `τ`'s first coordinate, so a pair of executed
    /// rows has `ω(X) = (ω_0 + ω_1)·eq(τ_0, X)` and the product with `eq(τ_0, X)` is taken once.
    pub fn omega_round(&self, omega: &[F128], tau0: Option<F128>) -> [F128; 5] {
        let pairs = omega.len().div_ceil(2);
        let whole = if tau0.is_some() { omega.len() / 2 } else { 0 };
        let (factored, direct) = parallel::fold_reduce(
            pairs.div_ceil(FOLD_ROWS),
            || ([F128Unreduced::ZERO; 4], [F128::ZERO; 5]),
            |(factored, direct), task| {
                let range = task * FOLD_ROWS..pairs.min((task + 1) * FOLD_ROWS);
                let rows = self.window(2 * range.start, 2 * range.end);
                for k in range {
                    let (w0, w1) = (omega[2 * k], at(omega, 2 * k + 1));
                    if w0.is_zero() && w1.is_zero() {
                        continue;
                    }
                    let (mut under, mut eq_blocks) = ([F128::ZERO; 4], [F128::ZERO; 5]);
                    self.pair(&rows, k, true, true, &mut under, &mut eq_blocks);
                    if k < whole {
                        let s = w0 + w1;
                        for (f, &v) in factored.iter_mut().zip(&under) {
                            *f ^= v.mul_unreduced(s);
                        }
                    } else {
                        let wb = w0 + w1;
                        direct[0] += under[0] * w0;
                        for j in 1..4 {
                            direct[j] += (under[j].mul_unreduced(w0) ^ under[j - 1].mul_unreduced(wb)).reduce();
                        }
                        direct[4] += under[3] * wb;
                    }
                }
            },
            |(mut fa, mut da), (fb, db)| {
                for (x, y) in fa.iter_mut().zip(fb) {
                    *x ^= y;
                }
                for (x, y) in da.iter_mut().zip(db) {
                    *x += y;
                }
                (fa, da)
            },
        );
        // `eq(τ_0, X) = 1 + τ_0 + X`.
        let mut out = direct;
        if let Some(t) = tau0 {
            let f = factored.map(F128Unreduced::reduce);
            for j in 0..4 {
                out[j] += f[j] * (F128::ONE + t);
                out[j + 1] += f[j];
            }
        }
        out
    }

    /// Whether a block reaches the padding rows, so the rounds must sum every explicit pair.
    pub fn on_padding(&self) -> bool {
        self.eq.is_some()
    }

    /// Add the pair `(2k, 2k + 1)`'s round polynomial: the `ω` blocks without their weight to `omega` when
    /// `with_omega`, the others to `acc`. Without `x1`, the `X` coefficient added to `omega` may be anything.
    #[inline(always)]
    pub fn pair(&self, rows: &Window, k: usize, with_omega: bool, x1: bool, omega: &mut [F128], acc: &mut [F128]) {
        let eq = self.eq.as_ref().map(|e| (at(e, 2 * k), at(e, 2 * k + 1)));
        if self.folded.is_none() && rows.cols.first().is_some_and(|c| 2 * k + 1 - rows.start < c.len()) {
            self.pair_columns(rows, k, with_omega, eq, omega, acc);
            return;
        }
        self.with_row(rows, 2 * k, |lo| {
            self.with_row(rows, 2 * k + 1, |hi| {
                for block in &self.blocks {
                    let (out, w) = match block.weight {
                        Weight::Omega if with_omega => (&mut *omega, None),
                        Weight::Omega => continue,
                        Weight::Eq => (&mut *acc, eq),
                    };
                    if w.is_some_and(|w| w.0.is_zero() && w.1.is_zero()) {
                        continue;
                    }
                    // A block that is its form alone puts the form's `X` coefficient only in the sum's, which
                    // without `x1` is not wanted: its value at the second row is skipped.
                    let exact = x1 || w.is_some() || block.gate.is_some();
                    let (mut c0, mut c1, mut c2) = (F128Unreduced::ZERO, F128Unreduced::ZERO, F128Unreduced::ZERO);
                    for &(f, l) in &block.products {
                        let (a0, a1, b0, b1) = (lo[f], hi[f], lo[l], hi[l]);
                        c0 ^= a0.mul_unreduced(b0);
                        if exact {
                            c1 ^= a1.mul_unreduced(b1);
                        }
                        c2 ^= (a0 + a1).mul_unreduced(b0 + b1);
                    }
                    let f0 = lo[block.linear] + c0.reduce();
                    let f2 = c2.reduce();
                    let mid = if exact {
                        f0 + hi[block.linear] + c1.reduce() + f2
                    } else {
                        F128::ZERO
                    };
                    add_block(out, w, block.gate.map(|g| (lo[g], hi[g])), [f0, mid, f2]);
                }
            })
        });
    }

    /// [`Self::pair`] on two rows of the `K` columns, before the first fold: a factor or gate is a column's value,
    /// so each product with it is a mixed one.
    #[inline(always)]
    fn pair_columns(
        &self,
        rows: &Window,
        k: usize,
        with_omega: bool,
        eq: Option<(F128, F128)>,
        omega: &mut [F128],
        acc: &mut [F128],
    ) {
        let (u0, u1) = (2 * k - rows.start, 2 * k + 1 - rows.start);
        let n = self.factors.len();
        let factor = |f: usize| {
            let c = rows.cols[self.factors[f]];
            (c[u0], c[u1])
        };
        // The linear slots at both rows.
        let mut lo = [MaybeUninit::<F128>::uninit(); MAX_SLOTS];
        let mut hi = [MaybeUninit::<F128>::uninit(); MAX_SLOTS];
        for ((l, a), b) in self.linears.iter().zip(&mut lo).zip(&mut hi) {
            let (x, y) = l.at_pair(|c| {
                let col = rows.cols[c];
                (col[u0], col[u1])
            });
            a.write(x);
            b.write(y);
        }
        let m = self.linears.len();
        // SAFETY: the loop above wrote the first `m` values of each.
        let (lo, hi) = unsafe { (lo[..m].assume_init_ref(), hi[..m].assume_init_ref()) };
        for block in &self.blocks {
            let (out, w) = match block.weight {
                Weight::Omega if with_omega => (&mut *omega, None),
                Weight::Omega => continue,
                Weight::Eq => (&mut *acc, eq),
            };
            if w.is_some_and(|w| w.0.is_zero() && w.1.is_zero()) {
                continue;
            }
            let (mut c0, mut c1, mut c2) = (F128Unreduced::ZERO, F128Unreduced::ZERO, F128Unreduced::ZERO);
            for &(f, l) in &block.products {
                let ((a0, a1), (b0, b1)) = (factor(f), (lo[l - n], hi[l - n]));
                c0 ^= b0.mul_base_unreduced(a0);
                c1 ^= b1.mul_base_unreduced(a1);
                c2 ^= (b0 + b1).mul_base_unreduced(a0 + a1);
            }
            let f0 = lo[block.linear - n] + c0.reduce();
            let f1 = hi[block.linear - n] + c1.reduce();
            let f2 = c2.reduce();
            add_block_base(out, w, block.gate.map(factor), [f0, f0 + f1 + f2, f2]);
        }
    }

    /// Bind the lowest row variable at `x`: `explicit` rows after.
    pub fn fold(&mut self, explicit: usize, x: F128) {
        let s = self.stride;
        let n = self.factors.len();
        // Before the first fold, each linear form at the folded row is `(1 + x)·L(lo) + x·L(hi)`: its coefficients
        // times `1 + x` and `x` on the two rows' columns, with no product of the two rows' values.
        let split: Vec<SplitLinear> = match &self.folded {
            Some(_) => Vec::new(),
            None => (self.linears.iter())
                .map(|l| {
                    let terms = l.terms.iter().map(|&(c, w)| (c, w * (F128::ONE + x), w * x)).collect();
                    (l.constant, terms)
                })
                .collect(),
        };
        let rows = self.columns.first().map_or(0, |c| c.len());
        // SAFETY: every row writes each of its `s` values.
        let folded = unsafe {
            primitives::filled_vec(explicit * s, |out| {
                if s > 0 {
                    parallel::chunks_mut(out, s * FOLD_ROWS, |task, chunk| {
                        let start = 2 * task * FOLD_ROWS;
                        let cols = self.window(start, start + 2 * FOLD_ROWS);
                        for (j, row) in chunk.chunks_mut(s).enumerate() {
                            let k = task * FOLD_ROWS + j;
                            if self.folded.is_none() && 2 * k + 1 < rows {
                                let u = 2 * j;
                                let column = |c: usize| (cols.cols[c][u], cols.cols[c][u + 1]);
                                for (o, &c) in row.iter_mut().zip(&self.factors) {
                                    let (a, b) = column(c);
                                    o.write(F128::from(a) + x.mul_base(a + b));
                                }
                                for (o, (constant, terms)) in row[n..].iter_mut().zip(&split) {
                                    let sum = terms.iter().fold(F128Unreduced::ZERO, |acc, &(c, w0, w1)| {
                                        let (a, b) = column(c);
                                        acc ^ w0.mul_base_unreduced(a) ^ w1.mul_base_unreduced(b)
                                    });
                                    o.write(*constant + sum.reduce());
                                }
                                continue;
                            }
                            self.with_row(&cols, 2 * k, |lo| {
                                self.with_row(&cols, 2 * k + 1, |hi| {
                                    for ((o, &a), &b) in row.iter_mut().zip(lo).zip(hi) {
                                        o.write(fold(a, b, x));
                                    }
                                })
                            });
                        }
                    });
                }
            })
        };
        self.folded = Some(folded);
        if let Some(eq) = &mut self.eq {
            *eq = (0..eq.len().div_ceil(2))
                .map(|k| {
                    let (a, b) = (eq[2 * k], at(eq, 2 * k + 1));
                    a + x * (a + b)
                })
                .collect();
        }
    }

    /// The base terms at the table's end, its rows bound: `omega` is `ω_F` there.
    pub fn end(&self, omega: F128) -> F128 {
        let eq = self.eq.as_ref().map(|e| e[0]);
        self.with_row(&self.window(0, 1), 0, |row| {
            self.blocks
                .iter()
                .map(|b| {
                    let w = match b.weight {
                        Weight::Omega => omega,
                        Weight::Eq => eq.expect("an eq table"),
                    };
                    w * form_at(b, row)
                })
                .sum()
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::{eq_table, poly_eval};
    use primitives::test_rng::Rng;

    /// The rounds of a table's base terms sum to its blocks over the rows, and end on the blocks at the bound point.
    #[test]
    fn base_matches_the_naive_sum_and_end() {
        let mut rng = Rng::new(0xba5e);
        let (m, rows, n_cols) = (4usize, 11usize, 5usize);
        let padrow: Vec<F64> = vec![F64::ZERO; n_cols];
        let columns: Vec<Vec<F64>> = (0..n_cols)
            .map(|_| {
                (0..1 << m)
                    .map(|u| if u < 13 { F64(rng.next_u64()) } else { F64::ZERO })
                    .collect()
            })
            .collect();
        let form = |rng: &mut Rng| {
            let mut f = Form::new(n_cols);
            f.constant = rng.ext();
            f.coeffs[1] = rng.ext();
            f.coeffs[3] = rng.ext();
            f.prods.push((0, 2, rng.ext()));
            f.prods.push((4, 4, rng.ext()));
            f.prods.push((1, 2, rng.ext()));
            f.prods.push((2, 2, rng.ext()));
            f
        };
        // The eq block must vanish on the zero padrow: no constant.
        let mut eq_form = form(&mut rng);
        eq_form.constant = F128::ZERO;
        let blocks = vec![
            Block {
                weight: Weight::Omega,
                gate: None,
                form: form(&mut rng),
            },
            Block {
                weight: Weight::Omega,
                gate: Some(3),
                form: form(&mut rng),
            },
            Block {
                weight: Weight::Eq,
                gate: None,
                form: eq_form,
            },
        ];
        let tau = rng.ext_vec(m);
        let eq = eq_table(&tau);
        let omega: Vec<F128> = (0..1 << m)
            .map(|u| if u < rows { rng.ext() } else { F128::ZERO })
            .collect();
        let scales = [F128::ONE; 3];
        let row_value = |scales: &[F128], omega_u: F128, eq_u: F128, col: &dyn Fn(usize) -> F128| -> F128 {
            blocks
                .iter()
                .zip(scales)
                .map(|(b, &scale)| {
                    let w = if b.weight == Weight::Omega { omega_u } else { eq_u };
                    let mut f = b.form.constant;
                    for (i, &c) in b.form.coeffs.iter().enumerate() {
                        f += c * col(i);
                    }
                    for &(x, y, c) in &b.form.prods {
                        f += c * col(x) * col(y);
                    }
                    scale * w * b.gate.map_or(F128::ONE, col) * f
                })
                .sum()
        };
        let mut claim: F128 = (0..1 << m)
            .map(|u| row_value(&scales, omega[u], eq[u], &|c| F128::from(columns[c][u])))
            .sum();
        let refs: Vec<&[F64]> = columns.iter().map(Vec::as_slice).collect();
        let mut base = Base::new(blocks.clone(), refs, &padrow, Some(eq.clone()));
        let omega_only = [F128::ONE, F128::ONE, F128::ZERO];
        let omega_sum: F128 = (0..1 << m)
            .map(|u| row_value(&omega_only, omega[u], eq[u], &|c| F128::from(columns[c][u])))
            .sum();
        let first = base.omega_round(&omega[..rows], None);
        assert_eq!(first[1..].iter().copied().sum::<F128>(), omega_sum);
        // With `ω = θ·eq(τ, ·)` on the executed rows, factoring `eq(τ_0, X)` out gives the same polynomial.
        let theta = rng.ext();
        let omega_eq: Vec<F128> = eq[..rows].iter().map(|&e| theta * e).collect();
        assert_eq!(
            base.omega_round(&omega_eq, Some(tau[0])),
            base.omega_round(&omega_eq, None)
        );
        let mut om = omega.clone();
        let mut point = Vec::new();
        let mut explicit = 1 << m;
        for _ in 0..m {
            let mut poly = [F128::ZERO; 5];
            for k in 0..explicit / 2 {
                let mut under = [F128::ZERO; 4];
                base.pair(&base.window(2 * k, 2 * k + 2), k, true, true, &mut under, &mut poly);
                let (w0, w1) = (om[2 * k], om[2 * k] + om[2 * k + 1]);
                for j in 0..5 {
                    poly[j] += at(&under, j) * w0 + if j > 0 { under[j - 1] * w1 } else { F128::ZERO };
                }
            }
            assert_eq!(claim, poly[1..].iter().copied().sum::<F128>());
            let x = rng.ext();
            claim = poly_eval(&poly, x);
            om = (0..om.len() / 2)
                .map(|k| om[2 * k] + x * (om[2 * k] + om[2 * k + 1]))
                .collect();
            explicit /= 2;
            base.fold(explicit, x);
            point.push(x);
        }
        assert_eq!(claim, base.end(om[0]));
        let eqs = eq_table(&point);
        let mle = |f: &dyn Fn(usize) -> F128| (0..1 << m).map(|u| eqs[u] * f(u)).sum::<F128>();
        let cols: Vec<F128> = (0..n_cols).map(|c| mle(&|u| F128::from(columns[c][u]))).collect();
        let expected = row_value(&scales, mle(&|u| omega[u]), eq_eval_at(&tau, &point), &|c| cols[c]);
        assert_eq!(claim, expected);
    }

    fn eq_eval_at(a: &[F128], b: &[F128]) -> F128 {
        primitives::multilinear::eq_eval(a, b)
    }
}
