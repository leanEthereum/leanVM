//! The row side's base terms: what a table's rows add at the pointer-column index `q = 0`, as forms of degree at most
//! two in the table's columns.
//!
//! A table carries one block per weight and gate: `ω_F(u)·form(u)` for the ungated part of its links, then
//! `ω_F(u)·gate(u)·form(u)` for each gate, and for `JUMP` `eq(τ_F, u)·form(u)` with its identities. A block is of
//! degree 4 in a row variable at most: its weight, its gate and the form's products.
//!
//! A form's products mostly share a column (`fp` times an operand, a layout flag times a lane), so each form is kept as
//! `L(u) + Σ_a col_a(u)·L_a(u)` for linear forms `L`, `L_a`. The base tabulates those and the factor and gate columns
//! once on the explicit rows, the padrow's values past them, and folds them in place of every column the forms read.

use super::row::Poly;
use crate::form::Form;
use primitives::field::{F64, F128, F128Unreduced};
use primitives::multilinear::interp;

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

/// Rows per task of the payload's sum.
const PAYLOAD_ROWS: usize = 1 << 12;

/// A linear form over a table's columns, by local index.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Linear {
    constant: F128,
    terms: Vec<(usize, F128)>,
}

impl Linear {
    /// The form at a row, `row(c)` column `c`'s value there.
    fn at(&self, row: impl Fn(usize) -> F64) -> F128 {
        let mut sum = F128Unreduced::ZERO;
        for &(c, w) in &self.terms {
            sum ^= w.mul_base_unreduced(row(c));
        }
        self.constant + sum.reduce()
    }
}

/// A form as `L + Σ_a col_a·L_a` for linear forms `L`, `L_a`: its products grouped by a shared column, greedily by the
/// column the most remaining products read.
fn factor(form: &Form) -> (Linear, Vec<(usize, Linear)>) {
    let nonzero = |terms: &mut Vec<(usize, F128)>| terms.retain(|t| !t.1.is_zero());
    let mut linear: Vec<(usize, F128)> = form.coeffs.iter().copied().enumerate().collect();
    nonzero(&mut linear);
    let mut prods: Vec<(usize, usize, F128)> = form.prods.iter().filter(|p| !p.2.is_zero()).copied().collect();
    let mut groups = Vec::new();
    while !prods.is_empty() {
        let mut reads = vec![0usize; form.coeffs.len()];
        for &(a, b, _) in &prods {
            reads[a] += 1;
            reads[b] += (a != b) as usize;
        }
        let col = (0..reads.len()).max_by_key(|&c| reads[c]).expect("a column");
        let mut terms = vec![F128::ZERO; form.coeffs.len()];
        prods.retain(|&(a, b, w)| {
            let other = if a == col {
                b
            } else if b == col {
                a
            } else {
                return true;
            };
            terms[other] += w;
            false
        });
        let mut terms: Vec<(usize, F128)> = terms.into_iter().enumerate().collect();
        nonzero(&mut terms);
        groups.push((
            col,
            Linear {
                constant: F128::ZERO,
                terms,
            },
        ));
    }
    let linear = Linear {
        constant: form.constant,
        terms: linear,
    };
    (linear, groups)
}

/// What a slot holds: a column, by local index, or a linear form of the columns.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Slot {
    Column(usize),
    Linear(Linear),
}

impl Slot {
    /// The slot at a row, `row(c)` column `c`'s value there.
    fn at(&self, row: impl Fn(usize) -> F64) -> F128 {
        match self {
            Slot::Column(c) => row(*c).into(),
            Slot::Linear(l) => l.at(row),
        }
    }
}

/// A block over the slots: `weight·gate·(linear + Σ factor·form)`, each named by its slot.
#[derive(Clone, Debug)]
struct Shaped {
    weight: Weight,
    gate: Option<usize>,
    linear: usize,
    prods: Vec<(usize, usize)>,
}

impl Shaped {
    /// The gate times the form at a row of slot values, without the weight.
    fn at(&self, row: impl Fn(usize) -> F128) -> F128 {
        let form = row(self.linear) + self.prods.iter().map(|&(f, l)| row(f) * row(l)).sum::<F128>();
        self.gate.map_or(form, |g| row(g) * form)
    }
}

/// The base terms of one table, over its slots: the factor and gate columns and the linear forms of its factored forms
/// (`factor`).
pub struct Base {
    blocks: Vec<Shaped>,
    /// Each slot's values on the explicit rows, those past them the padrow's.
    values: Vec<Vec<F128>>,
    /// Each slot's value on the padrow.
    padrow: Vec<F128>,
    /// `eq(τ_F, u)` on every row, when a block is weighed by it.
    eq: Option<Vec<F128>>,
}

impl Base {
    /// `columns` holds every local column of the table, a column's rows past its length, and every row from
    /// `explicit` on, the padrow's value; `eq` the table of `eq(τ_F, ·)` when a block is weighed by it.
    pub fn new(blocks: Vec<Block>, columns: &[&[F64]], padrow: &[F64], explicit: usize, eq: Option<Vec<F128>>) -> Self {
        let full_padrow: Vec<F128> = padrow.iter().map(|&v| F128::from(v)).collect();
        assert!(
            (blocks.iter().filter(|b| b.weight == Weight::Eq)).all(|b| b.form.evaluate(&full_padrow).is_zero()),
            "a block weighed on every row vanishes on the padrow"
        );
        assert_eq!(eq.is_some(), blocks.iter().any(|b| b.weight == Weight::Eq));
        let mut slots: Vec<Slot> = Vec::new();
        let mut slot = |s: Slot| match slots.iter().position(|t| *t == s) {
            Some(at) => at,
            None => {
                slots.push(s);
                slots.len() - 1
            }
        };
        let blocks = (blocks.iter())
            .map(|b| {
                let (linear, groups) = factor(&b.form);
                Shaped {
                    weight: b.weight,
                    gate: b.gate.map(|g| slot(Slot::Column(g))),
                    linear: slot(Slot::Linear(linear)),
                    prods: (groups.into_iter())
                        .map(|(c, l)| (slot(Slot::Column(c)), slot(Slot::Linear(l))))
                        .collect(),
                }
            })
            .collect();
        let value = |c: usize, u: usize| match u < columns[c].len() {
            true => columns[c][u],
            false => padrow[c],
        };
        Self {
            blocks,
            values: (slots.iter())
                .map(|s| parallel::map_collect(explicit, |u| s.at(|c| value(c, u))))
                .collect(),
            padrow: slots.iter().map(|s| s.at(|c| padrow[c])).collect(),
            eq,
        }
    }

    /// `Σ_u ω(u)·gate(u)·form(u)` over the [`Weight::Omega`] blocks, `omega` on the executed rows: the index side's
    /// payload.
    pub fn payload(&self, omega: &[F128]) -> F128 {
        let blocks: Vec<&Shaped> = self.blocks.iter().filter(|b| b.weight == Weight::Omega).collect();
        parallel::map_reduce(
            omega.len().div_ceil(PAYLOAD_ROWS),
            || F128::ZERO,
            |task| {
                let rows = task * PAYLOAD_ROWS..omega.len().min((task + 1) * PAYLOAD_ROWS);
                rows.filter(|&u| !omega[u].is_zero())
                    .map(|u| omega[u] * blocks.iter().map(|b| b.at(|s| self.value(s, u))).sum::<F128>())
                    .sum()
            },
            |a, b| a + b,
        )
    }

    /// Whether a block reaches the padding rows, which then take part in the rounds up to the explicit rows.
    pub(super) fn on_padding(&self) -> bool {
        self.eq.is_some()
    }

    /// Slot `s` at row `u`.
    fn value(&self, s: usize, u: usize) -> F128 {
        self.values[s].get(u).copied().unwrap_or(self.padrow[s])
    }

    /// Add the pair `(2k, 2k + 1)`'s round polynomial `Σ weight(X)·gate(X)·form(X)`, `omega` being `ω_F` at the two
    /// rows: each slot a line through its two values, the form a quadratic, times the gate's line and the weight's.
    pub(super) fn add_pair(&self, k: usize, omega: (F128, F128), acc: &mut Poly) {
        let pair = |s: usize| (self.value(s, 2 * k), self.value(s, 2 * k + 1));
        for block in &self.blocks {
            let weight = match block.weight {
                Weight::Omega => omega,
                Weight::Eq => {
                    let eq = self.eq.as_ref().expect("an eq table");
                    (at(eq, 2 * k), at(eq, 2 * k + 1))
                }
            };
            if weight.0.is_zero() && weight.1.is_zero() {
                continue;
            }
            let mut form = Poly::line(pair(block.linear));
            for &(f, l) in &block.prods {
                form.add(&Poly::line(pair(f)).mul(&Poly::line(pair(l))));
            }
            if let Some(g) = block.gate {
                form = form.mul(&Poly::line(pair(g)));
            }
            acc.add(&form.mul(&Poly::line(weight)));
        }
    }

    /// Bind the lowest row variable at `x`, keeping the first `explicit` rows: those past are the padrow's.
    pub(super) fn fold(&mut self, explicit: usize, x: F128) {
        let values = (0..self.values.len())
            .map(|s| parallel::map_collect(explicit, |j| interp(self.value(s, 2 * j), self.value(s, 2 * j + 1), x)))
            .collect();
        self.values = values;
        if let Some(eq) = &mut self.eq {
            *eq = parallel::map_collect(eq.len().div_ceil(2), |j| interp(eq[2 * j], at(eq, 2 * j + 1), x));
        }
    }

    /// The base terms at the table's end, its rows bound: `omega` is `ω_F` there.
    pub(super) fn end(&self, omega: F128) -> F128 {
        (self.blocks.iter())
            .map(|b| {
                let weight = match b.weight {
                    Weight::Omega => omega,
                    Weight::Eq => self.eq.as_ref().expect("an eq table")[0],
                };
                weight * b.at(|s| self.value(s, 0))
            })
            .sum()
    }
}

/// `v[i]`, zero past its end.
fn at(v: &[F128], i: usize) -> F128 {
    v.get(i).copied().unwrap_or(F128::ZERO)
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::{eq_eval, eq_table, poly_eval};
    use primitives::test_rng::Rng;

    /// The rounds of a table's base terms sum to its blocks over the rows and end on the blocks at the bound point;
    /// the payload is the `ω` blocks' sum.
    #[test]
    fn base_matches_the_naive_sum_and_end() {
        let mut rng = Rng::new(0xba5e);
        for (m, rows, explicit) in [(4usize, 11usize, 13usize), (3, 8, 8), (5, 0, 3), (1, 1, 2), (0, 1, 1)] {
            let n_cols = 5;
            let padrow: Vec<F64> = vec![
                F64::ZERO,
                F64(rng.next_u64()),
                F64::ZERO,
                F64(rng.next_u64()),
                F64::ZERO,
            ];
            let columns: Vec<Vec<F64>> = (0..n_cols)
                .map(|c| {
                    (0..explicit)
                        .map(|u| if u % 3 == 2 { padrow[c] } else { F64(rng.next_u64()) })
                        .collect()
                })
                .collect();
            let col = |c: usize, u: usize| F128::from(columns[c].get(u).copied().unwrap_or(padrow[c]));
            let form = |rng: &mut Rng, constant: bool| {
                let mut f = Form::new(n_cols);
                f.constant = if constant { rng.ext() } else { F128::ZERO };
                f.coeffs[0] = rng.ext();
                f.coeffs[2] = rng.ext();
                if constant {
                    f.coeffs[1] = rng.ext();
                    f.prods.push((4, 4, rng.ext()));
                    f.prods.push((1, 3, rng.ext()));
                }
                f.prods.push((0, 2, rng.ext()));
                f.prods.push((2, 4, rng.ext()));
                f
            };
            // The eq block vanishes on the padrow: no constant, and columns 0, 2 and 4 are zero there.
            let blocks = vec![
                Block {
                    weight: Weight::Omega,
                    gate: None,
                    form: form(&mut rng, true),
                },
                Block {
                    weight: Weight::Omega,
                    gate: Some(3),
                    form: form(&mut rng, true),
                },
                Block {
                    weight: Weight::Eq,
                    gate: Some(1),
                    form: form(&mut rng, false),
                },
            ];
            let tau = rng.ext_vec(m);
            let eq = eq_table(&tau);
            let omega: Vec<F128> = rng.ext_vec(rows);
            let om = |u: usize| omega.get(u).copied().unwrap_or(F128::ZERO);
            let row_value = |with: [bool; 2], omega_u: F128, eq_u: F128, col: &dyn Fn(usize) -> F128| -> F128 {
                (blocks.iter())
                    .filter(|b| with[(b.weight == Weight::Eq) as usize])
                    .map(|b| {
                        let w = if b.weight == Weight::Omega { omega_u } else { eq_u };
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
            };
            let refs: Vec<&[F64]> = columns.iter().map(Vec::as_slice).collect();
            let mut base = Base::new(blocks.clone(), &refs, &padrow, explicit, Some(eq.clone()));
            let payload: F128 = (0..rows)
                .map(|u| row_value([true, false], om(u), eq[u], &|c| col(c, u)))
                .sum();
            assert_eq!(base.payload(&omega), payload);

            let mut claim: F128 = (0..1 << m)
                .map(|u| row_value([true, true], om(u), eq[u], &|c| col(c, u)))
                .sum();
            let mut omegas = omega.clone();
            let (mut point, mut n) = (Vec::new(), explicit);
            for _ in 0..m {
                let mut poly = Poly::default();
                for k in 0..n.div_ceil(2) {
                    let omega = (at(&omegas, 2 * k), at(&omegas, 2 * k + 1));
                    base.add_pair(k, omega, &mut poly);
                }
                let poly = poly.coeffs(5);
                assert_eq!(claim, poly[1..].iter().copied().sum::<F128>(), "a round's sum");
                let x = rng.ext();
                claim = poly_eval(&poly, x);
                omegas = (0..omegas.len().div_ceil(2))
                    .map(|k| interp(omegas[2 * k], at(&omegas, 2 * k + 1), x))
                    .collect();
                n = n.div_ceil(2);
                base.fold(n, x);
                point.push(x);
            }
            assert_eq!(claim, base.end(at(&omegas, 0)));
            let eqs = eq_table(&point);
            let mle = |f: &dyn Fn(usize) -> F128| (0..1 << m).map(|u| eqs[u] * f(u)).sum::<F128>();
            let cols: Vec<F128> = (0..n_cols).map(|c| mle(&|u| col(c, u))).collect();
            let expected = row_value([true, true], mle(&om), eq_eval(&tau, &point), &|c| cols[c]);
            assert_eq!(claim, expected);
        }
    }
}
