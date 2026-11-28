//! Hotwire's row side: one sum-check over every table's rows, then over the pointer columns.
//!
//! The rows are bound lowest variable first, so a round pairs consecutive rows of a table. A table of `2^m` rows takes
//! part from round 1 and is finished after `m` rounds; from then on its value is multiplied by the all-zeros corner
//! factor `1 + x_h` of each further row variable. The pointer-column variables `q` come last.
//!
//! A pointer column `q` of table `F` contributes, at row `u`,
//!
//! `c_q(u)·Φ_0(u; r) + Σ_g c_g(u)·Φ_g(u; r) + ω_F(u)·Σ_i ε_{q,i}·(D_i(u; r_i)·D_i(u; 1 + r_i) + π_{w_i}(r_i))`,
//!
//! the column's coefficient `c_q = ω_F·(constant + aux) + act_F·(constant + aux)` times the pointer at the index point
//! `r`, each shift group's `c_g` times the pointer read further inside its window (`Φ_g`, chunk 0's table
//! `Σ_s μ_s·T_s` in place of `D_0`), plus the mirror certificate (the mirror test of Emile Wambsgans), which vanishes
//! on every executed row whose chunks are one-hot.
//!
//! Rows from `explicit` on hold the padrow, whose pointer words are zero, so every folded group of them holds the
//! padrow's values. A table's base terms ([`super::base`]) belong to the pointer-column index `q = 0`: the row rounds
//! add them like any summand, and the column rounds carry their total `B` as `eq(0, q)·B`.

use super::base::Base;
use super::pointer::{ChunkEq, Chunks, Shifts, eval_chunk, from_slices, mirror};
use primitives::field::F128;
use primitives::multilinear::{eq_table, interp, poly_eval};

/// A column's coefficient on one of its table's two row weights: `constant`, plus a scale times one of the table's
/// linear forms ([`RowTable::aux`]) when `aux` names one.
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
    /// The linear forms the coefficients name, each on the explicit rows, and their values on the padrow.
    pub aux: Vec<Vec<F128>>,
    pub aux_tail: Vec<F128>,
    pub columns: Vec<RowColumn<'a>>,
    /// The table's base terms, at `q = 0`.
    pub base: Base,
}

/// The functionals the row side reads pointers with: `D_i` at the index point `r`, at `1 + r` for the certificate,
/// chunk 0's window shifts at `r`, and `π_{w_i}(r_i)` per chunk.
pub struct RowPoints {
    pub eq: ChunkEq,
    pub bar: ChunkEq,
    pub shifts: Shifts,
    pub mirrors: Vec<F128>,
}

impl RowPoints {
    pub fn new(chunks: &Chunks, r: &[F128], max_shift: usize) -> Self {
        let eq = ChunkEq::at(chunks, r);
        Self {
            bar: ChunkEq::mirrored(chunks, r),
            shifts: Shifts::new(&eq, max_shift),
            mirrors: (0..chunks.d()).map(|i| mirror(chunks.part(r, i))).collect(),
            eq,
        }
    }
}

/// A column at the end of the row rounds: its 64 bit-slices at `χ_F`, and the values they give: `D_i` at `r` and at
/// `1 + r` (`d` each), then chunk 0's `T_s` for each shift `s` from 1 to the largest (`verifier`'s `Functionals`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnEnd {
    pub slices: Vec<F128>,
    pub values: Vec<F128>,
}

impl ColumnEnd {
    pub fn from_slices(chunks: &Chunks, points: &RowPoints, slices: Vec<F128>) -> Self {
        let d = chunks.d();
        let mut values: Vec<F128> = (0..d).map(|i| points.eq.from_slices(chunks, &slices, i)).collect();
        values.extend((0..d).map(|i| points.bar.from_slices(chunks, &slices, i)));
        let shifts = &points.shifts.tables[1..];
        values.extend(shifts.iter().map(|table| from_slices(chunks, table, &slices, 0)));
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

/// `(c·D_0 + Σ_s c_s·T_s)·Π_{i ≥ 1} D_i + Σ_i e_i·(D_i(r_i)·D_i(1 + r_i) + π_i)` from a column's values laid out as
/// [`ColumnEnd::values`]: the pointer at `r`, the pointer read `s` further, and the mirror certificate. `shifts[s - 1]`
/// is `c_s`.
pub fn summand(d: usize, mirrors: &[F128], coef: F128, shifts: &[F128], values: &[F128], certs: &[F128]) -> F128 {
    let rest: F128 = values[1..d].iter().copied().product();
    let low = coef * values[0]
        + (shifts.iter().zip(&values[2 * d..]))
            .map(|(&c, &v)| c * v)
            .sum::<F128>();
    let cert: F128 = (0..d)
        .map(|i| certs[i] * (values[i] * values[d + i] + mirrors[i]))
        .sum();
    low * rest + cert
}

/// The row side over `tables`, continuing `claim`. `round` takes each round polynomial's coefficients and returns the
/// challenge: [`row_coeffs`] of them a row round, [`column_coeffs`] a pointer-column round. The pointer-column rounds
/// run over `q_vars` variables, each column at its own `q`.
pub fn prove(
    chunks: &Chunks,
    points: &RowPoints,
    tables: Vec<RowTable>,
    q_vars: usize,
    claim: F128,
    round: &mut dyn FnMut(&[F128]) -> F128,
) -> RowEnd {
    let n_coeffs = row_coeffs(chunks.d());
    let n_rounds = tables.iter().map(|t| t.log_rows).max().unwrap_or(0);
    let mut states: Vec<State> = tables.into_iter().map(|t| State::new(t, chunks, points)).collect();
    let mut claim = claim;
    let mut point = Vec::with_capacity(n_rounds);
    let rounds = tracing::info_span!("Row rounds").entered();
    for h in 0..n_rounds {
        let _round = tracing::info_span!("Row round", round = h).entered();
        let poly = tracing::info_span!("Sum").in_scope(|| round_poly(&states, chunks));
        debug_assert_eq!(claim, poly.sum_at_0_and_1(), "a row round's sum");
        let coeffs = poly.coeffs(n_coeffs);
        let x = round(&coeffs);
        claim = poly_eval(&coeffs, x);
        tracing::info_span!("Fold").in_scope(|| {
            for state in &mut states {
                state.fold(x, chunks, points);
            }
        });
        point.push(x);
    }
    drop(rounds);

    let mut columns: Vec<ColumnAt> = (0..1 << q_vars).map(|_| ColumnAt::zero(chunks, points)).collect();
    let mut taken = vec![false; columns.len()];
    let mut base = F128::ZERO;
    let mut ends = Vec::with_capacity(states.len());
    for state in states {
        let (end, _) = state.done.expect("every table is bound after the row rounds");
        base += end.corner * end.base;
        for (column, column_end) in state.columns.iter().zip(&end.columns) {
            let q = column.input.q;
            assert!(!std::mem::replace(&mut taken[q], true), "two columns at q = {q}");
            let (coef, shifts, certs) = end_coefs(&column.input, &end, points.shifts.max_shift);
            let scale = |v: Vec<F128>| v.into_iter().map(|v| end.corner * v).collect();
            columns[q] = ColumnAt {
                coef: end.corner * coef,
                shifts: scale(shifts),
                values: column_end.values.clone(),
                certs: scale(certs),
            };
        }
        ends.push(end);
    }
    let (column_point, claim) = tracing::info_span!("Pointer-column rounds")
        .in_scope(|| prove_columns(chunks.d(), &points.mirrors, columns, base, claim, round));
    RowEnd {
        point,
        column_point,
        tables: ends,
        claim,
    }
}

/// Coefficients of a row round: degree `d + 2` from a gated coefficient times a pointer, 4 from the base terms.
pub fn row_coeffs(d: usize) -> usize {
    (d + 2).max(4) + 1
}

/// Coefficients of a column round: degree `d + 1` from a pointer, 3 from a certificate.
pub fn column_coeffs(d: usize) -> usize {
    (d + 1).max(3) + 1
}

/// Rounds that read a column's values from its words: the fold after the last stores them, for a sixteenth of the
/// rows.
const WORD_ROUNDS: usize = 4;

/// Pairs of rows a task of a round sums.
const TASK_PAIRS: usize = 256;

/// Rows a task of the bit-slices sums.
const SLICE_ROWS: usize = 1 << 12;

/// Coefficients of a round polynomial, at most: [`row_coeffs`] of the most chunks a pointer has, nine.
const MAX_COEFFS: usize = 12;

/// A polynomial in the round's variable `X`, its first `len` coefficients from the constant up.
#[derive(Clone, Copy, Debug)]
pub(super) struct Poly {
    coeffs: [F128; MAX_COEFFS],
    len: usize,
}

impl Default for Poly {
    fn default() -> Self {
        Self {
            coeffs: [F128::ZERO; MAX_COEFFS],
            len: 0,
        }
    }
}

impl Poly {
    fn from_coeffs(c: &[F128]) -> Self {
        let mut p = Self::default();
        p.coeffs[..c.len()].copy_from_slice(c);
        p.len = c.len();
        p
    }

    pub(super) fn constant(c: F128) -> Self {
        Self::from_coeffs(&[c])
    }

    /// The line through `lo` at 0 and `hi` at 1.
    pub(super) fn line((lo, hi): (F128, F128)) -> Self {
        Self::from_coeffs(&[lo, lo + hi])
    }

    pub(super) fn add(&mut self, other: &Self) {
        for (a, &b) in self.coeffs.iter_mut().zip(&other.coeffs[..other.len]) {
            *a += b;
        }
        self.len = self.len.max(other.len);
    }

    pub(super) fn mul(&self, other: &Self) -> Self {
        let mut p = Self::default();
        if self.len == 0 || other.len == 0 {
            return p;
        }
        p.len = self.len + other.len - 1;
        assert!(
            p.len <= MAX_COEFFS,
            "a round polynomial has at most {MAX_COEFFS} coefficients"
        );
        for (i, &a) in self.coeffs[..self.len].iter().enumerate() {
            for (j, &b) in other.coeffs[..other.len].iter().enumerate() {
                p.coeffs[i + j] += a * b;
            }
        }
        p
    }

    /// `p(0) + p(1)`, what the round's claim is.
    fn sum_at_0_and_1(&self) -> F128 {
        self.coeffs[1..].iter().copied().sum()
    }

    /// The first `n` coefficients, past the degree zero.
    pub(super) fn coeffs(&self, n: usize) -> Vec<F128> {
        assert!(
            self.coeffs.iter().skip(n).all(|c| c.is_zero()),
            "a round polynomial past {n} coefficients"
        );
        (0..n).map(|j| at(&self.coeffs, j, F128::ZERO)).collect()
    }
}

/// `(c·D_0 + Σ_s c_s·T_s)·Π_{i ≥ 1} D_i + Σ_i e_i·(D_i·D̄_i + π_i)` over a pair, as [`summand`] at each `X`: `lines[k]`
/// is value `k` ([`ColumnEnd::values`]) and `shifts[s]` the coefficient of value `2d + s`, each a line, `certs[i]` the
/// polynomial `e_i`.
fn summand_poly(d: usize, mirrors: &[F128], coef: &Poly, shifts: &[Poly], lines: &[Poly], certs: &[Poly]) -> Poly {
    let rest = (1..d).fold(Poly::constant(F128::ONE), |p, i| p.mul(&lines[i]));
    let mut low = coef.mul(&lines[0]);
    for (c, line) in shifts.iter().zip(&lines[2 * d..]) {
        low.add(&c.mul(line));
    }
    let mut poly = low.mul(&rest);
    for i in 0..d {
        let mut cert = lines[i].mul(&lines[d + i]);
        cert.add(&Poly::constant(mirrors[i]));
        poly.add(&certs[i].mul(&cert));
    }
    poly
}

/// A column's coefficient on `Φ_0`, on each shift `s` (at `s - 1`), and its certificate weights at its table's end,
/// without the corner factor.
fn end_coefs(column: &RowColumn, end: &TableEnd, max_shift: usize) -> (F128, Vec<F128>, Vec<F128>) {
    let weight = |c: Coef| c.constant + c.aux.map_or(F128::ZERO, |(a, s)| s * end.aux[a]);
    let coef = end.omega * weight(column.omega) + end.act * weight(column.act);
    let mut shifts = vec![F128::ZERO; max_shift];
    for g in &column.shifts {
        for &(s, mu) in &g.weights {
            shifts[s - 1] += end.omega * weight(g.coef) * mu;
        }
    }
    let certs = column.cert.iter().map(|&e| end.omega * e).collect();
    (coef, shifts, certs)
}

/// `v[i]`, `tail` past its end.
fn at(v: &[F128], i: usize, tail: F128) -> F128 {
    v.get(i).copied().unwrap_or(tail)
}

/// `v`, `tail` past its end, with its lowest variable bound at `x`, over `len` entries.
fn fold_vec(v: &[F128], tail: F128, len: usize, x: F128) -> Vec<F128> {
    parallel::map_collect(len, |j| interp(at(v, 2 * j, tail), at(v, 2 * j + 1, tail), x))
}

/// One pointer column through the row rounds.
struct Column<'a> {
    input: RowColumn<'a>,
    /// Per value slot, its chunk and table: `D_i` at `r`, `ε_i·D_i` at `1 + r` (the certificate's weight taken in),
    /// then each shift group's chunk-0 table.
    tables: Vec<(usize, Vec<F128>)>,
    /// `ε_i·π_i`, the certificate's constant per chunk.
    mirrors: Vec<F128>,
    /// Once stored, each slot's values on the explicit rows, zero past them; until then they are read from the words.
    values: Option<Vec<Vec<F128>>>,
}

impl<'a> Column<'a> {
    fn new(input: RowColumn<'a>, chunks: &Chunks, points: &RowPoints) -> Self {
        let d = chunks.d();
        let mut tables: Vec<(usize, Vec<F128>)> = (0..d).map(|i| (i, points.eq.tables[i].clone())).collect();
        let bar = |i: usize| points.bar.tables[i].iter().map(|&v| input.cert[i] * v).collect();
        tables.extend((0..d).map(|i| (i, bar(i))));
        tables.extend(input.shifts.iter().map(|g| (0, points.shifts.combined(&g.weights))));
        Self {
            mirrors: (0..d).map(|i| input.cert[i] * points.mirrors[i]).collect(),
            input,
            tables,
            values: None,
        }
    }

    /// Slot `s` at row `j` of the rows folded so far, `eq` the weight of each word a row folds, `eq` of the row
    /// challenges bound.
    fn value(&self, s: usize, j: usize, eq: &[F128], chunks: &Chunks) -> F128 {
        match &self.values {
            Some(values) => at(&values[s], j, F128::ZERO),
            None => {
                let (i, table) = &self.tables[s];
                let words = &self.input.words[j * eq.len()..(j + 1) * eq.len()];
                (eq.iter().zip(words))
                    .map(|(&e, &w)| e * eval_chunk(chunks, table, w, *i))
                    .sum()
            }
        }
    }

    /// Bind the lowest row variable at `x` over `len` rows, `eq` the words' weights with it bound: fold the stored
    /// values, or store them once the words have been read for [`WORD_ROUNDS`] rounds.
    fn fold(&mut self, x: F128, len: usize, eq: &[F128], chunks: &Chunks) {
        let slots = 0..self.tables.len();
        self.values = match &self.values {
            Some(values) => Some(values.iter().map(|v| fold_vec(v, F128::ZERO, len, x)).collect()),
            None if eq.len() == 1 << WORD_ROUNDS => Some(
                slots
                    .map(|s| parallel::map_collect(len, |j| self.value(s, j, eq, chunks)))
                    .collect(),
            ),
            None => None,
        };
    }

    /// The column's 64 bit-slices at the table's row point, `eq` its `eq` table ([`ColumnEnd`]).
    fn end(&self, chunks: &Chunks, points: &RowPoints, eq: &[F128]) -> ColumnEnd {
        let words = self.input.words;
        assert_eq!(words.len(), eq.len(), "a column is its table's rows");
        let slices = parallel::fold_reduce(
            words.len().div_ceil(SLICE_ROWS),
            || vec![F128::ZERO; 64],
            |slices, task| {
                for u in task * SLICE_ROWS..words.len().min((task + 1) * SLICE_ROWS) {
                    for (b, slice) in slices.iter_mut().enumerate() {
                        if words[u] >> b & 1 == 1 {
                            *slice += eq[u];
                        }
                    }
                }
            },
            |mut a, b| {
                a.iter_mut().zip(b).for_each(|(a, b)| *a += b);
                a
            },
        );
        ColumnEnd::from_slices(chunks, points, slices)
    }
}

/// One table through the row rounds.
struct State<'a> {
    log_rows: usize,
    /// Rows at the current level where `ω_F` or `act_F` can be nonzero.
    live: usize,
    /// Rows at the current level that are not the padrow.
    explicit: usize,
    /// `ω_F` and `act_F` on the live rows.
    omega: Vec<F128>,
    act: Vec<F128>,
    /// [`RowTable::aux`] on the explicit rows, and the padrow's.
    aux: Vec<Vec<F128>>,
    aux_tail: Vec<F128>,
    columns: Vec<Column<'a>>,
    base: Option<Base>,
    /// The row challenges bound so far, and their `eq` table while the columns read their words.
    bound: Vec<F128>,
    eq: Vec<F128>,
    /// Once its rows are bound: its end, the corner factor since, and its value there.
    done: Option<(TableEnd, F128)>,
}

impl<'a> State<'a> {
    fn new(table: RowTable<'a>, chunks: &Chunks, points: &RowPoints) -> Self {
        assert!(table.rows <= table.explicit && table.explicit <= 1 << table.log_rows);
        assert_eq!(table.omega.len(), table.rows);
        let explicit = table.explicit;
        let aux = (table.aux.into_iter())
            .map(|mut a| {
                assert!(a.len() >= explicit, "an aux form on every explicit row");
                a.truncate(explicit);
                a
            })
            .collect();
        let mut state = Self {
            log_rows: table.log_rows,
            live: table.rows,
            explicit,
            act: vec![F128::ONE; table.rows],
            omega: table.omega,
            aux,
            aux_tail: table.aux_tail,
            columns: (table.columns.into_iter())
                .map(|c| Column::new(c, chunks, points))
                .collect(),
            base: Some(table.base),
            bound: Vec::new(),
            eq: vec![F128::ONE],
            done: None,
        };
        if state.log_rows == 0 {
            state.finish(chunks, points);
        }
        state
    }

    /// Aux form `a` at row `j`.
    fn aux_at(&self, a: usize, j: usize) -> F128 {
        at(&self.aux[a], j, self.aux_tail[a])
    }

    /// The pairs of rows a round sums: the live ones, and the explicit ones when the base terms reach them.
    fn pairs(&self) -> usize {
        let live = self.live.div_ceil(2);
        match &self.base {
            Some(base) if base.on_padding() => live.max(self.explicit.div_ceil(2)),
            _ => live,
        }
    }

    /// The pair `(2k, 2k + 1)`'s round polynomial: each column's summand under `ω_F` and `act_F`, then the base terms.
    fn pair_poly(&self, k: usize, chunks: &Chunks) -> Poly {
        let d = chunks.d();
        let pair = |v: &[F128]| (at(v, 2 * k, F128::ZERO), at(v, 2 * k + 1, F128::ZERO));
        let (omega, act) = (pair(&self.omega), pair(&self.act));
        let mut poly = Poly::default();
        // The columns' terms vanish where `ω_F` and `act_F` do.
        if omega != (F128::ZERO, F128::ZERO) || act != (F128::ZERO, F128::ZERO) {
            let (omega, act) = (Poly::line(omega), Poly::line(act));
            let coef = |c: Coef| {
                let aux = |j: usize| c.aux.map_or(F128::ZERO, |(a, s)| s * self.aux_at(a, j));
                Poly::line((c.constant + aux(2 * k), c.constant + aux(2 * k + 1)))
            };
            for column in &self.columns {
                let value = |s: usize, j: usize| column.value(s, j, &self.eq, chunks);
                let lines: Vec<Poly> = (0..column.tables.len())
                    .map(|s| Poly::line((value(s, 2 * k), value(s, 2 * k + 1))))
                    .collect();
                let input = &column.input;
                let mut pointer = coef(input.omega).mul(&omega);
                pointer.add(&coef(input.act).mul(&act));
                let shifts: Vec<Poly> = input.shifts.iter().map(|g| coef(g.coef).mul(&omega)).collect();
                // The certificate's weights are in the bar tables and the mirrors.
                let certs = vec![omega; d];
                poly.add(&summand_poly(d, &column.mirrors, &pointer, &shifts, &lines, &certs));
            }
        }
        if let Some(base) = &self.base {
            base.add_pair(k, omega, &mut poly);
        }
        poly
    }

    /// Bind the lowest row variable at `x`; a finished table only takes its corner factor.
    fn fold(&mut self, x: F128, chunks: &Chunks, points: &RowPoints) {
        if let Some((end, _)) = &mut self.done {
            end.corner *= F128::ONE + x;
            return;
        }
        let (live, explicit) = (self.live.div_ceil(2), self.explicit.div_ceil(2));
        self.omega = fold_vec(&self.omega, F128::ZERO, live, x);
        self.act = fold_vec(&self.act, F128::ZERO, live, x);
        for (a, &tail) in self.aux.iter_mut().zip(&self.aux_tail) {
            *a = fold_vec(a, tail, explicit, x);
        }
        if let Some(base) = &mut self.base {
            base.fold(explicit, x);
        }
        self.bound.push(x);
        if self.bound.len() <= WORD_ROUNDS {
            self.eq = eq_table(&self.bound);
        }
        for column in &mut self.columns {
            column.fold(x, explicit, &self.eq, chunks);
        }
        (self.live, self.explicit) = (live, explicit);
        if self.bound.len() == self.log_rows {
            self.finish(chunks, points);
        }
    }

    /// Rows bound: the table's end and its value there.
    fn finish(&mut self, chunks: &Chunks, points: &RowPoints) {
        let omega = at(&self.omega, 0, F128::ZERO);
        let eq = eq_table(&self.bound);
        let end = TableEnd {
            omega,
            act: at(&self.act, 0, F128::ZERO),
            aux: (0..self.aux.len()).map(|a| self.aux_at(a, 0)).collect(),
            corner: F128::ONE,
            columns: (self.columns.iter()).map(|c| c.end(chunks, points, &eq)).collect(),
            base: self.base.as_ref().map_or(F128::ZERO, |b| b.end(omega)),
        };
        let d = chunks.d();
        let value: F128 = (self.columns.iter().zip(&end.columns))
            .map(|(column, column_end)| {
                let (coef, shifts, certs) = end_coefs(&column.input, &end, points.shifts.max_shift);
                summand(d, &points.mirrors, coef, &shifts, &column_end.values, &certs)
            })
            .sum();
        let value = value + end.base;
        self.done = Some((end, value));
        for column in &mut self.columns {
            column.values = None;
        }
        (self.omega, self.act, self.aux, self.base) = (Vec::new(), Vec::new(), Vec::new(), None);
    }
}

/// A row round's polynomial: every live table's pairs, then each finished table's value times its corner factor and
/// `1 + X`.
fn round_poly(states: &[State], chunks: &Chunks) -> Poly {
    let tasks: Vec<(usize, std::ops::Range<usize>)> = (states.iter().enumerate())
        .filter(|(_, s)| s.done.is_none())
        .flat_map(|(t, s)| {
            let pairs = s.pairs();
            (0..pairs.div_ceil(TASK_PAIRS)).map(move |i| (t, i * TASK_PAIRS..pairs.min((i + 1) * TASK_PAIRS)))
        })
        .collect();
    let mut poly = parallel::fold_reduce(
        tasks.len(),
        Poly::default,
        |acc, i| {
            let (t, pairs) = &tasks[i];
            for k in pairs.clone() {
                acc.add(&states[*t].pair_poly(k, chunks));
            }
        },
        |mut a, b| {
            a.add(&b);
            a
        },
    );
    for (end, value) in states.iter().filter_map(|s| s.done.as_ref()) {
        poly.add(&Poly::line((*value * end.corner, F128::ZERO)));
    }
    poly
}

/// One pointer column as the pointer-column rounds read it: its coefficient on `Φ_0`, per shift `s` (at `s - 1`), its
/// values ([`ColumnEnd::values`]) and its certificate weights per chunk, each times its table's corner factor.
#[derive(Clone, Debug)]
struct ColumnAt {
    coef: F128,
    shifts: Vec<F128>,
    values: Vec<F128>,
    certs: Vec<F128>,
}

impl ColumnAt {
    /// The empty column.
    fn zero(chunks: &Chunks, points: &RowPoints) -> Self {
        let (d, max_shift) = (chunks.d(), points.shifts.max_shift);
        Self {
            coef: F128::ZERO,
            shifts: vec![F128::ZERO; max_shift],
            values: vec![F128::ZERO; 2 * d + max_shift],
            certs: vec![F128::ZERO; d],
        }
    }
}

/// The rounds over the pointer-column index `q`, lowest bit first, over `columns.len()` columns; `base` is the
/// tables' base terms, at `q = 0`. Ends at the summand at `q*`.
fn prove_columns(
    d: usize,
    mirrors: &[F128],
    mut columns: Vec<ColumnAt>,
    mut base: F128,
    mut claim: F128,
    round: &mut dyn FnMut(&[F128]) -> F128,
) -> (Vec<F128>, F128) {
    assert!(columns.len().is_power_of_two());
    let n_coeffs = column_coeffs(d);
    let mut point = Vec::new();
    while columns.len() > 1 {
        let mut poly = Poly::line((base, F128::ZERO));
        for [lo, hi] in columns.as_chunks::<2>().0 {
            let lines = |lo: &[F128], hi: &[F128]| -> Vec<Poly> {
                lo.iter().zip(hi).map(|(&a, &b)| Poly::line((a, b))).collect()
            };
            poly.add(&summand_poly(
                d,
                mirrors,
                &Poly::line((lo.coef, hi.coef)),
                &lines(&lo.shifts, &hi.shifts),
                &lines(&lo.values, &hi.values),
                &lines(&lo.certs, &hi.certs),
            ));
        }
        debug_assert_eq!(claim, poly.sum_at_0_and_1(), "a pointer-column round's sum");
        let coeffs = poly.coeffs(n_coeffs);
        let x = round(&coeffs);
        claim = poly_eval(&coeffs, x);
        base *= F128::ONE + x;
        let fold = |a: &[F128], b: &[F128]| a.iter().zip(b).map(|(&a, &b)| interp(a, b, x)).collect();
        columns = (columns.as_chunks::<2>().0.iter())
            .map(|[lo, hi]| ColumnAt {
                coef: interp(lo.coef, hi.coef, x),
                shifts: fold(&lo.shifts, &hi.shifts),
                values: fold(&lo.values, &hi.values),
                certs: fold(&lo.certs, &hi.certs),
            })
            .collect();
        point.push(x);
    }
    let c = &columns[0];
    let last = summand(d, mirrors, c.coef, &c.shifts, &c.values, &c.certs) + base;
    debug_assert_eq!(claim, last, "the pointer-column rounds end at the summand");
    (point, last)
}

#[cfg(test)]
mod tests {
    use super::super::base::{Block, Weight};
    use super::super::pointer::eval_chunk;
    use super::*;
    use crate::form::Form;
    use primitives::field::F64;
    use primitives::multilinear::eq_eval;
    use primitives::test_rng::Rng;

    /// Value slot `k`'s chunk and table ([`ColumnEnd::values`]' order).
    fn slot_table(points: &RowPoints, d: usize, k: usize) -> (usize, &[F128]) {
        match k {
            k if k < d => (k, &points.eq.tables[k]),
            k if k < 2 * d => (k - d, &points.bar.tables[k - d]),
            k => (0, &points.shifts.tables[k - 2 * d + 1]),
        }
    }

    /// A word's values, laid out as [`ColumnEnd::values`].
    fn word_values(chunks: &Chunks, points: &RowPoints, word: u64) -> Vec<F128> {
        let d = chunks.d();
        (0..2 * d + points.shifts.max_shift)
            .map(|k| {
                let (i, table) = slot_table(points, d, k);
                eval_chunk(chunks, table, word, i)
            })
            .collect()
    }

    /// Random words whose neighbouring rows share most chunks, some not one-hot, some near the top of their window
    /// so a shift leaves it, zero from `explicit` on.
    fn random_words(rng: &mut Rng, chunks: &Chunks, n: usize, explicit: usize) -> Vec<u64> {
        let mask = (1usize << chunks.width) - 1;
        let mut sigma = rng.next_u64() as usize & mask;
        (0..n)
            .map(|u| {
                if u >= explicit {
                    return 0;
                }
                if rng.next_u64().is_multiple_of(3) {
                    sigma = (sigma + rng.next_u64() as usize % 5) & mask;
                }
                if rng.next_u64().is_multiple_of(7) {
                    sigma = (sigma | ((1 << chunks.widths[0]) - 2)) & mask;
                }
                let word = chunks.encode(sigma);
                if rng.next_u64().is_multiple_of(11) {
                    word ^ 1 << (rng.next_u64() % 64)
                } else {
                    word
                }
            })
            .collect()
    }

    #[test]
    fn values_from_slices_are_the_words_values_summed() {
        let mut rng = Rng::new(0x51c);
        for (width, max_shift) in [(1usize, 1usize), (7, 3), (22, 12), (24, 12)] {
            let chunks = Chunks::new(width);
            let points = RowPoints::new(&chunks, &rng.ext_vec(width), max_shift);
            let words = random_words(&mut rng, &chunks, 37, 37);
            let weights = rng.ext_vec(words.len());
            let slices = (0..64)
                .map(|b| {
                    (words.iter().zip(&weights))
                        .map(|(&w, &e)| e * F128::new(w >> b & 1, 0))
                        .sum()
                })
                .collect();
            let mut expected = vec![F128::ZERO; 2 * chunks.d() + max_shift];
            for (&w, &e) in words.iter().zip(&weights) {
                for (v, x) in expected.iter_mut().zip(word_values(&chunks, &points, w)) {
                    *v += e * x;
                }
            }
            assert_eq!(ColumnEnd::from_slices(&chunks, &points, slices).values, expected);
        }
    }

    #[test]
    fn pointer_column_rounds_end_at_the_summand() {
        let mut rng = Rng::new(0xc01);
        for (width, max_shift, n) in [(7usize, 3usize, 5usize), (22, 12, 8), (3, 1, 1), (24, 2, 13)] {
            let chunks = Chunks::new(width);
            let d = chunks.d();
            let points = RowPoints::new(&chunks, &rng.ext_vec(width), max_shift);
            let q_vars = n.next_power_of_two().trailing_zeros() as usize;
            let columns: Vec<ColumnAt> = (0..1 << q_vars)
                .map(|q| match q < n {
                    true => ColumnAt {
                        coef: rng.ext(),
                        shifts: rng.ext_vec(max_shift),
                        values: rng.ext_vec(2 * d + max_shift),
                        certs: rng.ext_vec(d),
                    },
                    false => ColumnAt::zero(&chunks, &points),
                })
                .collect();
            let at_q = |c: &ColumnAt| summand(d, &points.mirrors, c.coef, &c.shifts, &c.values, &c.certs);
            let base = rng.ext();
            let mut claim = columns.iter().map(at_q).sum::<F128>() + base;
            let mut n_rounds = 0;
            let (point, last) = prove_columns(d, &points.mirrors, columns.clone(), base, claim, &mut |poly| {
                assert_eq!(poly.len(), column_coeffs(d));
                assert_eq!(claim, poly[1..].iter().copied().sum::<F128>(), "a round's sum");
                n_rounds += 1;
                let x = rng.ext();
                claim = poly_eval(poly, x);
                x
            });
            assert_eq!((n_rounds, claim), (q_vars, last));
            let eqq = eq_table(&point);
            let mle = |f: &dyn Fn(&ColumnAt) -> F128| columns.iter().zip(&eqq).map(|(c, &e)| e * f(c)).sum::<F128>();
            let folded = ColumnAt {
                coef: mle(&|c| c.coef),
                shifts: (0..max_shift).map(|s| mle(&|c| c.shifts[s])).collect(),
                values: (0..2 * d + max_shift).map(|k| mle(&|c| c.values[k])).collect(),
                certs: (0..d).map(|i| mle(&|c| c.certs[i])).collect(),
            };
            let eq0: F128 = point.iter().map(|&x| F128::ONE + x).product();
            assert_eq!(last, at_q(&folded) + eq0 * base);
        }
    }

    /// A random table: three pointer columns, the first read shifted by one, the second by several shifts in two
    /// groups; three committed columns for the base terms, the padrow past `explicit`.
    struct Raw {
        log_rows: usize,
        rows: usize,
        explicit: usize,
        omega: Vec<F128>,
        aux: Vec<Vec<F128>>,
        aux_tail: Vec<F128>,
        words: Vec<Vec<u64>>,
        coefs: Vec<(Coef, Coef, Vec<ShiftGroup>, Vec<F128>)>,
        k_columns: Vec<Vec<F64>>,
        padrow: Vec<F64>,
        blocks: Vec<Block>,
        tau: Vec<F128>,
    }

    impl Raw {
        fn aux_at(&self, a: usize, u: usize) -> F128 {
            if u < self.explicit {
                self.aux[a][u]
            } else {
                self.aux_tail[a]
            }
        }

        fn omega_at(&self, u: usize) -> F128 {
            self.omega.get(u).copied().unwrap_or(F128::ZERO)
        }

        fn act_at(&self, u: usize) -> F128 {
            if u < self.rows { F128::ONE } else { F128::ZERO }
        }

        /// The base terms at one row, from the committed columns' values there.
        fn base_at(&self, omega: F128, eq: F128, col: &dyn Fn(usize) -> F128) -> F128 {
            (self.blocks.iter())
                .map(|b| {
                    let w = if b.weight == Weight::Omega { omega } else { eq };
                    w * b.gate.map_or(F128::ONE, col) * b.form.evaluate(&[col(0), col(1), col(2)])
                })
                .sum()
        }

        fn row_table(&self, base_q: &mut usize) -> RowTable<'_> {
            RowTable {
                log_rows: self.log_rows,
                rows: self.rows,
                explicit: self.explicit,
                omega: self.omega.clone(),
                aux: self.aux.clone(),
                aux_tail: self.aux_tail.clone(),
                columns: (self.words.iter().zip(&self.coefs))
                    .map(|(w, (o, a, g, e))| {
                        *base_q += 1;
                        RowColumn {
                            words: w,
                            omega: *o,
                            act: *a,
                            shifts: g.clone(),
                            cert: e.clone(),
                            q: *base_q - 1,
                        }
                    })
                    .collect(),
                base: Base::new(
                    self.blocks.clone(),
                    &self.k_columns.iter().map(Vec::as_slice).collect::<Vec<_>>(),
                    &self.padrow,
                    self.explicit,
                    Some(eq_table(&self.tau)),
                ),
            }
        }
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
        let block = |weight, gate, form| Block { weight, gate, form };
        vec![
            block(Weight::Omega, None, form(rng, true)),
            block(Weight::Omega, Some(2), form(rng, true)),
            block(Weight::Eq, None, form(rng, false)),
        ]
    }

    fn random_table(
        rng: &mut Rng,
        chunks: &Chunks,
        max_shift: usize,
        (log_rows, rows, explicit): (usize, usize, usize),
    ) -> Raw {
        let mut words = Vec::new();
        let mut coefs = Vec::new();
        for c in 0..3 {
            words.push(random_words(rng, chunks, 1 << log_rows, explicit));
            let coef = |rng: &mut Rng, a: usize| Coef {
                constant: rng.ext(),
                aux: (a < 2).then(|| (a, rng.ext())),
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
                            .map(|_| (1 + rng.next_u64() as usize % max_shift, rng.ext()))
                            .collect(),
                    })
                    .collect(),
                _ => Vec::new(),
            };
            // The third column has no coefficient on `act_F`, the first none on `ω_F`.
            let (omega, act) = match c {
                0 => (Coef::ZERO, coef(rng, c + 1)),
                2 => (coef(rng, c), Coef::ZERO),
                _ => (coef(rng, c), coef(rng, c + 1)),
            };
            coefs.push((omega, act, shifts, rng.ext_vec(chunks.d())));
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
        let omega = eq_table(&tau)[..rows].iter().map(|&e| theta * e).collect();
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

    /// Tables of different heights, the shortest finished first, and one of a single row: the rounds sum to the
    /// rows' summands, the row rounds end on the tables' ends at `χ`, and the column rounds on the summand at `q*`.
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
            (9, 12, vec![(5, 19, 25), (2, 0, 2)]),
            (1, 1, vec![(3, 6, 6), (1, 2, 2)]),
        ] {
            let chunks = Chunks::new(width);
            let d = chunks.d();
            let points = RowPoints::new(&chunks, &rng.ext_vec(width), max_shift);
            let raw: Vec<Raw> = (shapes.iter())
                .map(|&s| random_table(&mut rng, &chunks, max_shift, s))
                .collect();
            let n_columns = 3 * raw.len();
            let q_vars = n_columns.next_power_of_two().trailing_zeros() as usize;
            let mut q = 0;
            let tables: Vec<RowTable> = raw.iter().map(|t| t.row_table(&mut q)).collect();

            // Per row of a column: its coefficient, its coefficient per shift, and its certificate weights.
            let coefs_at = |t: &Raw, column: usize, om: F128, act: F128, aux: &dyn Fn(usize) -> F128| {
                let (co, ca, groups, cert) = &t.coefs[column];
                let weight = |c: &Coef| c.constant + c.aux.map_or(F128::ZERO, |(a, s)| s * aux(a));
                let mut shifts = vec![F128::ZERO; max_shift];
                for g in groups {
                    for &(s, mu) in &g.weights {
                        shifts[s - 1] += om * weight(&g.coef) * mu;
                    }
                }
                let certs: Vec<F128> = cert.iter().map(|&e| om * e).collect();
                (om * weight(co) + act * weight(ca), shifts, certs)
            };
            let mut total = F128::ZERO;
            for t in &raw {
                let eq = eq_table(&t.tau);
                for u in 0..1 << t.log_rows {
                    let (om, act) = (t.omega_at(u), t.act_at(u));
                    for column in 0..3 {
                        let (coef, shifts, certs) = coefs_at(t, column, om, act, &|a| t.aux_at(a, u));
                        let values = word_values(&chunks, &points, t.words[column][u]);
                        total += summand(d, &points.mirrors, coef, &shifts, &values, &certs);
                    }
                    total += t.base_at(om, eq[u], &|c| F128::from(t.k_columns[c][u]));
                }
            }

            let mut claim = total;
            let mut claims = Vec::new();
            let mut n_coeffs = Vec::new();
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
            assert_eq!(n_coeffs.len(), max_log + q_vars);
            assert!(n_coeffs[..max_log].iter().all(|&n| n == row_coeffs(d)));
            assert!(n_coeffs[max_log..].iter().all(|&n| n == column_coeffs(d)));

            // The end, from the rows' multilinear extensions at `χ`, then the columns' at `q*`.
            let chi = &end.point;
            let mut columns = Vec::new();
            let mut base = F128::ZERO;
            for (t, table_end) in raw.iter().zip(&end.tables) {
                let m = t.log_rows;
                let eqs = eq_table(&chi[..m]);
                let corner: F128 = chi[m..].iter().map(|&x| F128::ONE + x).product();
                let mle = |f: &dyn Fn(usize) -> F128| eqs.iter().enumerate().map(|(u, &e)| e * f(u)).sum::<F128>();
                let (om, act) = (mle(&|u| t.omega_at(u)), mle(&|u| t.act_at(u)));
                let aux: Vec<F128> = (0..2).map(|a| mle(&|u| t.aux_at(a, u))).collect();
                let k_values: Vec<F128> = (0..3).map(|c| mle(&|u| F128::from(t.k_columns[c][u]))).collect();
                let table_base = t.base_at(om, eq_eval(&t.tau, &chi[..m]), &|c| k_values[c]);
                assert_eq!(
                    (
                        table_end.omega,
                        table_end.act,
                        &table_end.aux,
                        table_end.corner,
                        table_end.base
                    ),
                    (om, act, &aux, corner, table_base)
                );
                base += corner * table_base;
                for column in 0..3 {
                    let slices: Vec<F128> = (0..64)
                        .map(|b| mle(&|u| F128::new(t.words[column][u] >> b & 1, 0)))
                        .collect();
                    let column_end = &table_end.columns[column];
                    assert_eq!(column_end.slices, slices);
                    assert_eq!(
                        column_end.values,
                        ColumnEnd::from_slices(&chunks, &points, slices).values
                    );
                    let (coef, shifts, certs) = coefs_at(t, column, om, act, &|a| aux[a]);
                    let scale = |v: Vec<F128>| v.into_iter().map(|v| corner * v).collect();
                    columns.push(ColumnAt {
                        coef: corner * coef,
                        shifts: scale(shifts),
                        values: column_end.values.clone(),
                        certs: scale(certs),
                    });
                }
            }
            let at_q = |c: &ColumnAt| summand(d, &points.mirrors, c.coef, &c.shifts, &c.values, &c.certs);
            let at_chi: F128 = columns.iter().map(at_q).sum();
            assert_eq!(claims[max_log], at_chi + base, "the row rounds end on the columns' sum");
            let eqq = eq_table(&end.column_point);
            let mle = |f: &dyn Fn(&ColumnAt) -> F128| columns.iter().zip(&eqq).map(|(c, &e)| e * f(c)).sum::<F128>();
            let folded = ColumnAt {
                coef: mle(&|c| c.coef),
                shifts: (0..max_shift).map(|s| mle(&|c| c.shifts[s])).collect(),
                values: (0..2 * d + max_shift).map(|k| mle(&|c| c.values[k])).collect(),
                certs: (0..d).map(|i| mle(&|c| c.certs[i])).collect(),
            };
            let eq0: F128 = end.column_point.iter().map(|&x| F128::ONE + x).product();
            assert_eq!(end.claim, at_q(&folded) + eq0 * base);
        }
    }
}
