//! The table sumcheck (§sec:air): one sumcheck over every table, for its identities and its share of each bus tree.
//!
//! Table `j`'s summand is one degree-two [`Form`] over its columns: its identities `C_{j,i}`, each weighted by its own
//! power of `ξ`, plus each tree's bus form `B^s_j` (from [`crate::leaf`]), weighted by the tree's power, which every
//! table shares. Against `eq(ζ_{<τ_j}, ·)` the identities sum to zero and the bus forms to what the tables owe each
//! tree, which the verifier derives from the GKR's leaf claims: the batch's claim is never sent.
//!
//! The tables share one cube of `τ_max` variables, table `j` lifted by `∏_{k ≥ τ_j} X_k`, which sums to one over the
//! variables it does not use. Rounds bind `X_{τ_max - 1}` first, so table `j` waits `τ_max - τ_j` rounds before it
//! joins ("back-loaded"). Binding `X_m` to `Y`, a waiting table adds `Y·k·σ_j` (`k` the challenges so far, `σ_j` its
//! sum) and a joined one `eq(ζ_m, Y)·p_j(Y)`, its summand's restriction, of degree two. The round polynomial is the
//! cubic `h(Y) = Σ_j (…)`: the claim fixes its linear coefficient and the other three travel. Each table's columns end
//! on the nested point `χ_{<τ_j}`. The prover takes `σ_j` from the first round table `j` is active in, which reads no
//! challenge: `eq` factors, so `σ_j = (1 + ζ_m)·p_j(0) + ζ_m·p_j(1)` at `m = τ_j - 1`.
//!
//! A table's rows are read from its `K` columns until it joins. From then on it is held as its summand's few linear
//! parts, folded as `E` columns (`Grouped`), rather than as its columns folded one by one.

use crate::{load_e, load_k};
use primitives::field::{Acc8, F64, F64x8, F128, F128x8};
use primitives::multilinear::{eq_table, poly_eval, shrink_eq_high};
use primitives::transcript::ProverState;

/// A degree-two form over one table's columns: `constant + Σ_c coeffs[c]·col_c + Σ q·col_a·col_b` over `prods`.
#[derive(Clone, Debug)]
pub struct Form {
    pub coeffs: Vec<F128>,
    /// `(a, b, q)`, in the table's local column indices.
    pub(crate) prods: Vec<(usize, usize, F128)>,
    pub constant: F128,
}

impl Form {
    /// The zero form over `n_cols` columns.
    pub(crate) fn new(n_cols: usize) -> Self {
        Self {
            coeffs: vec![F128::ZERO; n_cols],
            prods: Vec::new(),
            constant: F128::ZERO,
        }
    }

    /// The form scaled by `w`.
    pub fn scaled(&self, w: F128) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(|&c| c * w).collect(),
            prods: self.prods.iter().map(|&(a, b, q)| (a, b, q * w)).collect(),
            constant: self.constant * w,
        }
    }

    /// The sum of forms over the same columns, their products listed together.
    pub fn sum(forms: impl IntoIterator<Item = Self>) -> Self {
        let mut forms = forms.into_iter();
        let mut out = forms.next().expect("a table has at least one form");
        for form in forms {
            assert_eq!(out.coeffs.len(), form.coeffs.len(), "forms over the same columns");
            for (slot, c) in out.coeffs.iter_mut().zip(form.coeffs) {
                *slot += c;
            }
            out.constant += form.constant;
            out.prods.extend(form.prods);
        }
        out
    }

    /// `constant + Σ coeffs[c]·evals[c]`.
    #[cfg(test)]
    fn linear(&self, evals: &[F128]) -> F128 {
        self.coeffs
            .iter()
            .zip(evals)
            .fold(self.constant, |acc, (&w, &v)| acc + w * v)
    }

    /// The form at one row, `evals` the columns' values there; only its degree-two terms when `quadratic`.
    #[cfg(test)]
    pub(crate) fn eval(&self, evals: &[F128], quadratic: bool) -> F128 {
        let linear = if quadratic { F128::ZERO } else { self.linear(evals) };
        self.prods
            .iter()
            .fold(linear, |acc, &(a, b, q)| acc + evals[a] * evals[b] * q)
    }
}

/// One table's columns' evaluations at the sumcheck's point `χ_{<τ_j}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Claims {
    pub chi: Vec<F128>,
    pub evals: Vec<F128>,
}

/// One table in the batch.
pub(crate) struct Air<'a> {
    pub tau: usize,
    /// Its committed columns, `2^tau` values each, read in place.
    pub cols: &'a [&'a [F64]],
    /// Its summand.
    pub form: Form,
}

/// Where each table's range of `ξ`-powers starts, given each one's identity count.
pub fn xi_offsets(n_constraints: impl Iterator<Item = usize>) -> Vec<usize> {
    n_constraints
        .scan(0usize, |off, n| {
            let start = *off;
            *off += n;
            Some(start)
        })
        .collect()
}

/// Prove what every table's summand sums to against `eq(ζ_{<τ}, ·)`, as one sumcheck over `τ_max` variables, the `eq`
/// point `zeta` (the bus GKR's `ζ`). Returns each table's column claims, in input order.
pub(crate) fn prove(airs: &[Air<'_>], zeta: &[F128], ps: &mut ProverState) -> Vec<Claims> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    let mut tables: Vec<Table> = airs
        .iter()
        .map(|air| Table {
            tau: air.tau,
            weight: F128::ONE,
            form: Grouped::new(&air.form),
            cols: air.cols,
            state: None,
        })
        .collect();
    // One eq table over the variables still free serves every joined table.
    let mut eqr = eq_table(&zeta[..n.saturating_sub(1)]);
    let mut chi = vec![F128::ZERO; n];
    // `claim` and the waiting tables' slope `u = k·Σσ` start at zero, not at the target `Σσ` over every table: both
    // then sit `k·target` off, and only `claim + u` reaches a sent coefficient (the linear one is not sent), so the
    // offset cancels. A joining table's `σ` leaves `u`.
    let (mut claim, mut u) = (F128::ZERO, F128::ZERO);
    for m in (0..n).rev() {
        // The joined tables' `p(Y)`: an endpoint and its quadratic coefficient.
        let mut p = [F128::ZERO; 2];
        for t in tables.iter().filter(|t| t.tau > m) {
            let [end, quadratic] = t.message(&eqr, m, zeta[m], &mut u);
            p = [p[0] + t.weight * end, p[1] + t.weight * quadratic];
        }
        shrink_eq_high(&mut eqr);
        let h = round_polynomial(p, zeta[m], claim, u);
        ps.add_round_poly(&h, false);
        let r = ps.sample();
        claim = poly_eval(&h, r);
        u *= r;
        chi[m] = r;
        for t in &mut tables {
            if t.tau > m {
                t.weight *= F128::ONE + zeta[m] + r;
                t.bind(r, m);
            } else {
                t.weight *= r;
            }
        }
    }

    // Every column at its table's point, a table's in one pass: the columns themselves were never folded.
    crate::stage!("Constraint evals", || {
        tables
            .iter()
            .map(|t| {
                let chi = &chi[..t.tau];
                let columns: Vec<_> = t.cols.iter().map(|&c| (c, None)).collect();
                let evals = crate::eq::eq_sums(chi, &columns);
                ps.add_scalars(&evals);
                Claims {
                    chi: chi.to_vec(),
                    evals,
                }
            })
            .collect()
    })
}

/// The round polynomial `h(Y) = eq(ζ, Y)·p(Y) + Y·u`, `eq(ζ, Y) = 1 + ζ + Y`, from `p`'s endpoint at `0` (at `1`
/// when `ζ = 0`) and its quadratic coefficient: the claim `h(0) + h(1) = (1 + ζ)·p(0) + ζ·p(1) + u` gives the other.
fn round_polynomial([end, quadratic]: [F128; 2], zeta: F128, claim: F128, u: F128) -> [F128; 4] {
    let eq0 = F128::ONE + zeta;
    let (p0, p1) = if zeta.is_zero() {
        (claim + u, end)
    } else {
        (end, (claim + u + eq0 * end) * zeta.inv())
    };
    // `p(Y) = p0 + (p0 + p1 + quadratic)·Y + quadratic·Y²`, and `h1 = claim + h2 + h3`.
    let h2 = eq0 * quadratic + p0 + p1 + quadratic;
    [eq0 * p0, claim + h2 + quadratic, h2, quadratic]
}

/// One table of the batch, and what the rounds have made of it.
struct Table<'a> {
    tau: usize,
    /// Its factor in `F`: the challenges it waited, then `eq(ζ_m, χ_m)` of each round since it joined.
    weight: F128,
    form: Grouped,
    cols: &'a [&'a [F64]],
    /// Its folded state, once the table has joined.
    state: Option<State>,
}

impl Table<'_> {
    /// `[Σ_i eqr[i]·P(end_i), Σ_i eqr[i]·Q(lo_i + hi_i)]` for the round binding variable `m` (of weight `half`): `P`
    /// the summand, `Q` its quadratic part, `lo` and `hi` the rows `i` and `i + half`, `end` the upper ones when
    /// `ζ_m = 0`. `eqr` sums to one, so the form's constant is added once. The first, from both endpoints, adds the
    /// table's `weight·σ` to `u`.
    fn message(&self, eqr: &[F128], m: usize, zeta: F128, u: &mut F128) -> [F128; 2] {
        let c = self.form.constant;
        let Some(state) = &self.state else {
            let [p0, p1, quadratic] = message_waiting(&self.form, self.cols, eqr, 1 << m);
            let (p0, p1) = (p0 + c, p1 + c);
            *u += self.weight * ((F128::ONE + zeta) * p0 + zeta * p1);
            return [if zeta.is_zero() { p1 } else { p0 }, quadratic];
        };
        let [end, quadratic] = message_joined(&self.form, state, eqr, 1 << m, zeta.is_zero());
        [end + c, quadratic]
    }

    /// Bind variable `m` to `r`: the join of a table that has not joined, the fold of one that has.
    fn bind(&mut self, r: F128, m: usize) {
        match &mut self.state {
            Some(state) => fold_state(state, r, 1 << m),
            None => self.state = Some(join(&self.form, self.cols, r, 1 << m)),
        }
    }
}

/// A linear form over a table's columns, as `(column, coefficient)` terms.
type Lin = Vec<(usize, F128)>;

/// A [`Form`] as the rounds read it: `P(v) = constant + lin(v) + Σ_g v[left_g]·right_g(v)`.
///
/// The `right_g` and `lin` are linear, so a joined table folds them as single `E` columns instead of folding every
/// column it reads: its [`State`] is `[lin, left_0, right_0, left_1, right_1, …]`.
struct Grouped {
    constant: F128,
    lin: Lin,
    /// The products grouped by their lesser column `left_g`, each pair once: a table's products share few columns
    /// (a flag, `fp`), so a group costs one product beside its linear `right_g`.
    groups: Vec<(usize, Lin)>,
}

impl Grouped {
    fn new(form: &Form) -> Self {
        let lin: Lin = form
            .coeffs
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, c)| !c.is_zero())
            .collect();
        let mut pairs: Vec<(usize, usize, F128)> =
            form.prods.iter().map(|&(a, b, q)| (a.min(b), a.max(b), q)).collect();
        pairs.sort_unstable_by_key(|&(a, b, _)| (a, b));
        let mut groups: Vec<(usize, Lin)> = Vec::new();
        for (a, b, q) in pairs {
            match groups.last_mut() {
                Some((left, right)) if *left == a => match right.last_mut() {
                    Some(last) if last.0 == b => last.1 += q,
                    _ => right.push((b, q)),
                },
                _ => groups.push((a, vec![(b, q)])),
            }
        }
        Self {
            constant: form.constant,
            lin,
            groups,
        }
    }

    /// Columns of the joined state.
    fn width(&self) -> usize {
        1 + 2 * self.groups.len()
    }
}

/// A joined table's state: per vector of eight rows, its [`Grouped::width`] columns side by side,
/// `state[b·width + c]`. Below eight rows one vector per column holds them all, zero past them.
type State = Vec<F128x8>;

/// `Σ_terms w·v(c)`, unreduced.
#[inline(always)]
fn dot(terms: &[(usize, F128x8)], v: impl Fn(usize) -> F64x8) -> Acc8 {
    terms
        .iter()
        .fold(Acc8::ZERO, |acc, &(c, w)| acc + w.mul_base_unreduced(v(c)))
}

fn splat(terms: &Lin) -> Vec<(usize, F128x8)> {
    terms.iter().map(|&(c, w)| (c, F128x8::splat(w))).collect()
}

/// `Σ_b f(b)` over the vectors of eight rows `0..vectors`, reduced once per task.
fn sum_vectors<const N: usize>(vectors: usize, f: impl Fn(usize, &mut [Acc8; N]) + Sync) -> [F128; N] {
    let chunk = crate::chunk(vectors);
    parallel::map_reduce(
        vectors.div_ceil(chunk),
        || [F128::ZERO; N],
        |task| {
            let mut acc = [Acc8::ZERO; N];
            for b in task * chunk..vectors.min((task + 1) * chunk) {
                f(b, &mut acc);
            }
            acc.map(Acc8::sum)
        },
        |a, b| std::array::from_fn(|k| a[k] + b[k]),
    )
}

/// The message of a table that has not joined, from its `K` columns, less the constant, with both endpoints:
/// `[Σ_i eqr[i]·P(lo_i), Σ_i eqr[i]·P(hi_i), Σ_i eqr[i]·Q(lo_i + hi_i)]`.
fn message_waiting(form: &Grouped, cols: &[&[F64]], eqr: &[F128], half: usize) -> [F128; 3] {
    let lin = splat(&form.lin);
    let rights: Vec<_> = form.groups.iter().map(|(_, right)| splat(right)).collect();
    sum_vectors(half.div_ceil(8), |b, acc| {
        let (i, n) = (8 * b, (half - 8 * b).min(8));
        let lo = |c: usize| load_k(cols[c], i, n);
        let hi = |c: usize| load_k(cols[c], i + half, n);
        let sum = |c: usize| lo(c) + hi(c);
        let (mut at_zero, mut at_one, mut quadratic) = (dot(&lin, lo), dot(&lin, hi), Acc8::ZERO);
        for ((left, _), right) in form.groups.iter().zip(&rights) {
            at_zero += dot(right, lo).reduce().mul_base_unreduced(lo(*left));
            at_one += dot(right, hi).reduce().mul_base_unreduced(hi(*left));
            quadratic += dot(right, sum).reduce().mul_base_unreduced(sum(*left));
        }
        let eq = load_e(eqr, i, n);
        acc[0] += at_zero.reduce().mul_unreduced(eq);
        acc[1] += at_one.reduce().mul_unreduced(eq);
        acc[2] += quadratic.reduce().mul_unreduced(eq);
    })
}

/// [`Table::message`] of a joined table, from its state, less the constant.
fn message_joined(form: &Grouped, state: &State, eqr: &[F128], half: usize, at_one: bool) -> [F128; 2] {
    let width = form.width();
    if half < 8 {
        let lo: Vec<F128x8> = state.iter().map(|&v| shifted(v, 0, half)).collect();
        let hi: Vec<F128x8> = state.iter().map(|&v| shifted(v, half, half)).collect();
        let mut acc = [Acc8::ZERO; 2];
        add_state_message(&lo, &hi, load_e(eqr, 0, half), at_one, &mut acc);
        return acc.map(Acc8::sum);
    }
    let (lows, highs) = state.split_at(half / 8 * width);
    sum_vectors(half / 8, |b, acc| {
        let rows = b * width..(b + 1) * width;
        add_state_message(&lows[rows.clone()], &highs[rows], load_e(eqr, 8 * b, 8), at_one, acc);
    })
}

/// One vector of rows' terms of a joined table's message, its lower and upper rows `lo` and `hi`.
#[inline(always)]
fn add_state_message(lo: &[F128x8], hi: &[F128x8], eq: F128x8, at_one: bool, acc: &mut [Acc8; 2]) {
    let end = if at_one { hi } else { lo };
    let (mut end_value, mut quadratic) = (Acc8::ZERO, Acc8::ZERO);
    for g in (1..lo.len()).step_by(2) {
        end_value += end[g].mul_unreduced(end[g + 1]);
        quadratic += (lo[g] + hi[g]).mul_unreduced(lo[g + 1] + hi[g + 1]);
    }
    acc[0] += (end_value.reduce() + end[0]).mul_unreduced(eq);
    acc[1] += quadratic.reduce().mul_unreduced(eq);
}

/// Lanes `shift..shift + n` of `v` moved down to `0..n`, zero past them.
fn shifted(v: F128x8, shift: usize, n: usize) -> F128x8 {
    let v = v.to_array();
    F128x8::from_array(&std::array::from_fn(|p| if p < n { v[p + shift] } else { F128::ZERO }))
}

/// The state of a table joining in the round binding the variable of weight `half` to `r`: `lo + r·(lo + hi)` of
/// every state column, built straight from the `K` columns. By linearity `lin` and `right_g` take the terms
/// `w·lo + (w·r)·(lo + hi)`, so no row pays an `E x E` product.
fn join(form: &Grouped, cols: &[&[F64]], r: F128, half: usize) -> State {
    let width = form.width();
    let pair = |terms: &Lin| -> Vec<_> {
        terms
            .iter()
            .map(|&(c, w)| (c, F128x8::splat(w), F128x8::splat(w * r)))
            .collect()
    };
    let lin = pair(&form.lin);
    let rights: Vec<_> = form.groups.iter().map(|(_, right)| pair(right)).collect();
    let r = F128x8::splat(r);
    let vectors = half.div_ceil(8);
    let mut state = crate::filled(vectors * width, F128x8::ZERO);
    let chunk = crate::chunk(vectors);
    parallel::chunks_mut(&mut state, chunk * width, |task, out| {
        for (b, out) in (task * chunk..).zip(out.chunks_exact_mut(width)) {
            let (i, n) = (8 * b, (half - 8 * b).min(8));
            let lo = |c: usize| load_k(cols[c], i, n);
            let sum = |c: usize| lo(c) + load_k(cols[c], i + half, n);
            let dot = |terms: &[(usize, F128x8, F128x8)]| {
                terms
                    .iter()
                    .fold(Acc8::ZERO, |acc, &(c, w, wr)| {
                        acc + w.mul_base_unreduced(lo(c)) + wr.mul_base_unreduced(sum(c))
                    })
                    .reduce()
            };
            out[0] = dot(&lin);
            for (g, ((left, _), right)) in form.groups.iter().zip(&rights).enumerate() {
                let lifted = F128x8::from_array(&lo(*left).to_array().map(F128::from));
                out[1 + 2 * g] = lifted + r.mul_base(sum(*left));
                out[2 + 2 * g] = dot(right);
            }
        }
    });
    state
}

/// The state folded by `r`: row `i` becomes `lo + r·(lo + hi)` of rows `i` and `i + half` in every column, the upper
/// half dropped.
fn fold_state(state: &mut State, r: F128, half: usize) {
    if half < 8 {
        for v in state.iter_mut() {
            let (lo, hi) = (shifted(*v, 0, half), shifted(*v, half, half));
            *v = lo + F128x8::splat(r) * (lo + hi);
        }
        return;
    }
    let r = F128x8::splat(r);
    let n = state.len() / 2;
    let (lows, highs) = state.split_at_mut(n);
    let chunk = crate::chunk(n);
    parallel::chunks_mut(lows, chunk, |task, lows| {
        for (lo, &hi) in lows.iter_mut().zip(&highs[task * chunk..]) {
            *lo += r * (*lo + hi);
        }
    });
    state.truncate(n);
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::interp;
    use primitives::test_rng::Rng;

    const COLS: usize = 6;

    /// Products sharing column 0, one of them named twice and either way round, a square, linear
    /// terms and a constant.
    fn synth(pows: &[F128]) -> Form {
        let mut form = Form::new(COLS);
        form.constant = F128::ONE;
        (form.coeffs[2], form.coeffs[1], form.coeffs[4]) = (pows[0], pows[1], pows[2]);
        form.prods = vec![
            (0, 1, pows[0]),
            (3, 0, pows[1]),
            (0, 4, pows[1]),
            (5, 5, pows[2]),
            (1, 0, pows[2]),
        ];
        form
    }

    fn random_columns(rng: &mut Rng, rows: usize) -> Vec<Vec<F64>> {
        (0..COLS)
            .map(|_| (0..rows).map(|_| F64(rng.next_u64())).collect())
            .collect()
    }

    /// `[Σ eqr·P(end), Σ eqr·Q(lo + hi)]` by evaluating the summand row by row.
    fn naive_message(pows: &[F128], cols: &[Vec<F128>], eqr: &[F128], half: usize, at_one: bool) -> [F128; 2] {
        (0..half).fold([F128::ZERO; 2], |acc, i| {
            let row = |off: usize| -> Vec<F128> { cols.iter().map(|c| c[i + off]).collect() };
            let (lo, hi) = (row(0), row(half));
            let sum: Vec<F128> = lo.iter().zip(&hi).map(|(&a, &b)| a + b).collect();
            let end = if at_one { &hi } else { &lo };
            [
                acc[0] + eqr[i] * synth(pows).eval(end, false),
                acc[1] + eqr[i] * synth(pows).eval(&sum, true),
            ]
        })
    }

    /// Every round of a table's life, from its `K` columns and then from its folded state, against the naive
    /// formulas.
    #[test]
    fn round_messages_match_naive_evaluation() {
        let mut rng = Rng::new(7);
        let pows = rng.ext_vec(3);
        for m in [1usize, 3, 4, 11] {
            let kcols = random_columns(&mut rng, 2 << m);
            let views: Vec<&[F64]> = kcols.iter().map(|c| &c[..]).collect();
            let mut naive_cols: Vec<Vec<F128>> = kcols
                .iter()
                .map(|c| c.iter().map(|&x| F128::from(x)).collect())
                .collect();
            let mut table = Table {
                tau: m + 1,
                weight: F128::ONE,
                form: Grouped::new(&synth(&pows)),
                cols: &views,
                state: None,
            };
            let mut eqr = eq_table(&rng.ext_vec(m));
            for var in (0..=m).rev() {
                let half = 1 << var;
                let naive = [false, true].map(|at_one| naive_message(&pows, &naive_cols, &eqr, half, at_one));
                // The first message also adds `σ = (1 + ζ)·p(0) + ζ·p(1)`, affine in `ζ`, so its ends pin it.
                let first = table.state.is_none();
                for (zeta, at_one) in [(F128::ONE, false), (F128::ZERO, true)] {
                    let mut u = F128::ZERO;
                    let message = table.message(&eqr, var, zeta, &mut u);
                    assert_eq!(message, naive[usize::from(at_one)], "m {m} half {half}");
                    let sigma = if first {
                        naive[usize::from(!at_one)][0]
                    } else {
                        F128::ZERO
                    };
                    assert_eq!(u, sigma, "m {m} half {half}");
                }
                let r = rng.ext();
                shrink_eq_high(&mut eqr);
                table.bind(r, var);
                for c in &mut naive_cols {
                    *c = (0..half).map(|i| interp(c[i], c[i + half], r)).collect();
                }
            }
        }
    }
}
