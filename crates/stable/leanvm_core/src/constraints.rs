//! The tables' local constraints (§sec:air), proven by one sumcheck for all tables.
//!
//! Each table folds its identities with a DISJOINT range of one `ξ`'s powers, so
//! the batch is a polynomial in `ξ` whose coefficients are the individual sums and
//! matching the batch's target still pins each one. The bus forms, one per bus tree,
//! are the exception: they SHARE their powers across tables
//! ([`crate::cpu::xi_form_base`]), so those coefficients are per-tree totals and
//! the target pins the total, which is all the bus needs. The identities vanish on a
//! valid row, but a table also attaches its bus forms, whose sums are the
//! values the bus is owed, so the target is those rather than zero. It is
//! derived from the bus's leaf claims, never read off the stream.
//!
//! Tables of different heights are combined by back-loaded batching: table `t`'s
//! summand is lifted onto the common `n`-cube by `∏_{i ≥ τ_t} X_i`, which leaves
//! its hypercube sum alone. Rounds bind `X_{n-1}` first, so table `t` sits out the
//! first `n − τ_t` and joins at round `n − τ_t` weighted by the challenges it sat
//! out. Two payoffs: every table active in a round binds the same variable, so one
//! eq table serves the round; and the claims land on nested points `ρ[..τ_t]`.
//!
//! With nonzero sums the waiting tables stop dropping out: in a round it sits out, a
//! table's variable reaches its summand once, through the padding product, so its
//! contribution is degree 1 in that variable and vanishes at 0, and all of them
//! share the same challenge product. The round polynomial is the cubic
//! `eq(ζ_m, Y)·p(Y) + Y·u`. Its constant, quadratic and cubic coefficients are
//! sent; the running claim fixes the linear coefficient. The verifier evaluates
//! it at the challenge. Heights and `ζ` enter only the per-table `weights`, which
//! may be accumulated along the way or deferred to the end, as the recursion guest does.
//!
//! The eq point is the caller's, not a fresh one (the bus's GKR point `ζ`), which
//! is what lets the forms' sums settle the bus. Batching derived in `doc/leanvm/main.tex`
//! §sec:air. Both sides take `n = max τ_t` from the tables' heights; a recursive
//! verifier certifies that maximum with one hinted `g`-power (§recursion), so there
//! are no rounds in which no table has joined.

use crate::leaf::BusForm;
use crate::transcript::ProverState;
use crate::{load_e, load_k};
use primitives::field::{Acc8, F64, F64x8, F128, F128x8};
use primitives::multilinear::{eq_table, mle_eval, poly_eval, shrink_eq_high};

/// One table's involved columns' evaluations at its table-sumcheck point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub chi: Vec<F128>,
    pub evals: Vec<F128>,
}

/// One table's place in the shared batch.
pub struct Air<'a> {
    pub tau: usize,
    /// Its committed columns, `2^tau` values each, read in place.
    pub cols: &'a [&'a [F64]],
    /// Its summand, a degree-2 form over `cols`.
    pub form: BusForm,
    /// What the summand sums to against `eq(ζ, ·)`: prover-side only, for the line the table
    /// contributes while it waits. The verifier derives the total.
    pub sigma: F128,
}

/// Start of each table's disjoint range of `ξ`-powers.
pub fn xi_offsets(n_constraints: impl Iterator<Item = usize>) -> Vec<usize> {
    n_constraints
        .scan(0usize, |off, n| {
            let start = *off;
            *off += n;
            Some(start)
        })
        .collect()
}

/// Vectors of eight rows per parallel task of a round.
const CHUNK: usize = 1 << 7;

/// A linear form over a table's columns, as `(column, coefficient)` terms.
type Lin = Vec<(usize, F128)>;

/// A table's summand `P(v) = constant + lin(v) + Σ_g v[left_g]·right_g(v)`, its quadratic part `Q(v)` the last sum.
///
/// The `right_g` and `lin` are linear, so a joined table folds them as single `E` columns instead of folding every
/// column it reads: its state is `[lin, left_0, right_0, left_1, right_1, …]`.
struct Form {
    constant: F128,
    lin: Lin,
    /// The products grouped by their lesser column `left_g`, each pair once: a table's products share few columns
    /// (a flag, `fp`), so a group costs one product beside its linear `right_g`.
    groups: Vec<(usize, Lin)>,
}

impl Form {
    fn new(form: &BusForm) -> Self {
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

/// A joined table's state: per vector of eight rows, its [`Form::width`] columns side by side, `state[b·width + c]`.
/// Below eight rows one vector per column holds them all, zero past them.
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

fn add2(a: [F128; 2], b: [F128; 2]) -> [F128; 2] {
    [a[0] + b[0], a[1] + b[1]]
}

/// `Σ_b f(b)` over the vectors `0..blocks`, a chunk of them a task, reduced once per task.
fn sum_blocks(blocks: usize, f: impl Fn(usize, &mut [Acc8; 2]) + Sync) -> [F128; 2] {
    parallel::map_reduce(
        blocks.div_ceil(CHUNK),
        || [F128::ZERO; 2],
        |task| {
            let mut acc = [Acc8::ZERO; 2];
            for b in task * CHUNK..blocks.min((task + 1) * CHUNK) {
                f(b, &mut acc);
            }
            acc.map(Acc8::sum)
        },
        add2,
    )
}

/// The message of the round binding the variable of weight `half` of a table that has not joined, from its `K`
/// columns: `[Σ_i eqr[i]·P(end_i), Σ_i eqr[i]·Q(lo_i + hi_i)]`, `end` the upper rows when `at_one` and the lower ones
/// otherwise. `eqr` sums to one, so the form's constant is added once.
fn message_k(form: &Form, cols: &[&[F64]], eqr: &[F128], half: usize, at_one: bool) -> [F128; 2] {
    let lin = splat(&form.lin);
    let rights: Vec<_> = form.groups.iter().map(|(_, right)| splat(right)).collect();
    let [endpoint, slope] = sum_blocks(half.div_ceil(8), |b, acc| {
        let (i, n) = (8 * b, (half - 8 * b).min(8));
        let lo = |c: usize| load_k(cols[c], i, n);
        let hi = |c: usize| load_k(cols[c], i + half, n);
        let end = |c: usize| if at_one { hi(c) } else { lo(c) };
        let sum = |c: usize| lo(c) + hi(c);
        let (mut endpoint, mut slope) = (dot(&lin, end), Acc8::ZERO);
        for ((left, _), right) in form.groups.iter().zip(&rights) {
            endpoint += dot(right, end).reduce().mul_base_unreduced(end(*left));
            slope += dot(right, sum).reduce().mul_base_unreduced(sum(*left));
        }
        let eq = load_e(eqr, i, n);
        acc[0] += endpoint.reduce().mul_unreduced(eq);
        acc[1] += slope.reduce().mul_unreduced(eq);
    });
    [endpoint + form.constant, slope]
}

/// One vector of rows' terms of a joined table's message, its lower and upper rows `lo` and `hi`.
#[inline(always)]
fn add_state_message(lo: &[F128x8], hi: &[F128x8], eq: F128x8, at_one: bool, acc: &mut [Acc8; 2]) {
    let end = if at_one { hi } else { lo };
    let (mut endpoint, mut slope) = (Acc8::ZERO, Acc8::ZERO);
    for g in (1..lo.len()).step_by(2) {
        endpoint += end[g].mul_unreduced(end[g + 1]);
        slope += (lo[g] + hi[g]).mul_unreduced(lo[g + 1] + hi[g + 1]);
    }
    acc[0] += (endpoint.reduce() + end[0]).mul_unreduced(eq);
    acc[1] += slope.reduce().mul_unreduced(eq);
}

/// Lanes `shift..shift + n` of `v` moved down to `0..n`, zero past them.
fn shifted(v: F128x8, shift: usize, n: usize) -> F128x8 {
    let v = v.to_array();
    F128x8::from_array(&std::array::from_fn(|p| if p < n { v[p + shift] } else { F128::ZERO }))
}

/// The message of the round binding the variable of weight `half` of a joined table, from its state.
fn message_e(form: &Form, state: &State, eqr: &[F128], half: usize, at_one: bool) -> [F128; 2] {
    let width = form.width();
    let [endpoint, slope] = if half < 8 {
        let lo: Vec<F128x8> = state.iter().map(|&v| shifted(v, 0, half)).collect();
        let hi: Vec<F128x8> = state.iter().map(|&v| shifted(v, half, half)).collect();
        let mut acc = [Acc8::ZERO; 2];
        add_state_message(&lo, &hi, load_e(eqr, 0, half), at_one, &mut acc);
        acc.map(Acc8::sum)
    } else {
        let (lows, highs) = state.split_at(half / 8 * width);
        sum_blocks(half / 8, |b, acc| {
            let rows = b * width..(b + 1) * width;
            add_state_message(&lows[rows.clone()], &highs[rows], load_e(eqr, 8 * b, 8), at_one, acc);
        })
    };
    [endpoint + form.constant, slope]
}

/// The round a table joins, after its challenge `r`: the state `lo + r·(lo + hi)` of every entry, built straight
/// from the `K` columns. By linearity `lin` and `right_g` take the terms `w·lo + (w·r)·(lo + hi)`, so no row pays an
/// `E x E` product.
fn join(form: &Form, cols: &[&[F64]], r: F128, half: usize) -> State {
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
    let blocks = half.div_ceil(8);
    let mut state = parallel::filled(blocks * width, F128x8::ZERO);
    parallel::chunks_mut(&mut state, CHUNK * width, |task, out| {
        for (b, out) in (task * CHUNK..).zip(out.chunks_exact_mut(width)) {
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
    parallel::chunks_mut(lows, CHUNK, |task, lows| {
        for (lo, &hi) in lows.iter_mut().zip(&highs[task * CHUNK..]) {
            *lo += r * (*lo + hi);
        }
    });
    state.truncate(n);
}

/// One table of the batch, and what the rounds have made of it.
struct Table<'a> {
    tau: usize,
    sigma: F128,
    /// Its summand's factor: the challenges it sat out, then the eq factors of the rounds it was active.
    weight: F128,
    form: Form,
    cols: &'a [&'a [F64]],
    /// Its folded state, once the table has joined.
    state: Option<State>,
}

impl Table<'_> {
    /// The message of the round that binds variable `m`, while the table is active.
    fn message(&self, eqr: &[F128], m: usize, at_one: bool) -> [F128; 2] {
        match &self.state {
            Some(state) => message_e(&self.form, state, eqr, 1 << m, at_one),
            None => message_k(&self.form, self.cols, eqr, 1 << m, at_one),
        }
    }

    /// Binds variable `m` to `r`: the join of a table that has not joined, the fold of one that has.
    fn bind(&mut self, r: F128, m: usize) {
        match &mut self.state {
            Some(state) => fold_state(state, r, 1 << m),
            None => self.state = Some(join(&self.form, self.cols, r, 1 << m)),
        }
    }
}

fn round_polynomial([endpoint, quadratic]: [F128; 2], zeta: F128, claim: F128, waiting: F128) -> [F128; 4] {
    let eq_z = F128::ONE + zeta;
    // claim = (1 + zeta) p(0) + zeta p(1) + waiting.
    let (p0, p1) = if zeta.is_zero() {
        (claim + waiting, endpoint)
    } else {
        (endpoint, (claim + waiting + eq_z * endpoint) * zeta.inv())
    };
    let h2 = eq_z * quadratic + p0 + p1 + quadratic;
    [eq_z * p0, claim + h2 + quadratic, h2, quadratic]
}

/// Prove that every table's batched constraint vanishes on all of its rows, as ONE
/// sumcheck over `max τ_t` variables. Returns the per-table claims, in input order, on the
/// nested points `ρ[..τ_t]`.
pub fn prove(airs: &[Air<'_>], zeta: &[F128], ps: &mut ProverState) -> Vec<Claims> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    let mut tables: Vec<Table> = airs
        .iter()
        .map(|air| Table {
            tau: air.tau,
            sigma: air.sigma,
            weight: F128::ONE,
            form: Form::new(&air.form),
            cols: air.cols,
            state: None,
        })
        .collect();
    // ONE eq table over the low (still free) variables serves every active table.
    let mut eqr = eq_table(&zeta[..n.saturating_sub(1)]);
    let mut chi = vec![F128::ZERO; n];
    // `k`, the challenges drawn so far, common to every table that is still waiting.
    let mut k = F128::ONE;
    let mut claim = airs.iter().map(|a| a.sigma).sum();
    for j in 0..n {
        let m = n - 1 - j; // the variable this round binds
        let at_one = zeta[m].is_zero();
        // The waiting tables contribute the line `Y·k·Σσ`, whose slope `u` is all there
        // is to it. It is NOT sent on its own: it folds into `h` below, and only `h`
        // travels. `msg` is the active tables' degree-2 cofactor, `h`'s multiplicand.
        let waiting = tables.iter().filter(|t| t.tau <= m).map(|t| t.sigma).sum();
        let u = k * waiting;
        let mut msg = [F128::ZERO; 2];
        for t in tables.iter_mut().filter(|t| t.tau > m) {
            let p = t.message(&eqr, m, at_one);
            msg[0] += t.weight * p[0];
            msg[1] += t.weight * p[1];
        }
        shrink_eq_high(&mut eqr);
        // The running claim recovers the missing endpoint of the quadratic cofactor.
        // The fold stays separate: its challenge only exists after this message is bound.
        let h = round_polynomial(msg, zeta[m], claim, u);
        ps.add_round_poly(&h, false);
        let rk = ps.sample();
        claim = poly_eval(&h, rk);
        chi[m] = rk;
        k *= rk;
        let eq_k = F128::ONE + zeta[m] + rk;
        for t in &mut tables {
            if t.tau > m {
                t.weight *= eq_k;
                t.bind(rk, m);
            } else {
                t.weight *= rk;
            }
        }
    }

    // Each column's evaluation at its table's point, one task per column: the columns were never folded.
    crate::stage!("Constraint evals", || {
        tables
            .iter()
            .map(|t| {
                let chi = &chi[..t.tau];
                let evals = parallel::map_collect(t.cols.len(), |c| mle_eval(t.cols[c], chi));
                ps.add_scalars(&evals);
                Claims {
                    chi: chi.to_vec(),
                    evals,
                }
            })
            .collect()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::interp;

    const COLS: usize = 6;

    /// Products sharing column 0, one of them named twice and either way round, a square, linear
    /// terms and a constant.
    fn synth(pows: &[F128]) -> BusForm {
        let mut form = BusForm::new(COLS);
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

    fn splitmix(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn random_e(state: &mut u64) -> F128 {
        F128::new(splitmix(state), splitmix(state))
    }

    fn random_columns(state: &mut u64, rows: usize) -> Vec<Vec<F64>> {
        (0..COLS)
            .map(|_| (0..rows).map(|_| F64(splitmix(state))).collect())
            .collect()
    }

    #[test]
    fn products_are_merged_into_groups() {
        let mut s = 1;
        let pows: Vec<F128> = (0..3).map(|_| random_e(&mut s)).collect();
        let form = Form::new(&synth(&pows));
        let pairs: Vec<(usize, usize)> = form
            .groups
            .iter()
            .flat_map(|(a, r)| r.iter().map(|&(b, _)| (*a, b)))
            .collect();
        assert_eq!(
            pairs,
            [(0, 1), (0, 3), (0, 4), (5, 5)],
            "the pair named twice, either way round, is one product"
        );
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
        let mut s = 7;
        let pows: Vec<F128> = (0..3).map(|_| random_e(&mut s)).collect();
        for m in [1usize, 3, 4, 11] {
            let kcols = random_columns(&mut s, 2 << m);
            let views: Vec<&[F64]> = kcols.iter().map(|c| &c[..]).collect();
            let mut naive_cols: Vec<Vec<F128>> = kcols
                .iter()
                .map(|c| c.iter().map(|&x| F128::from(x)).collect())
                .collect();
            let mut table = Table {
                tau: m + 1,
                sigma: F128::ZERO,
                weight: F128::ONE,
                form: Form::new(&synth(&pows)),
                cols: &views,
                state: None,
            };
            let mut eqr = eq_table(&(0..m).map(|_| random_e(&mut s)).collect::<Vec<_>>());
            for var in (0..=m).rev() {
                let half = 1 << var;
                for at_one in [false, true] {
                    assert_eq!(
                        table.message(&eqr, var, at_one),
                        naive_message(&pows, &naive_cols, &eqr, half, at_one),
                        "m {m} half {half}"
                    );
                }
                let r = random_e(&mut s);
                shrink_eq_high(&mut eqr);
                table.bind(r, var);
                for c in &mut naive_cols {
                    *c = (0..half).map(|i| interp(c[i], c[i + half], r)).collect();
                }
            }
        }
    }
}
