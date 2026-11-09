//! The tables' local constraints (§sec:air), proven by one sumcheck for all tables.
//!
//! Each table folds its identities with a DISJOINT range of one `ξ`'s powers, so
//! the batch is a polynomial in `ξ` whose coefficients are the individual sums and
//! matching the batch's target still pins each one. The three bus forms are the
//! exception: they SHARE their three powers across tables
//! ([`crate::cpu::xi_form_base`]), so those coefficients are per-side totals and
//! the target pins the total, which is all the bus needs. The identities vanish on a
//! valid row, but a table also attaches its three bus forms, whose sums are the
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
use primitives::field::{F64, F64x8, F192, F192x8, Prod8};
use primitives::multilinear::{eq_table, interp, mle_eval, poly_eval, shrink_eq_high};

/// One table's involved columns' evaluations at its table-sumcheck point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub chi: Vec<F192>,
    pub evals: Vec<F192>,
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
    pub sigma: F192,
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

/// A linear form over a table's columns, as `(column, coefficient)` terms.
type Lin = Vec<(usize, F192)>;

/// Blocks of eight rows per task of the round passes.
const TASK_BLOCKS: usize = 128;

/// Vectors per task of a fold.
const FOLD_CHUNK: usize = 1 << 10;

/// A table's summand `P(v) = constant + lin(v) + Σ_g v[left_g] · right_g(v)`, its products grouped
/// by a shared column. Its homogeneous quadratic part is `Q(v) = Σ_g v[left_g] · right_g(v)`.
///
/// The `right_g` and `lin` are linear, so an active table folds them as single `E` columns
/// instead of folding every column: its state is `[lin, left_0, right_0, left_1, right_1, ..]`.
struct Form {
    constant: F192,
    lin: Lin,
    groups: Vec<(usize, Lin)>,
    /// Every column a term reads, ascending.
    used: Vec<usize>,
}

impl Form {
    /// The summand of `form`, its products grouped by a greedy vertex cover: the column with the most
    /// remaining products becomes a group's left factor.
    fn new(form: &BusForm) -> Self {
        let lin: Lin = form
            .coeffs
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, c)| !c.is_zero())
            .collect();
        let mut edges: Vec<(usize, usize, F192)> = Vec::new();
        for &(a, b, q) in &form.prods {
            let (a, b) = (a.min(b), a.max(b));
            match edges.iter_mut().find(|e| (e.0, e.1) == (a, b)) {
                Some(e) => e.2 += q,
                None => edges.push((a, b, q)),
            }
        }
        edges.retain(|e| !e.2.is_zero());
        let n_cols = form.coeffs.len();
        let mut groups = Vec::new();
        while !edges.is_empty() {
            let mut degree = vec![0usize; n_cols];
            for &(a, b, _) in &edges {
                degree[a] += 1;
                degree[b] += usize::from(a != b);
            }
            let left = (0..n_cols).max_by_key(|&c| degree[c]).unwrap();
            let mut right = Vec::new();
            edges.retain(|&(a, b, q)| {
                let partner = if a == left { b } else { a };
                let mine = a == left || b == left;
                if mine {
                    right.push((partner, q));
                }
                !mine
            });
            groups.push((left, right));
        }
        let mut used: Vec<usize> = lin.iter().map(|t| t.0).collect();
        for (left, right) in &groups {
            used.push(*left);
            used.extend(right.iter().map(|t| t.0));
        }
        used.sort_unstable();
        used.dedup();
        Self {
            constant: form.constant,
            lin,
            groups,
            used,
        }
    }

    /// Columns of the state: `lin`, then `left_g` and `right_g` per group.
    fn width(&self) -> usize {
        1 + 2 * self.groups.len()
    }

    /// The state of the first `rows` (at most eight) rows, unfolded, from the `K` columns.
    fn small_state(&self, cols: &[&[F64]], rows: usize) -> State {
        let dot = |terms: &Lin, i: usize| terms.iter().map(|&(c, w)| w.mul_base(cols[c][i])).sum();
        let column = |value: &dyn Fn(usize) -> F192| {
            F192x8::from_array(&std::array::from_fn(|i| if i < rows { value(i) } else { F192::ZERO }))
        };
        let mut state = vec![column(&|i| dot(&self.lin, i))];
        for (left, right) in &self.groups {
            state.push(column(&|i| F192::from(cols[*left][i])));
            state.push(column(&|i| dot(right, i)));
        }
        state
    }
}

fn load_k(col: &[F64], i: usize) -> F64x8 {
    F64x8::from_array(col[i..i + 8].try_into().unwrap())
}

fn load_e(col: &[F192], i: usize) -> F192x8 {
    F192x8::from_array(col[i..i + 8].try_into().unwrap())
}

fn splat(terms: &Lin) -> Vec<(usize, F192x8)> {
    terms.iter().map(|&(c, w)| (c, F192x8::splat(w))).collect()
}

/// A table's state: per vector of eight rows, its `width` columns side by side, `state[b * width + c]`,
/// the blocks of the rows below the round's `half` first, then those above. Below eight rows, one vector
/// per column holds them all.
type State = Vec<F192x8>;

/// The blocks task `t` covers out of `n`.
fn task_blocks(t: usize, n: usize) -> std::ops::Range<usize> {
    t * TASK_BLOCKS..((t + 1) * TASK_BLOCKS).min(n)
}

fn xor2(a: [Prod8; 2], b: [Prod8; 2]) -> [Prod8; 2] {
    [a[0] ^ b[0], a[1] ^ b[1]]
}

fn finish([endpoint, slope]: [Prod8; 2], constant: F192) -> [F192; 2] {
    [endpoint.reduce() + constant, slope.reduce()]
}

/// The first round a table is active: its message, and its state over all its rows, unfolded, in one
/// pass over the `K` columns, which no later round reads. The linear forms are `E x K` mixed dots, and
/// every product of the summand is one mixed product against a reduced `right_g`.
fn expand(form: &Form, cols: &[&[F64]], eqr: &[F192], half: usize, at_one: bool) -> (State, [F192; 2]) {
    if half < 8 {
        let state = form.small_state(cols, 2 * half);
        let message = message_e(form, &state, eqr, half, at_one);
        return (state, message);
    }
    let lin = splat(&form.lin);
    let rights: Vec<_> = form.groups.iter().map(|(_, right)| splat(right)).collect();
    let dot = |terms: &[(usize, F192x8)], vals: &[F64x8]| {
        terms
            .iter()
            .fold(Prod8::ZERO, |acc, &(c, w)| acc ^ w.mul_base_unreduced(vals[c]))
            .reduce_lanes()
    };
    let entries = |vals: &[F64x8], out: &mut [F192x8]| {
        out[0] = dot(&lin, vals);
        for (g, ((left, _), right)) in form.groups.iter().zip(&rights).enumerate() {
            out[1 + 2 * g] = F192x8::from(vals[*left]);
            out[2 + 2 * g] = dot(right, vals);
        }
    };
    let (blocks, width) = (half / 8, form.width());
    let zero = F64x8::from_array(&[F64::ZERO; 8]);
    let mut acc = [Prod8::ZERO; 2];
    // SAFETY: every task writes all `width` entries of each of its blocks in both halves.
    let state = unsafe {
        primitives::filled_vec(2 * blocks * width, |state| {
            let (lows, highs) = state.split_at_mut(blocks * width);
            acc = parallel::map_reduce_chunks_mut(
                [lows, highs],
                [TASK_BLOCKS * width; 2],
                || (vec![zero; cols.len()], vec![zero; cols.len()]),
                || [Prod8::ZERO; 2],
                |(lo, hi), acc, t, [lows, highs]| {
                    let outs = lows.chunks_exact_mut(width).zip(highs.chunks_exact_mut(width));
                    for (b, (lo_out, hi_out)) in task_blocks(t, blocks).zip(outs) {
                        let i = 8 * b;
                        for &c in &form.used {
                            (lo[c], hi[c]) = (load_k(cols[c], i), load_k(cols[c], i + half));
                        }
                        entries(lo, lo_out);
                        entries(hi, hi_out);
                        let (end, end_k) = if at_one { (&*hi_out, &*hi) } else { (&*lo_out, &*lo) };
                        let (mut endpoint, mut slope) = (Prod8::ZERO, Prod8::ZERO);
                        for (g, (left, _)) in form.groups.iter().enumerate() {
                            endpoint ^= end[2 + 2 * g].mul_base_unreduced(end_k[*left]);
                            slope ^= (lo_out[2 + 2 * g] + hi_out[2 + 2 * g]).mul_base_unreduced(lo[*left] + hi[*left]);
                        }
                        let eq = load_e(eqr, i);
                        acc[0] ^= (endpoint.reduce_lanes() + end[0]).mul_unreduced(eq);
                        acc[1] ^= slope.reduce_lanes().mul_unreduced(eq);
                    }
                },
                xor2,
            );
        })
    };
    (state, finish(acc, form.constant))
}

/// An active round of a table, from its state.
fn message_e(form: &Form, state: &State, eqr: &[F192], half: usize, at_one: bool) -> [F192; 2] {
    if half < 8 {
        // Fewer row pairs than a vector: `[Σ_i eqr[i]·end_i, Σ_i eqr[i]·Q(lo_i + hi_i)]` by lanes.
        // `eqr` sums to one, so the form's constant seeds the endpoint.
        let rows: Vec<[F192; 8]> = state.iter().map(|v| v.to_array()).collect();
        return (0..half).fold([form.constant, F192::ZERO], |acc, i| {
            let (lo, hi) = (|c: usize| rows[c][i], |c: usize| rows[c][i + half]);
            let end = |c| if at_one { hi(c) } else { lo(c) };
            let (mut endpoint, mut slope) = (end(0), F192::ZERO);
            for g in (1..state.len()).step_by(2) {
                endpoint += end(g) * end(g + 1);
                slope += (lo(g) + hi(g)) * (lo(g + 1) + hi(g + 1));
            }
            [acc[0] + eqr[i] * endpoint, acc[1] + eqr[i] * slope]
        });
    }
    let (blocks, width) = (half / 8, form.width());
    let (lows, highs) = state.split_at(blocks * width);
    let acc = parallel::fold_reduce(
        blocks.div_ceil(TASK_BLOCKS),
        || [Prod8::ZERO; 2],
        |acc, t| {
            for b in task_blocks(t, blocks) {
                let (lo, hi) = (&lows[b * width..][..width], &highs[b * width..][..width]);
                block_message(lo, hi, load_e(eqr, 8 * b), at_one, acc);
            }
        },
        xor2,
    );
    finish(acc, form.constant)
}

/// Adds one block's terms to a table's message: `lo` and `hi` are its state entries in the
/// two halves, `eq` its rows' eq weights.
#[inline(always)]
fn block_message(lo: &[F192x8], hi: &[F192x8], eq: F192x8, at_one: bool, acc: &mut [Prod8; 2]) {
    let end = if at_one { hi } else { lo };
    let (mut endpoint, mut slope) = (Prod8::ZERO, Prod8::ZERO);
    for g in (1..lo.len()).step_by(2) {
        endpoint ^= end[g].mul_unreduced(end[g + 1]);
        slope ^= (lo[g] + hi[g]).mul_unreduced(lo[g + 1] + hi[g + 1]);
    }
    acc[0] ^= (endpoint.reduce_lanes() + end[0]).mul_unreduced(eq);
    acc[1] ^= slope.reduce_lanes().mul_unreduced(eq);
}

/// [`fold_state`], and the next round's message from the folded state, in one pass: a task folds
/// block `k` of every quarter into block `k` of both next halves, the pair that message reads.
/// `eqr` and `at_one` are the next round's; `None` below sixteen rows per half.
fn fold_and_message(
    form: &Form,
    state: &mut State,
    r: F192,
    half: usize,
    eqr: &[F192],
    at_one: bool,
) -> Option<[F192; 2]> {
    if half < 16 {
        fold_state(state, r, half);
        return None;
    }
    let (pairs, width) = (half / 16, form.width());
    let r8 = F192x8::splat(r);
    let (left, right) = state.split_at_mut(2 * pairs * width);
    let (q0, q1) = left.split_at_mut(pairs * width);
    let (q2, q3) = right.split_at_mut(pairs * width);
    let acc = parallel::map_reduce_chunks_mut(
        [q0, q1, q2, q3],
        [TASK_BLOCKS * width; 4],
        || (),
        || [Prod8::ZERO; 2],
        |(), acc, t, [lo, hi, upper_lo, upper_hi]| {
            let quarters = lo.chunks_exact_mut(width).zip(hi.chunks_exact_mut(width));
            let uppers = upper_lo.chunks_exact(width).zip(upper_hi.chunks_exact(width));
            for (k, ((lo, hi), (upper_lo, upper_hi))) in task_blocks(t, pairs).zip(quarters.zip(uppers)) {
                for (v, &u) in lo.iter_mut().zip(upper_lo).chain(hi.iter_mut().zip(upper_hi)) {
                    *v = *v + (*v + u) * r8;
                }
                block_message(lo, hi, load_e(eqr, 8 * k), at_one, acc);
            }
        },
        xor2,
    );
    state.truncate(2 * pairs * width);
    Some(finish(acc, form.constant))
}

/// The state folded by `r`, `v[i] = v[i] + r·(v[i] + v[i + half])` in every column, the upper half dropped.
/// From eight rows up the halves are whole vectors, so the fold is elementwise.
fn fold_state(state: &mut State, r: F192, half: usize) {
    if half < 8 {
        for v in state.iter_mut() {
            let mut rows = v.to_array();
            (0..half).for_each(|i| rows[i] = interp(rows[i], rows[i + half], r));
            *v = F192x8::from_array(&rows);
        }
        return;
    }
    let r8 = F192x8::splat(r);
    let n = state.len() / 2;
    let (lows, highs) = state.split_at_mut(n);
    parallel::chunks_mut(lows, FOLD_CHUNK, |t, lows| {
        for (lo, &hi) in lows.iter_mut().zip(&highs[t * FOLD_CHUNK..]) {
            *lo = *lo + (*lo + hi) * r8;
        }
    });
    state.truncate(n);
}

/// One table of the batch, and what the rounds have made of it.
struct Table<'a> {
    tau: usize,
    sigma: F192,
    /// Its summand's factor: the challenges it sat out, then the eq factors of the rounds it was active.
    weight: F192,
    form: Form,
    cols: &'a [&'a [F64]],
    /// The state, from the table's first active round: a few `E` columns, the batch's largest transients.
    state: Option<State>,
    /// The next round's message, when the last fold built it.
    next: Option<[F192; 2]>,
}

impl Table<'_> {
    /// The message of the round that binds variable `m`, while the table is active. The first such
    /// round expands the table's state.
    fn message(&mut self, eqr: &[F192], m: usize, at_one: bool) -> [F192; 2] {
        if let Some(p) = self.next.take() {
            return p;
        }
        let (form, half) = (&self.form, 1 << m);
        match &self.state {
            Some(state) => message_e(form, state, eqr, half, at_one),
            None => {
                let (state, p) = expand(form, self.cols, eqr, half, at_one);
                self.state = Some(state);
                p
            }
        }
    }

    /// Binds variable `m` to `r`, folding the state, and builds the next round's message on the way
    /// against its `eqr` and `at_one`.
    fn bind(&mut self, r: F192, m: usize, eqr: &[F192], at_one: bool) {
        let state = self.state.as_mut().expect("an active table has its state");
        self.next = fold_and_message(&self.form, state, r, 1 << m, eqr, at_one);
    }
}

fn round_polynomial([endpoint, quadratic]: [F192; 2], zeta: F192, claim: F192, waiting: F192) -> [F192; 4] {
    let eq_z = F192::ONE + zeta;
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
pub fn prove(airs: &[Air<'_>], zeta: &[F192], ps: &mut ProverState) -> Vec<Claims> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    let mut tables: Vec<Table> = airs
        .iter()
        .map(|air| Table {
            tau: air.tau,
            sigma: air.sigma,
            weight: F192::ONE,
            form: Form::new(&air.form),
            cols: air.cols,
            state: None,
            next: None,
        })
        .collect();
    // ONE eq table over the low (still free) variables serves every active table.
    let mut eqr = eq_table(&zeta[..n.saturating_sub(1)]);
    let mut chi = vec![F192::ZERO; n];
    // `k`, the challenges drawn so far, common to every table that is still waiting.
    let mut k = F192::ONE;
    let mut claim = airs.iter().map(|a| a.sigma).sum();
    for j in 0..n {
        let m = n - 1 - j; // the variable this round binds
        let at_one = zeta[m].is_zero();
        // The waiting tables contribute the line `Y·k·Σσ`, whose slope `u` is all there
        // is to it. It is NOT sent on its own: it folds into `h` below, and only `h`
        // travels. `msg` is the active tables' degree-2 cofactor, `h`'s multiplicand.
        let waiting = tables.iter().filter(|t| t.tau <= m).map(|t| t.sigma).sum();
        let u = k * waiting;
        let mut msg = [F192::ZERO; 2];
        for t in tables.iter_mut().filter(|t| t.tau > m) {
            let p = t.message(&eqr, m, at_one);
            msg[0] += t.weight * p[0];
            msg[1] += t.weight * p[1];
        }
        shrink_eq_high(&mut eqr);
        // The running claim recovers the missing endpoint of the quadratic cofactor.
        // The fold waits for this message to be bound, since its challenge depends on it;
        // the next round's message rides along with the fold.
        let h = round_polynomial(msg, zeta[m], claim, u);
        ps.add_round_poly(&h, false);
        let rk = ps.sample();
        claim = poly_eval(&h, rk);
        chi[m] = rk;
        k *= rk;
        let eq_k = F192::ONE + zeta[m] + rk;
        let at_one_next = m > 0 && zeta[m - 1].is_zero();
        for t in &mut tables {
            if t.tau > m {
                t.weight *= eq_k;
                t.bind(rk, m, &eqr, at_one_next);
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

    const COLS: usize = 6;

    /// Products sharing column 0, one of them named twice and either way round, a square, linear
    /// terms and a constant.
    fn synth(pows: &[F192]) -> BusForm {
        let mut form = BusForm::new(COLS);
        form.constant = F192::ONE;
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

    fn random_e(state: &mut u64) -> F192 {
        F192::new(splitmix(state), splitmix(state), splitmix(state))
    }

    fn random_columns(state: &mut u64, rows: usize) -> Vec<Vec<F64>> {
        (0..COLS)
            .map(|_| (0..rows).map(|_| F64(splitmix(state))).collect())
            .collect()
    }

    #[test]
    fn grouped_form_reproduces_the_summand() {
        let mut s = 1;
        let pows: Vec<F192> = (0..3).map(|_| random_e(&mut s)).collect();
        let form = Form::new(&synth(&pows));
        assert_eq!(
            form.groups.len(),
            2,
            "column 0 covers three products, the square is the other group"
        );
        for _ in 0..4 {
            let v: Vec<F192> = (0..COLS).map(|_| random_e(&mut s)).collect();
            let dot = |terms: &Lin| terms.iter().map(|&(c, w)| w * v[c]).sum();
            let quad = form.groups.iter().map(|(l, right)| v[*l] * dot(right)).sum();
            assert_eq!(quad, synth(&pows).eval(&v, true));
            assert_eq!(form.constant + dot(&form.lin) + quad, synth(&pows).eval(&v, false));
        }
    }

    /// `[Σ eqr·P(end), Σ eqr·Q(lo + hi)]` by evaluating the summand row by row.
    fn naive_message(pows: &[F192], cols: &[Vec<F192>], eqr: &[F192], half: usize, at_one: bool) -> [F192; 2] {
        (0..half).fold([F192::ZERO; 2], |acc, i| {
            let row = |off: usize| -> Vec<F192> { cols.iter().map(|c| c[i + off]).collect() };
            let (lo, hi) = (row(0), row(half));
            let sum: Vec<F192> = lo.iter().zip(&hi).map(|(&a, &b)| a + b).collect();
            let end = if at_one { &hi } else { &lo };
            [
                acc[0] + eqr[i] * synth(pows).eval(end, false),
                acc[1] + eqr[i] * synth(pows).eval(&sum, true),
            ]
        })
    }

    /// Every round of a table's life, at row counts on both sides of one vector: the expanded
    /// state's message, then each fold, its state's message and the next round's message the fold
    /// builds, against the naive formulas.
    #[test]
    fn round_messages_match_naive_evaluation() {
        let mut s = 7;
        let pows: Vec<F192> = (0..3).map(|_| random_e(&mut s)).collect();
        let form = Form::new(&synth(&pows));
        for m in [1usize, 3, 4, 5, 11] {
            let kcols = random_columns(&mut s, 2 << m);
            let views: Vec<&[F64]> = kcols.iter().map(|c| &c[..]).collect();
            let mut naive_cols: Vec<Vec<F192>> = kcols
                .iter()
                .map(|c| c.iter().map(|&x| F192::from(x)).collect())
                .collect();
            let mut eqr = eq_table(&(0..m).map(|_| random_e(&mut s)).collect::<Vec<_>>());
            let mut state = State::new();
            let mut next: Option<([F192; 2], bool)> = None;
            let mut half = 1usize << m;
            while half >= 1 {
                for at_one in [false, true] {
                    let want = naive_message(&pows, &naive_cols, &eqr, half, at_one);
                    if half == 1 << m {
                        let (st, p) = expand(&form, &views, &eqr, half, at_one);
                        assert_eq!(p, want, "expand, m {m}");
                        state = st;
                    }
                    assert_eq!(message_e(&form, &state, &eqr, half, at_one), want, "m {m} half {half}");
                    if let Some((fused, _)) = next.filter(|n| n.1 == at_one) {
                        assert_eq!(fused, want, "fused, m {m} half {half}");
                    }
                }
                let r = random_e(&mut s);
                shrink_eq_high(&mut eqr);
                let at_one = half.is_multiple_of(32);
                let fused = fold_and_message(&form, &mut state, r, half, &eqr, at_one);
                assert_eq!(fused.is_some(), half >= 16, "m {m} half {half}");
                next = fused.map(|p| (p, at_one));
                for c in &mut naive_cols {
                    *c = (0..half).map(|i| interp(c[i], c[i + half], r)).collect();
                }
                half /= 2;
            }
        }
    }
}
