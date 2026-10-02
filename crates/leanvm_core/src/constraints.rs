//! The tables' local constraints (§sec:air), proven by one sumcheck for all tables,
//! the lookup arrays' producers among them.
//!
//! A table may fold identities with a DISJOINT range of one `η`'s powers, so the
//! batch is a polynomial in `η` whose coefficients are the individual sums and
//! matching the batch's target still pins each one. What every instruction table
//! attaches is its two bus forms, which SHARE their two powers across tables, so
//! those coefficients are per-side totals and the target pins the total, which is
//! all the bus needs; the extension-field table also folds its three identities,
//! at powers of their own past those two. The forms' sums are the values the bus is
//! owed, so the target is those rather than zero. The verifier derives it from the
//! bus claims, and never reads it off the stream.
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
//! may be accumulated along the way or deferred to the end.
//!
//! The eq point is the caller's, not a fresh one (the bus's GKR point `ζ`), which
//! is what lets the forms' sums settle the bus. Batching derived in `doc/leanvm/main.tex`
//! §sec:air. Both sides take `n = max τ_t` from the announced heights, so there
//! are no rounds in which no table has joined.

use crate::PAR_THRESHOLD;
use crate::colval::ColVal;
use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192, F192Unreduced};
use primitives::multilinear::{eq_table_arena, poly_eval, shrink_eq_high};
#[cfg(test)]
use primitives::multilinear::{fold_high_inplace, fold_high_k};
use zk_alloc::ArenaVec;

/// One table's sent columns' evaluations at its table-sumcheck point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub chi: Vec<F192>,
    pub evals: Vec<F192>,
}

impl Claims {
    /// The evaluations, then zeros up to `N`.
    ///
    /// # Panics
    ///
    /// Panics if there are more than `N` evaluations.
    pub fn evals_padded<const N: usize>(&self) -> [F192; N] {
        let mut out = [F192::ZERO; N];
        out[..self.evals.len()].copy_from_slice(&self.evals);
        out
    }
}

/// Why the table constraints reject.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// The bus point has fewer coordinates than the tallest table has variables.
    #[error("the bus point has {len} coordinates, and the tallest table has {rounds} variables")]
    PointTooShort { len: usize, rounds: usize },
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] fiat_shamir::transcript::Error),
    /// The sumcheck's final claim is not the tables' summands at the opened columns.
    #[error("the constraint sumcheck's final claim does not match the columns")]
    FinalMismatch,
}

/// One table's summand at one row: its identities and bus forms, already weighted by
/// their `η`-powers, over the table's columns.
///
/// Written once, generic over the column type: `K` in the round a table joins the
/// batch, `E` after it (see [`ColVal`]).
pub trait Summand: Sync {
    /// The summand at `cols`; `quadratic` selects only its degree-two terms.
    fn eval<T: ColVal>(&self, cols: &[T], quadratic: bool) -> F192;

    /// The table's public columns at its point `chi`, which the verifier computes rather
    /// than reads: as many as the air's `n_public`.
    fn public(&self, _chi: &[F192]) -> Vec<F192> {
        Vec::new()
    }
}

/// One table's place in the shared batch. Its last `n_public` columns are public: the
/// prover folds them like the rest, but sends none, and the verifier takes their values
/// at the point from [`Summand::public`].
pub struct Air<S> {
    pub tau: usize,
    pub n_cols: usize,
    pub n_public: usize,
    pub summand: S,
}

/// One table's columns as the prover hands them over: `K`-valued as committed, lifted
/// into `E` on the round the table joins, or `E`-valued from the start.
pub enum Columns<'a> {
    K(Vec<&'a [F64]>),
    E(Vec<ArenaVec<F192>>),
}

/// Start of each table's disjoint range of `η`-powers.
pub fn xi_offsets(n_constraints: impl Iterator<Item = usize>) -> Vec<usize> {
    n_constraints
        .scan(0usize, |off, n| {
            let start = *off;
            *off += n;
            Some(start)
        })
        .collect()
}

/// An active round: one endpoint evaluation and the quadratic coefficient.
///
/// Generic twice over: in the column element, `K` before a table's columns are
/// folded and `E` after ([`ColVal`]), and in the container, `Vec` for the former
/// and `ArenaVec` for the latter. `#[inline(always)]` matters here, on this and on
/// every `ColVal` method: this is the body of the constraint sumcheck's innermost
/// loop, and without it the generic stops inlining and costs measurable prover
/// time. Nothing is lifted into `E`, so a `K` round evaluates the identity and the
/// bus forms in 64-bit arithmetic, and its scratch is a third the size.
#[inline(always)]
fn table_message<T: ColVal, C: std::ops::Deref<Target = [T]> + Sync>(
    cols: &[C],
    summand: &impl Summand,
    half: usize,
    eqr: &[F192],
    at_one: bool,
) -> [F192; 2] {
    let ncols = cols.len();
    // The X² coefficient is Q(hi + lo); linear and constant terms cannot contribute.
    let summand = |i: usize, scratch: &mut [T]| -> [F192Unreduced; 2] {
        let e = eqr[i];
        let (endpoint, slope) = scratch.split_at_mut(ncols);
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            endpoint[ci] = if at_one { hi } else { lo };
            slope[ci] = lo + hi;
        }
        [
            e.mul_unreduced(summand.eval(endpoint, false)),
            e.mul_unreduced(summand.eval(slope, true)),
        ]
    };
    let xor = |a: [F192Unreduced; 2], b: [F192Unreduced; 2]| [a[0] ^ b[0], a[1] ^ b[1]];
    let acc = if half >= PAR_THRESHOLD {
        // The `2 * ncols` scratch is per-worker, not per-row: `map_reduce_with_state`
        // creates it once and threads it through every row that worker claims.
        parallel::map_reduce_with_state(
            half,
            || vec![T::ZERO; 2 * ncols],
            || [F192Unreduced::ZERO; 2],
            |scratch, acc, i| *acc = xor(*acc, summand(i, scratch)),
            xor,
        )
    } else {
        let mut scratch = vec![T::ZERO; 2 * ncols];
        (0..half).fold([F192Unreduced::ZERO; 2], |acc, i| xor(acc, summand(i, &mut scratch)))
    };
    acc.map(F192Unreduced::reduce)
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

/// Prove all tables' weighted constraints with one sumcheck over the tallest table.
/// Return each table's column evaluations at its nested terminal point.
/// Folded tables store whole rows to build each next message during the preceding fold.
pub fn prove<S: Summand>(
    airs: &[Air<S>],
    cols: Vec<Columns<'_>>,
    zeta: &[F192],
    sigma: &[F192],
    ps: &mut ProverState,
) -> Vec<Claims> {
    // The tallest table sets the common cube; shorter tables join after its high variables bind.
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    let mut weights = vec![F192::ONE; airs.len()];
    let mut eqr = eq_table_arena(&zeta[..n.saturating_sub(1)]);
    let mut chi = vec![F192::ZERO; n];
    // Borrow the committed columns until their joining round, then retain only folded rows.
    let mut pending: Vec<Option<Columns<'_>>> = cols.into_iter().map(Some).collect();
    let mut folded: Vec<Option<ArenaVec<F192>>> = (0..airs.len()).map(|_| None).collect();
    let mut messages = vec![None; airs.len()];
    let mut k = F192::ONE;
    let mut claim = sigma.iter().copied().fold(F192::ZERO, |a, b| a + b);
    for j in 0..n {
        let m = n - 1 - j;
        // Waiting tables contribute only a line in the current variable.
        let waiting = airs
            .iter()
            .zip(sigma)
            .filter(|(a, _)| a.tau <= m)
            .fold(F192::ZERO, |acc, (_, &s)| acc + s);
        let u = k * waiting;
        let mut msg = [F192::ZERO; 2];
        for (t, air) in airs.iter().enumerate() {
            if air.tau > m {
                // An active table's preceding fold already produced this message.
                let p = messages[t].take().unwrap_or_else(|| {
                    match pending[t].as_ref().expect("a joining table has columns") {
                        Columns::K(c) => table_message(c, &air.summand, 1 << m, &eqr, zeta[m].is_zero()),
                        Columns::E(c) => table_message(c, &air.summand, 1 << m, &eqr, zeta[m].is_zero()),
                    }
                });
                for i in 0..2 {
                    msg[i] += weights[t] * p[i];
                }
            }
        }
        // Bind the current message before sampling the challenge used by its fold.
        let h = round_polynomial(msg, zeta[m], claim, u);
        ps.add_round_poly(&h, false);
        let rk = ps.sample();
        claim = poly_eval(&h, rk);
        chi[m] = rk;
        k *= rk;
        let eq_k = F192::ONE + zeta[m] + rk;
        shrink_eq_high(&mut eqr);
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
            if air.tau <= m || air.n_cols == 0 {
                continue;
            }
            let at_one = m > 0 && zeta[m - 1].is_zero();
            // Folding two pairs produces the endpoints of the next round in worker scratch.
            if let Some(table) = &mut folded[t] {
                messages[t] = fold_rows_and_message(table, air.n_cols, rk, &air.summand, &eqr, at_one);
            } else {
                let (table, message) = match pending[t].take().expect("a joining table has columns") {
                    Columns::K(c) => fold_columns_and_message(&c, rk, &air.summand, &eqr, at_one),
                    Columns::E(c) => fold_columns_and_message(&c, rk, &air.summand, &eqr, at_one),
                };
                folded[t] = Some(table);
                messages[t] = message;
            }
        }
    }
    // The remaining row holds all final column evaluations in their original order.
    airs.iter()
        .enumerate()
        .map(|(t, air)| {
            let mut evals: Vec<F192> = folded[t].as_ref().map_or_else(
                || match pending[t].as_ref().expect("a constant table has columns") {
                    Columns::K(c) => c.iter().map(|v| F192::from(v[0])).collect(),
                    Columns::E(c) => c.iter().map(|v| v[0]).collect(),
                },
                |table| table.to_vec(),
            );
            // Public evaluations are reconstructed by the verifier rather than sent.
            evals.truncate(air.n_cols - air.n_public);
            ps.add_scalars(&evals);
            Claims {
                chi: chi[..air.tau].to_vec(),
                evals,
            }
        })
        .collect()
}

/// Fold two row pairs and accumulate their next-round summand before publishing the rows.
fn folded_message(
    ncols: usize,
    eqr: &[F192],
    summand: &impl Summand,
    at_one: bool,
    fold: impl Fn(usize, &mut [F192], &mut [F192]) + Sync,
) -> [F192; 2] {
    let accumulate = |scratch: &mut Vec<F192>, acc: &mut [F192Unreduced; 2], i: usize| {
        // Layout: [next low row | next high row | their difference].
        let (lo, rest) = scratch.split_at_mut(ncols);
        let (hi, slope) = rest.split_at_mut(ncols);
        fold(i, lo, hi);
        for c in 0..ncols {
            slope[c] = lo[c] + hi[c];
        }
        let endpoint = if at_one { &*hi } else { &*lo };
        // The quadratic coefficient depends only on the difference of the endpoint rows.
        acc[0] ^= eqr[i].mul_unreduced(summand.eval(endpoint, false));
        acc[1] ^= eqr[i].mul_unreduced(summand.eval(slope, true));
    };
    let acc = if eqr.len() >= PAR_THRESHOLD {
        parallel::map_reduce_with_state(
            eqr.len(),
            || vec![F192::ZERO; 3 * ncols],
            || [F192Unreduced::ZERO; 2],
            accumulate,
            |a, b| [a[0] ^ b[0], a[1] ^ b[1]],
        )
    } else {
        // Reuse scratch across the small final rounds without dispatching workers.
        let mut scratch = vec![F192::ZERO; 3 * ncols];
        let mut acc = [F192Unreduced::ZERO; 2];
        for i in 0..eqr.len() {
            accumulate(&mut scratch, &mut acc, i);
        }
        acc
    };
    acc.map(F192Unreduced::reduce)
}

/// Convert the joining table's column layout into folded rows and its next message.
fn fold_columns_and_message<T: ColVal + Into<F192>, C: std::ops::Deref<Target = [T]> + Sync>(
    cols: &[C],
    rk: F192,
    summand: &impl Summand,
    eqr: &[F192],
    at_one: bool,
) -> (ArenaVec<F192>, Option<[F192; 2]>) {
    let ncols = cols.len();
    let half = cols[0].len() / 2;
    // SAFETY: the single-row branch or the paired-row dispatch writes every output element.
    let mut out = unsafe { ArenaVec::uninitialized(half * ncols) };
    let interp = |a: T, b: T| a.into() + (a + b).mul_e(rk);
    if half == 1 {
        // No next variable remains, so only the final evaluations are needed.
        for (c, dst) in cols.iter().zip(&mut out) {
            *dst = interp(c[0], c[1]);
        }
        return (out, None);
    }
    let pairs = half / 2;
    let (lo, hi) = out.split_at_mut(pairs * ncols);
    let lo = parallel::Chunks::new(lo, ncols);
    let hi = parallel::Chunks::new(hi, ncols);
    let message = folded_message(ncols, eqr, summand, at_one, |i, a, b| {
        for (c, col) in cols.iter().enumerate() {
            a[c] = interp(col[i], col[i + half]);
            b[c] = interp(col[i + pairs], col[i + pairs + half]);
        }
        // SAFETY: task i owns row i in each disjoint output half for the whole dispatch.
        unsafe {
            lo.get(i).copy_from_slice(a);
            hi.get(i).copy_from_slice(b);
        }
    });
    (out, Some(message))
}

/// Fold row-major storage in place while building the next round's message from scratch.
fn fold_rows_and_message(
    table: &mut ArenaVec<F192>,
    ncols: usize,
    rk: F192,
    summand: &impl Summand,
    eqr: &[F192],
    at_one: bool,
) -> Option<[F192; 2]> {
    let half = table.len() / (2 * ncols);
    if half == 1 {
        // The final two rows collapse directly to one evaluation row.
        let (lo, hi) = table.split_at_mut(ncols);
        for (a, &b) in lo.iter_mut().zip(hi.iter()) {
            *a += (*a + b) * rk;
        }
        table.truncate(ncols);
        return None;
    }
    let pairs = half / 2;
    // Each task owns one row in all four quarters, including its two output rows.
    let (left, right) = table.split_at_mut(half * ncols);
    let (q0, q1) = left.split_at_mut(pairs * ncols);
    let (q2, q3) = right.split_at_mut(pairs * ncols);
    let q0 = parallel::Chunks::new(q0, ncols);
    let q1 = parallel::Chunks::new(q1, ncols);
    let q2 = parallel::Chunks::new(q2, ncols);
    let q3 = parallel::Chunks::new(q3, ncols);
    let message = folded_message(ncols, eqr, summand, at_one, |i, a, b| {
        // SAFETY: task i exclusively borrows row i in each disjoint quarter exactly once.
        let (lo, hi, upper_lo, upper_hi) = unsafe { (q0.get(i), q1.get(i), q2.get(i), q3.get(i)) };
        for c in 0..ncols {
            a[c] = lo[c] + (lo[c] + upper_lo[c]) * rk;
            b[c] = hi[c] + (hi[c] + upper_hi[c]) * rk;
        }
        // Read all four input rows before overwriting either output row.
        lo.copy_from_slice(a);
        hi.copy_from_slice(b);
    });
    table.truncate(half * ncols);
    Some(message)
}

/// Reference prover with separate column-message and column-fold passes.
#[cfg(test)]
fn prove_reference<S: Summand>(
    airs: &[Air<S>],
    cols: Vec<Columns<'_>>,
    zeta: &[F192],
    sigma: &[F192],
    ps: &mut ProverState,
) -> Vec<Claims> {
    // All tables share the tallest table's cube.
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    // Each table carries its own accumulated equality and waiting-variable factors.
    let mut weights = vec![F192::ONE; airs.len()];
    let mut eqr = eq_table_arena(&zeta[..n.saturating_sub(1)]);
    let mut chi = vec![F192::ZERO; n];
    // Extension columns are already owned; base columns stay borrowed until joining.
    let (cols, mut folded): (Vec<Vec<&[F64]>>, Vec<_>) = cols
        .into_iter()
        .map(|c| match c {
            Columns::K(k) => (k, None),
            Columns::E(e) => (Vec::new(), Some(e)),
        })
        .unzip();
    let mut k = F192::ONE;
    let mut claim = sigma.iter().copied().fold(F192::ZERO, |a, b| a + b);
    for j in 0..n {
        let m = n - 1 - j;
        // Shorter tables contribute a line until they join the common cube.
        let waiting = airs
            .iter()
            .zip(sigma)
            .filter(|(a, _)| a.tau <= m)
            .fold(F192::ZERO, |acc, (_, &s)| acc + s);
        let u = k * waiting;
        // Sum the current messages before any column is folded.
        let mut msg = [F192::ZERO; 2];
        for (t, air) in airs.iter().enumerate() {
            if air.tau > m {
                let p = folded[t].as_ref().map_or_else(
                    || table_message(&cols[t], &air.summand, 1 << m, &eqr, zeta[m].is_zero()),
                    |table| table_message(table, &air.summand, 1 << m, &eqr, zeta[m].is_zero()),
                );
                for i in 0..2 {
                    msg[i] += weights[t] * p[i];
                }
            }
        }
        // Retain only the equality weights needed by the next round.
        shrink_eq_high(&mut eqr);
        let h = round_polynomial(msg, zeta[m], claim, u);
        // Bind the message before drawing the challenge for its fold.
        ps.add_round_poly(&h, false);
        let rk = ps.sample();
        claim = poly_eval(&h, rk);
        chi[m] = rk;
        k *= rk;
        let eq_k = F192::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
            if air.tau <= m {
                continue;
            }
            // This independent oracle folds every column in a separate pass.
            if let Some(table) = &mut folded[t] {
                if m >= PAR_THRESHOLD.trailing_zeros() as usize {
                    let cols = parallel::Chunks::new(table, 1);
                    parallel::for_each(cols.count(), |ci| {
                        // SAFETY: each task exclusively folds one owned column for the whole dispatch.
                        let col = unsafe { &mut cols.get(ci)[0] };
                        fold_high_inplace(col, rk);
                    });
                } else {
                    table.iter_mut().for_each(|c| fold_high_inplace(c, rk));
                }
            } else {
                folded[t] = Some(parallel::map_collect(cols[t].len(), |ci| fold_high_k(cols[t][ci], rk)));
            }
        }
    }

    // Send only the nonpublic terminal evaluations.
    airs.iter()
        .enumerate()
        .map(|(t, air)| {
            let mut evals: Vec<F192> = folded[t].as_ref().map_or_else(
                || cols[t].iter().map(|c| F192::from(c[0])).collect(),
                |table| table.iter().map(|c| c[0]).collect(),
            );
            evals.truncate(air.n_cols - air.n_public);
            ps.add_scalars(&evals);
            Claims {
                chi: chi[..air.tau].to_vec(),
                evals,
            }
        })
        .collect()
}

/// Verify the table sumcheck, returning the per-table claims for the caller to
/// settle against the commitment.
pub fn verify<S: Summand>(
    airs: &[Air<S>],
    zeta: &[F192],
    target: F192,
    vs: &mut VerifierState,
) -> Result<Vec<Claims>, Error> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    if zeta.len() < n {
        return Err(Error::PointTooShort {
            len: zeta.len(),
            rounds: n,
        });
    }
    let mut weights = vec![F192::ONE; airs.len()];
    // An ordinary sumcheck for `target`, which the caller supplies. Each round
    // arrives as the round polynomial itself at `nd`, so the two steps are the
    // textbook ones and nothing has to be reapplied: no eq factor, no separate
    // waiting term. `ζ` and the heights enter only `weights`, never the check.
    let mut claim = target;
    let mut chi = vec![F192::ZERO; n];
    for j in 0..n {
        let m = n - 1 - j;
        // The running claim fixes the linear coefficient.
        let h = vs.next_round_poly(4, claim, None)?;
        let rk = vs.sample();
        chi[m] = rk;
        claim = poly_eval(&h, rk);
        let eq_k = F192::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
        }
    }

    let mut acc = F192::ZERO;
    let mut claims = Vec::with_capacity(airs.len());
    for (t, air) in airs.iter().enumerate() {
        let evals = vs.next_scalars(air.n_cols - air.n_public)?;
        let mut values = evals.clone();
        values.extend(air.summand.public(&chi[..air.tau]));
        assert_eq!(values.len(), air.n_cols, "a table's public columns are all evaluated");
        acc += weights[t] * air.summand.eval(&values, false);
        claims.push(Claims {
            chi: chi[..air.tau].to_vec(),
            evals,
        });
    }
    if acc != claim {
        return Err(Error::FinalMismatch);
    }
    Ok(claims)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::transcript::Proof;
    use primitives::field::powers;
    use primitives::test_rng::Rng;
    use proptest::prelude::*;

    /// Two identities over four columns, `pows`-weighted, plus `constant`. An attached
    /// third "identity" is the linear form `vals[1]`, whose claimed sum is an
    /// evaluation of column 1 rather than zero.
    struct Synth {
        pows: Vec<F192>,
        attached: bool,
        constant: F192,
    }

    impl Summand for Synth {
        fn eval<T: ColVal>(&self, v: &[T], quadratic: bool) -> F192 {
            let p = &self.pows;
            if quadratic {
                return (v[0] * v[1]).mul_e(p[0]);
            }
            let attached = if self.attached { v[1].mul_e(p[2]) } else { F192::ZERO };
            (v[0] * v[1] + v[2]).mul_e(p[0]) + (v[0] + v[3]).mul_e(p[1]) + attached + self.constant
        }
    }

    #[test]
    fn round_coefficients_match_full_evaluations() {
        fn check<T: ColVal + Into<F192>>(cols: &[Vec<T>]) {
            let synth = Synth {
                pows: powers(F192::new(3, 5, 7), 3),
                attached: true,
                constant: F192::ONE,
            };
            let eq = eq_table_arena(&[F192::new(11, 13, 17), F192::new(19, 23, 29)]);
            let full_eval = |r| {
                (0..4).fold(F192::ZERO, |sum, i| {
                    let v: Vec<_> = cols
                        .iter()
                        .map(|c| primitives::multilinear::interp(c[i].into(), c[i + 4].into(), r))
                        .collect();
                    sum + eq[i] * synth.eval(&v, false)
                })
            };
            let waiting = F192::new(43, 47, 53);
            for zeta in [F192::ZERO, F192::ONE, F192::new(59, 61, 67)] {
                let message = table_message(cols, &synth, 4, &eq, zeta.is_zero());
                let claim = (F192::ONE + zeta) * full_eval(F192::ZERO) + zeta * full_eval(F192::ONE) + waiting;
                let h = round_polynomial(message, zeta, claim, waiting);
                for r in [F192::ZERO, F192::ONE, F192::new(31, 37, 41)] {
                    assert_eq!(poly_eval(&h, r), (F192::ONE + zeta + r) * full_eval(r) + r * waiting);
                }
            }
        }
        let base: Vec<Vec<F64>> = (0..4)
            .map(|j| (0..8).map(|i| F64(13 * i + 17 * j + 1)).collect())
            .collect();
        check(&base);
        let ext: Vec<Vec<F192>> = base
            .iter()
            .map(|c| c.iter().map(|v| F192::new(v.0, 3 * v.0, 7 * v.0)).collect())
            .collect();
        check(&ext);
    }

    fn good_table(tau: usize, salt: u64) -> Vec<Vec<F64>> {
        let n = 1usize << tau;
        let a: Vec<F64> = (0..n).map(|i| F64(i as u64 + salt)).collect();
        let b: Vec<F64> = (0..n).map(|i| F64(3 * i as u64 + 1 + salt)).collect();
        let ab: Vec<F64> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
        vec![a.clone(), b, ab, a]
    }

    /// Each table takes the next `n` of `η`'s powers, `n` its identities.
    fn airs_for(taus: &[usize], attached: bool, xi: F192) -> Vec<Air<Synth>> {
        let n = if attached { 3 } else { 2 };
        let pows = powers(xi, n * taus.len());
        taus.iter()
            .enumerate()
            .map(|(t, &tau)| Air {
                tau,
                n_cols: 4,
                n_public: 0,
                summand: Synth {
                    pows: pows[n * t..n * (t + 1)].to_vec(),
                    attached,
                    constant: F192::ZERO,
                },
            })
            .collect()
    }

    /// The eq point and `η` are the caller's; the tests fix them.
    fn xi_zeta(taus: &[usize]) -> (F192, Vec<F192>) {
        let n = taus.iter().copied().max().unwrap_or(0);
        let xi = F192::new(0x9e37_79b9_7f4a_7c15, 0x1234_5678_9abc_def0, 7);
        let zeta = (0..n)
            .map(|i| F192::new(i as u64 + 3, 0x5555 * (i as u64 + 1), i as u64 + 11))
            .collect();
        (xi, zeta)
    }

    fn run(taus: &[usize], cols: &[Vec<Vec<F64>>]) -> (Proof, Result<Vec<Claims>, Error>) {
        let (xi, zeta) = xi_zeta(taus);
        let airs = airs_for(taus, false, xi);
        let zeros = vec![F192::ZERO; taus.len()];
        let mut ps = ProverState::from_label(b"zc-test");
        let views = cols
            .iter()
            .map(|t| Columns::K(t.iter().map(|c| &c[..]).collect()))
            .collect();
        let pclaims = prove(&airs, views, &zeta, &zeros, &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::from_label(b"zc-test", &proof);
        let vclaims = verify(&airs, &zeta, F192::ZERO, &mut vs);
        if let Ok(vc) = &vclaims {
            assert_eq!(&pclaims, vc);
        }
        (proof, vclaims)
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(40))]
        #[test]
        fn arbitrary_columns_preserve_the_transcript(
            taus in prop::collection::vec(0usize..9, 1..7), seed in any::<u64>(), kinds in any::<u64>(),
        ) {
            // Fixture state: arbitrary columns and mixed field types need not satisfy the constraints.
            let mut rng = Rng::new(seed);
            let n = taus.iter().copied().max().unwrap();
            let xi = rng.ext();
            let zeta = rng.ext_vec(n);
            let sigma = rng.ext_vec(taus.len());
            let airs = airs_for(&taus, true, xi);
            // Base tables have zero extension coordinates; extension tables use the entire field.
            let columns: Vec<Vec<Vec<F192>>> = taus.iter().enumerate().map(|(t, &tau)| {
                (0..4).map(|_| (0..1 << tau).map(|_| {
                    if kinds >> t & 1 == 0 { F192::from(F64(rng.next_u64())) } else { rng.ext() }
                }).collect()).collect()
            }).collect();
            let base: Vec<Vec<Vec<F64>>> = columns.iter().map(|table| {
                table.iter().map(|c| c.iter().map(|v| F64(v.c0)).collect()).collect()
            }).collect();
            // Both oracles receive fresh extension buffers and identical borrowed base values.
            let views = || columns.iter().enumerate().map(|(t, c)| {
                if kinds >> t & 1 == 0 { Columns::K(base[t].iter().map(|c| &c[..]).collect()) }
                else { Columns::E(c.iter().map(|c| ArenaVec::from_slice(c)).collect()) }
            }).collect();
            // Identical transcript seeds expose any changed message or challenge.
            let mut original = ProverState::from_label(b"arbitrary-constraint-test");
            let expected = prove_reference(&airs, views(), &zeta, &sigma, &mut original);
            let mut fused = ProverState::from_label(b"arbitrary-constraint-test");
            let actual = prove(&airs, views(), &zeta, &sigma, &mut fused);
            // Invariant: even a false statement produces the same messages before rejection.
            prop_assert_eq!(actual, expected);
            prop_assert_eq!(fused.into_proof().stream, original.into_proof().stream);
        }
    }

    #[test]
    fn fused_rows_match_reference_transcript() {
        // Fixture state: ragged tables include constant tables and tables joining after several rounds.
        for taus in [&[5, 3, 5, 0, 1][..], &[14, 12, 8, 1][..]] {
            let (xi, mut zeta) = xi_zeta(taus);
            for endpoint in [F192::ZERO, F192::ONE, F192::new(7, 11, 13)] {
                // Exercise recovery of either endpoint, including the zero equality coordinate.
                zeta.fill(endpoint);
                let airs = airs_for(taus, true, xi);
                let cols: Vec<_> = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
                for extension in [false, true] {
                    let views = || {
                        cols.iter()
                            .map(|table| {
                                if extension {
                                    Columns::E(
                                        table
                                            .iter()
                                            .map(|c| {
                                                ArenaVec::from_iter(c.iter().map(|&v| F192::new(v.0, 3 * v.0, 7 * v.0)))
                                            })
                                            .collect(),
                                    )
                                } else {
                                    Columns::K(table.iter().map(|c| &c[..]).collect())
                                }
                            })
                            .collect()
                    };
                    let sigma: Vec<_> = (0..taus.len()).map(|i| F192::new(i as u64 + 1, 3, 5)).collect();
                    let mut reference = ProverState::from_label(b"fused-constraint-test");
                    let expected = prove_reference(&airs, views(), &zeta, &sigma, &mut reference);
                    let mut fused = ProverState::from_label(b"fused-constraint-test");
                    let actual = prove(&airs, views(), &zeta, &sigma, &mut fused);
                    // Invariant: reordering exact field operations preserves all messages and final claims.
                    assert_eq!(actual, expected);
                    assert_eq!(fused.into_proof().stream, reference.into_proof().stream);
                }
            }
        }
    }

    #[test]
    fn constant_tables_need_no_columns() {
        struct Constant;
        impl Summand for Constant {
            fn eval<T: ColVal>(&self, _: &[T], quadratic: bool) -> F192 {
                // A constant has no quadratic coefficient.
                if quadratic { F192::ZERO } else { F192::ONE }
            }
        }
        for tau in [0, 7] {
            // Fixture state: a constant summand sums to one under equality weights at any cube size.
            let airs = [Air {
                tau,
                n_cols: 0,
                n_public: 0,
                summand: Constant,
            }];
            let zeta = vec![F192::new(3, 5, 7); tau];
            let mut ps = ProverState::from_label(b"constant-column-free-test");
            let claims = prove(&airs, vec![Columns::K(vec![])], &zeta, &[F192::ONE], &mut ps);
            let proof = ps.into_proof();
            // No column evaluations are transmitted, but the constant still binds every round.
            let mut vs = VerifierState::from_label(b"constant-column-free-test", &proof);
            assert_eq!(verify(&airs, &zeta, F192::ONE, &mut vs).unwrap(), claims);
            vs.finish().unwrap();
        }
    }

    #[test]
    fn ragged_batch_verifies() {
        let taus = [5usize, 3, 5, 0, 1];
        let cols: Vec<Vec<Vec<F64>>> = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let claims = run(&taus, &cols).1.expect("honest batch verifies");
        let tallest = claims.iter().max_by_key(|c| c.chi.len()).unwrap().chi.clone();
        for (c, &tau) in claims.iter().zip(&taus) {
            assert_eq!(c.chi, tallest[..tau]);
        }
    }

    #[test]
    fn one_bad_row_in_any_table_is_rejected() {
        let taus = [5usize, 3, 5, 0, 1];
        for bad in 0..taus.len() {
            for col in [2usize, 3] {
                let mut cols: Vec<Vec<Vec<F64>>> =
                    taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
                cols[bad][col][(1usize << taus[bad]) - 1] += F64::ONE;
                assert!(run(&taus, &cols).1.is_err());
            }
        }
    }

    /// An ATTACHED evaluation claim: the extra identity's claimed
    /// sum is `η^2 · col_1(ζ[..τ])`, not zero, so the batch's target is nonzero and
    /// every table that has not joined yet rides a deferred line. Checks the honest
    /// batch verifies and that perturbing ANY table's claimed sum is caught,
    /// including a short table whose line is carried through most of the rounds.
    #[test]
    fn attached_eval_claims_verify_and_bind() {
        let taus = [5usize, 3, 5, 0, 1];
        let cols: Vec<Vec<Vec<F64>>> = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let (xi, zeta) = xi_zeta(&taus);
        let pows = powers(xi, 3 * taus.len());
        // σ_t = η^{offset_t + 2} · col_1(ζ[..τ_t]): the attached identity is `vals[1]`,
        // so its eq-weighted sum over the table's cube is that column's evaluation.
        let sigmas: Vec<F192> = taus
            .iter()
            .enumerate()
            .map(|(t, &tau)| pows[3 * t + 2] * primitives::multilinear::mle_eval(&cols[t][1], &zeta[..tau]))
            .collect();

        let settle = |sig: &[F192], cols: &[Vec<Vec<F64>>]| -> Result<Vec<Claims>, Error> {
            let airs = airs_for(&taus, true, xi);
            let target = sig.iter().fold(F192::ZERO, |a, &b| a + b);
            let mut ps = ProverState::from_label(b"zc-test");
            let views = cols
                .iter()
                .map(|t| Columns::K(t.iter().map(|c| &c[..]).collect()))
                .collect();
            let pclaims = prove(&airs, views, &zeta, sig, &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(b"zc-test", &proof);
            let out = verify(&airs, &zeta, target, &mut vs);
            if let Ok(vc) = &out {
                assert_eq!(&pclaims, vc);
            }
            out
        };
        settle(&sigmas, &cols).expect("honest attached claims verify");
        for bad in 0..taus.len() {
            let mut wrong = sigmas.clone();
            wrong[bad] += F192::ONE;
            assert!(
                settle(&wrong, &cols).is_err(),
                "a wrong claimed sum for table {bad} must be rejected"
            );
        }
    }

    /// Tampering any transmitted word breaks the chain: the batch is one sumcheck,
    /// so there is no per-table slack.
    #[test]
    fn tampered_transcript_is_rejected() {
        let taus = [4usize, 2, 4];
        let cols: Vec<Vec<Vec<F64>>> = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let (proof, ok) = run(&taus, &cols);
        assert!(ok.is_ok());
        let (xi, zeta) = xi_zeta(&taus);
        let airs = airs_for(&taus, false, xi);
        for i in 0..proof.stream.len() {
            let mut bad = proof.clone();
            bad.stream[i] += F192::ONE;
            let mut vs = VerifierState::from_label(b"zc-test", &bad);
            assert!(
                verify(&airs, &zeta, F192::ZERO, &mut vs).is_err(),
                "tampered word {i} must be rejected"
            );
        }
    }
}
