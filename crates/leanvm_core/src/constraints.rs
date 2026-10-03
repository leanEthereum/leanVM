//! The tables' local constraints (§sec:air), proven by one sumcheck for all tables,
//! the lookup arrays' producers among them.
//!
//! A table may fold identities with a DISJOINT range of one `η`'s powers, so the
//! batch is a polynomial in `η` whose coefficients are the individual sums and
//! matching the batch's target still pins each one. The instruction tables fold
//! none: what each attaches is its two bus forms, which SHARE their two powers
//! across tables, so those coefficients are per-side totals and the target pins the
//! total, which is all the bus needs. The forms' sums are the values the bus is
//! owed, so the target is those rather than zero. The verifier derives it from the
//! bus claims, and never reads it off the stream.
//!
//! Tables of different heights are combined by front-loaded batching: table `t`'s
//! summand is lifted onto the common `n`-cube by `∏_{i ≥ τ_t} X_i`, which leaves
//! its hypercube sum alone. Rounds bind `X_0` first, so every table active in a
//! round binds the same variable, and table `t` is done after round `τ_t − 1`. The
//! claims land on nested points `ρ[..τ_t]`.
//!
//! In a round after it is done, a table's variable reaches its summand once, through
//! the lifting product, so its contribution is degree 1 in that variable and
//! vanishes at 0: its folded summand times the challenges since. The round
//! polynomial is the cubic `eq(ζ_j, Y)·p(Y) + Y·u`. Its constant, quadratic and
//! cubic coefficients are sent; the running claim fixes the linear coefficient. The
//! verifier evaluates it at the challenge. Heights and `ζ` enter only the per-table
//! `weights`, which may be accumulated along the way or deferred to the end.
//!
//! Binding the low variable first is what keeps a table's padding implicit
//! (§sec:jagged): its rows from some index on repeat one row, and a fold maps such a
//! run to a run of the same row, so every round reads the live rows, about half as
//! many each time, and weighs the rest by their `eq` mass in closed form. Binding the
//! top first pairs a row with the one half a cube away, and once more than half the
//! cube is live its first fold leaves half a cube of distinct rows.
//!
//! The eq point is the caller's, not a fresh one (the bus's GKR point `ζ`), which
//! is what lets the forms' sums settle the bus. Batching derived in `doc/leanvm/main.tex`
//! §sec:air. Both sides take `n = max τ_t` from the announced heights.

use crate::PAR_THRESHOLD;
use crate::colval::ColVal;
use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192, F192Unreduced, mul_base8, mul4};
use primitives::multilinear::{eq_table, interp, interp_k, poly_eval, tail_weight};
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
/// Written once, generic over the column type: `K` before a table's first fold, `E`
/// after it (see [`ColVal`]).
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

/// One table's columns as the prover hands them over: each column's first rows, every
/// later row of the table's cube repeating its last (§sec:jagged). `K`-valued as
/// committed, lifted into `E` by the table's first fold, or `E`-valued from the start.
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

/// `log2` of the pairs a task sums against one entry of the high `eq` table.
const LO_LOG: usize = 10;

/// The pairs of a cube of `size` whose columns are `len` long, every later row
/// repeating the last: the pairs holding a live row. Every later pair is two copies
/// of the last row.
const fn live_pairs(len: usize, size: usize) -> usize {
    if len == size { size / 2 } else { (len - 1).div_ceil(2) }
}

/// An active round of one table: one endpoint evaluation and the quadratic
/// coefficient, against `eq(zeta, ·)` over the table's pairs, `zeta` the table's
/// variables past the one the round binds.
///
/// The pairs past [`live_pairs`] are the last row twice: their slope is zero, so they
/// add the summand at that row, weighed by their `eq` mass, to the endpoint alone.
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
    zeta: &[F192],
    at_one: bool,
) -> [F192; 2] {
    let ncols = cols.len();
    let len = cols[0].len();
    let size = 2usize << zeta.len();
    debug_assert!(cols.iter().all(|c| c.len() == len) && (1..=size).contains(&len));
    let pairs = live_pairs(len, size);
    // `eq(zeta, i) = lo[i mod 2^L]·hi[i >> L]`: a task sums its run of pairs against
    // `lo` and scales once by its entry of `hi`.
    let lo_log = zeta.len().min(LO_LOG);
    let (lo, hi) = (eq_table(&zeta[..lo_log]), eq_table(&zeta[lo_log..]));
    // The X² coefficient is Q(x0 + x1); linear and constant terms cannot contribute.
    let task = |scratch: &mut [T], run: usize| -> [F192; 2] {
        let first = run << lo_log;
        let mut acc = [F192Unreduced::ZERO; 2];
        for (i, &e) in (first..pairs.min(first + (1 << lo_log))).zip(&lo) {
            let (endpoint, slope) = scratch.split_at_mut(ncols);
            for (ci, c) in cols.iter().enumerate() {
                let (x0, x1) = (c[2 * i], c[2 * i + 1]);
                endpoint[ci] = if at_one { x1 } else { x0 };
                slope[ci] = x0 + x1;
            }
            acc[0] ^= e.mul_unreduced(summand.eval(endpoint, false));
            acc[1] ^= e.mul_unreduced(summand.eval(slope, true));
        }
        acc.map(|a| hi[run] * a.reduce())
    };
    let add = |a: [F192; 2], b: [F192; 2]| [a[0] + b[0], a[1] + b[1]];
    let runs = pairs.div_ceil(1 << lo_log);
    let mut message = if pairs >= PAR_THRESHOLD {
        // The `2 * ncols` scratch is per-worker, not per-run: `map_reduce_with_state`
        // creates it once and threads it through every run that worker claims.
        parallel::map_reduce_with_state(
            runs,
            || vec![T::ZERO; 2 * ncols],
            || [F192::ZERO; 2],
            |scratch, acc, run| *acc = add(*acc, task(scratch, run)),
            add,
        )
    } else {
        let mut scratch = vec![T::ZERO; 2 * ncols];
        (0..runs).fold([F192::ZERO; 2], |acc, run| add(acc, task(&mut scratch, run)))
    };
    if pairs < size / 2 {
        let last: Vec<T> = cols.iter().map(|c| c[len - 1]).collect();
        message[0] += tail_weight(zeta, pairs) * summand.eval(&last, false);
    }
    message
}

/// Bind a column's low variable to `chi`, lifting it into `E`: its live pairs fold,
/// and the run of the last row past them stays that row. Eight pairs share one
/// batched mixed product ([`mul_base8`]).
fn fold_low_k(column: &[F64], size: usize, chi: F192) -> ArenaVec<F192> {
    let pairs = live_pairs(column.len(), size);
    let mut out = ArenaVec::with_capacity(pairs + 1);
    let (pairs8, tail) = column[..2 * pairs].as_chunks::<16>();
    for x in pairs8 {
        let p = mul_base8(chi, std::array::from_fn(|i| x[2 * i] + x[2 * i + 1]));
        out.extend((0..8).map(|i| F192::from(x[2 * i]) + p[i]));
    }
    out.extend(tail.as_chunks::<2>().0.iter().map(|&[x0, x1]| interp_k(x0, x1, chi)));
    if column.len() < size {
        out.push(F192::from(column[column.len() - 1]));
    }
    out
}

/// [`fold_low_k`] of an `E` column, in place: the write index trails the read, and
/// four pairs share one batched product ([`mul4`]), read before any is written.
fn fold_low_inplace(column: &mut ArenaVec<F192>, size: usize, chi: F192) {
    let (len, pairs) = (column.len(), live_pairs(column.len(), size));
    let last = column[len - 1];
    {
        let c: &mut [F192] = column;
        let quads = pairs / 4;
        for q in 0..quads {
            let x: [F192; 8] = std::array::from_fn(|k| c[8 * q + k]);
            let p = mul4([chi; 4], std::array::from_fn(|i| x[2 * i] + x[2 * i + 1]));
            for i in 0..4 {
                c[4 * q + i] = x[2 * i] + p[i];
            }
        }
        for i in 4 * quads..pairs {
            c[i] = interp(c[2 * i], c[2 * i + 1], chi);
        }
    }
    if len < size {
        column[pairs] = last;
        column.truncate(pairs + 1);
    } else {
        column.truncate(pairs);
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
/// sumcheck over `max τ_t` variables. `cols[t]` holds table `t`'s involved columns
/// (see [`Columns`]). Returns the per-table claims, in input order, on the nested
/// points `ρ[..τ_t]`.
pub fn prove<S: Summand>(
    airs: &[Air<S>],
    cols: Vec<Columns<'_>>,
    zeta: &[F192],
    sigma: &[F192],
    ps: &mut ProverState,
) -> Vec<Claims> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    // η^{offset_t}, already inside each summand; the rounds then fold in the eq
    // factors and the challenges past the table, so `weights` is the whole per-table state.
    let mut weights = vec![F192::ONE; airs.len()];
    let mut chi = vec![F192::ZERO; n];
    // The folded tables are the batch's largest transients: one E-lifted copy of
    // every column of every still-active table. Arena-backed, so they are bumped
    // rather than mapped afresh each round. A table handed over in `E` starts here.
    let (cols, mut folded): (Vec<Vec<&[F64]>>, Vec<_>) = cols
        .into_iter()
        .map(|c| match c {
            Columns::K(k) => (k, None),
            Columns::E(e) => (Vec::new(), Some(e)),
        })
        .unzip();
    // A done table's summand at its point, which every later round's line carries.
    let value = |t: usize, folded: &[Option<Vec<ArenaVec<F192>>>]| {
        folded[t].as_ref().map_or_else(
            || {
                airs[t]
                    .summand
                    .eval(&cols[t].iter().map(|c| c[0]).collect::<Vec<F64>>(), false)
            },
            |table| {
                airs[t]
                    .summand
                    .eval(&table.iter().map(|c| c[0]).collect::<Vec<F192>>(), false)
            },
        )
    };
    let mut done: Vec<Option<F192>> = (0..airs.len())
        .map(|t| (airs[t].tau == 0).then(|| value(t, &folded)))
        .collect();
    let mut claim = sigma.iter().copied().fold(F192::ZERO, |a, b| a + b);
    for j in 0..n {
        // The done airs contribute the line `Y·u`, `u` their weighted summands. It is
        // NOT sent on its own: it folds into `h` below, and only `h` travels. `msg`
        // is the active airs' degree-2 cofactor, `h`'s multiplicand.
        let u = (weights.iter().zip(&done))
            .filter_map(|(&w, v)| Some(w * (*v)?))
            .fold(F192::ZERO, |acc, x| acc + x);
        let mut msg = [F192::ZERO; 2];
        for (t, air) in airs.iter().enumerate().filter(|(_, a)| a.tau > j) {
            let at_one = zeta[j].is_zero();
            let p = folded[t].as_ref().map_or_else(
                || table_message(&cols[t], &air.summand, &zeta[j + 1..air.tau], at_one),
                |table| table_message(table, &air.summand, &zeta[j + 1..air.tau], at_one),
            );
            for i in 0..2 {
                msg[i] += weights[t] * p[i];
            }
        }
        // The running claim recovers the missing endpoint of the quadratic cofactor.
        // The fold stays separate: its challenge only exists after this message is bound.
        let h = round_polynomial(msg, zeta[j], claim, u);
        ps.add_round_poly(&h, false);
        let rk = ps.sample();
        claim = poly_eval(&h, rk);
        chi[j] = rk;
        let eq_k = F192::ONE + zeta[j] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > j { eq_k } else { rk };
            if air.tau <= j {
                continue;
            }
            let size = 1usize << (air.tau - j);
            if let Some(table) = &mut folded[t] {
                if live_pairs(table[0].len(), size) >= PAR_THRESHOLD {
                    let cols = parallel::Chunks::new(table, 1);
                    parallel::for_each(cols.count(), |ci| {
                        // SAFETY: column `ci` is folded by exactly one task.
                        let col = unsafe { &mut cols.get(ci)[0] };
                        fold_low_inplace(col, size, rk);
                    });
                } else {
                    table.iter_mut().for_each(|c| fold_low_inplace(c, size, rk));
                }
            } else {
                // The first fold of a table is its largest, so it fans out like the
                // in-place ones above rather than running on the dispatcher alone.
                folded[t] = Some(parallel::map_collect(cols[t].len(), |ci| {
                    fold_low_k(cols[t][ci], size, rk)
                }));
            }
            if air.tau == j + 1 {
                done[t] = Some(value(t, &folded));
            }
        }
    }

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
        // The running claim fixes the linear coefficient.
        let h = vs.next_round_poly(4, claim, None)?;
        let rk = vs.sample();
        chi[j] = rk;
        claim = poly_eval(&h, rk);
        let eq_k = F192::ONE + zeta[j] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > j { eq_k } else { rk };
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

    /// One table's round, binding its low variable, on every jagged length of an
    /// 8-row cube (the padding row alone up to the whole cube), against the dense
    /// table it stands for, evaluated directly.
    #[test]
    fn round_coefficients_match_full_evaluations() {
        fn check<T: ColVal + Into<F192>>(cols: &[Vec<T>]) {
            let synth = Synth {
                pows: powers(F192::new(3, 5, 7), 3),
                attached: true,
                constant: F192::ONE,
            };
            let zeta = [F192::new(11, 13, 17), F192::new(19, 23, 29)];
            let eq = eq_table(&zeta);
            let waiting = F192::new(43, 47, 53);
            for len in 1..=8 {
                let jagged: Vec<Vec<T>> = cols.iter().map(|c| c[..len].to_vec()).collect();
                let row = |c: &[T], z: usize| -> F192 { c[z.min(len - 1)].into() };
                let full_eval = |r| {
                    (0..4).fold(F192::ZERO, |sum, i| {
                        let v: Vec<F192> = (jagged.iter())
                            .map(|c| interp(row(c, 2 * i), row(c, 2 * i + 1), r))
                            .collect();
                        sum + eq[i] * synth.eval(&v, false)
                    })
                };
                for z0 in [F192::ZERO, F192::ONE, F192::new(59, 61, 67)] {
                    let message = table_message(&jagged, &synth, &zeta, z0.is_zero());
                    let claim = (F192::ONE + z0) * full_eval(F192::ZERO) + z0 * full_eval(F192::ONE) + waiting;
                    let h = round_polynomial(message, z0, claim, waiting);
                    for r in [F192::ZERO, F192::ONE, F192::new(31, 37, 41)] {
                        assert_eq!(poly_eval(&h, r), (F192::ONE + z0 + r) * full_eval(r) + r * waiting);
                    }
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

    /// A fold of a jagged column, its rows past the stored ones read as the last, is the
    /// fold of the dense column it stands for, in `K` and in `E`, on every length.
    #[test]
    fn folds_keep_the_tail_implicit() {
        let chi = F192::new(5, 7, 11);
        let dense: Vec<F64> = (0..32u64).map(|i| F64(i * i + 3)).collect();
        for len in 1..=32 {
            let column = &dense[..len];
            let row = |z: usize| column[z.min(len - 1)];
            let want: Vec<F192> = (0..16).map(|i| interp_k(row(2 * i), row(2 * i + 1), chi)).collect();
            let padded = |folded: &[F192]| -> Vec<F192> { (0..16).map(|i| folded[i.min(folded.len() - 1)]).collect() };
            let k = fold_low_k(column, 32, chi);
            assert_eq!(padded(&k), want, "K fold of {len} rows");
            let mut e = ArenaVec::with_capacity(len);
            e.extend(column.iter().map(|&v| F192::from(v)));
            fold_low_inplace(&mut e, 32, chi);
            assert_eq!(&e[..], &k[..], "E fold of {len} rows");
        }
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
    /// every table already done rides a deferred line. Checks the honest
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

    /// Honest random tables of mixed heights `h`, each a table's committed rows (its
    /// live rows, then the padding row every later row repeats), and the dense cubes
    /// they stand for.
    fn jagged_and_padded(taus: &[usize], heights: &[usize], seed: u64) -> [Vec<Vec<Vec<F64>>>; 2] {
        let mut rng = primitives::test_rng::Rng::new(seed);
        let (jagged, padded) = (taus.iter().zip(heights))
            .map(|(&tau, &h)| {
                let rows = crate::cpu::committed_rows(h, tau);
                let a: Vec<F64> = (0..rows).map(|_| F64(rng.next_u64())).collect();
                let b: Vec<F64> = (0..rows).map(|_| F64(rng.next_u64())).collect();
                let ab = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
                let jagged = vec![a.clone(), b, ab, a];
                let padded = (jagged.iter())
                    .map(|c| (0..1 << tau).map(|z| c[z.min(rows - 1)]).collect())
                    .collect();
                (jagged, padded)
            })
            .unzip();
        [jagged, padded]
    }

    /// Heights from the padding row alone (`h = 0`) to a full cube, through `2^τ - 1`.
    const TAUS: [usize; 7] = [5, 3, 5, 0, 1, 4, 2];
    const HEIGHTS: [usize; 7] = [0, 7, 32, 0, 1, 9, 3];

    /// The batch on jagged tables sends what it sends on the dense cubes they stand for,
    /// round message for round message, with nonzero sums so that every done table's
    /// line is live, and its claims are those cubes' extensions.
    #[test]
    fn jagged_tables_prove_as_their_padded_cubes() {
        let [jagged, padded] = jagged_and_padded(&TAUS, &HEIGHTS, 11);
        let (xi, zeta) = xi_zeta(&TAUS);
        let airs = airs_for(&TAUS, true, xi);
        let pows = powers(xi, 3 * TAUS.len());
        let sigmas: Vec<F192> = (TAUS.iter().enumerate())
            .map(|(t, &tau)| pows[3 * t + 2] * primitives::multilinear::mle_eval(&padded[t][1], &zeta[..tau]))
            .collect();
        let proofs = [&jagged, &padded].map(|cols| {
            let mut ps = ProverState::from_label(b"zc-test");
            let views = (cols.iter())
                .map(|t| Columns::K(t.iter().map(|c| &c[..]).collect()))
                .collect();
            let claims = prove(&airs, views, &zeta, &sigmas, &mut ps);
            (ps.into_proof(), claims)
        });
        assert_eq!(proofs[0].0.stream, proofs[1].0.stream);
        assert_eq!(proofs[0].1, proofs[1].1);
        let target = sigmas.iter().fold(F192::ZERO, |a, &b| a + b);
        let mut vs = VerifierState::from_label(b"zc-test", &proofs[0].0);
        let claims = verify(&airs, &zeta, target, &mut vs).expect("honest jagged batch verifies");
        for (t, c) in claims.iter().enumerate() {
            for (col, &eval) in padded[t].iter().zip(&c.evals) {
                assert_eq!(eval, primitives::multilinear::mle_eval(col, &c.chi));
            }
        }
    }

    /// The padding row stands for every row from the height on: one that breaks an
    /// identity is caught however many rows it stands for, and a prover summing a cube
    /// whose tail differs from it either breaks an identity there or leaves claims the
    /// committed rows' extension does not meet.
    #[test]
    fn a_tampered_padding_row_or_tail_is_rejected() {
        let [jagged, padded] = jagged_and_padded(&TAUS, &HEIGHTS, 13);
        for (t, &h) in HEIGHTS.iter().enumerate().filter(|&(t, &h)| h + 1 < 1 << TAUS[t]) {
            let mut bad = jagged.clone();
            bad[t][2][h] += F64::ONE;
            assert!(
                run(&TAUS, &bad).1.is_err(),
                "table {t}'s padding row breaks an identity"
            );

            let last = (1 << TAUS[t]) - 1;
            let mut bad = padded.clone();
            bad[t][2][last] += F64::ONE;
            assert!(run(&TAUS, &bad).1.is_err(), "table {t}'s tail breaks an identity");

            let mut other = padded.clone();
            let a = other[t][0][last] + F64::ONE;
            (other[t][0][last], other[t][2][last], other[t][3][last]) = (a, a * other[t][1][last], a);
            let claims = run(&TAUS, &other)
                .1
                .expect("an honest tail row satisfies the identities");
            let committed = |c: &[F64]| primitives::multilinear::mle_eval(c, &claims[t].chi);
            assert!(
                (padded[t].iter().zip(&claims[t].evals)).any(|(c, &eval)| eval != committed(c)),
                "table {t}'s claims are not on the committed rows"
            );
        }
    }
}
