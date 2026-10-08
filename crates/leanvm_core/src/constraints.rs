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
use crate::colval::{ColVal, padded_width};
use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::transcript::{Challenger, ProverState, TranscriptError, Transmitter, VerifierState};
use parallel::Chunks;
use primitives::field::{F64, F192, F192Unreduced};
use primitives::multilinear::{SplitEq, eq_table, poly_eval, shrink_eq_high};
use std::ops::Deref;
use thiserror::Error;

mod rows;

/// One table's columns' evaluations at its table-sumcheck point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims<E = F192> {
    pub chi: Vec<E>,
    /// Every column's evaluation but the public ones', a bit column's made of its bits'.
    pub evals: Vec<E>,
    /// The bit columns' bits' evaluations, column after column, low bit first.
    pub slices: Vec<E>,
}

/// Why the table constraints reject.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ConstraintError {
    /// The bus point has fewer coordinates than the tallest table has variables.
    #[error("the bus point has {len} coordinates, and the tallest table has {rounds} variables")]
    PointTooShort { len: usize, rounds: usize },
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
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
    /// than reads: as many as the air's `n_public`. A caller may leave a part of them
    /// out, which the final identity's residual then owes.
    fn public(&self, _chi: &[F192]) -> Vec<F192> {
        Vec::new()
    }
}

/// A table's summand as the verifier evaluates it at the batch's point, over the verifier's arithmetic.
pub trait Residual<A: Arith> {
    /// The summand at its columns' values `cols`.
    fn value_at(&self, a: &mut A, cols: &[A::E]) -> A::E;

    /// The table's public columns at its point `chi`, as many as the air's `n_public`.
    ///
    /// A caller may leave a part of them out, which the final identity's residual then owes.
    fn public_at(&self, _a: &mut A, _chi: &[A::E]) -> Vec<A::E> {
        Vec::new()
    }
}

impl<S: Summand> Residual<VerifierState<'_>> for S {
    fn value_at(&self, _: &mut VerifierState<'_>, cols: &[F192]) -> F192 {
        Summand::eval(self, cols, false)
    }

    fn public_at(&self, _: &mut VerifierState<'_>, chi: &[F192]) -> Vec<F192> {
        Summand::public(self, chi)
    }
}

/// One table's place in the shared batch. Its last `n_public` columns are public: the
/// prover folds them like the rest, but sends none, and the verifier takes their values
/// at the point from [`Summand::public`].
pub struct Air<S> {
    pub tau: usize,
    pub n_cols: usize,
    pub n_public: usize,
    /// The columns whose evaluations are sent as their bits' evaluations.
    pub bits: BitColumns,
    pub summand: S,
}

/// Columns of small integers, each evaluation sent as the evaluations of its bits.
///
/// - Bit `b` of an integer is the element `x^b` of `K`, so a column is the `K`-linear combination of its bits.
/// - The bits are slices of a committed word, so the opening binds them by ring switching (§sec:regpack).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BitColumns {
    /// The columns, in the order their bits are sent.
    pub fields: Vec<BitField>,
}

/// A column of integers below `2^width`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitField {
    /// The column.
    pub col: usize,
    /// The bits it holds.
    pub width: usize,
}

impl BitColumns {
    /// How many bit evaluations the columns send.
    pub fn n_slices(&self) -> usize {
        self.fields.iter().map(|f| f.width).sum()
    }

    /// Row `x`'s values as one integer: each field in the bits after the previous ones, the first lowest.
    ///
    /// # Panics
    ///
    /// Panics if a value does not fit its width.
    pub fn packed(&self, cols: &[&[F64]], x: usize) -> u64 {
        let (packed, _) = self.fields.iter().fold((0, 0), |(packed, shift), f| {
            let value = cols[f.col][x].0;
            assert!(value >> f.width == 0, "a bit column's value fits its width");
            (packed | value << shift, shift + f.width)
        });
        packed
    }

    /// Each column's bits' evaluations at `point`, column after column, low bit first.
    ///
    /// One pass per column: rows are summed into one bucket per value, under the low half of `eq`.
    ///
    /// ```text
    ///     slice_b = sum_x eq(point, x) bit_b(col(x)) = sum_{v : bit_b(v)} sum_{x : col(x) = v} eq(point, x)
    /// ```
    fn slices(&self, cols: &[&[F64]], point: &[F192]) -> Vec<F192> {
        if self.fields.is_empty() {
            return Vec::new();
        }
        let eq = SplitEq::with_high_vars(point, point.len() / 2);
        let low = eq.low_log();
        self.fields
            .iter()
            .flat_map(|f| {
                let (col, values) = (cols[f.col], 1usize << f.width);
                let buckets = parallel::map_reduce(
                    eq.high.len(),
                    || vec![F192::ZERO; values],
                    |h| {
                        let mut run = vec![F192::ZERO; values];
                        for (x, value) in col[h << low..(h + 1) << low].iter().enumerate() {
                            run[value.0 as usize] += eq.low[x];
                        }
                        run.iter_mut().for_each(|b| *b *= eq.high[h]);
                        run
                    },
                    |mut a, b| {
                        a.iter_mut().zip(b).for_each(|(a, b)| *a += b);
                        a
                    },
                );
                (0..f.width).map(move |b| {
                    (buckets.iter().enumerate())
                        .filter(|(v, _)| v >> b & 1 == 1)
                        .fold(F192::ZERO, |acc, (_, &e)| acc + e)
                })
            })
            .collect()
    }

    /// The field on column `c`, and where its bits start among the slices.
    fn field_of(&self, c: usize) -> Option<(BitField, usize)> {
        let mut start = 0;
        for &f in &self.fields {
            if f.col == c {
                return Some((f, start));
            }
            start += f.width;
        }
        None
    }

    /// Send the evaluations: every column's but the public and the bit ones', then the bits'.
    fn send(&self, chi: &[F192], evals: Vec<F192>, slices: Vec<F192>, ps: &mut ProverState) -> Claims {
        let sent: Vec<F192> = (evals.iter().enumerate())
            .filter(|&(c, _)| self.field_of(c).is_none())
            .map(|(_, &e)| e)
            .collect();
        ps.add_scalars(&sent);
        ps.add_scalars(&slices);
        Claims {
            chi: chi.to_vec(),
            evals,
            slices,
        }
    }

    /// Read the evaluations `send` sent, rebuilding each bit column's from its bits.
    fn receive<V: Verifier>(&self, v: &mut V, chi: &[V::E], n_sent: usize) -> Result<Claims<V::E>, TranscriptError> {
        let mut sent = v.next_scalars(n_sent - self.fields.len())?.into_iter();
        let slices = v.next_scalars(self.n_slices())?;
        let mut evals = Vec::with_capacity(n_sent);
        for c in 0..n_sent {
            evals.push(self.field_of(c).map_or_else(
                || sent.next().expect("a sent evaluation per column"),
                |(f, start)| Self::combine(v, &slices[start..start + f.width]),
            ));
        }
        Ok(Claims {
            chi: chi.to_vec(),
            evals,
            slices,
        })
    }

    /// A column's evaluation from its bits': `sum_b x^b slice_b`.
    fn combine<A: Arith>(a: &mut A, bits: &[A::E]) -> A::E {
        let zero = a.zero();
        (bits.iter().enumerate()).fold(zero, |acc, (b, &bit)| {
            a.mul_const_add(bit, F192::from(F64(1 << b)), acc)
        })
    }
}

/// One table's columns as the prover hands them over: `K`-valued as committed, lifted
/// into `E` on the round the table joins, or `E`-valued from the start.
pub enum Columns<'a> {
    K(Vec<&'a [F64]>),
    E(Vec<Vec<F192>>),
}

/// An active round: one endpoint evaluation and the quadratic coefficient.
///
/// Generic in the column element: `K` before a table's columns are folded, `E` after.
///
/// `#[inline(always)]` matters here, on this and on
/// every `ColVal` method: this is the body of the constraint sumcheck's innermost
/// loop, and without it the generic stops inlining and costs measurable prover
/// time. Nothing is lifted into `E`, so a `K` round evaluates the identity and the
/// bus forms in 64-bit arithmetic, and its scratch is a third the size.
///
/// With `rows`, a row at a time ([`rows`]), else in tiles of [`BLOCK`] rows.
#[inline(always)]
fn table_message<T: ColVal, C: Deref<Target = [T]> + Sync>(
    cols: &[C],
    summand: &impl Summand,
    half: usize,
    eqr: &[F192],
    at_one: bool,
    rows: bool,
) -> [F192; 2] {
    if rows {
        return rows::table_message(cols, summand, half, eqr, at_one);
    }
    let width = padded_width(cols.len());
    let block = |scratch: &mut Vec<T>, acc: &mut [F192Unreduced; 2], b: usize| {
        let (start, rows) = (b * BLOCK, BLOCK.min(half - b * BLOCK));
        let (lo, rest) = scratch.split_at_mut(BLOCK * width);
        let (hi, slope) = rest.split_at_mut(BLOCK * width);
        // Column by column, each a burst of consecutive rows, into row-major tiles.
        for (c, col) in cols.iter().enumerate() {
            let rows_lo = &col[start..start + rows];
            let rows_hi = &col[start + half..start + half + rows];
            for (r, (&l, &h)) in rows_lo.iter().zip(rows_hi).enumerate() {
                lo[r * width + c] = l;
                hi[r * width + c] = h;
            }
        }
        block_summand(summand, &eqr[start..start + rows], lo, hi, slope, at_one, acc);
    };
    message_over_blocks(half, (2 * BLOCK + 1) * width, block)
}

/// Rows per block of a message pass: each column is read in bursts of this many
/// consecutive rows into row-major tiles, where a row at a time would keep a read
/// stream open per column. The tiles of a wide `E` row outgrow L1 at this size, and
/// still beat smaller ones.
const BLOCK: usize = 64;

/// Whether the message passes go a row at a time, as [`rows`] does: everywhere but
/// AVX-512, the only target whose packed forms take the tiles' padded rows. Elsewhere
/// the tiles lose to rows, on aarch64 at this block size and at L1-sized ones.
const ROWS: bool = !cfg!(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx512f"
));

/// The message over `rows` rows, `block(scratch, acc, b)` adding rows `b * BLOCK..`
/// with a zeroed `scratch` of `scratch_len` per worker.
fn message_over_blocks<T: ColVal>(
    rows: usize,
    scratch_len: usize,
    block: impl Fn(&mut Vec<T>, &mut [F192Unreduced; 2], usize) + Sync,
) -> [F192; 2] {
    let blocks = rows.div_ceil(BLOCK);
    let acc = if rows >= PAR_THRESHOLD {
        // The scratch is per worker, not per block: `map_reduce_with_state` creates it
        // once and threads it through every block that worker claims.
        parallel::map_reduce_with_state(
            blocks,
            || vec![T::ZERO; scratch_len],
            || [F192Unreduced::ZERO; 2],
            block,
            |a, b| [a[0] ^ b[0], a[1] ^ b[1]],
        )
    } else {
        let mut scratch = vec![T::ZERO; scratch_len];
        let mut acc = [F192Unreduced::ZERO; 2];
        for b in 0..blocks {
            block(&mut scratch, &mut acc, b);
        }
        acc
    };
    acc.map(F192Unreduced::reduce)
}

/// Add one block's summands: `lo` and `hi` hold its rows at stride `width`, padded
/// with zero columns, and `slope` is one row of scratch.
#[inline(always)]
fn block_summand<T: ColVal>(
    summand: &impl Summand,
    eqr: &[F192],
    lo: &[T],
    hi: &[T],
    slope: &mut [T],
    at_one: bool,
    acc: &mut [F192Unreduced; 2],
) {
    let width = slope.len();
    for (r, &e) in eqr.iter().enumerate() {
        let (l, h) = (&lo[r * width..(r + 1) * width], &hi[r * width..(r + 1) * width]);
        for ((s, &l), &h) in slope.iter_mut().zip(l).zip(h) {
            *s = l + h;
        }
        let endpoint = if at_one { h } else { l };
        // The quadratic coefficient depends only on the difference of the endpoint rows.
        acc[0] ^= e.mul_unreduced(summand.eval(endpoint, false));
        acc[1] ^= e.mul_unreduced(summand.eval(slope, true));
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
    prove_with(airs, cols, zeta, sigma, ps, ROWS)
}

/// [`prove`], its message passes a row at a time with `rows`, else in tiles.
fn prove_with<S: Summand>(
    airs: &[Air<S>],
    cols: Vec<Columns<'_>>,
    zeta: &[F192],
    sigma: &[F192],
    ps: &mut ProverState,
    rows: bool,
) -> Vec<Claims> {
    // The tallest table sets the common cube; shorter tables join after its high variables bind.
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    let mut weights = vec![F192::ONE; airs.len()];
    let mut eqr = eq_table(&zeta[..n.saturating_sub(1)]);
    let mut chi = vec![F192::ZERO; n];
    // A table's bit columns are read again at the end: their bits are sent, not their folded value.
    let bit_columns: Vec<Vec<&[F64]>> = (airs.iter().zip(&cols))
        .map(|(air, c)| match c {
            Columns::K(c) if !air.bits.fields.is_empty() => c.clone(),
            _ => Vec::new(),
        })
        .collect();
    // Borrow the committed columns until their joining round, then retain only folded rows.
    let mut pending: Vec<Option<Columns<'_>>> = cols.into_iter().map(Some).collect();
    let mut folded: Vec<Option<Vec<F192>>> = (0..airs.len()).map(|_| None).collect();
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
                    let at_one = zeta[m].is_zero();
                    match pending[t].as_ref().expect("a joining table has columns") {
                        Columns::K(c) => table_message(c, &air.summand, 1 << m, &eqr, at_one, rows),
                        Columns::E(c) => table_message(c, &air.summand, 1 << m, &eqr, at_one, rows),
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
                messages[t] = fold_rows_and_message(table, air.n_cols, rk, &air.summand, &eqr, at_one, rows);
            } else {
                let (table, message) = match pending[t].take().expect("a joining table has columns") {
                    Columns::K(c) => fold_columns_and_message(&c, rk, &air.summand, &eqr, at_one, rows),
                    Columns::E(c) => fold_columns_and_message(&c, rk, &air.summand, &eqr, at_one, rows),
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
            let slices = air.bits.slices(&bit_columns[t], &chi[..air.tau]);
            air.bits.send(&chi[..air.tau], evals, slices, ps)
        })
        .collect()
}

/// Fold blocks of row pairs and accumulate their next-round summands before publishing the rows.
///
/// `fold(start, rows, lo, hi)` writes the next low and high rows of `start..start + rows`
/// into the tiles `lo` and `hi`, row `r` at `r * padded_width(ncols)`.
fn folded_message(
    ncols: usize,
    eqr: &[F192],
    summand: &impl Summand,
    at_one: bool,
    fold: impl Fn(usize, usize, &mut [F192], &mut [F192]) + Sync,
) -> [F192; 2] {
    let width = padded_width(ncols);
    message_over_blocks(eqr.len(), (2 * BLOCK + 1) * width, |scratch: &mut Vec<F192>, acc, b| {
        let (start, rows) = (b * BLOCK, BLOCK.min(eqr.len() - b * BLOCK));
        let (lo, rest) = scratch.split_at_mut(BLOCK * width);
        let (hi, slope) = rest.split_at_mut(BLOCK * width);
        fold(start, rows, lo, hi);
        block_summand(summand, &eqr[start..start + rows], lo, hi, slope, at_one, acc);
    })
}

/// Convert the joining table's column layout into folded rows and its next message.
fn fold_columns_and_message<T: ColVal + Into<F192>, C: Deref<Target = [T]> + Sync>(
    cols: &[C],
    rk: F192,
    summand: &impl Summand,
    eqr: &[F192],
    at_one: bool,
    rows: bool,
) -> (Vec<F192>, Option<[F192; 2]>) {
    let ncols = cols.len();
    let half = cols[0].len() / 2;
    let mut out = Box::new_uninit_slice(half * ncols);
    let interp = |a: T, b: T| a.into() + (a + b).mul_e(rk);
    if half == 1 {
        // No next variable remains, so only the final evaluations are needed.
        for (c, dst) in cols.iter().zip(&mut out) {
            dst.write(interp(c[0], c[1]));
        }
        // SAFETY: one value per column fills the `ncols` slots.
        return (unsafe { out.assume_init() }.into_vec(), None);
    }
    let pairs = half / 2;
    if rows {
        let message = rows::fold_columns_and_message(cols, &mut out, rk, summand, eqr, at_one);
        // SAFETY: the `pairs` tasks wrote every row of both halves.
        return (unsafe { out.assume_init() }.into_vec(), Some(message));
    }
    let width = padded_width(ncols);
    let (lo, hi) = out.split_at_mut(pairs * ncols);
    let lo = Chunks::new(lo, BLOCK * ncols);
    let hi = Chunks::new(hi, BLOCK * ncols);
    let message = folded_message(ncols, eqr, summand, at_one, |start, rows, a, b| {
        for (c, col) in cols.iter().enumerate() {
            let at = |offset: usize| &col[start + offset..start + offset + rows];
            interp_column(&mut a[c..], width, rk, at(0), at(half));
            interp_column(&mut b[c..], width, rk, at(pairs), at(pairs + half));
        }
        // SAFETY: the task folding rows `start..` owns block `start / BLOCK` of each output half.
        let (lo, hi) = unsafe { (lo.get(start / BLOCK), hi.get(start / BLOCK)) };
        for r in 0..rows {
            lo[r * ncols..(r + 1) * ncols].write_copy_of_slice(&a[r * width..r * width + ncols]);
            hi[r * ncols..(r + 1) * ncols].write_copy_of_slice(&b[r * width..r * width + ncols]);
        }
    });
    // SAFETY: the `pairs` tasks wrote every row of both halves.
    (unsafe { out.assume_init() }.into_vec(), Some(message))
}

/// Fold row-major storage in place while building the next round's message from scratch.
fn fold_rows_and_message(
    table: &mut Vec<F192>,
    ncols: usize,
    rk: F192,
    summand: &impl Summand,
    eqr: &[F192],
    at_one: bool,
    rows: bool,
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
    if rows {
        let message = rows::fold_rows_and_message(table, ncols, rk, summand, eqr, at_one);
        table.truncate(half * ncols);
        return Some(message);
    }
    let width = padded_width(ncols);
    // Each task owns one block of rows in all four quarters, including its two output blocks.
    let (left, right) = table.split_at_mut(half * ncols);
    let (q0, q1) = left.split_at_mut(pairs * ncols);
    let (q2, q3) = right.split_at_mut(pairs * ncols);
    let [q0, q1, q2, q3] = [q0, q1, q2, q3].map(|q| Chunks::new(q, BLOCK * ncols));
    let message = folded_message(ncols, eqr, summand, at_one, |start, rows, a, b| {
        let k = start / BLOCK;
        // SAFETY: the task folding rows `start..` owns block `k` of every quarter.
        let (lo, hi, upper_lo, upper_hi) = unsafe { (q0.get(k), q1.get(k), q2.get(k), q3.get(k)) };
        for r in 0..rows {
            let row = r * ncols..(r + 1) * ncols;
            let (a, b) = (
                &mut a[r * width..r * width + ncols],
                &mut b[r * width..r * width + ncols],
            );
            interp_row(a, rk, &lo[row.clone()], &upper_lo[row.clone()]);
            interp_row(b, rk, &hi[row.clone()], &upper_hi[row.clone()]);
            // Read all four input rows before overwriting either output row.
            lo[row.clone()].copy_from_slice(a);
            hi[row].copy_from_slice(b);
        }
    });
    table.truncate(half * ncols);
    Some(message)
}

/// `out[r * stride] = lo[r] + (lo[r] + hi[r])·rk` down one column, eight rows per batched product.
#[inline(always)]
fn interp_column<T: ColVal + Into<F192>>(out: &mut [F192], stride: usize, rk: F192, lo: &[T], hi: &[T]) {
    let (lo8, lo_tail) = lo.as_chunks::<8>();
    let (hi8, hi_tail) = hi.as_chunks::<8>();
    for (g, (l, h)) in lo8.iter().zip(hi8).enumerate() {
        let products = T::mul_e8(std::array::from_fn(|j| l[j] + h[j]), rk);
        for j in 0..8 {
            out[(8 * g + j) * stride] = l[j].into() + products[j];
        }
    }
    for (j, (&l, &h)) in lo_tail.iter().zip(hi_tail).enumerate() {
        out[(8 * lo8.len() + j) * stride] = l.into() + (l + h).mul_e(rk);
    }
}

/// `out[c] = lo[c] + (lo[c] + hi[c])·rk` along one row, eight columns per batched product.
#[inline(always)]
fn interp_row(out: &mut [F192], rk: F192, lo: &[F192], hi: &[F192]) {
    for ((dst, lo), hi) in out.chunks_mut(8).zip(lo.chunks(8)).zip(hi.chunks(8)) {
        // A short last group is padded with zeros, whose products are dropped.
        let at = |s: &[F192], j: usize| s.get(j).copied().unwrap_or(F192::ZERO);
        let products = F192::mul_e8(std::array::from_fn(|j| at(lo, j) + at(hi, j)), rk);
        for (j, d) in dst.iter_mut().enumerate() {
            *d = lo[j] + products[j];
        }
    }
}

/// What the table sumcheck's verifier establishes.
///
/// - The per-table claims.
/// - The batch's final identity, short of whatever the caller left out of the public columns and the target.
pub struct Final<E = F192> {
    /// Per air, its column claims.
    pub claims: Vec<Claims<E>>,
    /// Each air's weight in the final identity: the eq weight of its point times the challenges of the rounds it sat out.
    pub weights: Vec<E>,
    /// The final claim plus every air's weighted summand at its columns.
    ///
    /// It is zero when the identity holds as the airs and the target stand.
    /// Otherwise it is what the parts the caller left out owe: an air's through its summand, the target's times its weight.
    pub residual: E,
    /// What the final claim moves by per unit of target.
    ///
    /// It is the product of the round challenges, since each round's claim fixes the linear coefficient of its polynomial.
    pub target_weight: E,
}

/// Verify the table sumcheck.
///
/// It returns the per-table claims, for the caller to settle against the commitment.
/// It returns the final identity's residual, for the caller to settle against what it left out.
///
/// # Errors
///
/// Returns an error if the bus point is shorter than the tallest table, or the stream is malformed.
pub fn verify<V: Verifier, S: Residual<V>>(
    v: &mut V,
    airs: &[Air<S>],
    zeta: &[V::E],
    target: V::E,
) -> Result<Final<V::E>, ConstraintError> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    if zeta.len() < n {
        return Err(ConstraintError::PointTooShort {
            len: zeta.len(),
            rounds: n,
        });
    }
    let one = v.one();
    let mut weights = vec![one; airs.len()];
    // An ordinary sumcheck for `target`, which the caller supplies. Each round
    // arrives as the round polynomial itself at `nd`, so the two steps are the
    // textbook ones and nothing has to be reapplied: no eq factor, no separate
    // waiting term. `ζ` and the heights enter only `weights`, never the check.
    let mut claim = target;
    let mut chi = vec![one; n];
    for j in 0..n {
        let m = n - 1 - j;
        // The running claim fixes the linear coefficient.
        let h = v.next_round_poly(4, claim, None)?;
        let rk = v.sample();
        chi[m] = rk;
        claim = v.poly_eval(&h, rk);
        // A table active in the round takes `eq = 1 + zeta_m + r`, one that sits it out takes `r`.
        let s = v.add(zeta[m], rk);
        for (w, air) in weights.iter_mut().zip(airs) {
            *w = if air.tau > m {
                v.times_one_plus(*w, s)
            } else {
                v.mul(*w, rk)
            };
        }
    }

    let mut residual = claim;
    let mut claims = Vec::with_capacity(airs.len());
    for (&weight, air) in weights.iter().zip(airs) {
        let table = air.bits.receive(v, &chi[..air.tau], air.n_cols - air.n_public)?;
        let mut values = table.evals.clone();
        values.extend(air.summand.public_at(v, &chi[..air.tau]));
        assert_eq!(values.len(), air.n_cols, "a table's public columns are all evaluated");
        let summand = air.summand.value_at(v, &values);
        residual = v.mul_add(weight, summand, residual);
        claims.push(table);
    }
    let target_weight = v.product(&chi);
    Ok(Final {
        claims,
        weights,
        residual,
        target_weight,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::transcript::ProofTranscript;
    use primitives::field::powers;
    use primitives::multilinear::{fold_high_inplace, fold_high_k, mle_eval};
    use primitives::test_util::Rng;
    use proptest::prelude::*;

    impl Final {
        // The claims, when nothing was left out.
        fn settle(self) -> Result<Vec<Claims>, ConstraintError> {
            if self.residual.is_zero() {
                Ok(self.claims)
            } else {
                Err(ConstraintError::FinalMismatch)
            }
        }
    }

    /// Reference prover with separate column-message and column-fold passes.
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
        let mut eqr = eq_table(&zeta[..n.saturating_sub(1)]);
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
                        || rows::table_message(&cols[t], &air.summand, 1 << m, &eqr, zeta[m].is_zero()),
                        |table| rows::table_message(table, &air.summand, 1 << m, &eqr, zeta[m].is_zero()),
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
                        let cols = Chunks::new(table, 1);
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
                let slices = air.bits.slices(&cols[t], &chi[..air.tau]);
                air.bits.send(&chi[..air.tau], evals, slices, ps)
            })
            .collect()
    }

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
            let eq = eq_table(&[F192::new(11, 13, 17), F192::new(19, 23, 29)]);
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
                let claim = (F192::ONE + zeta) * full_eval(F192::ZERO) + zeta * full_eval(F192::ONE) + waiting;
                for rows in [false, true] {
                    let message = table_message(cols, &synth, 4, &eq, zeta.is_zero(), rows);
                    let h = round_polynomial(message, zeta, claim, waiting);
                    for r in [F192::ZERO, F192::ONE, F192::new(31, 37, 41)] {
                        assert_eq!(poly_eval(&h, r), (F192::ONE + zeta + r) * full_eval(r) + r * waiting);
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
                bits: BitColumns::default(),
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

    fn run(taus: &[usize], cols: &[Vec<Vec<F64>>]) -> (ProofTranscript, Result<Vec<Claims>, ConstraintError>) {
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
        let vclaims = verify(&mut vs, &airs, &zeta, F192::ZERO).and_then(Final::settle);
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
                else { Columns::E(c.iter().map(|c| c.to_vec()).collect()) }
            }).collect();
            // Identical transcript seeds expose any changed message or challenge, in either pass shape.
            let mut original = ProverState::from_label(b"arbitrary-constraint-test");
            let expected = prove_reference(&airs, views(), &zeta, &sigma, &mut original);
            let stream = original.into_proof().stream;
            for rows in [false, true] {
                let mut fused = ProverState::from_label(b"arbitrary-constraint-test");
                let actual = prove_with(&airs, views(), &zeta, &sigma, &mut fused, rows);
                // Invariant: even a false statement produces the same messages before rejection.
                prop_assert_eq!(&actual, &expected);
                prop_assert_eq!(&fused.into_proof().stream, &stream);
            }
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
                                            .map(|c| c.iter().map(|&v| F192::new(v.0, 3 * v.0, 7 * v.0)).collect())
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
                    let stream = reference.into_proof().stream;
                    for rows in [false, true] {
                        let mut fused = ProverState::from_label(b"fused-constraint-test");
                        let actual = prove_with(&airs, views(), &zeta, &sigma, &mut fused, rows);
                        // Invariant: reordering exact field operations preserves all messages and final claims.
                        assert_eq!(actual, expected);
                        assert_eq!(fused.into_proof().stream, stream);
                    }
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
                bits: BitColumns::default(),
                summand: Constant,
            }];
            let zeta = vec![F192::new(3, 5, 7); tau];
            let mut ps = ProverState::from_label(b"constant-column-free-test");
            let claims = prove(&airs, vec![Columns::K(vec![])], &zeta, &[F192::ONE], &mut ps);
            let proof = ps.into_proof();
            // No column evaluations are transmitted, but the constant still binds every round.
            let mut vs = VerifierState::from_label(b"constant-column-free-test", &proof);
            assert_eq!(
                verify(&mut vs, &airs, &zeta, F192::ONE)
                    .and_then(Final::settle)
                    .unwrap(),
                claims
            );
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

        let settle = |sig: &[F192], cols: &[Vec<Vec<F64>>]| -> Result<Vec<Claims>, ConstraintError> {
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
            let out = verify(&mut vs, &airs, &zeta, target).and_then(Final::settle);
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
                verify(&mut vs, &airs, &zeta, F192::ZERO)
                    .and_then(Final::settle)
                    .is_err(),
                "tampered word {i} must be rejected"
            );
        }
    }

    #[test]
    fn a_bit_column_is_sent_as_its_bits() {
        // Fixture state: column 0 holds integers below 8, sent as its three bits' evaluations.
        let tau = 5;
        let mut cols = good_table(tau, 0);
        cols[0] = (0..1u64 << tau).map(|i| F64(i * 5 % 8)).collect();
        cols[2] = cols[0].iter().zip(&cols[1]).map(|(&a, &b)| a * b).collect();
        cols[3] = cols[0].clone();
        let (xi, zeta) = xi_zeta(&[tau]);
        let mut airs = airs_for(&[tau], false, xi);
        airs[0].bits = BitColumns {
            fields: vec![BitField { col: 0, width: 3 }],
        };
        let views = vec![Columns::K(cols.iter().map(|c| &c[..]).collect())];
        let mut ps = ProverState::from_label(b"zc-bits");
        let claims = prove(&airs, views, &zeta, &[F192::ZERO], &mut ps);
        let proof = ps.into_proof();

        // Each slice is its bit's evaluation at the table's point.
        for (b, &slice) in claims[0].slices.iter().enumerate() {
            let bit: Vec<F64> = cols[0].iter().map(|v| F64(v.0 >> b & 1)).collect();
            assert_eq!(slice, mle_eval(&bit, &claims[0].chi));
        }
        let verdict = |proof: &ProofTranscript| {
            let mut vs = VerifierState::from_label(b"zc-bits", proof);
            verify(&mut vs, &airs, &zeta, F192::ZERO).and_then(Final::settle)
        };
        assert_eq!(verdict(&proof), Ok(claims));

        // Mutation: one slice moved, which the column's rebuilt evaluation carries into the final identity.
        for at in proof.stream.len() - 3..proof.stream.len() {
            let mut bad = proof.clone();
            bad.stream[at] += F192::ONE;
            assert_eq!(verdict(&bad), Err(ConstraintError::FinalMismatch), "slice {at}");
        }
    }
}
