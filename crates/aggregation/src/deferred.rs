//! The deferred claim on the split program and the sumcheck that batches it.

use super::cells::count;
use super::hints::SubHints;
use super::split::{SPLIT_LOG, split_live, split_table, split_values};
use fiat_shamir_prover::{FiatShamirState, RATE_SCALARS, Sequential, grinding_bits};
use isa::Prover;
use lean_vm_core::cpu::{from_scalar, to_scalar};
use primitives::field::{F64, F128, F128Unreduced};
// `eq` tables on the calling thread: the batch runs under either prover, some of it in its pool's tasks.
use primitives::multilinear::{eq_table_serial as eq_table, interp};
use std::ops::Range;

pub(super) const RECURSION_AGG_LABEL: &[u8] = b"leanvm/recursion-aggregation/v1";

/// The claim on the split program ([`split_table`]) that a node defers rather than evaluating in-circuit: one point
/// and value (§sec:deferred-claims).
///
/// Only the point is transmitted; the value is derived from it on receipt, so a
/// prover that lies about a value changes the statement its proof has to satisfy
/// rather than the claim anyone checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DeferredBytecodeClaim {
    pub(super) bytecode_point: Vec<F128>,
    pub(super) bytecode_value: F128,
}

impl DeferredBytecodeClaim {
    /// What a leaf defers: the all-zeros point, where the value is just the
    /// table's first entry.
    pub(super) fn leaf() -> Self {
        Self::recompute(vec![F128::ZERO; bytecode_vars()])
    }

    /// The claim at `bytecode_point`, its value read off the point's [`bytecode_sums`].
    pub(super) fn from_sums(bytecode_point: Vec<F128>, sums: &[F128]) -> Self {
        let bytecode_value = bytecode_value_of(sums, &bytecode_point);
        Self {
            bytecode_point,
            bytecode_value,
        }
    }

    /// The claim at `bytecode_point`, a point of [`bytecode_vars`] coordinates (the instructions', then the split
    /// columns'), evaluated by the `verifier` crate, scalar and single threaded: what a received aggregate is checked
    /// with.
    pub(super) fn recompute(bytecode_point: Vec<F128>) -> Self {
        // Every leaf defers the all-zeros point, where the table is just its first entry: a leaf is the aggregate
        // people verify most, and the general path is a pass over the program.
        let bytecode_value = if bytecode_point.iter().all(|x| *x == F128::ZERO) {
            F128::new(split_table()[0], 0)
        } else {
            let (row, column) = bytecode_point.split_at(bytecode_vars() - SPLIT_LOG);
            let scalars: Vec<_> = row.iter().map(to_scalar).collect();
            fold_columns(
                column,
                &split_values(&scalars).into_iter().map(from_scalar).collect::<Vec<_>>(),
            )
        };
        Self {
            bytecode_point,
            bytecode_value,
        }
    }

    /// The cells the statement digest absorbs, in the guest's `defer_stmt` order.
    pub(super) fn cells(&self) -> Vec<F128> {
        let mut cells = self.bytecode_point.clone();
        cells.push(self.bytecode_value);
        cells
    }
}

/// The claim a child's verification raises: the split columns' values at its link point's instruction coordinates.
#[derive(Clone, Debug)]
pub(super) struct FreshClaim {
    pub(super) point: Vec<F128>,
    pub(super) values: Vec<F128>,
}

impl FreshClaim {
    /// The split columns at `point`, a point over the instructions.
    pub(super) fn at(point: Vec<F128>) -> Self {
        let scalars: Vec<_> = point.iter().map(to_scalar).collect();
        let values = split_values(&scalars).into_iter().map(from_scalar).collect();
        Self { point, values }
    }

    /// The cells the batch absorbs: the point, then the values.
    fn cells(&self) -> Vec<F128> {
        [&self.point[..], &self.values[..]].concat()
    }
}

/// `Σ_j eq(column, j)·values[j]`: the split columns' values folded at the column point.
fn fold_columns(column: &[F128], values: &[F128]) -> F128 {
    eq_table(column).iter().zip(values).map(|(&e, &v)| e * v).sum()
}

/// The rows of [`BLOCK`] entries of the split table that hold its live columns: every other row is zero.
fn bytecode_rows() -> Range<usize> {
    static ROWS: std::sync::OnceLock<Range<usize>> = std::sync::OnceLock::new();
    ROWS.get_or_init(|| {
        let rows = split_table().len() / BLOCK;
        let per_column = rows >> SPLIT_LOG;
        assert!(
            per_column.is_multiple_of(8),
            "a column is whole groups of rows, as `Prover::combine_rows` may require"
        );
        0..split_live() * per_column
    })
    .clone()
}

/// Low row variables of the split table, which the batch binds first.
const BLOCK_VARS: usize = 10;
const BLOCK: usize = 1 << BLOCK_VARS;

/// Per claim point, the split table with the point's weight on all but the low `BLOCK_VARS` variables summed
/// out: `G(low) = Σ_r eq(point[BLOCK_VARS..], r) · row_r[low]`, over rows `r` of `BLOCK` entries. The weight
/// `eq(point, ·)` is a product of a factor on the low variables and one on the rest, so the batch's low rounds run
/// on these, and a point's value is read off its own (`bytecode_value_of`).
pub(super) fn bytecode_sums<P: Prover>(points: &[Vec<F128>]) -> Vec<Vec<F128>> {
    let _span = tracing::info_span!("Bytecode sums").entered();
    let (table, live) = (split_table(), bytecode_rows());
    points
        .iter()
        .map(|point| {
            // A leaf's claim weighs the first row alone.
            if point.iter().all(|&x| x == F128::ZERO) {
                return table[..BLOCK].iter().map(|&w| F128::new(w, 0)).collect();
            }
            let eq: Vec<_> = eq_table(&point[BLOCK_VARS..])[live.clone()]
                .iter()
                .map(to_scalar)
                .collect();
            let sums = P::combine_rows(&table[live.start * BLOCK..live.end * BLOCK], &eq);
            sums.into_iter().map(from_scalar).collect()
        })
        .collect()
}

/// The split table's nonzero entries, instruction by instruction, each its column and value.
struct SplitEntries {
    /// Instruction `k`'s entries are `entries[starts[k]..starts[k + 1]]`.
    starts: Vec<u32>,
    entries: Vec<(u8, u64)>,
}

impl SplitEntries {
    fn get() -> &'static Self {
        static ENTRIES: std::sync::OnceLock<SplitEntries> = std::sync::OnceLock::new();
        ENTRIES.get_or_init(|| {
            let table = split_table();
            let n = table.len() >> SPLIT_LOG;
            let (mut starts, mut entries) = (vec![0u32], Vec::new());
            for k in 0..n {
                entries.extend((0..1usize << SPLIT_LOG).filter_map(|j| {
                    let v = table[j * n + k];
                    (v != 0).then_some((j as u8, v))
                }));
                starts.push(entries.len() as u32);
            }
            SplitEntries { starts, entries }
        })
    }

    /// The instructions.
    fn len(&self) -> usize {
        self.starts.len() - 1
    }

    /// Instruction `k`'s entries.
    fn of(&self, k: usize) -> &[(u8, u64)] {
        &self.entries[self.starts[k] as usize..self.starts[k + 1] as usize]
    }
}

/// [`bytecode_sums`] for points that share their column coordinates, `column`: the table's columns folded at them
/// once, then each point's instruction rows against that fold.
fn fresh_sums<P: Prover>(points: &[Vec<F128>], column: &[F128]) -> Vec<Vec<F128>> {
    let _span = tracing::info_span!("Bytecode sums").entered();
    let split = SplitEntries::get();
    let n = split.len();
    let eq_col = eq_table(column);
    // The fold, `CHUNK` instructions a task.
    const CHUNK: usize = 1 << 13;
    assert!(n.is_multiple_of(CHUNK), "{n} instructions, not whole tasks of {CHUNK}");
    let folded: Vec<F128> = P::map_collect(n / CHUNK, |c| {
        (c * CHUNK..(c + 1) * CHUNK)
            .map(|k| {
                (split.of(k).iter())
                    .fold(F128Unreduced::ZERO, |acc, &(j, v)| {
                        acc ^ eq_col[j as usize].mul_base_unreduced(F64(v))
                    })
                    .reduce()
            })
            .collect::<Vec<_>>()
    })
    .concat();
    // A task per point and run of `PART` low entries, summed unreduced.
    const PART: usize = BLOCK / 4;
    let eq_his: Vec<Vec<F128>> = (points.iter())
        .map(|point| {
            assert!(
                point[point.len() - SPLIT_LOG..] == *column,
                "a fresh point ends in the column challenges"
            );
            eq_table(&point[BLOCK_VARS..point.len() - SPLIT_LOG])
        })
        .collect();
    let parts = P::map_collect(points.len() * (BLOCK / PART), |task| {
        let (p, part) = (task / (BLOCK / PART), task % (BLOCK / PART));
        let mut acc = [F128Unreduced::ZERO; PART];
        for (&e, row) in eq_his[p].iter().zip(folded.as_chunks::<BLOCK>().0) {
            for (a, &v) in acc.iter_mut().zip(&row[part * PART..(part + 1) * PART]) {
                *a ^= e.mul_unreduced(v);
            }
        }
        acc.map(F128Unreduced::reduce)
    });
    parts.chunks(BLOCK / PART).map(|p| p.concat()).collect()
}

/// The split table at `point`, from its [`bytecode_sums`].
fn bytecode_value_of(sums: &[F128], point: &[F128]) -> F128 {
    eq_table(&point[..BLOCK_VARS])
        .iter()
        .zip(sums)
        .map(|(&eq, &sum)| eq * sum)
        .sum()
}

/// Variables of a deferred claim's point: the instructions', then the split columns'.
pub(super) fn bytecode_vars() -> usize {
    split_table().len().trailing_zeros() as usize
}

fn fold_lsb(table: &mut Vec<F128>, challenge: F128) {
    let half = table.len() / 2;
    for i in 0..half {
        table[i] = interp(table[2 * i], table[2 * i + 1], challenge);
    }
    table.truncate(half);
}

/// Compressed product-sumcheck round message of `u·m`: (g1, g∞) with g0 recovered from the
/// running claim.
fn round_msg(u: &[F128], m: &[F128]) -> (F128, F128) {
    (0..u.len() / 2).fold((F128::ZERO, F128::ZERO), |acc, i| {
        let (u0, u1) = (u[2 * i], u[2 * i + 1]);
        let (m0, m1) = (m[2 * i], m[2 * i + 1]);
        (acc.0 + u1 * m1, acc.1 + (u0 + u1) * (m0 + m1))
    })
}

/// The grind before the batching challenges: the powers of `lam` weigh at most `2 MAX_RECURSIONS` claims, and
/// each fresh claim's values are folded at the `SPLIT_LOG` column challenges.
pub(super) const BATCH_LAM_GRIND_BITS: u32 = grinding_bits((2 * super::MAX_RECURSIONS - 1 + SPLIT_LOG) as u128);

/// One round of a batching sumcheck, in the transcript order the guest mirrors
/// word for word: observe `(g1, g_inf)`, grind for the round's degree two, squeeze the fold challenge, record
/// the two words and the nonce, if the grind sends one, and advance the running claim through the compressed round polynomial.
/// Returns the challenge, which the caller folds its tables with.
fn absorb_round(
    transcript: &mut FiatShamirState<F128>,
    messages: &mut Vec<F128>,
    challenges: &mut Vec<F128>,
    claim: &mut F128,
    (g1, gi): (F128, F128),
) -> F128 {
    transcript.observe(g1);
    transcript.observe(gi);
    let nonce = transcript.grind::<Sequential>(grinding_bits(2));
    let challenge = transcript.sample();
    messages.extend([g1, gi]);
    messages.extend(nonce.map(|nonce| F128::new(nonce, 0)));
    challenges.push(challenge);
    let g0 = *claim + g1;
    let c1 = g0 + g1 + gi;
    *claim = (gi * challenge + c1) * challenge + g0;
    challenge
}

/// Mirror the guest's `aggregate_claims` transcript and prove the batching sumcheck over the split table.
///
/// Each child brings its public input and two claims, the fresh one its verification raised and the one it deferred;
/// `carried_sums` are the carried ones' [`bytecode_sums`]. After the batch absorbs them all, `lam` and the column
/// challenges turn each fresh claim into one at its point and the column challenges. A child's fresh claim is
/// batched with its carried one at every child count, one included. Returns the guest hints and the single claim they
/// reduce to.
pub(super) fn aggregate_deferred_claims<P: Prover>(
    public_inputs: &[[F128; 2]],
    fresh: &[FreshClaim],
    carried: &[DeferredBytecodeClaim],
    carried_sums: Vec<Vec<F128>>,
) -> (SubHints, DeferredBytecodeClaim) {
    let kbcv = bytecode_vars();

    // The count and each child's words are padded with zeros to whole rates, so the
    // guest's loop over the children finds every child starting the same way.
    let mut transcript = FiatShamirState::from_label(RECURSION_AGG_LABEL);
    let pad = |transcript: &mut FiatShamirState<F128>, n: usize| {
        for _ in 0..n.next_multiple_of(RATE_SCALARS) - n {
            transcript.observe(F128::ZERO);
        }
    };
    transcript.observe(count(public_inputs.len()));
    pad(&mut transcript, 1);
    for ((public_input, fresh), carried) in public_inputs.iter().zip(fresh).zip(carried) {
        let words: Vec<F128> = public_input
            .iter()
            .copied()
            .chain(fresh.cells())
            .chain(carried.cells())
            .collect();
        for &value in &words {
            transcript.observe(value);
        }
        pad(&mut transcript, words.len());
    }

    let _span = tracing::info_span!("Bytecode batch", vars = kbcv).entered();
    // Powers of one challenge: child i's fresh claim takes lam^(2i), its carried one lam^(2i+1). The batch's grinds
    // are short, so they search on the calling thread, under either prover.
    let nonce = transcript.grind::<Sequential>(BATCH_LAM_GRIND_BITS);
    let lam = transcript.sample();
    let column: Vec<F128> = (0..SPLIT_LOG).map(|_| transcript.sample()).collect();
    let fresh_points: Vec<Vec<F128>> = fresh.iter().map(|f| [&f.point[..], &column[..]].concat()).collect();
    let fresh_sums = fresh_sums::<P>(&fresh_points, &column);
    let mut claims = Vec::with_capacity(2 * fresh.len());
    let mut sums = Vec::with_capacity(2 * fresh.len());
    for ((((point, f), fs), c), cs) in fresh_points
        .into_iter()
        .zip(fresh)
        .zip(fresh_sums)
        .zip(carried)
        .zip(carried_sums)
    {
        let bytecode_value = fold_columns(&column, &f.values);
        debug_assert_eq!(bytecode_value, bytecode_value_of(&fs, &point));
        claims.push(DeferredBytecodeClaim {
            bytecode_point: point,
            bytecode_value,
        });
        sums.push(fs);
        claims.push(c.clone());
        sums.push(cs);
    }
    let powers: Vec<F128> = std::iter::successors(Some(F128::ONE), |&power| Some(power * lam))
        .take(claims.len())
        .collect();
    let mut claim: F128 = powers.iter().zip(&claims).map(|(&g, c)| g * c.bytecode_value).sum();
    let mut messages: Vec<F128> = nonce.map(|nonce| F128::new(nonce, 0)).into_iter().collect();
    let mut challenges = Vec::new();
    // The low rounds, on each claim's sums against its `eq` on the low rows, scaled by its power of `lam`.
    let mut low_weights: Vec<Vec<F128>> = claims
        .iter()
        .zip(&powers)
        .map(|(c, &power)| {
            eq_table(&c.bytecode_point[..BLOCK_VARS])
                .into_iter()
                .map(|eq| power * eq)
                .collect()
        })
        .collect();
    for _ in 0..BLOCK_VARS {
        let msg = sums
            .iter()
            .zip(&low_weights)
            .fold((F128::ZERO, F128::ZERO), |acc, (sums, weights)| {
                let (g1, gi) = round_msg(sums, weights);
                (acc.0 + g1, acc.1 + gi)
            });
        let r = absorb_round(&mut transcript, &mut messages, &mut challenges, &mut claim, msg);
        for table in sums.iter_mut().chain(&mut low_weights) {
            fold_lsb(table, r);
        }
    }
    // The rest: every row against the low challenges, zero outside the populated ones, and each claim's `eq` on
    // the rows, scaled by what its low rows left.
    // Row `j·(n / BLOCK) + h` of column `j`, from the nonzero entries, a task per instruction row `h`.
    let split = SplitEntries::get();
    let n = split.len();
    let low_eq = eq_table(&challenges);
    let dots = P::map_collect(n / BLOCK, |h| {
        let mut acc = [F128Unreduced::ZERO; 1 << SPLIT_LOG];
        for (k, &e) in (h * BLOCK..(h + 1) * BLOCK).zip(&low_eq) {
            for &(j, v) in split.of(k) {
                acc[j as usize] ^= e.mul_base_unreduced(F64(v));
            }
        }
        acc.map(F128Unreduced::reduce)
    });
    let mut rows = vec![F128::ZERO; n << SPLIT_LOG >> BLOCK_VARS];
    for (h, dot) in dots.iter().enumerate() {
        for (j, &d) in dot.iter().enumerate() {
            rows[j * (n / BLOCK) + h] = d;
        }
    }
    let mut weights = vec![F128::ZERO; rows.len()];
    for (c, low_weight) in claims.iter().zip(&low_weights) {
        for (weight, eq) in weights.iter_mut().zip(eq_table(&c.bytecode_point[BLOCK_VARS..])) {
            *weight += low_weight[0] * eq;
        }
    }
    for _ in BLOCK_VARS..kbcv {
        let msg = round_msg(&rows, &weights);
        let r = absorb_round(&mut transcript, &mut messages, &mut challenges, &mut claim, msg);
        fold_lsb(&mut rows, r);
        fold_lsb(&mut weights, r);
    }
    let value = rows[0];
    assert_eq!(
        claim,
        value * weights[0],
        "every claim's value is the bytecode's evaluation"
    );

    drop(_span);
    let hints = vec![("bc_sumcheck_msgs", messages), ("bc_star_hint", vec![value])];
    let reduced = DeferredBytecodeClaim {
        bytecode_point: challenges,
        bytecode_value: value,
    };
    (hints, reduced)
}
