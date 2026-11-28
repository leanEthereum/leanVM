//! Phase 7b: the stacked opening (`NativeVm/Model/Whir.lean`), with the ladder of the statement's
//! parameter table (`Whir.ladder`).

use crate::buf::Buf;
use crate::data::{QUERY_LEVELS, QUERY_TABLE};
use crate::field::{EW, ONE, ZERO, eq_eval, kinv, kmul, multilinear_eval, powers};
use crate::keccak_gkr::KeccakOutW;
use crate::layout::{LayoutW, MAX_LOG_STACK, MIN_LOG_STACK, QKECCAK};
use crate::ring_switch::RingW;
use crate::stack::{ClaimsW, EqClaimW, STACK_CAP, column_weight, level_shape, on_stack, ring_claim_weight};
use crate::transcript::{Rows, TState, require};

/// `Whir.queryGrindingBits`, `foldGrindingBits`, `batchGrindingBits`, `oodGrindingBits`.
pub const QUERY_GRINDING_BITS: u32 = 17;
pub const FOLD_GRINDING_BITS: u32 = 7;
pub const BATCH_GRINDING_BITS: u32 = 13;
pub const OOD_GRINDING_BITS: u32 = 15;
/// `Whir.initialFold`, `subsequentFold`, `initialReduction`, `subsequentReduction`,
/// `residualMaxLog`.
const INITIAL_FOLD: usize = 6;
const SUBSEQUENT_FOLD: usize = 4;
const INITIAL_REDUCTION: usize = 3;
const SUBSEQUENT_REDUCTION: usize = 1;
const RESIDUAL_MAX_LOG: usize = 5;
/// `maxStackedClaims`.
const MAX_STACKED_CLAIMS: usize = 512;
/// `levelCap`: the longest ladder.
pub const LEVEL_CAP: usize = 6;
/// `queryCap`: a level's query positions.
pub const QUERY_CAP: usize = 230;
/// `gluedCap`: two glued claims per non-final level.
const GLUED_CAP: usize = 2 * (LEVEL_CAP - 1);
/// `roundCap`: a level's fold rounds.
const ROUND_CAP: usize = INITIAL_FOLD;
/// `stackClaimCap`: the ring-switched claim, every column claim, the out-of-domain one.
pub const STACK_CLAIM_CAP: usize = crate::stack::CLAIM_CAP + 2;
/// The lanes of an opened row: `2^initialFold` at level `0`.
const LANE_CAP: usize = 1 << INITIAL_FOLD;
/// The final level's folded lane, `2^μ + fold` scalars.
const FOLDED_CAP: usize = 64;
/// The roots of `subspaceRoots μ`, `μ + 1`.
const ROOT_CAP: usize = MAX_LOG_STACK + 1;

/// `Whir.Level`: its fold rounds, its rate exponent, its query count.
#[derive(Clone, Copy, Default)]
#[repr(C)]
pub struct Level {
    pub fold: usize,
    pub log_inv_rate: usize,
    pub queries: usize,
}

/// `Whir.ladder μ logInvRate`: the levels and their count; `None` outside the window or when the
/// table has not one count per level. The geometry is `ladderShape` (`levelsFrom`).
#[inline(never)]
pub fn ladder(mu: usize, log_inv_rate: usize) -> Option<([Level; LEVEL_CAP], usize)> {
    require((MIN_LOG_STACK..=MAX_LOG_STACK).contains(&mu) && (1..=4).contains(&log_inv_rate))?;
    let mut levels = [Level::default(); LEVEL_CAP];
    let mut n = 0;
    let mut push = |fold, rate| -> Option<()> {
        *levels.get_mut(n)? = Level { fold, log_inv_rate: rate, queries: 0 };
        n += 1;
        Some(())
    };
    push(INITIAL_FOLD, log_inv_rate)?;
    // `levelsFrom μ (μ - initialFold) initialFold logInvRate initialReduction`.
    let (mut remaining, mut prev_fold, mut prev_rate, mut reduction) =
        (mu - INITIAL_FOLD, INITIAL_FOLD, log_inv_rate, INITIAL_REDUCTION);
    for _ in 0..mu {
        if remaining <= RESIDUAL_MAX_LOG {
            break;
        }
        let rate = (prev_rate + prev_fold).saturating_sub(reduction);
        let fold = SUBSEQUENT_FOLD.min(remaining);
        push(fold, rate)?;
        (remaining, prev_fold, prev_rate, reduction) = (remaining - fold, fold, rate, SUBSEQUENT_REDUCTION);
    }
    let row = QUERY_TABLE.get(log_inv_rate - 1)?.get(mu - MIN_LOG_STACK)?;
    let count = *QUERY_LEVELS.get(log_inv_rate - 1)?.get(mu - MIN_LOG_STACK)?;
    require(count == n)?;
    for (level, &q) in levels.iter_mut().zip(row).take(n) {
        level.queries = q as usize;
    }
    Some((levels, n))
}

/// `queryBits c shift depth`: `(bits >>> shift) % 2^depth` of the challenge's 128-bit integer.
#[inline(never)]
fn query_bits(c: EW, shift: usize, depth: usize) -> u64 {
    let v = if shift == 0 {
        c.c0
    } else if shift < 64 {
        (c.c0 >> shift) | (c.c1 << (64 - shift))
    } else if shift < 128 {
        c.c1 >> (shift - 64)
    } else {
        0
    };
    if depth >= 64 { v } else { v & ((1u64 << depth) - 1) }
}

/// `128 / d` for `d ≤ 128` (`0` at `0`), by table: no division instruction (`div`), which Kraken's
/// x86-64 lacks.
const PER_CHALLENGE: [u8; 129] = {
    let mut table = [0u8; 129];
    let mut d = 1;
    while d < 129 {
        table[d] = (128 / d) as u8;
        d += 1;
    }
    table
};

/// `sampleQueries depth count` (`sampleQueriesAux`).
#[inline(never)]
fn sample_queries(t: &mut TState, depth: usize, count: usize, out: &mut Buf<u64, QUERY_CAP>) -> Option<()> {
    out.clear();
    let mut remaining = count;
    for _ in 0..count {
        if remaining == 0 {
            break;
        }
        let c = t.sample_challenge();
        let n = (PER_CHALLENGE.get(depth).copied().unwrap_or(0) as usize).min(remaining);
        for i in 0..n {
            out.push(query_bits(c, i * depth, depth))?;
        }
        remaining -= n;
    }
    Some(())
}

/// `extRow` or the level-0 reversal (`lanesOf`): an opened row's lanes into `out`; their count.
#[inline(never)]
fn lanes_of(index: usize, row: &[u64], out: &mut [EW; LANE_CAP]) -> Option<usize> {
    if index == 0 {
        let lanes = out.get_mut(..row.len())?;
        for (lane, &w) in lanes.iter_mut().zip(row.iter().rev()) {
            *lane = EW::of_k(w);
        }
        Some(row.len())
    } else {
        let n = row.len() / 2;
        let lanes = out.get_mut(..n)?;
        for (lane, pair) in lanes.iter_mut().zip(row.chunks_exact(2)) {
            *lane = EW::new(pair[0], pair[1]);
        }
        Some(n)
    }
}

/// `subspaceTable μ`: `subspaceRoots μ` with their inverses.
#[inline(never)]
fn subspace_table(mu: usize) -> Option<Buf<(u64, u64), ROOT_CAP>> {
    let mut layer = [0u64; ROOT_CAP];
    let layer = layer.get_mut(..mu)?;
    for (i, v) in layer.iter_mut().enumerate() {
        *v = 1u64 << (i + 1);
    }
    let mut table = Buf { len: 0, items: [(0u64, 0u64); ROOT_CAP] };
    table.push((1, kinv(1)))?;
    // `subspaceRoots`: square-and-shift the layer by the last root, pop the next root.
    let (mut last, mut start) = (1u64, 0usize);
    for _ in 0..mu {
        let rest = layer.get_mut(start..).unwrap_or(&mut []);
        for v in rest.iter_mut() {
            *v = kmul(*v, *v) ^ kmul(last, *v);
        }
        match rest.first() {
            Some(&root) => {
                table.push((root, kinv(root)))?;
                last = root;
                start += 1;
            }
            None => break,
        }
    }
    Some(table)
}

/// `subspaceAtTable table x`: `What_i(x)`, then `W_(i+1) = W_i² + W_i(β_i)·W_i`.
#[inline(never)]
fn subspace_at_table(table: &[(u64, u64)], x: u64) -> Buf<u64, ROOT_CAP> {
    let mut what = Buf { len: 0, items: [0u64; ROOT_CAP] };
    let mut w = x;
    for (slot, &(root, inverse)) in what.items.iter_mut().zip(table) {
        *slot = kmul(w, inverse);
        w = kmul(w, w) ^ kmul(root, w);
    }
    what.len = table.len().min(ROOT_CAP);
    what
}

/// `novelEval coefficients what`: `Σ_c p_c·X_c(x)`, `novelBasis what |coefficients|` doubling the
/// basis by each `What_i` until it is long enough.
#[inline(never)]
fn novel_eval(coefficients: &[EW], what: &[u64]) -> Option<EW> {
    let count = coefficients.len();
    let mut basis = [0u64; 2 * FOLDED_CAP];
    require(count <= FOLDED_CAP)?;
    basis[0] = 1;
    let mut size = 1;
    for &value in what {
        if count <= size {
            continue;
        }
        let (low, high) = basis.split_at_mut_checked(size)?;
        for (h, &l) in high.iter_mut().zip(low.iter()) {
            *h = kmul(l, value);
        }
        size *= 2;
    }
    let basis = basis.get(..count.min(size))?;
    Some(coefficients.iter().zip(basis).fold(ZERO, |acc, (&p, &b)| acc + EW::scale(b, p)))
}

/// `FoldRoundW`: `α`, `β`.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct FoldRoundW {
    pub alpha: EW,
    pub beta: EW,
}

/// `foldRow values x rounds`: each round's `foldLanes` (adjacent lanes `(f, g)` become
/// `g + (α + β·x)·f`), the first lane left or `0`.
#[inline(never)]
fn fold_row(values: &mut [EW; LANE_CAP], n: usize, x: u64, rounds: &[FoldRoundW]) -> EW {
    let mut size = n.min(LANE_CAP);
    for round in rounds {
        let factor = round.alpha + EW::scale(x, round.beta);
        for i in 0..size / 2 {
            if let (Some(&f), Some(&g)) = (values.get(2 * i), values.get(2 * i + 1)) {
                values[i % LANE_CAP] = g + factor * f;
            }
        }
        size /= 2;
    }
    if size > 0 { values[0] } else { ZERO }
}

/// `GluedClaimW`: the power of `λ`, the fold rounds before its level, its weight: `kind` `0` for
/// `eq p`, `1` for `induced μ queries weights` (`GluedAt`).
#[derive(Clone, Copy)]
#[repr(C)]
pub struct GluedClaimW {
    pub scalar: EW,
    pub fold_start: usize,
    pub kind: u64,
    pub mu: usize,
    pub p: Buf<EW, STACK_CAP>,
    pub queries: Buf<u64, QUERY_CAP>,
    pub weights: Buf<EW, QUERY_CAP>,
}

/// `inducedWeight μ queries weights point`, `subspaceTable μ` computed once.
#[inline(never)]
fn induced_weight(mu: usize, queries: &[u64], query_weights: &[EW], point: &[EW]) -> Option<EW> {
    let table = subspace_table(mu)?;
    let mut total = ZERO;
    for (&weight, &query) in query_weights.iter().zip(queries) {
        let what = subspace_at_table(table.as_slice(), query);
        let product = point
            .iter()
            .zip(what.as_slice())
            .fold(weight, |product, (&challenge, &value)| product * (ONE + EW::scale(1 ^ value, challenge)));
        total = total + product;
    }
    Some(total)
}

/// `GluedWeight.eval`.
#[inline(never)]
fn glued_eval(g: &GluedClaimW, x: &[EW]) -> Option<EW> {
    if g.kind == 0 {
        Some(eq_eval(g.p.as_slice(), x))
    } else {
        induced_weight(g.mu, g.queries.as_slice(), g.weights.as_slice(), x)
    }
}

/// `WhirAt`: the running claim, every fold round's `α`, the glued claims.
#[repr(C)]
pub struct WhirStateW {
    pub claim: EW,
    pub alphas: Buf<EW, STACK_CAP>,
    pub glued: Buf<GluedClaimW, GLUED_CAP>,
}

/// The phase-7 state in the working area but the batching scales: WHIR's state, a level's fold
/// rounds and its query positions.
#[repr(C)]
pub struct WhirW {
    pub state: WhirStateW,
    pub rounds: Buf<FoldRoundW, ROUND_CAP>,
    pub queries: Buf<u64, QUERY_CAP>,
}

/// `BasisAt`: the batching scales.
pub type ScalesW = Buf<EW, STACK_CLAIM_CAP>;

/// `BasisW`: the scales, and the stack claims they weigh: the ring-switched one, the column claims
/// with a placement, the out-of-domain one.
#[repr(C)]
struct BasisW<'a> {
    scales: &'a [EW],
    layout: &'a LayoutW,
    ring: &'a RingW,
    keccak: &'a KeccakOutW,
    claims: &'a ClaimsW,
    ood: &'a EqClaimW,
}

impl BasisW<'_> {
    /// `BasisW.eval`: `dot scales (claims.map (·.weight.eval point))`.
    #[inline(never)]
    fn eval(&self, point: &[EW]) -> Option<EW> {
        let mut scales = self.scales.iter();
        let mut next = || scales.next().copied().unwrap_or(ZERO);
        let ring = self.layout.placement(QKECCAK);
        let mut total =
            next() * ring_claim_weight(ring, self.keccak.point.as_slice(), &self.ring.coefficients, point)?;
        for c in self.claims.as_slice() {
            if let Some(p) = on_stack(c, self.layout) {
                total = total + next() * column_weight(p, c.point.as_slice(), self.layout.stack_log, point)?;
            }
        }
        Some(total + next() * eq_eval(self.ood.z.as_slice(), point))
    }
}

/// `foldRound`: four scalars, a grind, `α`, `β`; the claim folded at `α`.
#[inline(never)]
fn fold_round(t: &mut TState, s: &mut WhirStateW) -> Option<FoldRoundW> {
    let u0 = t.read_scalar()?;
    let w = t.read_scalar()?;
    let c0 = t.read_scalar()?;
    let c1 = t.read_scalar()?;
    t.grind(FOLD_GRINDING_BITS)?;
    let alpha = t.sample_challenge();
    let beta = t.sample_challenge();
    s.claim = u0 + alpha * (u0 + s.claim) + alpha * alpha * w + beta * c0 + alpha * beta * (c0 + c1);
    s.alphas.push(alpha)?;
    Some(FoldRoundW { alpha, beta })
}

/// `foldRounds n`, the rounds into `rounds`.
#[inline(never)]
fn fold_rounds(t: &mut TState, n: usize, s: &mut WhirStateW, rounds: &mut Buf<FoldRoundW, ROUND_CAP>) -> Option<()> {
    rounds.clear();
    for _ in 0..n {
        let round = fold_round(t, s)?;
        rounds.push(round)?;
    }
    Some(())
}

/// Every opened row folded and checked: `foldRow (lanesOf row) query rounds` with the queries'
/// `What`s, `f` given each query's index, `What`s, and folded row.
#[inline(never)]
fn each_row(
    index: usize,
    queries: &[u64],
    rows: &Rows,
    mu: usize,
    rounds: &[FoldRoundW],
    mut f: impl FnMut(usize, &[u64], EW) -> Option<()>,
) -> Option<()> {
    let table = subspace_table(mu)?;
    for (j, &query) in queries.iter().enumerate().take(rows.count) {
        let mut lanes = [ZERO; LANE_CAP];
        let n = lanes_of(index, rows.row(j), &mut lanes)?;
        let folded = fold_row(&mut lanes, n, query, rounds);
        let what = subspace_at_table(table.as_slice(), query);
        f(j, what.as_slice(), folded)?;
    }
    Some(())
}

/// The final level of `whirLevels`, after its fold rounds `rounds` (`w.rounds`): the folded lane
/// read, the queries checked against it, the last sumcheck and the end check.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn final_level(
    t: &mut TState,
    index: usize,
    level: &Level,
    mu: usize,
    lane_folds: usize,
    basis: &BasisW,
    w: &mut WhirW,
) -> Option<()> {
    let depth = mu + level.log_inv_rate;
    let mut folded = [ZERO; FOLDED_CAP];
    let size = 1usize.checked_shl(u32::try_from(mu).ok()?)?;
    let folded = folded.get_mut(..size.checked_add(level.fold)?)?;
    t.read_scalars(folded)?;
    t.grind(QUERY_GRINDING_BITS)?;
    sample_queries(t, depth, level.queries, &mut w.queries)?;
    let queries = w.queries.as_slice();
    let rows = t.query_openings(index, queries)?;
    each_row(index, queries, &rows, mu, w.rounds.as_slice(), |_, what, row| require(row == novel_eval(folded, what)?))?;
    let mut tail = [ZERO; STACK_CAP];
    let tail = tail.get_mut(..mu)?;
    let claim = t.sumcheck_plain(w.state.claim, 3, tail)?;
    let mut point = Buf { len: 0, items: [ZERO; STACK_CAP] };
    point.set(w.state.alphas.as_slice())?;
    point.extend(tail)?;
    let point = point.as_slice();
    let mut rotated = Buf { len: 0, items: [ZERO; STACK_CAP] };
    rotated.set(point.get(lane_folds..).unwrap_or(&[]))?;
    rotated.extend(point.get(..lane_folds).unwrap_or(point))?;
    let mut weight = basis.eval(rotated.as_slice())?;
    for g in w.state.glued.as_slice() {
        weight = weight + g.scalar * glued_eval(g, point.get(g.fold_start..).unwrap_or(&[]))?;
    }
    require(weight * multilinear_eval(folded.get(..size)?, tail) == claim)
}

/// A level of `whirLevels` before the last, after its fold rounds `rounds` (`w.rounds`): the next
/// commitment, the out-of-domain sample, the queries batched, and the level glued (`glueLevel`).
#[inline(never)]
fn next_level(t: &mut TState, index: usize, level: &Level, next: &Level, mu: usize, w: &mut WhirW) -> Option<()> {
    let depth = mu + level.log_inv_rate;
    let (height, width) = level_shape(mu, next, 2 << next.fold);
    t.read_commitment(height, width)?;
    let mut high = [ZERO; ROUND_CAP];
    let high = high.get_mut(..level.fold)?;
    t.read_scalars(high)?;
    t.grind(OOD_GRINDING_BITS)?;
    let mut ood_point = Buf { len: 0, items: [ZERO; STACK_CAP] };
    t.sample_challenges(ood_point.resize(mu)?);
    let ood_value = t.read_scalar()?;
    t.grind(QUERY_GRINDING_BITS)?;
    sample_queries(t, depth, level.queries, &mut w.queries)?;
    let lam = t.sample_challenge();
    let queries = w.queries.as_slice();
    let mut query_weights = Buf { len: 0, items: [ZERO; QUERY_CAP] };
    powers(lam, query_weights.resize(queries.len())?);
    let rows = t.query_openings(index, queries)?;
    let qw = query_weights.as_slice();
    let mut batched = ZERO;
    each_row(index, queries, &rows, mu, w.rounds.as_slice(), |j, what, row| {
        let correction = EW::scale(what.get(mu).copied().unwrap_or(0), novel_eval(high, what)?);
        batched = batched + qw.get(j).copied().unwrap_or(ZERO) * (row + correction);
        Some(())
    })?;
    glue_level(&mut w.state, lam, mu, ood_point.as_slice(), ood_value, queries, qw, batched)
}

/// `glueLevel`: the claim moved by the out-of-domain value and the batched queries, and the level's
/// two glued claims appended.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn glue_level(
    s: &mut WhirStateW,
    lam: EW,
    mu: usize,
    ood_point: &[EW],
    ood_value: EW,
    queries: &[u64],
    query_weights: &[EW],
    batched: EW,
) -> Option<()> {
    s.claim = s.claim + lam * ood_value + lam * lam * batched;
    let fold_start = s.alphas.len;
    let g = s.glued.items.get_mut(s.glued.len)?;
    g.scalar = lam;
    g.fold_start = fold_start;
    g.kind = 0;
    g.p.set(ood_point)?;
    s.glued.len += 1;
    let g = s.glued.items.get_mut(s.glued.len)?;
    g.scalar = lam * lam;
    g.fold_start = fold_start;
    g.kind = 1;
    g.mu = mu;
    g.queries.set(queries)?;
    g.weights.set(query_weights)?;
    s.glued.len += 1;
    Some(())
}

/// `whirLevels logN laneFolds basis 0 config`: every level of the ladder, the last one final.
#[inline(never)]
fn whir_levels(
    t: &mut TState,
    log_n: usize,
    lane_folds: usize,
    basis: &BasisW,
    levels: &[Level],
    w: &mut WhirW,
) -> Option<()> {
    for (index, level) in levels.iter().enumerate() {
        fold_rounds(t, level.fold, &mut w.state, &mut w.rounds)?;
        let mu = log_n.saturating_sub(w.state.alphas.len);
        match levels.get(index + 1) {
            None => return final_level(t, index, level, mu, lane_folds, basis, w),
            Some(next) => next_level(t, index, level, next, mu, w)?,
        }
    }
    None
}

/// **Phase 7b** (`verifyStackedOpening`, `verifyWhir`): at most `maxStackedClaims` claims, the
/// ring-switched one, the column claims with a placement and the out-of-domain one, batched by the
/// powers of one challenge into one opening.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn verify_stacked_opening(
    t: &mut TState,
    layout: &LayoutW,
    log_inv_rate: usize,
    ring: &RingW,
    keccak: &KeccakOutW,
    claims: &ClaimsW,
    ood: &EqClaimW,
    scales: &mut ScalesW,
    w: &mut WhirW,
) -> Option<()> {
    let placed = claims.as_slice().iter().filter(|c| on_stack(c, layout).is_some()).count();
    let count = placed + 2;
    require(count <= MAX_STACKED_CLAIMS)?;
    let scale = t.sample_challenge();
    powers(scale, scales.resize(count)?);
    let scales = scales.as_slice();
    let mut values = scales.iter();
    let mut next = || values.next().copied().unwrap_or(ZERO);
    let mut target = next() * ring.target;
    for c in claims.as_slice() {
        if on_stack(c, layout).is_some() {
            target = target + next() * c.value;
        }
    }
    target = target + next() * ood.value;
    let basis = BasisW { scales, layout, ring, keccak, claims, ood };
    // `verifyWhir`.
    let (levels, n) = ladder(layout.stack_log, log_inv_rate)?;
    let levels = levels.get(..n)?;
    let lane_folds = levels.first().map_or(0, |l| l.fold);
    w.state.claim = target;
    w.state.alphas.clear();
    w.state.glued.clear();
    whir_levels(t, layout.stack_log, lane_folds, &basis, levels, w)
}
