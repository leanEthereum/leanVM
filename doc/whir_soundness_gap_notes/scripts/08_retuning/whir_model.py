"""Standalone model of leanVM's WHIR parameter search (researcher 08).

A port, in exact integer arithmetic, of
  crates/experimental_prover/pcs/src/whir_config.rs            (ladder, per-message checks, level search)
  crates/experimental_prover/pcs/src/whir_config/affine_mca.rs (CWYZ26 Thm 4.10, admissible triples)
with every protocol constant turned into a knob (`Knobs`). Floats are used only where the Rust uses them (to steer
the search for the interpolation degree D and for the intermediate threshold B); every accept/reject is an integer
comparison. Where the Rust treats a u128 overflow as a failure, so does this port (`U128`).

Standard library only. `validate.py` checks the port against `WHIR_QUERIES` in crates/verifier/src/whir.rs.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field, replace
from functools import lru_cache
from math import isqrt

LOG_Q = 128
U128 = 1 << 128
U128_MAX = U128 - 1
MAX_MULTIPLICITY = 1 << 16


# --------------------------------------------------------------------------------------------------------------
# affine_mca.rs
# --------------------------------------------------------------------------------------------------------------


# When True, intermediate values are not held to u128 (the Rust counts an overflow as a failed hypothesis). Set per
# call from `Knobs.exact_wide`; the deployed analysis keeps it False.
_WIDE = False


def _ck(x):
    """A u128 value, or None on overflow / underflow (Rust's checked_* arithmetic)."""
    if x is None or x < 0:
        return None
    return x if (_WIDE or x < U128) else None


def johnson_list(n, agree, inter):
    """floor(n (agree - inter) / (agree^2 - n inter)), None below the Johnson radius."""
    if agree < inter:
        return None
    num = _ck(n * (agree - inter))
    sq = _ck(agree * agree)
    ni = _ck(n * inter)
    if num is None or sq is None or ni is None:
        return None
    den = sq - ni
    if den <= 0:
        return None
    return num // den


def interpolation_m(d, a, m, big_d):
    ma = _ck(m * a)
    if ma is None:
        return None
    c = ma - big_d - 1
    if c < 0:
        return None
    big_m = min(big_d, c // d)
    return big_m if big_m >= 1 else None


def power_sums(j):
    jj = _ck(j * (j + 1))
    if jj is None:
        return None
    s1 = jj // 2
    t = _ck(jj * (2 * j + 1))
    if t is None:
        return None
    return (j + 1, s1, t // 6)


def interpolation_holds(n, d, a, m, big_d):
    """The interpolation inequality (4.5) of CWYZ26 Lemma 4.2, exactly. Returns M or None."""
    big_m = interpolation_m(d, a, m, big_d)
    if big_m is None:
        return None
    c = m * a - big_d
    e = big_d + 1
    ps = power_sums(big_m)
    if ps is None:
        return None
    s0, s1, s2 = ps
    ce = _ck(c * e)
    if ce is None:
        return None
    ces0 = _ck(ce * s0)
    ds2 = _ck(d * s2)
    if ces0 is None or ds2 is None:
        return None
    left = _ck(ces0 + ds2)
    de = _ck(d * e)
    if left is None or de is None:
        return None
    cde = _ck(c + de)
    if cde is None:
        return None
    sub = _ck(cde * s1)
    if sub is None:
        return None
    unknowns = left - sub
    if unknowns < 0:
        return None
    ps = power_sums(min(m - 1, big_m))
    if ps is None:
        return None
    t0, t1, t2 = ps
    me = _ck(m * e)
    if me is None:
        return None
    met0 = _ck(me * t0)
    if met0 is None:
        return None
    add = _ck(met0 + t2)
    sub2 = _ck((m + e) * t1)
    if add is None or sub2 is None:
        return None
    inner = add - sub2
    if inner < 0:
        return None
    equations = _ck(n * inner)
    if equations is None:
        return None
    return big_m if unknowns > equations else None


def interpolation_ratio(n, d, a, m, big_d):
    """unknowns / equations in floating point, in the Rust's operation order (steers, never decides)."""
    big_m = min(big_d, float(math.floor((m * a - big_d - 1.0) / d)))
    if big_m < 1.0:
        return 0.0
    c, e = m * a - big_d, big_d + 1.0

    def sums(j):
        return (j + 1.0, j * (j + 1.0) / 2.0, j * (j + 1.0) * (2.0 * j + 1.0) / 6.0)

    s0, s1, s2 = sums(big_m)
    t0, t1, t2 = sums(min(m - 1.0, big_m))
    return (c * e * s0 + d * s2 - (c + d * e) * s1) / (n * (m * e * t0 + t2 - (m + e) * t1))


def smallest_big_d(n, d, a, m):
    lo = max((m * a - 1) // d, 1)
    hi = m * a // 2
    if lo >= hi:
        return None
    nf, df, af, mf = float(n), float(d), float(a), float(m)

    def ratio(big_d):
        return interpolation_ratio(nf, df, af, mf, float(big_d))

    x, y = lo, hi
    while y - x > 3:
        x1, y1 = x + (y - x) // 3, y - (y - x) // 3
        if ratio(x1) < ratio(y1):
            x = x1 + 1
        else:
            y = y1
    peak = None
    for big_d in range(x, y + 1):
        if interpolation_holds(n, d, a, m, big_d) is not None:
            peak = big_d
            break
    if peak is None:
        return None
    x, y = lo, peak
    while x < y:
        mid = x + (y - x) // 2
        if interpolation_holds(n, d, a, m, mid) is not None:
            y = mid
        else:
            x = mid + 1
    return x


def interpolation(n, d, a, max_multiplicity=MAX_MULTIPLICITY):
    """(m, D) with the smallest feasible m, then its smallest D."""
    gap = a * a - n * d
    if gap <= 0:
        return None
    lo = max(n * d // gap, 1)
    hi = lo
    while smallest_big_d(n, d, a, hi) is None:
        lo = hi + 1
        hi *= 2
        if hi > max_multiplicity:
            return None
    while lo < hi:
        mid = lo + (hi - lo) // 2
        if smallest_big_d(n, d, a, mid) is not None:
            hi = mid
        else:
            lo = mid + 1
    big_d = smallest_big_d(n, d, a, hi)
    if big_d is None:
        return None
    return hi, big_d


def hypotheses(n, d, a, m, big_d, b):
    if a > n or not (d + 1 < b < a):
        return None
    big_m = interpolation_holds(n, d, a, m, big_d)
    if big_m is None:
        return None
    ell_b = johnson_list(n, b, d + 1)
    if ell_b is None:
        return None
    return big_m, ell_b


def affine_error_log2(n, d, a, m, big_d, b):
    hyp = hypotheses(n, d, a, m, big_d, b)
    if hyp is None:
        return None
    big_m, ell_b = hyp
    nf, df, mf, bd = float(n), float(d), float(big_m), float(big_d)
    q = 2.0**LOG_Q
    pairs = nf * (nf - 1.0) / 2.0
    r = nf / float(a - b)
    interp = 4.0 * df * df * mf * mf * (bd * bd * bd) * (r * r)
    return math.log2(bd * bd + float(ell_b) * max(q, pairs) + interp) - 2.0 * LOG_Q


def combiner_within(n, d, a, m, big_d, b, budget, exact=False):
    """Whether eps_aff + 2 ell(A - 1, d) / q <= budget / q, exactly. None when a hypothesis fails.

    `exact=True` drops the Rust's u128 overflow conservatism (an overflow there counts as a miss)."""
    hyp = hypotheses(n, d, a, m, big_d, b)
    if hyp is None:
        return None
    big_m, ell_b = hyp
    ell = johnson_list(n, a - 1, d)
    if ell is None:
        return None
    assert n < 1 << 64
    slack = budget - 2 * ell - ell_b
    if slack < 0 or (not exact and 2 * ell >= U128):
        return False
    gap2 = (a - b) * (a - b)
    rhs_high = slack * gap2
    if not exact and rhs_high >= U128:
        return True
    interp = 4 * d * d * big_m * big_m * big_d * big_d * big_d
    if not exact:
        # try_fold of checked_mul over [4, d, d, M, M, D, D, D]: any partial product past u128 is a miss.
        if interp >= U128:
            return False
    total = interp * n * n + big_d * big_d * gap2
    if not exact and total >= 1 << 256:
        return False
    return total <= rhs_high << 128


@lru_cache(maxsize=None)
def find_witness(n, d, a, max_multiplicity=MAX_MULTIPLICITY, wide=False):
    """(m, D, B) with the smallest feasible m, its smallest D, then B = A - 2^i minimising the float bound."""
    global _WIDE
    _WIDE = wide
    interp = interpolation(n, d, a, max_multiplicity)
    if interp is None:
        return None
    m, big_d = interp
    best = None
    for i in range(128):
        b = a - (1 << i)
        if b < 0:
            break
        err = affine_error_log2(n, d, a, m, big_d, b)
        if err is not None:
            if best is None or err < best[1]:
                best = ((m, big_d, b), err)
        elif b <= d + 1 or johnson_list(n, b, d + 1) is None:
            break
    return best


# --------------------------------------------------------------------------------------------------------------
# whir_config.rs
# --------------------------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class Knobs:
    """Every constant the search reads. The defaults are the deployed ones (crates/verifier/src/whir.rs)."""

    initial_fold: int = 6  # INITIAL_FOLDING_FACTOR
    sub_fold: int = 4  # SUBSEQUENT_FOLDING_FACTOR
    initial_reduction: int = 3  # RS_DOMAIN_INITIAL_REDUCTION_FACTOR
    sub_reduction: int = 1  # RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
    residual_max: int = 5  # RESIDUAL_MAX_LOG
    g_query: int = 17  # QUERY_GRINDING_BITS
    g_fold: int = 7  # FOLD_GRINDING_BITS
    g_batch: int = 13  # BATCH_GRINDING_BITS
    g_ood: int = 15  # OOD_GRINDING_BITS
    # Per-level overrides of the query grind (level index -> bits); absent levels use g_query.
    g_query_levels: tuple = ()
    # Per-level overrides of the ladder: (level index >= 1, fold rounds of that level) and
    # (level index, domain reduction after that level). Absent levels use the four constants above.
    fold_levels: tuple = ()
    reduction_levels: tuple = ()
    # Sample a level's queries without replacement (a protocol change; the deployed protocol samples i.i.d.).
    distinct_queries: bool = False
    target: int = 125  # SECURITY_BITS
    max_list_0: int = 166  # MAX_LIST_0
    stacked_claims: int = 512 + 2  # MAX_STACKED_CLAIMS + RING_SWITCH_ERROR_NUMERATOR
    # Analysis variants for the slack estimates of section 4 of the note. The deployed analysis is all-False.
    no_degree_slack: bool = False  # analyse at d = 2^kappa - 1 instead of 2^kappa - 1 + k
    no_round_loss: bool = False  # every round at t_end instead of t_end - (k - j)
    exact_wide: bool = False  # drop the u128-overflow conservatism of combiner_within
    max_multiplicity: int = MAX_MULTIPLICITY

    def query_grind(self, level):
        return dict(self.g_query_levels).get(level, self.g_query)


DEPLOYED = Knobs()


def budget(grind, target):
    """The largest count c with c / q <= 2^-(target - grind)."""
    bits = max(LOG_Q - max(target - grind, 0), 0)
    return U128_MAX if bits >= 128 else 1 << bits


def degree(cols, k, kn=DEPLOYED):
    return (1 << cols) - 1 + (0 if kn.no_degree_slack else k)


def ladder(log_n, log_inv_rate, kn=DEPLOYED):
    """(rates, cols, folds, residual) as derive_ladder_shape, or None when the shape is not admitted."""
    k0 = kn.initial_fold
    if log_n <= k0:
        return None
    rates, cols, folds = [log_inv_rate], [log_n - k0], [k0]
    n_running, rate_running, fold_running = log_n - k0, log_inv_rate, k0
    fold_at, reduction_at = dict(kn.fold_levels), dict(kn.reduction_levels)
    while n_running > kn.residual_max:
        level = len(folds)
        k = min(fold_at.get(level, kn.sub_fold), n_running)
        reduction = reduction_at.get(level - 1, kn.initial_reduction if level == 1 else kn.sub_reduction)
        if fold_running < reduction:
            return None
        rate = rate_running + fold_running - reduction
        rates.append(rate)
        cols.append(n_running - k)
        folds.append(k)
        n_running -= k
        rate_running, fold_running = rate, k
    if len(folds) < 2:
        return None
    if any(r == 0 or c == 0 for r, c in zip(rates, cols)):
        return None  # validate(): rate-one code or empty lanes
    return rates, cols, folds, n_running


def check_list_terms(n, d, a0, mu, first, kn):
    """The terms that depend only on ell(t_0, d). Returns ell, or None when one fails."""
    ell = johnson_list(n, a0, d)
    if ell is None:
        return None
    if first:
        if ell > kn.max_list_0:
            return None
        if (kn.stacked_claims - 1) * ell > budget(kn.g_batch, kn.target):
            return None
    pairs = ell * (ell - 1) // 2
    if pairs * mu > budget(kn.g_ood, kn.target):
        return None
    return ell


def fold_witnesses(n, d, k, t_end, kn):
    global _WIDE
    rounds = []
    fold_budget = budget(kn.g_fold, kn.target)
    for j in range(1, k + 1):
        a = t_end if kn.no_round_loss else t_end - (k - j)
        if a < 0:
            return None
        found = find_witness(n, d, a, kn.max_multiplicity, kn.exact_wide)
        if found is None:
            return None
        (m, big_d, b), _ = found
        _WIDE = kn.exact_wide
        if combiner_within(n, d, a, m, big_d, b, fold_budget, kn.exact_wide) is not True:
            return None
        rounds.append((m, big_d, b))
    return rounds


def _level_key(cols, rate, k, first, kn):
    return (cols, rate, k, first, kn.g_fold, kn.g_ood, kn.g_batch if first else None, kn.target,
            kn.max_list_0 if first else None, kn.stacked_claims if first else None, kn.no_degree_slack,
            kn.no_round_loss, kn.exact_wide, kn.max_multiplicity)


_LEVEL_CACHE: dict = {}


def search_level(cols, rate, k, first, kn=DEPLOYED, faithful=True):
    """The smallest t_end for which every term of the level clears the target: (t_end, rounds, start list).

    `faithful=True` is the Rust's bisection over the full feasibility predicate. `faithful=False` first bisects the
    list terms alone (monotone, cheap), accepts that threshold when the fold rounds clear at it, and otherwise
    bisects the full predicate above it; it returns the same threshold whenever feasibility is monotone in t_end.
    """
    key = _level_key(cols, rate, k, first, kn) + (faithful,)
    if key in _LEVEL_CACHE:
        return _LEVEL_CACHE[key]
    other = key[:-1] + (not faithful,)
    n, d = 1 << (cols + rate), degree(cols, k, kn)
    mu = cols + k
    loss = 0 if kn.no_round_loss else k

    def list_ok(t_end):
        return check_list_terms(n, d, t_end - loss, mu, first, kn)

    def feasible(t_end):
        if list_ok(t_end) is None:
            return None
        return fold_witnesses(n, d, k, t_end, kn)

    lo, hi = isqrt(n * d) + 1, n
    result = None
    if feasible(hi) is not None:
        if not faithful:
            a, b = lo, hi
            while a < b:
                mid = a + (b - a) // 2
                if list_ok(mid) is not None:
                    b = mid
                else:
                    a = mid + 1
            lo = b
        rounds = feasible(lo) if not faithful else None
        if rounds is None:
            while lo < hi:
                mid = lo + (hi - lo) // 2
                if feasible(mid) is not None:
                    hi = mid
                else:
                    lo = mid + 1
            rounds = feasible(hi)
            lo = hi
        result = (lo, rounds, johnson_list(n, lo - loss, d))
    _LEVEL_CACHE[key] = result
    return result


def query_room(omega, next_list, grind, target):
    room = budget(grind, target) - (omega + 1) * next_list
    return room if room > 0 else None


def query_count(log_n, t_end, next_list, grind, target, distinct=False):
    """The fewest queries with ((t_end - 1) / n)^omega + (omega + 1) next_list / q <= 2^-(target - grind).

    `distinct=True` replaces the first term by prod_{i < omega} (t_end - 1 - i) / (n - i), queries without
    replacement (not the deployed protocol)."""
    power, denom = 1, 1
    for omega in range(1, (1 << log_n) + 1):
        if distinct:
            power *= max(t_end - omega, 0)
            denom *= (1 << log_n) - (omega - 1)
        else:
            power *= t_end - 1
        room = query_room(omega, next_list, grind, target)
        if room is None:
            return None
        if (power << LOG_Q <= room * denom) if distinct else (power << LOG_Q <= room << (omega * log_n)):
            return omega
    return None


@dataclass
class Level:
    log_inv_rate: int
    cols: int  # kappa: log2 of the coefficients per lane
    k: int  # fold rounds (log2 of the lanes per leaf)
    agreement: int  # t_end
    rounds: list  # (m, D, B) per fold round
    list_bound: int  # ell(t_0, d)
    queries: int = 0

    @property
    def log_block(self):
        return self.cols + self.log_inv_rate


@dataclass
class Config:
    log_n: int
    log_inv_rate: int
    knobs: Knobs
    levels: list = field(default_factory=list)
    residual: int = 0

    @property
    def queries(self):
        return [lv.queries for lv in self.levels]


def derive(log_n, log_inv_rate, kn=DEPLOYED, faithful=True):
    """WhirSecurityConfig::derive_with. None when the shape or a level has no feasible parameters."""
    shape = ladder(log_n, log_inv_rate, kn)
    if shape is None:
        return None
    rates, cols, folds, residual = shape
    levels = []
    for i, (rate, c, k) in enumerate(zip(rates, cols, folds)):
        found = search_level(c, rate, k, i == 0, kn, faithful)
        if found is None:
            return None
        t_end, rounds, ell = found
        levels.append(Level(rate, c, k, t_end, rounds, ell))
    for i, lv in enumerate(levels):
        next_list = levels[i + 1].list_bound if i + 1 < len(levels) else 0
        lv.queries = query_count(lv.log_block, lv.agreement, next_list, kn.query_grind(i), kn.target, kn.distinct_queries)
        if lv.queries is None or lv.queries > 1 << lv.log_block:
            return None
    return Config(log_n, log_inv_rate, kn, levels, residual)


def johnson_limit_queries(cfg):
    """Per level, the queries at the Johnson radius itself (eta -> 0, no list terms): the floor of this analysis."""
    out = []
    for i, lv in enumerate(cfg.levels):
        n, d = 1 << lv.log_block, degree(lv.cols, lv.k, cfg.knobs)
        bits = cfg.knobs.target - cfg.knobs.query_grind(i)
        per_query = lv.log_block - 0.5 * math.log2(n * d)
        out.append(math.ceil(bits / per_query - 1e-12))
    return out


def with_knobs(**kw):
    return replace(DEPLOYED, **kw)
