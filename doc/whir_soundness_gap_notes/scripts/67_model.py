#!/usr/bin/env python3
"""Note 67: the DEEP-fold opening of doc/deep_fold (Protocol D, Theorem 5.2) under proven list bounds only.

Standard library only. Reuses the validated models of note 08 (`08_retuning/whir_model.py`, `costs.py`) and the
Merkle and sponge accounting of note 11 (`11_deep_fold_whir.py`); nothing of those files is edited. What is new
here: the paper's error rows with their exact constants, point schedules (ladders), a query grind per level, any
ladder of note 08's `Knobs`, and the list bounds of section 1 of the note (Johnson, counting, shortened Johnson).

Error rows (Theorem 5.2 of the paper), q = 2^128, eps = (d + 2^ell - 1) / q, Theta = K0 (K0 - 1) (K0 - 2 q):
  M0  C(L, 2) eps^sbar_1 + (L^3 q^6 / Theta) sum_{j=1..ell} tau^-(j-1) eps^sbar_j   <= 2^-(125 - g_point)
  M1  (J0 + 1) / q, J0 = 512                                                         <= 2^-(125 - g_batch)
  M2  (K0 - 1) / q^2 + tau                                                           <= 2^-(125 - g_fold)
  M3  ((A_end - 1) / n)^t + (sbar_ell + t) / q                                       <= 2^-(125 - g_query)
  M4  ((A_end - 1) / n)^t                                                            <= 2^-(125 - g_query)
with K0 = 2^(g_fold + 2) q and tau = 2^-(126 - g_fold). Every accept or reject is an exact integer comparison.
"""

from __future__ import annotations

import importlib.util
import math
import os
import sys
from fractions import Fraction
from math import comb, isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "08_retuning"))
import costs as c8  # noqa: E402
import whir_model as wm  # noqa: E402


def _load(name, file):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, file))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


d11 = _load("deep11", "11_deep_fold_whir.py")

LOG_Q, Q, TARGET = 128, 1 << 128, 125


def lg(x):
    """log2 of a positive integer or Fraction of any size."""
    if isinstance(x, Fraction):
        return d11.log2_big(x.numerator) - d11.log2_big(x.denominator)
    return d11.log2_big(x)


# ---------------------------------------------------------------------------------------------------------------
# Proven list bounds for interleaved words (section 1 of the note). n columns, tuples of degree <= d, agreement a.
# ---------------------------------------------------------------------------------------------------------------


def johnson(n, a, d):
    """floor(n (a - d) / (a^2 - n d)) when a^2 > n d (Theorem 2.2 of the paper), else None."""
    den = a * a - n * d
    return None if den <= 0 or a <= d else n * (a - d) // den


def counting(n, a, d):
    """floor(C(n, d+1) / C(a, d+1)), for a >= d + 1."""
    return comb(n, d + 1) // comb(a, d + 1)


def packing(n, a, d, j):
    """Shortened Johnson bound, j columns fixed: floor(n/a floor((n-1)/(a-1) ... J(n-j, a-j, d-j))), or None."""
    inner = johnson(n - j, a - j, d - j) if j < d else (n - d) // (a - d)
    if inner is None:
        return None
    for i in range(j - 1, -1, -1):
        inner = (n - i) * inner // (a - i)
    return inner


def first_johnson_j(n, a, d):
    """The least j with (a - j)^2 > (n - j)(d - j); j = d always qualifies when a > d."""
    lo, hi = 0, d
    while lo < hi:
        mid = (lo + hi) // 2
        if (a - mid) ** 2 > (n - mid) * (d - mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def best_list(n, a, d):
    """(bound, source): the least of unique decoding, Johnson, and the shortened Johnson bounds over j. The scan
    starts at the least admissible j0 and is short: with f(j) = (a-j)^2 - (n-j)(d-j) = f(0) + (n + d - 2a) j, one
    more fixed column multiplies the bound by (n-j)/(a-j) and f by at most (m+1)/m at the m-th step after j0, so
    the minimum is within about a / (n - a) + 1 steps of j0. j = d is the counting bound with floors."""
    if 2 * a > n + d:
        return 1, "unique"
    jl = johnson(n, a, d)
    if jl is not None:
        return jl, "Johnson"
    j0 = first_johnson_j(n, a, d)
    best, src = None, None
    for j in range(j0, min(d, j0 + a // (n - a) + 3) + 1):
        b = packing(n, a, d, j)
        if b is not None and (best is None or b < best):
            best, src = b, ("counting" if j == d else f"short({j})")
    return best, src


def list_bits_estimate(n, a, d):
    """A float lower estimate of log2 of the best shortened bound (used only to skip hopeless thresholds)."""
    if a * a > n * d:
        return 0.0
    return first_johnson_j(n, a, d) * math.log2(n / a)


# ---------------------------------------------------------------------------------------------------------------
# The error rows, exactly
# ---------------------------------------------------------------------------------------------------------------


def fold_constants(g_fold):
    """(K0, Theta, T): K0 = 2^(g_fold + 2) q, Theta = K0 (K0 - 1)(K0 - 2q), tau = 2^-T, T = 126 - g_fold.
    Row M2 is then (K0 - 1)/q^2 + tau < 2^-(125 - g_fold)."""
    k0 = Q << (g_fold + 2)
    return k0, k0 * (k0 - 1) * (k0 - 2 * Q), 126 - g_fold


def m0_ok(big_l, d, ell, sbar, g_point, g_fold):
    """Row M0 for the held counts sbar = (sbar_1, ..., sbar_ell), non-decreasing."""
    _k0, theta, big_t = fold_constants(g_fold)
    e = d + (1 << ell) - 1
    top = sbar[-1]
    lhs = comb(big_l, 2) * theta * e ** sbar[0] * Q ** (top - sbar[0])
    lhs += big_l**3 * Q**6 * sum((1 << (big_t * j)) * e ** sbar[j] * Q ** (top - sbar[j]) for j in range(ell))
    return lhs << (TARGET - g_point) <= theta * Q**top


def one_batch(big_l, d, ell, g_point=15, g_fold=7, cap=4096):
    """The least s with M0 for the schedule (s, 0, ..., 0), or None above `cap`."""
    lo, hi = 1, 2
    while not m0_ok(big_l, d, ell, (hi,) * ell, g_point, g_fold):
        lo, hi = hi, hi * 2
        if hi > cap:
            return None
    while lo < hi:
        mid = (lo + hi) // 2
        if m0_ok(big_l, d, ell, (mid,) * ell, g_point, g_fold):
            hi = mid
        else:
            lo = mid + 1
    return lo


def scalars_of(sbar):
    """Prover scalars of a schedule: an answer a point, and one scalar a held point a round."""
    return sbar[-1] + sum(sbar)


def ladder_schedule(big_l, d, ell, g_point=15, g_fold=7):
    """A schedule with the one-batch total and few prover scalars: round j holds the least count for which the
    row M0 of the first j rounds passes (a binary search), then the whole row is checked and single counts are
    raised if it fails (its sum is dominated by one term, so this is rare)."""
    total = one_batch(big_l, d, ell, g_point, g_fold)
    if total is None:
        return None
    sbar = []
    for j in range(ell):
        lo, hi = (sbar[-1] if sbar else 1), total
        while lo < hi:
            mid = (lo + hi) // 2
            if m0_ok(big_l, d, j + 1, tuple(sbar) + (mid,), g_point, g_fold):
                hi = mid
            else:
                lo = mid + 1
        sbar.append(lo)
    while not m0_ok(big_l, d, ell, tuple(sbar), g_point, g_fold):
        for j in range(ell - 1, -1, -1):
            trial = sbar[:]
            trial[j] = min(trial[j] + 1, total)
            for i in range(j + 1, ell):
                trial[i] = max(trial[i], trial[j])
            if trial != sbar and m0_ok(big_l, d, ell, tuple(trial), g_point, g_fold):
                sbar = trial
                break
        else:
            sbar = [min(x + 1, total) for x in sbar]
    return tuple(sbar)


def query_ok(log_n, a_end, t, held, g_query, final):
    n = 1 << log_n
    if final:
        return (a_end - 1) ** t << (TARGET - g_query) <= n**t
    room = (1 << (LOG_Q - TARGET + g_query)) - (t + held)
    return room > 0 and (a_end - 1) ** t * Q <= room * n**t


def query_count(log_n, a_end, held, g_query, final):
    t = 1
    while not query_ok(log_n, a_end, t, held, g_query, final):
        t += 1
    return t


def max_end(log_n, t, held, g_query, final):
    """The largest A_end for which t queries suffice (0 if none)."""
    lo, hi = 0, 1 << log_n
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid >= 2 and query_ok(log_n, mid, t, held, g_query, final):
            lo = mid
        else:
            hi = mid - 1
    return lo


# ---------------------------------------------------------------------------------------------------------------
# Levels and configurations
# ---------------------------------------------------------------------------------------------------------------

S_HOLD = 64  # the held-point count assumed in M3 while a threshold is chosen; rechecked exactly in `finish`


class Level:
    def __init__(self, index, rate, cols, k, a0, big_l, source, g_query, final):
        self.index, self.log_inv_rate, self.cols, self.k = index, rate, cols, k
        self.a0, self.list_size, self.source, self.g_query, self.final = a0, big_l, source, g_query, final
        self.log_block, self.degree = cols + rate, (1 << cols) - 1 + k
        self.sbar, self.queries = None, None

    @property
    def points(self):
        return self.sbar[-1]

    def finish(self, sched, g_point, g_fold):
        """sched: 'batch' or 'ladder'. Returns False when no schedule within the cap exists."""
        if sched == "ladder":
            self.sbar = ladder_schedule(self.list_size, self.degree, self.k, g_point, g_fold)
        else:
            s = one_batch(self.list_size, self.degree, self.k, g_point, g_fold)
            self.sbar = None if s is None else (s,) * self.k
        if self.sbar is None:
            return False
        self.queries = query_count(self.log_block, self.a0 + self.k, self.points, self.g_query, self.final)
        return True

    def bytes(self, fill=1.0):
        """The level's query phase plus its point scalars."""
        words = c8.leaf_words(self.index, self.k)
        if self.index == 0 and fill < 1.0:
            words = min(words, math.ceil(fill * words - 1e-9))
        depth, t = self.log_block, self.queries
        phase = 16 + 4 * t + c8.expected_distinct(1 << depth, t) * 8 * words + c8.DIGEST * c8.expected_siblings(depth, t)
        return phase + c8.SCALAR * scalars_of(self.sbar)

    def point_cycles(self):
        """Guest cycles of the level's points (estimate): note 11's count, two cycles a field product and 20 a
        point, with the carried update counted for the rounds a point is held."""
        kappa, ell, s = self.cols, self.k, self.points
        per = 3 * (kappa + 1) + (2 * ((1 << kappa) + ell) if self.final else (2 * ell + 4) + (2 * kappa + 1))
        return 2 * (3 * sum(self.sbar) + s * per) + 20 * s

    def cycle_equiv(self):
        """Guest cycle-equivalents of the level: query cycles, 8 a KECCAK step of its paths, and its points."""
        depth, t = self.log_block, self.queries
        cap = c8.merkle_cap_depth(t, depth)
        perms = c8.leaf_perms(c8.leaf_words(self.index, self.k))
        keccak = t * (perms + depth - cap) + c8.expected_cap_hashes(cap, t) + scalars_of(self.sbar) / 4
        return t * c8.guest_query_cycles(self.index, self.k, depth - cap, self.cols, self.final) + 8 * keccak + self.point_cycles()


def johnson_level(index, rate, cols, k, g_query, final, sched="ladder", g_point=15, g_fold=7):
    """The fewest queries the Johnson bound allows, at the largest threshold with that count (smallest list)."""
    log_n, d = cols + rate, (1 << cols) - 1 + k
    n = 1 << log_n
    t = query_count(log_n, isqrt(n * d) + 1 + k, S_HOLD, g_query, final)
    a0 = max(max_end(log_n, t, S_HOLD, g_query, final) - k, isqrt(n * d) + 1)
    lv = Level(index, rate, cols, k, a0, johnson(n, a0, d), "Johnson", g_query, final)
    assert lv.finish(sched, g_point, g_fold) and lv.points <= S_HOLD
    return lv


def below_johnson_levels(index, rate, cols, k, g_query, final, sched="ladder", g_point=15, g_fold=7, max_points=128):
    """Every level with fewer queries than the Johnson level whose list is bounded by a proven bound of section 1
    and paid for with at most `max_points` points: one candidate per query count (the largest threshold)."""
    log_n, d = cols + rate, (1 << cols) - 1 + k
    n, out = 1 << log_n, []
    base = johnson_level(index, rate, cols, k, g_query, final, sched, g_point, g_fold)
    bits_per_point = LOG_Q - math.log2(d + (1 << k))
    for t in range(base.queries - 1, 0, -1):
        a0 = max_end(log_n, t, max_points, g_query, final) - k
        if a0 < d + 2:  # standing assumption (S2)
            break
        if a0 * a0 > n * d:
            continue
        if 3 * list_bits_estimate(n, a0, d) > max_points * bits_per_point:
            break
        big_l, src = best_list(n, a0, d)
        lv = Level(index, rate, cols, k, a0, big_l, src, g_query, final)
        if not lv.finish(sched, g_point, g_fold) or lv.points > max_points:
            break
        out.append(lv)
    return base, out


# ---------------------------------------------------------------------------------------------------------------
# A whole opening: shape, levels, costs
# ---------------------------------------------------------------------------------------------------------------


def shape(mu, rate, folds, reductions):
    """[(log_inv_rate, kappa, ell)] of a ladder with the given fold rounds and the domain reduction after each
    level but the last; the final polynomial has 2^(mu - sum(folds)) + ell_last coefficients."""
    out, cols, r = [], mu, rate
    for i, k in enumerate(folds):
        cols -= k
        out.append((r, cols, k))
        if i + 1 < len(folds):
            r = r + k - reductions[i]
    return out


def deployed_shape(mu, rate, kn=wm.DEPLOYED):
    rates, cols, folds, _res = wm.ladder(mu, rate, kn)
    return list(zip(rates, cols, folds))


def encoding(shp, fill=1.0):
    """(K words, words times log2 block length, Merkle permutations) of all commitments, as `costs.cost`."""
    words_total = ntt = perms = 0
    for i, (r, c, k) in enumerate(shp):
        words = c8.leaf_words(i, k)
        block = words << (c + r)
        if i == 0:
            block = math.ceil(block * fill)
        words_total += block
        ntt += block * (c + r)
        perms += (c8.leaf_perms(words) + 1) << (c + r)
    return words_total, ntt, perms


_LEVELS: dict = {}


def level_options(index, rate, cols, k, g_query, final, sched, g_point=15, g_fold=7, max_points=128):
    key = (min(index, 1), rate, cols, k, g_query, final, sched, g_point, g_fold, max_points)
    if key not in _LEVELS:
        base, below = below_johnson_levels(min(index, 1), rate, cols, k, g_query, final, sched, g_point, g_fold, max_points)
        _LEVELS[key] = [base] + below
    return _LEVELS[key]


def build(shp, g_queries, sched="ladder", objective="bytes", lists="proven", g_point=15, g_fold=7, max_points=128):
    """One Level per level of the shape: among the Johnson level and (lists='proven') the levels below it with a
    proven list bound, the one with the least bytes or the least guest cycle-equivalents."""
    out = []
    for i, (r, c, k) in enumerate(shp):
        final = i == len(shp) - 1
        opts = level_options(i, r, c, k, g_queries[i], final, sched, g_point, g_fold, max_points)
        if lists == "johnson":
            opts = opts[:1]
        key = (lambda lv: lv.bytes()) if objective == "bytes" else (lambda lv: lv.cycle_equiv())
        out.append(min(opts, key=key))
    return out


def cost(levels, g_point=15, g_fold=7, g_batch=7, fill=1.0):
    """Bytes, Keccak, guest cycles and grinding of a DEEP-fold opening (the stream of Protocol D with schedules).
    Mirrors `11_deep_fold_whir.deep_cost`, with a schedule and a query grind per level."""
    sponge = c8.SpongeCount()
    n_levels = len(levels)
    first = levels[0].sbar[0]
    scalars = 2 + (1 if g_point else 0) + first  # root, nonce, answers of the first batch
    sponge.absorb(2)
    sponge.grind(g_point)
    sponge.sample(2 * first)
    sponge.absorb(first)
    scalars += 1 if g_batch else 0
    sponge.grind(g_batch)
    sponge.sample()
    grind = n_levels * (1 << g_point) + (1 << g_batch)
    merkle_bytes = guest_merkle = query_cycles = point_cycles = 0.0
    native_merkle = 0
    for i, lv in enumerate(levels):
        depth, t = lv.log_block, lv.queries
        for j in range(lv.k):
            fresh = lv.sbar[j] - lv.sbar[j - 1] if j else 0  # answers of batch j + 1, sent before the round
            scalars += fresh + 4 + lv.sbar[j] + (1 if g_fold else 0)
            sponge.absorb(fresh + 4 + lv.sbar[j])
            sponge.grind(g_fold)
            nxt = lv.sbar[j + 1] - lv.sbar[j] if j + 1 < lv.k else 0
            sponge.sample(2 + 2 * nxt)
        grind += lv.k * (1 << g_fold) + (1 << lv.g_query)
        per_word = 128 // depth
        if lv.final:
            n_final = (1 << lv.cols) + lv.k
            scalars += n_final + 1 + 2 * lv.cols
            sponge.absorb(n_final)
            sponge.grind(lv.g_query)
            sponge.sample(-(-t // per_word))
            for _ in range(lv.cols):
                sponge.absorb(2)
                sponge.sample()
        else:
            s_next = levels[i + 1].sbar[0]
            scalars += 2 + lv.k + (1 if g_point else 0) + s_next + 1
            sponge.absorb(2 + lv.k)
            sponge.grind(g_point)
            sponge.sample(2 * s_next)
            sponge.absorb(s_next)
            sponge.grind(lv.g_query)
            sponge.sample(-(-t // per_word))
            sponge.sample()
        words = c8.leaf_words(i, lv.k)
        perms = c8.leaf_perms(words)
        sent = words if not (i == 0 and fill < 1.0) else min(words, math.ceil(fill * words - 1e-9))
        merkle_bytes += 16 + 4 * t + c8.expected_distinct(1 << depth, t) * 8 * sent + c8.DIGEST * c8.expected_siblings(depth, t)
        cap = c8.merkle_cap_depth(t, depth)
        guest_merkle += t * (perms + depth - cap) + c8.expected_cap_hashes(cap, t)
        native_merkle += t * (perms + depth)
        query_cycles += t * c8.guest_query_cycles(i, lv.k, depth - cap, lv.cols, lv.final)
        point_cycles += lv.point_cycles()
    guest_keccak = guest_merkle + sponge.perms
    return {
        "bytes": merkle_bytes + c8.SCALAR * scalars,
        "scalars": scalars,
        "point_scalars": sum(scalars_of(lv.sbar) for lv in levels),
        "guest_keccak": guest_keccak,
        "native_keccak": native_merkle + sponge.perms,
        "query_cycles": query_cycles,
        "point_cycles": point_cycles,
        "cycle_equiv": query_cycles + point_cycles + 8 * guest_keccak,
        "grind": grind,
        "queries": [lv.queries for lv in levels],
        "points": [lv.points for lv in levels],
    }


def today_cost(mu, rate, kn=wm.DEPLOYED, fill=1.0):
    """Today's protocol at the knobs `kn` (note 08's model), in the same units."""
    cfg = wm.derive(mu, rate, kn)
    c = c8.cost(cfg, fill)
    return {
        "bytes": c.proof_bytes,
        "scalars": c.stream_scalars,
        "point_scalars": len(cfg.levels),
        "guest_keccak": c.guest_keccak,
        "native_keccak": c.native_keccak,
        "query_cycles": c.guest_cycles,
        "point_cycles": 0.0,
        "cycle_equiv": c.guest_cycles + 8 * c.guest_keccak,
        "grind": c.grind_perms,
        "queries": cfg.queries,
        "points": [1] * len(cfg.levels),
        "encoding": (c.encode_words, c.encode_ntt, c.commit_perms),
    }


def point_prover_share(levels, mu, rate):
    """Estimated share of `Prove` taken by the points, net of today's OOD evaluations, from note 24's measured
    units (one OOD evaluation of the stack = 1): a fused first batch of s points costs 0.9 + 0.45 s, a later
    point of level 0 0.37, the conversion 0.083 a point, a point of a later level 0.057 per 2^(mu - 6) message
    elements; one unit is 0.34 percent of Prove at rate 1/2 and 0.78 of that at rate 1/4 (lower rates: the 1/4
    value, an upper estimate). Today's OOD evaluations are 1.05 units."""
    lv0 = levels[0]
    units = 0.9 + 0.45 * lv0.sbar[0] + 0.37 * (lv0.points - lv0.sbar[0]) + 0.083 * lv0.points
    for lv in levels[1:]:
        units += 0.057 * lv.points * 2.0 ** (lv.cols + lv.k - (mu - 6))
    return (units - 1.05) * 0.34 * (1.0 if rate == 1 else 0.78)


def selftest():
    # the paper's points table (section 7.1) and its two ladders
    want = {(24, 6): [11, 11, 12, 13, 14, 14, 21], (20, 4): [8, 8, 9, 10, 11, 12, 18], (4, 4): [7, 7, 8, 9, 10, 10, 16]}
    for (kap, ell), row in want.items():
        d = (1 << kap) - 1 + ell
        assert [one_batch(1 << b, d, ell) for b in (7, 10, 40, 70, 100, 130, 340)] == row
    assert ladder_schedule(1 << 40, (1 << 24) + 5, 6) == (6, 7, 8, 10, 11, 12)
    assert ladder_schedule(1 << 100, (1 << 24) + 5, 6) == (8, 9, 10, 11, 12, 14)
    # the shapes of note 08, and its numbers for today's protocol
    assert deployed_shape(30, 1) == shape(30, 1, [6, 4, 4, 4, 4, 4], [3, 1, 1, 1, 1])
    assert round(today_cost(30, 1)["bytes"] / 1024, 1) == 335.9
    # the paper's Johnson instance (one batch, counting at the last level allowed at A0 = d + 1 there)
    lv = build(deployed_shape(30, 1), [17] * 6, sched="batch")
    print("mu 30, rate 1/2, one batch, proven lists:", [x.queries for x in lv], [x.points for x in lv], f"{cost(lv)['bytes'] / 1024:.1f} KiB")
    # list bounds: the shortened bound never exceeds the counting bound, and equals Johnson at j = 0
    for n, a, d in [(1 << 10, 40, 19), (1 << 12, 300, 67), (1 << 8, 30, 7), (64, 24, 7)]:
        b, _src = best_list(n, a, d)
        assert b <= counting(n, a, d), (n, a, d)
    print("selftest passed")


if __name__ == "__main__":
    selftest()
