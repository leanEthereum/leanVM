#!/usr/bin/env python3
"""DEEP-fold WHIR: parameters and costs as a function of the proven list bound (researcher 11, note 11).

Standard library only. Builds on the validated model of note 08 (`08_retuning/whir_model.py` for the ladder and for
today's queries, `08_retuning/costs.py` for today's bytes and Keccak counts and for the Merkle formulas).

The protocol modelled is Protocol D of note 11: after each commitment the verifier sends s points (theta, zeta) in
E^2, the prover answers one scalar per point, then one scalar per point per fold round; a level's point claims are
converted at its end and batched with the residual and the queries. Error terms (Theorem D of note 11), q = 2^128:

  points of level i      [C(L, 2) + 4 L^3 q^6 / K0^3 * sum_{j < ell} tau^-j] * ((d + 2^ell) / q)^s
  batching lambda_0      (J0 - 1) / q
  fold round             K0 / q^2 + tau
  query message          ((A_end - 1) / n)^t + (t + s) / q      (no second term at the last level)
  tail round             2 / q

with K0 = 2^(g_fold + 2) q and tau = 2^-(126 - g_fold), so a fold round is exactly 2^-125 after its grind. Every
accept/reject below is an exact integer comparison.

Usage:
  python3 11_deep_fold_whir.py            all tables of note 11 (a few seconds)
  python3 11_deep_fold_whir.py selftest   consistency checks of the model against note 08's
"""

from __future__ import annotations

import math
import os
import sys
from dataclasses import dataclass, replace
from fractions import Fraction
from math import comb, isqrt

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "08_retuning"))
import costs as c8  # noqa: E402
import whir_model as wm  # noqa: E402

LOG_Q = 128
Q = 1 << LOG_Q


@dataclass(frozen=True)
class Grinds:
    """Grinding bits of the DEEP-fold opening. The batching grind is the least that fits (J0 - 1) / q."""

    query: int = 17
    fold: int = 7
    point: int = 15
    batch: int = 7
    target: int = 125
    stacked_claims: int = 514


DEPLOYED_GRINDS = Grinds()
NO_GRINDS = Grinds(fold=0, point=0)  # only the query and the batching messages grind


# --------------------------------------------------------------------------------------------------------------
# Error terms, exactly
# --------------------------------------------------------------------------------------------------------------


def fold_split(g: Grinds):
    """(log2(K0 / q), -log2 tau): the fold round's two terms, each 2^-(126 - g_fold)."""
    return g.fold + 2, 126 - g.fold


def points_ok(list_size: int, d: int, ell: int, s: int, g: Grinds) -> bool:
    """[C(L,2) + 4 L^3 q^3 2^(-3k) sum_{j<ell} 2^(T j)] (d + 2^ell)^s / q^s <= 2^(3 + g_point) / q, exactly."""
    k, big_t = fold_split(g)
    nested = sum(1 << (big_t * j) for j in range(ell))
    lhs = (comb(list_size, 2) << (3 * k)) + 4 * list_size**3 * Q**3 * nested
    lhs *= (d + (1 << ell)) ** s * Q
    rhs = (1 << (3 + g.point + 3 * k)) * Q**s
    return lhs <= rhs


def points_needed(list_size: int, d: int, ell: int, g: Grinds) -> int:
    s = 1
    while not points_ok(list_size, d, ell, s, g):
        s += 1
    return s


def point_bits(list_size: int, d: int, ell: int, g: Grinds) -> float:
    """log2 of the bracket of the point error, plus the target after the grind: what s log2(1/eps) must reach."""
    k, big_t = fold_split(g)
    nested = sum(1 << (big_t * j) for j in range(ell))
    bracket = comb(list_size, 2) + Fraction(4 * list_size**3 * Q**3 * nested, 1 << (3 * k))
    return log2_big(bracket.numerator) - log2_big(bracket.denominator) + (g.target - g.point)


def log2_big(x: int) -> float:
    if x <= 0:
        return float("-inf")
    shift = max(x.bit_length() - 1000, 0)
    return math.log2(x >> shift) + shift


def query_ok(log_n: int, a_end: int, t: int, s: int, g: Grinds, final: bool) -> bool:
    n = 1 << log_n
    if final:
        return (a_end - 1) ** t << (g.target - g.query) <= n**t
    room = (1 << (LOG_Q - g.target + g.query)) - (t + s)
    return room > 0 and (a_end - 1) ** t * Q <= room * n**t


def query_count(log_n: int, a_end: int, s: int, g: Grinds, final: bool) -> int:
    assert 1 < a_end <= 1 << log_n
    t = 1
    while not query_ok(log_n, a_end, t, s, g, final):
        t += 1
    return t


def max_end(log_n: int, t: int, s: int, g: Grinds, final: bool) -> int:
    """The largest A_end for which t queries suffice."""
    lo, hi = 1, 1 << log_n
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if query_ok(log_n, mid, t, s, g, final):
            lo = mid
        else:
            hi = mid - 1
    return lo


def johnson_list(n: int, a: int, d: int):
    den = a * a - n * d
    return None if den <= 0 else n * (a - d) // den


def counting_list(n: int, a: int, d: int) -> int:
    """Every tuple of degree <= d is fixed by d + 1 of its agreement points: L C(a, d+1) <= C(n, d+1)."""
    assert a >= d + 1
    return comb(n, d + 1) // comb(a, d + 1)


# --------------------------------------------------------------------------------------------------------------
# Levels
# --------------------------------------------------------------------------------------------------------------

S_CAP = 64  # an upper bound on s used while a level's threshold is chosen (the query term has (t + s) / q)


@dataclass
class Level:
    log_inv_rate: int
    cols: int  # kappa
    k: int  # ell
    a0: int  # A^(i,0): the threshold the list bound is assumed at
    list_size: int  # L_i
    source: str  # where L_i comes from
    points: int = 0  # s_i
    queries: int = 0

    @property
    def log_block(self):
        return self.cols + self.log_inv_rate

    @property
    def degree(self):
        return (1 << self.cols) - 1 + self.k

    @property
    def a_end(self):
        return self.a0 + self.k


def finish(lv: Level, g: Grinds, final: bool) -> Level:
    lv.points = points_needed(lv.list_size, lv.degree, lv.k, g)
    assert lv.points <= S_CAP
    lv.queries = query_count(lv.log_block, lv.a_end, lv.points, g, final)
    return lv


def johnson_level(rate, cols, k, g, final) -> Level:
    """The fewest queries the Johnson bound allows, then the largest threshold with that count (smallest list)."""
    log_n, d = cols + rate, (1 << cols) - 1 + k
    n = 1 << log_n
    t = query_count(log_n, isqrt(n * d) + 1 + k, S_CAP, g, final)
    a0 = max_end(log_n, t, S_CAP, g, final) - k
    return finish(Level(rate, cols, k, a0, johnson_list(n, a0, d), "Johnson"), g, final)


def assumed_level(rate, cols, k, g, final, tau: Fraction, list_bits: int, label=None) -> Level:
    """ListBound(rho, tau, 2^b) as a hypothesis: A^(i,0) = ceil(tau n), L = 2^b."""
    n = 1 << (cols + rate)
    a0 = -((-tau.numerator * n) // tau.denominator)
    d = (1 << cols) - 1 + k
    assert a0 >= d + 1, "threshold at or below capacity"
    return finish(Level(rate, cols, k, a0, 1 << list_bits, label or f"assumed {float(tau):.4g}, 2^{list_bits}"), g, final)


def level_bytes(index, lv: Level, fill=1.0) -> float:
    """The level's query phase plus its point scalars."""
    words = c8.leaf_words(index, lv.k)
    if index == 0 and fill < 1.0:
        words = min(words, math.ceil(fill * words - 1e-9))
    depth, t = lv.log_block, lv.queries
    phase = 16 + 4 * t + c8.expected_distinct(1 << depth, t) * 8 * words + c8.DIGEST * c8.expected_siblings(depth, t)
    return phase + c8.SCALAR * lv.points * (1 + lv.k)


_COUNTING_CACHE: dict = {}


def counting_level(index, rate, cols, k, g, final) -> Level:
    """The cheapest threshold whose list is bounded by counting, the Johnson threshold included."""
    key = (index > 0, rate, cols, k, g, final)
    if key not in _COUNTING_CACHE:
        _COUNTING_CACHE[key] = _counting_level(index, rate, cols, k, g, final)
    return replace(_COUNTING_CACHE[key])


def _counting_level(index, rate, cols, k, g, final) -> Level:
    best = johnson_level(rate, cols, k, g, final)
    log_n, d = cols + rate, (1 << cols) - 1 + k
    for t in range(best.queries - 1, 0, -1):
        a0 = max_end(log_n, t, S_CAP, g, final) - k
        if a0 < d + 1:
            break
        if 3 * (d + 1) * (log_n - math.log2(a0)) > S_CAP * LOG_Q:
            break  # C(n, d+1) / C(a0, d+1) >= (n / a0)^(d+1): more list than S_CAP points pay for
        size = counting_list(1 << log_n, a0, d)
        if not points_ok(size, d, k, S_CAP, g):
            break
        cand = finish(Level(rate, cols, k, a0, size, "counting"), g, final)
        if level_bytes(index, cand) < level_bytes(index, best):
            best = cand
    return best


def build(mu, rate, g=DEPLOYED_GRINDS, level0=None, later="johnson", last="counting", gamma=None, gamma_bits=None):
    """The levels of a DEEP-fold opening.

    level0: None (Johnson) or (tau, b). later: 'johnson', or 'gamma' with `gamma` and `gamma_bits`, which assumes at
    every level ListBound(rho_i, rho_i^gamma, 2^gamma_bits). last: 'counting' takes, at every level after the first,
    the counting bound where it gives fewer bytes than Johnson (in practice the last one or two levels); 'johnson'
    never does (ignored under 'gamma')."""
    rates, cols, folds, _residual = wm.ladder(mu, rate)
    out = []
    for i, (r, c, k) in enumerate(zip(rates, cols, folds)):
        final = i == len(rates) - 1
        if later == "gamma":
            n, d = 1 << (c + r), (1 << c) - 1 + k
            a0 = max(math.ceil(n * 2.0 ** (-gamma * r)), d + 1)
            tau = Fraction(a0, n)
            lv = assumed_level(r, c, k, g, final, tau, gamma_bits, f"assumed rho^{gamma:.3f}, 2^{gamma_bits}")
        elif i == 0 and level0 is not None:
            lv = assumed_level(r, c, k, g, final, Fraction(level0[0]).limit_denominator(1 << 20), level0[1])
        elif i >= 1 and last == "counting":
            lv = counting_level(i, r, c, k, g, final)
        else:
            lv = johnson_level(r, c, k, g, final)
        out.append(lv)
    return out


# --------------------------------------------------------------------------------------------------------------
# Costs
# --------------------------------------------------------------------------------------------------------------


@dataclass
class Cost:
    proof_bytes: float
    merkle_bytes: float
    stream_scalars: int
    point_scalars: int
    fs_perms: int
    guest_keccak: float
    native_keccak: int
    guest_query_cycles: float
    grind_perms: int
    mults: dict


def deep_cost(mu, levels, g=DEPLOYED_GRINDS, fill=1.0) -> Cost:
    """Bytes, Keccak and grinding of a DEEP-fold opening: `08_retuning/costs.cost` with the new stream."""
    sponge = c8.SpongeCount()
    n_levels = len(levels)
    s0 = levels[0].points
    # Commitment: root, grind, 2 s_0 point coordinates, s_0 answers. Then the batching grind and lambda_0.
    scalars = 2 + (1 if g.point else 0) + s0
    sponge.absorb(2)
    sponge.grind(g.point)
    sponge.sample(2 * s0)
    sponge.absorb(s0)
    scalars += 1 if g.batch else 0
    sponge.grind(g.batch)
    sponge.sample()
    grind = n_levels * (1 << g.point if g.point else 0) + (1 << g.batch if g.batch else 0)
    point_scalars = s0
    merkle_bytes, guest_merkle, native_merkle, cycles = 0.0, 0.0, 0, 0.0
    for i, lv in enumerate(levels):
        final = i == n_levels - 1
        depth, t, s = lv.log_block, lv.queries, lv.points
        for _ in range(lv.k):
            scalars += 4 + s + (1 if g.fold else 0)
            sponge.absorb(4 + s)
            sponge.grind(g.fold)
            sponge.sample(2)
        point_scalars += s * lv.k
        grind += lv.k * (1 << g.fold if g.fold else 0) + (1 << g.query if g.query else 0)
        per_word = 128 // depth
        if final:
            n_final = (1 << lv.cols) + lv.k
            scalars += n_final + (1 if g.query else 0) + 2 * lv.cols
            sponge.absorb(n_final)
            sponge.grind(g.query)
            sponge.sample(-(-t // per_word))
            for _ in range(lv.cols):
                sponge.absorb(2)
                sponge.sample()
        else:
            s_next = levels[i + 1].points
            scalars += 2 + lv.k + (1 if g.point else 0) + s_next + (1 if g.query else 0)
            point_scalars += s_next
            sponge.absorb(2 + lv.k)
            sponge.grind(g.point)
            sponge.sample(2 * s_next)
            sponge.absorb(s_next)
            sponge.grind(g.query)
            sponge.sample(-(-t // per_word))
            sponge.sample()
        words = c8.leaf_words(i, lv.k)
        perms = c8.leaf_perms(words)
        sent = words if not (i == 0 and fill < 1.0) else min(words, math.ceil(fill * words - 1e-9))
        merkle_bytes += 16 + 4 * t + c8.expected_distinct(1 << depth, t) * 8 * sent + c8.DIGEST * c8.expected_siblings(depth, t)
        cap = c8.merkle_cap_depth(t, depth)
        guest_merkle += t * (perms + depth - cap) + c8.expected_cap_hashes(cap, t)
        native_merkle += t * (perms + depth)
        cycles += t * c8.guest_query_cycles(i, lv.k, depth - cap, lv.cols, final)
    return Cost(
        proof_bytes=merkle_bytes + c8.SCALAR * scalars,
        merkle_bytes=merkle_bytes,
        stream_scalars=scalars,
        point_scalars=point_scalars,
        fs_perms=sponge.perms,
        guest_keccak=guest_merkle + sponge.perms,
        native_keccak=native_merkle + sponge.perms,
        guest_query_cycles=cycles,
        grind_perms=grind,
        mults=verifier_mults(mu, levels, deep=True),
    )


def verifier_mults(mu, levels, deep: bool) -> dict:
    """Field multiplications of the native verifier's WHIR opening, counted from `crates/verifier/src/whir.rs` by
    formula (not measured): EE = E by E, EK = E by K, KK = K by K. `levels` need .cols, .k, .queries and, when
    `deep`, .points. The outer weight (`evaluate_basis`) and the Merkle hashing are not field work and are left out.

    Today: a fold round is 4 EE. A query costs the chain What_i(x) (3 (kappa + 1) KK), the row fold (2^ell - 1 products,
    the first round's E by K at level 0, plus ell EK for beta x), the high-part correction (about 2 ell + 1), one
    EE for its lambda power and one for the batch, then at the terminal point the chain again and kappa EK + kappa EE
    for its column weight. An OOD claim is kappa EE at the terminal point. The last level evaluates the final
    polynomial at each query (2^kappa + ell KK for the basis, as many EK) and closes with a sumcheck and one
    multilinear evaluation.

    DEEP removes the OOD weights and adds, per point: 3 EE a fold round; at the level's end the chain What_i(zeta)
    over E ((kappa + 1) (2 EK + 1 EE)), the high-part correction (2 ell + 2 EE) and 2 EE for the batch; at the
    terminal point 2 kappa + 1 EE. At the last level a point is one evaluation of the final polynomial at zeta
    (chain, then 2 (2^kappa + ell) EE)."""
    ee = ek = kk = 0
    n_levels = len(levels)
    if not deep:
        ee += mu  # the commitment's OOD claim eq(z_0, .) at the terminal point
    for i, lv in enumerate(levels):
        final = i == n_levels - 1
        kappa, ell, t = lv.cols, lv.k, lv.queries
        ee += 4 * ell
        kk += (kappa + 1) * (kappa + 2)  # Subspace::new
        chain = 3 * (kappa + 1)
        half = 1 << (ell - 1)
        row_ee = (half - 1) if i == 0 else (2 * half - 1)
        row_ek = (half if i == 0 else 0) + ell
        if final:
            n_final = (1 << kappa) + ell
            kk += t * (chain + n_final)
            ek += t * (row_ek + n_final)
            ee += t * row_ee
            ee += 3 * kappa + (1 << kappa)  # tail sumcheck and the final multilinear evaluation
        else:
            kk += t * (2 * chain + ell)
            ek += t * (row_ek + ell + 1 + kappa)
            ee += t * (row_ee + 2 + kappa)
            if not deep:
                ee += kappa + 2  # the next level's OOD claim
        if deep:
            s = lv.points
            ee += 3 * s * ell
            ek += 2 * s * (kappa + 1)
            ee += s * (kappa + 1)
            if final:
                ee += 2 * s * ((1 << kappa) + ell)
            else:
                ee += s * (2 * ell + 4) + s * (2 * kappa + 1)
    return {"EE": ee, "EK": ek, "KK": kk, "total": ee + ek + kk}


def point_guest_cycles(levels) -> float:
    """A rough estimate of the guest's extra cycles for the points: two cycles a field multiplication of the point
    path (the ratio note 08 fitted on the query path), plus 20 a point. Not calibrated on a DEEP guest."""
    total = 0.0
    for i, lv in enumerate(levels):
        final = i == len(levels) - 1
        kappa, ell, s = lv.cols, lv.k, lv.points
        per = 3 * ell + 3 * (kappa + 1)
        per += 2 * ((1 << kappa) + ell) if final else (2 * ell + 4) + (2 * kappa + 1)
        total += s * (2 * per + 20)
    return total


def prover_extra(mu, rate, levels, fill=1.0):
    """Carry-less multiplications of the point evaluations at commit time, next to the encoder's multiplications.

    Level 0: each point needs the 2^ell lane values P_u(zeta), one pass of 2^mu K by E products (2 carry-less
    multiplications each, accumulated unreduced). Later levels: 2^(nu_i) E by E products a point. The NTT of level i
    takes kappa_i / 2 multiplications a codeword word (Annex D, Proposition prop:ntt)."""
    lv0 = levels[0]
    deep0 = 2 * lv0.points * fill * 2.0**mu
    ntt0 = 0.5 * lv0.cols * fill * 2.0 ** (mu + rate)
    later = sum(3 * lv.points * 2.0 ** (lv.cols + lv.k) for lv in levels[1:])
    return {"deep_level0_clmul": deep0, "ntt_level0_kmul": ntt0, "ratio": deep0 / ntt0, "later_clmul": later}


def today(mu, rate, fill=1.0):
    cfg = wm.derive(mu, rate)
    cost = c8.cost(cfg, fill)

    class _L:
        def __init__(self, lv):
            self.cols, self.k, self.queries = lv.cols, lv.k, lv.queries

    return cfg, cost, verifier_mults(mu, [_L(lv) for lv in cfg.levels], deep=False)


# --------------------------------------------------------------------------------------------------------------
# Tables
# --------------------------------------------------------------------------------------------------------------

MUS = (24, 28, 30)
RATES = (1, 2, 3, 4)
LEVEL0_THRESHOLDS = {
    1: [("0.66", Fraction(66, 100)), ("0.64", Fraction(64, 100)), ("5/8", Fraction(5, 8)), ("9/16", Fraction(9, 16))],
    2: [("7/16", Fraction(7, 16)), ("3/8", Fraction(3, 8)), ("5/16", Fraction(5, 16))],
    3: [("5/16", Fraction(5, 16)), ("1/4", Fraction(1, 4)), ("3/16", Fraction(3, 16))],
    4: [("3/16", Fraction(3, 16)), ("1/8", Fraction(1, 8)), ("3/32", Fraction(3, 32))],
}
LIST_BITS = (10, 40, 70, 100)


def kib(x):
    return f"{x / 1024:.1f}"


def pct(new, old):
    return f"{100 * (new / old - 1):+.1f}%"


def lists_str(levels):
    return " ".join(f"2^{log2_big(lv.list_size):.0f}" for lv in levels)


def table_points_budget():
    print("## T1. Bits of list one point pays for, and the points a list needs (deployed grinds 17/7/15/7)\n")
    print("| level shape | kappa | ell | log2(1/eps) | bits needed at L = 1 | s for L = 2^10, 2^40, 2^70, 2^100, 2^334 |")
    print("| --- | --- | --- | --- | --- | --- |")
    for name, kappa, ell in (("mu=30 level 0", 24, 6), ("mu=30 level 1", 20, 4), ("mu=30 level 3", 12, 4), ("mu=30 level 5", 4, 4), ("mu=24 level 4", 2, 4)):
        d = (1 << kappa) - 1 + ell
        eps = LOG_Q - math.log2(d + (1 << ell))
        ss = [points_needed(1 << b, d, ell, DEPLOYED_GRINDS) for b in (10, 40, 70, 100, 334)]
        print(f"| {name} | {kappa} | {ell} | {eps:.1f} | {point_bits(1, d, ell, DEPLOYED_GRINDS):.0f} | {', '.join(map(str, ss))} |")
    print()


def row_today(mu, rate):
    cfg, cost, mults = today(mu, rate)
    return cfg, cost, mults


def table_no_new_theorem():
    print("## T2. No new theorem: Johnson lists at every level, counting list at the last level\n")
    print("| mu | rate | | queries per level | points per level | list bounds (log2) | WHIR bytes (KiB) | of which point scalars | native Keccak | guest Keccak | verifier field mults (EE / all) | grind (log2 perms) |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for mu in MUS:
        for rate in RATES:
            cfg, cost, mults = today(mu, rate)
            print(
                f"| {mu} | 1/{1 << rate} | today | {' '.join(map(str, cfg.queries))} | 1 multilinear | {' '.join(str(lv.list_bound) for lv in cfg.levels)} | {kib(cost.proof_bytes)} | "
                f"| {cost.native_keccak} | {cost.guest_keccak:.0f} | {mults['EE']} / {mults['total']} | {math.log2(cost.grind_perms):.2f} |"
            )
            for label, kwargs in (("DEEP, Johnson", dict(last="johnson")), ("DEEP, Johnson + counting", dict(last="counting"))):
                lv = build(mu, rate, **kwargs)
                c = deep_cost(mu, lv)
                print(
                    f"| | | {label} | {' '.join(str(x.queries) for x in lv)} | {' '.join(str(x.points) for x in lv)} | {lists_str(lv)} | {kib(c.proof_bytes)} ({pct(c.proof_bytes, cost.proof_bytes)}) | {kib(16 * c.point_scalars)} "
                    f"| {c.native_keccak} ({pct(c.native_keccak, cost.native_keccak)}) | {c.guest_keccak:.0f} ({pct(c.guest_keccak, cost.guest_keccak)}) | {c.mults['EE']} / {c.mults['total']} | {math.log2(c.grind_perms):.2f} |"
                )
    print()


def table_listbound_level0():
    print("## T3. Queries and proof size as a function of the proven ListBound at level 0 (later levels as in T2, last row)\n")
    print("| rate | level-0 threshold | bits a query | level-0 queries | s_0 at mu=30 for lists 2^10, 2^40, 2^70, 2^100 | KiB at mu = 24 / 28 / 30, list 2^40 | KiB at mu = 30, list 2^100 | guest Keccak, mu=30, list 2^40 | level-0 query cycles saved, mu=30 (est.) |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for rate in RATES:
        base = {mu: today(mu, rate) for mu in MUS}
        cfg30, cost30 = base[30][0], base[30][1]
        l0 = cfg30.levels[0]
        print(f"| 1/{1 << rate} | today (Johnson, CWYZ fold) | {l0.log_block - math.log2(l0.agreement - 1):.3f} | {cfg30.queries[0]} | 1 multilinear point | " + " / ".join(kib(base[mu][1].proof_bytes) for mu in MUS) + f" | | {cost30.guest_keccak:.0f} | |")
        lv = {mu: build(mu, rate) for mu in MUS}
        cs = {mu: deep_cost(mu, lv[mu]) for mu in MUS}
        d0 = lv[30][0]
        cyc = lambda x: c8.guest_query_cycles(0, 6, x.log_block - c8.merkle_cap_depth(x.queries, x.log_block), x.cols, False) * x.queries
        cyc_today = cyc(l0)
        print(
            f"| | Johnson, DEEP fold (no new theorem) | {d0.log_block - math.log2(d0.a_end - 1):.3f} | {d0.queries} | {d0.points} (Johnson list 2^{log2_big(d0.list_size):.0f}) | "
            + " / ".join(f"{kib(cs[mu].proof_bytes)} ({pct(cs[mu].proof_bytes, base[mu][1].proof_bytes)})" for mu in MUS)
            + f" | | {cs[30].guest_keccak:.0f} ({pct(cs[30].guest_keccak, cost30.guest_keccak)}) | {cyc_today - cyc(d0):.0f} |"
        )
        for name, tau in LEVEL0_THRESHOLDS[rate]:
            ss = [build(30, rate, level0=(tau, b))[0].points for b in LIST_BITS]
            lv = {mu: build(mu, rate, level0=(tau, 40)) for mu in MUS}
            cs = {mu: deep_cost(mu, lv[mu]) for mu in MUS}
            c100 = deep_cost(30, build(30, rate, level0=(tau, 100)))
            x = lv[30][0]
            print(
                f"| | {name} n | {x.log_block - math.log2(x.a_end - 1):.3f} | {x.queries} | {', '.join(map(str, ss))} | "
                + " / ".join(f"{kib(cs[mu].proof_bytes)} ({pct(cs[mu].proof_bytes, base[mu][1].proof_bytes)})" for mu in MUS)
                + f" | {kib(c100.proof_bytes)} ({pct(c100.proof_bytes, cost30.proof_bytes)}) | {cs[30].guest_keccak:.0f} ({pct(cs[30].guest_keccak, cost30.guest_keccak)}) | {cyc_today - cyc(x):.0f} |"
            )
    print()


def table_all_levels():
    print("## T4. ListBound assumed at every level: threshold rho_i^gamma n_i with lists 2^b (gamma = 1/2 is Johnson, 1 is capacity)\n")
    print("| rate | gamma (level-0 threshold) | b | queries per level (mu=30) | points per level | KiB at mu = 24 / 28 / 30 | native Keccak, mu=30 | guest Keccak, mu=30 |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for rate in RATES:
        base = {mu: today(mu, rate)[1] for mu in MUS}
        rows = [(name, math.log(float(tau)) / math.log(2.0**-rate)) for name, tau in LEVEL0_THRESHOLDS[rate]]
        for name, gamma in rows:
            for b in (40, 100):
                lv = {mu: build(mu, rate, later="gamma", gamma=gamma, gamma_bits=b) for mu in MUS}
                cs = {mu: deep_cost(mu, lv[mu]) for mu in MUS}
                print(
                    f"| 1/{1 << rate} | {gamma:.3f} ({name} n) | {b} | {' '.join(str(x.queries) for x in lv[30])} | {' '.join(str(x.points) for x in lv[30])} | "
                    + " / ".join(f"{kib(cs[mu].proof_bytes)} ({pct(cs[mu].proof_bytes, base[mu].proof_bytes)})" for mu in MUS)
                    + f" | {cs[30].native_keccak} ({pct(cs[30].native_keccak, base[30].native_keccak)}) | {cs[30].guest_keccak:.0f} ({pct(cs[30].guest_keccak, base[30].guest_keccak)}) |"
                )
    print()


def table_counting():
    print("## T5. The last two levels with the counting bound (provable today)\n")
    print("| mu | level | kappa | d | n | Johnson: queries, s, bytes | counting: queries, s, log2 L, bytes | saved |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    g = DEPLOYED_GRINDS
    for mu in MUS:
        for rate in (1, 4):
            rates, cols, folds, _ = wm.ladder(mu, rate)
            n_levels = len(rates)
            for i in (n_levels - 2, n_levels - 1):
                final = i == n_levels - 1
                j = johnson_level(rates[i], cols[i], folds[i], g, final)
                c = counting_level(i, rates[i], cols[i], folds[i], g, final)
                bj, bc = level_bytes(i, j), level_bytes(i, c)
                tag = "last" if final else "last but one"
                print(
                    f"| {mu}, rate 1/{1 << rate} | {i} ({tag}) | {cols[i]} | {j.degree} | 2^{j.log_block} | {j.queries}, {j.points}, {bj:.0f} | "
                    + (f"{c.queries}, {c.points}, {log2_big(c.list_size):.0f}, {bc:.0f}" if c.source == "counting" else "no gain")
                    + f" | {bj - bc:.0f} B |"
                )
    print()


def table_grinds_and_work():
    print("## T6. Grinding variants, verifier work and prover work (Johnson + counting)\n")
    print("| mu | rate | grinds (query/fold/point/batch) | points per level | KiB | guest Keccak | grind (log2 perms) | verifier mults EE / all (today) | guest point cycles (est.) | prover: point clmul over level-0 NTT mults |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for mu in MUS:
        for rate in (1, 2, 4):
            _cfg, cost, mults = today(mu, rate)
            for g in (DEPLOYED_GRINDS, NO_GRINDS, Grinds(fold=12, point=20)):
                lv = build(mu, rate, g=g)
                c = deep_cost(mu, lv, g)
                pe = prover_extra(mu, rate, lv)
                print(
                    f"| {mu} | 1/{1 << rate} | {g.query}/{g.fold}/{g.point}/{g.batch} | {' '.join(str(x.points) for x in lv)} | {kib(c.proof_bytes)} ({pct(c.proof_bytes, cost.proof_bytes)}) | {c.guest_keccak:.0f} ({pct(c.guest_keccak, cost.guest_keccak)}) "
                    f"| {math.log2(c.grind_perms):.2f} | {c.mults['EE']} / {c.mults['total']} ({mults['EE']} / {mults['total']}) | {point_guest_cycles(lv):.0f} | {pe['ratio']:.2f} |"
                )
    print()


def table_budget(mu=30, rate=1, tau=Fraction(64, 100), bits=40, g=DEPLOYED_GRINDS):
    print(f"## T7. Error of every verifier message, mu = {mu}, rate 1/{1 << rate}, ListBound(1/{1 << rate}, {float(tau)}, 2^{bits}) at level 0 (log2, after the grind)\n")
    levels = build(mu, rate, g, level0=(tau, bits))
    k, big_t = fold_split(g)
    print("| message | error before the grind (log2) | grind bits | after the grind |")
    print("| --- | --- | --- | --- |")
    print(f"| batching lambda_0 (J_0 = {g.stacked_claims}) | {math.log2(g.stacked_claims - 1) - 128:.2f} | {g.batch} | {math.log2(g.stacked_claims - 1) - 128 - g.batch:.2f} |")
    for i, lv in enumerate(levels):
        final = i == len(levels) - 1
        eps = math.log2(lv.degree + (1 << lv.k)) - 128
        pt = point_bits(lv.list_size, lv.degree, lv.k, g) - (g.target - g.point) + lv.points * eps
        print(f"| points of level {i} (s = {lv.points}, L = 2^{log2_big(lv.list_size):.0f}, {lv.source}) | {pt:.2f} | {g.point} | {pt - g.point:.2f} |")
        fold = math.log2(2.0 ** (k - 128) + 2.0**-big_t)
        print(f"| each of the {lv.k} fold rounds of level {i} | {fold:.2f} | {g.fold} | {fold - g.fold:.2f} |")
        qa = lv.queries * (math.log2(lv.a_end - 1) - lv.log_block)
        qb = float("-inf") if final else math.log2(lv.queries + lv.points) - 128
        tot = math.log2(2.0**qa + (0 if final else 2.0**qb))
        print(f"| query message of level {i} (t = {lv.queries}) | {tot:.2f} | {g.query} | {tot - g.query:.2f} |")
    print(f"| each tail round | -127.00 | 0 | -127.00 |")
    print()


def headline():
    print("## T0. Headline (rate 1/2 and 1/4, deployed grinds; later levels at Johnson, the last one or two by counting)\n")
    print("| configuration | level-0 queries | mu = 24 | mu = 28 | mu = 30 | guest Keccak, mu = 30 |")
    print("| --- | --- | --- | --- | --- | --- |")
    for rate, rows in ((1, [("0.66", Fraction(66, 100), 40), ("0.64", Fraction(64, 100), 40), ("5/8", Fraction(5, 8), 40), ("9/16", Fraction(9, 16), 100)]), (2, [("3/8", Fraction(3, 8), 40), ("5/16", Fraction(5, 16), 70)])):
        base = {mu: today(mu, rate) for mu in MUS}
        print(f"| rate 1/{1 << rate}, today | {base[30][0].queries[0]} | " + " | ".join(f"{kib(base[mu][1].proof_bytes)} KiB" for mu in MUS) + f" | {base[30][1].guest_keccak:.0f} |")
        lv = {mu: build(mu, rate) for mu in MUS}
        cs = {mu: deep_cost(mu, lv[mu]) for mu in MUS}
        print(f"| DEEP fold, no new theorem | {lv[30][0].queries} | " + " | ".join(f"{kib(cs[mu].proof_bytes)} ({pct(cs[mu].proof_bytes, base[mu][1].proof_bytes)})" for mu in MUS) + f" | {cs[30].guest_keccak:.0f} ({pct(cs[30].guest_keccak, base[30][1].guest_keccak)}) |")
        for name, tau, b in rows:
            lv = {mu: build(mu, rate, level0=(tau, b)) for mu in MUS}
            cs = {mu: deep_cost(mu, lv[mu]) for mu in MUS}
            print(f"| ListBound(1/{1 << rate}, {name}, 2^{b}) at level 0 | {lv[30][0].queries} | " + " | ".join(f"{kib(cs[mu].proof_bytes)} ({pct(cs[mu].proof_bytes, base[mu][1].proof_bytes)})" for mu in MUS) + f" | {cs[30].guest_keccak:.0f} ({pct(cs[30].guest_keccak, base[30][1].guest_keccak)}) |")
            gamma = math.log(float(tau)) / math.log(2.0**-rate)
            lv = {mu: build(mu, rate, later="gamma", gamma=gamma, gamma_bits=b) for mu in MUS}
            cs = {mu: deep_cost(mu, lv[mu]) for mu in MUS}
            print(f"| the same exponent at every level (threshold rho_i^{gamma:.3f} n_i, lists 2^{b}) | {lv[30][0].queries} | " + " | ".join(f"{kib(cs[mu].proof_bytes)} ({pct(cs[mu].proof_bytes, base[mu][1].proof_bytes)})" for mu in MUS) + f" | {cs[30].guest_keccak:.0f} ({pct(cs[30].guest_keccak, base[30][1].guest_keccak)}) |")
    print()


def selftest():
    # 1. With the points switched off and today's thresholds, the byte and Keccak formulas are note 08's.
    for mu in MUS:
        for rate in RATES:
            cfg, cost, _ = today(mu, rate)
            merkle = sum(16 + 4 * lv.queries + c8.expected_distinct(1 << lv.log_block, lv.queries) * 8 * c8.leaf_words(i, lv.k) + 32 * c8.expected_siblings(lv.log_block, lv.queries) for i, lv in enumerate(cfg.levels))
            assert abs(merkle - cost.merkle_bytes) < 1e-6, (mu, rate)
            # 2. The Johnson levels never take more queries than today's analysis, and at most S_CAP points.
            lv = build(mu, rate, last="johnson")
            assert all(a.queries <= b.queries for a, b in zip(lv, cfg.levels)), (mu, rate)
            floor = wm.johnson_limit_queries(cfg)
            assert all(a.queries >= f - 1 for a, f in zip(lv, floor)), (mu, rate, [a.queries for a in lv], floor)
            # 3. Every message is within 2^-125 after its grind, recomputed in floating point.
            g = DEPLOYED_GRINDS
            for i, x in enumerate(build(mu, rate)):
                final = i == len(lv) - 1
                eps = (x.degree + (1 << x.k)) / 2.0**128
                bits = point_bits(x.list_size, x.degree, x.k, g) - (g.target - g.point)
                assert bits + x.points * math.log2(eps) <= -(g.target - g.point) + 1e-6
                assert bits + (x.points - 1) * math.log2(eps) > -(g.target - g.point) - 1e-6, "s is not minimal"
                q_err = x.queries * (math.log2(x.a_end - 1) - x.log_block)
                assert q_err <= -(g.target - g.query) + 1e-9
                if x.source == "Johnson":
                    assert x.a0 * x.a0 > (1 << x.log_block) * x.degree
    # 4. The counting bound on a brute-forceable size: n = 8, d = 1, every word over GF(4) restricted to 3 symbols.
    import itertools

    n, d, a = 6, 1, 3
    pts = list(range(n))
    worst = 0
    lines = [(s, t) for s in range(7) for t in range(7)]  # y = s x + t over GF(7)
    for _ in range(200):
        import random

        w = [random.randrange(7) for _ in pts]
        worst = max(worst, sum(1 for s, t in lines if sum((s * x + t) % 7 == w[x] for x in pts) >= a))
    assert worst <= counting_list(n, a, d), (worst, counting_list(n, a, d))
    del itertools
    print("selftest passed")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        selftest()
    else:
        headline()
        table_points_budget()
        table_no_new_theorem()
        table_listbound_level0()
        table_all_levels()
        table_counting()
        table_grinds_and_work()
        table_budget()
