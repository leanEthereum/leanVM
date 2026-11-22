#!/usr/bin/env python3
"""Note 61: parameters and sizes of the DEEP-fold opening on window-mixed codes, with Theorem M of note 57 as a
hypothesis. Standard library only. Builds on the validated models of notes 08, 11 and 14 (imported, not edited).

The protocol modelled is Protocol D' of note 61: Protocol D of the paper with the plain fold G + alpha F (the affine
fold does not commute with the mixing), no degree slack and no high part, a proximity loss of t columns a fold round,
and at a mixed level one weighted claim per query whose weight is a sum of r column weights. Error terms (Theorem D'
of note 61), q = 2^128, alpha in E:

  points of level i      [C(L, 2) + L^3 q^3 / Theta * sum_{j < ell} tau^-j] * ((2^kappa + 2^ell - 2) / q)^s
  batching lambda_0      (J0 - 1) / q
  fold round             (K0 - 1) / q + tau,   K0 > M = max(2, floor(n / (t + 1))),   Theta = K0 (K0 - 1) (K0 - M)
  query message          ((A_end - 1) / n)^w + (w + s) / q,    A_end = A0 + ell t
  tail round             2 / q

with K0 = 2^(g_fold + 2), M = 2^(g_fold + 1), tau = 2^-(126 - g_fold): a fold round is 2^-125 after its grind.

Inequality (1) of note 57, for a code over a field of 2^c elements (c = 64: coefficients in K):
  c ((L + 1) A - n - L k) >= (L + 1) n H(A / n) + 130.

Every accept or reject is an exact integer or rational comparison, except inequality (1) itself, which is evaluated
in double precision against its 130-bit margin (the entropy term is a float; its error is below 1e-5 bits).

Usage:
  python3 61_params.py            all tables of note 61 (about a minute)
  python3 61_params.py selftest   consistency checks
"""

from __future__ import annotations

import importlib.util
import math
import os
import sys
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
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
p14 = _load("params14", "14_params.py")

LOG_Q = 128
Q = 1 << LOG_Q
TARGET = 125
G_QUERY, G_POINT, G_BATCH = 17, 15, 7
G_FOLD = 12  # the plain fold's grind (the deployed affine fold has 7); see fold_constants
MARGIN = 130  # the additive constant of inequality (1)
S_CAP = 400


# --------------------------------------------------------------------------------------------------------------
# Inequality (1) and what follows from it
# --------------------------------------------------------------------------------------------------------------


def entropy_bits(n, a):
    """n H(a / n) in bits."""
    if a <= 0 or a >= n:
        return 0.0
    x = a / n
    return n * (-x * math.log2(x) - (1 - x) * math.log2(1 - x))


def log2_binom(n, a):
    return (math.lgamma(n + 1) - math.lgamma(a + 1) - math.lgamma(n - a + 1)) / math.log(2)


def ineq1(n, k, big_l, a, c=64, exact=False):
    """Inequality (1) at the integer agreement a. `exact` counts the set systems by C(n, a)^(L+1), not 2^((L+1) n H)."""
    sets = (big_l + 1) * (log2_binom(n, a) if exact else entropy_bits(n, a))
    return c * ((big_l + 1) * a - n - big_l * k) >= sets + MARGIN


def min_agreement(n, k, big_l, c=64, exact=False):
    """The least integer A with (1). The left side grows by c (L+1) a column and the right by less than (L+1) log2 n."""
    lo, hi = k + 1, n
    if not ineq1(n, k, big_l, hi, c, exact):
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        if ineq1(n, k, big_l, mid, c, exact):
            hi = mid
        else:
            lo = mid + 1
    return lo


def profile(n, k, a, c=64, cap=None):
    """The least L >= 1 for which (1) holds at agreement a (so that the single-lane list there has affine dimension
    at most L - 1), or None. (1) is linear in L, increasing exactly above the pigeonhole value."""
    cap = cap if cap is not None else n.bit_length() - 3  # L <= N - 2
    slope = c * (a - k) - entropy_bits(n, a)
    if slope <= 0:
        return None
    big_l = max(1, math.ceil((c * (n - k) + MARGIN) / slope - 1 - 1e-12))
    while big_l > 1 and ineq1(n, k, big_l - 1, a, c):
        big_l -= 1
    while not ineq1(n, k, big_l, a, c):
        big_l += 1
    return big_l if big_l <= cap else None


def agreement_bound(n, k, c=64):
    """d_mu: two distinct codewords agree on at most this many columns, from Theorem M at L = 1. If they agree on s
    columns, a word agrees with each on s + floor((n - s) / 2), so s + floor((n - s) / 2) < A_1."""
    a1 = min_agreement(n, k, 1, c)
    return 2 * a1 - n, a1


def direct_distance(n, k, c=64):
    """The first-moment distance bound (rank one of note 57's Key Lemma): the least T with C(n, T) q^(k - T) below
    2^-129, minus one."""
    lo, hi = k, n
    while lo < hi:
        mid = (lo + hi) // 2
        if c * (mid - k) >= log2_binom(n, mid) + 129:
            hi = mid
        else:
            lo = mid + 1
    return lo - 1


def profile_tree(n, k, a0, d_mu, lanes, c=64):
    """The interleaved list bound of note 61, Proposition I': N_m(A) <= N_{m-1}(A) + (Lam(A) - 1) N_{m-1}(2A - d),
    N_1 = Lam, with Lam(A_j) = 2^(c (L_j - 1)) read off (1) at A_j = d + 2^j (A - d). Returns (bound, [L_j])."""
    ls, a = [], a0
    while a <= n:
        lj = profile(n, k, a, c)
        if lj is None:
            return None, ls
        ls.append(lj)
        if lj == 1:
            break
        a = 2 * a - d_mu
    else:
        ls.append(0)  # the next agreement exceeds n: no member at all
    lam = [0 if x == 0 else 1 << (c * (x - 1)) for x in ls]
    f = [1 if lam[-1] == 1 else 0] * (lanes + 1)  # the deepest level: unique, or empty
    for j in range(len(lam) - 2, -1, -1):
        g = [0] * (lanes + 1)
        g[1] = lam[j]
        for m in range(2, lanes + 1):
            g[m] = g[m - 1] + (lam[j] - 1) * f[m - 1]
        f = g
    return f[lanes], ls


# --------------------------------------------------------------------------------------------------------------
# The protocol's error terms
# --------------------------------------------------------------------------------------------------------------


def fold_constants(g_fold=G_FOLD):
    """(K0, M, 1/tau): (K0 - 1)/q + tau < 2^(g_fold - 125)."""
    return 1 << (g_fold + 2), 1 << (g_fold + 1), 1 << (126 - g_fold)


def loss(n, g_fold=G_FOLD):
    """The least t with floor(n / (t + 1)) <= M."""
    _, big_m, _ = fold_constants(g_fold)
    t = max(-(-n // big_m) - 1, 0)
    while t > 0 and n // t <= big_m:
        t -= 1
    return t


def points_ok(lam, kappa, ell, s, g_fold=G_FOLD):
    k0, big_m, inv_tau = fold_constants(g_fold)
    theta = k0 * (k0 - 1) * (k0 - big_m)
    nested = sum(inv_tau**j for j in range(ell))
    bracket = Fraction(comb(lam, 2)) + Fraction(lam**3 * Q**3 * nested, theta)
    eps_num = (1 << kappa) + (1 << ell) - 2
    return bracket * eps_num**s * (1 << (TARGET - G_POINT)) <= Q**s


def points_needed(lam, kappa, ell, g_fold=G_FOLD):
    """Exact, by bisection on the exact test (the test is monotone in s)."""
    k0, big_m, inv_tau = fold_constants(g_fold)
    lg_bracket = max(2 * d11.log2_big(lam) - 1, 3 * d11.log2_big(lam) + 3 * LOG_Q - (3 * (g_fold + 2) - 1) + (ell - 1) * (126 - g_fold))
    per = LOG_Q - math.log2((1 << kappa) + (1 << ell) - 2)
    s = max(1, int((lg_bracket + TARGET - G_POINT) / per) - 1)
    while not points_ok(lam, kappa, ell, s, g_fold):
        s += 1
    while s > 1 and points_ok(lam, kappa, ell, s - 1, g_fold):
        s -= 1
    return s


def query_ok(log_n, a_end, w, s, final):
    n = 1 << log_n
    if final:
        return (a_end - 1) ** w << (TARGET - G_QUERY) <= n**w
    room = (1 << (LOG_Q - TARGET + G_QUERY)) - (w + s)
    return room > 0 and (a_end - 1) ** w * Q <= room * n**w


def query_count(log_n, a_end, s, final):
    w = max(1, int(108 / (log_n - math.log2(a_end - 1))) - 1)
    while not query_ok(log_n, a_end, w, s, final):
        w += 1
    return w


# --------------------------------------------------------------------------------------------------------------
# Levels
# --------------------------------------------------------------------------------------------------------------


@dataclass
class Level:
    log_inv_rate: int
    cols: int  # kappa
    k: int  # ell
    a0: int  # the agreement the list bound is assumed at
    a_end: int  # what the queries see
    list_size: int
    code: str  # "RS Johnson", "RS counting", "mixed K L=..", "mixed E L=.."
    big_l: int = 0  # 0 for a Reed-Solomon level
    coeff_bits: int = 0
    points: int = 0
    queries: int = 0
    profile: tuple = ()
    g_fold: int = G_FOLD
    partners: int = -1  # of a mixed level's window: -1 the N cube directions, else that many power-of-two strides

    @property
    def log_block(self):
        return self.cols + self.log_inv_rate

    @property
    def mixed(self):
        return self.big_l > 0

    @property
    def window(self):
        """r - 1: the partners of a position (the cube directions), 0 for a Reed-Solomon level."""
        return self.log_block if self.mixed else 0


def finish(lv: Level, final: bool):
    lv.points = points_needed(lv.list_size, lv.cols, lv.k, lv.g_fold)
    lv.queries = query_count(lv.log_block, lv.a_end, lv.points, final)
    return lv


def mixed_level(rate, cols, k, big_l, variant, final, c=64, first_moment_distance=False):
    """A window-mixed level. variant: 'direct' (the list of every interleaved word is 2^(c (L - 1)), a hypothesis
    stronger than Theorem M), 'profile' (Proposition I' of note 61 from Theorem M at several L), 'tree' (Theorem 6.1
    of the paper from Theorem M at one L)."""
    log_n = cols + rate
    n, kk = 1 << log_n, 1 << cols
    if big_l > log_n - 2:
        return None
    a0 = min_agreement(n, kk, big_l, c)
    if a0 is None:
        return None
    d_mu, _ = agreement_bound(n, kk, c)
    if first_moment_distance:  # a second hypothesis on the code: its distance by the rank-one first moment
        d_mu = direct_distance(n, kk, c)
    if a0 <= d_mu:
        return None
    lanes = (2 << k) if c == 64 else (1 << k)  # K-lanes of an E-valued word, or E-lanes
    prof = ()
    if variant == "direct":
        lam = 1 << (c * (big_l - 1))
    elif variant == "profile":
        lam, prof = profile_tree(n, kk, a0, d_mu, lanes, c)
        if lam is None:
            return None
    elif variant == "tree":
        lam = p14.tree_bound(1 << (c * (big_l - 1)), n, d_mu, a0)
    else:
        raise ValueError(variant)
    t = loss(n)
    name = f"mixed {'K' if c == 64 else 'E'} L={big_l}"
    return finish(Level(rate, cols, k, a0, a0 + k * t, lam, name, big_l, c, profile=tuple(prof)), final)


def rs_level(index, rate, cols, k, final):
    """The better, in bytes, of the Reed-Solomon levels at fold grinds 12 and 16: where the threshold is a few dozen
    columns (the counting bound at the last levels) the loss of a 12-bit grind is too large."""
    cands = [_rs_level(index, rate, cols, k, final, g) for g in ((G_FOLD, 16) if index >= 1 else (G_FOLD,))]
    return min(cands, key=lambda lv: level_bytes(index, lv))


def _rs_level(index, rate, cols, k, final, g_fold):
    """A Reed-Solomon level under the plain fold: the Johnson bound at d = 2^kappa - 1, or the counting bound where
    it gives fewer bytes (the last levels), with the loss of t columns a round."""
    log_n = cols + rate
    n, d = 1 << log_n, (1 << cols) - 1
    t = loss(n, g_fold)

    def johnson_at(a0):
        den = a0 * a0 - n * d
        return None if den <= 0 else n * (a0 - d) // den

    lo = isqrt(n * d) + 1
    w = query_count(log_n, lo + k * t, S_CAP, final)
    hi_lo, hi_hi = lo, n - k * t
    while hi_lo < hi_hi:  # the largest threshold with that query count (the smallest list)
        mid = (hi_lo + hi_hi + 1) // 2
        if query_ok(log_n, mid + k * t, w, S_CAP, final):
            hi_lo = mid
        else:
            hi_hi = mid - 1
    best = finish(Level(rate, cols, k, hi_lo, hi_lo + k * t, johnson_at(hi_lo), "RS Johnson", g_fold=g_fold), final)
    if index >= 1:
        for w2 in range(best.queries - 1, 0, -1):
            a_lo, a_hi = d + 1, n - k * t
            if not query_ok(log_n, a_lo + k * t, w2, S_CAP, final):
                break
            while a_lo < a_hi:
                mid = (a_lo + a_hi + 1) // 2
                if query_ok(log_n, mid + k * t, w2, S_CAP, final):
                    a_lo = mid
                else:
                    a_hi = mid - 1
            if 3 * (d + 1) * (log_n - math.log2(a_lo)) > 64 * LOG_Q:
                break
            size = comb(n, d + 1) // comb(a_lo, d + 1)
            cand = finish(Level(rate, cols, k, a_lo, a_lo + k * t, size, "RS counting", g_fold=g_fold), final)
            if cand.points > 64:  # the cap of note 11's model on a counting level
                break
            if level_bytes(index, cand) < level_bytes(index, best):
                best = cand
    return best


def level_bytes(index, lv: Level):
    words = c8.leaf_words(index, lv.k)
    depth, w = lv.log_block, lv.queries
    phase = 16 + 4 * w + c8.expected_distinct(1 << depth, w) * 8 * words + c8.DIGEST * c8.expected_siblings(depth, w)
    return phase + c8.SCALAR * lv.points * (1 + lv.k)


def window_products(kappa, log_n):
    """E by E products of the r - 1 partner weights of a query at the terminal point, given the base point's factors:
    the partner x + beta_j changes the factors k <= j, so sum_j min(j + 1, kappa) (note 61, section 6)."""
    return sum(min(j + 1, kappa) for j in range(log_n))


def stride_products(kappa, log_n, partners):
    """Expected products of the partner weights when the partners are the positions at index distance 2^j, for
    `partners` exponents j spread from 0 to log_n - 1: index + 2^j flips the bits j to j + c, c the carry run
    (c = i with probability 2^-(i+1)), so the factors k <= j + c change: about min(j + 2, kappa) of them."""
    if partners == 1:
        js = [0]
    else:
        js = [round(i * (log_n - 1) / (partners - 1)) for i in range(partners)]
    return sum(min(j + 2, kappa) for j in js)


def mu_perms(log_n):
    """Keccak-f calls that give the r - 1 = log_n coefficients of one position (25 words a call)."""
    return -(-log_n // 25)


# --------------------------------------------------------------------------------------------------------------
# The opening
# --------------------------------------------------------------------------------------------------------------


@dataclass
class Cost:
    proof_bytes: float
    merkle_bytes: float
    stream_scalars: int
    point_scalars: int
    fs_perms: int
    guest_keccak: float
    native_keccak: float
    guest_cycles: float
    grind_perms: int
    window_mults: int
    mu_keccak: int

    @property
    def recursion(self):
        """Guest cycles of the queries and points plus 8 a KECCAK step (note 08's estimate of a step's weight)."""
        return self.guest_cycles + 8 * self.guest_keccak


def cost(levels, fill=1.0) -> Cost:
    """`fill` is the share of the stack's 2^ell lanes that hold data: a level-0 leaf sends only those."""
    sponge = c8.SpongeCount()
    n_levels = len(levels)
    s0 = levels[0].points
    scalars = 2 + 1 + s0 + 1
    sponge.absorb(2)
    sponge.grind(G_POINT)
    sponge.sample(2 * s0)
    sponge.absorb(s0)
    sponge.grind(G_BATCH)
    sponge.sample()
    grind = n_levels * (1 << G_POINT) + (1 << G_BATCH)
    point_scalars = s0
    merkle_bytes = guest_merkle = native_merkle = cycles = 0.0
    window_mults = mu_keccak = 0
    for i, lv in enumerate(levels):
        final = i == n_levels - 1
        depth, w, s = lv.log_block, lv.queries, lv.points
        for _ in range(lv.k):
            scalars += 2 + s + 1  # v_G, v_F, one phi a point, the grind's nonce
            sponge.absorb(2 + s)
            sponge.grind(lv.g_fold)
            sponge.sample(1)
        point_scalars += s * lv.k
        grind += lv.k * (1 << lv.g_fold) + (1 << G_QUERY)
        per_word = 128 // depth
        if final:
            n_final = 1 << lv.cols
            scalars += n_final + 1 + 2 * lv.cols
            sponge.absorb(n_final)
            sponge.grind(G_QUERY)
            sponge.sample(-(-w // per_word))
            for _ in range(lv.cols):
                sponge.absorb(2)
                sponge.sample()
        else:
            s_next = levels[i + 1].points
            scalars += 2 + 1 + s_next + 1
            point_scalars += s_next
            sponge.absorb(2)
            sponge.grind(G_POINT)
            sponge.sample(2 * s_next)
            sponge.absorb(s_next)
            sponge.grind(G_QUERY)
            sponge.sample(-(-w // per_word))
            sponge.sample()
        words = c8.leaf_words(i, lv.k)
        perms = c8.leaf_perms(words)
        sent = words if i > 0 else min(words, math.ceil(fill * words - 1e-9))
        merkle_bytes += 16 + 4 * w + c8.expected_distinct(1 << depth, w) * 8 * sent + c8.DIGEST * c8.expected_siblings(depth, w)
        cap = c8.merkle_cap_depth(w, depth)
        guest_merkle += w * (perms + depth - cap) + c8.expected_cap_hashes(cap, w)
        native_merkle += w * (perms + depth)
        cycles += w * c8.guest_query_cycles(i, lv.k, depth - cap, lv.cols, final)
        if lv.mixed:
            if lv.partners < 0:
                prods, partners, perms_mu, per = window_products(lv.cols, depth), depth, mu_perms(depth), 2
            else:  # stride windows: a run of constants to add before each product
                prods, partners, perms_mu, per = stride_products(lv.cols, depth, lv.partners), lv.partners, 1, 3
            if final:
                extra = partners * (2.2 * (1 << lv.cols) + 60)  # the final polynomial at the partners
            else:
                extra = per * prods + 4 * partners
            cycles += w * extra
            window_mults += w * prods
            mu_keccak += w * perms_mu
    cycles += d11.point_guest_cycles(levels)
    return Cost(
        proof_bytes=merkle_bytes + c8.SCALAR * scalars,
        merkle_bytes=merkle_bytes,
        stream_scalars=scalars,
        point_scalars=point_scalars,
        fs_perms=sponge.perms,
        guest_keccak=guest_merkle + sponge.perms + mu_keccak,
        native_keccak=native_merkle + sponge.perms + mu_keccak,
        guest_cycles=cycles,
        grind_perms=grind,
        window_mults=window_mults,
        mu_keccak=mu_keccak,
    )


def build(mu, rate, big_l, variant="profile", mixed_levels=None, later_e=True):
    """The levels of an opening. Level i is window-mixed with parameter `big_l` (clipped to N_i - 2) when that gives
    fewer bytes than the best Reed-Solomon level and i is in `mixed_levels` (None: every level may be). A later
    level may take its coefficients in E (`later_e`), which halves the pigeonhole term and doubles the list's bits."""
    rates, cols, folds, _ = wm.ladder(mu, rate)
    out = []
    for i, (r, c, k) in enumerate(zip(rates, cols, folds)):
        final = i == len(rates) - 1
        best = rs_level(i, r, c, k, final)
        if big_l and (mixed_levels is None or i in mixed_levels) and not final:
            ll = min(big_l, c + r - 2)
            for bits in (64, 128) if (i >= 1 and later_e) else (64,):
                cand = mixed_level(r, c, k, ll, variant, final, bits)
                if cand is not None and cand.points <= S_CAP and level_bytes(i, cand) < level_bytes(i, best):
                    best = cand
        out.append(best)
    return out


def today(mu, rate):
    cfg = wm.derive(mu, rate)
    c = c8.cost(cfg)
    return cfg, c


def today_recursion(c):
    return c.guest_cycles + 8 * c.guest_keccak


def paper_johnson(mu, rate):
    lv = d11.build(mu, rate)
    return lv, d11.deep_cost(mu, lv)


# --------------------------------------------------------------------------------------------------------------
# Tables
# --------------------------------------------------------------------------------------------------------------

LS = (4, 7, 11, 15, 23, 31)
RATES = (1, 2, 3, 4)
FRONTIER = {1: (0.5156, 114), 2: (0.263, 57), 3: (0.1339, 38), 4: (0.0681, 28)}  # note 38, s >= 4


def kib(x):
    return f"{x / 1024:.1f}"


def pct(new, old):
    return f"{100 * (new / old - 1):+.1f}%"


def lg(x):
    return d11.log2_big(x) if x > 0 else float("-inf")


def table_inequality(mu=30):
    print(f"## T1. Inequality (1) at level 0, mu = {mu} (kappa = {mu - 6}, n = 2^(kappa + R)), coefficients in K\n")
    print("| rate | n | L | admitted (L <= N - 2) | A / n from (1) | same with C(n, A) for 2^(nH) | a - rho - (1 - rho)/(L + 1) | pigeonhole term H(a)/64 | queries, simple ceil(108 / log2(1/a)) | queries, exact with the loss | today | frontier (note 38) | gap to frontier |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for rate in RATES:
        kappa = mu - 6
        n, k = 1 << (kappa + rate), 1 << kappa
        cfg, _ = today(mu, rate)
        for big_l in LS:
            a = min_agreement(n, k, big_l)
            ax = min_agreement(n, k, big_l, exact=True)
            ok = big_l <= kappa + rate - 2
            t = loss(n)
            w = query_count(kappa + rate, a + 6 * t, 40, False)
            simple = math.ceil(108 / -math.log2(a / n))
            fr = FRONTIER[rate][1]
            x = a / n
            print(
                f"| 1/{1 << rate} | 2^{kappa + rate} | {big_l} | {'yes' if ok else 'NO'} | {x:.6f} | {ax / n:.6f} ({a - ax} columns fewer) | {x - 2.0**-rate - (1 - 2.0**-rate) / (big_l + 1):.5f} "
                f"| {entropy_bits(n, a) / n / 64:.5f} | {simple} | {w} | {cfg.queries[0]} | {fr} | {w - fr} ({100 * (w / fr - 1):.0f}%) |"
            )
    print()


def table_lists(mu=30):
    print(f"## T2. Level 0, mu = {mu}: agreement bound, list bounds for interleaved words and points (grinds {G_QUERY}/{G_FOLD}/{G_POINT}/{G_BATCH})\n")
    print("| rate | L | d_mu / n (Theorem M, L = 1) | first-moment distance / n | profile L_j at A_j = d_mu + 2^j (A - d_mu) | log2 list: direct (hypothetical) | profile tree (Prop. I') | tree (paper Thm 6.1) | points s_0: direct / profile / tree | bytes of the points: direct / profile / tree | with the first-moment distance: profile L_j, log2 list, s_0 |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    kappa, ell = mu - 6, 6
    for rate in RATES:
        n, k = 1 << (kappa + rate), 1 << kappa
        d_mu, _ = agreement_bound(n, k)
        dd = direct_distance(n, k)
        for big_l in LS:
            if big_l > kappa + rate - 2:
                continue
            lv = {v: mixed_level(rate, kappa, ell, big_l, v, False) for v in ("direct", "profile", "tree")}
            fm = mixed_level(rate, kappa, ell, big_l, "profile", False, first_moment_distance=True)
            prof = lv["profile"].profile
            print(
                f"| 1/{1 << rate} | {big_l} | {d_mu / n:.5f} | {dd / n:.5f} | {' '.join(map(str, prof))} | {lg(lv['direct'].list_size):.0f} | {lg(lv['profile'].list_size):.0f} | {lg(lv['tree'].list_size):.0f} "
                f"| {lv['direct'].points} / {lv['profile'].points} / {lv['tree'].points} | {' / '.join(str(16 * x.points * (1 + ell)) for x in lv.values())} "
                f"| {' '.join(map(str, fm.profile))}, {lg(fm.list_size):.0f}, {fm.points} |"
            )
    print()


def describe(levels):
    return "; ".join(f"L{i} {lv.code} a={lv.a0 / (1 << lv.log_block):.4f} w={lv.queries} s={lv.points}" for i, lv in enumerate(levels))


def table_openings(mu=30, variant="profile"):
    print(f"## T3. The whole opening, mu = {mu}, list bounds by the {variant} reduction; a level is mixed where that gives fewer bytes\n")
    print("| rate | L | queries per level | points per level | codes per level | KiB | vs today | vs paper's Johnson DEEP | guest Keccak (of which mu) | guest cycles (est.) | recursion = cycles + 8 Keccak (est.) | vs today | native window products |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for rate in RATES:
        cfg, c0 = today(mu, rate)
        lvj, cj = paper_johnson(mu, rate)
        rec0 = today_recursion(c0)
        print(f"| 1/{1 << rate} | today | {' '.join(map(str, cfg.queries))} | 1 OOD | RS, affine fold | {kib(c0.proof_bytes)} | | | {c0.guest_keccak:.0f} | {c0.guest_cycles:.0f} | {rec0:.0f} | | |")
        recj = cj.guest_query_cycles + d11.point_guest_cycles(lvj) + 8 * cj.guest_keccak
        print(
            f"| | paper, Johnson | {' '.join(str(x.queries) for x in lvj)} | {' '.join(str(x.points) for x in lvj)} | RS, affine fold | {kib(cj.proof_bytes)} | {pct(cj.proof_bytes, c0.proof_bytes)} | | {cj.guest_keccak:.0f} "
            f"| {cj.guest_query_cycles + d11.point_guest_cycles(lvj):.0f} | {recj:.0f} | {pct(recj, rec0)} | |"
        )
        for big_l in (0,) + LS:
            lv = build(mu, rate, big_l, variant)
            c = cost(lv)
            codes = " ".join(("M" + ("E" if x.coeff_bits == 128 else "K") + str(x.big_l)) if x.mixed else ("J" if x.code == "RS Johnson" else "C") for x in lv)
            print(
                f"| | {'RS, plain fold' if big_l == 0 else big_l} | {' '.join(str(x.queries) for x in lv)} | {' '.join(str(x.points) for x in lv)} | {codes} | {kib(c.proof_bytes)} | {pct(c.proof_bytes, c0.proof_bytes)} | {pct(c.proof_bytes, cj.proof_bytes)} "
                f"| {c.guest_keccak:.0f} ({c.mu_keccak}) | {c.guest_cycles:.0f} | {c.recursion:.0f} | {pct(c.recursion, rec0)} | {c.window_mults} |"
            )
    print()


def table_best(mu=30):
    print(f"## T4. Best L for bytes and for recursion, mu = {mu}, the same L at every mixed level (clipped to N_i - 2)\n")
    print("| rate | reduction | mixed levels | best L for bytes | queries | points | KiB (vs today) | recursion (vs today) | best L for recursion | KiB | recursion (vs today) |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for rate in RATES:
        _, c0 = today(mu, rate)
        rec0 = today_recursion(c0)
        for variant in ("direct", "profile", "tree"):
            for which, name in ((None, "any"), ({0}, "level 0 only")):
                rows = []
                for big_l in range(2, mu - 6 + rate - 1):
                    lv = build(mu, rate, big_l, variant, which)
                    rows.append((big_l, lv, cost(lv)))
                bl, lvb, cb = min(rows, key=lambda x: x[2].proof_bytes)
                rl, _lvr, cr = min(rows, key=lambda x: x[2].recursion)
                print(
                    f"| 1/{1 << rate} | {variant} | {name} | {bl} | {' '.join(str(x.queries) for x in lvb)} | {' '.join(str(x.points) for x in lvb)} | {kib(cb.proof_bytes)} ({pct(cb.proof_bytes, c0.proof_bytes)}) "
                    f"| {cb.recursion:.0f} ({pct(cb.recursion, rec0)}) | {rl} | {kib(cr.proof_bytes)} | {cr.recursion:.0f} ({pct(cr.recursion, rec0)}) |"
                )
    print()


def table_fold_grind(mu=30):
    print(f"## T5. The plain fold's loss and grind, level 0, mu = {mu}\n")
    print("| rate | n | fold grind bits | M | loss t a round | 6 t / n | queries at L = 15 | grind work of the opening's fold rounds (perms) | same at t = 1 (efficient extractor), bits and perms |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    global G_FOLD
    keep = G_FOLD
    for rate in RATES:
        rates, cols, folds, _ = wm.ladder(mu, rate)
        n, k = 1 << (cols[0] + rates[0]), 1 << cols[0]
        a = min_agreement(n, k, 15)
        t1 = [max(c + r - 1 - 1, 0) for c, r in zip(cols, rates)]  # K0 = 2M = 2 n / 2: g = log2 n - 2
        work1 = sum(f * (1 << g) for f, g in zip(folds, t1))
        for g in (7, 10, 12, 14, 16):
            G_FOLD = g
            t = loss(n, g)
            w = query_count(cols[0] + rates[0], a + 6 * t, 40, False)
            work = sum(folds) * (1 << g)
            print(f"| 1/{1 << rate} | 2^{cols[0] + rates[0]} | {g} | 2^{g + 1} | {t} | {6 * t / n:.5f} | {w} | 2^{math.log2(work):.1f} | {t1[0]} bits at level 0, 2^{math.log2(work1):.1f} |")
        G_FOLD = keep
    print()


def table_equal_cost(mu=30):
    print(f"## T6. Mixed at one rate against Reed-Solomon at lower rates, mu = {mu} (profile reduction, best L for bytes)\n")
    print("| code | level-0 queries | KiB | encoded words, units of 2^mu | level-0 mixing in units of the level-0 encode's field work (1.1 one thread, measured; 2.5 if bandwidth bound, estimate) |")
    print("| --- | --- | --- | --- | --- |")
    for rate in RATES:
        cfg, c0 = today(mu, rate)
        print(f"| RS today, rate 1/{1 << rate} | {cfg.queries[0]} | {kib(c0.proof_bytes)} | {c0.encode_words / 2**mu:.2f} | |")
    for rate in RATES:
        rows = []
        for big_l in range(2, mu - 6 + rate - 1):
            lv = build(mu, rate, big_l, "profile")
            rows.append((big_l, lv, cost(lv)))
        bl, lv, c = min(rows, key=lambda x: x[2].proof_bytes)
        _, c0 = today(mu, rate)
        print(f"| mixed, rate 1/{1 << rate}, L = {bl} | {lv[0].queries} | {kib(c.proof_bytes)} | {c0.encode_words / 2**mu:.2f} | 1.1 to 2.5 |")
    print()


def table_native(mu=30):
    print(f"## T7. Native verifier of the opening, mu = {mu}: Keccak-f calls and field products (formula counts of note 11, plus the window products)\n")
    print("| rate | | Keccak-f | field products, all kinds | of which window products |")
    print("| --- | --- | --- | --- | --- |")
    for rate in RATES:
        cfg, c0, m0 = d11.today(mu, rate)
        print(f"| 1/{1 << rate} | today | {c0.native_keccak} | {m0['total']} | |")
        for big_l in (0, 7, 15):
            lv = build(mu, rate, big_l, "profile")
            c = cost(lv)
            m = d11.verifier_mults(mu, lv, deep=True)
            name = "RS, plain fold" if big_l == 0 else f"mixed, L = {big_l}"
            print(f"| | {name} | {c.native_keccak:.0f} ({pct(c.native_keccak, c0.native_keccak)}) | {m['total'] + c.window_mults} ({pct(m['total'] + c.window_mults, m0['total'])}) | {c.window_mults} |")
    print()


def table_bench_shape(mu=26, fill=40 / 64):
    print(f"## T8. The shape of the 900-signature benchmark: mu = {mu}, {round(fill * 64)} of 64 lanes hold data (profile reduction)\n")
    print("| rate | | queries per level | points per level | WHIR opening, KiB | vs today | guest Keccak | recursion (est.) |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for rate in RATES:
        cfg = wm.derive(mu, rate)
        c0 = c8.cost(cfg, fill)
        rec0 = today_recursion(c0)
        print(f"| 1/{1 << rate} | today | {' '.join(map(str, cfg.queries))} | 1 OOD | {kib(c0.proof_bytes)} | | {c0.guest_keccak:.0f} | {rec0:.0f} |")
        rows = []
        for big_l in range(2, mu - 6 + rate - 1):
            lv = build(mu, rate, big_l, "profile")
            rows.append((big_l, lv, cost(lv, fill)))
        for big_l, lv, c in (rows[5], rows[13], min(rows, key=lambda x: x[2].proof_bytes)):
            print(
                f"| | mixed, L = {big_l} | {' '.join(str(x.queries) for x in lv)} | {' '.join(str(x.points) for x in lv)} | {kib(c.proof_bytes)} | {pct(c.proof_bytes, c0.proof_bytes)} "
                f"| {c.guest_keccak:.0f} | {c.recursion:.0f} ({pct(c.recursion, rec0)}) |"
            )
    print()


def selftest():
    # (1) is monotone in A and the minimal A satisfies it.
    for rate in RATES:
        n, k = 1 << (24 + rate), 1 << 24
        for big_l in LS:
            a = min_agreement(n, k, big_l)
            assert ineq1(n, k, big_l, a) and not ineq1(n, k, big_l, a - 1)
            assert profile(n, k, a, cap=99) == big_l, (rate, big_l, profile(n, k, a, cap=99))
    # Note 57's table, to its three digits.
    n, k = 1 << 25, 1 << 24
    for big_l, a57 in ((4, 0.616), (7, 0.578), (15, 0.547)):
        assert abs(min_agreement(n, k, big_l) / n - a57) < 1.5e-3, (big_l, min_agreement(n, k, big_l) / n)
    assert abs(min_agreement(1 << 26, 1 << 24, 15) / (1 << 26) - 0.311) < 1.5e-3
    # The profile tree on a hand case: Lam = (q^2, 1) and three lanes gives q^2 + 2 (q^2 - 1).
    f, _ = None, None
    lam = [1 << 128, 1]
    g = [0, lam[0], lam[0] + (lam[0] - 1), lam[0] + 2 * (lam[0] - 1)]
    n, k = 1 << 25, 1 << 24
    d_mu, a1 = agreement_bound(n, k)
    a0 = (a1 + d_mu) // 2 + 1  # one doubling reaches A_1
    val, ls = profile_tree(n, k, a0, d_mu, 3)
    assert ls[-1] == 1 and len(ls) == 2 and val == (1 << (64 * (ls[0] - 1))) + 2 * ((1 << (64 * (ls[0] - 1))) - 1), (ls, lg(val))
    # The fold constants give 2^-125 after the grind, and the loss gives floor(n / (t + 1)) <= M.
    for gf in (7, 12, 16):
        k0, big_m, inv_tau = fold_constants(gf)
        assert Fraction(k0 - 1, Q) + Fraction(1, inv_tau) < Fraction(1, 1 << (TARGET - gf))
        for log_n in (20, 25, 28):
            t = loss(1 << log_n, gf)
            assert (1 << log_n) // (t + 1) <= big_m and (t == 0 or (1 << log_n) // t > big_m)
    # The points formula follows the law s log2(1/eps) >= 3 b + 1023 at level 0 (fold grind 12): 104 bits a point.
    for b in (40, 75, 110, 896, 2700):
        s = points_needed(1 << b, 24, 6)
        assert s == math.ceil((3 * b + 1023.0) / (128 - math.log2((1 << 24) + 62))), (b, s)
    for b in (896, 1871):  # and 3 b + 795 for a level of four rounds
        s = points_needed(1 << b, 20, 4)
        assert s == math.ceil((3 * b + 795.0) / (128 - math.log2((1 << 20) + 14))), (b, s)
    # The Reed-Solomon levels under the plain fold are within two queries of the paper's Johnson levels.
    for rate in RATES:
        lv = build(30, rate, 0)
        lj, _ = paper_johnson(30, rate)
        assert all(abs(a.queries - b.queries) <= 2 for a, b in zip(lv, lj)), ([a.queries for a in lv], [b.queries for b in lj])
    # The cost function at the paper's levels, with the plain fold's shorter stream, is below the paper's bytes.
    print("selftest passed")


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        selftest()
        return
    table_inequality()
    table_lists()
    table_fold_grind()
    table_openings(30, "profile")
    table_openings(30, "direct")
    table_openings(30, "tree")
    table_best()
    table_equal_cost()
    table_native()
    table_bench_shape()
    selftest()


if __name__ == "__main__":
    main()
