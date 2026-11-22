#!/usr/bin/env python3
"""Note 71: level 0 of a DEEP-fold opening when its code is a random tree code with a scalar fold.

Standard library only; reuses note 67's model (`67_model.py`) and note 08's cost model, edits neither.

Assumed theorem (not proved here): every word has at most L codewords at agreement tau n, tau = (1 + L rho)/(L+1)
+ eps. The interleaved list over E is then at most L (the paper's projection bound, for L < 2^63).

Error rows of the level (section 4 of the note; q = 2^128, scalar fold challenge alpha in E):
  fold     (K0 - 1)/q + psi <= 2^-(125 - g_fold), K0 = 2^(g_fold+2), psi = 2^-(126 - g_fold), a class holding at most
           M = 2^(g_fold+1) candidates, which costs g = ceil(n / M) - 1 columns of agreement a round
  points   C(L,2) e^s1 + (L^3 q^3 / Theta) sum_j psi^-(j-1) e^sbar_j <= 2^-(125 - g_point), Theta = K0 (K0-1)(K0-M),
           e = point_degree / q the chance that a nonzero tuple vanishes at one point
  queries  ((A_end - 1)/n)^t + (sbar + t)/q <= 2^-(125 - g_query), A_end = ceil(tau n) + ell g
"""

from __future__ import annotations

import importlib.util
import math
import os
import sys
from fractions import Fraction
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))


def _load(name, file):
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, file))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


m67 = _load("m67", "67_model.py")
c8 = m67.c8
Q, TARGET = 1 << 128, 125

# Guest cycle estimates (section 2.5 of the note). All are instruction counts read off the guest's source, not
# measurements: a split of one cell into two K limbs is 3 cycles, a product into the running weight 2.
TODAY_PER_LAYER = 4.3  # today's residual chain: two XOR and two MUL a coordinate plus shared reads
HASHED_PER_LAYER = 6.0  # design D2, without the KECCAK step itself: key, operands, splits, product, dispatch
TABLE_PER_LAYER = 5.3  # a layer whose twiddle is read from the per-opening table: today's product plus one DEREF
FOLD_SAVED_PER_ROUND = 2.0  # t = alpha instead of alpha + beta x
HIGH_SAVED = 14.0  # no high part: its evaluation and its chain
TABLE_CYCLES_PER_WORD = 1.5  # one split per two table twiddles
MAX_TABLE_BITS = 12


def m0_ok(big_l, e, sbar, g_point, g_fold):
    k0 = 1 << (g_fold + 2)
    theta = k0 * (k0 - 1) * (k0 - (1 << (g_fold + 1)))
    big_t, top = 126 - g_fold, sbar[-1]
    lhs = comb(big_l, 2) * theta * e ** sbar[0] * Q ** (top - sbar[0])
    lhs += big_l**3 * Q**3 * sum((1 << (big_t * j)) * e ** sbar[j] * Q ** (top - sbar[j]) for j in range(len(sbar)))
    return lhs << (TARGET - g_point) <= theta * Q**top


def one_batch(big_l, e, ell, g_point, g_fold):
    s = 1
    while not m0_ok(big_l, e, (s,) * ell, g_point, g_fold):
        s += 1
    return s


def ladder(big_l, e, ell, g_point, g_fold):
    """Round j holds the least count its prefix of the row allows; then the whole row is repaired if needed."""
    total, sbar = one_batch(big_l, e, ell, g_point, g_fold), []
    for j in range(ell):
        s = sbar[-1] if sbar else 1
        while not m0_ok(big_l, e, tuple(sbar) + (s,), g_point, g_fold):
            s += 1
        sbar.append(min(s, total))
    while not m0_ok(big_l, e, tuple(sbar), g_point, g_fold):
        sbar = [min(x + 1, total) for x in sbar]
    return tuple(sbar)


def twiddle_plan(depth, kappa, queries):
    """(hashed layers h, table bits, cycle-equivalents a query beyond today's residual chain). h is a multiple of 4;
    the top depth - h bits index a table of twiddles built once per opening."""
    best = None
    for h in range(0, kappa + 1, 4):
        bits = depth - h
        if bits > MAX_TABLE_BITS:
            continue
        table_perms = (1 << bits) / 15
        table = 8 * table_perms + TABLE_CYCLES_PER_WORD * (1 << bits)
        per_query = 8 * h / 4 + (HASHED_PER_LAYER - TODAY_PER_LAYER) * h + (TABLE_PER_LAYER - TODAY_PER_LAYER) * (kappa - h) + 2
        total = per_query + table / queries
        if best is None or total < best[0]:
            best = (total, h, bits, table_perms)
    return best
