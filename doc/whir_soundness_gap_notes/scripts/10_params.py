#!/usr/bin/env python3
"""Researcher 10: independent parameter count for the DEEP fold (note 07, Theorem 3), from the re-derived bound.

Bound used (note 10, Theorem A): for one fold round with s fresh points, the points are exceptional with probability at most
    e_pt = Lambda^3 q^6 eps^s / (K0 (K0 - 1) (K0 - M)),   M = max(2q, C(n, 2)) = 2q at our sizes,
and outside that set every answer vector and round message wins fewer than K0 challenges.
Variant P (points fixed for the level, ell rounds): nested Markov with a per-round fraction tau,
    Pr[points bad for the level] <= e_pt (1 + 1/tau + ... + tau^-(ell-1)),   fold round error <= K0 / q^2 + tau.
eps = (d + 1 + log2 lanes) / q with d = 2^kappa - 1 + ell; the first round of a level has the most lanes (2^(ell-1)).

Budgets: 125 bits less the grind of the message: fold 7 bits, point message 15 bits (today's OOD grind), or no grind.
Pure python, instant.
"""
import math

LOGQ = 128
KAPPA = [24, 20, 16, 12, 8, 4]
FOLDS = [6, 4, 4, 4, 4, 4]


def log2_eps(kappa, ell):
    return math.log2((1 << kappa) + ell + (ell - 1)) - LOGQ  # d + 1 + log2(2^(ell-1))


def best_split(ell, fold_budget_log2):
    """Split the fold budget B between K0 / q^2 = (1 - x) B and tau = x B to minimise the exponent the points must pay:
    cost(x) = -log2(k^2 (k - 2)) + (ell - 1) log2(1 / tau), k = K0 / q."""
    best = None
    for i in range(1, 2000):
        x = i / 2000
        k = (1 - x) * 2.0 ** (LOGQ + fold_budget_log2)
        if k <= 2.0:
            continue
        tau_log2 = math.log2(x) + fold_budget_log2
        cost = -math.log2(k * k * (k - 2)) + (ell - 1) * (-tau_log2)
        if best is None or cost < best[0]:
            best = (cost, x, k, tau_log2)
    return best


def points_needed(b, kappa, ell, g_fold, g_point, nested=True):
    fold_budget = -(125 - g_fold)
    point_budget = -(125 - g_point) - 1  # half of the message's budget; the rest for separation and r = 0
    if nested:
        cost, x, k, tau_log2 = best_split(ell, fold_budget)
    else:
        cost, x, k, tau_log2 = best_split(1, fold_budget)
    need = 3 * b + 3 * LOGQ + cost - point_budget
    le = -log2_eps(kappa, ell)
    s = math.ceil(need / le - 1e-9)
    # separation of the level's list at s points: C(Lambda, 2) eps^s must also fit
    while 2 * b - 1 - s * le > point_budget:
        s += 1
    return s, k, tau_log2, need, le


def table(g_fold, g_point, nested, title):
    print(f"\n== {title} (fold grind {g_fold} bits, point grind {g_point} bits)")
    print("log2(Lambda)  points per level (levels 0..5)   scalars   bytes   K0/q at level 0   log2(tau)   bits needed at level 0 / bits per point")
    for b in (0, 8, 10, 40, 70, 100, 130):
        ss, scal = [], 0
        for kappa, ell in zip(KAPPA, FOLDS):
            s, k, tau_log2, need, le = points_needed(b, kappa, ell, g_fold, g_point, nested)
            ss.append(s)
            scal += s * (ell + 1) if nested else s * 2 * ell
        s0, k0, t0, need0, le0 = points_needed(b, KAPPA[0], FOLDS[0], g_fold, g_point, nested)
        print(f"{b:<13} {str(ss):<32} {scal:<9} {scal * 16:<7} {k0:<18.1f} {t0:<11.2f} {need0:.0f} / {le0:.1f}")


def fold_error():
    print("\n== Fold round error against the 2^-118 budget (7-bit grind) and 2^-125 (no grind)")
    for g in (7, 0):
        cost, x, k, tau_log2 = best_split(6, -(125 - g))
        tot = math.log2(k * 2.0 ** (-LOGQ) + 2.0**tau_log2)
        print(f"grind {g}: K0 = {k:.1f} q, K0/q^2 = 2^{math.log2(k) - LOGQ:.2f}, tau = 2^{tau_log2:.2f}, total 2^{tot:.2f} (budget 2^-{125 - g})")
    print("no grind, minimal K0: K0 = 2.72 q gives K0/q^2 = 2^%.2f; with tau = 2^-126 the total is 2^%.2f" % (
        math.log2(2.72) - LOGQ, math.log2(2.72 * 2.0**-LOGQ + 2.0**-126)))


def constants():
    print("== Constants of one round: Pr[exceptional] <= c Lambda^3 q^3 eps^s")
    print("K0/q      note 07 (4 / k^3)   re-derived (1 / (k^2 (k - 2)))")
    for k in (2.72, 3, 4, 8, 256, 512):
        print(f"{k:<9} {4 / k**3:<19.3g} {1 / (k * k * (k - 2)):.3g}")


def hypothetical():
    print("\n== For scale only (NOT proved): points needed at level 0 if the exceptional probability were (n/q)^s + C(Lambda,2) eps^s,")
    print("   the two largest events found by brute force (all points in D; two list members sharing all s answers)")
    le = -log2_eps(24, 6)
    for b in (40, 70, 100):
        s = 1
        while max(2 * b - 1 - s * le, -100 * s) > -111:
            s += 1
        print(f"log2(Lambda) = {b}: s = {s}")


if __name__ == "__main__":
    constants()
    table(7, 15, True, "Variant P: points fixed per level, carried unbatched (nested Markov)")
    table(0, 0, True, "Variant P with no grinding on the fold and point messages")
    table(7, 15, False, "Fresh points every round (no nesting loss; 2 s scalars per round, old claims must be batched away)")
    fold_error()
    hypothetical()
