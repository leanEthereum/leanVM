#!/usr/bin/env python3
"""Researcher 16: point counts per level under the bounds of note 16. Standard library, instant.

Per level: kappa, ell, eps = (2^kappa - 1 + ell + 2^ell - 1) / q (note 14), point-message budget 2^-110 (15-bit grind),
fold budget 2^-118 with K0 = 2^9 q and tau = 2^-119 (note 14's deployed choice).

Bounds on the probability that the s points of a level are bad, as functions of the list bound L = 2^b:

  proved    note 14, theorem card: [C(L,2) + L^3 q^6 / (K0 (K0-1) (K0-2q)) * NEST] eps^s
  thmB(u)   note 16, Theorem B with unexplained mass |T_un| <= 2^u q:
            C(s,2)/q + C(L,2) eps^s + [s C(L,2) eps^(s-1) + 2^(3u) q^3 eps^s / (Ku (Ku-1) (Ku-q))] * NEST,
            Ku = K0 - s q - L (so that fewer than K0 challenges win; needs L < K0);  u = 128 + b is unconditional
  floor     note 16, Proposition 3.1: any theorem with the state function of note 14 has error at least
            s (r/q)^(s-1) (1 - r/q) when lists of K0/q members sharing a factor of degree r exist; r = d/4 here
  redteam   the conjecture of note 10, section 9: ell ((n/q)^s + C(L,2) eps^s), n = 2^(kappa+R), R = 1 + 3 level

NEST is sum_{j<ell} tau^-j (points reused across the ell rounds, Lemma T of note 14) or ell (no nesting loss: a union over the rounds).

Usage: python3 16_params.py [bits]   (bits: the point-message budget is 2^-bits; default 110, the 15-bit grind)
"""
import math
import sys

LOGQ = 128
KAPPA = [24, 20, 16, 12, 8, 4]
FOLDS = [6, 4, 4, 4, 4, 4]
BUDGET = -float(sys.argv[1]) if len(sys.argv) > 1 else -110.0  # log2 of the point-message budget
LOGK0 = LOGQ + 9
LOGTAU = -119.0


def lse(*xs):
    m = max(xs)
    if m == -math.inf:
        return m
    return m + math.log2(sum(2.0 ** (x - m) for x in xs))


def log_eps(kappa, ell):
    return math.log2((1 << kappa) - 1 + ell + (1 << ell) - 1) - LOGQ


def log_c2(b):  # log2 C(2^b, 2)
    return 2 * b - 1 if b > 0 else -math.inf


def nest(ell, nested):
    if not nested:
        return math.log2(ell)
    return lse(*[-j * LOGTAU for j in range(ell)])


def proved(b, s, kappa, ell, nested):
    le = log_eps(kappa, ell)
    triple = 3 * b + 6 * LOGQ - (2 * LOGK0 + math.log2(2.0**9 - 2) + LOGQ)
    return lse(log_c2(b), triple + nest(ell, nested)) + s * le


def thm_b(b, u, s, kappa, ell, nested):
    le = log_eps(kappa, ell)
    ku = 2.0**9 - s - 2.0 ** (b - LOGQ)
    if ku <= 2:
        return math.inf
    unexpl = 3 * u + 3 * LOGQ - (2 * math.log2(ku) + math.log2(ku - 1) + 3 * LOGQ) + s * le
    sep1 = math.log2(s) + log_c2(b) + (s - 1) * le
    eq = math.log2(max(s * (s - 1) / 2, 1e-300)) - LOGQ
    return lse(eq, log_c2(b) + s * le, lse(sep1, unexpl) + nest(ell, nested))


def floor_bound(s, kappa, ell, frac=0.25):
    lr = math.log2(frac * ((1 << kappa) - 1 + ell)) - LOGQ
    return math.log2(s) + (s - 1) * lr


def redteam(b, s, kappa, ell, level):
    le = log_eps(kappa, ell)
    ln = kappa + 1 + 3 * level - LOGQ
    return math.log2(ell) + lse(s * ln, log_c2(b) + s * le)


def least(f, lo=1):
    s = lo
    while f(s) > BUDGET:
        s += 1
        if s > 200:
            return None
    return s


def row(name, f):
    counts = [least(lambda s, i=i: f(s, KAPPA[i], FOLDS[i], i)) for i in range(6)]
    if any(c is None for c in counts):
        print(f"  {name:<46} not applicable (needs L < K0)")
        return
    print(f"  {name:<46} {', '.join(str(c) for c in counts)}   total {sum(counts)}")


def main():
    print(f"point-message budget 2^{BUDGET:.0f}")
    print("log2(1/eps) per level:", ", ".join(f"{-log_eps(k, l):.1f}" for k, l in zip(KAPPA, FOLDS)))
    print("nesting factor log2 sum tau^-j:", ", ".join(f"{nest(l, True):.0f}" for l in FOLDS))
    for b in (10, 40, 70, 100, 300):
        print(f"\n== list bound L = 2^{b}: points per level (levels 0..5)")
        for nested in (True, False):
            tag = "points reused, Lemma T" if nested else "no nesting loss (union over rounds)"
            print(f" [{tag}]")
            row("proved (note 14)", lambda s, k, l, i: proved(b, s, k, l, nested))
            row(f"Theorem B, unconditional (u = {128 + b})", lambda s, k, l, i: thm_b(b, 128 + b, s, k, l, nested))
            for u in (64, b + 10, 0):
                row(f"Theorem B, unexplained mass 2^{u} q", lambda s, k, l, i: thm_b(b, u, s, k, l, nested))
        print(" [for comparison]")
        row("floor of the method (Prop. 3.1, r = d/4)", lambda s, k, l, i: floor_bound(s, k, l))
        row("conjecture of note 10 (refuted as stated)", lambda s, k, l, i: redteam(b, s, k, l, i))
    print("\n== largest unexplained mass (log2 of |T_un|/q) at which Theorem B's count equals its structured count, L = 2^40")
    for nested in (True, False):
        out = []
        for i in range(6):
            s0 = least(lambda s: thm_b(40, 0, s, KAPPA[i], FOLDS[i], nested))
            u = 0
            while u < 400 and thm_b(40, u + 1, s0, KAPPA[i], FOLDS[i], nested) <= BUDGET:
                u += 1
            out.append(f"s={s0}: u<={u}")
        print(" ", "nested   " if nested else "no nesting", "; ".join(out))


if __name__ == "__main__":
    main()
